#!/usr/bin/env python3
"""
Generate per-module markdown API docs from Verge source files.

Reads verge_lib/ source, extracts doc comments and public item signatures,
and writes per-module markdown files. Warns on undocumented public items.

Key behaviors:
  - `open spec fn`: body is included (it IS the specification)
  - `closed spec fn`, `proof fn`, `exec fn`, regular `fn`:
    signature + clauses (requires/ensures/recommends/returns/no_unwind/opens_invariants)
  - `uninterp spec fn`: signature only
  - `mod tests` blocks are skipped entirely
  - Items marked `#[doc(hidden)]` are exempt from warnings
  - Macro definitions (macro_rules!) are skipped unless marked //~doc-macro

Doc directives (//~ comments):
  - `//~doc-skip`         — suppress the next item from docs entirely (no warning)
  - `//~doc-item: <line>` — override the next item's rendered signature
  - `//~doc-macro`        — on a macro_rules! definition, marks its invocations as documentable

Usage:
    python3 tools/generate_verge_docs.py [--output docs/api]

Exits with code 1 if any undocumented public items are found.
"""

import argparse
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

VERGE_LIB = Path(__file__).resolve().parent.parent / "verge_lib"

# ---------------------------------------------------------------------------
# Data model
# ---------------------------------------------------------------------------

@dataclass
class Item:
    kind: str            # fn, struct, enum, trait, type, impl, assume_specification, macro
    name: str            # short display name
    signature: str       # full signature (possibly multi-line)
    doc: str             # /// doc comment text
    body: str            # for open spec fn: the function body; empty otherwise
    clauses: str         # requires/ensures/etc. block (for non-open fns)
    children: list       # for impl/trait blocks: child Items
    is_open_spec: bool   # True for `open spec fn`
    attrs: list          # attributes preceding this item
    visibility: str      # "pub", "pub(crate)", "" etc.


# ---------------------------------------------------------------------------
# Brace tracking
# ---------------------------------------------------------------------------

def _net_braces(s: str) -> int:
    """Count net { minus } ignoring string literals."""
    n, in_s = 0, False
    i = 0
    while i < len(s):
        c = s[i]
        if c == '\\' and in_s:
            i += 2
            continue
        if c == '"':
            in_s = not in_s
        elif not in_s:
            if c == '{':
                n += 1
            elif c == '}':
                n -= 1
        i += 1
    return n


# ---------------------------------------------------------------------------
# Item keyword detection
# ---------------------------------------------------------------------------

# Matches public item keywords. We only document public items.
_ITEM_KW_RE = re.compile(
    r'^(\s*)'
    r'(pub(?:\s*\([^)]*\))?\s+)?'              # optional visibility
    r'((?:(?:open|closed|uninterp|broadcast|axiom|'
    r'proof|exec|default|unsafe|const|async|extern|tracked)\s+)*'
    r'(?:spec\s+)?)'                            # mode qualifiers
    r'(fn|struct|enum|trait|type|impl|mod|assume_specification)\b'
)

_MACRO_RE = re.compile(r'^\s*(?:pub\s+)?macro_rules!\s+(\w+)')

# Macro invocation: `name!(...)` or `name!(...);` — not macro_rules!
_MACRO_INVOCATION_RE = re.compile(r'^\s*(\w+)!\s*[\(\[]')

# Clause keywords that follow a signature
_CLAUSE_KW = {'requires', 'ensures', 'recommends', 'returns', 'no_unwind', 'opens_invariants'}


# ---------------------------------------------------------------------------
# Parsing
# ---------------------------------------------------------------------------

def _extract_name(kind: str, first_line: str) -> str:
    """Extract display name from the first line of a signature."""
    if kind == 'assume_specification':
        # Extract the target inside [...], handling nested brackets
        bracket_start = first_line.find('[')
        if bracket_start >= 0:
            depth = 0
            for j in range(bracket_start, len(first_line)):
                if first_line[j] == '[':
                    depth += 1
                elif first_line[j] == ']':
                    depth -= 1
                    if depth == 0:
                        return first_line[bracket_start+1:j].strip()
        return first_line.strip()[:60]
    if kind == 'impl':
        # impl<...> Foo or impl<...> Trait for Foo
        m = re.search(r'impl\s*(?:<[^>]*>)?\s+([\w:<>\[\], &\?]+?)(?:\s*\{|$)', first_line)
        return m.group(1).strip() if m else first_line.strip()
    m = re.search(r'(?:fn|struct|enum|trait|type|mod)\s+(\w+)', first_line)
    return m.group(1) if m else first_line.strip()[:60]


def _is_open_spec(qualifiers: str) -> bool:
    return bool(re.search(r'\bopen\b', qualifiers))


def _is_uninterp(qualifiers: str) -> bool:
    return bool(re.search(r'\buninterp\b', qualifiers))


def _has_attr(attrs: list[str], name: str) -> bool:
    """Check if any attribute matches (substring)."""
    return any(name in a for a in attrs)


def _is_verus_plumbing(item: Item) -> bool:
    """Items that are Verus internal plumbing, not useful in user docs."""
    return item.name == 'ExternalTraitSpecificationFor'


def _is_doc_exempt(attrs: list[str]) -> bool:
    return _has_attr(attrs, 'doc(hidden)')


def _dedent(text: str) -> str:
    lines = [l for l in text.splitlines() if l.strip()]
    if not lines:
        return text
    indent = min(len(l) - len(l.lstrip()) for l in lines)
    return "\n".join(l[indent:] for l in text.splitlines()).strip()


def _collect_body(lines: list[str], start: int, depth: int, stop_depth: int) -> tuple[int, str]:
    """Collect lines of a body block until depth returns to stop_depth. Returns (next_i, body_text)."""
    body_lines = []
    i = start
    d = depth
    while i < len(lines) and d > stop_depth:
        body_lines.append(lines[i])
        d += _net_braces(lines[i].strip())
        i += 1
    return i, "\n".join(body_lines)


def _has_doc_macro_directive(lines: list[str], macro_line: int) -> bool:
    """Check if the lines immediately preceding macro_line contain //~doc-macro."""
    j = macro_line - 1
    while j >= 0:
        s = lines[j].strip()
        if s.startswith("//~") and "doc-macro" in s:
            return True
        if s.startswith("///") or s.startswith("//~") or s.startswith("#[") or s.startswith("#!") or not s:
            j -= 1
            continue
        break
    return False


def _split_sig_and_clauses(text: str) -> tuple[str, str]:
    """Split a //~doc-item: override into signature and clause parts."""
    clause_kws = {'requires', 'ensures', 'recommends', 'returns', 'no_unwind',
                  'opens_invariants', 'decreases'}
    lines = text.splitlines()
    sig_lines = []
    clause_lines = []
    in_clauses = False
    for line in lines:
        stripped = line.strip()
        first_word = stripped.split()[0].rstrip(',').rstrip(';') if stripped else ""
        if first_word in clause_kws:
            in_clauses = True
        if in_clauses:
            clause_lines.append(line)
        else:
            sig_lines.append(line)
    return "\n".join(sig_lines), "\n".join(clause_lines)


def _net_parens(s: str) -> int:
    """Count net ( minus ) in a string, ignoring string literals."""
    n, in_s = 0, False
    i = 0
    while i < len(s):
        c = s[i]
        if c == '\\' and in_s:
            i += 2
            continue
        if c == '"':
            in_s = not in_s
        elif not in_s:
            if c == '(':
                n += 1
            elif c == ')':
                n -= 1
        i += 1
    return n


def _collect_signature_and_clauses(
    lines: list[str], start: int, stop_depth: int
) -> tuple[int, str, str, bool]:
    """
    From the first line of an item, collect the full signature + clause block.

    Returns (next_line, signature, clauses, body_opened).

    The signature includes everything up to and including the first {.
    Clauses (requires/ensures/etc.) are part of the signature for display purposes
    but tracked separately.

    Key: braces inside parenthesized expressions (like `({ match ... })`) in
    clause bodies are NOT treated as function body openings.
    """
    sig_lines = []
    clause_lines = []
    i = start
    d = stop_depth    # brace depth
    pd = 0            # paren depth (tracks clause expression nesting)
    in_clauses = False
    body_opened = False

    while i < len(lines) and len(sig_lines) + len(clause_lines) < 120:
        l = lines[i]
        ls = l.strip()
        delta = _net_braces(ls)
        pdelta = _net_parens(ls)

        # Track whether a brace opened on this line that could be a function body.
        # NOT a body opener if we're inside clause expressions AND the { isn't on its own line.
        # A standalone `{` after clauses IS a body opener.
        # Balanced braces in a clause expression (like `if a { b } else { c }`) are NOT.
        brace_is_body = pd == 0 and '{' in ls
        if in_clauses and brace_is_body:
            # Only treat as body if it's a standalone `{` (possibly with whitespace)
            # or if the line starts with `{`
            if ls != '{' and not ls.startswith('{'):
                brace_is_body = False

        d += delta
        pd += pdelta

        # Check if this line starts a clause keyword
        first_word = ls.split()[0].rstrip(',').rstrip(';') if ls else ""
        if first_word in _CLAUSE_KW:
            in_clauses = True

        if in_clauses:
            clause_lines.append(l)
        else:
            sig_lines.append(l)

        # Bodyless: ends with ; at the right depth (and not inside parens in clause)
        if re.search(r';\s*$', ls) and d <= stop_depth + 1 and pd <= 0:
            i += 1
            break
        # Body opened — only when the brace is NOT inside a parenthesized clause expr
        if brace_is_body and d > stop_depth and pd <= 0:
            body_opened = True
            i += 1
            break
        # Self-closing body (e.g., `impl X {}` or `fn foo() { expr }`)
        if brace_is_body and d == stop_depth and pd <= 0 and delta == 0 and '}' in ls:
            body_opened = True
            i += 1
            break
        i += 1
    else:
        pass

    sig = "\n".join(l.rstrip() for l in sig_lines)
    clauses = "\n".join(l.rstrip() for l in clause_lines)
    return i, sig, clauses, body_opened


def _scan_items(lines: list[str], start: int, stop_depth: int,
                 doc_macros: set[str]) -> tuple[int, list[Item]]:
    """Scan lines collecting items at stop_depth. Returns (next_i, items).

    doc_macros: set of macro names marked with //~doc-macro (mutable, updated in place).
    """
    items: list[Item] = []
    i = start
    n = len(lines)
    depth = stop_depth
    doc_lines: list[str] = []
    attrs: list[str] = []
    doc_item_lines: list[str] = []  # //~doc-item: override lines
    doc_skip = False                # //~doc-skip flag

    while i < n:
        line = lines[i]
        stripped = line.strip()
        delta = _net_braces(stripped)

        # Doc comment
        if stripped.startswith("///"):
            text = stripped[3:]
            if text.startswith(" "):
                text = text[1:]
            doc_lines.append(text)
            i += 1
            continue

        # Doc directives (//~ comments)
        if stripped.startswith("//~"):
            directive = stripped[3:]
            if directive.startswith("doc-skip"):
                doc_skip = True
            elif directive.startswith("doc-item:"):
                doc_item_lines.append(directive[len("doc-item:"):].rstrip())
            elif directive.startswith("doc-macro"):
                pass  # handled at macro_rules! definition site below
            i += 1
            continue

        # Attribute
        if stripped.startswith("#[") or stripped.startswith("#!"):
            attrs.append(stripped)
            i += 1
            continue

        # Blank line: reset doc but keep attrs
        if not stripped:
            doc_lines = []
            doc_item_lines = []
            doc_skip = False
            depth += delta
            i += 1
            continue

        # Non-doc comment (but not //~ directive)
        if stripped.startswith("//"):
            doc_lines = []
            doc_item_lines = []
            doc_skip = False
            depth += delta
            i += 1
            continue

        # macro_rules! — check for //~doc-macro, then skip definition
        mm = _MACRO_RE.match(line)
        if mm and depth == stop_depth:
            macro_name = mm.group(1)
            # Check if preceding //~ directives included doc-macro
            if _has_doc_macro_directive(lines, i):
                doc_macros.add(macro_name)
            doc_lines = []
            doc_item_lines = []
            doc_skip = False
            attrs = []
            depth += delta
            i += 1
            # Skip body
            while i < n and depth > stop_depth:
                depth += _net_braces(lines[i].strip())
                i += 1
            continue

        # Skip `mod tests`
        if re.match(r'\s*(?:pub\s+)?mod\s+tests\b', line) and depth == stop_depth:
            doc_lines = []
            doc_item_lines = []
            doc_skip = False
            attrs = []
            depth += delta
            i += 1
            while i < n and depth > stop_depth:
                depth += _net_braces(lines[i].strip())
                i += 1
            continue

        # Macro invocation (not macro_rules!)
        mi = _MACRO_INVOCATION_RE.match(line)
        if mi and depth == stop_depth and not _MACRO_RE.match(line):
            macro_name = mi.group(1)
            has_doc = bool(doc_lines)
            is_marked = macro_name in doc_macros

            doc_text = "\n".join(doc_lines)
            cur_attrs = list(attrs)
            cur_doc_item = list(doc_item_lines)
            cur_skip = doc_skip
            doc_lines = []
            doc_item_lines = []
            doc_skip = False
            attrs = []

            # Collect the full invocation (may span multiple lines)
            inv_lines = []
            pd = 0
            while i < n:
                l = lines[i]
                ls = l.strip()
                inv_lines.append(l)
                pd += _net_parens(ls)
                pd += ls.count('[') - ls.count(']')
                depth += _net_braces(ls)
                i += 1
                if pd <= 0 and (ls.endswith(');') or ls.endswith('];') or ls.endswith(')')):
                    break
            # Restore depth (macro invocation is balanced)
            depth = stop_depth

            if cur_skip:
                continue

            if not has_doc and not is_marked:
                # Undocumented invocation of unmarked macro — silently skip
                continue

            if has_doc and not is_marked:
                # Documented invocation of unmarked macro — skip but this will
                # be caught by the undocumented-item warning system naturally
                continue

            # This is a documentable macro invocation
            raw_sig = "\n".join(l.rstrip() for l in inv_lines)

            # Use //~doc-item: override if present
            if cur_doc_item:
                sig = "\n".join(cur_doc_item)
                # Detect kind from the override text
                kind = 'fn'
                if re.match(r'\s*pub\s+(?:open\s+|closed\s+|uninterp\s+)?spec\s+fn', sig):
                    kind = 'fn'
                elif 'assume_specification' in sig:
                    kind = 'assume_specification'
                elif re.match(r'\s*pub\s+(?:struct|enum|trait|type)', sig):
                    m2 = re.match(r'\s*pub\s+\S+\s+(struct|enum|trait|type)', sig)
                    kind = m2.group(1) if m2 else 'fn'
                name = _extract_name(kind, sig.splitlines()[0])
                # Split signature and clauses
                sig_part, clause_part = _split_sig_and_clauses(sig)
                is_open = bool(re.search(r'\bopen\b', sig))
                items.append(Item(
                    kind=kind, name=name, signature=sig_part, doc=doc_text,
                    body="", clauses=clause_part, children=[],
                    is_open_spec=is_open, attrs=cur_attrs, visibility="pub",
                ))
            else:
                # Use raw macro invocation as signature
                bracket_match = re.search(r'\[\s*(\w+)', raw_sig)
                name = f"{macro_name}!({bracket_match.group(1)})" if bracket_match else f"{macro_name}!"
                items.append(Item(
                    kind='fn', name=name, signature=raw_sig, doc=doc_text,
                    body="", clauses="", children=[],
                    is_open_spec=False, attrs=cur_attrs, visibility="pub",
                ))
            continue

        # Check for item keyword
        m = _ITEM_KW_RE.match(line)

        if m and depth == stop_depth:
            vis = (m.group(2) or "").strip()
            qualifiers = (m.group(3) or "").strip()
            kind = m.group(4)

            # Skip `mod` declarations (submodules) — we process them as separate files
            if kind == 'mod':
                doc_lines = []
                doc_item_lines = []
                doc_skip = False
                attrs = []
                depth += delta
                i += 1
                # Skip body if any
                while i < n and depth > stop_depth:
                    depth += _net_braces(lines[i].strip())
                    i += 1
                continue

            doc_text = "\n".join(doc_lines)
            cur_attrs = list(attrs)
            cur_doc_item = list(doc_item_lines)
            cur_skip = doc_skip
            doc_lines = []
            doc_item_lines = []
            doc_skip = False
            attrs = []

            # Handle //~doc-skip
            if cur_skip:
                # Skip the item entirely — consume its body
                depth += delta
                i += 1
                while i < n and depth > stop_depth:
                    depth += _net_braces(lines[i].strip())
                    i += 1
                depth = stop_depth
                continue

            # Handle //~doc-item: override
            if cur_doc_item:
                sig_override = "\n".join(cur_doc_item)
                # Detect kind from override
                if 'assume_specification' in sig_override:
                    kind = 'assume_specification'
                sig_part, clause_part = _split_sig_and_clauses(sig_override)
                name = _extract_name(kind, sig_part.splitlines()[0] if sig_part else "")
                is_open = bool(re.search(r'\bopen\b', sig_override))

                # Still need to skip the actual item in source
                depth += delta
                i += 1
                while i < n and depth > stop_depth:
                    depth += _net_braces(lines[i].strip())
                    i += 1
                depth = stop_depth

                items.append(Item(
                    kind=kind, name=name, signature=sig_part, doc=doc_text,
                    body="", clauses=clause_part, children=[],
                    is_open_spec=is_open, attrs=cur_attrs, visibility=vis or "pub",
                ))
                continue

            # Normal item parsing (unchanged)
            is_open = _is_open_spec(qualifiers)

            i, sig, clauses, body_opened = _collect_signature_and_clauses(lines, i, stop_depth)
            name = _extract_name(kind, sig.splitlines()[0] if sig else "")

            last_sig_line = sig.splitlines()[-1].strip() if sig else ""
            body_self_closed = body_opened and _net_braces(last_sig_line) == 0 and '{' in last_sig_line and '}' in last_sig_line
            if body_self_closed:
                depth = stop_depth
            else:
                depth = stop_depth + (1 if body_opened else 0)

            if kind in ('impl', 'trait') and body_opened and not body_self_closed:
                i, children = _scan_items(lines, i, depth, doc_macros)
                depth -= 1

                has_pub_children = any(c.visibility.startswith('pub') for c in children)
                if vis.startswith('pub') or has_pub_children:
                    items.append(Item(
                        kind=kind, name=name, signature=sig, doc=doc_text,
                        body="", clauses=clauses, children=children,
                        is_open_spec=False, attrs=cur_attrs, visibility=vis,
                    ))
                continue

            body = ""
            if body_opened:
                if is_open:
                    i, body = _collect_body(lines, i, depth, stop_depth)
                    depth = stop_depth
                else:
                    while i < n and depth > stop_depth:
                        depth += _net_braces(lines[i].strip())
                        i += 1
                    depth = stop_depth

            items.append(Item(
                kind=kind, name=name, signature=sig, doc=doc_text,
                body=body, clauses=clauses, children=[],
                is_open_spec=is_open, attrs=cur_attrs, visibility=vis,
            ))
            continue

        # Not an item — track depth
        doc_lines = []
        doc_item_lines = []
        doc_skip = False
        attrs = []
        depth += delta
        if depth < stop_depth:
            i += 1
            break
        i += 1

    return i, items


def parse_source(source: str, doc_macros: set[str] = None) -> tuple[str, list[Item]]:
    """Parse a Verge source file. Returns (module_doc, items)."""
    lines = source.splitlines()
    module_doc_lines: list[str] = []
    all_items: list[Item] = []
    if doc_macros is None:
        doc_macros = set()

    i = 0
    n = len(lines)
    depth = 0
    doc_lines: list[str] = []
    attrs: list[str] = []
    doc_item_lines: list[str] = []
    doc_skip = False

    while i < n:
        line = lines[i]
        stripped = line.strip()
        delta = _net_braces(stripped)

        # Module doc
        if stripped.startswith("//!"):
            text = stripped[3:]
            if text.startswith(" "):
                text = text[1:]
            module_doc_lines.append(text)
            i += 1
            continue

        # Item doc
        if stripped.startswith("///"):
            text = stripped[3:]
            if text.startswith(" "):
                text = text[1:]
            doc_lines.append(text)
            i += 1
            continue

        # Doc directives
        if stripped.startswith("//~"):
            directive = stripped[3:]
            if directive.startswith("doc-skip"):
                doc_skip = True
            elif directive.startswith("doc-item:"):
                doc_item_lines.append(directive[len("doc-item:"):].rstrip())
            i += 1
            continue

        if stripped.startswith("#[") or stripped.startswith("#!"):
            attrs.append(stripped)
            i += 1
            continue

        if not stripped:
            doc_lines = []
            doc_item_lines = []
            doc_skip = False
            depth += delta
            i += 1
            continue

        if stripped.startswith("//"):
            doc_lines = []
            doc_item_lines = []
            doc_skip = False
            depth += delta
            i += 1
            continue

        # verus! { block
        if depth == 0 and re.match(r'verus_?!\s*\{', stripped):
            depth += delta
            doc_lines = []
            doc_item_lines = []
            doc_skip = False
            attrs = []
            i += 1
            i, items = _scan_items(lines, i, depth, doc_macros)
            all_items.extend(items)
            depth -= 1
            continue

        # Top-level items outside verus!
        m = _ITEM_KW_RE.match(line)
        mm = _MACRO_RE.match(line)

        if mm and depth == 0:
            macro_name = mm.group(1)
            if _has_doc_macro_directive(lines, i):
                doc_macros.add(macro_name)
            doc_lines = []
            doc_item_lines = []
            doc_skip = False
            attrs = []
            depth += delta
            i += 1
            while i < n and depth > 0:
                depth += _net_braces(lines[i].strip())
                i += 1
            continue

        # Skip `mod tests` at top level
        if re.match(r'\s*(?:pub\s+)?mod\s+tests\b', line) and depth == 0:
            doc_lines = []
            doc_item_lines = []
            doc_skip = False
            attrs = []
            depth += delta
            i += 1
            while i < n and depth > 0:
                depth += _net_braces(lines[i].strip())
                i += 1
            continue

        if m and depth == 0:
            vis = (m.group(2) or "").strip()
            qualifiers = (m.group(3) or "").strip()
            kind = m.group(4)

            if kind == 'mod':
                doc_lines = []
                doc_item_lines = []
                doc_skip = False
                attrs = []
                depth += delta
                i += 1
                while i < n and depth > 0:
                    depth += _net_braces(lines[i].strip())
                    i += 1
                continue

            doc_text = "\n".join(doc_lines)
            cur_attrs = list(attrs)
            cur_doc_item = list(doc_item_lines)
            cur_skip = doc_skip
            doc_lines = []
            doc_item_lines = []
            doc_skip = False
            attrs = []

            # Handle //~doc-skip
            if cur_skip:
                depth += delta
                i += 1
                while i < n and depth > 0:
                    depth += _net_braces(lines[i].strip())
                    i += 1
                depth = 0
                continue

            # Handle //~doc-item: override
            if cur_doc_item:
                sig_override = "\n".join(cur_doc_item)
                if 'assume_specification' in sig_override:
                    kind = 'assume_specification'
                sig_part, clause_part = _split_sig_and_clauses(sig_override)
                name = _extract_name(kind, sig_part.splitlines()[0] if sig_part else "")
                is_open = bool(re.search(r'\bopen\b', sig_override))

                depth += delta
                i += 1
                while i < n and depth > 0:
                    depth += _net_braces(lines[i].strip())
                    i += 1
                depth = 0

                all_items.append(Item(
                    kind=kind, name=name, signature=sig_part, doc=doc_text,
                    body="", clauses=clause_part, children=[],
                    is_open_spec=is_open, attrs=cur_attrs, visibility=vis or "pub",
                ))
                continue

            # Normal item parsing
            is_open = _is_open_spec(qualifiers)
            i, sig, clauses, body_opened = _collect_signature_and_clauses(lines, i, 0)
            name = _extract_name(kind, sig.splitlines()[0] if sig else "")

            last_sig_line = sig.splitlines()[-1].strip() if sig else ""
            body_self_closed = body_opened and _net_braces(last_sig_line) == 0 and '{' in last_sig_line and '}' in last_sig_line
            if body_self_closed:
                depth = 0
            else:
                depth = 1 if body_opened else 0

            if kind in ('impl', 'trait') and body_opened and not body_self_closed:
                i, children = _scan_items(lines, i, depth, doc_macros)
                depth -= 1
                has_pub_children = any(c.visibility.startswith('pub') for c in children)
                if vis.startswith('pub') or has_pub_children:
                    all_items.append(Item(
                        kind=kind, name=name, signature=sig, doc=doc_text,
                        body="", clauses=clauses, children=children,
                        is_open_spec=False, attrs=cur_attrs, visibility=vis,
                    ))
                continue

            body = ""
            if body_opened:
                if is_open:
                    i, body = _collect_body(lines, i, depth, 0)
                    depth = 0
                else:
                    while i < n and depth > 0:
                        depth += _net_braces(lines[i].strip())
                        i += 1
                    depth = 0

            all_items.append(Item(
                kind=kind, name=name, signature=sig, doc=doc_text,
                body=body, clauses=clauses, children=[],
                is_open_spec=is_open, attrs=cur_attrs, visibility=vis,
            ))
            continue

        doc_lines = []
        doc_item_lines = []
        doc_skip = False
        attrs = []
        depth += delta
        i += 1

    return "\n".join(module_doc_lines), all_items


# ---------------------------------------------------------------------------
# Warning collection
# ---------------------------------------------------------------------------

def _check_undocumented(items: list[Item], module_path: str, warnings: list[str]):
    """Collect warnings for undocumented public items."""
    for item in items:
        if item.kind == 'impl':
            # Check children of impl blocks
            _check_undocumented(item.children, module_path, warnings)
            continue
        if item.kind == 'trait':
            # Trait itself should be documented
            if item.visibility.startswith('pub') and not item.doc and not _is_doc_exempt(item.attrs):
                warnings.append(f"  {module_path}: pub {item.kind} `{item.name}` has no doc comment")
            _check_undocumented(item.children, module_path, warnings)
            continue
        if not item.visibility.startswith('pub'):
            continue
        if _is_doc_exempt(item.attrs):
            continue
        if not item.doc:
            warnings.append(f"  {module_path}: pub {item.kind} `{item.name}` has no doc comment")


# ---------------------------------------------------------------------------
# Markdown rendering
# ---------------------------------------------------------------------------

def _normalize_code_block(sig: str, clauses: str, body: str = "") -> str:
    """
    Normalize a code block with proper indentation:
    - First line (signature start) has no indent
    - Continuation of signature: 1 indent (4 spaces)
    - Clause keywords (requires, ensures, etc.): 1 indent
    - Clause expressions: 2 indents base, preserving relative indent for nested blocks
    - Body lines: 1 indent base, preserving relative indent
    """
    INDENT = "    "

    # Combine sig + clauses into raw lines
    raw = sig
    if clauses:
        raw += "\n" + clauses
    if body:
        raw += "\n" + body

    raw_lines = raw.splitlines()
    if not raw_lines:
        return ""

    # Find minimum indent of non-empty lines
    non_empty = [l for l in raw_lines if l.strip()]
    if not non_empty:
        return ""
    base_indent = min(len(l) - len(l.lstrip()) for l in non_empty)

    result = []
    clause_kws = {'requires', 'ensures', 'recommends', 'returns', 'no_unwind',
                  'opens_invariants', 'decreases'}
    in_body = False
    past_signature = False
    clause_base_indent = None  # indent level of clause keyword lines in source

    for i, line in enumerate(raw_lines):
        stripped = line.strip()
        if not stripped:
            result.append("")
            continue

        # Measure original indent relative to base
        orig_indent = len(line) - len(line.lstrip()) - base_indent

        # First line: no indent
        if i == 0:
            result.append(stripped)
            continue

        # Check for body start (standalone {)
        if stripped == '{' and not past_signature:
            result.append("{")
            in_body = True
            continue

        # Body closing (only for function body, not clause expressions)
        if stripped == '}' and in_body and not past_signature:
            result.append("}")
            in_body = False
            continue

        # Detect clause keyword
        first_word = stripped.split()[0].rstrip(',').rstrip(';') if stripped else ""
        is_clause_kw = first_word in clause_kws

        if is_clause_kw:
            past_signature = True
            clause_base_indent = orig_indent + 4  # expressions are typically 1 indent deeper
            result.append(INDENT + stripped)
        elif past_signature and not in_body:
            # Clause expression: 2 indent base + preserve extra nesting
            if clause_base_indent is not None:
                extra = max(0, orig_indent - clause_base_indent)
            else:
                extra = 0
            result.append(INDENT + INDENT + " " * extra + stripped)
        elif in_body:
            # Body line: 1 indent base + preserve relative
            result.append(INDENT + " " * max(0, orig_indent) + stripped)
        else:
            # Signature continuation
            result.append(INDENT + stripped)

    return "\n".join(result)


def _render_signature_block(item: Item) -> str:
    """Render the code block for an item."""

    if item.is_open_spec and item.body:
        # Open spec fn: show signature + clauses + body
        code = _normalize_code_block(item.signature, item.clauses, item.body)
        # Ensure it ends with }
        if not code.rstrip().endswith("}"):
            code += "\n}"
        return f"```rust\n{code}\n```"

    if item.kind == 'assume_specification':
        # Show full signature + clauses (these are the spec)
        code = _normalize_code_block(item.signature, item.clauses)
        return f"```rust\n{code}\n```"

    # Non-open: show signature + clauses, no body
    code = _normalize_code_block(item.signature, item.clauses)
    # Strip trailing { if present (we don't show body)
    code = re.sub(r'\s*\{\s*$', '', code)
    # Add ; if it doesn't end with one and isn't a struct/enum with fields
    if not code.rstrip().endswith((';', '}', ',')):
        code = code.rstrip()
    return f"```rust\n{code}\n```"


def _kind_label(item: Item) -> str:
    """Return a section label for grouping."""
    if item.kind == 'trait':
        return "Traits"
    if item.kind == 'struct':
        return "Structs"
    if item.kind == 'enum':
        return "Enums"
    if item.kind == 'type':
        return "Type Aliases"
    if item.kind in ('fn', 'assume_specification'):
        return "Functions"
    if item.kind == 'impl':
        return "Implementations"
    return "Items"


def _render_item(item: Item, level: int) -> str:
    hdr = "#" * min(level, 6)
    parts: list[str] = []

    if item.kind in ('impl', 'trait'):
        if item.kind == 'trait':
            parts.append(f"\n{hdr} `{item.name}`\n")
        else:
            parts.append(f"\n{hdr} `impl {item.name}`\n")
        if item.doc:
            parts.append(item.doc + "\n")
        if item.signature:
            # Show trait/impl signature
            sig = _dedent(item.signature)
            sig = re.sub(r'\s*\{\s*$', '', sig)
            parts.append(f"```rust\n{sig}\n```\n")
        if item.children:
            # For traits, show all methods (they're implicitly pub)
            # For impl blocks, show only pub items
            # Filter out Verus plumbing in all cases
            if item.kind == 'trait':
                visible = [c for c in item.children if not _is_verus_plumbing(c)]
            else:
                visible = [c for c in item.children
                           if c.visibility.startswith('pub') and not _is_verus_plumbing(c)]
            for child in visible:
                parts.append(_render_item(child, level + 1))
    else:
        parts.append(f"\n{hdr} `{item.name}`\n")
        if item.doc:
            parts.append(item.doc + "\n")
        parts.append(_render_signature_block(item) + "\n")

    return "\n".join(parts)


def render_md(module_path: str, module_doc: str, items: list[Item]) -> str:
    """Render a full module markdown file."""
    out: list[str] = [f"# `verge::{module_path}`\n"]
    if module_doc:
        out.append(module_doc + "\n")

    # Filter to public items only (impl blocks may contain pub children)
    pub_items = []
    for item in items:
        if item.kind in ('impl', 'trait'):
            # Include if trait is pub, or impl has any pub children
            if item.visibility.startswith('pub') or any(
                c.visibility.startswith('pub') for c in item.children
            ):
                pub_items.append(item)
        elif item.visibility.startswith('pub'):
            pub_items.append(item)

    if not pub_items:
        return ""

    # Group by kind
    groups: dict[str, list[Item]] = {}
    for item in pub_items:
        label = _kind_label(item)
        groups.setdefault(label, []).append(item)

    # Render in a sensible order
    order = ["Structs", "Enums", "Traits", "Functions", "Type Aliases", "Implementations", "Items"]
    for group_name in order:
        if group_name not in groups:
            continue
        out.append(f"\n## {group_name}\n")
        for item in groups[group_name]:
            out.append(_render_item(item, level=3))

    text = "\n".join(out)
    return re.sub(r"\n{4,}", "\n\n\n", text)


# ---------------------------------------------------------------------------
# File discovery and processing
# ---------------------------------------------------------------------------

def _discover_modules(lib_root: Path) -> list[tuple[str, Path]]:
    """
    Discover all .rs source files under verge_lib/, returning (module_path, file_path) pairs.
    The module_path uses :: separators (e.g., "io::stdio").
    """
    # Read verge.rs to find top-level public modules
    verge_rs = lib_root / "verge.rs"
    if not verge_rs.exists():
        print(f"Error: {verge_rs} not found", file=sys.stderr)
        sys.exit(1)

    modules = []
    # Find all .rs files recursively, compute module paths
    for rs_file in sorted(lib_root.rglob("*.rs")):
        rel = rs_file.relative_to(lib_root)
        parts = list(rel.parts)

        # Skip verge.rs (crate root) and prelude.rs (just re-exports)
        if parts == ["verge.rs"]:
            # Process crate root as special case
            modules.append(("", rs_file))
            continue
        if parts == ["prelude.rs"]:
            continue

        # Convert path to module path
        # foo/bar.rs -> foo::bar
        # foo/mod.rs -> foo (but we skip mod.rs if it just declares submodules)
        if parts[-1] == "mod.rs":
            # Skip pure mod.rs files that just declare submodules
            # but include them if they have substantial content
            mod_path = "::".join(parts[:-1])
        else:
            parts[-1] = parts[-1].removesuffix(".rs")
            mod_path = "::".join(parts)

        modules.append((mod_path, rs_file))

    return modules


def process_file(module_path: str, src_file: Path, out_root: Path, warnings: list[str],
                 doc_macros: set[str] = None) -> bool:
    """Process one source file. Returns True if output was written."""
    source = src_file.read_text(encoding="utf-8")
    module_doc, items = parse_source(source, doc_macros)

    # Check for undocumented items
    display_path = module_path or "(crate root)"
    _check_undocumented(items, display_path, warnings)

    if not items and not module_doc:
        return False

    md = render_md(module_path, module_doc, items)
    if not md.strip():
        return False

    # Output path
    if not module_path:
        out_file = out_root / "index.md"
    else:
        out_file = out_root / (module_path.replace("::", "/") + ".md")

    out_file.parent.mkdir(parents=True, exist_ok=True)
    out_file.write_text(md, encoding="utf-8")
    return True


def generate_index(out_root: Path, written_modules: list[str]):
    """Generate a README.md index linking all module docs."""
    lines = [
        "# Verge API Reference\n",
        "Auto-generated from source. See the [source code](../verge_lib/) for full details.\n",
        "## Modules\n",
    ]
    for mod_path in sorted(written_modules):
        if not mod_path:
            continue
        rel_path = mod_path.replace("::", "/") + ".md"
        lines.append(f"- [`verge::{mod_path}`]({rel_path})")

    (out_root / "README.md").write_text("\n".join(lines) + "\n", encoding="utf-8")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def _prescan_doc_macros(lib_root: Path) -> set[str]:
    """Pre-scan all source files for //~doc-macro markers on macro_rules! definitions."""
    macros = set()
    for rs_file in lib_root.rglob("*.rs"):
        lines = rs_file.read_text(encoding="utf-8").splitlines()
        for i, line in enumerate(lines):
            mm = _MACRO_RE.match(line)
            if mm and _has_doc_macro_directive(lines, i):
                macros.add(mm.group(1))
    return macros


def main():
    parser = argparse.ArgumentParser(description="Generate Verge API docs as markdown")
    parser.add_argument("--output", default="docs/api",
                        help="Output directory (default: docs/api)")
    parser.add_argument("--no-warn", action="store_true",
                        help="Don't fail on undocumented items")
    args = parser.parse_args()

    out_root = Path(args.output)
    out_root.mkdir(parents=True, exist_ok=True)

    print(f"  Source: {VERGE_LIB}", file=sys.stderr)
    print(f"  Output: {out_root}", file=sys.stderr)

    modules = _discover_modules(VERGE_LIB)
    print(f"  Found {len(modules)} source files", file=sys.stderr)

    doc_macros = _prescan_doc_macros(VERGE_LIB)
    if doc_macros:
        print(f"  Doc macros: {', '.join(sorted(doc_macros))}", file=sys.stderr)

    warnings: list[str] = []
    written_modules: list[str] = []

    for mod_path, src_file in modules:
        rel = src_file.relative_to(VERGE_LIB)
        label = mod_path or "(crate root)"
        print(f"  Processing {label} ({rel})", file=sys.stderr)
        if process_file(mod_path, src_file, out_root, warnings, doc_macros):
            written_modules.append(mod_path)

    generate_index(out_root, written_modules)

    print(f"\n  Done: {len(written_modules)} module docs written to {out_root}", file=sys.stderr)

    if warnings:
        print(f"\n  ⚠ {len(warnings)} undocumented public item(s):", file=sys.stderr)
        for w in warnings:
            print(w, file=sys.stderr)
        if not args.no_warn:
            sys.exit(1)


if __name__ == "__main__":
    main()
