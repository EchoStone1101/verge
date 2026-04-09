#!/usr/bin/env python3
"""
Convert vstd source HTML (from third-party/vstd-raw/src/vstd/) into
per-module markdown files under third-party/vstd/.

Source files are the rustdoc "source view" pages (*.rs.html) which contain the
full Rust/Verus source. We strip the HTML and parse the plain source to
extract documented items.

Layout produced:
    /tmp/vstd-md-{VERSION}/
    ├── seq.md
    ├── seq_lib.md
    ├── map.md
    ├── arithmetic/
    │   ├── mod.md       (from arithmetic/mod.rs.html)
    │   ├── div_mod.md
    │   ├── mul.md
    │   └── ...
    └── ...

Usage:
    python3 tools/generate_vstd_md.py \
        [--input  /tmp/vstd-raw-{VERSION}/src/vstd] \
        [--output /tmp/vstd-md-{VERSION}]
"""

import argparse
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

from bs4 import BeautifulSoup


# ---------------------------------------------------------------------------
# Step 1: Extract plain Rust source from *.rs.html
# ---------------------------------------------------------------------------

def extract_source(html: str) -> str:
    """Extract the plain Rust source text from a rustdoc source-view HTML file."""
    soup = BeautifulSoup(html, "html.parser")
    pre = soup.find("pre", class_="rust")
    if not pre:
        return ""
    code = pre.find("code") or pre
    for a in code.find_all("a", attrs={"data-nosnippet": True}):
        a.decompose()
    return code.get_text()


# ---------------------------------------------------------------------------
# Step 2: Parse Rust/Verus source into documented items
# ---------------------------------------------------------------------------

@dataclass
class Item:
    kind: str           # "fn" | "struct" | "enum" | "trait" | "type" | "impl"
    signature: str      # signature lines (up to body open or ;), stripped
    doc: str            # doc comment text (/// lines joined, stripped of ///)
    children: list      # for impl blocks: list of child Items


# Matches the item-defining keyword at the start of a (possibly indented) line.
_ITEM_KW_RE = re.compile(
    r'^\s*'
    r'(?:pub(?:\s*\([^)]*\))?\s+)?'           # optional visibility
    r'(?:(?:open|closed|uninterp|broadcast|axiom|'
    r'proof|exec|default|unsafe|const|async|extern|tracked)\s+)*'
    r'(?:spec\s+)?'
    r'(fn|struct|enum|trait|type|impl|mod|assume_specification)\b'
)


def _net_braces(s: str) -> int:
    """Count net { minus } in a string, ignoring string literal contents.

    We deliberately do NOT track char literals: Rust lifetime annotations ('a,
    'static, '_) look like the start of a char literal to a naive scanner, and
    would cause the closing { of any generic impl/fn with lifetimes to be
    swallowed.  Real char literals that contain { or } ('{'  / '}') are
    vanishingly rare in Verus signatures and spec bodies, so the small risk of
    miscounting them is far outweighed by the correctness gain on lifetimes.
    """
    n, in_s = 0, False
    i = 0
    while i < len(s):
        c = s[i]
        if c == '\\' and in_s:
            i += 2  # skip escaped character inside string literal
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


def _scan_items(lines: list[str], start: int, stop_depth: int) -> tuple[int, list[Item]]:
    """
    Scan lines[start:] and collect items encountered at `stop_depth`.
    Returns (next_line_index, items).

    stop_depth: the brace depth at which items live (1 for inside verus!, 2 for inside impl).
    Items are consumed when brace_depth drops below stop_depth.
    """
    items: list[Item] = []
    i = start
    n = len(lines)
    depth = stop_depth   # we enter already at stop_depth
    doc: list[str] = []

    while i < n:
        line = lines[i]
        stripped = line.strip()

        # ── Track depth changes on non-item lines ─────────────────────────
        # Apply depth changes BEFORE checking for items so that closing }
        # of the enclosing block terminates us.
        delta = _net_braces(stripped)

        # ── Doc comment ───────────────────────────────────────────────────
        if stripped.startswith("///"):
            doc.append(stripped[3:].lstrip())
            i += 1
            continue

        # ── Attribute: keep doc ───────────────────────────────────────────
        if stripped.startswith("#[") or stripped.startswith("#!"):
            i += 1
            continue

        # ── Blank line ───────────────────────────────────────────────────
        if not stripped:
            doc = []
            depth += delta
            i += 1
            continue

        # ── Non-doc comment ───────────────────────────────────────────────
        if stripped.startswith("//"):
            doc = []
            depth += delta
            i += 1
            continue

        # ── Check for item keyword at current depth ───────────────────────
        m = _ITEM_KW_RE.match(line)

        if m and depth == stop_depth:
            kind = m.group(1)
            doc_text = "\n".join(doc)
            doc = []

            # Capture signature: lines from here until we either open a body {
            # (body_opened=True) or end with ; (bodyless spec fn / type alias)
            sig_lines: list[str] = []
            j = i
            sig_depth = depth

            while j < n and len(sig_lines) < 80:
                l = lines[j]
                ls = l.strip()
                sig_depth += _net_braces(ls)
                sig_lines.append(l)
                # Bodyless: ends with ; at the top or one level in
                if re.search(r';\s*$', ls) and sig_depth <= stop_depth + 1:
                    j += 1
                    body_opened = False
                    break
                # Body opened
                if sig_depth > stop_depth:
                    j += 1
                    body_opened = True
                    break
                j += 1
            else:
                body_opened = False

            signature = "\n".join(l.rstrip() for l in sig_lines)

            if kind == "impl" and body_opened:
                # Recurse: parse the impl's children at depth = stop_depth + 1
                depth = sig_depth   # = stop_depth + 1
                j, children = _scan_items(lines, j, depth)
                depth -= 1  # back to stop_depth after impl body consumed
                items.append(Item(kind="impl", signature=signature,
                                  doc=doc_text, children=children))
                i = j
                continue
            else:
                # Update outer depth
                depth = sig_depth
                if body_opened:
                    # Skip function body
                    while j < n and depth > stop_depth:
                        depth += _net_braces(lines[j].strip())
                        j += 1
                i = j
                items.append(Item(kind=kind, signature=signature,
                                  doc=doc_text, children=[]))
                continue

        else:
            # Not an item at our depth — update depth, check for early exit
            doc = []
            depth += delta
            if depth < stop_depth:
                # Closing brace of the enclosing block (e.g. end of impl or verus!)
                i += 1
                break

        i += 1

    return i, items


def parse_source(source: str) -> tuple[str, list[Item]]:
    """
    Parse Rust/Verus source.
    Returns (module_doc, items).
    module_doc: //! module-level doc comment text.
    items: list of Item (including impl blocks with children).
    """
    lines = source.splitlines()
    module_doc_lines: list[str] = []
    all_items: list[Item] = []

    i = 0
    n = len(lines)
    depth = 0
    doc: list[str] = []

    while i < n:
        line = lines[i]
        stripped = line.strip()
        delta = _net_braces(stripped)

        # Module-level doc
        if stripped.startswith("//!"):
            module_doc_lines.append(stripped[3:].lstrip())
            i += 1
            continue

        # Item doc
        if stripped.startswith("///"):
            doc.append(stripped[3:].lstrip())
            i += 1
            continue

        if stripped.startswith("#[") or stripped.startswith("#!"):
            i += 1
            continue

        if not stripped:
            doc = []
            depth += delta
            i += 1
            continue

        if stripped.startswith("//"):
            doc = []
            depth += delta
            i += 1
            continue

        # Check for verus! { or verus_! { — the main content block
        if depth == 0 and re.match(r'verus_?!\s*\{', stripped):
            depth += delta  # depth becomes 1
            i += 1
            # Scan items inside verus! {} at depth 1
            i, items = _scan_items(lines, i, depth)
            all_items.extend(items)
            depth -= 1  # verus! block closed
            continue

        # Top-level items outside verus! (rare in vstd but handle them)
        m = _ITEM_KW_RE.match(line)
        if m and depth == 0:
            kind = m.group(1)
            doc_text = "\n".join(doc)
            doc = []
            sig_lines = [line]
            depth += delta
            j = i + 1
            body_opened = depth > 0
            while not body_opened and j < n and len(sig_lines) < 20:
                l = lines[j]
                ls = l.strip()
                depth += _net_braces(ls)
                sig_lines.append(l)
                if re.search(r';\s*$', ls):
                    j += 1
                    break
                if depth > 0:
                    body_opened = True
                    j += 1
                    break
                j += 1
            if body_opened:
                while j < n and depth > 0:
                    depth += _net_braces(lines[j].strip())
                    j += 1
            i = j
            all_items.append(Item(
                kind=kind,
                signature="\n".join(l.rstrip() for l in sig_lines),
                doc=doc_text,
                children=[],
            ))
            continue

        doc = []
        depth += delta
        i += 1

    return "\n".join(module_doc_lines), all_items


# ---------------------------------------------------------------------------
# Step 3: Render to markdown
# ---------------------------------------------------------------------------

def _dedent(sig: str) -> str:
    """Remove common leading whitespace from a multi-line signature."""
    lines = [l for l in sig.splitlines() if l.strip()]
    if not lines:
        return sig
    indent = min(len(l) - len(l.lstrip()) for l in lines)
    return "\n".join(l[indent:] for l in sig.splitlines()).strip()


def _item_heading(item: Item) -> str:
    """Extract a short display name from an item's first signature line."""
    first = item.signature.lstrip().splitlines()[0] if item.signature else ""
    # assume_specification: name is the target inside [...], e.g. Vec::<T>::len
    if item.kind == "assume_specification":
        m = re.search(r'\[\s*([^\]]+?)\s*\]', first)
        return m.group(1).strip() if m else first[:60].strip()
    m = re.search(r'(?:fn|struct|enum|trait|type|mod)\s+(\w+)', first)
    return m.group(1) if m else first[:60].strip()


def _render_item(item: Item, level: int) -> str:
    hdr = "#" * min(level, 6)
    parts: list[str] = []

    if item.kind == "impl":
        # Impl header — extract the self type for a readable heading
        first = item.signature.lstrip().splitlines()[0]
        m = re.search(r'impl\s*(?:<[^>]*>)?\s+([\w:<>\[\], ]+?)(?:\s+for\s+[\w:<>]+)?\s*\{', first)
        type_name = m.group(1).strip() if m else first.rstrip("{").strip()
        if item.children:
            parts.append(f"\n{hdr} `impl {type_name}`\n")
            for child in item.children:
                parts.append(_render_item(child, level + 1))
    else:
        name = _item_heading(item)
        parts.append(f"\n{hdr} `{name}`\n")
        if item.doc:
            parts.append(item.doc + "\n")
        sig = _dedent(item.signature)
        if sig:
            parts.append(f"```rust\n{sig}\n```\n")

    return "\n".join(parts)


def render_md(module_path: str, module_doc: str, items: list[Item]) -> str:
    lines: list[str] = [f"# vstd::{module_path}\n"]
    if module_doc:
        lines.append(module_doc + "\n")
    for item in items:
        lines.append(_render_item(item, level=2))
    text = "\n".join(lines)
    return re.sub(r"\n{4,}", "\n\n\n", text)


# ---------------------------------------------------------------------------
# Step 4: Walk source tree and write files
# ---------------------------------------------------------------------------

def process_file(src_file: Path, src_root: Path, out_root: Path) -> bool:
    html = src_file.read_text(encoding="utf-8")
    source = extract_source(html)
    if not source.strip():
        return False

    module_doc, items = parse_source(source)
    if not items and not module_doc:
        return False

    # Output path: seq.rs.html → seq.md;  arithmetic/div_mod.rs.html → arithmetic/div_mod.md
    rel = src_file.relative_to(src_root)
    parts = list(rel.parts)
    parts[-1] = re.sub(r'\.rs\.html$', '.md', parts[-1])
    out_file = out_root / Path(*parts)
    out_file.parent.mkdir(parents=True, exist_ok=True)

    # Module path for heading: arithmetic/div_mod → arithmetic::div_mod
    mod_parts = list(rel.parts)
    mod_parts[-1] = re.sub(r'\.rs\.html$', '', mod_parts[-1])
    module_path = "::".join(mod_parts)

    out_file.write_text(render_md(module_path, module_doc, items), encoding="utf-8")
    return True


def main() -> None:
    parser = argparse.ArgumentParser(description="Convert vstd source HTML to markdown")
    parser.add_argument("--input", default=None,
                        help="Path to vstd source HTML dir (default: /tmp/vstd-raw-{VERSION}/src/vstd, requires --version)")
    parser.add_argument("--version", default=None,
                        help="vstd version string (used to derive default --input and --output paths)")
    parser.add_argument(
        "--output", default=None,
        help="Output directory (default: /tmp/vstd-md-{VERSION})",
    )
    args = parser.parse_args()

    # Resolve input path
    if args.input:
        src_root = Path(args.input)
    elif args.version:
        src_root = Path(f"/tmp/vstd-raw-{args.version}/src/vstd")
    else:
        # Fall back to reading version from a VERSION file if it exists
        version_file = Path("/tmp/vstd-raw/VERSION")
        if version_file.exists():
            version = version_file.read_text(encoding="utf-8").strip()
            src_root = Path(f"/tmp/vstd-raw-{version}/src/vstd")
        else:
            print("Error: supply --input or --version", file=sys.stderr)
            sys.exit(1)

    if not src_root.exists():
        print(f"Error: input path not found: {src_root}", file=sys.stderr)
        sys.exit(1)

    # Resolve output path
    if args.output:
        out_root = Path(args.output)
    elif args.version:
        out_root = Path(f"/tmp/vstd-md-{args.version}")
        print(f"  vstd version: {args.version}", file=sys.stderr)
        print(f"  Output:       {out_root}", file=sys.stderr)
    else:
        version_file = src_root.parent.parent / "VERSION"
        if not version_file.exists():
            print(
                f"Error: cannot auto-detect output path: {version_file} not found.\n"
                f"Supply --output explicitly.",
                file=sys.stderr,
            )
            sys.exit(1)
        version = version_file.read_text(encoding="utf-8").strip()
        out_root = Path(f"/tmp/vstd-md-{version}")
        print(f"  vstd version: {version}", file=sys.stderr)
        print(f"  Output:       {out_root}", file=sys.stderr)

    out_root.mkdir(parents=True, exist_ok=True)

    src_files = sorted(src_root.rglob("*.rs.html"))
    # Skip internals (deep implementation details)
    src_files = [f for f in src_files if "internals" not in f.parts]

    print(f"  Processing {len(src_files)} source files ...", file=sys.stderr)
    written = 0
    for idx, src_file in enumerate(src_files, 1):
        rel = src_file.relative_to(src_root)
        print(f"  [{idx}/{len(src_files)}] {rel}           ", file=sys.stderr, end="\r")
        if process_file(src_file, src_root, out_root):
            written += 1

    out_files = list(out_root.rglob("*.md"))
    print(f"\n  Done: {written} files written to {out_root}  ({len(out_files)} .md total)",
          file=sys.stderr)


if __name__ == "__main__":
    main()
