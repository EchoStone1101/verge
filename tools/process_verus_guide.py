#!/usr/bin/env python3
"""
Post-process the verus-guide markdown files to make them usable by an offline agent.

Three transformations are applied to every .md file under third-party/verus-guide/:

1. Resolve {{#include}} directives
   - {{#include ./local.md}}            – inline local markdown file
   - {{#include ../../../../path.rs[:anchor]}} – fetch from GitHub main branch and
     inline the named anchor section (or the whole file if no anchor is given).
     All // ANCHOR: / // ANCHOR_END: comment lines are stripped from the output.

2. Strip external URLs from hyperlinks
   [text](https://...)  →  [text]
   Exception: links whose URL resolves to a local guide page are converted instead
   (see rule 3 below).

3. Fix non-local links that should be local
   - Local-looking links with .html extension → .md
     [text](foo.html#anchor)  →  [text](foo.md#anchor)
   - Links to https://verus-lang.github.io/verus/guide/page.html
     → [text](./page.md)

Usage:
    # Preferred: use a local verus checkout (fast, no network)
    python3 tools/process_verus_guide.py \\
        --verus-repo /path/to/verus \\
        [--guide     third-party/verus-guide] \\
        [--dry-run]

    # Fallback: fetch source files from GitHub
    python3 tools/process_verus_guide.py \\
        [--guide   third-party/verus-guide] \\
        [--branch  main]                    \\
        [--dry-run]
"""

import argparse
import asyncio
import re
import sys
from pathlib import Path

try:
    import aiohttp
except ImportError:
    print("aiohttp required: pip install aiohttp", file=sys.stderr)
    sys.exit(1)

VERUS_RAW = "https://raw.githubusercontent.com/verus-lang/verus/{branch}/{path}"
ANCHOR_RE = re.compile(r"^\s*//\s*ANCHOR(_END)?:\s*([\w-]+)\s*$")


# ---------------------------------------------------------------------------
# Anchor extraction
# ---------------------------------------------------------------------------

def extract_anchor(source: str, anchor: str) -> str | None:
    """Return the text of the named anchor section, with all anchor comment lines removed."""
    lines = source.splitlines()
    result: list[str] = []
    inside = False
    found = False
    for line in lines:
        m = ANCHOR_RE.match(line)
        if m:
            is_end, name = bool(m.group(1)), m.group(2)
            if name == anchor:
                inside = not is_end
                if not is_end:
                    found = True
            # Skip ALL anchor comment lines from output
            continue
        if inside:
            result.append(line)
    if not found:
        return None
    return "\n".join(result)


def strip_anchors(source: str) -> str:
    """Return the source with all anchor comment lines removed (whole-file include)."""
    lines = source.splitlines()
    return "\n".join(l for l in lines if not ANCHOR_RE.match(l))


# ---------------------------------------------------------------------------
# Source file loading — local repo first, GitHub fallback
# ---------------------------------------------------------------------------

def load_sources_local(
    paths: set[str],
    verus_repo: Path,
) -> dict[str, str | None]:
    """Read source files from a local verus checkout. Returns {path: content | None}."""
    results: dict[str, str | None] = {}
    for path in paths:
        local = verus_repo / path
        if local.exists():
            results[path] = local.read_text(encoding="utf-8")
        else:
            results[path] = None
    found = sum(1 for v in results.values() if v is not None)
    print(f"  Local repo: {found}/{len(paths)} found in {verus_repo}", file=sys.stderr)
    return results


async def fetch_sources_github(
    paths: set[str],
    branch: str,
    session: aiohttp.ClientSession,
) -> dict[str, str | None]:
    """Fetch source file paths from GitHub. Returns {path: content | None}."""
    results: dict[str, str | None] = {}

    async def fetch_one(path: str) -> None:
        url = VERUS_RAW.format(branch=branch, path=path)
        try:
            async with session.get(url, timeout=aiohttp.ClientTimeout(total=30)) as resp:
                if resp.status == 200:
                    results[path] = await resp.text()
                else:
                    print(f"  WARNING: {resp.status} fetching {url}", file=sys.stderr)
                    results[path] = None
        except Exception as e:
            print(f"  WARNING: error fetching {url}: {e}", file=sys.stderr)
            results[path] = None

    await asyncio.gather(*[fetch_one(p) for p in paths])
    return results


# ---------------------------------------------------------------------------
# Link transformations
# ---------------------------------------------------------------------------

def _strip_external_url(m: re.Match) -> str:
    """Replace [text](https://...) with [text], except for convertible guide links."""
    text = m.group(1)
    url  = m.group(2)

    # Verus guide web link → local .md link
    guide_m = re.match(
        r"https://verus-lang\.github\.io/verus/guide/([^#)]+?)(?:\.html)?([^)]*)", url
    )
    if guide_m:
        page    = guide_m.group(1)  # e.g. "multitriggers"
        anchor  = guide_m.group(2)  # e.g. "#section" or ""
        return f"[{text}](./{page}.md{anchor})"

    # All other external links: keep text, drop URL
    return f"[{text}]"


def fix_html_links(text: str) -> str:
    """Convert [text](local.html#anchor) → [text](local.md#anchor)."""
    # Only local-looking hrefs (no scheme, no authority)
    def _replace(m: re.Match) -> str:
        link_text = m.group(1)
        href      = m.group(2)
        new_href  = re.sub(r"\.html(#|$)", r".md\1", href)
        return f"[{link_text}]({new_href})"
    return re.sub(r"\[([^\]]*)\]\(([^)]*\.html[^)]*)\)", _replace, text)


def process_links(text: str) -> str:
    """Strip external URLs and fix .html local links."""
    # External https?:// links (handles verus guide → local conversion too)
    text = re.sub(r"\[([^\]]*)\]\((https?://[^)]+)\)", _strip_external_url, text)
    # Remaining local .html links
    text = fix_html_links(text)
    return text


# ---------------------------------------------------------------------------
# {{#include}} resolution
# ---------------------------------------------------------------------------

INCLUDE_RE = re.compile(r"\{\{#include ([^}]+)\}\}")


def resolve_includes(
    text: str,
    md_file: Path,
    guide_dir: Path,
    sources: dict[str, str | None],
) -> tuple[str, int, int]:
    """
    Replace all {{#include ...}} directives in text.
    Returns (new_text, resolved_count, failed_count).
    """
    resolved = failed = 0

    def replace(m: re.Match) -> str:
        nonlocal resolved, failed
        arg = m.group(1).strip()

        # ── Local markdown include ────────────────────────────────────────
        if arg.startswith("./") and arg.endswith(".md"):
            local_path = (md_file.parent / arg).resolve()
            try:
                content = local_path.read_text(encoding="utf-8")
                resolved += 1
                return content.rstrip()
            except FileNotFoundError:
                print(f"  WARNING: local include not found: {local_path}", file=sys.stderr)
                failed += 1
                return m.group(0)  # leave unchanged

        # ── GitHub source include ─────────────────────────────────────────
        if ":" in arg.split("/")[-1]:
            file_part, anchor = arg.rsplit(":", 1)
        else:
            file_part, anchor = arg, None

        # Strip leading ../../../../ to get the repo-relative path
        rel_path = re.sub(r"^(?:\.\./)+" , "", file_part)

        if rel_path not in sources or sources[rel_path] is None:
            print(f"  WARNING: source not fetched: {rel_path}", file=sys.stderr)
            failed += 1
            return f"// [source not available: {rel_path}]"

        source = sources[rel_path]
        if anchor:
            code = extract_anchor(source, anchor)
            if code is None:
                print(
                    f"  WARNING: anchor {anchor!r} not found in {rel_path}",
                    file=sys.stderr,
                )
                failed += 1
                return f"// [anchor '{anchor}' not found in {rel_path}]"
        else:
            code = strip_anchors(source)

        resolved += 1
        return code.rstrip()

    new_text = INCLUDE_RE.sub(replace, text)
    return new_text, resolved, failed


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

async def process_guide(
    guide_dir: Path,
    branch: str,
    dry_run: bool,
    verus_repo: Path | None,
) -> None:
    md_files = sorted(guide_dir.glob("*.md"))
    print(f"  Guide directory: {guide_dir}  ({len(md_files)} .md files)", file=sys.stderr)

    # Collect all source paths needed
    needed_paths: set[str] = set()
    for md_file in md_files:
        text = md_file.read_text(encoding="utf-8")
        for m in INCLUDE_RE.finditer(text):
            arg = m.group(1).strip()
            if arg.startswith("./"):
                continue  # local markdown — no fetch needed
            file_part = arg.rsplit(":", 1)[0] if ":" in arg.split("/")[-1] else arg
            rel_path = re.sub(r"^(?:\.\./)+" , "", file_part)
            needed_paths.add(rel_path)

    if verus_repo is not None:
        # Preferred: read from local checkout
        sources = load_sources_local(needed_paths, verus_repo)
        # Fall back to GitHub for anything not found locally
        missing = {p for p, v in sources.items() if v is None}
        if missing:
            print(f"  Fetching {len(missing)} missing files from GitHub ({branch}) ...",
                  file=sys.stderr)
            async with aiohttp.ClientSession() as session:
                github = await fetch_sources_github(missing, branch, session)
            sources.update(github)
    else:
        print(f"  Fetching {len(needed_paths)} source files from GitHub ({branch}) ...",
              file=sys.stderr)
        async with aiohttp.ClientSession() as session:
            sources = await fetch_sources_github(needed_paths, branch, session)

    ok = sum(1 for v in sources.values() if v is not None)
    print(f"  Sources available: {ok}/{len(needed_paths)}", file=sys.stderr)

    total_resolved = total_failed = 0
    files_changed = 0

    for md_file in md_files:
        original = md_file.read_text(encoding="utf-8")
        text = original

        # 1. Resolve {{#include}} directives
        text, res, fail = resolve_includes(text, md_file, guide_dir, sources)
        total_resolved += res
        total_failed   += fail

        # 2. Fix links
        text = process_links(text)

        if text != original:
            files_changed += 1
            if not dry_run:
                md_file.write_text(text, encoding="utf-8")
            else:
                print(f"  [dry-run] would modify {md_file.name}", file=sys.stderr)

    action = "Would modify" if dry_run else "Modified"
    print(
        f"\n  Done: {action} {files_changed}/{len(md_files)} files | "
        f"{total_resolved} includes resolved | {total_failed} failed",
        file=sys.stderr,
    )


def main() -> None:
    parser = argparse.ArgumentParser(description="Post-process verus-guide markdown")
    parser.add_argument("--guide",      default="third-party/verus-guide",
                        help="Path to verus-guide directory (default: third-party/verus-guide)")
    parser.add_argument("--verus-repo", default=None,
                        help="Path to a local verus repository checkout; source files are "
                             "read from disk instead of fetched from GitHub (faster and "
                             "allows offline use). Falls back to GitHub for missing files.")
    parser.add_argument("--branch",     default="main",
                        help="GitHub branch to fetch from if not using --verus-repo "
                             "(default: main)")
    parser.add_argument("--dry-run",    action="store_true",
                        help="Report what would change without modifying files")
    args = parser.parse_args()

    guide_dir = Path(args.guide)
    if not guide_dir.is_dir():
        print(f"Error: guide directory not found: {guide_dir}", file=sys.stderr)
        sys.exit(1)

    verus_repo: Path | None = None
    if args.verus_repo:
        verus_repo = Path(args.verus_repo)
        if not verus_repo.is_dir():
            print(f"Error: verus repo not found: {verus_repo}", file=sys.stderr)
            sys.exit(1)
        print(f"  Using local repo: {verus_repo}", file=sys.stderr)

    asyncio.run(process_guide(guide_dir, args.branch, args.dry_run, verus_repo))


if __name__ == "__main__":
    main()
