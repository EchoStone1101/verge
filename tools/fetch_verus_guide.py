#!/usr/bin/env python3
"""
Download the Verus guide markdown files from GitHub and save them under
third-party/verus-guide/, then generate a TABLE_OF_CONTENTS.md from SUMMARY.md.

Source: https://github.com/verus-lang/verus/tree/main/source/docs/guide/src

Usage:
    python3 tools/fetch_verus_guide.py [--output third-party/verus-guide] [--concurrency 8]
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

RAW_BASE = "https://raw.githubusercontent.com/verus-lang/verus/main/source/docs/guide/src/"
API_BASE = "https://api.github.com/repos/verus-lang/verus/contents/source/docs/guide/src"


# ---------------------------------------------------------------------------
# Fetch file list from GitHub API
# ---------------------------------------------------------------------------

async def list_md_files(session: aiohttp.ClientSession) -> list[str]:
    """Return list of .md filenames in the guide/src directory."""
    async with session.get(API_BASE, timeout=aiohttp.ClientTimeout(total=30)) as resp:
        resp.raise_for_status()
        items = await resp.json()
    return [i["name"] for i in items if i["type"] == "file" and i["name"].endswith(".md")]


# ---------------------------------------------------------------------------
# Download files
# ---------------------------------------------------------------------------

async def fetch_file(
    session: aiohttp.ClientSession,
    filename: str,
    sema: asyncio.Semaphore,
    retries: int = 3,
) -> tuple[str, str | None]:
    url = RAW_BASE + filename
    for attempt in range(retries):
        try:
            async with sema:
                async with session.get(url, timeout=aiohttp.ClientTimeout(total=30)) as resp:
                    if resp.status == 200:
                        return filename, await resp.text()
                    elif resp.status == 404:
                        return filename, None
                    await asyncio.sleep(1)
        except Exception as e:
            if attempt == retries - 1:
                print(f"  ERROR {filename}: {e}", file=sys.stderr)
                return filename, None
            await asyncio.sleep(1)
    return filename, None


# ---------------------------------------------------------------------------
# Build TABLE_OF_CONTENTS.md from SUMMARY.md
# ---------------------------------------------------------------------------

def build_toc(summary_text: str) -> str:
    """
    Convert mdBook SUMMARY.md into a clean TABLE_OF_CONTENTS.md.

    The TOC tells the agent:
    - What chapters exist and how they're organized
    - The filename to read for each chapter
    - One-line description (the chapter title)
    """
    lines = summary_text.splitlines()
    toc_lines = [
        "# Verus Guide — Table of Contents",
        "",
        "Read this file first to decide which chapter to read.",
        "Each entry: `chapter title → filename`",
        "All files are in the same directory as this file.",
        "",
    ]

    current_section = None

    for line in lines:
        stripped = line.strip()

        # Skip empty lines and comment-only entries like []() <!--- --->
        if not stripped or re.match(r'\[.*?\]\(\s*\)', stripped):
            continue

        # Top-level section headers (# Header)
        if re.match(r'^#+\s+', stripped) and not stripped.startswith('#['):
            header = re.sub(r'^#+\s+', '', stripped)
            if header.lower() != 'summary':
                toc_lines.append(f"\n## {header}\n")
                current_section = header
            continue

        # Standalone link (no list marker) — like [Verus overview](./overview.md)
        m_standalone = re.match(r'^\[([^\]]+)\]\(\.?/?([^)]+)\)', stripped)
        if m_standalone and not stripped.startswith('-'):
            title = m_standalone.group(1)
            path = m_standalone.group(2).lstrip('./')
            if path.endswith('.md'):
                toc_lines.append(f"- **{title}** → `{path}`")
            continue

        # List item: - [Title](file.md) or   - [Title](file.md) (indented)
        m_item = re.match(r'^(-\s+)\[([^\]]+)\]\(\.?/?([^)]+)\)', stripped)
        if m_item:
            title = m_item.group(2)
            path = m_item.group(3).lstrip('./')
            # Compute indent level from original line
            indent_len = len(line) - len(line.lstrip())
            indent = "  " * (indent_len // 2)
            if path.endswith('.md'):
                toc_lines.append(f"{indent}- **{title}** → `{path}`")
            continue

        # Section divider or other header
        if stripped.startswith('#'):
            toc_lines.append(f"\n## {stripped.lstrip('#').strip()}\n")

    toc_lines.append("")
    toc_lines.append("---")
    toc_lines.append("*Files are plain markdown — read them directly with your Read tool.*")
    toc_lines.append("")

    return "\n".join(toc_lines)


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

async def run(output_dir: str, concurrency: int) -> None:
    out = Path(output_dir)
    out.mkdir(parents=True, exist_ok=True)

    sema = asyncio.Semaphore(concurrency)

    async with aiohttp.ClientSession() as session:
        print("  Listing files from GitHub API ...", file=sys.stderr)
        filenames = await list_md_files(session)
        print(f"  Found {len(filenames)} .md files", file=sys.stderr)

        tasks = [fetch_file(session, fn, sema) for fn in filenames]
        results = await asyncio.gather(*tasks)

    saved, failed = 0, 0
    summary_text = None

    for filename, content in results:
        if content is None:
            failed += 1
            continue
        (out / filename).write_text(content, encoding="utf-8")
        saved += 1
        if filename == "SUMMARY.md":
            summary_text = content

    print(f"  Saved {saved} files, {failed} failed", file=sys.stderr)

    # Build TABLE_OF_CONTENTS.md
    if summary_text:
        toc = build_toc(summary_text)
        toc_file = out / "TABLE_OF_CONTENTS.md"
        toc_file.write_text(toc, encoding="utf-8")
        print(f"  Wrote TABLE_OF_CONTENTS.md", file=sys.stderr)
    else:
        print("  WARNING: SUMMARY.md not found, skipping TOC", file=sys.stderr)


def main() -> None:
    parser = argparse.ArgumentParser(description="Download Verus guide markdown files")
    parser.add_argument("--output", default="third-party/verus-guide",
                        help="Output directory (default: third-party/verus-guide)")
    parser.add_argument("--concurrency", type=int, default=8,
                        help="Max concurrent downloads (default: 8)")
    args = parser.parse_args()

    print(f"Fetching Verus guide to {args.output} ...", file=sys.stderr)
    asyncio.run(run(args.output, args.concurrency))


if __name__ == "__main__":
    main()
