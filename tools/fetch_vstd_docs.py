#!/usr/bin/env python3
"""
Crawl vstd SOURCE HTML from the Verus team's docs site and save it locally
under third-party/vstd-raw/src/vstd/, organized by module.

Note: the docs site always serves the latest vstd version; there is no
per-version URL structure.

Strategy: the docs site has no src/vstd/index.html.  Instead we crawl the
rendered API pages (vstd/), collect every *.rs.html source link they contain,
then fetch those source files.  Only source files (*.rs.html) are saved; the
API pages are used purely for link discovery.

Layout produced:
    third-party/vstd-raw/src/vstd/
    ├── seq.rs.html
    ├── arithmetic/
    │   ├── div_mod.rs.html
    │   └── ...
    ├── std_specs/
    │   └── ...
    └── ...

Usage:
    python3 tools/fetch_vstd_docs.py [--output third-party/vstd-raw/src/vstd] [--concurrency 8]
"""

import argparse
import asyncio
import re
import sys
import time
from pathlib import Path
from urllib.parse import urljoin

try:
    import aiohttp
except ImportError:
    print("aiohttp required: pip install aiohttp", file=sys.stderr)
    sys.exit(1)

# Verus team's hosted docs site (has std_specs; docs.rs does not).
BASE_API_URL = "https://verus-lang.github.io/verus/verusdoc/vstd/"
BASE_SRC_URL = "https://verus-lang.github.io/verus/verusdoc/src/vstd/"


def _is_api_page(url: str) -> bool:
    return url.startswith(BASE_API_URL) and url.endswith(".html")


def _is_source_page(url: str) -> bool:
    return url.startswith(BASE_SRC_URL) and url.endswith(".rs.html")


def _src_rel_path(url: str) -> str:
    """Strip the BASE_SRC_URL prefix to get the relative save path."""
    return url[len(BASE_SRC_URL):]


def discover_links(html: str, page_url: str) -> tuple[list[str], list[str]]:
    """
    Return (api_links, source_links) extracted from an HTML page.
    api_links:    rendered API pages to continue crawling for more source links
    source_links: *.rs.html source files to fetch and save
    """
    api_links: list[str] = []
    src_links: list[str] = []
    for m in re.finditer(r'href="([^"#][^"]*)"', html):
        href = m.group(1).split("?")[0].split("#")[0]
        full = urljoin(page_url, href)
        if _is_source_page(full):
            src_links.append(full)
        elif _is_api_page(full):
            api_links.append(full)
    return api_links, src_links


async def fetch_page(
    session: aiohttp.ClientSession,
    url: str,
    sema: asyncio.Semaphore,
    retries: int = 3,
) -> tuple[str, str | None]:
    """Fetch a URL; return (url, html_text) or (url, None) on failure."""
    for attempt in range(retries):
        try:
            async with sema:
                async with session.get(url, timeout=aiohttp.ClientTimeout(total=30)) as resp:
                    if resp.status == 200:
                        return url, await resp.text()
                    elif resp.status == 404:
                        return url, None
                    else:
                        await asyncio.sleep(1)
        except Exception as e:
            if attempt == retries - 1:
                print(f"  ERROR fetching {url}: {e}", file=sys.stderr)
                return url, None
            await asyncio.sleep(1)
    return url, None


async def crawl(output_dir: str, concurrency: int) -> None:
    output_path = Path(output_dir)
    output_path.mkdir(parents=True, exist_ok=True)

    api_visited: set[str] = set()
    src_queued: set[str] = set()
    api_queue: list[str] = [BASE_API_URL + "index.html"]

    sema = asyncio.Semaphore(concurrency)
    saved = 0
    failed = 0
    start = time.time()

    async with aiohttp.ClientSession() as session:
        # Phase 1: crawl API pages to discover all source file links
        while api_queue:
            batch = []
            for url in api_queue:
                if url not in api_visited:
                    api_visited.add(url)
                    batch.append(url)
            api_queue = []

            if not batch:
                break

            print(
                f"  [API] Fetching {len(batch)} pages "
                f"(visited: {len(api_visited)}, source files queued: {len(src_queued)}) ...",
                file=sys.stderr,
            )
            results = await asyncio.gather(
                *[fetch_page(session, url, sema) for url in batch]
            )
            for url, html in results:
                if html is None:
                    continue
                new_api, new_src = discover_links(html, url)
                for link in new_api:
                    if link not in api_visited:
                        api_queue.append(link)
                src_queued.update(new_src)

        # Phase 2: fetch and save all discovered source files
        src_list = sorted(src_queued)
        print(
            f"\n  [SRC] Fetching {len(src_list)} source files ...",
            file=sys.stderr,
        )
        results = await asyncio.gather(
            *[fetch_page(session, url, sema) for url in src_list]
        )
        for url, html in results:
            if html is None:
                failed += 1
                continue
            rel = _src_rel_path(url)
            dest = output_path / rel
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_text(html, encoding="utf-8")
            saved += 1

    elapsed = time.time() - start
    print(
        f"\n  Done: {saved} source files saved, {failed} failed, {elapsed:.1f}s",
        file=sys.stderr,
    )

    dirs = sorted({p.parent.name for p in output_path.rglob("*.rs.html") if p.parent != output_path})
    print(f"  Modules: {', '.join(dirs) or '(none)'}", file=sys.stderr)


def main() -> None:
    parser = argparse.ArgumentParser(description="Crawl vstd source HTML from verus-lang.github.io")
    parser.add_argument(
        "--output", default="third-party/vstd-raw/src/vstd",
        help="Output directory for source HTML (default: third-party/vstd-raw/src/vstd)",
    )
    parser.add_argument(
        "--concurrency", type=int, default=8,
        help="Max concurrent HTTP requests (default: 8)",
    )
    args = parser.parse_args()

    print(f"Crawling vstd source HTML from {BASE_API_URL}", file=sys.stderr)
    print(f"  Output:      {args.output}", file=sys.stderr)
    print(f"  Concurrency: {args.concurrency}", file=sys.stderr)
    print(file=sys.stderr)

    asyncio.run(crawl(args.output, args.concurrency))


if __name__ == "__main__":
    main()
