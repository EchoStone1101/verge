#!/usr/bin/env python3
"""
Produce a source-level diff between two vstd versions.

For each version:
  1. Download the crate tarball from crates.io into /tmp/vstd-src-{VERSION}/
     (skipped if already present unless --force)
  2. Convert .rs source files to markdown using the generate_vstd_md pipeline

Then diff the two markdown trees and print the unified diff to stdout.

Usage:
    python3 tools/vstd_diff.py VERSION_A VERSION_B [--concurrency 8] [--force]

    --force   re-download and re-generate even if cached data exists
"""

import argparse
import io
import sys
import tarfile
import urllib.request
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import generate_vstd_md
import difflib


CRATES_IO_URL = "https://static.crates.io/crates/vstd/{version}/download"


def fetch_if_needed(version: str, force: bool) -> Path:
    src_dir = Path(f"/tmp/vstd-src-{version}")
    if src_dir.exists() and any(src_dir.rglob("*.rs")) and not force:
        print(f"[{version}] Using cached source in {src_dir}", file=sys.stderr)
        return src_dir

    url = CRATES_IO_URL.format(version=version)
    print(f"[{version}] Downloading crate tarball from crates.io ...", file=sys.stderr)
    with urllib.request.urlopen(url) as resp:
        data = resp.read()

    print(f"[{version}] Extracting src/*.rs files ...", file=sys.stderr)
    src_dir.mkdir(parents=True, exist_ok=True)
    with tarfile.open(fileobj=io.BytesIO(data), mode="r:gz") as tar:
        for member in tar.getmembers():
            # tarball root is vstd-{version}/src/...
            # strip the leading vstd-{version}/ prefix
            parts = Path(member.name).parts
            if len(parts) < 2:
                continue
            rel = Path(*parts[1:])  # strip crate root dir
            if not member.isfile():
                continue
            if rel.suffix != ".rs":
                continue
            dest = src_dir / rel
            dest.parent.mkdir(parents=True, exist_ok=True)
            f = tar.extractfile(member)
            if f:
                dest.write_bytes(f.read())

    count = len(list(src_dir.rglob("*.rs")))
    print(f"[{version}] Extracted {count} .rs files to {src_dir}", file=sys.stderr)
    return src_dir


def generate_if_needed(version: str, src_dir: Path, force: bool) -> Path:
    md_dir = Path(f"/tmp/vstd-md-{version}")
    if md_dir.exists() and any(md_dir.rglob("*.md")) and not force:
        print(f"[{version}] Using cached markdown in {md_dir}", file=sys.stderr)
        return md_dir

    print(f"[{version}] Generating markdown ...", file=sys.stderr)
    # The generate_vstd_md pipeline expects *.rs.html files, but we have *.rs.
    # We'll call parse_source / render_md directly on .rs text.
    md_dir.mkdir(parents=True, exist_ok=True)

    rs_files = sorted(src_dir.rglob("*.rs"))
    rs_files = [f for f in rs_files if "internals" not in f.parts]
    written = 0
    for idx, rs_file in enumerate(rs_files, 1):
        rel = rs_file.relative_to(src_dir)
        print(f"  [{idx}/{len(rs_files)}] {rel}           ", file=sys.stderr, end="\r")

        source = rs_file.read_text(encoding="utf-8", errors="replace")
        if not source.strip():
            continue

        module_doc, items = generate_vstd_md.parse_source(source)
        if not items and not module_doc:
            continue

        # Output path: src/seq.rs → seq.md;  src/arithmetic/div_mod.rs → arithmetic/div_mod.md
        parts = list(rel.parts)
        # strip leading "src/" if present
        if parts and parts[0] == "src":
            parts = parts[1:]
        parts[-1] = parts[-1].removesuffix(".rs") + ".md"
        out_file = md_dir / Path(*parts)
        out_file.parent.mkdir(parents=True, exist_ok=True)

        mod_parts = list(parts)
        mod_parts[-1] = mod_parts[-1].removesuffix(".md")
        module_path = "::".join(mod_parts)

        out_file.write_text(
            generate_vstd_md.render_md(module_path, module_doc, items),
            encoding="utf-8",
        )
        written += 1

    print(f"\n[{version}] Done: {written} markdown files in {md_dir}", file=sys.stderr)
    return md_dir


def collect_md_files(md_dir: Path) -> dict[str, str]:
    return {
        str(f.relative_to(md_dir)): f.read_text(encoding="utf-8")
        for f in sorted(md_dir.rglob("*.md"))
    }


def write_diffs(ver_a: str, ver_b: str, files_a: dict, files_b: dict, out_dir: Path) -> int:
    """Write per-file diffs to out_dir. Returns number of files written."""
    written = 0
    for key in sorted(set(files_a) | set(files_b)):
        text_a = files_a.get(key, "")
        text_b = files_b.get(key, "")
        if text_a == text_b:
            continue
        diff = "".join(difflib.unified_diff(
            text_a.splitlines(keepends=True),
            text_b.splitlines(keepends=True),
            fromfile=f"{ver_a}/{key}",
            tofile=f"{ver_b}/{key}",
        ))
        out_file = out_dir / key
        out_file.parent.mkdir(parents=True, exist_ok=True)
        out_file.write_text(diff, encoding="utf-8")
        written += 1
    return written


def main() -> None:
    parser = argparse.ArgumentParser(description="Diff vstd source between two versions")
    parser.add_argument("version_a", help="First vstd version string")
    parser.add_argument("version_b", help="Second vstd version string")
    parser.add_argument("--force", action="store_true",
                        help="Re-download and re-generate even if cached data exists")
    args = parser.parse_args()

    for version in (args.version_a, args.version_b):
        src_dir = fetch_if_needed(version, args.force)
        generate_if_needed(version, src_dir, args.force)

    print("\nCollecting markdown files ...", file=sys.stderr)
    files_a = collect_md_files(Path(f"/tmp/vstd-md-{args.version_a}"))
    files_b = collect_md_files(Path(f"/tmp/vstd-md-{args.version_b}"))
    print(f"  {args.version_a}: {len(files_a)} files", file=sys.stderr)
    print(f"  {args.version_b}: {len(files_b)} files", file=sys.stderr)
    print("\nComputing diff ...", file=sys.stderr)

    out_dir = Path(f"/tmp/vstd-diff-{args.version_a}--{args.version_b}")
    if out_dir.exists():
        import shutil
        shutil.rmtree(out_dir)
    written = write_diffs(args.version_a, args.version_b, files_a, files_b, out_dir)
    if written:
        print(f"  {written} changed files written to {out_dir}", file=sys.stderr)
    else:
        print("  (no differences found)", file=sys.stderr)


if __name__ == "__main__":
    main()
