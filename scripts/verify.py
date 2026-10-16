#!/usr/bin/env python3
"""Check the packaged sources, then build and inspect final Lean axioms."""
from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
PROJECTS = {
    "codex": ("lean/CanonicalDet49LiftComplete.lean", "Conway99.graph_minimal_article_theorem"),
    "opus": ("Conway99Audit/CheckAll.lean", "Conway99.theorem_1_1"),
}


def lean_sources() -> list[Path]:
    return sorted([
        *(ROOT / "codex/lean").rglob("*.lean"),
        *(ROOT / "opus/Conway99Audit").rglob("*.lean"),
        ROOT / "opus/Conway99Audit.lean",
    ])


def without_comments(source: str) -> str:
    """Remove line and nested block comments without treating strings as comments."""
    out: list[str] = []
    i, depth, in_string = 0, 0, False
    while i < len(source):
        pair = source[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                i += 2
            elif pair == "-/":
                depth -= 1
                i += 2
            else:
                out.append("\n" if source[i] == "\n" else " ")
                i += 1
        elif in_string:
            out.append(source[i])
            if source[i] == "\\" and i + 1 < len(source):
                out.append(source[i + 1])
                i += 2
            else:
                if source[i] == '"':
                    in_string = False
                i += 1
        elif pair == "/-":
            depth = 1
            out.append(" ")
            i += 2
        elif pair == "--":
            end = source.find("\n", i)
            i = len(source) if end == -1 else end
        else:
            in_string = source[i] == '"'
            out.append(source[i])
            i += 1
    if depth:
        raise ValueError("Unterminated block comment")
    return "".join(out)


def check_sources() -> None:
    recorded: set[str] = set()
    for line in (ROOT / "verification/sources.sha256").read_text(encoding="utf-8").splitlines():
        if not line or line.startswith("#"):
            continue
        expected, relative = line.split("  ", 1)
        path = (ROOT / relative).resolve()
        if not path.is_relative_to(ROOT) or not path.is_file():
            raise ValueError(f"Invalid manifest path: {relative}")
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        if actual != expected:
            raise ValueError(f"Source hash mismatch: {relative}")
        recorded.add(relative)
    forbidden = re.compile(
        r"\b(?:sorry|admit|native_decide|unsafe|implemented_by|ofReduceBool|trustCompiler)\b"
        r"|^\s*(?:axiom|opaque)\b|skipKernel", re.MULTILINE,
    )
    sources = lean_sources()
    for path in sources:
        relative = path.relative_to(ROOT).as_posix()
        if relative not in recorded:
            raise ValueError(f"Unrecorded Lean source: {relative}")
        match = forbidden.search(without_comments(path.read_text(encoding="utf-8-sig")))
        if match:
            raise ValueError(f"Forbidden proof construct in {relative}: {match.group().strip()}")
    print(f"Integrity verified for {len(recorded)} files; proof-policy scan passed for {len(sources)} Lean sources.")
    print("Source checks alone are not Lean proof verification.")


def check_axioms(output: str, theorem: str | None = None) -> int:
    if re.search(r"sorryAx|Lean\.(?:ofReduceBool|trustCompiler)", output):
        raise ValueError("Unaccepted trusted shortcut in Lean output")
    lists = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", output)
    for raw in lists:
        axioms = {name.strip() for name in raw.split(",") if name.strip()}
        if not axioms <= ALLOWED_AXIOMS:
            raise ValueError(f"Unexpected axioms: {sorted(axioms - ALLOWED_AXIOMS)}")
    if theorem and not re.search(r"'" + re.escape(theorem) + r"'\s+depends on axioms:", output):
        raise ValueError(f"Missing final-theorem axiom check: {theorem}")
    return len(lists)


def run(project: str, args: list[str], log) -> str:
    print(f"[{project}] {' '.join(args)}", flush=True)
    result = subprocess.run(args, cwd=ROOT / project, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True, encoding="utf-8", errors="replace")
    log.write("$ " + " ".join(args) + "\n" + result.stdout + "\n")
    log.flush()
    if result.returncode:
        print(result.stdout[-12000:], file=sys.stderr)
        raise RuntimeError(f"Command failed with exit {result.returncode}; see {log.name}")
    check_axioms(result.stdout)
    return result.stdout


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", choices=[*PROJECTS, "all"], default="all")
    parser.add_argument("--source-only", action="store_true")
    parser.add_argument("--fetch-cache", action="store_true", help="Download pinned Mathlib caches before building")
    args = parser.parse_args()
    check_sources()
    if args.source_only:
        return
    selected = PROJECTS if args.project == "all" else [args.project]
    (ROOT / "artifacts").mkdir(exist_ok=True)
    for project in selected:
        endpoint, theorem = PROJECTS[project]
        with (ROOT / f"artifacts/{project}-verification.log").open("w", encoding="utf-8") as log:
            if args.fetch_cache:
                run(project, ["lake", "exe", "cache", "get"], log)
            run(project, ["lake", "build"], log)
            output = run(project, ["lake", "env", "lean", endpoint], log)
            count = check_axioms(output, theorem)
        print(f"[{project}] Build and final axiom check passed ({count} printed lists). Imports may be cached.")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, RuntimeError) as error:
        print(f"Verification failed: {error}", file=sys.stderr)
        sys.exit(1)
