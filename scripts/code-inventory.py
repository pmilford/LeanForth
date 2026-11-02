#!/usr/bin/env python3
"""Count project text files, including untracked non-ignored work in progress."""
from collections import defaultdict
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parent.parent
names = subprocess.check_output(
    ["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z"],
    cwd=root,
).split(b"\0")
counts = defaultdict(lambda: [0, 0])
for raw in set(names):
    if not raw:
        continue
    name = raw.decode("utf-8", errors="surrogateescape")
    path = root / name
    if not path.is_file():
        continue
    if name.startswith("src/") and name.endswith(".fs"):
        folder = name.split("/")[1] if name.count("/") > 1 else "main.fs"
        category = f"Forth source, untrusted ({folder})"
    elif name.startswith("tests/") and name.endswith(".fs"):
        category = "Forth tests and support"
    elif name.startswith("tests/") and name.endswith(".lean"):
        category = "Lean references and tests"
    elif name.startswith("tests/") and name.endswith((".py", ".sh")):
        category = "Other test code and support"
    elif name.endswith(".ndjson"):
        category = "NDJSON fixtures"
    elif name.endswith(".md"):
        category = "Markdown documentation"
    else:
        category = "Other project files"
    data = path.read_bytes()
    counts[category][0] += 1
    counts[category][1] += len(data.splitlines())
for category, (files, lines) in sorted(counts.items()):
    print(f"{category}: {files} files, {lines} physical lines")
