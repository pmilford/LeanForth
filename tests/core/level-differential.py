"""Compare the development preview's concrete level decoding with Lean."""
import io
import json
import os
from pathlib import Path
import subprocess
import sys

sys.path.insert(0, "tests/support")
from ndjson_preview import LEAN_HASH, preview


def main():
    lean = os.environ.get("LEAN", "lean")
    version = subprocess.run([lean, "--version"], check=True, capture_output=True, text=True).stdout
    revision = subprocess.run([lean, "--githash"], check=True, capture_output=True, text=True).stdout.strip()
    if not version.startswith("Lean (version 4.35.0,") or revision != LEAN_HASH:
        raise ValueError("unexpected Lean toolchain")
    lean_rows = subprocess.run([lean, "--run", "tests/reference/level-table.lean"],
                               check=True, capture_output=True, text=True).stdout.splitlines()
    fixture = Path("tests/reference/identity.ndjson").read_text().splitlines()
    position = next(i for i, line in enumerate(fixture) if '"ie":0' in line)
    records = [{"il": i, "succ": i - 1} for i in range(1, 6)]
    cases = []
    for left in range(6):
        for right in range(6):
            for kind, name in enumerate(("max", "imax")):
                records.append({"il": len(records) + 1, name: [left, right]})
                cases.append((kind, left, right))
    # Index 78 evaluates to zero; its numeric index is deliberately unrelated
    # to its value, so these nested operations exercise reference resolution.
    zero_index = len(records) + 1
    records.append({"il": zero_index, "imax": [2, 0]})
    for index, (name, operands) in enumerate((
        ("imax", [1, zero_index]), ("max", [zero_index, 1]),
        ("imax", [2, zero_index]), ("max", [zero_index, 2]),
    )):
        records.append({"il": len(records) + 1, name: operands})
        cases.append((2, index, 0))
    fixture[position:position] = [json.dumps(record) for record in records]
    result = preview(io.BytesIO(("\n".join(fixture) + "\n").encode()))
    values = result["levels"][6:zero_index] + result["levels"][zero_index + 1:]
    rows = [f"{kind} {left} {right} {level}" for (kind, left, right), level
            in zip(cases, values, strict=True)]
    if len(rows) != 76 or rows != lean_rows:
        raise ValueError("concrete universe results differ from Lean")
    print("Lean and preview agree on 76 concrete and nested max and imax cases.")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        print(f"Level differential failed: {error}", file=sys.stderr)
        sys.exit(1)
