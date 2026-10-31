"""Emit untrusted Forth probe outcomes for the actual poly-identity fixture."""
import io
import os
from pathlib import Path
import subprocess
import sys

sys.path.insert(0, "tests/core")
from test_poly_specialization import specialization_stream
from ndjson_preview import preview


def main():
    decoded = preview(io.BytesIO(Path("tests/reference/poly-identity.ndjson").read_bytes()))
    command = [os.environ.get("GFORTH", "gforth"), "tests/core/specialize-fixture-stream.fs"]
    claim = decoded["declarations"][0]["type"]
    for level in range(4):
        for kind in range(2):
            data = specialization_stream(decoded, [(2, level)], claim if kind else None)
            result = subprocess.run(command, input=data, capture_output=True, check=True)
            rows = result.stdout.splitlines()
            words = rows[0].split()
            if len(words) != 1:
                raise ValueError("unexpected probe response")
            shapes = []
            for row in rows[1:]:
                index, tag, first, second = map(int, row.split())
                if index != len(shapes):
                    raise ValueError("unexpected expression index")
                if tag == 1:
                    shape = f"s{first}"
                elif tag == 2:
                    shape = f"v{first}"
                elif tag in (3, 4, 5) and first < index and second < index:
                    shape = f"{ {3: 'a', 4: 'l', 5: 'p'}[tag]}({shapes[first]},{shapes[second]})"
                else:
                    raise ValueError("unexpected expression row")
                shapes.append(shape)
            value_index = claim if kind else decoded["declarations"][0]["value"]
            print(level, kind, int(words[0]), shapes[claim], shapes[value_index])


if __name__ == "__main__":
    main()
