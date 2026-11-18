"""Measurement only (MF design): copy elaboration data without the given
record lines (1-based file line numbers), fixing the header's counts and
records_sha256, to step around one refusal and reach the next.
Usage: python3 drop_lines.py IN OUT LINE..."""
import hashlib
import json
import sys

drop = {int(n) for n in sys.argv[3:]}
with open(sys.argv[1], "rb") as f:
    lines = f.read().split(b"\n")
head = json.loads(lines[0])
kept = []
for number, line in enumerate(lines[1:-1], start=2):
    if number in drop:
        kind = next(iter(json.loads(line)))
        kind = "instance_left_out" if kind == "instance_left_out" else kind
        head["elab_data"]["records"][kind] -= 1
        print("dropped", number, line[:160].decode())
        continue
    kept.append(line)
body = b"\n".join(kept) + b"\n"
head["elab_data"]["records_sha256"] = hashlib.sha256(body).hexdigest()
with open(sys.argv[2], "wb") as f:
    f.write(json.dumps(head, separators=(",", ":"), sort_keys=True).encode() + b"\n" + body)
