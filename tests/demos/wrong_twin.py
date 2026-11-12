"""Make the wrong twin of a demo's export: the same proof under a different statement.

Usage: python3 tests/demos/wrong_twin.py EXPORT.ndjson TWIN.ndjson

The last theorem of the export is the demo's. Its statement P (a closed
expression) is replaced by P -> P: one new expression record, a forall
with domain and body P, is added just before the theorem, and the theorem's
type points to it. The value (a proof of P) is unchanged, so the checker has
to reject the declaration: the value does not have the stated type. Nothing
else changes, and no other declaration is touched. Untrusted test tool.
"""
import json
import sys


def twin(text):
    lines = text.split("\n")
    theorems = [i for i, line in enumerate(lines) if line.startswith('{"thm"')]
    last = json.loads(lines[theorems[-1]])["thm"]
    newest = max(json.loads(line)["ie"] for line in lines if line.startswith("{") and '"ie"' in line)
    implication = {"forallE": {"binderInfo": "default", "body": last["type"], "name": last["name"],
                               "type": last["type"]}, "ie": newest + 1}
    last["type"] = newest + 1
    lines[theorems[-1]] = json.dumps({"thm": last}, separators=(",", ":"), sort_keys=True)
    lines.insert(theorems[-1], json.dumps(implication, separators=(",", ":"), sort_keys=True))
    return "\n".join(lines)


if __name__ == "__main__":
    with open(sys.argv[1], encoding="utf-8") as source:
        result = twin(source.read())
    with open(sys.argv[2], "w", encoding="utf-8") as target:
        target.write(result)
