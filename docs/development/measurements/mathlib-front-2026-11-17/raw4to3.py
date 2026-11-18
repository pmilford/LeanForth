"""Measurement only (MF design): turn a format-4 RAW, already without the
11 sunfold records format 3 cannot say, into a format-3 RAW: drop format 4's
kinds and its defeq tags, header "simp": null.
Usage: python3 raw4to3.py RAW4 RAW3 SCRIPTS_DIR"""
import json
import sys

sys.path.insert(0, sys.argv[3])
import export_elab as E  # noqa: E402

kinds3 = set(E.RAW_KINDS)
tags3 = set(E.TAGS)
n = {"kept": 0, "kind_dropped": 0, "tag_dropped": 0}
with open(sys.argv[1]) as raw, open(sys.argv[2], "w") as out:
    head = json.loads(raw.readline())
    head["simp"] = None
    head.pop("norm_num_core", None)
    out.write(json.dumps(head, separators=(",", ":")) + "\n")
    for line in raw:
        kind, body = next(iter(json.loads(line).items()))
        if kind not in kinds3:
            n["kind_dropped"] += 1
            continue
        if kind == "tag" and body.get("tag") not in tags3:
            n["tag_dropped"] += 1
            continue
        out.write(line)
        n["kept"] += 1
print(n)
