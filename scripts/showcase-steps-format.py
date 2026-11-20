#!/usr/bin/env python3
"""Lays out one `bin/leanforth check ... --steps -` run for a person (scripts/showcase-steps.sh).

Usage: python3 scripts/showcase-steps-format.py FILE.lf EXIT < OUTPUT
  FILE.lf  the LeanForth file that was checked; EXIT its exit status;
  OUTPUT   everything the run printed (verdict lines, errors and the step log's
           JSON lines, docs/user/COMMAND_LINE.md "The step log").

For each theorem of the file it prints the LeanForth text with its line numbers,
LeanForth's reading of the statement (the first goal, in Lean's notation), then each
step LeanForth's tactics took: the step's own text from the file, the name of the
same tactic in Lean, the goal before and the goals after exactly as the log gives
them, indented under the step it belongs to; then the same theorem in Lean (its
twin, which tests/front/lean-twins.json names, copied from the Lean file) and the
verdict line of LeanForth's kernel. Last come the run's error lines, its summary
line and the exit status. It reads FILE.lf, the twin file and the Lean source it
names, and standard input, and writes only standard output. Exit status 0, or 1 when a step-log
line is not JSON or lacks a field (the formatter's own failure, not a verdict).
"""
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
TWINS = ROOT / "tests/front/lean-twins.json"

THEOREM = re.compile(r"^\s*theorem\s+(\S+)")


def blocks(lines):
    """[(name, first, last)] of the file's theorems: 1-based lines of `theorem NAME` to `end NAME`."""
    found, open_ = [], None
    for number, line in enumerate(lines, 1):
        if line.lstrip().startswith("\\"):
            continue
        head = THEOREM.match(line)
        if head and open_ is None:
            open_ = (head.group(1), number)
        if open_ and re.search(r"(^|\s)end\s+" + re.escape(open_[0]) + r"\s*$", line):
            found.append((open_[0], open_[1], number))
            open_ = None
    return found


def step_text(line, column, word):
    """The step's own words on its source line: a tactic word with the arguments written
    before it (after `=>` or `:= by`), a rewrite's bracket, or an alternative's `| ... =>`."""
    at = column - 1
    if word == "|":
        arrow = line.find("=>", at)
        return line[at:arrow + 2] if arrow >= 0 else line[at:].strip()
    end = at + len(word)
    if word.endswith("["):
        close = line.find("]", at)
        end = close + 1 if close >= 0 else len(line)
    start = 0
    for mark in ("=>", ":= by"):
        found = line.rfind(mark, 0, at)
        if found >= 0:
            start = max(start, found + len(mark))
    return " ".join(line[start:end].split())


def goal(text, lead):
    return "\n".join(lead + part for part in text.splitlines())


def show_step(record, depth, lines):
    """The lines of one step, DEPTH steps deep."""
    pad = "    " + "  " * depth
    row, column = (int(part) for part in record["source"].split(":"))
    source = lines[row - 1] if 0 < row <= len(lines) else ""
    out = [f"{pad}{record['step']}. {step_text(source, column, record['word'])}"
           f"   [the same tactic in Lean: {record['tactic']}; line {row}, column {column}]"]
    after = record["goals_after"]
    if record["goal_before"] is None:
        out.append(f"{pad}   opens the case:")
        out += [goal(text, pad + "     ") for text in after]
        return out
    out.append(f"{pad}   goal before:")
    out.append(goal(record["goal_before"], pad + "     "))
    if after:
        out.append(f"{pad}   goals after ({len(after)}):")
        out += [goal(text, pad + "     ") for text in after]
    elif record["tactic"] == "induction":
        out.append(f"{pad}   goals after: none listed here; each case's goal is on its alternative below")
    else:
        out.append(f"{pad}   goals after: none (this goal is proved)")
    return out


def step_log(output):
    """{declaration: (header, [step records])} from the run's JSON lines."""
    logs, current = {}, None
    for line in output:
        if not line.startswith("{"):
            continue
        record = json.loads(line)
        if "tactic_steps" in record:
            current = record["tactic_steps"]["declaration"]
            logs[current] = (record["tactic_steps"], [])
        elif current is not None:
            logs[current][1].append(record)
    return logs


def lean_source(lines, name):
    """The Lean theorem NAME of a Lean file's LINES: its line and the indented lines after it."""
    head = re.compile(r"^theorem\s+" + re.escape(name) + r"(\s|$)")
    start = next((n for n, line in enumerate(lines) if head.match(line)), None)
    if start is None:
        raise ValueError(f"theorem {name} is not in the Lean twin file")
    end = start + 1
    while end < len(lines) and lines[end][:1] in (" ", "\t"):
        end += 1
    return [line.rstrip() for line in lines[start:end]]


def lean_twin(path, name):
    """The lines that show theorem NAME of the LeanForth file PATH in Lean, from the twin
    file tests/front/lean-twins.json names, or a line saying none is recorded."""
    twin = json.loads(TWINS.read_text(encoding="utf-8"))["twins"].get(path)
    if twin is None:
        return ["  The same theorem in Lean: no Lean twin recorded"]
    source = (ROOT / twin["lean"]).read_text(encoding="utf-8").splitlines()
    text = lean_source(source, twin["names"].get(name, name))
    return [f"  The same theorem in Lean ({twin['lean']}):"] + ["    " + line for line in text]


def show_theorem(path, name, first, last, lines, logs, output):
    where = f"line {first}" if first == last else f"lines {first}-{last}"
    out = [f"theorem {name}  ({where})", "  LeanForth:"]
    out += [f"    {n:3d} | {lines[n - 1].rstrip()}" for n in range(first, last + 1)]
    head, steps = logs.get(name, (None, []))
    tactics = re.search(r":=\s+by\b", " ".join(lines[first - 1:last]))
    if head is None and not tactics:
        out.append("  Proof: a term (after :=), not tactics; the step log has no steps for it.")
    elif head is None:
        out.append("  Steps: none in the step log for it (see the run's errors below).")
    else:
        if steps and steps[0]["goal_before"] is not None:
            out.append("  Statement (LeanForth's reading of the text, written in Lean's notation):")
            out.append(goal(steps[0]["goal_before"], "    "))
        axioms = ", ".join(head["axioms"]) or "none"
        out.append(f"  Steps LeanForth's tactics took ({head['steps']} in the step log; "
                   f"axioms: {axioms}; open parts: {head['open_parts']}):")
        if head["cut"]:
            out.append("    (the step log ran out of room: its steps are left out)")
        depth = {0: -1}
        for record in steps:
            depth[record["step"]] = depth.get(record["parent"], -1) + 1
            out += show_step(record, depth[record["step"]], lines)
    out += lean_twin(path, name)
    verdicts = [line for line in output if line.startswith(f"{name}: ")]
    out.append("  Verdict (LeanForth's kernel): " +(verdicts[-1] if verdicts else "none (the run stopped before it)"))
    return out


def main(argv):
    if len(argv) != 3:
        print(__doc__.split("\n\n")[1], file=sys.stderr)
        return 1
    path, status = argv[1], argv[2]
    with open(path, encoding="utf-8") as stream:
        lines = stream.read().splitlines()
    output = sys.stdin.read().splitlines()
    try:
        logs = step_log(output)
    except (ValueError, KeyError) as problem:
        print(f"showcase-steps-format: a step-log line is malformed: {problem}", file=sys.stderr)
        return 1
    print(f"=== {path}")
    for name, first, last in blocks(lines):
        print()
        try:
            print("\n".join(show_theorem(path, name, first, last, lines, logs, output)))
        except (ValueError, KeyError, TypeError, OSError) as problem:
            print(f"showcase-steps-format: a step of {name} is malformed: {problem}", file=sys.stderr)
            return 1
    print()
    for line in output:
        if line.startswith("error") or re.match(r"^\d+ declarations: ", line):
            print(line)
    print(f"--- exit {status}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
