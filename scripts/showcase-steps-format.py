#!/usr/bin/env python3
"""Lays out one `bin/leanforth check ... --steps -` run for a person (scripts/showcase-steps.sh).

Usage: python3 scripts/showcase-steps-format.py FILE.lf EXIT < OUTPUT
  FILE.lf  the LeanForth file that was checked; EXIT its exit status;
  OUTPUT   everything the run printed (verdict lines, errors and the step log's
           JSON lines, docs/user/COMMAND_LINE.md "The step log").

For each theorem of the file it prints four parts: A, the LeanForth text; B, the
same theorem in Lean (its twin, which tests/front/lean-twins.json names, copied from
the Lean file); C, what LeanForth did: its reading of the statement (the first goal,
in Lean's notation), then each step its tactics took, numbered as in the step log,
with the step's own text from the file, Lean's name for the tactic, the goal before
and the goals after exactly as the log gives them, a step inside another indented
under it; D, the verdict line of LeanForth's kernel. Last come the run's error lines,
its summary line and the exit status. It reads FILE.lf, the twin file and the Lean
source it
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


LEAN_NAME = {"alternative": "one case of the induction above"}


def lean_name(tactic):
    return LEAN_NAME.get(tactic, f"Lean calls this tactic `{tactic}`")


def show_step(record, depth, lines):
    """The lines of one step, DEPTH steps deep: its number, its own text from the file,
    Lean's name for it, the goal it met and what it left."""
    pad = "   " + "      " * depth
    body = pad + "         "
    row, column = (int(part) for part in record["source"].split(":"))
    source = lines[row - 1] if 0 < row <= len(lines) else ""
    out = ["", f"{pad}Step {record['step']}.  {step_text(source, column, record['word'])}",
           f"{body}({lean_name(record['tactic'])})"]
    after = record["goals_after"]
    if record["goal_before"] is None:
        out.append(f"{body}The goal of this case:")
        out += [goal(text, body + "    ") for text in after]
        return out
    out.append(f"{body}Goal before this step:")
    out.append(goal(record["goal_before"], body + "    "))
    if after:
        left = "1 goal is left:" if len(after) == 1 else f"{len(after)} goals are left:"
        out.append(f"{body}After this step {left}")
        for text in after:
            out.append(goal(text, body + "    "))
    elif record["tactic"] == "induction":
        out.append(f"{body}After this step: one goal for each case. The cases follow, indented.")
    else:
        out.append(f"{body}After this step: nothing is left to prove here.")
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


def lean_note(path, name):
    """The Lean theorem NAME as a comment line `\\ Lean: theorem NAME ...` of the LeanForth
    file PATH gives it, or None."""
    mark = re.compile(r"^\\\s+Lean:\s+(theorem\s+" + re.escape(name) + r"\s.*)$")
    for line in (ROOT / path).read_text(encoding="utf-8").splitlines():
        found = mark.match(line)
        if found:
            return found.group(1).rstrip()
    return None


def lean_twin(path, name):
    """The lines that show theorem NAME of the LeanForth file PATH in Lean, from the twin
    file tests/front/lean-twins.json names, or a line saying none is recorded."""
    twin = json.loads(TWINS.read_text(encoding="utf-8"))["twins"].get(path)
    if twin is None:
        note = lean_note(path, name)
        if note is None:
            return ["      (no Lean twin recorded for this theorem)"]
        return ["      " + note, "", f"      (from the note in {path}; no test compares this one with Lean yet)"]
    source = (ROOT / twin["lean"]).read_text(encoding="utf-8").splitlines()
    text = lean_source(source, twin["names"].get(name, name))
    return ["      " + line for line in text] + ["", f"      (copied from {twin['lean']})"]


RULE = "-" * 78


def unindented(lines):
    """LINES without the indentation they all share."""
    margin = min((len(line) - len(line.lstrip()) for line in lines if line.strip()), default=0)
    return [line[margin:].rstrip() for line in lines]


def show_work(name, first, last, lines, logs):
    """Part C: how LeanForth read the statement and each step its tactics took."""
    head, steps = logs.get(name, (None, []))
    tactics = re.search(r":=\s+by\b", " ".join(lines[first - 1:last]))
    if head is None and not tactics:
        return ["   This proof is a term written out in full after := , not a list of tactics,",
                "   so there are no tactic steps to show. The kernel checks the term as it stands."]
    if head is None:
        return ["   No tactic step was recorded: the run stopped first (see its error below)."]
    out = []
    if steps and steps[0]["goal_before"] is not None:
        out += ["   First it read the statement. This is what has to be proved, in Lean's notation.",
                "   Lines of the form  name : type  are what is given; the line after the mark \u22a2 is",
                "   what must be shown.", "",
                goal(steps[0]["goal_before"], "      "), ""]
    count = "1 tactic step" if head["steps"] == 1 else f"{head['steps']} tactic steps"
    out.append(f"   Then it ran the proof's {count}, in this order. A step that works inside")
    out.append("   another step is indented under it.")
    if head["cut"]:
        out.append("   (The step log ran out of room: its steps are left out.)")
    depth = {0: -1}
    for record in steps:
        depth[record["step"]] = depth.get(record["parent"], -1) + 1
        out += show_step(record, depth[record["step"]], lines)
    axioms = ", ".join(head["axioms"]) or "none"
    out += ["", f"   Every step is done. Parts left unproved: {head['open_parts']}. Axioms used: {axioms}."]
    return out


def show_theorem(path, name, first, last, lines, logs, output):
    out = [RULE, f"Theorem {name}        (from the file {path})", RULE, "",
           "A. The proof as written in LeanForth", ""]
    out += ["      " + line for line in unindented(lines[first - 1:last])]
    out += ["", "B. The same proof as a Lean user would write it  (for comparison; Lean is not run)", ""]
    out += lean_twin(path, name)
    out += ["", "C. What LeanForth did with the LeanForth text", ""]
    out += show_work(name, first, last, lines, logs)
    verdicts = [line for line in output if line.startswith(f"{name}: ")]
    out += ["", "D. The result", ""]
    if verdicts:
        out += ["   LeanForth's kernel checked the finished proof and printed its verdict:", "",
                "      " + verdicts[-1]]
    else:
        out.append("   No verdict: the run stopped before the kernel was given this theorem.")
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
    for name, first, last in blocks(lines):
        print()
        try:
            print("\n".join(show_theorem(path, name, first, last, lines, logs, output)))
        except (ValueError, KeyError, TypeError, OSError) as problem:
            print(f"showcase-steps-format: a step of {name} is malformed: {problem}", file=sys.stderr)
            return 1
    print()
    print(f"End of the run on {path}. LeanForth's last lines and its exit status")
    print("(0 means every theorem of the file was accepted):")
    print()
    for line in output:
        if line.startswith("error") or re.match(r"^\d+ declarations: ", line):
            print("   " + line)
    print(f"   exit status {status}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
