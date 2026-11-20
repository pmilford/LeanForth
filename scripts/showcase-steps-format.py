#!/usr/bin/env python3
"""Lays out one `bin/leanforth check ... --steps -` run for a person (scripts/showcase-steps.sh).

Usage: python3 scripts/showcase-steps-format.py FILE.lf EXIT < OUTPUT
  FILE.lf  the LeanForth file that was checked; EXIT its exit status;
  OUTPUT   everything the run printed (verdict lines, errors and the step log's
           JSON lines, docs/user/COMMAND_LINE.md "The step log").

For each theorem of the file it prints four parts: A, the LeanForth text; B, the
same theorem in Lean (its twin, which tests/front/lean-twins.json names, copied from
the Lean file; not LeanForth's output); C, what LeanForth did: its reading of the
statement (the first goal, in Lean's notation), then each step its tactics took, as
written in the file, with the goal before and the goals after exactly as the step log
gives them, a step inside another indented under it; D, the verdict line of
LeanForth's kernel. Explanations are comments on the right, after LeanForth's comment
mark (a backslash) or, in the Lean part, Lean's (--). Last come the run's error
lines, its summary line and the exit status. It reads FILE.lf, the twin file and the
Lean source it
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


COLUMN = 50   # where a comment on the right starts


def noted(text, comment, mark="\\"):
    """TEXT with COMMENT on its right as a comment: after MARK (LeanForth's backslash, or
    Lean's --), at COLUMN when the text is short enough, else two spaces after it."""
    if not comment:
        return text.rstrip()
    return f"{text:<{COLUMN - 1}}" + (" " if len(text) < COLUMN - 1 else "  ") + f"{mark} {comment}"


def goal(text, lead, comment, given="", full=False):
    """A goal's lines after LEAD. The first carries COMMENT; the line to prove is marked
    (with the mark's reading when FULL); each line naming something given carries GIVEN."""
    out = []
    for n, part in enumerate(text.splitlines()):
        if part.startswith("\u22a2"):
            note = 'to prove (the mark \u22a2 reads "show that")' if full else "to prove"
        elif part.startswith("case "):
            note = "" if comment else "the case"
        else:
            note = given
        if n == 0 and comment:
            note = f"{comment}: {note}" if note else comment
        out.append(noted(lead + part, note))
    return out


# What each tactic does, in a line: general, not about the theorem at hand.
DOES = {
    "rfl": "computes both sides of  a = b ; if they come out the same, the goal is proved",
    "exact": "closes the goal with the proof term written before it",
    "rw": "rewrites the goal with each equation named, left to right; then tries rfl",
    "induction": "splits the goal into one case for each way the variable can be built",
    "alternative": "starts one case of the induction above and names what it introduces",
    "intro": "moves the goal's first assumption or variable up among what is given",
    "apply": "reduces the goal to the assumptions of the theorem or term applied",
    "assumption": "closes the goal with something given that states it",
    "constructor": "reduces the goal to the parts its first constructor needs",
    "case": "turns to the goal of the case named",
    "sorry": "leaves the goal unproved (the theorem is then NOT PROVED)",
    "left": "proves an  or  (or a two-case goal) by its first case",
    "right": "proves an  or  (or a two-case goal) by its second case",
    "exfalso": "turns the goal into False: a contradiction proves anything",
    "intros": "moves every leading assumption and variable up among what is given",
    "clear": "forgets the assumption named",
    "decide": "works the closed statement out by computation and proves it when it comes out true",
}


def lean_name(tactic):
    return "a case of the induction" if tactic == "alternative" else f"Lean's {tactic}"


def show_step(record, depth, lines):
    """The lines of one step, DEPTH steps deep: its own text from the file with its number
    and Lean's name for it as a comment, what the tactic does, then the goal it met and
    what it left."""
    pad = "    " + "    " * depth
    row, column = (int(part) for part in record["source"].split(":"))
    source = lines[row - 1] if 0 < row <= len(lines) else ""
    out = ["", noted(pad + step_text(source, column, record["word"]),
                     f"step {record['step']} ({lean_name(record['tactic'])})")]
    if record["tactic"] in DOES:
        out.append(noted("", DOES[record["tactic"]]))
    after = record["goals_after"]
    if record["goal_before"] is None:
        for text in after:
            out += goal(text, pad + "    ", "the goal of this case", "given in this case")
        return out
    out += goal(record["goal_before"], pad + "    ", "the goal before this step", "")
    if after:
        for n, text in enumerate(after, 1):
            out += goal(text, pad + "    ", f"left after the step, goal {n} of {len(after)}", "")
    elif record["tactic"] == "induction":
        out.append(noted("", "after the step: one goal for each case; the cases follow"))
    else:
        out.append(noted("", "after the step: nothing is left to prove here"))
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
    """(lines, source) showing theorem NAME of the LeanForth file PATH in Lean: from the twin
    file tests/front/lean-twins.json names, else from the LeanForth file's own note, else none."""
    twin = json.loads(TWINS.read_text(encoding="utf-8"))["twins"].get(path)
    if twin is None:
        note = lean_note(path, name)
        if note is None:
            return [], "no Lean twin is recorded for this theorem"
        return ["    " + note], f"copied from the note in {path}; no test compares it with Lean yet"
    source = (ROOT / twin["lean"]).read_text(encoding="utf-8").splitlines()
    text = lean_source(source, twin["names"].get(name, name))
    return ["    " + line for line in text], f"copied from {twin['lean']}, which the tests compare with"


RULE = "=" * 100


def unindented(lines):
    """LINES without the indentation they all share."""
    margin = min((len(line) - len(line.lstrip()) for line in lines if line.strip()), default=0)
    return [line[margin:].rstrip() for line in lines]


def show_work(name, first, last, lines, logs):
    """Part C: how LeanForth read the statement and each step its tactics took."""
    head, steps = logs.get(name, (None, []))
    tactics = re.search(r":=\s+by\b", " ".join(lines[first - 1:last]))
    if head is None and not tactics:
        return ["\\ The proof is a term written out in full after := , not tactics: there are no steps.",
                "\\ The kernel checks the term as it stands."]
    if head is None:
        return ["\\ No step was recorded: the run stopped first (its error is below)."]
    out = []
    if steps and steps[0]["goal_before"] is not None:
        out += [noted("", "The statement of A as LeanForth read it. This is the first goal:"),
                *goal(steps[0]["goal_before"], "    ", "", "given: a variable of the theorem", True)]
    if head["cut"]:
        out.append("\\ The step log ran out of room: its steps are left out.")
    depth = {0: -1}
    for record in steps:
        depth[record["step"]] = depth.get(record["parent"], -1) + 1
        out += show_step(record, depth[record["step"]], lines)
    axioms = ", ".join(head["axioms"]) or "none"
    done = "The one step is done." if head["steps"] == 1 else f"All {head['steps']} steps are done."
    out += ["", f"\\ {done} Parts left unproved: {head['open_parts']}. Axioms used: {axioms}."]
    return out


def show_theorem(path, name, first, last, lines, logs, output):
    out = [RULE, f"Theorem {name}", RULE, "",
           noted("A. The proof in LeanForth", f"input: the text of {path}"), ""]
    out += ["    " + line for line in unindented(lines[first - 1:last])]
    twin, source = lean_twin(path, name)
    out += ["", noted("B. The same proof in Lean", "for comparison only. Not LeanForth's output; Lean is not run:", "--"),
            noted("", source, "--"), ""]
    out += twin
    out += ["", noted("C. What LeanForth did", "LeanForth's output: its step log, laid out by the showcase script."),
            noted("", "LeanForth prints goals in Lean's notation. A goal is what is still to be proved."),
            noted("", "Each step is a tactic as written in A; a step inside another is indented."), ""]
    out += show_work(name, first, last, lines, logs)
    verdicts = [line for line in output if line.startswith(f"{name}: ")]
    out += ["", noted("D. The verdict of LeanForth's kernel", "LeanForth's output, as printed"), ""]
    out.append("    " + verdicts[-1] if verdicts else "\\ None: the run stopped before the kernel was given this theorem.")
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
    print(f"\\ End of the run on {path}: LeanForth's closing lines, as printed, and its exit")
    print("\\ status (0: every theorem of the file was accepted).")
    for line in output:
        if line.startswith("error") or re.match(r"^\d+ declarations: ", line):
            print("    " + line)
    print(f"    exit status {status}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
