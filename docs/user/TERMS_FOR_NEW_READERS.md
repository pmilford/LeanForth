# LeanForth terms for new readers

This page is an introduction for Forth programmers, mathematicians and others
who do not already know Lean's terminology. It describes the intended design
and distinguishes it from today's implementation. It is not a specification
of all Lean typing rules.

**Current status:** LeanForth does not yet have a trusted theorem checker or
fully import Lean or Mathlib. The Forth code described as experimental is
development work, and its successful diagnostics do not establish a theorem.
See [project progress](../project/PROJECT_PROGRESS.md) for what has actually been tested.

## Core ideas

**Expression or term.** A structured piece of mathematical data, such as a
variable, a function applied to an argument, or a function type. Internally
LeanForth represents expressions as nodes with links to other nodes. A printed
formula is a way to read that structure; it is not the structure itself.

**Type.** A description of what kind of value an expression has. For example,
in Lean notation `Nat` is a type and `3` has type `Nat`. A function type such
as `Nat → Nat` describes a function taking a natural number and returning one.
Lean's dependent function types can also mention an earlier argument in the
type of a later argument or result.

**Proposition and proof.** A proposition is a statement that may be proved,
such as `n = n` given `n : Nat`. If `P : Prop` is a proposition, `p : P`
denotes a proof of it. Lean represents a proof as a term whose type is that
proposition. A proof must have the right type according to the kernel's rules;
an explanation in English, a passing test, or an AI's claim is not itself a
proof. The mathematical statements printed here use Lean notation for
illustration, not LeanForth's canonical Forth grammar.

**Theorem.** A named proposition together with a proof. For LeanForth to accept
it, the intended workflow requires the trusted kernel to check that proof and
its dependencies against the reviewed axiom policy. A theorem may depend on
assumptions or axioms; a useful result must report them. Lean can check terms
depending on axioms that LeanForth's policy may not permit.

**Kernel.** The small, security-critical part of a theorem prover that checks
proof terms against types and approved assumptions. It does not need to trust
the parser, a tactic, an AI, or an explanation that produced a candidate proof.
That checks the statement actually supplied to the kernel; a faulty parser or
display can still misrepresent what the user intended. Users must be able to
inspect or otherwise validate the checked statement and its assumptions.
LeanForth's proposed kernel is still under development and requires explicit
human review before trusted use.

**Universe level and `Sort`.** Types themselves have types. Lean organizes
them into a hierarchy written `Sort u`, where `u` is a *universe level*.
`Sort 0` is `Prop`, the universe of propositions; `Type u` is notation for
`Sort (u + 1)`. A level may be a symbolic parameter or an expression involving
levels, not just a fixed integer. For example, a generic construction may work
at several levels without committing to one in advance. In Lean notation,
`Nat : Type` and `Type : Type 1`; plain `Type` means `Type 0`, or `Sort 1`.
Lean's universes are not cumulative: a type's membership in one universe
does not automatically make it a member of every higher one. A level here is not
the depth of a Forth data stack or a measure of proof difficulty.

**Binder and scope.** A binder introduces a variable for a part of an
expression, like the `x` in “for every `x`”. The variable's *scope* is where
that binding applies. A variable used outside its scope must not be silently
accepted. LeanForth experiments often store a bound variable as a de Bruijn
index: `0` refers to the nearest enclosing binder, `1` to the next, and so on.
These indices are mathematical term data, not Forth stack positions.

**Substitution and capture.** Substitution replaces a variable with a term.
It must preserve the meaning of variables in the replacement when crossing a
binder; otherwise a previously free variable can accidentally become bound.
That error is called *variable capture*. The current mixed-term shifting and
single-binder instantiation experiments test selected capture-sensitive examples
against Lean; they do not constitute a general proof of correctness.

**Reduction and conversion.** Reduction simplifies an expression according
to rules, such as applying the identity function to `3` to obtain `3`.
Conversion asks whether
two expressions count as the same type or term under the allowed rules, even
if written differently. Lean's rules include more than simple substitution.
LeanForth's untrusted experimental conversion diagnostic can return *unknown*: it has not established
equality, and it has not proved inequality either.

**Declaration and environment.** A declaration records a named item, its type,
and, where applicable, a value or proof. An environment holds declarations
that later expressions can refer to. A name found in imported data is only a
candidate until its declaration and dependencies have been checked against a
reviewed environment and axiom policy.

**NDJSON and Mathlib.** NDJSON is a file format with one JSON record per line;
it is used here for exported Lean data. Reading those records is separate from
checking their meaning. Mathlib is Lean's mathematical library. The project
goal is to use its full library with independently checked declarations; that
capability has not yet been delivered.

## Programs as well as theorems

A **program contract** says what a program assumes and what it guarantees.
For a Forth word it can describe the input and output stack, memory it may
change, and failure conditions. A **reference model** is a precise mathematical
description used for reasoning. Lean checks that current model definitions are
well typed and checks stated proofs about them. That does not establish that a
handwritten model matches Forth or that Gforth, compiled code, or hardware
behaves like it. The future verifier must connect the program and its stated
semantics to checked proofs and report runtime and compiler assumptions.

For the development roadmap and test strategy, see
[development roadmap](../project/DEVELOPMENT_ROADMAP.md) and [testing strategy](../development/TESTING_STRATEGY.md).
