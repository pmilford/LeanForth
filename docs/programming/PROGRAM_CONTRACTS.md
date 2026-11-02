# Program contracts: Lean reference model

`tests/reference/program-contracts.lean` defines a small reference stack
language with literal push, duplicate and addition. Its `wp` function computes
the weakest precondition for successful execution of a finite instruction list
against a postcondition. Lean proves that this precondition is equivalent to
successful modeled execution with the postcondition, and proves a composition
rule for two instruction lists. The reference checks a symbolic duplicate-and-
add example and rejects duplicate on an empty stack.

`add_three` proves a second value contract for all mathematical integers and
stack tails: two adds transform `b :: c :: a :: tail` into
`((c + b) + a) :: tail`. Its weakest precondition includes successful
execution and preserves the untouched tail.

The same file also defines a separate bounded-memory model: a natural-number
size and a total function from addresses to mathematical integers. `load` and
`store` return `none` outside the half-open range `[0, size)`; a successful
store preserves the size. `store_read_frame` proves, for every in-bounds
address and value, that reading the address returns the stored value and all
other backing cells remain unchanged. `out_of_bounds_access` proves both
operations fail at the boundary and beyond, including for an empty memory.
These are symbolic results for arbitrary sizes, addresses, values and initial
memories. The backing function includes inaccessible addresses; preserving
those cells is a property of this model, not a claim about physical memory.
Memory is separate from the stack interpreter: there are no modeled Forth
load/store instructions, byte addressing, allocation, ownership, aliasing,
alignment, concurrency or host memory semantics.

`copyCell` composes the separate memory model's load and store, reading the
source before writing the destination. `copyCell_success` proves that when
both addresses are in bounds, the destination receives the original source
value, the size is unchanged, and every other backing cell is unchanged.
`copyCell_self` covers equal source and destination and proves all backing
cells unchanged. Two negative theorems prove that an out-of-bounds source or
destination produces `none`, including the boundary. Failure produces no
resulting memory in this pure model; it does not establish atomicity of a
real Forth or concurrent memory operation. This operation is not an instruction
in the stack interpreter and has no ownership or physical-memory guarantees.

`wp_weakest` states the general contract rule: for arbitrary finite modeled
code and predicates `pre` and `post`, `pre` implies `wp code post` for every
initial stack exactly when every stack satisfying `pre` executes successfully
to a result satisfying `post`. Thus modeled underflow cannot discharge the
contract vacuously. `wp_mono` shows that a postcondition can be weakened when
the stronger postcondition implies the weaker one for every result stack;
successful execution is still required. These results assume precisely the
file's deterministic `step` and `execute` definitions, finite instruction
lists, and Lean's integer and list semantics. They impose no separate
precondition on the initial stack beyond the stated predicates.

`requiredDepth` computes a static minimum input depth by walking the modeled
instruction list backwards. For a suffix needing `r` items, push needs
`r - 1` (natural-number subtraction saturates at zero), duplicate needs
`max 1 (r - 1)`, and add needs `max 2 (r + 1)`. The empty list needs zero.
`requiredDepth_iff_execution` proves for every finite modeled instruction list
and every initial stack that this bound is met exactly when execution returns
some result. In particular, meeting the bound rules out modeled stack
underflow, and failing it guarantees failure. The file also checks examples
where instruction order changes the bound and where an empty stack fails it.
The bound concerns stack depth only: it does not establish an arbitrary value
postcondition; use `wp` and a separate proof for that.

`append_success_iff_intermediate_depth` connects sequential composition to
that bound: arbitrary `first ++ second` code succeeds exactly when `first`
produces an intermediate stack whose depth meets `requiredDepth second`.
`append_failure_iff` gives the complementary partial-failure rule: the sequence
returns `none` exactly when the first part fails, or it succeeds with an
intermediate stack strictly shallower than the second part requires. Equality
with the bound is sufficient for the second part to execute; this says nothing
about its values or any desired postcondition. These results apply to the
abstract stack operations only, not to the separate memory model or a Forth
runtime.

`src/experimental/program-depth.fs` implements a separate untrusted Forth
diagnostic for arrays of the three opcode tags. It does not execute programs or
issue a proof. `make test-program-depth-differential` compares its results with
the Lean reference on all 1,093 opcode lists of length at most six. This is
finite evidence, not a proof that the Forth implementation matches the model.
The Gforth development host needs a writable library cache; in a restricted
environment set `libccnameddir` to a writable temporary directory before running
the test if its normal cache is unavailable.
At this checkpoint, `libccnameddir=/tmp/leanforth-gforth-libcc
ELAN_HOME="$PWD/.tools/elan" make test-program-depth-differential
LEAN="$PWD/.tools/elan/bin/lean"` passed with Gforth 1.0.0 amd64 and pinned
Lean 4.35.0; Gforth printed library-reopen warnings. CI was not run for this
checkpoint. The analyzer SHA-256 is
`6d16b3c4ca766637e82970a61a44de7c28a2df55e9a0a155a5eaad96160863d3`.
The caller must provide genuinely readable, aligned storage and its capacity;
Forth cannot validate memory ownership or prevent concurrent mutation. Push
values, actual Forth source, finite-cell arithmetic and effects are outside
this depth-only representation.

`tests/program/program-depth.fs` also tests the input validation:
- Misaligned zero-filled storage must be rejected. Its misaligned bytes would
  decode as valid push tags, so only the alignment check can reject it.
- The smallest count whose byte size exceeds the largest signed cell must be
  rejected.
- A negative count whose byte size wraps to zero must be rejected.

The tests observe only the returned result. They cannot show that a rejection
happened before any array read: a 2026-11-02 review mutant without the
negative-size check read outside the array and still returned `0 false`.
Proving read-free rejection needs an instrumented fetch, which is not
implemented.

Run with the pinned toolchain:

```sh
ELAN_HOME="$PWD/.tools/elan" .tools/elan/bin/lean tests/reference/program-contracts.lean
```

The command passed locally with Lean 4.35.0 (commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`). This is a local reference check;
it does not establish CI status or cross-platform behavior.
The reference file SHA-256 for this check is
`3cb499863916d2c5ccaa44eba24ece852b59f81ad25843a5336212f93f646d27`.

This is a reference specification for future verification-condition work, not
a LeanForth program verifier. It models unbounded mathematical integers and a
partial data stack and the separate abstract memory above; it does not model
host cell overflow, a return stack, I/O, loops, Forth parsing, a compiler or a runtime. The Lean proof is
checked by Lean, not by LeanForth. Its `wp` is a Lean function rather than an
implemented Forth-facing contract language or production VC generator.

Separately, `tests/reference/program-stack-composition.lean` proves composition
and data- and return-stack frame properties for the `stack-clamp.lean` model,
including a modeled clamp followed by `DROP`. Its frame theorem requires both
components to succeed: the file includes a counterexample showing that an
extra frame can supply an otherwise missing operand. `make reference` checks
this Lean model; it does not establish source-to-Gforth correspondence.
`tests/reference/program-stack-swap.lean` further proves a modeled swap, its
double-swap property and underflow propagation through a continuation. Both
data and return-stack frames are covered; the same runtime limitation applies.

`tests/reference/program-verified-obligations.lean` characterizes the weakest
precondition for a modeled `DOUBLE` sequence, proves its stated contract for
any stack suffix and refutes that contract for an add-one variant. Lean checks
these abstract obligations in `make reference`; this does not connect them to
Forth source or runtime behavior. The file prints its Lean axiom dependencies
(`propext`, and `Quot.sound` for the weakest-precondition characterization).
