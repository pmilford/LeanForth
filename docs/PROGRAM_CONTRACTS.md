# Program contracts: Lean reference model

`tests/reference/program-contracts.lean` defines a small reference stack
language with literal push, duplicate and addition. Its `wp` function computes
the weakest precondition for successful execution of a finite instruction list
against a postcondition. Lean proves that this precondition is equivalent to
successful modeled execution with the postcondition, and proves a composition
rule for two instruction lists. The reference checks a symbolic duplicate-and-
add example and rejects duplicate on an empty stack.

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

Run with the pinned toolchain:

```sh
ELAN_HOME="$PWD/.tools/elan" .tools/elan/bin/lean tests/reference/program-contracts.lean
```

The command passed locally with Lean 4.35.0 (commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`). This is a local reference check;
it does not establish CI status or cross-platform behavior.
The reference file SHA-256 at this checkpoint is
`1775e3a6116ce0495d2de27e3791af70e2f160b1e7a9b997e2ced23ee6583d9a`.

This is a reference specification for future verification-condition work, not
a LeanForth program verifier. It models unbounded mathematical integers and a
partial data stack; it does not model host cell overflow, a return stack,
memory, I/O, loops, Forth parsing, a compiler or a runtime. The Lean proof is
checked by Lean, not by LeanForth. Its `wp` is a Lean function rather than an
implemented Forth-facing contract language or production VC generator.
