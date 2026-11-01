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

Run with the pinned toolchain:

```sh
ELAN_HOME="$PWD/.tools/elan" .tools/elan/bin/lean tests/reference/program-contracts.lean
```

This is a reference specification for future verification-condition work, not
a LeanForth program verifier. It models unbounded mathematical integers and a
partial data stack; it does not model host cell overflow, a return stack,
memory, I/O, loops, Forth parsing, a compiler or a runtime. The Lean proof is
checked by Lean, not by LeanForth. Its `wp` is a Lean function rather than an
implemented Forth-facing contract language or production VC generator.
