# Program contracts: Lean reference model

`tests/reference/program-contracts.lean` defines a small reference stack
language with literal push, duplicate and addition. Its `wp` function computes
the weakest precondition for successful execution of a finite instruction list
against a postcondition. Lean proves that this precondition is equivalent to
successful modeled execution with the postcondition, and proves a composition
rule for two instruction lists. The reference checks a symbolic duplicate-and-
add example and rejects duplicate on an empty stack.

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
