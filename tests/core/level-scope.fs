\ Tests for untrusted symbolic universe structure and parameter contexts.
include ../support/tester.fs
require ../../src/core/level-scope.fs
require ../../src/core/levels.fs
require ../support/store-faults.fs

\ Zero and a parameterized expression are structurally valid in context.
lf-level-reset lf-lscope-context-reset
T{ 0 1 lf-lscope-check -> outcome-ok }T
T{ 2 lf-lscope-context-add -> true }T
T{ 2 lf-lscope-context-add -> false }T
T{ 0 lf-lscope-context-add -> false }T
T{ 2 lf-level-param -> 1 true }T
T{ 1 lf-level-succ -> 2 true }T
T{ 0 2 lf-level-imax -> 3 true }T
T{ 3 4 lf-lscope-check -> outcome-ok }T
T{ 3 3 lf-lscope-check -> outcome-exhausted }T
T{ 3 -1 lf-lscope-check -> outcome-invalid }T
T{ -1 10 lf-lscope-check -> outcome-invalid }T
T{ 4 10 lf-lscope-check -> outcome-invalid }T
\ The check is refused at its root when the store's seal is broken, the
\ count still sound (compact-store plan step S2: its reads check the index).
level-seal-flip
T{ 3 10 lf-lscope-check 3 lf-level-root? 3 lf-level-valid?
   -> outcome-invalid false true }T
level-seal-flip
T{ 3 10 lf-lscope-check 3 lf-level-root? 4 lf-level-valid? -> outcome-ok true false }T
lf-lscope-context-reset
T{ 3 10 lf-lscope-check -> outcome-invalid }T
T{ 2 lf-lscope-context-add -> true }T
T{ 3 10 lf-lscope-check -> outcome-ok }T

\ Shared DAG occurrences consume fuel for each visit, not each unique node.
lf-level-reset lf-lscope-context-reset
T{ 0 0 lf-level-max -> 1 true }T
T{ 1 1 lf-level-max -> 2 true }T
T{ 2 7 lf-lscope-check -> outcome-ok }T
T{ 2 6 lf-lscope-check -> outcome-exhausted }T

\ Corrupt tags, reserved fields, self references and zero node are rejected.
99 2 level-tag!
T{ 2 20 lf-lscope-check -> outcome-invalid }T
lf-level-tag-max 2 level-tag!
2 2 level-first!
T{ 2 20 lf-lscope-check -> outcome-invalid }T
1 2 level-first!
1 0 level-first!
T{ 2 20 lf-lscope-check -> outcome-invalid }T
0 0 level-first!
T{ 2 20 lf-lscope-check -> outcome-ok }T
lf-level-reset
T{ 0 lf-level-succ -> 1 true }T
1 1 level-second!
T{ 1 20 lf-lscope-check -> outcome-invalid }T
0 1 level-second!
T{ 1 20 lf-lscope-check -> outcome-ok }T

\ Corrupt context counts, identifiers and duplicate entries are invalid.
lf-lscope-context-reset
T{ 2 lf-lscope-context-add -> true }T
T{ 3 lf-lscope-context-add -> true }T
2 lf-lscope-context cell+ !
T{ 0 10 lf-lscope-check -> outcome-invalid }T
T{ 4 lf-lscope-context-add -> false }T
T{ lf-lscope-context-count @ -> 2 }T
0 lf-lscope-context cell+ !
T{ 0 10 lf-lscope-check -> outcome-invalid }T
-1 lf-lscope-context-count !
T{ 0 10 lf-lscope-check -> outcome-invalid }T
T{ 4 lf-lscope-context-add -> false }T
lf-lscope-ids slab-capacity 1+ lf-lscope-context-count !
T{ 0 10 lf-lscope-check -> outcome-invalid }T
lf-lscope-context-reset
T{ 0 1 lf-lscope-check -> outcome-ok }T

\ A corrupted parameter payload or reserved field must never validate.
lf-level-reset lf-lscope-context-reset
T{ 2 lf-lscope-context-add -> true }T
T{ 2 lf-level-param -> 1 true }T
0 1 level-first!
T{ 1 10 lf-lscope-check -> outcome-invalid }T
2 1 level-first!
1 1 level-second!
T{ 1 10 lf-lscope-check -> outcome-invalid }T
0 1 level-second!
T{ 1 10 lf-lscope-check -> outcome-ok }T

\ The parameter context has no fixed limit (plan task 6.2.0): it grows to
\ 1,000 parameters and more, refuses a repeat, and its audit (the hashed
\ table, which grows too) still finds a corrupted repeat among them.
lf-lscope-context-reset
: fill-level-context ( n -- )
  0 do i 1+ lf-lscope-context-add 0= if -1 throw then loop ;
1000 fill-level-context
T{ 1001 lf-lscope-context-add 500 lf-lscope-context-add -> true false }T
T{ lf-lscope-context-count @ -> 1001 }T
T{ 1 10 lf-lscope-check -> outcome-ok }T
T{ lf-level-count @ -> 2 }T
T{ 1000 lf-lscope-member? 1002 lf-lscope-member? -> true false }T
7 999 lf-lscope-slot !
T{ 1 10 lf-lscope-check lf-lscope-context-valid? -> outcome-invalid false }T
1000 999 lf-lscope-slot !
T{ lf-lscope-context-valid? -> true }T
\ Entries the audit passed are compared with its copy whole: a repeat put
\ in the last or the first slot after a pass at the same count is found
\ too (review rvPF1 2), and the restored entries pass again.
7 1000 lf-lscope-slot !
T{ lf-lscope-context-valid? -> false }T
1001 1000 lf-lscope-slot !
1000 0 lf-lscope-slot !
T{ lf-lscope-context-valid? -> false }T
1 0 lf-lscope-slot !
T{ lf-lscope-context-valid? lf-lscope-state lf-lsctx-passed @ -> true 1002 }T

\ The copy's count is checked against the copy's capacity before the
\ compared range is formed (review rvPF1 3): with no copy held (its slab
\ empty, as in a new context) and a corrupted count claiming two IDs, the
\ entries go to the audit, which finds a repeat, or passes them and keeps
\ them; nothing is read beyond the copy (without the check, from address
\ 0).
lf-lscope-context-reset
T{ 2 lf-lscope-context-add 3 lf-lscope-context-add -> true true }T
lf-lscope-audited slab-free  1 cells dup slab-limit-max lf-lscope-audited slab-init drop
3 lf-lscope-state lf-lsctx-passed !
2 1 lf-lscope-slot !
T{ ' lf-lscope-context-valid? catch lf-lscope-audited slab-capacity -> false 0 0 }T
3 1 lf-lscope-slot !
T{ ' lf-lscope-context-valid? catch lf-lscope-state lf-lsctx-passed @ -> true 0 3 }T
T{ lf-lscope-audited slab-capacity 2 < -> false }T

\ A parameter's visit: ok for an ID in the context, invalid outside it
\ (lf-lscope-param-in, beside the flag lf-lscope-in? that searches a
\ prefix of the context).
lf-lscope-context-reset
T{ 5 lf-lscope-context-add -> true }T
T{ 5 lf-lscope-param-in 6 lf-lscope-param-in -> outcome-ok outcome-invalid }T
T{ 5 1 lf-lscope-in? 6 1 lf-lscope-in? -> true false }T

\ The audit's hash table masks with slots - 1, so the slot count must be a
\ power of two, at least twice the entries; the audit checks it before
\ using the table.
T{ 0 lf-lscope-slots 16 lf-lscope-slots 17 lf-lscope-slots -> 32 32 64 }T
T{ 1000 lf-lscope-slots dup lf-lscope-power-of-two? swap 2000 < 0= -> true true }T
T{ 1 lf-lscope-power-of-two? 2 lf-lscope-power-of-two? 128 lf-lscope-power-of-two? -> true true true }T
T{ 0 lf-lscope-power-of-two? 3 lf-lscope-power-of-two? 200 lf-lscope-power-of-two? -> false false false }T
bye
