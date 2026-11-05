\ Test driver for the whnf rows of the definitional-equality table
\ (tests/reference/definitional-equality-terms.lean; table
\ definitional-equality of tests/core/lean-differential.py; plan task
\ 4.2.2c). On top of first-checker-driver.fs, whose cases it reads: a
\ case's last declaration is a probe whose value is a constant; while the
\ probe is checked, that value is put in LeanForth's whnf (src/kernel/
\ whnf.fs) on a fresh job's frames, in the check's snapshot of the
\ checked environment, as Lean's Kernel.whnf of the constant. fc-whnf-run
\ checks the case and prints
\   WHNF <id> <answer>
\ with answer unfolds (another term), stays (the constant itself), or the
\ outcome of a whnf that failed. Test-only; nothing here accepts a
\ theorem.

require ./first-checker-driver.fs

variable fw-node  variable fw-outcome
: fw-value ( d -- node ) lf-input-decl lf-idecl-value @ ;
: fw-probe ( -- )
  fc-fuel lf-minfer-start-env lf-env-limit fw-value lf-minfer-frames lf-whnf-on
  fw-outcome ! fw-node ! ;
: fw-check ( -- ) lf-env-limit fc-last = if fw-probe then lf-check-declaration ;
: fw-answer ( -- c-addr u )
  fw-outcome @ ok? 0= if fw-outcome @ outcome-text exit then
  fw-node @ fc-last fw-value = if s" stays" else s" unfolds" then ;
: fc-whnf-run ( -- )
  -1 fw-node ! outcome-invalid fw-outcome !
  lf-input-end ok? must 64 lf-env-new ok? must dup lf-env-use ok? must
  ['] fw-check ['] fc-no-maker lf-env-run ok? must
  ." WHNF " fc-.id fw-answer type cr lf-env-free ok? must ;
