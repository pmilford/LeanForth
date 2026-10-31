\ Untrusted experiment for closed, axiom-free candidate theorem declarations.
\ It returns a diagnostic status only: no declaration, certificate, checked
\ bit or theorem handle is created. Its components and their interaction need
\ human review and soundness work before any trusted use. Global mutable state
\ and no concurrent arena mutation are assumed throughout the experiment.
include infer.fs

variable lf-probe-type
variable lf-probe-value
variable lf-probe-start

\ Translate comparison results explicitly instead of assuming matching numeric
\ status values. An unexpected status is invalid, never successful.
: lf-probe-compare-status ( status -- status )
  case
    lf-compare-equal of lf-infer-ok endof
    lf-compare-invalid of lf-infer-invalid endof
    lf-compare-exhausted of lf-infer-exhausted endof
    lf-compare-unknown of lf-infer-unknown endof
    drop lf-infer-invalid 0
  endcase ;

\ Exercise the candidate checks with a shared work budget. A non-proposition
\ or an inconclusive comparison is unknown, never an accepted theorem.
: lf-probe-walk ( fuel -- status )
  lf-probe-type @ swap lf-infer dup if nip exit then drop
  lf-infer-sortlevel dup if nip exit then drop
  0<> if lf-infer-unknown exit then
  lf-probe-value @ lf-infer-fuel @ lf-infer dup if nip exit then drop
  lf-probe-type @ lf-infer-compare lf-probe-compare-status ;

\ Probe a type/value pair and restore all temporary allocations on every path.
\ Status zero means only that this untrusted experiment found no obstacle in
\ its supported subset. Negative fuel and invalid arena counts fail closed.
: lf-declaration-probe ( type value fuel -- status )
  dup 0< if drop 2drop lf-infer-invalid exit then
  lf-term-count-valid? 0= if drop 2drop lf-infer-invalid exit then
  2 pick lf-term-valid? 2 pick lf-term-valid? and 0= if
    drop 2drop lf-infer-invalid exit
  then
  >r lf-probe-value ! lf-probe-type ! r>
  lf-term-count @ lf-probe-start !
  lf-probe-walk
  lf-probe-start @ lf-term-count ! ;
