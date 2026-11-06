\ Conversion of mixed terms: Lean's is_def_eq as LeanForth ports it
\ (defeq.fs; ADR 0014 Q1, plan tasks 4.2.2b and 4.2.2d), after a
\ complete audit of both graphs. Untrusted: not a trusted kernel or proof
\ checker. The audit checks universe parameter scope, not term binder
\ scope or typing; callers must establish those independently before
\ using a conversion result.
\ Answers: ok when Lean's is_def_eq says yes; rejected when it says no
\ (the caller reports Lean's exception for its step: declTypeMismatch,
\ appTypeMismatch) and when Lean's is_def_eq throws (an unknown constant
\ the typer or steps 12 and 14 look up, a numeral reduce_nat refuses:
\ the exception's own diagnostic, which the caller keeps);
\ lf-mixed-convert-no? ( -- flag ) tells the two apart after a
\ comparison. Unknown where the port cannot decide; invalid, exhausted or
\ full for a failure. No failure ever authorizes equality.
\ The caller may lend the port a typer (lf-dq-typer, defeq.fs), as
\ mixed-infer.fs does; without one, a no that steps 4 or 14 could have
\ turned into a yes is unknown.
\ Fuel: one budget for the audit and the comparison. lf-mixed-convert
\ leaves no fuel after any outcome but ok; lf-mixed-convert-keeping, which
\ mixed-infer uses, keeps what an unknown comparison left.
\ State: one paired walk record, lf-mconvert-walker (the audit, and the
\ fuel left), one frames record, lf-mconvert-frames (the comparison), and
\ one module record, lf-mconvert-state (whether the comparison may keep
\ its fuel when unknown; whether it answered Lean's no), all members of the checker context
\ (lib/context.fs). Single-threaded within one context; no raw or
\ concurrent mutation is safe; a comparison cannot run inside another
\ (the frames record is busy: invalid).

require ../lib/lib.fs
require ../core/constant-references.fs
require ../core/constant-term-boundary.fs
require ../core/derivation-log.fs
require ../core/diagnostics.fs
require ../core/levels.fs
require ../core/local-context.fs
require ../core/terms.fs
require ./defeq.fs
require ./mixed-compare.fs

lf-walk-room context-walk2: lf-mconvert-walker
begin-structure /lf-mcvs
  field: lf-mcvs-keep       \ true: an unknown comparison keeps its fuel
  field: lf-mcvs-no         \ true: the last comparison answered Lean's no
end-structure
/lf-mcvs context-record: lf-mconvert-state
\ The frames' visitor is never run: every visit of the port is opened
\ with frame-open, each with its own first step (defeq.fs, whnf.fs).
: lf-mconvert-no-visit ( x frames -- -1 outcome frames 0 )
  nip outcome-invalid no-result rot 0 ;
' lf-mconvert-no-visit context-frames: lf-mconvert-frames

\ Fuel left after a conversion; mixed-infer continues with it.
: lf-mconvert-fuel ( -- addr ) lf-mconvert-walker walk-fuel ;
: lf-mconvert-keep ( -- addr ) lf-mconvert-state lf-mcvs-keep ;
: lf-mconvert-said ( flag -- ) lf-mconvert-state lf-mcvs-no ! ;
\ Whether the last comparison's rejection was Lean's no, not an exception.
: lf-mixed-convert-no? ( -- flag ) lf-mconvert-state lf-mcvs-no @ ;
\ The port on the walk's fuel left after the audits: yes is ok, no is
\ rejected, recorded as not definitionally equal with both terms (a
\ caller that knows the step records its own rule in its place).
: lf-mconvert-no ( left right -- outcome )
  true lf-mconvert-said
  c" mixed-convert lf-mixed-convert" lf-diag-not-defeq lf-diag-note outcome-rejected ;
: lf-mconvert-answer ( left right flag outcome -- outcome )
  dup ok? if drop if 2drop outcome-ok else lf-mconvert-no then else nip nip nip then ;
: lf-mconvert-defeq ( left right -- outcome )
  lf-mconvert-fuel @ lf-mconvert-frames frame-budget 0= if 2drop outcome-invalid exit then
  2dup lf-mconvert-frames lf-defeq-on lf-mconvert-answer
  lf-mconvert-frames frame-fuel @ lf-mconvert-fuel ! ;

\ Compare after both audits; the term, level and reference counts are
\ restored on every result, and the local context entries of the free
\ variables the comparison made dropped, discarding all temporary
\ allocations (serials never rewind).
: lf-mconvert-marks ( -- terms levels crefs )
  lf-term-count @ lf-level-count @ lf-cref-count @ ;
: lf-mconvert-restore ( terms levels crefs -- )
  lf-cref-count ! lf-level-count ! dup lf-term-count ! lf-lctx-drop ;
\ While the caches keep scratch until the job ends (kernel/caches.fs sets
\ the hook), nothing is restored.
defer lf-mconvert-keeps? ( -- flag )
:noname ( -- flag ) false ; is lf-mconvert-keeps?
: lf-mconvert-done ( terms levels crefs -- )
  lf-mconvert-keeps? if 2drop drop else lf-mconvert-restore then ;
: lf-mconvert-run ( left right -- outcome )
  lf-mconvert-marks 2>r >r lf-mconvert-defeq r> 2r> lf-mconvert-done ;
\ An outcome but ok leaves no fuel, unless the comparison keeps it (an
\ unknown one, lf-mixed-convert-keeping).
: lf-mconvert-kept? ( outcome -- flag ) outcome-unknown = lf-mconvert-keep @ and ;
: lf-mconvert-settle ( outcome -- outcome )
  dup ok? over lf-mconvert-kept? or 0= if 0 lf-mconvert-fuel ! then ;

\ ( left left-id right right-id fuel -- status )
\ Validate both complete graphs, then compare; restore all temporary term
\ allocations on every result. Failed preflight conservatively leaves zero fuel.
: lf-mconvert-pass ( left lid right rid fuel -- status )
  lf-mconvert-walker tuck walk-budget 0= if lf-mcompare-refused exit then
  lf-mcompare-roots ok-then? if lf-mconvert-run else nip then lf-mconvert-settle ;
\ The derivation log (ADR 0013): with it on, a conversion is one defeq
\ step of left and right; both paths run the same pass.
: lf-mconvert-logged ( left lid right rid fuel -- status )
  4 pick 3 pick lf-rule-defeq lf-log-open lf-mconvert-pass lf-log-decided ;
: lf-mconvert-checked ( left lid right rid fuel -- status )
  false lf-mconvert-said lf-log? if lf-mconvert-logged else lf-mconvert-pass then ;
: lf-mixed-convert ( left lid right rid fuel -- status )
  false lf-mconvert-keep ! lf-mconvert-checked ;
: lf-mixed-convert-keeping ( left lid right rid fuel -- status )
  true lf-mconvert-keep ! lf-mconvert-checked ;

\ Recovery after a THROW out of a conversion: its records idle again
\ (the caller discards what it made, as for mixed-beta.fs's passes).
: lf-mixed-convert-reset ( -- )
  lf-mconvert-frames frame-reset lf-open-reset lf-defeq-reset ;
