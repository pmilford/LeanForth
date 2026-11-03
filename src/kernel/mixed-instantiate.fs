\ Untrusted capture-avoiding single-binder instantiation of mixed terms.
\ This is syntax transformation, not type checking or theorem acceptance.
\ State: one job record, lf-minst-job (fields lf-instjob-*): the pass's
\ frames (fuel, nesting, and the binder depth as context), the replacement
\ and the term count before the pass; a member of the checker context
\ (lib/context.fs), whose frames a set-up word prepares in every context.
\ The replacement is shifted on mixed-shift's record. Single-threaded
\ within one context; callers must not mutate the stores concurrently.

require ../lib/lib.fs
require ../core/constant-term-boundary.fs
require ../core/diagnostics.fs
require ../core/tagged-sort-boundary.fs
require ../core/terms.fs
require ./mixed-rebuild.fs
require ./mixed-shift.fs

\ The frames come first, so the visitor finds the job record at the
\ address of the frames it is given (checked here), as in mixed-shift.fs.
begin-structure /lf-instjob
  /frames +field lf-instjob-frames   \ fuel, nesting, the binder depth as context
  field: lf-instjob-replacement      \ the term put in for the target variable
  field: lf-instjob-start            \ term count before the pass
end-structure
0 lf-instjob-frames 0<> [if] .( mixed-instantiate.fs: frames come first) cr abort [then]
/lf-instjob context-record: lf-minst-job

: lf-minst-frames ( -- frames ) lf-minst-job lf-instjob-frames ;
\ Fuel left after an instantiation; mixed-beta and mixed-infer continue
\ with it.
: lf-minst-fuel ( -- addr ) lf-minst-frames frame-fuel ;
: lf-minst-replacement ( -- addr ) lf-minst-job lf-instjob-replacement ;
: lf-minst-start ( -- addr ) lf-minst-job lf-instjob-start ;

\ Only nodes of the original input, below the starting count, are visited,
\ and a child must precede its parent (so it is old too).
: lf-minst-old? ( node frames -- flag ) lf-instjob-start @ 0 swap within ;
: lf-minst-readable? ( node frames -- flag )
  over swap lf-minst-old? swap lf-term-valid? and ;
: lf-minst-below? ( child node -- flag ) 0 swap within ;
: lf-minst-first? ( node -- flag ) dup lf-term-first@ swap lf-minst-below? ;
: lf-minst-second? ( node -- flag ) dup lf-term-second@ swap lf-minst-below? ;
: lf-minst-children? ( node -- flag ) dup lf-minst-first? swap lf-minst-second? and ;

\ Bound variables at binder depth d: a local one (index below d) is kept;
\ the target (index d) becomes the replacement shifted by d, with the
\ remaining shared fuel; outer ones are lowered by one. A negative index or
\ a nonzero second field is malformed.
: lf-minst-replace ( frames -- result outcome )
  dup lf-instjob-replacement @ over frame-context @ rot lf-mshift-inside ;
: lf-minst-lower ( index -- result outcome ) 1- lf-term-bvar lf-rebuild-allocated ;
: lf-minst-outer ( index frames -- result outcome )
  2dup frame-context @ = if nip lf-minst-replace else drop lf-minst-lower then ;
: lf-minst-variable ( node index frames -- result outcome )
  2dup frame-context @ < if 2drop outcome-ok else rot drop lf-minst-outer then ;
: lf-minst-bvar? ( node -- flag ) dup lf-term-first@ swap lf-term-second@ lf-repr-leaf? ;
: lf-minst-bvar ( node frames -- result outcome )
  over lf-minst-bvar? 0= if lf-rebuild-bad exit then
  over lf-term-first@ swap lf-minst-variable ;

\ Visiting one source node. Application, lambda and Pi nodes are rebuilt;
\ leaves are kept; any other tag is malformed. Each visit costs one unit of
\ fuel.
: lf-minst-binary ( node frames -- result outcome )
  over lf-minst-children? if lf-rebuild-binary else lf-rebuild-bad then ;
: lf-minst-leaf ( node frames tag -- result outcome )
  case lf-tag-bvar of lf-minst-bvar endof
    lf-tag-constant of lf-rebuild-keep endof
    lf-tag-symbolic-sort of lf-rebuild-keep endof
    >r lf-rebuild-bad r> endcase ;
: lf-minst-visit ( node frames -- result outcome )
  2dup lf-minst-readable? lf-rebuild-tag
  dup lf-term-binary-tag? if drop lf-minst-binary else lf-minst-leaf then ;
\ The frames and their visitor, set up once in every context.
: lf-minst-setup ( -- )
  lf-term-capacity ['] lf-minst-visit lf-minst-frames frame-init ;
' lf-minst-setup context-setup

\ Validate both complete handles with one fuel budget before allocating, even
\ when the replacement is unused. Roll back term allocations on every failure;
\ allocation serials are intentionally never rewound. Constant and Sort nodes
\ are reused with their stamps. Identities are session-local; resets
\ invalidate handles. Child indices rely on backward edges and no raw
\ mutation or count edits during their lifetime. Fuel charges both audits,
\ source visits and each replacement shift visit. No type, scope, proof, or
\ executable-program correctness is established. Negative fuel and a failed
\ validation leave zero remaining fuel as a conservative bound.
: lf-minst-audit ( source sid replacement rid -- source sid replacement rid outcome )
  2over lf-minst-frames lf-rebuild-audit
  dup ok? if drop 2dup lf-minst-frames lf-rebuild-audit then ;
: lf-minst-refuse ( source sid replacement rid outcome -- -1 0 outcome )
  >r 2drop 2drop r> lf-rebuild-none ;
: lf-minst-unfueled ( source sid replacement rid -- -1 0 status )
  0 lf-minst-fuel ! outcome-invalid lf-minst-refuse ;
: lf-minst-begin ( source replacement -- source context frames )
  lf-minst-replacement ! lf-term-count @ lf-minst-start ! 0 lf-minst-frames ;
\ Running out of fuel or frames is recorded as a diagnostic.
: lf-minst-site ( -- site ) c" mixed-instantiate lf-mixed-instantiate" ;
: lf-minst-explain ( outcome -- outcome ) lf-minst-frames lf-minst-site lf-diag-frames ;
: lf-mixed-instantiate ( source sid replacement rid fuel -- result id status )
  lf-minst-frames frame-budget 0= if lf-minst-unfueled exit then
  lf-minst-audit dup ok? 0= if lf-minst-refuse exit then
  2drop nip lf-minst-begin lf-rebuild-run lf-minst-explain ;
