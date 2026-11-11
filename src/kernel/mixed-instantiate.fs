\ Untrusted capture-avoiding single-binder instantiation of mixed terms.
\ This is syntax transformation, not type checking or theorem acceptance.
\ It is Lean's instantiate of one term (instantiate.cpp 15-37, a replace;
\ compact-store plan step S6, plan task 6.5.5): a binary node whose data
\ word (core/terms.fs) shows no loose bound variable at or beyond the
\ binder depth comes back unchanged without a visit below it (22), every
\ other binary node's result is kept for the rest of the call in the
\ replace memo (replace-memo.fs, keyed by the node and its depth) and
\ given back when the node is met again there, and a node whose children
\ come back unchanged is kept (update_app, update_binding). The target
\ variable becomes the replacement lifted by the depth (lift_loose_bvars,
\ mixed-shift.fs). Each visit costs one unit of fuel, a kept or
\ remembered node only its own.
\ State: one job record, lf-minst-job (fields lf-instjob-*): the pass's
\ frames (fuel, nesting, and the binder depth as context), the replacement
\ and a mark of the term store before the pass, and the replace memo
\ lf-minst-memo; members of the checker context
\ (lib/context.fs), whose frames a set-up word prepares in every context.
\ The replacement is shifted on mixed-shift's record. Single-threaded
\ within one context; callers must not mutate the stores concurrently.

require ../lib/lib.fs
require ../core/constant-term-boundary.fs
require ../core/derivation-log.fs
require ../core/diagnostics.fs
require ../core/local-context.fs
require ../core/tagged-sort-boundary.fs
require ../core/terms.fs
require ./mixed-rebuild.fs
require ./mixed-shift.fs
require ./replace-memo.fs

\ The frames come first, so the visitor finds the job record at the
\ address of the frames it is given (checked here), as in mixed-shift.fs.
begin-structure /lf-instjob
  /frames +field lf-instjob-frames   \ fuel, nesting, the binder depth as context
  field: lf-instjob-replacement      \ the term put in for the target variable
  /store-mark +field lf-instjob-start  \ the term store before the pass
end-structure
0 lf-instjob-frames 0<> [if] .( mixed-instantiate.fs: frames come first) cr abort [then]
/lf-instjob context-record: lf-minst-job
\ The replace memo, freed with the context.
/lf-rmemo context-record: lf-minst-memo
:noname ( -- ) lf-minst-memo lf-rmemo-release ; context-teardown

: lf-minst-frames ( -- frames ) lf-minst-job lf-instjob-frames ;
\ Fuel left after an instantiation; mixed-beta and mixed-infer continue
\ with it.
: lf-minst-fuel ( -- addr ) lf-minst-frames frame-fuel ;
: lf-minst-replacement ( -- addr ) lf-minst-job lf-instjob-replacement ;
: lf-minst-start ( -- addr ) lf-minst-job lf-instjob-start ;

\ Only nodes of the original input, below the term store's mark taken when
\ the pass starts, are visited, and a child must precede its parent (so it
\ is old too). The mark (lib/store.fs) is a boundary to read below, never
\ rolled back to; the pass's rollback is the rebuild's scratch mark
\ (mixed-rebuild.fs).
: lf-minst-old? ( node frames -- flag ) lf-instjob-start mark-count @ 0 swap within ;
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
\ leaves are kept (free variables too, which the audit found live); any
\ other tag is malformed. Each visit costs one unit of fuel.
\ Binary nodes (see the header): unchanged by the data word, given back
\ by the memo, or rebuilt as mixed-rebuild.fs's passes are, then kept.
: lf-minst-clean? ( node frames -- flag )
  swap lf-term-data@ if lf-data-loose swap frame-context @ > 0= else drop false then ;
: lf-minst-known? ( node frames -- result true | false )
  frame-context @ lf-minst-memo lf-rmemo@ ;
: lf-minst-keep ( result node frames -- ) frame-context @ lf-minst-memo lf-rmemo! ;
: lf-minst-update ( r1 node r2 -- result outcome )
  over >r lf-replace-update dup ok? if over r@ lf-minst-frames lf-minst-keep then r> drop ;
: lf-minst-updated ( r2 outcome frames -- result outcome frames 0 )
  ['] lf-minst-update lf-rebuild-joined ;
: lf-minst-second ( r1 outcome frames -- second frames next | -1 outcome frames 0 )
  ['] lf-minst-updated lf-rebuild-next ;
: lf-minst-rebuild ( node frames -- ... frames next )
  2dup lf-rebuild-stuck? if nip >r lf-rebuild-deep r> 0 exit then
  ['] lf-minst-second lf-rebuild-first ;
: lf-minst-pair ( node frames -- ... frames next )
  2dup lf-minst-clean? if lf-replace-same exit then
  2dup lf-minst-known? if lf-replace-recall else lf-minst-rebuild then ;
: lf-minst-binary ( node frames -- ... frames next )
  over lf-minst-children? if lf-minst-pair else lf-rebuild-refuse then ;
: lf-minst-leaf ( node frames tag -- result outcome )
  case lf-tag-bvar of lf-minst-bvar endof  lf-tag-fvar of lf-rebuild-keep endof
    lf-tag-constant of lf-rebuild-keep endof  lf-tag-proj of lf-rebuild-keep endof
    lf-tag-lit of lf-rebuild-keep endof  lf-tag-let of lf-rebuild-keep endof
    lf-tag-str of lf-rebuild-keep endof
    lf-tag-symbolic-sort of lf-rebuild-keep endof
    >r lf-rebuild-bad r> endcase ;
\ The visit's first step (lib/frame.fs).
: lf-minst-visit ( node frames -- ... frames next )
  2dup lf-minst-readable? lf-rebuild-tag
  dup lf-term-binary-tag? if drop lf-minst-binary else over >r lf-minst-leaf r> 0 then ;
\ The frames and their visitor, set up once in every context; their stack
\ is freed with the context.
: lf-minst-setup ( -- ) ['] lf-minst-visit lf-minst-frames frame-init ;
' lf-minst-setup context-setup
: lf-minst-free ( -- ) lf-minst-frames frame-free ;
' lf-minst-free context-teardown

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
: lf-minst-marked ( -- outcome ) lf-minst-start lf-terms store-mark ;
: lf-minst-begin ( source replacement -- source context frames )
  lf-minst-replacement ! 0 lf-minst-frames ;
\ Running out of fuel or frames is recorded as a diagnostic.
: lf-minst-site ( -- site ) c" mixed-instantiate lf-mixed-instantiate" ;
: lf-minst-explain ( outcome -- outcome ) lf-minst-frames lf-minst-site lf-diag-frames ;
: lf-minst-memo-end ( outcome -- outcome ) dup lf-minst-memo lf-rmemo-end ;
: lf-minst-pass ( source sid replacement rid fuel -- result id status )
  lf-minst-frames frame-budget 0= if lf-minst-unfueled exit then
  lf-minst-audit dup ok? 0= if lf-minst-refuse exit then drop
  lf-minst-marked dup ok? 0= if lf-minst-refuse exit then
  2drop nip 0 lf-minst-memo lf-rmemo-begin
  lf-minst-begin lf-rebuild-run lf-minst-explain lf-minst-memo-end ;
\ The derivation log (ADR 0013): with it on, the pass is one instantiate
\ step of the source and the replacement; both paths run the same pass.
: lf-minst-logged ( source sid replacement rid fuel -- result id status )
  4 pick 3 pick lf-rule-instantiate lf-log-open lf-minst-pass lf-log-close-handle ;
: lf-mixed-instantiate ( source sid replacement rid fuel -- result id status )
  lf-log? if lf-minst-logged else lf-minst-pass then ;
