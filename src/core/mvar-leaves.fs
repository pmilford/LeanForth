\ Metavariables as leaves of the term and level stores (ADR 0021 D2; plan
\ task FE1b): Lean's Expr.mvar and Level.mvar, the holes the front end's
\ elaborator fills (src/front/mvars.fs keeps what each one is). A term
\ metavariable is a term node of tag lf-tag-mvar and a level metavariable
\ a level of tag lf-level-tag-mvar; for both, the first field is the
\ metavariable's number in the front end's context and the second that
\ context's epoch, so a leaf of an earlier context is never taken for a
\ later one's (src/front/mvars.fs). Only the front end makes them. The
\ kernel never receives one: Lean's export format has no metavariable,
\ the export writer refuses a kernel-form run whose stores hold any
\ (author/export.fs, lf-holes?) and a front-end run whose declarations
\ reach any (lf-author-export-reached, core/reach.fs), and the importer
\ stage refuses every record kind it does not know. The leaves are never
\ shared, as a free variable's are not (core/local-context.fs): a new
\ metavariable is always a new node with a new identity. Untrusted.
\ Words: lf-tag-mvar, lf-level-tag-mvar, lf-mvar-leaf ( n epoch -- term
\ true | false ), lf-level-mvar-leaf ( n epoch -- level true | false ),
\ lf-mvar? ( term -- flag ), lf-level-mvar? ( level -- flag ), lf-holes?
\ ( -- flag ): whether the term or level store holds a metavariable.
\ No state of its own.

require ../lib/lib.fs
require ./terms.fs
require ./levels.fs

16 constant lf-tag-mvar
5 constant lf-level-tag-mvar
lf-tag-mvar lf-term-unshare

: lf-mvar-leaf ( n epoch -- term true | false ) lf-tag-mvar -rot lf-term-add ;
: lf-level-mvar-leaf ( n epoch -- level true | false )
  >r lf-level-tag-mvar swap r> lf-level-add ;
: lf-mvar? ( term -- flag ) lf-term-tag@ lf-tag-mvar = ;
: lf-level-mvar? ( level -- flag ) lf-level-slot node-tag @ lf-level-tag-mvar = ;

\ Every node of the stores, the input view's aside (an export holds none).
: lf-term-holes? ( -- flag )
  false lf-term-count @ 0 ?do i lf-term-base + lf-mvar? or loop ;
: lf-level-holes? ( -- flag ) false lf-level-count @ 0 ?do i lf-level-mvar? or loop ;
: lf-holes? ( -- flag ) lf-term-holes? lf-level-holes? or ;
