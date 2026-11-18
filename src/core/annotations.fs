\ Smart-unfolding markers (plan S2 merge B; docs/design/S2_INTERFACE.md
\ §3): Lean 4.35.0's sunfoldMatch and sunfoldMatchAlt annotations (mdata
\ entries; Meta/WHNF.lean's smartUnfoldingMatch? and
\ smartUnfoldingMatchAlt?) as one front-end-only term node,
\ ANNOTATION(child, key): its first field the annotated term, its second
\ the key, lf-annot-match or lf-annot-match-alt. Its data word is its
\ child's (core/constant-term-boundary.fs), so a walk that keeps a
\ closed subterm keeps it alike. Only the smart-unfolding bodies of the
\ elaboration data make them. The walkers that carry one, as Lean's
\ preserveMData: front/instantiate.fs (instantiate1, abstract and head
\ beta, which looks through one between lambdas as Lean's betaRev does,
\ unless asked to keep it) and front/beta-inst.fs; front/whnf.fs strips
\ the outer ones (whnfEasyCases). Other front-end walkers (mvars.fs,
\ assign-check.fs, reach.fs's sweep, term-find.fs, discr-keys.fs,
\ defeq.fs) treat the node as an opaque leaf whose data word is its
\ child's; kabstract.fs and meta-check.fs answer unsupported on it. The
\ barrier is the hand-over, which refuses a declaration reaching one
\ (error 200, front/handover.fs), and the export writer, which refuses to
\ write one (author/export.fs): so the kernel never receives one.
\ Untrusted.
\ Words: lf-tag-annotation (core/terms.fs), lf-annot-match,
\ lf-annot-match-alt, lf-annot ( child key -- t outcome ) (full when the
\ store has no room), lf-annot? ( t -- flag ), lf-annot-child ( t --
\ child ), lf-annot-key ( t -- key ), lf-annot-strip ( t -- t' ) (every
\ outer annotation dropped: consumeMData), lf-annot-keyed? ( t key --
\ child true | false ) (an annotation of that key: smartUnfoldingMatch?,
\ smartUnfoldingMatchAlt?).
\ No state of its own.

require ../lib/lib.fs
require ./terms.fs

0 constant lf-annot-match   1 constant lf-annot-match-alt

: lf-annot? ( t -- flag ) lf-term-tag@ lf-tag-annotation = ;
: lf-annot-child ( t -- child ) lf-term-first@ ;
: lf-annot-key ( t -- key ) lf-term-second@ ;
: lf-annot ( child key -- t outcome ) 2>r lf-tag-annotation 2r> lf-term-add room-result ;
: lf-annot-strip ( t -- t' ) begin dup lf-annot? while lf-annot-child repeat ;
: lf-annot-keyed? ( t key -- child true | false )
  over lf-annot? 0= if 2drop false exit then
  over lf-annot-key = if lf-annot-child true else drop false then ;
