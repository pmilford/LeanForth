\ Simp's theorem set for simp only (plan row FE9, simp slice SL1a-1 of
\ docs/design/TACTIC_SIMP.md): Lean 4.35.0's SimpTheorems as
\ elabSimpArgs fills it (src/lean/Lean/Meta/Tactic/Simp/SimpTheorems.lean;
\ Elab/Tactic/Simp.lean:268-300, 512). A theorem is a record of the
\ context slab simp-thms; its number is the value the set's two trees
\ (pre and post, discr-tree.fs) hold under its keys.
\ - lf-simp-set-new ( -- ): an empty set. The trees' keys are elab-keys
\   (elab-keys.fs) of the key scope its caller opened (discr-keys.fs's
\   lf-dt-scoped around the whole simp call), so they live as long as the
\   set is used.
\ - lf-simp-add-decl ( d post -- ): mkSimpTheoremFromConst d (453), not
\   inverted, at the default priority 1000, origin .decl: d's type under
\   simpGlobalConfig (meta-config.fs's lf-with-simp-keys), one
\   metavariable depth deeper, through forallMetaTelescopeReducing (its
\   level parameters fresh level metavariables), must be an Eq
\   (shouldPreprocess, 311: any other proposition needs a helper theorem
\   `_simp_1` and is unsupported until SL3d); its left side's full keys
\   (mkPath, noIndexAtArgs false, 470); its rfl flag Lean's defeq tag
\   (isRflProof of a constant: simp-data.fs's simp-defeq?); a perm theorem
\   (isPerm, 291: here any theorem whose sides are two metavariables or
\   applications of the same head to as many arguments) unsupported until
\   SL3d (acLt).
\ - lf-simp-add-hyp ( h post -- ): mkSimpTheoremFromExpr (502) of the
\   hypothesis h (a free variable), origin .stx (Elab/Tactic/Simp.lean:
\   363): its type, whnf'd under mkIndexConfig (lf-with-simp-index), must
\   be an Eq (a proposition p, an Iff or a forall is preprocessed by Lean:
\   SL1a-2, SL1b, unsupported here); head-only keys (lf-dt-path-head,
\   noIndexAtArgs true, 509); rfl false (isRflProof of a free variable).
\ A theorem whose proof is in the set already takes its record again
\   (insertVal's BEq SimpTheorem compares proofs, Basic.lean:139).
\ - lf-simp-pre lf-simp-post ( -- tree ); lf-simp-thms# ( -- n );
\   lf-simp-thm-proof ( t -- x ) (the declaration, or the free variable),
\   lf-simp-thm-decl? lf-simp-thm-post? lf-simp-thm-rfl? ( t -- flag ),
\   lf-simp-thm-prio ( t -- n ).
\ Throws as meta-must.fs's words do. Untrusted: a theorem only proposes
\ a rewrite whose proof the kernel checks. State: the slab simp-thms and
\ the two tree records, given back by lf-simp-set-new and the teardown.
\ Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../../lib/lib.fs
require ../../lib/slab.fs
require ../../lib/context.fs
require ../discr-tree.fs
require ../simp-data.fs
require ../app-builder.fs

begin-structure /sth
  field: sth-proof   \ the declaration, or the hypothesis's free variable
  field: sth-decl?   \ true: sth-proof is a declaration (origin .decl)
  field: sth-post   field: sth-prio   field: sth-rfl
end-structure
/sth context-slab: simp-thms
/dtree context-record: simp-pre-tree
/dtree context-record: simp-post-tree
: sth-trees-free ( -- ) simp-pre-tree lf-dtree-free simp-post-tree lf-dtree-free ;
' sth-trees-free context-teardown
1000 constant lf-simp-default-prio
: lf-simp-set-new ( -- ) simp-thms slab-clear sth-trees-free ;
: lf-simp-pre ( -- tree ) simp-pre-tree ;
: lf-simp-post ( -- tree ) simp-post-tree ;
: lf-simp-thms# ( -- n ) simp-thms slab-count ;
: sth ( t -- addr ) simp-thms slab-at ;
: lf-simp-thm-proof ( t -- x ) sth sth-proof @ ;
: lf-simp-thm-decl? ( t -- flag ) sth sth-decl? @ ;
: lf-simp-thm-post? ( t -- flag ) sth sth-post @ ;
: lf-simp-thm-prio ( t -- n ) sth sth-prio @ ;
: lf-simp-thm-rfl? ( t -- flag ) sth sth-rfl @ ;

\ ---- The record: found by its proof, else claimed.
: sth-same? ( proof decl? t -- flag )
  sth dup sth-decl? @ rot = >r sth-proof @ = r> and ;
: sth-find ( proof decl? -- t true | false )
  lf-simp-thms# 0 ?do 2dup i sth-same? if 2drop i true unloop exit then loop 2drop false ;
: sth-new ( proof decl? -- t )
  1 simp-thms slab-claim lf-must dup >r sth tuck sth-decl? ! sth-proof ! r> ;
: sth-claim ( proof decl? -- t ) 2dup sth-find if nip nip else sth-new then ;
: sth-flags! ( post rfl t -- t )
  dup >r sth tuck sth-rfl ! tuck sth-post ! lf-simp-default-prio swap sth-prio ! r> ;
: sth-tree ( post -- tree ) if simp-post-tree else simp-pre-tree then ;
: sth-insert ( t k n -- )
  rot dup lf-simp-thm-post? sth-tree dup lf-dtree-ready lf-must lf-dtree-insert lf-must ;

\ ---- The keys (mkSimpTheoremKeys, 380): the left side of an Eq.
\ isPerm (291), kept on the side of caution: two metavariables, or two
\ applications of the same head to as many arguments, may be a perm.
: sth-perm? ( lhs rhs -- flag )
  2dup lf-mvar? swap lf-mvar? and if 2drop true exit then
  lf-meta-head-args rot lf-meta-head-args rot = >r lf-meta-eqv lf-must r> and ;
: sth-lhs ( type -- lhs )
  lf-eq? 0= if lf-unported then rot drop 2dup sth-perm? if lf-unported then drop ;
: sth-decl-path ( d -- k n ) lf-const-meta-applied nip sth-lhs lf-dt-path lf-must ;
: sth-decl-keyed ( d -- k n ) ['] sth-decl-path lf-with-simp-keys ;
: sth-decl-keys ( d -- k n ) ['] sth-decl-keyed lf-with-new-depth ;
: sth-decl-rfl ( d -- flag ) lf-menv-elab 0= if lf-unported then simp-defeq? lf-must ;
: lf-simp-add-decl ( d post -- )
  over sth-decl-rfl rot dup >r true sth-claim sth-flags! r> sth-decl-keys sth-insert ;
: sth-hyp-path ( h -- k n )
  lf-infer! lf-instantiate! lf-whnf-r! sth-lhs lf-dt-path-head lf-must ;
: sth-hyp-keyed ( h -- k n ) ['] sth-hyp-path lf-with-simp-index ;
: lf-simp-add-hyp ( h post -- )
  over false sth-claim false swap sth-flags! swap ['] sth-hyp-keyed lf-with-new-depth
  sth-insert ;

base !   \ the BASE this file was loaded with
