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
\   (isPerm, 291, below) unsupported until SL3d (acLt).
\ - lf-simp-add-hyp ( h post -- ): mkSimpTheoremCore (502) of the proof
\   h, a hypothesis or the term preprocess made of one (the caller's:
\   simp/preprocess.fs), origin .stx (Elab/Tactic/Simp.lean:363): its
\   type, through forallMetaTelescopeReducing and whnf'd under
\   mkIndexConfig (lf-with-simp-index), must be an Eq;
\   head-only keys (lf-dt-path-head, noIndexAtArgs true, 509); rfl false
\   (isRflProof of a term that is no constant).
\ A theorem whose proof is in the set already takes its record again
\   (insertVal's BEq SimpTheorem compares proofs, Basic.lean:139).
\ - lf-simp-pre lf-simp-post ( -- tree ); lf-simp-thms# ( -- n );
\   lf-simp-thm-proof ( t -- x ) (the declaration, or the free variable),
\   lf-simp-thm-decl? lf-simp-thm-post? lf-simp-thm-rfl? ( t -- flag ),
\   lf-simp-thm-prio ( t -- n ).
\ The default set (simp/default-set.fs, simp group 4): lf-simp-set-data!
\ ( pre-kind post-kind -- ) makes the trees ranked-record indexes
\ (data-index.fs) of format 4.1's lemmas, each root built at its first
\ query; lf-simp-default? ( -- flag ); lf-simp-data-entry ( v -- t
\ outcome ), the record of a lemma value of the data (a left-out one with
\ no proof, its rfl flag true); lf-simp-thm-usable ( t -- ), run before a
\ theorem is tried: a left-out lemma unsupported, a data lemma's keys
\ recomputed once (sth-decl-keys) and compared with its record's (any
\ difference unsupported, Lean's no_index included), a perm one
\ unsupported; lf-simp-unfold? ( d -- flag ), a definition the default
\ set unfolds. A rule added to the default set (lf-simp-add-decl,
\ lf-simp-add-hyp) forces its root first (lf-rix-force), so it goes in
\ after the root's values and a lemma the set holds keeps its record.
\ Throws as meta-must.fs's words do. Untrusted: a theorem only proposes
\ a rewrite whose proof the kernel checks. State: the slab simp-thms, the
\ two tree records and the record sts (the set is the default one),
\ given back by lf-simp-set-new and the teardown.
\ Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../../lib/lib.fs
require ../../lib/slab.fs
require ../../lib/context.fs
require ../discr-tree.fs
require ../data-index.fs
require ../simp-data.fs
require ../simp-set-data.fs
require ../term-eqv.fs
require ../app-builder.fs
require ./types.fs

begin-structure /sth
  field: sth-proof   \ the declaration, or the hypothesis's free variable
  field: sth-decl?   \ true: sth-proof is a declaration (origin .decl)
  field: sth-post   field: sth-prio   field: sth-rfl
  field: sth-data    \ the default set's lemma record + 1, -1 a left-out one, 0 none
  field: sth-checked \ true: the lemma's keys recomputed and found its record's
end-structure
/sth context-slab: simp-thms
/rix context-record: simp-pre-tree    \ data-index.fs's: a plain tree, or the
/rix context-record: simp-post-tree   \ default set's (lf-simp-set-data!)
begin-structure /sts  field: sts-default  end-structure
/sts context-record: sts
: sth-trees-free ( -- ) simp-pre-tree lf-rix-free simp-post-tree lf-rix-free ;
' sth-trees-free context-teardown
1000 constant lf-simp-default-prio
: lf-simp-set-new ( -- )
  simp-thms slab-clear sth-trees-free 0 simp-pre-tree lf-rix-kind!
  0 simp-post-tree lf-rix-kind! false sts sts-default ! ;
: lf-simp-set-data! ( pre-kind post-kind -- )
  simp-post-tree lf-rix-kind! simp-pre-tree lf-rix-kind! true sts sts-default ! ;
: lf-simp-default? ( -- flag ) sts sts-default @ ;
: lf-simp-post-tree ( -- tree ) simp-post-tree ;   \ as it is, its roots not made
: sth-rooted ( tree -- tree ) dup lf-rix-roots lf-must ;
: lf-simp-pre ( -- tree ) simp-pre-tree sth-rooted ;
: lf-simp-post ( -- tree ) simp-post-tree sth-rooted ;
: lf-simp-unfold? ( d -- flag ) lf-simp-default? if simp-unfold? else drop false then ;
: lf-simp-thms# ( -- n ) simp-thms slab-count ;
: sth ( t -- addr ) simp-thms slab-at ;
: lf-simp-thm-proof ( t -- x ) sth sth-proof @ ;
: lf-simp-thm-decl? ( t -- flag ) sth sth-decl? @ ;
: lf-simp-thm-post? ( t -- flag ) sth sth-post @ ;
: lf-simp-thm-prio ( t -- n ) sth sth-prio @ ;
: lf-simp-thm-rfl? ( t -- flag ) sth sth-rfl @ ;

\ ---- The record: found by its proof, else claimed.
: sth-same? ( proof decl? t -- flag ) sth dup sth-proof @ swap sth-decl? @ d= ;
: sth-find ( proof decl? -- t true | false )
  lf-simp-thms# 0 ?do 2dup i sth-same? if 2drop i true unloop exit then loop 2drop false ;
: sth-new ( proof decl? -- t )
  1 simp-thms slab-claim lf-must dup >r sth dup /sth erase
  tuck sth-decl? ! sth-proof ! r> ;
: sth-claim ( proof decl? -- t ) 2dup sth-find 0= if sth-new exit then nip nip ;
: sth-flags! ( post rfl t -- t )
  dup >r sth tuck sth-rfl ! tuck sth-post ! lf-simp-default-prio swap sth-prio ! r> ;
: sth-tree ( post -- tree ) if simp-post-tree else simp-pre-tree then ;
\ Lean adds a rule to a set whose trees hold every lemma already
\ (Elab/Tactic/Simp.lean:434): the default set's root of the rule's
\ first key is built before the rule goes in after its values.
: sth-root-ready ( k t -- k t ) 2dup lf-simp-thm-post? sth-tree lf-rix-force lf-must ;
: sth-insert ( t k n -- )
  rot >r over r> sth-root-ready nip
  dup lf-simp-thm-post? sth-tree lf-dtree-insert lf-must ;

\ ---- The keys (mkSimpTheoremKeys, 380): the left side of an Eq.
\ isPerm (291): two metavariables unify (isDefEq); two applications are
\ a perm when their heads and then each argument pair, left to right,
\ are; anything else is Lean's == (term-eqv.fs). Below the top, two
\ different compound terms (applications, binders, lets, projections,
\ annotations), which Lean walks into, are unsupported here.
lf-tag-sort lf-tag-symbolic-sort lf-tag-constant lf-tag-fvar lf-tag-mvar lf-tag-lit
  lf-tag-str lf-tag-bvar 8 lf-tags constant sth-leaf-tags
: sth-compound? ( e -- flag ) lf-term-tag@ sth-leaf-tags lf-tag-in? 0= ;
: sth-mvars? ( a b -- flag ) lf-mvar? swap lf-mvar? and ;
: sth-inner? ( a b -- flag )
  2dup sth-mvars? if lf-defeq! exit then
  2dup lf-eqv! if 2drop true exit then
  sth-compound? swap sth-compound? and if lf-unported then false ;
: sth-pair? ( l r j -- l r flag )
  >r 2dup r@ lf-meta-app-arg swap r> lf-meta-app-arg swap sth-inner? ;
: sth-args? ( l r n -- flag )
  0 ?do i sth-pair? 0= if 2drop false unloop exit then loop 2drop true ;
: sth-heads? ( l r -- flag ) lf-meta-head swap lf-meta-head swap sth-inner? ;
: sth-perm? ( lhs rhs -- flag )
  over lf-meta-args# over lf-meta-args# over <> if drop 2drop false exit then
  dup 0= if drop sth-inner? exit then
  >r 2dup sth-heads? if r> sth-args? else r> drop 2drop false then ;
: sth-lhs ( type -- lhs ) lf-simp-sides 2dup sth-perm? if lf-unported then drop ;
: sth-decl-path ( d -- k n ) lf-const-meta-applied nip sth-lhs lf-dt-path lf-must ;
: sth-decl-keyed ( d -- k n ) ['] sth-decl-path lf-with-simp-keys ;
: sth-decl-keys ( d -- k n ) ['] sth-decl-keyed lf-with-new-depth ;
: sth-decl-rfl ( d -- flag ) lf-menv-elab 0= if lf-unported then simp-defeq? lf-must ;
\ Its root built first, so that a lemma the default set holds already
\ keeps its record (insertVal's equality by proof: replaced in place).
: sth-forced ( k post -- ) sth-tree lf-rix-force lf-must ;
: lf-simp-add-decl ( d post -- )
  over sth-decl-keys 2>r 2r@ drop over sth-forced
  over sth-decl-rfl rot true sth-claim sth-flags! 2r> sth-insert ;
: sth-body ( type -- body ) 0 swap -1 ['] 2drop lf-forall-meta-telescope-reducing nip ;
: sth-hyp-path ( h -- k n )
  lf-infer! lf-instantiate! sth-body lf-whnf-r! sth-lhs lf-dt-path-head lf-must ;
: sth-hyp-keyed ( h -- k n ) ['] sth-hyp-path lf-with-simp-index ;
: lf-simp-add-hyp ( h post -- )
  over false sth-claim false swap sth-flags! swap ['] sth-hyp-keyed lf-with-new-depth
  sth-insert ;

\ ---- The default set's lemmas (simp/default-set.fs's trees): a record
\ per value of the data, made when its root is built.
\ A data lemma whose proof the library cannot decode (a string literal,
\ plan S5: unsupported) is kept as one the library lacks: its record is
\ made, and unsupported when the rewrite reaches it in candidate order.
: sth-undecoded ( x outcome -- x' outcome' )
  dup outcome-unsupported = if 2drop -1 outcome-ok then ;
: sth-v-proof ( v -- x outcome )
  dup 0< if drop -1 outcome-ok else simp-lemma-proof lf-menv-of-data sth-undecoded then ;
: sth-v-rfl ( v -- flag ) dup 0< if drop true else simp-lemma-rfl? then ;
: sth-v-data ( v -- x ) dup 0< if drop -1 else 1+ then ;
: sth-put ( v addr xt off -- v addr ) >r >r over r> execute over r> + ! ;
: sth-fill ( v addr -- )
  dup /sth erase true over sth-decl? !  ['] sth-v-rfl 0 sth-rfl sth-put
  ['] simp-lemma-post? 0 sth-post sth-put  ['] simp-lemma-prio 0 sth-prio sth-put
  ['] sth-v-data 0 sth-data sth-put 2drop ;
: sth-proof! ( x addr -- ) over 0< if -1 over sth-data ! then sth-proof ! ;
: lf-simp-data-entry ( v -- t outcome )
  dup sth-v-proof ok-then? 0= if nip no-result exit then
  1 simp-thms slab-claim ok-then? 0= if nip nip no-result exit then
  >r swap r@ sth sth-fill r@ sth sth-proof! r> outcome-ok ;
\ Before a lemma is tried: one the library lacks unsupported (its
\ statement is unknown); a data lemma's keys recomputed from its proof's
\ statement once, which must be its record's (a recorded star where the
\ statement gives a term, Lean's no_index, is not supported yet); a perm
\ lemma unsupported (acLt, slice SL3d).
: sth-keys= ( k n k' n' -- flag )
  rot over <> if 2drop drop false exit then
  0 ?do over i + over i + elab-key= 0= if 2drop false unloop exit then loop 2drop true ;
: sth-record ( t -- i ) sth sth-data @ 1- ;
: sth-same-keys ( t -- )
  dup sth-record simp-lemma-keys rot lf-simp-thm-proof sth-decl-keys sth-keys=
  0= if lf-unported then ;
: sth-check ( t -- )
  dup sth-record simp-lemma-perm? if lf-unported then
  dup sth-same-keys true swap sth sth-checked ! ;
: lf-simp-thm-usable ( t -- )
  dup sth sth-data @ dup 0< if lf-unported then
  0= over sth sth-checked @ or if drop exit then sth-check ;

base !   \ the BASE this file was loaded with
