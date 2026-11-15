\ Lean's kabstract (plan S2, branch s2-tactics; docs/design/S2_INTERFACE.md
\ 5), after Lean 4.35.0's Meta/KAbstract.lean (kabstract) and HeadIndex.lean
\ (toHeadIndex, headNumArgs): the occurrences of a pattern p in a term e
\ become a loose bound variable, the one of the binder the caller puts
\ around the result (rewrite's motive).
\ - lf-meta-kabstract ( e p -- e' flag outcome ): e instantiated; for a
\   free variable p, its occurrences abstracted syntactically (Lean's easy
\   case, Expr.abstract: instantiate.fs's lf-meta-abstract); otherwise a
\   pre-order walk, an application's function before its argument, a
\   binder's domain before its body: a subterm with no loose bound variable,
\   p's head (its constant's name, its free variable or metavariable, sort,
\   lambda, pi, literal or projection) and p's number of arguments is
\   compared with p by isDefEq, at the transparency and in the
\   configuration the caller set (rewriting's: reducible, offsets on, the
\   tactics' flags); a match becomes #k, k the binders passed, and its
\   parts are not visited; any other node is rebuilt from its parts (the
\   same node when they did not change, a binder keeping its name and
\   kind). Every occurrence is abstracted (Lean's Occurrences.all), so the
\   metavariable context is never put back: a match's assignments stay
\   for the comparisons after it, as in Lean. flag: the result has a loose
\   bound variable (Lean's eAbst.hasLooseBVars, rewrite's "found").
\   Lean visits a node shared by several parents once per path, with no
\   cache: so does this.
\ Not supported yet (unsupported): a candidate whose head, past its
\ applications, is a let (Lean looks at the let's body there); a let's
\ parts are visited value first, then the binder's type and body
\ (LeanForth's LET(v, fun x : T => b) node), where Lean visits the type
\ first: no rewrite of the proof set reaches a let.
\ Each visit spends one unit of the declaration's budget (meta-config.fs,
\ --elab-fuel): exhausted when none is left. Outcomes: ok; full when a
\ store or the heap has no room; exhausted; unsupported as above; the
\ outcome of isDefEq, instantiateMVars or abstract when not ok (an
\ internal code made invalid, outcome-sane). -1 and false whenever the
\ outcome is not ok. Untrusted: only the kernel's check of the finished
\ proof decides anything.
\ Example: in 0 + (k + 1) = k + 1, the pattern ?n + Nat.succ ?m (with
\ ?n := 0, ?m := k assigned on the way) gives #0 = k + 1 and true; k + 1
\ is compared with 0 + Nat.succ k and is no match at reducible
\ transparency.
\ State: the record kab (the pattern, its head and argument count) and
\ the slabs kab-todo (the walk's work: node and offset, rebuild or visit)
\ and kab-images (the images made), in the checker context (ADR 0009).
\ Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/slab.fs
require ../core/terms.fs
require ../core/constant-term-boundary.fs
require ../core/let-terms.fs
require ./mvars.fs
require ./meta-config.fs
require ./meta-spine.fs
require ./instantiate.fs
require ./defeq.fs

begin-structure /kab
  field: kab-pattern     \ p
  field: kab-head        \ p's head, past its applications
  field: kab-args        \ and the number of its arguments
end-structure
/kab context-record: kab
2 cells context-slab: kab-todo     \ node, offset * 2 + 1 to rebuild or + 0 to visit
1 cells context-slab: kab-images   \ the images made, the last on top

\ ---- Heads (Lean's toHeadIndex): the same tag and, for a constant, the
\ same name; a projection, the same structure and field (its leaf); a
\ free variable, metavariable or literal, the same node.
: kab-tag= ( h1 h2 -- flag ) lf-term-tag@ swap lf-term-tag@ = ;
: kab-names= ( h1 h2 -- flag ) lf-const-name swap lf-const-name = ;
: kab-fields= ( h1 h2 -- flag ) lf-term-first@ swap lf-term-first@ = ;
: kab-tag-only? ( tag -- flag )
  dup lf-tag-sort = over lf-tag-lam = or swap lf-tag-pi = or ;
: kab-same ( h1 h2 tag -- flag )
  case lf-tag-constant of kab-names= endof  lf-tag-projection of kab-fields= endof
    >r = r> endcase ;
: kab-heads= ( h1 h2 -- flag )
  2dup kab-tag= 0= if 2drop false exit then
  dup lf-term-tag@ dup kab-tag-only? if drop 2drop true else kab-same then ;
\ e has p's head and number of arguments.
: kab-shaped? ( e -- flag )
  lf-meta-head-args kab kab-args @ = swap kab kab-head @ kab-heads= and ;

\ ---- A candidate: no loose bound variable (lf-meta-loose), a head that is
\ no let, p's shape; then isDefEq decides.
: kab-closed? ( e -- flag outcome ) lf-meta-loose ok-then? if 0= outcome-ok else false
  swap then ;
: kab-let-head ( e -- flag outcome )
  lf-meta-head-args drop lf-let? if false outcome-unsupported else false outcome-ok then ;
: kab-candidate? ( e -- flag outcome )
  dup kab-closed? ok-then? 0= if nip false swap exit then
  0= if drop false outcome-ok exit then
  dup kab-let-head ok-then? 0= if nip false swap exit then drop
  kab-shaped? outcome-ok ;
: kab-defeq ( e -- flag outcome ) kab kab-pattern @ lf-meta-defeq outcome-sane ;
: kab-matched? ( e -- flag outcome )
  dup kab-candidate? ok-then? 0= if nip false swap exit then
  if kab-defeq else drop false outcome-ok then ;

\ ---- The walk's work and images.
: kab-push ( e code -- outcome ) kab-todo slab-2push ;
: kab-visit+ ( e off -- outcome ) 2* kab-push ;
: kab-build+ ( e off -- outcome ) 2* 1+ kab-push ;
: kab-image ( x -- outcome ) kab-images slab-push ;
: kab-bvar ( off -- outcome ) lf-term-bvar if kab-image else outcome-full then ;
\ A binary node's parts: the second under one more binder for a binder.
: kab-second+ ( e off -- outcome )
  over lf-term-tag@ lf-term-inner if swap lf-term-second@ swap kab-visit+ else
    drop outcome-full then ;
: kab-first+ ( e off -- outcome ) swap lf-term-first@ swap kab-visit+ ;
\ The node is rebuilt once both parts are visited, the first part first.
: kab-open ( e off -- outcome )
  2dup kab-build+ ok-then2? 0= if exit then 2dup kab-second+ ok-then2? 0= if exit then
  kab-first+ ;
: kab-visit ( e off -- outcome )
  over kab-matched? ok-then? 0= if nip nip exit then if nip kab-bvar exit then
  over lf-term-binary? if kab-open else drop kab-image then ;

\ ---- Rebuilding: e's tag over the two images, the same node when they
\ are e's own parts; a new binder keeps e's name and kind.
: kab-parts= ( e f s -- flag ) rot tuck lf-term-second@ = -rot lf-term-first@ = and ;
: kab-node ( e f s -- e' outcome )
  rot >r r@ lf-term-tag@ lf-term-binary if r> lf-meta-named else r> drop
    outcome-full no-result then ;
: kab-rebuilt ( e f s -- e' outcome )
  >r 2dup r@ kab-parts= if drop r> drop outcome-ok else r> kab-node then ;
: kab-pair ( -- f s ) kab-images slab-pop kab-images slab-pop swap ;
: kab-build ( e off -- outcome )
  drop kab-pair kab-rebuilt ok-then? if kab-image then ;

\ ---- The loop (lib/slab.fs's worklist drain): one unit of the budget a
\ visit.
: kab-paid ( e off -- outcome )
  lf-meta-spend? if kab-visit else 2drop outcome-exhausted then ;
: kab-step ( e code -- flag outcome )
  2 /mod swap if kab-build else kab-paid then true swap ;
: kab-run ( -- outcome ) kab-todo ['] kab-step slab-2all? nip ;
: kab-pattern! ( p -- )
  dup kab kab-pattern ! lf-meta-head-args kab kab-args ! kab kab-head ! ;
: kab-start ( e p -- outcome )
  kab-pattern! kab-todo slab-clear kab-images slab-clear 0 kab-visit+ ;
: kab-walk ( e p -- e' outcome )
  kab-start dup ok? if drop kab-run then
  dup ok? if drop kab-images slab-pop outcome-ok else no-result then ;
: kab-fvar ( e p -- e' outcome ) kab kab-pattern ! kab kab-pattern 1 lf-meta-abstract ;
: kab-abstract ( e p -- e' outcome ) dup lf-meta-fvar? if kab-fvar else kab-walk then ;
: kab-none ( outcome -- -1 false outcome ) -1 false rot ;
: kab-found ( e' -- e' flag outcome )
  dup lf-meta-loose ok-then? if 0<> outcome-ok else nip kab-none then ;
: lf-meta-kabstract ( e p -- e' flag outcome )
  swap lf-instantiate-mvars ok-then? 0= if nip kab-none exit then
  swap kab-abstract ok-then? if kab-found else kab-none then ;
base !   \ the BASE this file was loaded with
