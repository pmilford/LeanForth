\ Unit tests of the Meta words simp's first slice adds (plan row FE9,
\ slice SL1a-1 of docs/design/TACTIC_SIMP.md), over the simp slice and its
\ elaboration data, by the classes of docs/development/TEST_COVERAGE_REVIEW.md:
\ meta-config.fs's whnfCore settings and simp's three scopes (each value,
\ restored on both paths, a THROW included; withInferTypeConfig's
\ defaults); whnf.fs reading zetaDelta, iota, proj, zeta and beta;
\ discr-keys.fs's head-only paths and match keys; discr-tree.fs's
\ lf-dtree-match and lf-dtree-match-extra (a prefix with its extra
\ count, the star root again, none for an empty tree); meta-must.fs's
\ lf-with-new-depth; fun-info.fs's dependency facts; congr-thms.fs's
\ kinds (Eq, HAdd.hAdd, ite's subsingleton instance) and its refusals;
\ app-builder.fs's shortcuts; a heap sweep of the kinds (full or the same
\ answer, never another). Nothing here accepts a theorem.
include ../support/heap-watch.fs
require ../support/tester.fs
require ../support/meta-sweeps.fs
require ../../src/load/checker.fs
require ../../src/load/front.fs
require ../../src/cli/check-lf.fs
decimal

4000000 lf-term-capacity! drop  100000 lf-cref-capacity! drop
T{ s" tests/front/simp-slice.ndjson" true lfc-library-open -> outcome-ok }T
lf-author-begin
T{ s" tests/front/simp-slice.elab.ndjson" lfc-elab-file! lfc-elab-read lfc-rooms
   -> outcome-ok outcome-ok }T
: made ( x outcome -- x ) ok? 0= abort" simp-meta: not made" ;
: nat ( -- t ) s" Nat" lf-mk-const0 ;
: prop ( -- t ) 0 lf-term-symbolic-sort lf-made! ;
: binder ( type c-addr u -- fvar )
  lfa-intern swap lf-lctx-local made tuck swap 0 lf-local-new made
  lf-mctx-view swap lf-view-push made lf-mctx-view! ;
: code1 ( x xt -- code ) catch dup if nip then ;
nat s" n" binder constant n0
prop s" p" binder constant p0   p0 s" h" binder constant h0

\ ---- 1. Settings: 0 is Lean's default; each scope's values; restored.
: seen ( -- mode proj iota? zeta-delta? )
  lf-defeq-mode lf-meta-proj lf-meta-no-iota lf-meta-on? lf-meta-no-zeta-delta lf-meta-on? ;
T{ lf-meta-proj lf-meta-no-iota lf-meta-on? lf-meta-settings lf-meta-defaults -> lf-proj-delta true 0 }T
T{ lf-defeq-elab lf-meta-no-iota or lf-meta-defaults -> lf-defeq-elab }T
T{ ' seen lf-with-simp-keys -> lf-tr-reducible lf-proj-no false false }T
T{ ' seen lf-with-simp-index -> lf-tr-reducible lf-proj-no true false }T
T{ ' seen lf-with-simp-meta -> lf-tr-reducible lf-proj-delta true false }T
: fl ( -- flags ) lf-defeq-flags ;
T{ ' fl lf-with-simp-keys lf-meta-defaults -> lf-meta-default }T
T{ ' fl lf-with-simp-meta lf-meta-defaults -> lf-defeq-flags lf-meta-defaults }T
T{ lf-meta-config ' seen lf-with-simp-keys 2drop 2drop lf-meta-config d= -> true }T
: boom ( -- ) 7 throw ;
: after-boom ( -- flag code )
  lf-meta-config ['] boom ['] lf-with-simp-index catch nip >r lf-meta-config d= r> ;
T{ after-boom -> true 7 }T
\ Each proj kind round-trips through the flags.
: proj-as ( kind -- kind' ) mcfg-proj-bits lf-tr-default ['] lf-meta-proj -rot lf-meta-with ;
T{ lf-proj-no proj-as lf-proj-yes proj-as lf-proj-delta proj-as lf-proj-delta-i proj-as
   -> lf-proj-no lf-proj-yes lf-proj-delta lf-proj-delta-i }T

\ ---- 2. whnf.fs: zetaDelta off keeps a let variable; zeta and beta off
\ answer unsupported; iota off keeps a recursor; inferType at defaults.
: let-binder ( type value c-addr u -- fvar )
  lfa-intern -rot lf-lctx-let made tuck swap 0 lf-local-new made
  lf-mctx-view swap lf-view-push made lf-mctx-view! ;
nat n0 s" x" let-binder constant x0
: core ( e -- e' outcome ) lf-whnf-core ;
: meta-core ( e -- e' outcome ) ['] core lf-with-simp-meta ;
T{ x0 core x0 meta-core -> n0 outcome-ok x0 outcome-ok }T
T{ x0 ' core lf-with-simp-keys -> x0 outcome-ok }T
: with-bits ( e bits -- e' outcome ) ['] core swap lf-tr-default lf-meta-with ;
: lam-n ( -- e ) nat n0 lf-term-lam lf-made! ;
T{ lam-n n0 lf-mk-app lf-meta-no-beta with-bits nip lam-n n0 lf-mk-app core
   -> outcome-unsupported n0 outcome-ok }T
create xs0 x0 ,
: let-n ( -- e ) x0 xs0 1 lf-mk-let-fvars ;   \ let x : Nat := n; x
T{ let-n lf-meta-no-zeta with-bits nip let-n core -> outcome-unsupported n0 outcome-ok }T
: zero ( -- e ) s" Nat.zero" lf-mk-const0 ;
\ @Eq.rec Nat n (fun _ _ => Nat) n n (Eq.refl n): iota gives the minor n.
: motive ( -- e ) nat n0 n0 lf-mk-eq nat lf-term-lam lf-made! lf-term-lam lf-made! ;
: rec-z ( -- e )
  s" Eq.rec" 0 0 2 lf-mk-const nat lf-mk-app n0 lf-mk-app motive lf-mk-app
  n0 lf-mk-app n0 lf-mk-app n0 lf-mk-eq-refl lf-mk-app ;
\ (Eq is K-like: with iota on, toCtorWhenK is not ported, unsupported;
\ with iota off the recursor is not looked at.)
T{ rec-z core nip rec-z dup lf-meta-no-iota with-bits -rot =
   -> outcome-unsupported outcome-ok true }T
T{ x0 ' lf-infer lf-with-simp-keys swap s" Nat" lf-meta-const-named? -> outcome-ok true }T
\ Review of 2026-11-25, low 1. withInferTypeConfig: inside lf-infer the
\ settings are the defaults, so g n infers with g : T, the let T := Nat
\ -> Nat unfolded by zetaDelta (infer-at-defaults); after it simp's are
\ in force again (infer-restore).
: type0 ( -- t ) 1 lf-term-symbolic-sort lf-made! ;
type0 nat nat lf-term-pi lf-made! s" T" let-binder constant t0
t0 s" g" binder constant g0
: infer-flags ( -- type outcome flags ) g0 n0 lf-mk-app lf-infer lf-defeq-flags ;
T{ ' infer-flags lf-with-simp-index lf-meta-no-zeta-delta and 0<> swap rot
   s" Nat" lf-meta-const-named? -> true outcome-ok true }T
\ withImplicitConfig: defeq compares a postponed implicit argument at the
\ defaults, so @Eq U y y =?= @Eq Nat y y with the let U := Nat
\ (defeq-flags-dropped).
type0 nat s" U" let-binder constant u0   u0 s" y" binder constant y0
: eq-nat-y ( -- e ) n0 n0 lf-mk-eq lf-term-first@ lf-term-first@ y0 lf-mk-app y0 lf-mk-app ;
: implicit-dq ( -- flag outcome ) y0 y0 lf-mk-eq eq-nat-y lf-meta-defeq ;
T{ ' implicit-dq lf-with-simp-meta -> true outcome-ok }T

\ ---- 3. Keys: head-only paths, match keys.
: eq-nn ( -- e ) n0 n0 lf-mk-eq ;
: path-run ( e xt -- n star? ) execute made swap 1+ elab-key-star? ;
: full-path ( -- n star? ) eq-nn ['] lf-dt-path ['] path-run lf-dt-scoped ;
: head-path ( -- n star? ) eq-nn ['] lf-dt-path-head ['] path-run lf-dt-scoped ;
: path-in ( e xt -- n star? ) ['] path-run lf-dt-scoped ;
T{ eq-nn ' lf-dt-path path-in eq-nn ' lf-dt-path-head path-in -> 4 false 4 true }T
nat mv-natural lf-mvar-new made constant m0
: key-star? ( e xt -- flag ) >r true lf-dt-nil r> execute made drop elab-key-star? ;
: key-in ( e xt -- flag ) ['] key-star? lf-dt-scoped ;
T{ m0 ' lf-dt-key key-in m0 ' lf-dt-match-key key-in -> true false }T

\ ---- 4. getMatch and getMatchWithExtra on a tree: eq_n's head-only keys
\ under value 1 match any Eq; Nat.succ's keys under value 2 match
\ Nat.succ n as a prefix with one extra argument.
create tree /dtree allot   tree /dtree erase
create outs /slab allot   1 cells 1000 outs slab-init drop
: put ( e v -- ) swap lf-dt-path-head made rot tree lf-dtree-insert ok? 0= abort" not put" ;
: succ ( -- e ) s" Nat.succ" lf-mk-const0 ;
T{ outs slab-clear eq-nn tree outs lf-dtree-match outs slab-count -> outcome-ok 0 }T
T{ tree lf-dtree-ready -> outcome-ok }T
T{ eq-nn 1 put succ 2 put -> }T
: out@ ( i -- x ) outs slab-at @ ;
T{ outs slab-clear m0 m0 lf-mk-eq tree outs lf-dtree-match outs slab-count 0 out@ -> outcome-ok 1 1 }T
T{ outs slab-clear succ n0 lf-mk-app tree outs lf-dtree-match outs slab-count -> outcome-ok 0 }T
T{ outs slab-clear succ n0 lf-mk-app tree outs lf-dtree-match-extra outs slab-count 0 out@ 1 out@
   -> outcome-ok 2 2 1 }T
T{ outs slab-clear eq-nn tree outs lf-dtree-match-extra outs slab-count 0 out@ 1 out@
   -> outcome-ok 2 1 0 }T
T{ succ n0 lf-mk-app tree outs ' lf-dt-get-match-extra code1 -> 0 }T

\ ---- 5. withNewMCtxDepth: one deeper inside, put back on both paths.
T{ ' lf-mctx-depth lf-with-new-depth lf-mctx-depth - -> 1 }T
T{ lf-mctx-depth ' boom ' lf-with-new-depth catch nip swap lf-mctx-depth = -> 7 true }T

\ ---- 6. Dependency facts and congruence kinds.
\ Constants at new level metavariables: Sort ?u is no Prop, as Lean's
\ getFunInfo sees a polymorphic constant.
: fresh ( c-addr u -- f ) lfa-intern lf-menv-find made lf-meta-const-fresh made ;
: eq-c ( -- f ) s" Eq" fresh ;
T{ eq-c 63 lf-meta-fun-deps 0 lf-param-back-deps 1 lf-param-back-deps 2 lf-param-back-deps
   -> 3 outcome-ok 0 1 1 }T
T{ 0 lf-param-fwd-deps? 1 lf-param-fwd-deps? lf-fun-result-deps 0 lf-param-head -> true false 0 0 }T
: kinds ( n -- k0 .. kn-1 ) 0 ?do i lf-congr-kind loop ;
T{ eq-c lf-congr-simp-kinds 3 kinds 3 lf-congr-plain?
   -> 3 outcome-ok lf-ck-fixed lf-ck-eq lf-ck-eq true }T
: hadd ( -- f ) s" HAdd.hAdd" 0 0 0 3 lf-mk-const ;
T{ hadd lf-congr-simp-kinds nip 6 kinds 6 lf-congr-plain?
   -> outcome-ok lf-ck-fixed lf-ck-fixed lf-ck-fixed lf-ck-fixed lf-ck-eq lf-ck-eq true }T
: ite-c ( -- f ) s" ite" fresh ;
T{ ite-c lf-congr-simp-kinds 5 kinds 5 lf-congr-plain?
   -> 5 outcome-ok lf-ck-fixed lf-ck-eq lf-ck-subsingleton lf-ck-eq lf-ck-eq false }T
\ A function of no parameters; a non-term is invalid, never kinds.
T{ n0 lf-congr-simp-kinds -> 0 outcome-ok }T
\ Every heap allocation refused in turn: full or Eq's three kinds.
: kinds-pass ( e -- n outcome ) lf-congr-simp-kinds ;
T{ eq-c ' kinds-pass heap-sweep nip -> 0 }T

\ ---- 7. Builders: the shortcuts give h back; congrFun of Eq.refl.
T{ h0 lf-mk-eq-true dup 2 s" eq_true" lf-meta-app-of? swap lf-mk-of-eq-true -> true h0 }T
p0 s" True" lf-mk-const0 lf-mk-eq s" hq" binder constant hq0
T{ hq0 lf-mk-of-eq-true 2 s" of_eq_true" lf-meta-app-of? -> true }T
\ mkAppM's mismatch (h : p is no p = True, no ¬p): rejected, thrown.
T{ h0 ' lf-mk-of-eq-true code1 h0 ' lf-mk-eq-false code1 -> -4204 -4204 }T
: refl-f ( -- h ) succ lf-mk-eq-refl ;
T{ refl-f n0 lf-mk-congr-fun lf-term-second@ succ n0 lf-mk-app lf-meta-eqv -> true outcome-ok }T
T{ h0 n0 ' lf-mk-congr-fun catch nip nip 0<> -> true }T
T{ refl-f n0 lf-mk-eq-refl lf-mk-congr 2 s" Eq.refl" lf-meta-app-of? -> true }T

\ ---- 8. Each remaining branch (make cover-changed, 2026-11-25).
\ mkCongr: h2 refl gives mkCongrFun of h1 (refused unless refl); neither
\ refl unsupported; the shortcuts of mkEqTrue and mkEqFalse.
: refl-n ( -- h ) n0 lf-mk-eq-refl ;
T{ refl-f refl-n lf-mk-congr 2 s" Eq.refl" lf-meta-app-of? -> true }T
T{ hq0 refl-n ' lf-mk-congr catch nip nip hq0 hq0 ' lf-mk-congr catch nip nip -> -4205 -4205 }T
T{ hq0 lf-mk-of-eq-true lf-mk-eq-true -> hq0 }T
: not-p-false ( -- h ) s" of_eq_false" lf-mk-const0 p0 lf-mk-app h0 lf-mk-app ;
T{ not-p-false lf-mk-eq-false -> h0 }T
\ A proof parameter is cast: of_eq_true {p} (h : p = True) : p.
: oet ( -- f ) s" of_eq_true" lf-mk-const0 ;
T{ oet lf-congr-simp-kinds 2 kinds 2 lf-congr-plain? -> 2 outcome-ok lf-ck-fixed lf-ck-cast false }T
\ More than 62 parameters: unsupported, never kinds.
: big-pi ( -- t ) nat 63 0 do nat swap lf-term-pi lf-made! loop ;
big-pi s" big" binder constant big0
T{ big0 lf-congr-simp-kinds nip -> outcome-unsupported }T
\ A let at an application's head under zeta off: unsupported.
T{ let-n n0 lf-mk-app lf-meta-no-zeta with-bits nip -> outcome-unsupported }T
\ match-extra on an application whose root key is other (a metavariable
\ head): no prefix tried; getMatch's throwing face.
T{ outs slab-clear m0 n0 lf-mk-app tree outs lf-dtree-match-extra outs slab-count -> outcome-ok 0 }T
T{ succ n0 lf-mk-app tree outs ' lf-dt-get-match code1 -> 0 }T
\ @id Nat n: a constant head no root has (Eq's and Nat.succ's differ in
\ their declaration): no prefix may match, none.
: id-n ( -- e ) s" id" 0 lf-mk-const1 nat lf-mk-app n0 lf-mk-app ;
T{ outs slab-clear id-n tree outs lf-dtree-match-extra outs slab-count -> outcome-ok 0 }T
\ Every heap allocation of a match-extra query and of the kinds refused
\ in turn, the slabs they claim given back first: full or the answer.
: simp-slabs-anew ( -- )
  dk-cells sweep-slab-anew dk-args sweep-slab-anew dk-kinds sweep-slab-anew
  fi-params sweep-slab-anew fi-deps sweep-slab-anew ck-kinds sweep-slab-anew
  dts sweep-slab-anew outs slab-clear ;
' simp-slabs-anew sweep-slabs-xt !
: mx ( e -- n outcome ) outs slab-clear tree outs lf-dtree-match-extra outs slab-count swap ;
T{ succ n0 lf-mk-app ' mx heap-sweep nip -> 0 }T
T{ eq-c ' kinds-pass heap-sweep nip -> 0 }T
\ A projection n.0 under proj := no stays at once; under yes its
\ structure goes through whnfCore (n, no constructor: it stays).
n0 s" Nat" lfa-intern 0 lf-proj-of made constant pj0
T{ pj0 lf-proj-no mcfg-proj-bits with-bits pj0 lf-proj-yes mcfg-proj-bits with-bits
   -> pj0 outcome-ok pj0 outcome-ok }T
\ A type whose head past the pis is a lambda: undecided, -1.
T{ lam-n n0 lf-mk-app fi-head-name -> -1 }T
\ The head-name facts of congr-thms.fs one by one: Nat no class, so no
\ instance; id a definition Lean would unfold, undecided; a class under a
\ constructor (getClassSubobjectMask?, SL2) unsupported; a name no
\ declaration has no kind.
: nm ( c-addr u -- name ) lfa-intern ;
T{ s" Nat" nm ck-named-inst s" id" nm ck-named-inst -> false outcome-ok false outcome-unsupported }T
T{ true cks cks-ctor ! s" Decidable" nm ck-named-inst false cks cks-ctor ! -> false outcome-unsupported }T
T{ s" No.such.name" nm dup ck-decl-kind swap ck-class? -> -1 false }T
\ On ite's facts with its instance's head changed: undecided (-1) and a
\ definition head refused; Decidable with no eq parameter before it fixed.
T{ ite-c lf-congr-simp-kinds -> 5 outcome-ok }T
: param-head! ( name i -- ) fi-deps slab-at cell+ ! ;
T{ -1 2 param-head! 2 ck-instance? s" id" nm 2 param-head! 2 ck-plain-kind 2 ck-inst-kind
   -> false outcome-unsupported -1 outcome-unsupported -1 outcome-unsupported }T
T{ s" Decidable" nm 2 param-head! lf-ck-fixed 1 ck-kind! 2 ck-inst-kind -> lf-ck-fixed outcome-ok }T
