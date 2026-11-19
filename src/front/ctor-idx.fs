\ T.ctorIdx, the index of the constructor a value of an inductive type is
\ made with (plan row FE6), built as Lean 4.35.0's mkCtorIdx
\ (src/Lean/Meta/Constructions/CtorIdx.lean) builds it, on a job of
\ src/front/constructions.fs:
\   T.ctorIdx.{us} : {params} -> {indices} -> T params indices -> Nat
\   fun {params} {indices} x => T.casesOn.{1, us} params
\     (fun {indices} x => Nat) indices x (fun fields => c) ...
\ with c each constructor's index as a raw natural-number literal; just 0
\ when T has one constructor. The parameters and indices are the binders
\ of T's type made implicit (withImplicitBinderInfos), the fields of each
\ constructor the binders of its type after the parameters. Lean names
\ the arrow's binder afresh (mkArrow, x with macro scopes); here it is x,
\ so no type equals Lean's export node for node, only up to binder names
\ (aux-alike?), and other names come from T's type and constructors as the
\ export shows them, which may be a shared term's (constructions.fs, the
\ limit of review fe6a M1).
\ When Lean makes one: mkCtorIdx itself skips a Prop former and a type
\ eliminating only into Prop (unsupported here, with that reason); but
\ mkAuxConstructions calls it only when Nat is already declared (hasNat),
\ the option genCtorIdx can turn it off, a private type's is not exported,
\ and Lean.Grind.ToInt's dates from stage0. None of that is in an export,
\ so this builds one for every type that passes mkCtorIdx's own tests:
\ on Init twelve types Lean has none for (PUnit, PEmpty, Empty, Inhabited,
\ Decidable and BEq, declared before Nat; the private HasModel and four
\ private structures of Std.Format; Lean.Grind.ToInt), pinned by name in
\ tests/front/constructions-init.sh. The front end decides with its own
\ environment and options when it declares a type (plan FE6).
\ Outcomes: ok with the type and value (aux-type@, aux-value@);
\ unsupported, with the reason, as above and for a type whose Sort only
\ reduction shows; invalid for a constructor missing from the export;
\ full when the scratch tier refuses a name; otherwise as aux-cases-on.
\ Untrusted front-end code, compared with Lean's by
\ tests/front/constructions-init.sh.
\ State: none of its own; the job record (/aux) holds everything.

require ../lib/decimal.fs
require ./constructions.fs

\ ---- T's numbers, binders and constructors.
: type-item ( i job -- u ) dup aux-type @ swap decl-of staged-item ;
: type-params ( job -- n ) more-type-params swap type-item ;
: type-indices ( job -- n ) more-type-indices swap type-item ;
: ind-ctors ( job -- t ) more-type-ctors swap type-item ;
: ctor-count ( job -- n ) dup ind-ctors swap aux-tuples tuple-length ;
: xs-count ( job -- n ) dup type-params swap type-indices + ;
: type-pi ( j job -- e ) >r r@ type-type swap r> nth-pi ;
: type-binder ( j job -- head dom ) tuck type-pi swap pi-parts ;
\ A binder made implicit: as a Pi, as a fun.
: implicit ( head -- head' ) dup head-payload swap plain-binder 1+ swap pack-head ;
: implicit-lam ( head -- head' ) implicit pi>lam ;
\ Constructor c of T (from 0), its index, fields and type.
: ctor-name ( c job -- n ) dup ind-ctors swap aux-tuples tuple-item ;
: ctor-decl ( c job -- d true | false ) tuck ctor-name swap aux-stage @ stage-find ;
: ctor-item ( i job -- u ) dup aux-ctor @ swap decl-of staged-item ;
: ctor-index ( job -- u ) more-ctor-cidx swap ctor-item ;
: ctor-fields ( job -- n ) more-ctor-fields swap ctor-item ;
: ctor-type ( job -- e ) dup aux-ctor @ swap decl-of staged-type@ ;

\ ---- Small terms.
: nat-literal ( u job -- e outcome )
  >r u>decimal r@ aux-tier tier-texts text-intern
  ok-then? if r> aux-tier expr-nat else r> drop no-result then ;
\ A top-level name, made in the scratch tier when the input lacks it: its
\ number and ok, or -1 and full.
: top-name ( c-addr u job -- n outcome ) >r 0 -rot r> aux-tier name-str ;
: empty-levels ( job -- t outcome ) dup tuple-begin tuple-done ;
: nat-name ( job -- n outcome ) >r s" Nat" r> top-name ;
: nat-const ( job -- e outcome )
  dup nat-name ok-keep? 0= if exit then
  swap dup empty-levels ok-keep? if swap aux-tier expr-const else failed-past then ;
\ The binder x, as a fun and as a Pi, with domain dom around body; its
\ name made once per build (x-ready).
: x-ready ( job -- outcome )
  >r s" x" r@ top-name r> aux-x swap ok-store ;
: x-lam ( dom body job -- e outcome )
  >r r@ aux-x @ 0 lam-head -rot r> aux-tier expr-make ;
: x-pi ( dom body job -- e outcome ) >r r@ aux-x @ 0 pi-head -rot r> aux-tier expr-make ;
\ T.{us} applied to the parameters, from variable pfirst down, then to
\ the indices, from variable k - 1 down (k the indices).
: down-var ( f i job -- e outcome ) tuck aux-span @ swap - swap apply-var ;
: vars, ( f n job -- e outcome ) ['] down-var ok-fold ;
: ind-const ( job -- e outcome )
  dup type-levels ok-keep? 0= if exit then
  swap dup >r type-name swap r> aux-tier expr-const ;
: ind-params ( pfirst job -- e outcome )
  tuck aux-span ! dup ind-const ok-keep? if swap dup type-params swap vars, then ;
: ind-app ( pfirst job -- e outcome )
  tuck ind-params ok-keep? 0= if exit then
  swap dup type-indices 1- over aux-span ! dup type-indices swap vars, ;

\ ---- The type: Pi {params} {indices} (x : T params indices), Nat.
: xs-binder ( job j -- job outcome )
  over tuck type-binder swap implicit swap rot binder, outcome-ok ;
: xs-binders ( job -- outcome ) dup xs-count ['] xs-binder ok-each nip ;
: arrow-domain ( job -- e outcome ) dup xs-count 1- swap ind-app ;
: arrow ( job -- e outcome )
  dup arrow-domain ok-keep? 0= if exit then
  over nat-const ok-keep? 0= if failed-past exit then rot x-pi ;
: idx-type! ( job -- outcome )
  dup arrow ok-keep? 0= if nip exit then
  over aux-pis ok-keep? if swap aux-built-type ! outcome-ok else nip then ;

\ ---- The value's pieces. The motive: fun {indices} (x : T params
\ indices) => Nat, in the context of the parameters, indices and x.
: motive-x ( job -- e outcome )
  dup dup type-params over type-indices 2* + swap ind-app ok-keep? 0= if exit then
  over nat-const ok-keep? 0= if failed-past exit then rot x-lam ;
: motive-binder ( j job -- head dom outcome )
  2dup lifting tuck type-params + over type-binder rot run-remap ;
: motive-step ( body i job -- e outcome )
  tuck aux-span @ swap - over motive-binder ok-then?
  if swap implicit-lam swap make-binder else nip nip nip no-result then ;
: motive ( job -- e outcome )
  dup motive-x ok-keep? 0= if exit then swap dup type-indices 1- over aux-span !
  dup type-indices swap ['] motive-step ok-fold ;
\ Constructor c's alternative: fun fields => c's index; the fields'
\ types moved past the indices and x.
: field-pi ( q job -- e ) >r r@ type-params + r@ ctor-type swap r> nth-pi ;
: field-binder ( q job -- head dom outcome )
  2dup lifting tuck field-pi over pi-parts rot run-remap ;
: alt-step ( body i job -- e outcome )
  tuck m-last over field-binder ok-then?
  if swap pi>lam swap make-binder else nip nip nip no-result then ;
: no-ctor ( c job -- -1 outcome )
  nip c" a constructor missing from the export" swap aux-invalid no-result ;
: alt ( c job -- e outcome )
  2dup ctor-decl 0= if no-ctor exit then over aux-ctor ! nip
  dup ctor-index over nat-literal ok-keep? 0= if exit then
  swap dup ctor-fields over aux-span ! ['] alt-step m-fold ;
: apply-alt ( f c job -- e outcome )
  tuck alt ok-keep? if swap aux-tier expr-app else failed-past then ;
\ A fold whose alternatives each fold their fields.
: alts, ( f job -- e outcome ) dup ctor-count swap ['] apply-alt ok-fold ;

\ ---- The value, grown in aux-built-value: T.casesOn.{1, us} params
\ motive indices x alternatives, then fun x, then the implicit funs.
: grown ( job e outcome -- outcome )
  ok-keep? if swap aux-built-value ! outcome-ok else nip then ;
: grow ( job xt -- outcome ) >r dup aux-value@ over r> execute grown ;
: one-levels ( job -- t outcome )
  dup tuple-begin ['] level-one, ok-with ['] type-levels-add ok-with tuple-done ;
: one-cases ( job -- e outcome )
  dup cases-name 0= if no-cases exit then
  over one-levels ok-keep? if rot aux-tier expr-const else failed-past then ;
: with-params ( f job -- e outcome )
  dup xs-count over aux-span ! dup type-params swap vars, ;
: with-motive ( f job -- e outcome )
  dup motive ok-keep? if swap aux-tier expr-app else failed-past then ;
: with-indices ( f job -- e outcome )
  dup type-indices over aux-span ! dup type-indices swap vars, ;
: with-x ( f job -- e outcome ) 0 swap apply-var ;
: +params ( job -- outcome ) ['] with-params grow ;
: +motive ( job -- outcome ) ['] with-motive grow ;
: +indices ( job -- outcome ) ['] with-indices grow ;
: +x ( job -- outcome ) ['] with-x grow ;
: +alts ( job -- outcome ) ['] alts, grow ;
: start-cases ( job -- outcome ) dup one-cases grown ;
: cases-app ( job -- outcome )
  dup start-cases ['] +params ok-with ['] +motive ok-with ['] +indices ok-with
  ['] +x ok-with ['] +alts ok-with nip ;
: idx-body ( job -- outcome )
  dup ctor-count 1 = if 0 over nat-literal grown exit then cases-app ;
: x-wrapped ( job -- e outcome )
  dup arrow-domain ok-keep? 0= if exit then over aux-value@ rot x-lam ;
: wrap-x ( job -- outcome ) dup x-wrapped grown ;
: wrap-xs ( job -- outcome ) dup aux-value@ over aux-lams grown ;
: idx-value! ( job -- outcome )
  dup idx-body ['] wrap-x ok-with ['] wrap-xs ok-with nip ;

\ ---- ctorIdx.
: no-prop ( job -- outcome ) c" Lean makes no ctorIdx for a Prop" swap aux-refuse ;
: no-large ( job -- outcome )
  c" Lean makes no ctorIdx for a type eliminating into Prop only" swap aux-refuse ;
: idx-ready ( job -- outcome )
  dup type-end over aux-tier expr-tag@ tag-sort <> if no-sort exit then
  dup prop-former? if no-prop exit then dup large? 0= if no-large exit then
  dup type-names swap aux-built-params ! outcome-ok ;
: ctor-idx ( job -- outcome )
  dup idx-ready ['] x-ready ok-with ['] xs-binders ok-with ['] idx-type! ok-with
  ['] idx-value! ok-with nip ;
: aux-ctor-idx ( d job -- outcome )
  tuck aux-begin ['] ctor-idx ok-with swap aux-because ;
