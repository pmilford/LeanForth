\ T.casesOn for a type whose recursor has several motives: a mutual type,
\ or a nested one such as Lean.Syntax, whose recursor also eliminates the
\ Array and List of it (plan row FE6; src/front/constructions.fs builds
\ the one-motive case). Lean's C++ mk_cases_on (lean_mk_cases_on,
\ Meta/Constructions/CasesOn.lean) keeps T's own motive and the minor
\ premises whose conclusion is that motive, and gives the recursor, for
\ every other motive x, fun ys => PUnit.{u}, and for every other minor
\ premise fun fields hyps => PUnit.unit.{u}, u the motive's universe; the
\ types of the hypotheses about other motives become PUnit.{u} (the
\ recursor's type instantiated with those motives, beta-reduced). So for
\ Lean.Syntax:
\   Lean.Syntax.casesOn : (motive_1 : Syntax -> Sort u) -> (t : Syntax) ->
\     missing -> node -> atom -> ident -> motive_1 t
\   fun motive_1 t missing node atom ident => Lean.Syntax.rec motive_1
\     (fun t => PUnit) (fun t => PUnit) missing
\     (fun info kind args args_ih => node info kind args) ...
\     (fun toList toList_ih => PUnit.unit) PUnit.unit
\     (fun head tail head_ih toList_ih => PUnit.unit) t
\ The binders move between the recursor's context and casesOn's with the
\ table map of front/expr-remap.fs: T's motive goes to its new place, the
\ parameters after it, and anything naming another motive or a dropped
\ binder is refused. aux-cases-on-any builds either case.
\ Outcomes: as aux-cases-on; unsupported for several motives eliminating
\ only into Prop (Lean's choice of unit there is not ported: no type of
\ Init has it); invalid when T is not among its recursor's types.
\ Untrusted front-end code, compared with Lean's by
\ tests/front/constructions-init.sh.
\ State: none of its own; the job record (/aux) holds everything.

require ./constructions.fs

\ ---- T's motive and the minor premises it keeps.
: rec-all ( job -- t ) more-rec-all swap rec-item ;
: all-count ( job -- n ) dup rec-all swap aux-tuples tuple-length ;
: all-name ( i job -- n ) dup rec-all swap aux-tuples tuple-item ;
: main-index ( job -- i | -1 )
  dup all-count 0 ?do
    i over all-name over type-name = if drop i unloop exit then
  loop drop -1 ;
\ Motives as slots from the innermost: T's, and minor i's.
: main-slot ( job -- x ) dup aux-motives @ 1- swap aux-main @ - ;
: minor-slot ( i job -- x ) 2dup minor-type over target rot - nip ;
: minor-main? ( i job -- flag ) tuck minor-slot swap main-slot = ;
: kept-before ( i job -- n ) 0 rot 0 ?do over i swap minor-main? - loop nip ;
: kept-count ( job -- n ) dup aux-minors @ swap kept-before ;
\ T's motive's variable in casesOn's value: past the kept minor premises,
\ the major premise and the indices.
: motive-place ( job -- t ) dup aux-indices @ 1+ swap aux-kept @ + ;

\ ---- The renumbering table (front/expr-remap.fs, table map).
: block-grow ( u addr -- outcome )
  tuck @ ?dup if swap resize else allocate then
  if 2drop outcome-full else swap ! outcome-ok then ;
: table-reserve ( n job -- outcome )
  2dup aux-table-room @ > 0= if 2drop outcome-ok exit then
  over cells over aux-table block-grow
  ok-then? if aux-table-room ! outcome-ok else nip then ;
: table-cell ( r job -- addr ) aux-table @ swap cells + ;
: table-size ( lead job -- n ) aux-motives @ + ;
: table-start ( lead job -- )
  tuck table-size 0 ?do -1 over i swap table-cell ! loop drop ;
: main-cell ( lead job -- addr ) tuck main-slot + swap table-cell ;
: table-delta! ( lead t job -- ) >r 1+ swap r@ table-size - r> aux-remap remap-delta! ;
: table-map! ( lead job -- )
  tuck table-size over aux-table @ swap rot aux-remap remap-table! ;
\ From a context of lead binders inside the motives to one where T's
\ motive is variable t and the parameters follow it: the lead binders
\ and every other motive refused.
: motive-table ( lead t job -- )
  >r 2dup r@ table-delta! over r@ table-start over r@ main-cell !
  0 r@ at-cutoff r> table-map! ;

\ ---- The type's binders: parameters, T's motive, indices and major
\ premise, T's minor premises without hypotheses.
: params-copy ( job -- outcome ) dup aux-params @ swap ['] copy-binder aux-each ;
: motive-shift ( job -- job )
  dup aux-remap >r 0 r@ remap-cutoff! dup aux-main @ 0 r> remap-shift! ;
: main-motive-binder ( job -- outcome )
  motive-shift dup aux-params @ over aux-main @ + swap with-domain moved ;
: index-drop ( j job -- )
  tuck at-cutoff dup aux-minors @ over aux-motives @ +
  1 rot aux-remap remap-shift! ;
: several-index ( j job -- outcome )
  2dup index-drop tuck first-index + swap with-domain moved ;
: several-indices ( job -- outcome )
  dup aux-indices @ 1+ swap ['] several-index aux-each ;
: kept-table ( i job -- ) 2dup kept-before over aux-indices @ 1+ + swap motive-table ;
: several-minor ( i job -- outcome )
  2dup minor-main? 0= if 2drop outcome-ok exit then
  2dup stripped ok-keep? 0= if nip nip exit then
  >r 2dup kept-table tuck first-minor + swap r> swap moved ;
: several-minors ( job -- outcome ) dup aux-minors @ swap ['] several-minor aux-each ;
\ The conclusion: indices and major past the kept minors, T's motive.
: conclusion-lead ( job -- n ) dup aux-indices @ 1+ swap aux-minors @ + ;
: index-cells ( job -- )
  dup aux-indices @ 1+ 0 ?do i over aux-kept @ + over i swap table-cell ! loop drop ;
: several-conclusion ( job -- e outcome )
  dup conclusion-lead over motive-place rot >r r@ motive-table r@ index-cells
  r@ rec-end r> run-remap ;
: several-type! ( job -- outcome ) dup several-conclusion type-around ;

\ ---- PUnit.{u} and PUnit.unit.{u}, u the motive's universe.
\ The names, made in the scratch tier when the input lacks them: the
\ number and ok, or -1 and full.
: punit-name ( job -- n outcome ) >r 0 s" PUnit" r> aux-tier name-str ;
: unit-name ( job -- n outcome )
  >r r@ punit-name ok-then? 0= if r> drop no-result exit then
  s" unit" r> aux-tier name-str ;
: elim-add ( job -- outcome )
  dup rec-params over aux-names ! 0 over param-level
  ok-keep? if swap aux-tuples tuple-add else nip then ;
: elim-levels ( job -- t outcome ) dup tuple-begin ['] elim-add aux-then tuple-done ;
: elim-const ( n job -- e outcome )
  tuck elim-levels ok-keep? if rot aux-tier expr-const else failed-past then ;
: punit ( job -- e outcome ) dup punit-name ok-keep? if swap elim-const then ;
: unit-body ( job -- e outcome ) dup unit-name ok-keep? if swap elim-const then ;

\ ---- A minor premise in casesOn's value: its type with every
\ hypothesis about another motive ending in PUnit.{u}, moved into the
\ value's context, then fun fields hyps => T's minor fields, or PUnit.unit.
: ih-slot ( dom q job -- x ) rot over target rot - swap aux-minor @ - ;
: other-slot? ( x job -- flag ) 2dup aux-motives @ u< -rot main-slot <> and ;
: other-ih? ( q job -- flag ) dup >r 2dup m-domain -rot ih-slot r> other-slot? ;
: ih-last ( i job -- q ) aux-ih-span @ 1- swap - ;
: ih-pi ( q job -- e ) >r r@ aux-ih @ swap r> nth-pi ;
: ih-step ( body i job -- e outcome )
  tuck ih-last over ih-pi over pi-parts make-binder ;
\ Not a fold: it runs inside the fold over the minor premise's binders.
: ih-wrap ( body job -- e outcome )
  dup aux-ih-span @ 0 ?do
    tuck i swap ih-step ok-keep? 0= if unloop exit then swap
  loop drop outcome-ok ;
: unit-ih ( dom job -- e outcome )
  tuck aux-ih ! dup aux-ih @ over pi-count over aux-ih-span !
  dup punit ok-keep? if swap ih-wrap then ;
: minor-domain ( q job -- dom outcome )
  2dup other-ih? if tuck m-domain swap unit-ih else m-domain outcome-ok then ;
: minor-step ( body q job -- e outcome )
  2dup minor-domain ok-keep? 0= if 2swap 2drop exit then
  >r tuck m-pi over aux-tier expr-head@ r> make-binder ;
: m-before ( i job -- q ) m-count 1- swap - ;
: unit-step ( body i job -- e outcome ) tuck m-before swap minor-step ;
: mtype! ( job e outcome -- outcome )
  ok-keep? if swap aux-mtype ! outcome-ok else nip then ;
: unit-fold ( e job -- e' outcome ) dup m-count swap ['] unit-step fold-with ;
\ The conclusion, which may name another motive, becomes Prop: only the
\ binders are used.
: closed-end ( job -- e outcome ) level-zero swap aux-tier expr-sort ;
: unit-ihs ( job -- outcome )
  dup closed-end ok-keep? 0= if nip exit then over unit-fold mtype! ;
: value-table ( i job -- ) dup motive-place swap motive-table ;
: several-ready ( i job -- outcome )
  2dup m-open 0= if drop nip interleaved exit then over aux-span !
  dup unit-ihs ok-then? 0= if nip exit then tuck value-table m-move ;
\ T's kept minor i': variable m' - 1 - i' past the minor premise's binders.
: kept-head ( job -- b )
  dup aux-minor @ over kept-before >r dup aux-span @ swap aux-kept @ 1- + r> - ;
: minor-body ( i job -- e outcome )
  tuck minor-main? if dup kept-head swap m-body-at else unit-body then ;
: minor-arg ( j job -- e outcome )
  tuck first-minor - swap 2dup several-ready
  ok-then? 0= if nip no-result exit then
  tuck minor-body ok-keep? if swap ['] m-lam-step m-fold then ;

\ ---- The recursor's other arguments.
: param-var ( j job -- e outcome ) tuck aux-count @ 1- swap - swap aux-var ;
: index-var ( j job -- e outcome )
  tuck first-index - over motive-place 1- swap - swap aux-var ;
: motive-var ( job -- e outcome ) dup motive-place swap aux-var ;
\ Another motive x: fun ys => PUnit.{u}, its binders moved past T's.
: unit-shift ( x job -- )
  dup aux-remap >r 0 r@ remap-cutoff! motive-place 1+ r> remap-shift! ;
: lams-around ( body job -- e outcome )
  dup m-count over aux-span ! ['] m-lam-step m-fold ;
: unit-motive ( x job -- e outcome )
  2dup unit-shift tuck aux-params @ + over rec-domain over run-remap
  ok-keep? 0= if exit then over aux-mtype ! dup punit ok-keep? if swap lams-around then ;
: motive-arg ( j job -- e outcome )
  tuck aux-params @ - 2dup swap aux-main @ =
  if drop motive-var else swap unit-motive then ;
: several-arg ( j job -- e outcome )
  2dup aux-params @ < if param-var exit then
  2dup first-minor < if motive-arg exit then
  2dup first-index < if minor-arg exit then index-var ;
: several-body ( job -- e outcome ) ['] several-arg over aux-arg ! generic-body ;
: several-value! ( job -- outcome ) ['] several-body over aux-body ! built-value! ;

\ ---- casesOn, one motive or several.
: not-among ( job -- outcome )
  c" a type not among its recursor's types" swap aux-invalid ;
: prop-only ( job -- outcome )
  c" several motives eliminating into Prop only" swap aux-refuse ;
: several-check ( job -- outcome )
  dup main-index dup 0< if drop not-among exit then over aux-main !
  dup large? 0= if prop-only exit then
  dup kept-count over aux-kept ! dup rec-total swap table-reserve ;
: several-cases ( job -- outcome )
  dup several-check ['] params-copy aux-then ['] main-motive-binder aux-then
  ['] several-indices aux-then ['] several-minors aux-then
  ['] several-type! aux-then ['] several-value! aux-then nip ;
: cases-any ( job -- outcome ) dup aux-motives @ 1 = if cases else several-cases then ;
: aux-cases-on-any ( d job -- outcome )
  tuck aux-begin ['] cases-any aux-then swap aux-because ;
