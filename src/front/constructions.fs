\ The definitions Lean's front end generates for an inductive type, built
\ from the type's recursor as Lean builds them (plan row FE6, first slice;
\ ADR 0021; owner decision "Front-end syntax" 7: proof terms identical to
\ Lean's): T.casesOn and T.recOn. Each is built from a loaded, sealed
\ stage (import/stage.fs) in a scratch tier over its input tier, so a
\ definition equal to Lean's node for node -- binder names, binder
\ information and universe arguments included -- has the number of
\ Lean's own expression in the same export (core/compact-tier.fs).
\
\ Ported from Lean 4.35.0 (src/Lean/Meta/Constructions):
\ - casesOn: Lean's C++ mk_cases_on (lean_mk_cases_on, CasesOn.lean): the
\   recursor's binders reordered to parameters, motive, indices, major
\   premise, then minor premises without their induction hypotheses; the
\   value applies T.rec to the parameters, the motive, each minor premise
\   as fun fields hyps => minor fields, the indices and the major premise.
\   Its structure case, mkCasesOnViaProjs? (a Prop with one constructor,
\   no index, not recursive, eliminating into every universe, such as
\   And): the value applies the minor premise to the projections of the
\   major premise.
\ - recOn: mkRecOn (RecOn.lean): the recursor's binders reordered to
\   parameters and motives, indices and major premise, minor premises;
\   the value applies T.rec to them in the recursor's order. With
\   mkRecOnViaCasesOn? (the structure case above) the value is T.casesOn.
\ Lean abstracts free variables (forallTelescope, mkForallFVars); here the
\ same reordering renumbers de Bruijn indices (front/expr-remap.fs): the
\ indices and major premise move out past the minor premises (shifted
\ down by their count), each minor premise in past them (shifted up), and
\ the conclusion's variables are swapped.
\
\ Outcomes (ADR 0008): ok with the type and value; unsupported, with a
\ reason (aux-why), for a shape not ported yet: casesOn of a mutual or
\ nested type (several motives: src/front/cases-several.fs builds that
\ case, and aux-cases-on-any either), a minor premise
\ whose fields and hypotheses are interleaved (Lean's recursors never
\ are), an mdata record in a domain, a type whose Sort only reduction
\ shows (casesOn needs it to choose the structure case); invalid for a
\ recursor whose type has fewer binders than its numbers say or a missing
\ recursor; full or exhausted as the tier and the renumbering pass report.
\ Untrusted front-end code: the result is compared with Lean's
\ (tests/front/constructions-init.sh) and would be checked by the kernel
\ like any declaration. Comparing (aux-same?, aux-alike?): node for node,
\ or up to binder names and information, which the kernel ignores and
\ Lean's exporter shares terms by (so an export's names need not be the
\ ones the generator chose); universe parameters must be equal.
\ Limit (review fe6a M1): the binder names and information of what is
\ built here are the ones the export gives T.rec, and an export may show
\ another, shared term's (Equivalence.rec's symm field: explicit binders
\ a b in Init's export, implicit x y in Lean's environment). Comparing
\ with the same export cannot see that; tests/front/constructions-init.sh
\ also compares them with pinned Lean's environment and counts the
\ differences. The front end needs an exact source of binder names and
\ information (the elaboration data, or an export without sharing)
\ before it uses these definitions (plan row FE6).
\
\ Usage (stage s loaded and sealed, d a type declaration of it):
\   create job /aux allot  s job aux-init drop
\   d job aux-cases-on .   \ 0 (ok): job aux-type@ and aux-value@ hold it
\   d job aux-rec-on .
\   job aux-free
\ State: none of its own; every word takes a job record (/aux), which owns
\ a scratch tier, the renumbering pass and a block of binders until
\ aux-free.

require ../lib/lib.fs
require ../lib/bytes.fs
require ../core/compact.fs
require ../import/stage.fs
require ./expr-remap.fs

begin-structure /aux
  /remap +field aux-remap       \ the renumbering pass, in aux-scratch
  /tier +field aux-scratch      \ the scratch tier over the stage's input
  field: aux-stage              \ the loaded, sealed stage
  field: aux-type               \ the inductive type's declaration
  field: aux-rec                \ its recursor's declaration
  field: aux-params             \ the recursor's numbers
  field: aux-motives
  field: aux-minors
  field: aux-indices
  field: aux-block              \ heap: head and domain of each binder made
  field: aux-room               \ binders the block holds
  field: aux-count              \ binders in it
  field: aux-minor              \ the minor premise being read, and its type
  field: aux-mtype
  field: aux-fields             \ its fields
  field: aux-span               \ binders a minor premise's fold wraps
  field: aux-arg                \ the recursor's arguments ( j job -- e outcome )
  field: aux-body               \ the value's body ( job -- e outcome )
  field: aux-ctor               \ the constructor being read (ctorIdx)
  field: aux-x                  \ the name x (ctorIdx's binder)
  field: aux-main               \ several motives: the type's, from 0
  field: aux-kept               \ the minor premises casesOn keeps
  field: aux-table              \ heap: a renumbering table (expr-remap.fs)
  field: aux-table-room         \ cells it holds
  field: aux-ih                 \ a hypothesis's type being rebuilt, its binders
  field: aux-ih-span
  field: aux-names              \ a tuple of universe parameter names
  field: aux-built-params       \ the result's universe parameters
  field: aux-why                \ counted string: why unsupported, or 0
  field: aux-built-type         \ the result
  field: aux-built-value
end-structure

: aux-tier ( job -- tier ) aux-scratch ;
: aux-tuples ( job -- cons ) aux-tier tier-tuples ;
: aux-input ( job -- tier ) aux-stage @ stage-tier ;
: aux-type@ ( job -- e ) aux-built-type @ ;
: aux-value@ ( job -- e ) aux-built-value @ ;
: aux-refuse ( c-addr job -- outcome ) aux-why ! outcome-unsupported ;
: aux-invalid ( c-addr job -- outcome ) aux-why ! outcome-invalid ;
\ The why of an outcome that is not ok, when nothing more specific is
\ known: the renumbering pass's.
: pass-why ( outcome -- c-addr )
  case outcome-exhausted of c" the renumbering pass ran out of fuel" endof
    outcome-unsupported of c" an mdata record, or a dropped binder used" endof
    >r c" no room for the renumbering pass" r> endcase ;
: aux-because ( outcome job -- outcome )
  over ok? if drop exit then dup aux-why @ if drop exit then
  over pass-why swap aux-why ! ;

\ ---- Making and freeing.
: aux-init ( stage job -- outcome )
  dup /aux erase tuck aux-stage ! dup aux-tier over aux-remap remap-init
  dup aux-input swap aux-tier tier-extend ;
: aux-free ( job -- )
  dup aux-tier tier-free dup aux-remap remap-free dup aux-block heap-release
  aux-table heap-release ;

\ ---- The declarations.
: decl-of ( d job -- d stage ) aux-stage @ ;
: type-decl ( job -- d stage ) dup aux-type @ swap decl-of ;
: rec-decl ( job -- d stage ) dup aux-rec @ swap decl-of ;
: type-name ( job -- n ) type-decl staged-name@ ;
: type-type ( job -- e ) type-decl staged-type@ ;
: type-rec? ( job -- flag ) type-decl staged-rec? ;
: rec-item ( i job -- u ) rec-decl staged-item ;
: rec-type ( job -- e ) rec-decl staged-type@ ;
: recursor-name ( job -- n ) rec-decl staged-name@ ;
: rec-params ( job -- t ) rec-decl staged-params@ ;
: params-count ( d job -- n )
  tuck decl-of staged-params@ swap aux-tuples tuple-length ;
\ The declaration named T.s, T the type's name.
: aux-named ( c-addr u job -- d true | false )
  dup >r type-name -rot r@ aux-tier name-find-str
  if r> aux-stage @ stage-find else r> drop false then ;
: aux-numbers ( job -- )
  more-rec-params over rec-item over aux-params !
  more-rec-indices over rec-item over aux-indices !
  more-rec-motives over rec-item over aux-motives !
  more-rec-minors over rec-item swap aux-minors ! ;
: rec-kind? ( d job -- flag ) decl-of staged-kind@ kind-recursor = ;
: find-rec ( job -- d true | false ) >r s" rec" r> aux-named ;
: no-recursor ( job -- outcome ) c" no recursor" swap aux-invalid ;
\ Type d's recursor found and its numbers read: ok, or invalid.
: aux-recursor ( d job -- outcome )
  tuck aux-type ! dup find-rec 0= if no-recursor exit then
  2dup swap rec-kind? 0= if drop no-recursor exit then
  over aux-rec ! aux-numbers outcome-ok ;
\ The rule's fields of a one-constructor type's recursor.
: one-rule-fields ( job -- n )
  dup >r more-rec-rules swap rec-item rule-fields-item swap r> aux-tuples tuple-item ;

\ ---- Expressions.
: pi-parts ( e job -- head dom ) aux-tier 2dup expr-head@ -rot expr-a@ ;
\ The telescope words of core/compact-exprs.fs, on the job's tier.
\ nth-pi requires n <= pi-count (expr-pi-after's precondition; past it
\ the walk stops at the end). Its callers stay within: rec-pi and rec-end
\ in the recursor's type, which rec-whole? finds long enough before any
\ binder is made; m-pi, ctor-idx.fs's type-pi and field-pi and
\ cases-several.fs's ih-pi at binders counted from the same declarations
\ (Forth review of reuse-c, finding 3).
: nth-pi ( e n job -- e' ) aux-tier swap expr-pi-after drop ;
: pi-count ( e job -- n ) aux-tier expr-pis ;
\ Binder j of e (nth-pi's order for a type read from the job).
: pi-at ( j e job -- e' ) >r swap r> nth-pi ;
: app-head ( e job -- f ) aux-tier expr-app-fn ;
: var-index ( e job -- b )
  aux-tier 2dup expr-tag@ tag-bvar = if expr-a@ else 2drop -1 then ;
: pi>lam ( head -- head' ) tag-pi tag-lam - - ;
: aux-var ( b job -- e outcome ) aux-tier expr-bvar ;
\ After ok-keep? fails below x: x dropped, the failure kept.
: failed-past ( x -1 outcome -- -1 outcome ) >r nip r> ;
\ The binder with head and domain around body.
: make-binder ( body job head dom -- e outcome ) 2swap aux-tier expr-make ;
\ f applied to variable b.
: apply-var ( f b job -- e outcome )
  tuck aux-var ok-keep? if swap aux-tier expr-app else failed-past then ;
\ The end of type e's Pi telescope.
: pi-end ( e job -- e' ) aux-tier expr-pi-end ;
: prop-sort? ( e job -- flag )
  aux-tier 2dup expr-tag@ tag-sort = if expr-a@ level-zero = else 2drop false then ;

\ ---- The recursor's binders: params, motives, minors, indices, major.
: rec-total ( job -- n )
  dup aux-params @ over aux-motives @ + over aux-minors @ + swap aux-indices @ + 1+ ;
: first-minor ( job -- j ) dup aux-params @ swap aux-motives @ + ;
: first-index ( job -- j ) dup first-minor swap aux-minors @ + ;
: rec-pi ( j job -- e ) dup rec-type swap pi-at ;
: rec-domain ( j job -- e ) tuck rec-pi swap aux-tier expr-a@ ;
: rec-head ( j job -- head ) tuck rec-pi swap aux-tier expr-head@ ;
: with-domain ( j job -- j dom job ) 2dup rec-domain swap ;
: rec-end ( job -- e ) >r r@ rec-type r@ rec-total r> nth-pi ;
: rec-whole? ( job -- flag ) dup rec-type over pi-count swap rec-total < 0= ;

\ ---- The block of binders made, outermost first, and folds.
: aux-slot ( i job -- addr ) aux-block @ pair-at ;
: binder@ ( i job -- head dom ) aux-slot 2@ ;
: aux-reserve ( n job -- outcome )
  2dup aux-room @ > 0= if 2drop outcome-ok exit then
  over 2* cells over aux-block @ ?dup if swap resize else allocate then
  if 2drop drop outcome-full exit then over aux-block ! aux-room ! outcome-ok ;
: binder, ( head dom job -- ) dup >r aux-count @ r@ aux-slot 2! 1 r> aux-count +! ;
\ Loops over a job (lib/outcome.fs): steps ( job -- outcome ) chained by
\ ok-with, steps ( job i -- job outcome ) by ok-each, folds ( x i job --
\ x' outcome ) by ok-fold.
\ The block's binders wrapped around body, from the inside: Pi or fun.
: aux-last ( i job -- i' ) aux-count @ 1- swap - ;
: block-pi ( body i job -- e outcome ) tuck aux-last over binder@ make-binder ;
: block-lam ( body i job -- e outcome )
  tuck aux-last over binder@ swap pi>lam swap make-binder ;
: aux-fold ( body job xt -- e outcome ) over aux-count @ -rot ok-fold ;
: aux-pis ( body job -- e outcome ) ['] block-pi aux-fold ;
: aux-lams ( body job -- e outcome ) ['] block-lam aux-fold ;

\ ---- Renumbering (front/expr-remap.fs).
: run-remap ( e job -- e' outcome ) aux-remap remap-run ;
: at-cutoff ( c job -- ) aux-remap remap-cutoff! ;
\ Indices and the major premise move out past the minor premises.
: lowering ( c job -- ) tuck at-cutoff dup aux-minors @ 0 rot aux-remap remap-shift! ;
\ Minor premises move in past the indices and the major premise.
: lifting ( c job -- ) tuck at-cutoff 0 over aux-indices @ 1+ rot aux-remap remap-shift! ;
\ The conclusion's variables: indices and major out, minors in.
: swapping ( job -- )
  0 over at-cutoff dup aux-indices @ 1+ over aux-minors @ rot aux-remap remap-swap! ;
\ Binder j of the recursor, with domain dom renumbered as set, appended.
: moved ( j dom job -- outcome )
  tuck run-remap ok-keep? 0= if nip nip exit then
  swap >r swap r@ rec-head swap r> binder, outcome-ok ;
: rec-binder ( j job -- head dom ) tuck rec-pi swap pi-parts ;
: copy-binder ( job j -- job outcome ) over tuck rec-binder rot binder, outcome-ok ;
: index-binder ( job j -- job outcome )
  over 2dup lowering tuck first-index + swap with-domain moved ;
: minor-binder ( job i -- job outcome )
  over 2dup lifting tuck first-minor + swap with-domain moved ;
: front-binders ( job -- outcome ) ['] first-minor ['] copy-binder ok-each-of ;
: index-binders ( job -- outcome ) dup aux-indices @ 1+ ['] index-binder ok-each nip ;
: minor-binders ( job -- outcome ) dup aux-minors @ ['] minor-binder ok-each nip ;
\ The type: the block around the conclusion.
: conclusion ( job -- e outcome ) dup swapping dup rec-end swap run-remap ;
\ The type: the block's Pis around the conclusion given.
: type-around ( job e outcome -- outcome )
  ok-keep? 0= if nip exit then
  over aux-pis ok-keep? if swap aux-built-type ! outcome-ok else nip then ;
: built-type! ( job -- outcome ) dup conclusion type-around ;

\ ---- The value: T.rec.{params} applied, the block's funs around it.
\ Universe argument lists: the parameters a tuple of names (aux-names)
\ holds, as levels, after any levels already added.
: name-param ( i job -- name ) dup aux-names @ swap aux-tuples tuple-item ;
: param-level ( i job -- l outcome ) tuck name-param swap aux-tier level-param ;
: level-add ( job i -- job outcome )
  over tuck param-level ok-keep? if swap aux-tuples tuple-add else nip then ;
: names-count ( job -- n ) dup aux-names @ swap aux-tuples tuple-length ;
: levels-add ( t job -- outcome )
  tuck aux-names ! dup names-count ['] level-add ok-each nip ;
: level-one, ( job -- outcome )
  level-zero over aux-tier level-succ
  ok-keep? if swap aux-tuples tuple-add else nip then ;
: tuple-begin ( job -- outcome ) aux-tuples tuple-start ;
: tuple-done ( job outcome -- t outcome )
  ok-then? if aux-tuples tuple-end else no-result then ;
: type-names ( job -- t ) type-decl staged-params@ ;
: rec-levels-add ( job -- outcome ) dup rec-params swap levels-add ;
: type-levels-add ( job -- outcome ) dup type-names swap levels-add ;
\ A tuple made by xt ( job -- outcome ), which adds its items.
: tuple-of ( job xt -- t outcome ) over tuple-begin swap ok-with tuple-done ;
: rec-levels ( job -- t outcome ) ['] rec-levels-add tuple-of ;
: type-levels ( job -- t outcome ) ['] type-levels-add tuple-of ;
: rec-const ( job -- e outcome )
  dup rec-levels ok-keep? if swap dup >r recursor-name swap r> aux-tier expr-const then ;
\ Argument j of the recursor: its variable, renumbered as the conclusion's.
: rec-arg ( j job -- e outcome )
  tuck rec-total 1- swap - over aux-var ok-keep? if swap dup swapping run-remap then ;
: apply-arg ( f j job -- e outcome )
  tuck dup aux-arg @ execute ok-keep? if swap aux-tier expr-app else failed-past then ;
\ The recursor applied to its arguments (casesOn's fold minor premises of
\ their own inside this fold).
: rec-apply ( f job -- e outcome ) dup rec-total swap ['] apply-arg ok-fold ;
: generic-body ( job -- e outcome ) dup rec-const ok-keep? if swap rec-apply then ;
: built-value! ( job -- outcome )
  dup dup aux-body @ execute ok-keep? 0= if nip exit then
  over aux-lams ok-keep? if swap aux-built-value ! outcome-ok else nip then ;

\ ---- Minor premise i: fields, then induction hypotheses, whose type
\ ends in a motive (Lean's is_type_former_arg).
: minor-type ( i job -- e ) tuck first-minor + swap rec-domain ;
: m-pi ( q job -- e ) dup aux-mtype @ swap pi-at ;
\ The variable type e's conclusion applies, seen from outside e.
: target ( e job -- b ) 2dup pi-count >r tuck pi-end over app-head swap var-index r> - ;
\ Whether index b, seen from the minor premise, names a motive.
: motive-place? ( b job -- flag ) tuck aux-minor @ - swap aux-motives @ u< ;
: ih? ( dom q job -- flag ) rot over target rot - swap motive-place? ;
: m-domain ( q job -- dom ) tuck m-pi swap aux-tier expr-a@ ;
: m-ih? ( q job -- flag ) 2dup m-domain -rot ih? ;
: m-fields ( n job -- f )
  over 0 ?do i over m-ih? if 2drop i unloop exit then loop drop ;
: m-ihs? ( f n job -- flag )
  -rot swap ?do i over m-ih? 0= if drop false unloop exit then loop drop true ;
: m-start ( i job -- job ) 2dup aux-minor ! tuck minor-type over aux-mtype ! ;
: m-count ( job -- n ) dup aux-mtype @ swap pi-count ;
: m-split ( n job -- n flag ) >r dup r@ aux-fields @ swap r> m-ihs? ;
\ Minor i opened: its binders, and whether all after its fields are hypotheses.
: m-open ( i job -- n flag )
  m-start dup m-count tuck over m-fields over aux-fields ! m-split ;
: interleaved ( job -- outcome )
  c" a minor premise with fields after hypotheses" swap aux-refuse ;
\ Its binders wrapped around body, from the inside (aux-span of them).
: m-last ( i job -- q ) aux-span @ 1- swap - ;
: m-binder ( i job -- head dom ) tuck m-last over m-pi swap pi-parts ;
: m-pi-step ( body i job -- e outcome ) tuck m-binder make-binder ;
: m-lam-step ( body i job -- e outcome ) tuck m-binder swap pi>lam swap make-binder ;
: m-fold ( body job xt -- e outcome ) >r dup aux-span @ swap r> ok-fold ;
\ casesOn's minor premise: the fields only, the conclusion moved past the
\ hypotheses it never names (in the recursor's context).
: m-dropping ( n job -- )
  0 over at-cutoff tuck aux-fields @ - 0 rot aux-remap remap-shift! ;
: m-conclusion ( n job -- e outcome ) 2dup m-dropping tuck m-pi swap run-remap ;
: span-fields ( job -- ) dup aux-fields @ swap aux-span ! ;
: stripped ( i job -- e outcome )
  tuck m-open 0= if drop interleaved no-result exit then
  2dup swap aux-fields @ = if drop aux-mtype @ outcome-ok exit then
  over span-fields over m-conclusion ok-keep? if swap ['] m-pi-step m-fold then ;
: case-binder ( job i -- job outcome )
  over 2dup stripped ok-keep? 0= if nip nip exit then
  >r 2dup lifting tuck first-minor + swap r> swap moved ;
: case-minors ( job -- outcome ) dup aux-minors @ ['] case-binder ok-each nip ;
\ casesOn's argument for minor i: fun fields hyps => minor' fields, its
\ binders moved from the recursor's context into the value's.
: m-moving ( i job -- )
  0 over at-cutoff dup aux-indices @ 1+ over aux-minors @ + swap aux-remap remap-shift! ;
: m-move ( job -- outcome )
  dup aux-mtype @ over run-remap ok-keep? if swap aux-mtype ! outcome-ok else nip then ;
: m-ready ( i job -- outcome )
  2dup m-open 0= if drop nip interleaved exit then over aux-span ! tuck m-moving m-move ;
: m-head-var ( job -- b ) dup aux-span @ over aux-minors @ 1- + swap aux-minor @ - ;
: field-arg ( f q job -- e outcome ) tuck m-last swap apply-var ;
\ Variable b applied to the fields.
: m-body-at ( b job -- e outcome )
  tuck aux-var ok-keep? 0= if exit then
  swap dup aux-fields @ swap ['] field-arg ok-fold ;
: m-body ( job -- e outcome ) dup m-head-var swap m-body-at ;
: minor-lambda ( i job -- e outcome )
  tuck m-ready ok-then? 0= if no-result exit then
  dup m-body ok-keep? if swap ['] m-lam-step m-fold then ;
: minor-at? ( j job -- flag ) dup first-minor swap first-index within ;
: case-arg ( j job -- e outcome )
  2dup minor-at? if tuck first-minor - swap minor-lambda else rec-arg then ;

\ ---- The structure case (Lean's isCasesOnViaProjs): one constructor,
\ no index, not recursive, a Prop former, eliminating into every universe.
: one-case? ( job -- flag )
  dup aux-minors @ 1 = over aux-motives @ 1 = and swap aux-indices @ 0= and ;
: large? ( job -- flag )
  dup aux-rec @ over params-count swap dup aux-type @ swap params-count 1+ = ;
: type-end ( job -- e ) dup type-type swap pi-end ;
: prop-former? ( job -- flag ) dup type-end swap prop-sort? ;
: via-projs? ( job -- flag )
  dup one-case? over type-rec? 0= and over large? and swap prop-former? and ;
\ The minor premise applied to the major premise's projections.
: field-proj ( q job -- e outcome )
  dup >r type-name proj-head 1 r@ aux-var ok-keep?
  if rot r> aux-tier expr-make else r> drop failed-past then ;
: apply-proj ( f q job -- e outcome )
  tuck field-proj ok-keep? if swap aux-tier expr-app else failed-past then ;
: projs-body ( job -- e outcome )
  0 over aux-var ok-keep? 0= if exit then
  swap dup one-rule-fields swap ['] apply-proj ok-fold ;
: cases-name ( job -- n true | false )
  >r r@ type-name s" casesOn" r> aux-tier name-find-str ;
: no-cases ( job -- -1 outcome ) c" no casesOn to unfold to" swap aux-refuse no-result ;
: cases-const ( job -- e outcome )
  dup cases-name 0= if no-cases exit then
  over rec-levels ok-keep? if rot aux-tier expr-const else failed-past then ;

\ ---- Starting a build, and the two constructions.
: aux-clear ( job -- )
  0 over aux-why ! 0 over aux-count ! -1 over aux-built-type ! -1 over aux-built-value !
  false over aux-remap remap-erase! aux-tier tier-reset drop ;
: short-type ( job -- outcome )
  c" a recursor type shorter than its numbers" swap aux-invalid ;
: aux-shape ( job -- outcome )
  dup rec-params over aux-built-params ! dup rec-whole? 0= if short-type exit then
  dup rec-total swap aux-reserve ;
: aux-begin ( d job -- outcome )
  dup aux-clear tuck aux-recursor ok-then? if aux-shape then ;
\ The structure case is chosen on the Sort that ends T's type, which
\ Lean's isPropFormerType finds by reduction: a type that needs it is
\ unsupported for both constructions.
: no-sort ( job -- outcome ) c" a type whose Sort only reduction shows" swap aux-refuse ;
: sort-ready ( job -- outcome )
  dup type-end over aux-tier expr-tag@ tag-sort <> if no-sort exit then drop outcome-ok ;
\ recOn (mkRecOn; mkRecOnViaCasesOn? for the structure case).
: recon-binders ( job -- outcome )
  dup front-binders ['] index-binders ok-with ['] minor-binders ok-with nip ;
: recon-body ( job -- e outcome ) ['] rec-arg over aux-arg ! generic-body ;
: recon-value ( job -- outcome )
  dup via-projs? 0= if ['] recon-body over aux-body ! built-value! exit then
  dup cases-const ok-keep? if swap aux-built-value ! outcome-ok else nip then ;
: recon ( job -- outcome )
  dup sort-ready ['] recon-binders ok-with ['] built-type! ok-with
  ['] recon-value ok-with nip ;
\ A construction of Lean's declaration d by xt ( job -- outcome ), its
\ refusal explained (aux-because).
: aux-run ( d job xt -- outcome ) >r tuck aux-begin r> ok-with swap aux-because ;
: aux-rec-on ( d job -- outcome ) ['] recon aux-run ;
\ casesOn (mk_cases_on; mkCasesOnViaProjs? for the structure case).
: several-motives ( job -- outcome )
  c" several motives (a mutual or nested type)" swap aux-refuse ;
: cases-ready ( job -- outcome )
  dup aux-motives @ 1 <> if several-motives exit then sort-ready ;
: cases-binders ( job -- outcome )
  dup front-binders ['] index-binders ok-with ['] case-minors ok-with nip ;
: cases-body ( job -- e outcome )
  dup via-projs? if projs-body exit then ['] case-arg over aux-arg ! generic-body ;
: cases-value ( job -- outcome ) ['] cases-body over aux-body ! built-value! ;
: cases ( job -- outcome )
  dup cases-ready ['] cases-binders ok-with ['] built-type! ok-with
  ['] cases-value ok-with nip ;
: aux-cases-on ( d job -- outcome ) ['] cases aux-run ;

\ ---- Comparing with Lean's declaration d of the same name: type, value
\ and universe parameters, each one number (hash-consing).
: lean-type ( d job -- e ) decl-of staged-type@ ;
: lean-value ( d job -- e ) decl-of staged-value@ ;
: lean-params ( d job -- t ) decl-of staged-params@ ;
: params-same? ( d job -- flag ) tuck lean-params swap aux-built-params @ = ;
: type-same? ( d job -- flag ) tuck lean-type swap aux-type@ = ;
: value-same? ( d job -- flag ) tuck lean-value swap aux-value@ = ;
: aux-same? ( d job -- flag )
  2dup type-same? 0= if 2drop false exit then
  2dup value-same? 0= if 2drop false exit then params-same? ;
\ The same up to binder names (which the kernel ignores, and Lean's
\ exporter shares between terms equal but for them, so that the names in
\ an export need not be the ones the generator chose): both sides with
\ every binder name made anonymous, then compared by number. A side the
\ pass cannot rename (fuel, room) makes them not alike.
: erasing ( job -- ) aux-remap remap-erasing ;
: erased? ( e job -- e' true | false ) dup erasing run-remap ok? dup 0= if nip then ;
: alike? ( e1 e2 job -- flag )
  tuck erased? 0= if 2drop false exit then -rot erased? 0= if drop false exit then = ;
: type-alike? ( d job -- flag ) tuck lean-type over aux-type@ rot alike? ;
: value-alike? ( d job -- flag ) tuck lean-value over aux-value@ rot alike? ;
: aux-alike? ( d job -- flag )
  2dup type-alike? 0= if 2drop false exit then
  2dup value-alike? 0= if 2drop false exit then params-same? ;
