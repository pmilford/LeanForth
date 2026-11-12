\ Term printer (plan task 2.4.3): prints a term of the term store as Lean
\ 4.35.0 prints it with pp.unicode.fun, or in plain ASCII or LaTeX, to the
\ caller's character sink. Binder names come from the presentation side
\ table and are restored from de Bruijn indices without capture; binders
\ group as {A B : Prop}; Pi prints as ∀ (propositions), as → (no dependency)
\ or as (x : A) → B; fun binders merge into one fun; implicit arguments of
\ known heads are hidden; parentheses only where Lean's grammar needs them.
\ Untrusted presentation code: the checker never loads it and no output is
\ evidence of anything. Requires print-analysis.fs and the modules it
\ loads. State: the printer record of print-job.fs.
\ Depth (plan task 6.2.0): every node is a visit of the print's frames
\ (print-job.fs), a chain of steps that keeps what it needs across a
\ child's visit on the frames' explicit stack, so a print holds a constant
\ number of host-stack cells whatever the depth of its term, and its
\ binders in scope and their names grow on the heap too.
\
\ Public words (outcomes from lib/outcome.fs):
\   lf-print-setup ( sink options -- )   sink xt ( c-addr u -- ); a mode
\     (lf-print-unicode, lf-print-ascii or lf-print-latex) plus option bits
\     (lf-print-universes shows universe arguments, c.{u}).
\   lf-print-term ( term fuel -- outcome )       a closed term
\   lf-print-statement ( term fuel -- outcome )  a theorem's statement: its
\     Pi spine is printed as a proposition (∀) whatever the quick test says
\   lf-print-level ( level fuel -- outcome )     a universe level
\   lf-print-name ( id -- outcome )              a structured name; the
\     anonymous name 0 prints as [anonymous]
\   lf-print-inline, lf-print-display ( term fuel -- outcome )  the term in
\     LaTeX as Markdown math, $...$ or $$...$$
\   lf-print-limit! ( n -- flag )   at most n nested visits per print (no
\     limit unless set)
\   lf-print-reset ( -- )   recover after a THROW out of a print
\ ok: printed. invalid: malformed input (bad index, stale reference,
\ unknown tag, a variable outside the term's binders, a corrupted name
\ store), a busy printer, negative fuel, or a print during which the sink
\ called lf-print-reset. exhausted: out of fuel (one unit per visited
\ node). full: no room on the heap for the print's stack, its binders in
\ scope or their names, or out of nested visits once the caller set a
\ limit (lf-print-limit!). After a failure the sink has received a partial
\ text. The sink rules are in print-job.fs.

require ./print-analysis.fs
require ./print-strings.fs

1024 constant lf-prec-max      \ atoms; the head of an application
1023 constant lf-prec-arg      \ an argument
1022 constant lf-prec-lead     \ an application, ∀, Type u
26 constant lf-prec-domain     \ left of →
25 constant lf-prec-arrow      \ right of →, and A → B itself

\ A position: the least precedence allowed there, whether text follows at
\ the same level (then an open-ended form such as fun or ∀ needs
\ parentheses), and whether a Pi there is known to be a proposition. It
\ is one cell: the precedence in units of lf-pos-unit, and two bits.
1 constant lf-pos-followed
2 constant lf-pos-prop
4 constant lf-pos-unit
: lf-pos ( prec followed -- pos ) lf-pos-followed and swap lf-pos-unit * or ;
: lf-prop-pos ( prec -- pos ) false lf-pos lf-pos-prop or ;
: lf-pos-prec ( pos -- prec ) lf-pos-unit / ;
: lf-pos-followed? ( pos -- flag ) lf-pos-followed and 0<> ;
: lf-pos-prop? ( pos -- flag ) lf-pos-prop and 0<> ;
: lf-pp-parens? ( pos prec open -- flag )
  >r over lf-pos-prec < swap lf-pos-followed? r> and or ;
: lf-pp-open-if ( flag -- flag ) dup if s" (" lf-pp-emit then ;
: lf-pp-enclose ( pos flag -- pos' flag ) dup if s" (" lf-pp-emit nip 0 swap then ;
\ Leave the binders bound since the scope had depth0 binders; the step
\ that does so at the end of a part, for the depth saved under it.
: lf-pp-leave ( outcome depth0 -- outcome ) lf-pp-depth swap - lf-pp-unbind ;
: lf-pp-leaving ( outcome frames -- outcome frames 0 )
  >r r@ frame-restore lf-pp-leave r> 0 ;

defer lf-pp-term-step ( term pos frames -- ... frames next )
: lf-pp-term-call ( term pos frames cont -- ... frames next )
  ['] lf-pp-term-step lf-pp-call ;

\ Sorts: Prop and Type are atoms; Type u and Sort u are not (their
\ parenthesis flag waits while the level prints).
: lf-pp-concrete ( term pos -- outcome )
  swap lf-term-first@ dup 2 < if nip lf-pp-sort-number outcome-ok exit then
  swap lf-prec-lead false lf-pp-parens? lf-pp-open-if >r lf-pp-sort-number outcome-ok r>
  lf-pp-wrap ;
: lf-pp-concrete-step ( term pos frames -- outcome frames 0 ) >r lf-pp-concrete r> 0 ;
: lf-pp-symbolic ( term pos frames -- ... frames next )
  >r swap lf-term-first@ dup lf-pp-level-atom? if nip lf-pp-sort-atom r> 0 exit then
  swap lf-prec-lead false lf-pp-parens? lf-pp-open-if r@ frame-save
  r> ['] lf-pp-wrapped lf-pp-sort-body ;

\ Atoms: a variable by its display name; a constant by name, with its
\ universe arguments when lf-print-universes is set; @ when asked.
: lf-pp-var ( i -- outcome )
  dup 0 lf-pp-depth within 0= if drop-invalid exit then
  lf-pp-entry lf-pp-text lf-pp-ident outcome-ok ;
\ Universe arguments from index i on, a comma before all but the first
\ and the closing brace after the last: the reference's levels (addr),
\ their number and the next index wait while one prints.
defer lf-pp-uargs ( addr n i frames -- ... frames next )
: lf-pp-uargs-back ( outcome frames -- ... frames next )
  3 lf-pp-failed? if 0 exit then dup >r lf-pp-restore3 r> lf-pp-uargs ;
: lf-pp-uargs-next ( addr n i frames -- ... frames next )
  >r 2dup > 0= if 2drop drop lf-pp-universes-close outcome-ok r> 0 exit then
  dup if lf-pp-list-comma then
  r@ lf-pp-keep-next nip lf-pp-level-at false r> ['] lf-pp-uargs-back lf-pp-level-part ;
' lf-pp-uargs-next is lf-pp-uargs
: lf-pp-universe-args ( term frames cont -- ... frames next )
  2>r lf-pp-const-levels 0= if outcome-invalid 2r> exit then
  dup 0= if 2drop outcome-ok 2r> exit then
  lf-pp-universes-open 2r> over frame-save 0 swap lf-pp-uargs ;
: lf-pp-const ( term frames cont -- ... frames next )
  2>r dup lf-pp-const-name 0= if drop-invalid 2r> exit then lf-pp-constant
  lf-pp-universes? if 2r> lf-pp-universe-args else drop outcome-ok 2r> then ;
: lf-pp-atom ( head at? frames cont -- ... frames next )
  2>r if lf-pp-explicit then
  dup lf-tag-bvar lf-pp-is? if lf-term-first@ lf-pp-var 2r> else 2r> lf-pp-const then ;

\ Applications: the head, then the shown arguments, each in argument
\ position; an argument is followed unless it is the last shown one and
\ nothing follows the application. info packs both: the index of the
\ last shown argument times two, plus one when text follows.
: lf-pp-info ( last followed -- info ) 1 and swap 2* or ;
: lf-pp-info-last ( info -- i ) 2/ ;
: lf-pp-info-followed? ( info -- flag ) 1 and 0<> ;
: lf-pp-fn ( app frames cont -- ... frames next )
  2>r lf-pp-head 2dup lf-pp-at? >r drop dup lf-pp-atom-head?
  if r> 2r> lf-pp-atom exit then r> drop lf-prec-max true lf-pos 2r> lf-pp-term-call ;
: lf-pp-args-info ( app pos -- info ) lf-pos-followed? swap lf-pp-last swap lf-pp-info ;
: lf-pp-arg-pos ( info i -- pos )
  over lf-pp-info-last < swap lf-pp-info-followed? or lf-prec-arg swap lf-pos ;
\ The shown arguments from index i on, each after a space: app, info and
\ the next index wait while one prints.
: lf-pp-arg-term ( app info i -- arg pos ) tuck lf-pp-arg-pos >r lf-pp-arg-at r> ;
defer lf-pp-args ( app info i frames -- ... frames next )
: lf-pp-args-back ( outcome frames -- ... frames next )
  3 lf-pp-failed? if 0 exit then dup >r lf-pp-restore3 r> lf-pp-args ;
: lf-pp-arg ( app info i frames -- ... frames next )
  >r r@ lf-pp-keep-next lf-pp-arg-term lf-pp-space
  r> ['] lf-pp-args-back lf-pp-term-call ;
: lf-pp-more? ( app info i -- app info i flag ) 2 pick lf-pp-head nip over > ;
: lf-pp-shown? ( app info i -- app info i flag ) 2 pick over lf-pp-visible? ;
: lf-pp-args-from ( app info i frames -- ... frames next )
  >r begin lf-pp-more? while lf-pp-shown? if r> lf-pp-arg exit then 1+ repeat
  drop 2drop outcome-ok r> 0 ;
' lf-pp-args-from is lf-pp-args
\ The head and the arguments, a part of the visit: app, info and the
\ first index wait while the head prints.
: lf-pp-applied ( app pos frames cont -- ... frames next )
  over frame-save >r over swap lf-pp-args-info 2dup 0 r@ lf-pp-save3 drop
  r> ['] lf-pp-args-back lf-pp-fn ;
\ No argument shown: the head alone, in the application's own position.
: lf-pp-bare ( app pos frames -- ... frames next )
  >r swap lf-pp-head 2dup lf-pp-at? >r drop dup lf-pp-atom-head?
  if nip r> r> ['] frame-return lf-pp-atom exit then
  r> drop swap r> ['] frame-return lf-pp-term-call ;
\ Notation (print-notation.fs installs the two words): the row of the
\ notation table that prints this application, or 0; and the step that
\ prints it by the row. Off, or with no row, the application prints as
\ the kernel's term does.
defer lf-pp-notation ( term -- row | 0 )
: lf-pp-no-notation ( term -- 0 ) drop 0 ;
' lf-pp-no-notation is lf-pp-notation
defer lf-pp-notated ( term row pos frames -- ... frames next )
: lf-pp-app ( term pos frames -- ... frames next )
  >r over lf-pp-spine >r 2drop r> ok-then2? 0= if r> 0 exit then
  over lf-pp-notation ?dup if swap r> lf-pp-notated exit then
  over lf-pp-shown# 0= if r> lf-pp-bare exit then
  dup lf-prec-lead false lf-pp-parens? lf-pp-enclose r@ frame-save
  r> ['] lf-pp-wrapped lf-pp-applied ;

\ Binders. A binder's display name is chosen (print-names.fs), shown and
\ brought into scope; its domain is printed before it is in scope. from is
\ the bottom index of the binders a new name must not repeat: a fun's
\ earlier binders, none for Pi.
: lf-pp-name-binder ( node from -- mark outcome ) over lf-term-second@ swap lf-pp-choose ;
: lf-pp-show-bind ( node from -- outcome )
  over swap lf-pp-name-binder ok-then2? 0= if exit then
  dup lf-pp-pending lf-pp-ident swap lf-term-first@ swap lf-pp-bind ;
: lf-pp-bind-plain ( node -- outcome )
  dup lf-pp-depth lf-pp-name-binder ok-then2?
  if swap lf-term-first@ swap lf-pp-bind then ;
\ The last binder of a bracketed group, a part of the visit: its name
\ unless nameless, the domain, the closing bracket; node and the name's
\ mark wait while the domain prints.
: lf-pp-typed-back ( outcome frames -- ... frames next )
  2 lf-pp-failed? if 0 exit then
  >r r@ lf-pp-restore2 over lf-pp-kind lf-pp-close swap lf-term-first@ swap lf-pp-bind
  r> 0 ;
: lf-pp-typed-binder ( node nameless from frames cont -- ... frames next )
  over frame-save >r >r over r> lf-pp-name-binder dup ok? 0= if nip nip nip r> 0 exit then
  drop swap 0= if dup lf-pp-pending lf-pp-ident lf-pp-colon then
  over lf-term-first@ -rot r@ lf-pp-save2 0 r> ['] lf-pp-typed-back lf-pp-term-call ;

\ Pi. Its flags say whether the Pi is a proposition (lf-flag-prop) and
\ whether its first binder prints as a binder (lf-flag-dep: it is used in
\ the body, or, by Lean's RFC 1834, an explicit binder of a proposition
\ whose domain is not one) rather than as A → B.
1 constant lf-flag-dep
2 constant lf-flag-prop
: lf-pp-flags ( prop dep -- flags ) lf-flag-dep and swap lf-flag-prop and or ;
: lf-flags-dep? ( flags -- flag ) lf-flag-dep and 0<> ;
: lf-flags-prop? ( flags -- flag ) lf-flag-prop and 0<> ;
: lf-pp-flags@ ( flags -- prop dep ) dup lf-flags-prop? swap lf-flags-dep? ;
: lf-pp-rfc? ( pi -- flag outcome )
  dup lf-pp-kind lf-binder-default <> if drop false outcome-ok exit then
  lf-term-first@ lf-pp-prop? >r 0= r> ;
: lf-pp-dep? ( pi prop -- flag outcome )
  over lf-term-second@ 0 lf-pp-loose? dup ok? 0= if >r drop 2drop false r> exit then
  drop if 2drop true outcome-ok exit then
  if lf-pp-rfc? else drop false outcome-ok then ;
: lf-pp-pi-prop? ( pi pos -- flag outcome )
  lf-pos-prop? if drop true outcome-ok else lf-pp-prop? then ;
: lf-pp-pi-flags ( pi pos -- flags outcome )
  over swap lf-pp-pi-prop? dup ok? 0= if >r 2drop 0 r> exit then drop
  tuck lf-pp-dep? >r lf-pp-flags r> ;
: lf-pp-arrow? ( pi dep -- flag ) 0= swap lf-pp-kind lf-binder-default = and ;
\ Grouping (Lean's shouldGroupWithNext and its dependency check): the next
\ binder is a binder of the same, non-instance kind, its domain is the
\ same term, and it prints the same way.
: lf-pp-like? ( node -- flag )
  dup lf-term-second@ 2dup swap lf-term-tag@ lf-pp-is? 0= if 2drop false exit then
  lf-pp-kind swap lf-pp-kind tuck = swap lf-binder-instance <> and ;
: lf-pp-same-next? ( node -- flag outcome )
  dup lf-term-first@ swap lf-term-second@ lf-term-first@ lf-pp-same-domain? ;
: lf-pp-groupable? ( node -- flag outcome )
  dup lf-pp-like? if lf-pp-same-next? else drop false outcome-ok then ;
\ Does pi (the next binder) print with the given dependency?
: lf-pp-same-dep? ( pi prop dep -- flag outcome ) >r lf-pp-dep? swap r> = swap ;
: lf-pp-joins? ( pi prop dep -- flag outcome )
  2>r dup lf-pp-groupable? dup ok? 0= if rot drop 2r> 2drop exit then drop
  if lf-term-second@ 2r> lf-pp-same-dep? else drop 2r> 2drop false outcome-ok then ;
\ An instance binder that is not used and has a hygienic name prints as [A].
: lf-pp-hygienic-binder? ( node -- flag )
  lf-pres-binder@ if lf-pp-hygienic else false then ;
: lf-pp-nameless? ( pi dep -- flag )
  0= swap dup lf-pp-kind lf-binder-instance = swap lf-pp-hygienic-binder? and and ;
\ A group visit: binders that join show their names, the next one in the
\ next group visit; the last one ends the group.
defer lf-pp-group-step ( pi flags frames -- ... frames next )
: lf-pp-group-call ( pi flags frames cont -- ... frames next )
  ['] lf-pp-group-step lf-pp-call ;
: lf-pp-group-more ( pi flags frames -- ... frames next )
  >r swap dup lf-pp-depth lf-pp-show-bind ok-then2? 0= if r> 0 exit then
  lf-pp-space lf-term-second@ swap r> ['] frame-return lf-pp-group-call ;
: lf-pp-group-end ( pi flags frames -- ... frames next )
  >r lf-flags-dep? over swap lf-pp-nameless? lf-pp-depth r> ['] frame-return
  lf-pp-typed-binder ;
: lf-pp-group ( pi flags frames -- ... frames next )
  >r 2dup lf-pp-flags@ lf-pp-joins? dup ok? 0= if nip nip nip r> 0 exit then drop
  r> swap if lf-pp-group-more else lf-pp-group-end then ;
' lf-pp-group is lf-pp-group-step
\ A bracketed group from pi, a part of the visit that continues with cont
\ ( body outcome frames -- ... ), body the term after the group: pi and the
\ scope's depth before it wait meanwhile.
: lf-pp-after ( pi depth0 -- body ) lf-pp-depth swap - lf-pp-bodies ;
: lf-pp-group-back ( outcome frames -- body outcome frames cont )
  >r r@ lf-pp-restore2 lf-pp-after swap r> dup frame-restore ;
: lf-pp-group-then ( pi flags frames cont -- ... frames next )
  over frame-save >r over lf-pp-depth r@ lf-pp-save2
  over lf-pp-kind lf-pp-open r> ['] lf-pp-group-back lf-pp-group-call ;
\ The body of a Pi spine keeps the proposition flag.
: lf-pp-body-pos ( flags prec -- pos )
  swap lf-flags-prop? if lf-prop-pos else false lf-pos then ;

\ A → B: pi and flags wait while A prints, the parenthesis flag below.
: lf-pp-arrow-done ( outcome frames -- outcome frames 0 ) 1 lf-pp-unbind 0 ;
: lf-pp-arrow-domain ( outcome frames -- ... frames next )
  2 lf-pp-failed? if 0 exit then
  >r r@ lf-pp-restore2 lf-pp-arrow over lf-pp-bind-plain ok-then2? 0= if r> 0 exit then
  swap lf-term-second@ swap lf-prec-arrow lf-pp-body-pos
  r> ['] lf-pp-arrow-done lf-pp-term-call ;
: lf-pp-arrow-body ( pi flags frames cont -- ... frames next )
  over frame-save >r 2dup r@ lf-pp-save2 drop
  lf-term-first@ lf-prec-domain true lf-pos r> ['] lf-pp-arrow-domain lf-pp-term-call ;
: lf-pp-arrow-form ( pi pos flags frames -- ... frames next )
  >r swap lf-prec-arrow true lf-pp-parens? lf-pp-open-if r@ frame-save
  r> ['] lf-pp-wrapped lf-pp-arrow-body ;
\ (x : A) → B and {x : A} → B, for a Pi that is not a proposition: the
\ scope's depth before the group and the flags wait meanwhile.
: lf-pp-dep-group ( body outcome frames -- ... frames next )
  >r r@ frame-restore -rot ok-then? 0= if nip r> lf-pp-leaving exit then
  lf-pp-arrow swap lf-prec-arrow lf-pp-body-pos r> ['] lf-pp-leaving lf-pp-term-call ;
: lf-pp-dep-body ( pi flags frames cont -- ... frames next )
  over frame-save >r lf-pp-depth r@ frame-save dup r@ frame-save
  r> ['] lf-pp-dep-group lf-pp-group-then ;
: lf-pp-dep-form ( pi pos flags frames -- ... frames next )
  >r swap lf-prec-arrow true lf-pp-parens? lf-pp-open-if r@ frame-save
  r> ['] lf-pp-wrapped lf-pp-dep-body ;
\ ∀ g1 g2 ..., B: further binder groups of the proposition join the ∀, a
\ visit each; the depth before the ∀ waits under them, with the step that
\ leaves its binders.
defer lf-pp-forall-step ( term x frames -- ... frames next )
: lf-pp-forall-call ( term x frames cont -- ... frames next )
  ['] lf-pp-forall-step lf-pp-call ;
: lf-pp-forall-next? ( term -- flags flag outcome )
  dup lf-tag-pi lf-pp-is? 0= if drop 0 false outcome-ok exit then
  dup true lf-pp-dep? dup ok? 0= if >r 2drop 0 false r> exit then drop
  tuck lf-pp-arrow? 0= swap true swap lf-pp-flags swap outcome-ok ;
: lf-pp-forall-on ( body outcome frames -- ... frames next )
  >r ok-then? if 0 r> ['] frame-return lf-pp-forall-call else r> 0 then ;
: lf-pp-forall-end ( term frames -- ... frames next )
  >r lf-pp-comma 0 lf-prop-pos r> ['] frame-return lf-pp-term-call ;
: lf-pp-forall-more ( term flags frames -- ... frames next )
  lf-pp-space ['] lf-pp-forall-on lf-pp-group-then ;
: lf-pp-forall-rest ( term x frames -- ... frames next )
  >r drop dup lf-pp-forall-next? dup ok? 0= if nip nip nip r> 0 exit then drop
  r> swap if lf-pp-forall-more else nip lf-pp-forall-end then ;
' lf-pp-forall-rest is lf-pp-forall-step
: lf-pp-forall-body ( pi flags frames cont -- ... frames next )
  over frame-save >r lf-pp-depth r@ frame-save ['] lf-pp-leaving r@ frame-save
  lf-pp-forall r> ['] lf-pp-forall-on lf-pp-group-then ;
: lf-pp-forall-form ( pi pos flags frames -- ... frames next )
  >r swap lf-prec-lead true lf-pp-parens? lf-pp-open-if r@ frame-save
  r> ['] lf-pp-wrapped lf-pp-forall-body ;
\ The form a Pi prints in, from its flags.
: lf-pp-pi-form ( pi flags -- xt )
  2dup lf-pp-flags@ nip lf-pp-arrow? if 2drop ['] lf-pp-arrow-form exit then
  nip lf-flags-prop? if ['] lf-pp-forall-form else ['] lf-pp-dep-form then ;
: lf-pp-pi ( pi pos frames -- ... frames next )
  >r 2dup lf-pp-pi-flags ok-then? 0= if nip nip r> 0 exit then
  2 pick over lf-pp-pi-form r> swap execute ;

\ fun b1 b2 ... ↦ body: one fun for a chain of lambdas. Explicit binders
\ show their names only, implicit ones group as {A B}, an instance binder
\ shows [A] or, when used, [a : A]. Names in one fun never repeat.
: lf-pp-chain-from ( -- from ) lf-pjob lf-pjob-chain @ ;
\ A bracket group's names, a visit each.
defer lf-pp-names-step ( lam x frames -- ... frames next )
: lf-pp-names-call ( lam x frames cont -- ... frames next )
  ['] lf-pp-names-step lf-pp-call ;
: lf-pp-lam-names ( lam x frames -- ... frames next )
  >r drop dup lf-pp-chain-from lf-pp-show-bind ok-then? 0= if r> 0 exit then
  dup lf-pp-groupable? ok-then2? 0= if r> 0 exit then
  if lf-pp-space lf-term-second@ 0 r> ['] frame-return lf-pp-names-call
  else drop outcome-ok r> 0 then ;
' lf-pp-lam-names is lf-pp-names-step
\ Groups that are parts of the fun's visit: a bracket (its kind waits for
\ the closing bracket) or an instance binder.
: lf-pp-closing ( outcome frames -- outcome frames 0 )
  >r r@ frame-restore over ok? if lf-pp-close else drop then r> 0 ;
: lf-pp-lam-bracket ( lam frames cont -- ... frames next )
  over frame-save >r dup lf-pp-kind dup r@ frame-save lf-pp-open
  0 r> ['] lf-pp-closing lf-pp-names-call ;
: lf-pp-lam-instance ( lam frames cont -- ... frames next )
  2>r dup lf-term-second@ 0 lf-pp-loose? ok-keep? 0= if nip 2r> exit then
  lf-binder-instance lf-pp-open 0= lf-pp-chain-from 2r> lf-pp-typed-binder ;
: lf-pp-lam-group ( lam frames cont -- ... frames next )
  2 pick lf-pp-kind lf-binder-instance =
  if lf-pp-lam-instance else lf-pp-lam-bracket then ;
\ The fun's groups from node, the next binder to bring into scope:
\ explicit binders at once, any other group as a part of the visit, node
\ and the depth before it waiting meanwhile; then ↦ and the body.
: lf-pp-fun-tail ( body frames -- ... frames next )
  >r lf-pp-mapsto 0 r> ['] frame-return lf-pp-term-call ;
defer lf-pp-lam-groups ( node frames -- ... frames next )
: lf-pp-groups-back ( outcome frames -- ... frames next )
  2 lf-pp-failed? if 0 exit then
  >r r@ lf-pp-restore2 lf-pp-depth swap - lf-pp-bodies r> lf-pp-lam-groups ;
: lf-pp-group-part ( node frames -- ... frames next )
  >r dup lf-pp-depth r@ lf-pp-save2 r> ['] lf-pp-groups-back lf-pp-lam-group ;
: lf-pp-lam-default ( node -- node' outcome )
  dup lf-pp-chain-from lf-pp-show-bind swap lf-term-second@ swap ;
: lf-pp-groups-from ( node frames -- ... frames next )
  >r begin dup lf-tag-lam lf-pp-is? while
    lf-pp-space dup lf-pp-kind lf-binder-default <> if r> lf-pp-group-part exit then
    lf-pp-lam-default ok-then? 0= if r> 0 exit then
  repeat r> lf-pp-fun-tail ;
' lf-pp-groups-from is lf-pp-lam-groups
\ The fun's visit: its parenthesis flag, the chain's start before it and
\ the depth before it wait until it ends.
: lf-pp-fun-end ( outcome frames -- outcome frames 0 )
  >r r@ frame-restore lf-pp-leave r@ frame-restore lf-pjob lf-pjob-chain !
  r> lf-pp-wrapped ;
: lf-pp-lam ( lam pos frames -- ... frames next )
  >r lf-prec-max true lf-pp-parens? lf-pp-open-if r@ frame-save
  lf-pp-chain-from r@ frame-save lf-pp-depth dup r@ frame-save lf-pjob lf-pjob-chain !
  ['] lf-pp-fun-end r@ frame-save lf-pp-fun r> lf-pp-lam-groups ;

\ Dispatch on the node's tag. Variables and constants print through the
\ application printer, which decides on @ for them too; a CASE with one
\ arm for each other tag (read as a table) gives the visit's first step.
: lf-pp-applied-tag? ( tag -- flag )
  dup lf-pp-app-tag? over lf-tag-bvar = or swap lf-tag-constant = or ;
\ A projection leaf (core/projections.fs; plan task 5.2.2) prints as its
\ structure's name and Lean's field number from 1, the head of an
\ application to the projected term: Prod.1 p for Lean's p.1. Not Lean's
\ syntax yet; the printer is untrusted presentation.
: lf-pp-proj-step ( term pos frames -- outcome frames 0 )
  >r drop dup lf-proj-name lf-pp-constant s" ." lf-pp-emit lf-proj-idx 1+ lf-pp-number
  outcome-ok r> 0 ;
\ A literal (core/literals.fs; plan task 5.2.3): its value when it fits
\ one cell, else the number of its limbs.
: lf-pp-lit-step ( term pos frames -- outcome frames 0 )
  >r drop dup lf-lit-small? if lf-lit-cell lf-pp-number
  else s" (literal of " lf-pp-emit lf-term-second@ lf-pp-number s"  limbs)" lf-pp-emit then
  outcome-ok r> 0 ;
\ A string literal (core/string-literals.fs): quoted as Lean quotes it
\ (print-strings.fs).
: lf-pp-str-step ( term pos frames -- outcome frames 0 ) >r drop lf-pp-string r> 0 ;
: lf-pp-tag-step ( tag -- xt )
  dup lf-pp-applied-tag? if drop ['] lf-pp-app exit then
  case lf-tag-sort of ['] lf-pp-concrete-step endof
    lf-tag-symbolic-sort of ['] lf-pp-symbolic endof
    lf-tag-lam of ['] lf-pp-lam endof
    lf-tag-pi of ['] lf-pp-pi endof
    lf-tag-proj of ['] lf-pp-proj-step endof
    lf-tag-lit of ['] lf-pp-lit-step endof
    lf-tag-str of ['] lf-pp-str-step endof
    ['] lf-pp-invalid-step swap endcase ;
: lf-pp-term ( term pos frames -- ... frames next )
  2 pick lf-pp-tag if lf-pp-tag-step else ['] lf-pp-invalid-step then execute ;
' lf-pp-term is lf-pp-term-step

\ Public words; see the header. Every print is busy from lf-pp-start to
\ lf-pp-finish, and visits its root as a visit of the frames (lf-pp-run).
\ A name left out of the pool for lack of room makes an otherwise good
\ print full. A print ends with its visit count back at zero; any other
\ count, or a print the sink reset (against the sink rules), is invalid,
\ and the printer is reset. A result outside the outcome vocabulary is
\ invalid.
: lf-pp-finish ( outcome -- outcome )
  lf-pp-frames frame-busy? lf-pp-broken @ or if drop lf-pp-reset outcome-invalid exit then
  false lf-pp-printing ! outcome-sane dup ok? lf-pp-full? and if drop outcome-full then ;
\ The stores' headers are checked here, at the print's root; its reads
\ check only their indices (core/terms.fs).
: lf-print-stores? ( -- flag )
  lf-name-storage-valid? lf-term-count-valid? and lf-level-count-valid? and ;
: lf-print-ready? ( fuel -- flag ) lf-print-stores? if lf-pp-start else drop false then ;
: lf-print-run ( term pos fuel -- outcome )
  lf-print-ready? if ['] lf-pp-term-step lf-pp-run lf-pp-finish else 2drop outcome-invalid
  then ;
: lf-print-term ( term fuel -- outcome ) 0 swap lf-print-run ;
: lf-print-statement ( term fuel -- outcome ) 0 lf-prop-pos swap lf-print-run ;
: lf-print-level ( level fuel -- outcome )
  lf-print-ready? if false lf-pp-level lf-pp-finish else drop-invalid then ;
\ A name is one visit, with one unit of fuel.
: lf-pp-name-visit ( id x frames -- outcome frames 0 )
  >r drop lf-pp-constant outcome-ok r> 0 ;
: lf-print-name ( id -- outcome )
  dup lf-name-valid? 0= if drop-invalid exit then
  1 lf-print-ready? 0= if drop-invalid exit then
  0 ['] lf-pp-name-visit lf-pp-run lf-pp-finish ;

\ Open terms (plan task 2.4.4, for the proof outline): a term whose
\ variables refer to count binders, the lambda or Pi nodes at addr,
\ outermost first, brought into scope with display names chosen as for one
\ fun (no name repeats, and no capture). lf-print-scoped prints the term
\ in that scope; lf-print-scope-name prints the innermost binder's name.
\ A node that is no lambda or Pi is invalid; the scope is full when the
\ heap has no room for its binders or their names.
: lf-pp-binder-node? ( node -- flag )
  dup lf-tag-lam lf-pp-is? swap lf-tag-pi lf-pp-is? or ;
: lf-pp-scope-bind ( node -- outcome )
  dup lf-pp-binder-node? 0= if drop-invalid exit then
  dup 0 lf-pp-name-binder ok-then2? if swap lf-term-first@ swap lf-pp-bind then ;
: lf-pp-scope ( addr count -- outcome )
  0 ?do dup i cells + @ lf-pp-scope-bind ok-then? 0= if unloop exit then
  loop drop outcome-ok ;
: lf-print-scoped ( term addr count fuel -- outcome )
  lf-print-ready? 0= if 2drop drop-invalid exit then
  lf-pp-scope ok-then? if 0 ['] lf-pp-term-step lf-pp-run then lf-pp-finish ;
: lf-print-scope-name ( addr count fuel -- outcome )
  lf-print-ready? 0= if 2drop outcome-invalid exit then
  lf-pp-scope dup ok? if drop 0 lf-pp-var then lf-pp-finish ;

\ Markdown math, as GitHub renders it: a term in LaTeX between $ and $
\ (inline) or $$ and $$ (display), whatever the mode set by lf-print-setup,
\ which stays as it is. A busy printer refuses at once and writes nothing.
\ The delimiters are written while no print is in progress, so a print
\ that the sink starts then (against the sink rules) is not refused; it
\ runs wholly before or after the term's print and does not disturb it.
: lf-pp-math-run ( term fuel c-addr u -- outcome )
  2dup lf-pp-emit 2>r true lf-pp-math! lf-print-term false lf-pp-math! 2r> lf-pp-emit ;
: lf-pp-math ( term fuel c-addr u -- outcome )
  lf-pp-busy? if 2drop 2drop outcome-invalid else lf-pp-math-run then ;
: lf-print-inline ( term fuel -- outcome ) s" $" lf-pp-math ;
: lf-print-display ( term fuel -- outcome ) s" $$" lf-pp-math ;
