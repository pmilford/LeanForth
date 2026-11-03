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
\
\ Public words (outcomes from lib/outcome.fs):
\   lf-print-setup ( sink options -- )   sink xt ( c-addr u -- ); a mode
\     (lf-print-unicode, lf-print-ascii or lf-print-latex) plus option bits
\     (lf-print-universes shows universe arguments, c.{u}).
\   lf-print-term ( term fuel -- outcome )       a closed term
\   lf-print-statement ( term fuel -- outcome )  a theorem's statement: its
\     Pi spine is printed as a proposition (∀) whatever the quick test says
\   lf-print-level ( level fuel -- outcome )     a universe level
\   lf-print-name ( id -- outcome )              a structured name
\   lf-print-inline, lf-print-display ( term fuel -- outcome )  the term in
\     LaTeX as Markdown math, $...$ or $$...$$
\ ok: printed. invalid: malformed input (bad index, stale reference,
\ unknown tag, a variable outside the term's binders, a corrupted name
\ store), a busy printer or negative fuel. exhausted: out of fuel (one unit
\ per visited node), out of nested visits (lf-print-limit!) or out of room
\ for binder names. After a failure the sink has received a partial text.

require ./print-analysis.fs

1024 constant lf-prec-max      \ atoms; the head of an application
1023 constant lf-prec-arg      \ an argument
1022 constant lf-prec-lead     \ an application, ∀, Type u
26 constant lf-prec-domain     \ left of →
25 constant lf-prec-arrow      \ right of →, and A → B itself

\ A position: the least precedence allowed there, whether text follows at
\ the same level (then an open-ended form such as fun or ∀ needs
\ parentheses), and whether a Pi there is known to be a proposition.
: lf-pos ( prec followed -- pos ) 1 and swap 4 * or ;
: lf-pos-prec ( pos -- prec ) 4 / ;
: lf-pos-followed? ( pos -- flag ) 1 and 0<> ;
: lf-pos-prop? ( pos -- flag ) 2 and 0<> ;
: lf-pp-parens? ( pos prec open -- flag )
  >r over lf-pos-prec < swap lf-pos-followed? r> and or ;
: lf-pp-open-if ( flag -- flag ) dup if s" (" lf-pp-emit then ;
: lf-pp-enclose ( pos flag -- pos' flag ) dup if s" (" lf-pp-emit nip 0 swap then ;
\ Leave the binders bound since the scope had depth0 binders.
: lf-pp-leave ( outcome depth0 -- outcome ) lf-pp-depth swap - lf-pp-unbind ;

defer lf-pp-term-visit ( term pos -- outcome )
: lf-pp-term-call ( term pos -- outcome ) ['] lf-pp-term-visit lf-pp-call ;

\ Sorts: Prop and Type are atoms; Type u and Sort u are not.
: lf-pp-concrete ( term pos -- outcome )
  swap lf-term-first@ dup 2 < if nip lf-pp-sort-number outcome-ok exit then
  swap lf-prec-lead false lf-pp-parens? lf-pp-open-if >r lf-pp-sort-number outcome-ok r>
  lf-pp-wrap ;
: lf-pp-symbolic ( term pos -- outcome )
  swap lf-term-first@ dup lf-pp-level-atom? if nip lf-pp-sort-level exit then
  swap lf-prec-lead false lf-pp-parens? lf-pp-open-if >r lf-pp-sort-level r> lf-pp-wrap ;

\ Atoms: a variable by its display name; a constant by name, with its
\ universe arguments when lf-print-universes is set; @ when asked.
: lf-pp-var ( i -- outcome )
  dup 0 lf-pp-depth within 0= if drop-invalid exit then
  lf-pp-entry lf-pp-text lf-pp-ident outcome-ok ;
: lf-pp-levels-out ( addr count -- outcome )
  0 ?do i if lf-pp-list-comma then dup i lf-pp-level-at false lf-pp-level
    dup ok? 0= if nip unloop exit then drop loop drop outcome-ok ;
: lf-pp-universe-args ( term -- outcome )
  lf-pp-const-levels 0= if outcome-invalid exit then
  dup 0= if 2drop outcome-ok exit then
  lf-pp-universes-open lf-pp-levels-out dup ok? if lf-pp-universes-close then ;
: lf-pp-const ( term -- outcome )
  dup lf-pp-const-name 0= if drop-invalid exit then lf-pp-constant
  lf-pp-universes? if lf-pp-universe-args else drop outcome-ok then ;
: lf-pp-atom ( head at? -- outcome )
  if lf-pp-explicit then
  dup lf-tag-bvar lf-pp-is? if lf-term-first@ lf-pp-var else lf-pp-const then ;

\ Applications: the head, then the shown arguments, each in argument
\ position; an argument is followed unless it is the last shown one and
\ nothing follows the application. info is last * 2 + followed.
: lf-pp-fn ( app -- outcome )
  lf-pp-head 2dup lf-pp-at? >r drop dup lf-pp-atom-head?
  if r> lf-pp-atom else r> drop lf-prec-max true lf-pos lf-pp-term-call then ;
: lf-pp-args-info ( app pos -- info ) lf-pos-followed? 1 and swap lf-pp-last 2* or ;
: lf-pp-arg-pos ( info i -- pos ) over 2/ < swap 1 and 0<> or lf-prec-arg swap lf-pos ;
: lf-pp-arg ( app info i -- outcome )
  >r over r@ lf-pp-visible? 0= if 2drop r> drop outcome-ok exit then
  r@ lf-pp-arg-pos swap r> lf-pp-arg-at swap lf-pp-space lf-pp-term-call ;
: lf-pp-args ( app info -- outcome )
  over lf-pp-head nip 0 ?do 2dup i lf-pp-arg dup ok? 0=
  if nip nip unloop exit then drop loop 2drop outcome-ok ;
: lf-pp-applied ( app pos -- outcome )
  over swap lf-pp-args-info over lf-pp-fn dup ok? if drop lf-pp-args else nip nip then ;
\ No argument shown: the head alone, in the application's own position.
: lf-pp-bare ( app pos -- outcome )
  swap lf-pp-head 2dup lf-pp-at? >r drop dup lf-pp-atom-head?
  if nip r> lf-pp-atom else r> drop swap lf-pp-term-call then ;
: lf-pp-app ( term pos -- outcome )
  over lf-pp-spine >r 2drop r> dup ok? 0= if nip nip exit then drop
  over lf-pp-shown# 0= if lf-pp-bare exit then
  dup lf-prec-lead false lf-pp-parens? lf-pp-enclose >r lf-pp-applied r> lf-pp-wrap ;

\ Binders. A binder's display name is chosen (print-names.fs), shown and
\ brought into scope; its domain is printed before it is in scope. from is
\ the bottom index of the binders a new name must not repeat: a fun's
\ earlier binders, none for Pi.
: lf-pp-name-binder ( node from -- mark outcome ) over lf-term-second@ swap lf-pp-choose ;
: lf-pp-show-bind ( node from -- outcome )
  over swap lf-pp-name-binder dup ok? 0= if nip nip exit then drop
  dup lf-pp-pending lf-pp-ident swap lf-term-first@ swap lf-pp-bind ;
: lf-pp-bind-plain ( node -- outcome )
  dup lf-pp-depth lf-pp-name-binder dup ok?
  if drop swap lf-term-first@ swap lf-pp-bind else nip nip then ;
\ The last binder of a bracketed group: its name unless nameless, the
\ domain, the closing bracket.
: lf-pp-typed-binder ( node nameless from -- outcome )
  >r over r> lf-pp-name-binder dup ok? 0= if nip nip nip exit then drop
  swap 0= if dup lf-pp-pending lf-pp-ident lf-pp-colon then
  over lf-term-first@ 0 lf-pp-term-call dup ok? 0= if nip nip exit then drop
  over lf-pp-kind lf-pp-close swap lf-term-first@ swap lf-pp-bind ;

\ Pi. flags = prop * 2 + dep: whether the Pi is a proposition, and whether
\ its first binder prints as a binder (it is used in the body, or, by
\ Lean's RFC 1834, an explicit binder of a proposition whose domain is not
\ one) rather than as A → B.
: lf-pp-flags ( prop dep -- flags ) 1 and swap 2 and or ;
: lf-pp-flags@ ( flags -- prop dep ) dup 2 and 0<> swap 1 and 0<> ;
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
defer lf-pp-group-visit ( pi flags -- outcome )
: lf-pp-group-call ( pi flags -- outcome ) ['] lf-pp-group-visit lf-pp-call ;
: lf-pp-group-more ( pi flags -- outcome )
  swap dup lf-pp-depth lf-pp-show-bind dup ok? 0= if nip nip exit then drop
  lf-pp-space lf-term-second@ swap lf-pp-group-call ;
: lf-pp-group-end ( pi flags -- outcome )
  1 and 0<> over swap lf-pp-nameless? lf-pp-depth lf-pp-typed-binder ;
: lf-pp-group ( pi flags -- outcome )
  2dup lf-pp-flags@ lf-pp-joins? dup ok? 0= if nip nip nip exit then drop
  if lf-pp-group-more else lf-pp-group-end then ;
' lf-pp-group is lf-pp-group-visit
\ A bracketed group from pi; the term after it.
: lf-pp-binders ( pi flags -- outcome ) over lf-pp-kind lf-pp-open lf-pp-group-call ;
: lf-pp-after ( pi depth0 -- body ) lf-pp-depth swap - lf-pp-bodies ;
: lf-pp-group-then ( pi flags -- body outcome )
  lf-pp-depth >r over swap lf-pp-binders r> swap >r lf-pp-after r> ;
\ The body of a Pi spine keeps the proposition flag.
: lf-pp-body-pos ( flags prec -- pos ) false lf-pos swap 2 and or ;

\ A → B.
: lf-pp-arrow-body ( pi flags -- outcome )
  over lf-term-first@ lf-prec-domain true lf-pos lf-pp-term-call dup ok? 0= if nip nip
  exit then drop
  lf-pp-arrow over lf-pp-bind-plain dup ok? 0= if nip nip exit then drop
  swap lf-term-second@ swap lf-prec-arrow lf-pp-body-pos lf-pp-term-call 1 lf-pp-unbind ;
: lf-pp-arrow-form ( pi pos flags -- outcome )
  swap lf-prec-arrow true lf-pp-parens? lf-pp-open-if >r lf-pp-arrow-body r> lf-pp-wrap ;
\ (x : A) → B and {x : A} → B, for a Pi that is not a proposition.
: lf-pp-dep-body ( pi flags -- outcome )
  lf-pp-depth >r tuck lf-pp-group-then ok-then?
  if lf-pp-arrow swap lf-prec-arrow lf-pp-body-pos lf-pp-term-call else nip then r>
  lf-pp-leave ;
: lf-pp-dep-form ( pi pos flags -- outcome )
  swap lf-prec-arrow true lf-pp-parens? lf-pp-open-if >r lf-pp-dep-body r> lf-pp-wrap ;
\ ∀ g1 g2 ..., B: further binder groups of the proposition join the ∀.
defer lf-pp-forall-visit ( term x -- outcome )
: lf-pp-forall-call ( term x -- outcome ) ['] lf-pp-forall-visit lf-pp-call ;
: lf-pp-forall-next? ( term -- flags flag outcome )
  dup lf-tag-pi lf-pp-is? 0= if drop 0 false outcome-ok exit then
  dup true lf-pp-dep? dup ok? 0= if >r 2drop 0 false r> exit then drop
  tuck lf-pp-arrow? 0= swap true swap lf-pp-flags swap outcome-ok ;
: lf-pp-forall-end ( term -- outcome ) lf-pp-comma 2 lf-pp-term-call ;
: lf-pp-forall-more ( term flags -- outcome )
  lf-pp-space lf-pp-group-then ok-then? if 0 lf-pp-forall-call then ;
: lf-pp-forall-rest ( term x -- outcome )
  drop dup lf-pp-forall-next? dup ok? 0= if nip nip nip exit then drop
  if lf-pp-forall-more else drop lf-pp-forall-end then ;
' lf-pp-forall-rest is lf-pp-forall-visit
: lf-pp-forall-body ( pi flags -- outcome )
  lf-pp-depth >r lf-pp-forall lf-pp-group-then ok-then?
  if 0 lf-pp-forall-call then r> lf-pp-leave ;
: lf-pp-forall-form ( pi pos flags -- outcome )
  swap lf-prec-lead true lf-pp-parens? lf-pp-open-if >r lf-pp-forall-body r> lf-pp-wrap ;
: lf-pp-pi ( pi pos -- outcome )
  2dup lf-pp-pi-flags ok-then? 0= if nip nip exit then
  >r over r@ lf-pp-flags@ nip lf-pp-arrow? if r> lf-pp-arrow-form exit then
  r@ 2 and if r> lf-pp-forall-form else r> lf-pp-dep-form then ;

\ fun b1 b2 ... ↦ body: one fun for a chain of lambdas. Explicit binders
\ show their names only, implicit ones group as {A B}, an instance binder
\ shows [A] or, when used, [a : A]. Names in one fun never repeat.
: lf-pp-chain-from ( -- from ) lf-pjob lf-pjob-chain @ ;
defer lf-pp-names-visit ( lam x -- outcome )
: lf-pp-names-call ( lam x -- outcome ) ['] lf-pp-names-visit lf-pp-call ;
: lf-pp-more-names ( lam -- outcome )
  dup lf-pp-groupable? dup ok? 0= if nip nip exit then drop
  if lf-pp-space lf-term-second@ 0 lf-pp-names-call else drop outcome-ok then ;
: lf-pp-lam-names ( lam x -- outcome )
  drop dup lf-pp-chain-from lf-pp-show-bind ok-then? if lf-pp-more-names then ;
' lf-pp-lam-names is lf-pp-names-visit
: lf-pp-lam-bracket ( lam -- outcome )
  dup lf-pp-kind dup >r lf-pp-open 0 lf-pp-names-call r> over ok?
  if lf-pp-close else drop then ;
: lf-pp-lam-instance ( lam -- outcome )
  dup lf-term-second@ 0 lf-pp-loose? ok-keep? 0= if nip exit then
  lf-binder-instance lf-pp-open 0= lf-pp-chain-from lf-pp-typed-binder ;
: lf-pp-lam-group ( lam -- outcome )
  lf-pp-space dup lf-pp-kind case
    lf-binder-default of lf-pp-chain-from lf-pp-show-bind endof
    lf-binder-instance of lf-pp-lam-instance endof
    >r lf-pp-lam-bracket r> endcase ;
: lf-pp-lam-next ( lam0 -- node ) lf-pp-depth lf-pp-chain-from - lf-pp-bodies ;
: lf-pp-lam-groups ( lam0 -- body outcome )
  begin dup lf-pp-lam-next dup lf-tag-lam lf-pp-is? while
    lf-pp-lam-group dup ok? 0= if exit then drop
  repeat nip outcome-ok ;
: lf-pp-fun-body ( lam -- outcome )
  lf-pp-fun lf-pp-lam-groups ok-then? if lf-pp-mapsto 0 lf-pp-term-call then ;
: lf-pp-fun-scope ( lam -- outcome )
  lf-pp-chain-from >r lf-pp-depth dup lf-pjob lf-pjob-chain ! >r
  lf-pp-fun-body r> lf-pp-leave r> lf-pjob lf-pjob-chain ! ;
: lf-pp-lam ( lam pos -- outcome )
  lf-prec-max true lf-pp-parens? lf-pp-open-if >r lf-pp-fun-scope r> lf-pp-wrap ;

\ Dispatch on the node's tag. Variables and constants print through the
\ application printer, which decides on @ for them too.
: lf-pp-applied-tag? ( tag -- flag )
  dup lf-tag-app = over lf-tag-bvar = or swap lf-tag-constant = or ;
: lf-pp-term ( term pos -- outcome )
  over lf-pp-tag 0= if 2drop outcome-invalid exit then
  dup lf-pp-applied-tag? if drop lf-pp-app exit then
  case lf-tag-sort of lf-pp-concrete endof
    lf-tag-symbolic-sort of lf-pp-symbolic endof
    lf-tag-lam of lf-pp-lam endof
    lf-tag-pi of lf-pp-pi endof
    >r 2drop outcome-invalid r> endcase ;
' lf-pp-term is lf-pp-term-visit

\ Public words; see the header. A name cut short for lack of pool room
\ makes an otherwise good print exhausted.
: lf-pp-finish ( outcome -- outcome )
  dup ok? lf-pp-full? and if drop outcome-exhausted then ;
: lf-print-ready? ( fuel -- flag )
  lf-name-storage-valid? if lf-pp-start else drop false then ;
: lf-print-run ( term pos fuel -- outcome )
  lf-print-ready? if lf-pp-term-call lf-pp-finish else 2drop outcome-invalid then ;
: lf-print-term ( term fuel -- outcome ) 0 swap lf-print-run ;
: lf-print-statement ( term fuel -- outcome ) 2 swap lf-print-run ;
: lf-print-level ( level fuel -- outcome )
  lf-print-ready? if false lf-pp-level lf-pp-finish else drop-invalid then ;
: lf-print-name ( id -- outcome )
  dup lf-name-valid? lf-name-storage-valid? and 0= if drop-invalid exit then
  lf-pp-frames frame-busy? if drop-invalid exit then
  lf-pp-clear lf-pp-constant outcome-ok lf-pp-finish ;

\ Markdown math, as GitHub renders it: a term in LaTeX between $ and $
\ (inline) or $$ and $$ (display), whatever the mode set by lf-print-setup.
: lf-pp-options ( -- addr ) lf-pjob lf-pjob-options ;
: lf-pp-as-latex ( options -- options' ) lf-print-mode-mask invert and lf-print-latex or ;
: lf-pp-math ( term fuel c-addr u -- outcome )
  2dup lf-pp-emit 2>r lf-pp-options @ dup >r lf-pp-as-latex lf-pp-options !
  lf-print-term r> lf-pp-options ! 2r> lf-pp-emit ;
: lf-print-inline ( term fuel -- outcome ) s" $" lf-pp-math ;
: lf-print-display ( term fuel -- outcome ) s" $$" lf-pp-math ;
