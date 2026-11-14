\ LeanForth's side of tests/front/check_synth.py on all of Init (plans
\ FE1e2 and FE1e3; S1_INTERFACE.md §9): Init's export read into a stage
\ with its manifest, its elaboration data read against it, sealed and fed
\ to this context; then (1) every instance's class and keys recomputed
\ from its type (src/front/instances.fs, lf-inst-check): one line per
\ outcome with its count, and one line for each instance that is not ok;
\ (2) for each problem of check_synth.py, the candidates getInstances
\ gives (lf-inst-candidates), by name, or the outcome. Usage:
\   gforth tests/front/synth-init.fs -e 's" EXPORT" s" DATA" synth-init bye'
\ Test support: printing recurses on the host stack over name parts.
require ../../src/front/synth.fs
require ../../src/import/feed.fs

create init /stage allot
create init-feed /feed allot
: must ( outcome -- ) ok? 0= abort" synth-init: a loading step failed" ;
: made ( x outcome -- x ) ok? 0= abort" synth-init: not made" ;
: init-load ( c-addr u c-addr' u' -- )
  2>r 22 init stage-init must init stage-read must
  2r> init init stage-manifest manifest-digest elab-read must
  init stage-seal must init init-feed lf-feed must init lf-menv-stage! ;
: tier ( -- tier ) init stage-tier ;
: .part ( n -- )
  dup tier name-tag@ tag-name-str = if tier name-text@ type else tier name-number@ 0 .r then ;
: .dotted ( n -- ) dup tier name-prefix@ ?dup if recurse ." ." then .part ;

\ ---- (1) The checks.
create tally 8 cells allot
: tally! ( outcome -- ) cells tally + 1 swap +! ;
: .outcome-name ( outcome -- ) outcome-text type ;
: .bad ( i outcome -- )
  ." instance " swap elab-instance@ 2drop elab-decl-name .dotted space .outcome-name cr ;
: check-one ( i -- )
  dup lf-inst-check dup tally! dup ok? if 2drop else .bad then ;
: checks ( -- )
  tally 8 cells erase elab-instance elab-count 0 ?do i check-one loop
  7 0 do tally i cells + @ ?dup if ." checked " i .outcome-name space 0 .r cr then loop ;

\ ---- (2) The problems: terms by name, as tests/front/whnf-cases.fs.
: name-of ( c-addr u -- name )
  0 -rot begin dup while
    2dup s" ." search if 2swap 2 pick - 2swap 1 /string else 2drop 0 0 then
    2>r lf-name-tier name-seek-str made 2r> repeat 2drop ;
create lv-pairs 8 cells allot
: lv! ( level i -- ) 2* cells lv-pairs + >r dup lf-level-identity drop swap r> 2! ;
variable cn-k  variable cn-name
: cn ( l1 .. lk k c-addr u -- term )
  name-of cn-name ! dup cn-k ! 0 ?do cn-k @ 1- i - lv! loop
  cn-name @ lf-name-generation @ lv-pairs cn-k @ lf-cref-new 0= abort" cn"
  lf-cterm-new 0= abort" cn" drop ;
: app ( f a -- t ) lf-term-app 0= abort" app" ;
: lv? ( -- level ) lf-level-mvar-new made ;
: type? ( -- t ) lv? lf-level-succ 0= abort" level" dup lf-level-identity drop
  lf-hterm-sort 0= abort" sort" drop mv-natural lf-mvar-new made ;
: nat ( -- t ) 0 s" Nat" cn ;
: num ( u -- t ) lf-hterm-cell 0= abort" lit" drop ;
: c1 ( t c-addr u -- t' ) 2>r lv? 1 2r> cn swap app ;     \ C.{?u} t
: c1z ( t c-addr u -- t' ) 2>r 0 1 2r> cn swap app ;       \ C.{0} t
: hop ( c-addr u a b c -- t ) >r >r >r 2>r lv? lv? lv? 3 2r> cn r> app r> app r> app ;
: .value ( v -- )
  dup lf-inst-left-out? if drop ." <left out>" else elab-instance@ 2drop elab-decl-name .dotted then ;
: .values ( addr n -- ) dup 0 ?do over i cells + @ .value i 1+ over < if ." , " then loop 2drop ;
: problem ( type c-addr u -- )
  ." problem " type ." : " false lf-mctx-depth{ made >r
  lf-defeq-elab lf-defeq-stuck or lf-defeq-flags! lf-tr-instances lf-defeq-mode!
  lf-inst-candidates dup ok? if drop .values else nip nip ." outcome " .outcome-name then cr
  lf-meta-default lf-tr-default lf-meta-config! r> }lf-mctx-depth drop ;
: problems ( -- )
  type? s" OfNat" c1 0 num app s" OfNat ?T 0" problem
  nat s" OfNat" c1z 0 num app s" OfNat Nat 0" problem
  s" HAdd" type? type? type? hop s" HAdd ?a ?b ?c" problem
  s" HAdd" nat nat type? hop s" HAdd Nat Nat ?c" problem
  type? s" Add" c1 s" Add ?a" problem
  nat s" Add" c1z s" Add Nat" problem
  nat s" Mul" c1z s" Mul Nat" problem
  nat s" Sub" c1z s" Sub Nat" problem
  nat s" LE" c1z s" LE Nat" problem
  nat s" LT" c1z s" LT Nat" problem
  nat s" Inhabited" c1 s" Inhabited Nat" problem
  nat s" BEq" c1z s" BEq Nat" problem
  s" HMul" nat nat type? hop s" HMul Nat Nat ?c" problem ;

\ ---- (3) The searches (src/front/synth.fs, lf-synth-instance), each goal
\ as pinned Lean's #synth elaborates it: its result printed as Lean's
\ pp.all prints it, without @ (`instHAdd.{0} Nat instAddNat`, a raw
\ literal `(nat_lit 0)`), none, stuck, or the outcome and the code; and
\ the instances it tried, in order (Lean's apply trace lines).
: .level ( level -- )   \ a numeral when it is one, else ?
  0 swap begin dup lf-level-tag@ lf-level-tag-succ = while lf-level-first@ swap 1+ swap
  repeat lf-level-tag@ lf-level-tag-zero = if 0 .r else drop ." ?" then ;
: .levels ( const -- )
  lf-term-first@ lf-cref-slot lf-cref-pairs dup 0= if 2drop exit then ." .{"
  0 ?do i if ." , " then dup i lf-cref-pair@ drop .level loop drop ." }" ;
: .head ( t -- )
  dup lf-term-const? if dup lf-term-first@ lf-cref-slot lf-cref-name@ drop .dotted .levels
  exit then
  dup lf-lit-leaf? if ." (nat_lit " lf-lit-cell 0 .r ." )" exit then
  dup lf-term-tag@ lf-tag-symbolic-sort = if ." Sort ?" drop exit then drop ." ?" ;
: .term ( t -- )
  dup lf-term-app? if dup lf-term-first@ recurse space lf-term-second@
    dup lf-term-app? if ." (" recurse ." )" else .head then exit then .head ;
: .result ( inst flag outcome -- )
  dup lf-meta-stuck = if drop 2drop ." stuck" exit then
  dup ok? 0= if nip nip outcome-text type space lf-synth-error 0 .r exit then drop
  if .term else drop ." none" then ;
: .tried ( -- ) lf-synth-tried .values ;
: search ( type c-addr u -- )
  2dup ." synth " type ." : " rot lf-synth-instance .result cr
  ." tried " type ." : " .tried cr ;
: ?level ( -- level ) lv? ;
: ?type ( level -- t ) lf-level-succ 0= abort" level" dup lf-level-identity drop
  lf-hterm-sort 0= abort" sort" drop mv-natural lf-mvar-new made ;
: prop ( -- t ) 0 0 lf-level-identity drop lf-hterm-sort 0= abort" sort" drop ;
: one ( -- level ) 0 lf-level-succ 0= abort" level" ;
: c1u ( level t c-addr u -- t' ) 2>r swap 1 2r> cn swap app ;   \ C.{l} t
: c2z ( a b c-addr u -- t ) 2>r 0 0 2 2r> cn rot app swap app ;  \ C.{0,0} a b
create hl 3 cells allot
: hl@ ( i -- level ) cells hl + @ ;
: hout ( a b c-addr u -- t )   \ C.{0,0,?w} a b ?c, ?c : Type ?w
  ?level hl ! 2>r 0 0 0 hl@ 3 2r> cn rot app swap app 0 hl@ ?type app ;
: hvars ( c-addr u -- t )   \ C.{?u,?v,?w} ?a ?b ?c, ?a : Type ?u, ...
  3 0 do ?level hl i cells + ! loop 2>r 0 hl@ 1 hl@ 2 hl@ 3 2r> cn
  3 0 do i hl@ ?type app loop ;
: searches ( -- )
  ?level dup ?type swap 1 s" OfNat" cn swap app 0 num app s" OfNat ?T 0" search
  nat s" OfNat" c1z 0 num app s" OfNat Nat 0" search
  s" HAdd" hvars s" HAdd ?a ?b ?c" search
  nat nat s" HAdd" hout s" HAdd Nat Nat ?c" search
  ?level dup ?type s" Add" c1u s" Add ?a" search
  nat s" Add" c1z s" Add Nat" search
  nat s" Mul" c1z s" Mul Nat" search   nat s" Sub" c1z s" Sub Nat" search
  nat s" LE" c1z s" LE Nat" search   nat s" LT" c1z s" LT Nat" search
  one nat s" Inhabited" c1u s" Inhabited Nat" search
  nat s" BEq" c1z s" BEq Nat" search
  nat nat s" HMul" hout s" HMul Nat Nat ?c" search
  nat nat s" HSub" hout s" HSub Nat Nat ?c" search
  nat nat s" HPow" hout s" HPow Nat Nat ?c" search
  nat s" OfNat" c1z 5 num app s" OfNat Nat 5" search
  prop s" Add" c1z s" Add Prop" search
  0 s" Bool" cn s" OfNat" c1z 0 num app s" OfNat Bool 0" search
  one nat s" Nonempty" c1u s" Nonempty Nat" search
  nat s" Mod" c1z s" Mod Nat" search   nat s" Div" c1z s" Div Nat" search
  nat nat s" HMod" hout s" HMod Nat Nat ?c" search
  nat s" Max" c1z s" Max Nat" search   nat s" Min" c1z s" Min Nat" search
  one prop s" Inhabited" c1u s" Inhabited Prop" search
  one 0 s" Bool" cn s" Inhabited" c1u s" Inhabited Bool" search
  nat nat s" Pow" c2z s" Pow Nat Nat" search
  nat s" NatPow" c1z s" NatPow Nat" search
  0 s" Int" cn s" Neg" c1z s" Neg Int" search
  0 s" Int" cn s" Add" c1z s" Add Int" search ;

: synth-init ( c-addr u c-addr' u' -- ) init-load lf-mctx-reset checks problems searches ;
