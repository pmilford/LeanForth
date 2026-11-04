\ The derivation log (ADR 0013, plan task 2.4.1): an optional, bounded
\ notebook in which the checker writes one numbered record for each rule
\ it applies, and which nothing in the checker ever reads. Off unless
\ asked for; while it is off, the checker's only cost is the test lf-log?
\ ( -- flag ), one fetch from the current context, at each logged site.
\
\ Records (L1). Step s is record s, counting from 1 in the log's order. A
\ rule opens before its work and closes after it, and its record is
\ written when it closes, after the records of everything it used
\ (post-order): its sub-derivation is steps start+1 to s-1, and its
\ premises are the top-level records of that range, found from start
\ alone (lf-log-premise). A record holds the rule's code (the catalogue
\ below), its outcome (ADR 0008: ok, or the failure the rule ended with),
\ start, the context depth (binders around its subject), and its inputs a
\ and b and its result out, each a reference of the kind the catalogue
\ gives: a term or a level (n >= 0 is input object n, below the input
\ marks; -1-k is copy k in the log's own pool; lf-log-none; lf-log-unkept
\ for a scratch object at level steps), or a plain number (a name, a slot,
\ a count). A rule's depth is the one it opens with (inference rules: the
\ binder context's depth), else the innermost open rule's.
\
\ Copies (L1, owner decision D3). At level terms each scratch term or
\ level a record mentions is copied into the log's pools when the record
\ is written, its identity checked first: a copied node keeps its tag and
\ its children as references, so input subterms are shared, and a memo
\ copies a scratch node once while it lives. The copier reads the stores
\ only through lf-term-read, lf-term-identity, lf-level-read and
\ lf-level-identity and does not recurse: a node's scratch children lie
\ below it in its store, so one pass down marks what is reachable and one
\ pass up copies it, children first. Constant nodes are kept only for
\ references below the input marks; any other is a node it cannot read.
\
\ Bounds (L3, owner decision D2). The first bound reached wins: no room for
\ a record, for an open rule (a mark), in either pool, or a node the copier
\ cannot read. The log then records the step it could not write and the
\ bound, stops recording (lf-log? is false from then on) and stays a
\ consistent prefix: steps 1 to N-1 complete, nothing after. Only the log
\ is incomplete: it never changes an outcome, a result or fuel.
\
\ Why it cannot change a verdict (L5): it writes only its own context
\ record and the shared options (only outside jobs, by lf-log-set and
\ lf-log-limits); it reads the checker's stores only through the read-only
\ words above; it never throws, aborts, allocates, prints or notes a
\ diagnostic; every bound is checked before use; and its open and close
\ words leave the stack as the kernel word left it. A kernel site reads
\ lf-log? and runs the same kernel word on both paths.
\
\ Lifetime. lf-env-begin calls lf-log-begin, which starts a fresh log for
\ the check at the options' level (or clears it when that is off); after
\ the hand-over, lf-log-publish writes the publish record and the log
\ stays readable, not recording, until the next lf-log-begin in that
\ context. lf-log-start starts a log for work outside the checked
\ environment (a test calling lf-mixed-infer directly).
\ Test preset: a word lf-log-preset-level defined before this file loads
\ (gforth -e "2 constant lf-log-preset-level" test.fs, as
\ tests/support/gforth-log.sh does) sets that level and makes every
\ context log every call, restarting a truncated log when its outermost
\ rule ends (a check's log only at the next check); lf-log-preset-records,
\ -marks, -terms and -levels set the limits. So every existing test can
\ run with the log on, and with the log full at any step.
\
\ [kernel] path (called from the checker), no-behaviour-change review.
\ Limits: lf-log-record-capacity records, lf-log-mark-capacity open rules,
\ lf-log-term-capacity and lf-log-level-capacity copies per context; the
\ reach flags are sized by the term and level stores (64 nodes each),
\ which the compact store (ADR 0016) will replace by a walk.
\ State: the shared options record lf-log-options (read-only during a
\ run), the two copier descriptors (constant), and one context record,
\ lf-log-state (ADR 0009): header, open rules, records, pools, memos and
\ reach flags.

require ../lib/lib.fs
require ./terms.fs
require ./levels.fs
require ./constant-references.fs
require ./tagged-sort-boundary.fs
require ./constant-term-boundary.fs
require ./input.fs

1024 constant lf-log-record-capacity
256 constant lf-log-mark-capacity
2048 constant lf-log-term-capacity
512 constant lf-log-level-capacity
256 constant lf-log-memo-size

\ Levels (L2): off, steps (records without copies), terms (with copies;
\ the proof outline needs it).
0 constant lf-log-off
1 constant lf-log-steps
2 constant lf-log-terms

\ References that are no object: none, and a scratch object not kept.
max-n invert constant lf-log-none
lf-log-none 1+ constant lf-log-unkept

\ The bound that truncated a log.
1 constant lf-bound-records
2 constant lf-bound-marks
3 constant lf-bound-terms
4 constant lf-bound-levels
5 constant lf-bound-unreadable

\ The kinds of a rule's a, b and out.
0 constant lf-ref-none
1 constant lf-ref-term
2 constant lf-ref-level
3 constant lf-ref-number
: lf-ref-kinds ( a b out -- kinds ) 16 * swap 4 * + + ;

\ The rule catalogue: stable codes, like the diagnostic codes, documented
\ in docs/programming/DERIVATION_LOG.md, which tests/core/check_log_catalogue.py
\ keeps equal to this table. Codes 10-19 are conversion and reduction
\ steps: phase 4 adds unfold (14: a named constant replaced by its value,
\ Lean's delta), eta (15), proof-irrelevance (16) and let (17, zeta) beside
\ whnf and beta, as further premises of whnf and defeq.
1 constant lf-rule-sort
2 constant lf-rule-variable
3 constant lf-rule-constant
4 constant lf-rule-application
5 constant lf-rule-lambda
6 constant lf-rule-pi
7 constant lf-rule-form
10 constant lf-rule-whnf
11 constant lf-rule-beta
12 constant lf-rule-defeq
13 constant lf-rule-level-eq
20 constant lf-rule-instantiate
21 constant lf-rule-shift
22 constant lf-rule-instantiate-levels
30 constant lf-rule-resolve
31 constant lf-rule-fresh-name
32 constant lf-rule-universe-arity
33 constant lf-rule-universe-parameter
34 constant lf-rule-distinct-parameters
40 constant lf-rule-proposition
41 constant lf-rule-declaration
42 constant lf-rule-publish
43 constant lf-rule-type

\ Each entry: the code, the kinds, the name's length and its characters,
\ aligned; the last entry, code 0, names every code not listed.
: lf-log-entry, ( code kinds c-addr u -- )
  2swap swap , , dup , here swap dup allot move align ;
: lf-log-entry-code ( entry -- code ) @ ;
: lf-log-entry-kinds ( entry -- kinds ) cell+ @ ;
: lf-log-entry-name ( entry -- c-addr u ) 2 cells + dup cell+ swap @ ;
: lf-log-entry-next ( entry -- entry' ) lf-log-entry-name + aligned ;
lf-ref-term lf-ref-none lf-ref-term lf-ref-kinds constant lf-kinds-infer
lf-ref-term lf-ref-term lf-ref-term lf-ref-kinds constant lf-kinds-terms
lf-ref-term lf-ref-number lf-ref-term lf-ref-kinds constant lf-kinds-count
lf-ref-number lf-ref-none lf-ref-none lf-ref-kinds constant lf-kinds-number
lf-ref-number lf-ref-number lf-ref-none lf-ref-kinds constant lf-kinds-numbers
lf-ref-term lf-ref-none lf-ref-level lf-ref-kinds constant lf-kinds-formation
create lf-log-catalogue
  lf-rule-sort lf-kinds-infer s" sort" lf-log-entry,
  lf-rule-variable lf-kinds-infer s" variable" lf-log-entry,
  lf-rule-constant lf-kinds-infer s" constant" lf-log-entry,
  lf-rule-application lf-kinds-infer s" application" lf-log-entry,
  lf-rule-lambda lf-kinds-infer s" lambda" lf-log-entry,
  lf-rule-pi lf-kinds-infer s" pi" lf-log-entry,
  lf-rule-form lf-kinds-infer s" form" lf-log-entry,
  lf-rule-whnf lf-kinds-infer s" whnf" lf-log-entry,
  lf-rule-beta lf-kinds-terms s" beta" lf-log-entry,
  lf-rule-defeq lf-ref-term lf-ref-term lf-ref-none lf-ref-kinds s" defeq" lf-log-entry,
  lf-rule-level-eq lf-ref-level lf-ref-level lf-ref-none lf-ref-kinds s" level-eq"
  lf-log-entry,
  lf-rule-instantiate lf-kinds-terms s" instantiate" lf-log-entry,
  lf-rule-shift lf-kinds-count s" shift" lf-log-entry,
  lf-rule-instantiate-levels lf-kinds-count s" instantiate-levels" lf-log-entry,
  lf-rule-resolve lf-ref-number lf-ref-none lf-ref-number lf-ref-kinds s" resolve"
  lf-log-entry,
  lf-rule-fresh-name lf-kinds-number s" fresh-name" lf-log-entry,
  lf-rule-universe-arity lf-kinds-numbers s" universe-arity" lf-log-entry,
  lf-rule-universe-parameter lf-kinds-number s" universe-parameter" lf-log-entry,
  lf-rule-distinct-parameters lf-kinds-number s" distinct-parameters" lf-log-entry,
  lf-rule-proposition lf-kinds-formation s" proposition" lf-log-entry,
  lf-rule-declaration lf-ref-term lf-ref-term lf-ref-none lf-ref-kinds s" declaration"
  lf-log-entry,
  lf-rule-publish lf-kinds-numbers s" publish" lf-log-entry,
  lf-rule-type lf-kinds-formation s" type" lf-log-entry,
  0 0 s" unknown rule" lf-log-entry,
: lf-log-end? ( code entry -- flag ) lf-log-entry-code tuck = swap 0= or ;
\ The entry of code, or the last entry.
: lf-log-entry ( code -- entry )
  lf-log-catalogue begin 2dup lf-log-end? 0= while lf-log-entry-next repeat nip ;
: lf-log-rule-name ( code -- c-addr u ) lf-log-entry lf-log-entry-name ;
\ The kind of a, b or out (shift 0, 2 or 4) of a rule.
: lf-log-kind ( rule shift -- kind )
  swap lf-log-entry lf-log-entry-kinds swap rshift 3 and ;

\ The rule of an inference visit, from the node's tag; form for a node
\ inference does not handle or cannot read. A CASE with one arm per tag.
: lf-log-tag-rule ( tag -- rule )
  case lf-tag-sort of lf-rule-sort endof lf-tag-symbolic-sort of lf-rule-sort endof
    lf-tag-bvar of lf-rule-variable endof lf-tag-constant of lf-rule-constant endof
    lf-tag-app of lf-rule-application endof lf-tag-lam of lf-rule-lambda endof
    lf-tag-pi of lf-rule-pi endof lf-rule-form swap endcase ;
: lf-log-node-rule ( node -- rule )
  lf-term-read if 2drop lf-log-tag-rule else lf-rule-form then ;

\ The options (L2), shared and read-only during a run: the level of every
\ check of the checked environment, the limits (at most the capacities)
\ and the test preset's auto flag. Set only outside jobs; inside one the
\ setting words do nothing.
begin-structure /lf-logopt
  field: lf-logopt-level
  field: lf-logopt-records
  field: lf-logopt-marks
  field: lf-logopt-terms
  field: lf-logopt-levels
  field: lf-logopt-auto
end-structure
create lf-log-options /lf-logopt allot
lf-log-options /lf-logopt erase
: lf-log-clamp ( n capacity -- n' ) swap 0 max min ;
: lf-log-limit! ( n capacity field -- ) >r lf-log-clamp lf-log-options r> + ! ;
: lf-log-limits ( records marks terms levels -- )
  context-in-job? if 2drop 2drop exit then
  lf-log-level-capacity 0 lf-logopt-levels lf-log-limit!
  lf-log-term-capacity 0 lf-logopt-terms lf-log-limit!
  lf-log-mark-capacity 0 lf-logopt-marks lf-log-limit!
  lf-log-record-capacity 0 lf-logopt-records lf-log-limit! ;
: lf-log-capacities ( -- records marks terms levels )
  lf-log-record-capacity lf-log-mark-capacity lf-log-term-capacity lf-log-level-capacity ;
: lf-log-set ( level -- )
  context-in-job? if drop exit then lf-log-terms 0 lf-logopt-level lf-log-limit! ;

\ The limits start at the capacities; the test preset (see the header) is
\ read once, here.
lf-log-capacities lf-log-limits
[defined] lf-log-preset-records [if]
  lf-log-preset-records lf-log-record-capacity 0 lf-logopt-records lf-log-limit! [then]
[defined] lf-log-preset-marks [if]
  lf-log-preset-marks lf-log-mark-capacity 0 lf-logopt-marks lf-log-limit! [then]
[defined] lf-log-preset-terms [if]
  lf-log-preset-terms lf-log-term-capacity 0 lf-logopt-terms lf-log-limit! [then]
[defined] lf-log-preset-levels [if]
  lf-log-preset-levels lf-log-level-capacity 0 lf-logopt-levels lf-log-limit! [then]
[defined] lf-log-preset-level [if]
  lf-log-preset-level lf-log-set true lf-log-options lf-logopt-auto !
[then]

\ An open rule (a mark) and a record.
begin-structure /lf-logmark
  field: logmark-rule
  field: logmark-start
  field: logmark-depth
  field: logmark-a
  field: logmark-a-id      \ a's identity when the rule opened, for a term or level
  field: logmark-b
  field: logmark-b-id
end-structure
begin-structure /lf-logrec
  field: logrec-rule       \ the rule's code
  field: logrec-outcome    \ its outcome
  field: logrec-start      \ records written when it opened
  field: logrec-depth      \ binders around its subject
  field: logrec-a
  field: logrec-b
  field: logrec-out
end-structure

\ The log of one context.
begin-structure /lf-logs
  field: lf-logs-active      \ the level while it records; 0 when off or truncated
  field: lf-logs-level       \ the level it started at; 0 for no log
  field: lf-logs-auto        \ restarts itself (the test preset)
  field: lf-logs-held        \ a check's log, kept until the next lf-log-begin
  field: lf-logs-decl        \ the declaration that check checked
  field: lf-logs-count       \ records written
  field: lf-logs-opens       \ rules open now
  field: lf-logs-cut         \ the step that could not be written; 0 while complete
  field: lf-logs-bound       \ the bound that stopped it
  field: lf-logs-records-max
  field: lf-logs-marks-max
  field: lf-logs-terms-max
  field: lf-logs-levels-max
  field: lf-logs-terms       \ term copies made
  field: lf-logs-levels      \ level copies made
  field: lf-logs-term-mark   \ input terms lie below
  field: lf-logs-level-mark  \ input levels lie below
  field: lf-logs-cref-mark   \ input constant references lie below
  field: lf-logs-written     \ statistics: records written in this context, in all
  field: lf-logs-restarts    \ statistics: preset logs restarted after truncation
  lf-log-memo-size 3 * cells +field lf-logs-term-memo
  lf-log-memo-size 3 * cells +field lf-logs-level-memo
  lf-term-capacity cells +field lf-logs-term-reach
  lf-level-capacity cells +field lf-logs-level-reach
  lf-log-mark-capacity /lf-logmark * +field lf-logs-marks
  lf-log-record-capacity /lf-logrec * +field lf-logs-records
  lf-log-term-capacity /node * +field lf-logs-term-pool
  lf-log-level-capacity /node * +field lf-logs-level-pool
end-structure
/lf-logs context-record: lf-log-state

\ The hot test: nonzero only while this context's log records.
: lf-log? ( -- flag ) lf-log-state lf-logs-active @ ;

\ Reading the log (the printers and tests; never the checker).
: lf-log-count ( -- n ) lf-log-state lf-logs-count @ ;
: lf-log-level ( -- level ) lf-log-state lf-logs-level @ ;
: lf-log-decl ( -- i ) lf-log-state lf-logs-decl @ ;
: lf-log-cut ( -- step bound ) lf-log-state dup lf-logs-cut @ swap lf-logs-bound @ ;
: lf-log-complete? ( -- flag ) lf-log-cut drop 0= ;
\ Record of step s, 1 <= s <= lf-log-count. Unchecked.
: lf-log-record ( step -- rec ) 1- /lf-logrec * lf-log-state lf-logs-records + ;
\ Statistics for tests and measurements: records written in this context
\ since it was made, and preset logs restarted after a truncation.
: lf-log-written ( -- n ) lf-log-state lf-logs-written @ ;
: lf-log-restarts ( -- n ) lf-log-state lf-logs-restarts @ ;
: lf-log-term-copies ( -- n ) lf-log-state lf-logs-terms @ ;
: lf-log-level-copies ( -- n ) lf-log-state lf-logs-levels @ ;
\ Copy k's node (tag first second); unchecked.
: lf-log-term-slot ( k -- addr ) /node * lf-log-state lf-logs-term-pool + ;
: lf-log-level-slot ( k -- addr ) /node * lf-log-state lf-logs-level-pool + ;
\ Whether ref is a copy, and which.
: lf-log-copy? ( ref -- flag ) dup 0< swap lf-log-unkept > and ;
: lf-log-copy-index ( ref -- k ) negate 1- ;
\ The premise before p in a record's chain: the record just before p's
\ own sub-derivation. The premises of s are s-1, then each start of the
\ last, while above s's start.
: lf-log-premise ( p -- p' ) lf-log-record logrec-start @ ;

\ Starting and stopping. The input marks are read when a log starts: the
\ objects below them never change during a check.
: lf-log-memos-clear ( -- )
  lf-log-state dup lf-logs-term-memo lf-log-memo-size 3 * cells erase
  lf-logs-level-memo lf-log-memo-size 3 * cells erase ;
: lf-log-mark-of ( k -- count ) lf-input-intact? if lf-input-mark mark-count @
  else drop 0 then ;
: lf-log-bases ( -- )
  0 lf-log-mark-of lf-log-state lf-logs-term-mark !
  1 lf-log-mark-of lf-log-state lf-logs-level-mark !
  3 lf-log-mark-of lf-log-state lf-logs-cref-mark ! ;
: lf-log-option ( field -- n ) lf-log-options + @ ;
: lf-log-limits! ( -- )
  0 lf-logopt-records lf-log-option lf-log-state lf-logs-records-max !
  0 lf-logopt-marks lf-log-option lf-log-state lf-logs-marks-max !
  0 lf-logopt-terms lf-log-option lf-log-state lf-logs-terms-max !
  0 lf-logopt-levels lf-log-option lf-log-state lf-logs-levels-max ! ;
: lf-log-zero ( field -- ) lf-log-state + 0 swap ! ;
: lf-log-empty ( -- )
  0 lf-logs-count lf-log-zero 0 lf-logs-opens lf-log-zero 0 lf-logs-cut lf-log-zero
  0 lf-logs-bound lf-log-zero 0 lf-logs-terms lf-log-zero 0 lf-logs-levels lf-log-zero
  lf-log-memos-clear ;
: lf-log-run ( level -- )
  lf-log-empty lf-log-bases lf-log-limits!
  dup lf-log-state lf-logs-level ! lf-log-state lf-logs-active ! ;
\ Start a fresh log in this context at level (1 steps, 2 terms; anything
\ else is clamped), outside the checked environment; it records until it
\ is truncated, or until lf-log-stop or the next lf-log-begin.
: lf-log-start ( level -- )
  1 max lf-log-terms min false lf-log-state lf-logs-held ! lf-log-run ;
\ No log: nothing recorded, nothing to read.
: lf-log-stop ( -- )
  lf-log-empty 0 lf-logs-level lf-log-zero 0 lf-logs-active lf-log-zero ;
\ A check of declaration i begins (lf-env-begin): a fresh log at the
\ options' level, held for the check, or none when that is off.
: lf-log-held ( -- ) true lf-log-state lf-logs-held ! ;
: lf-log-begin ( i -- )
  lf-log-state lf-logs-decl ! 0 lf-logopt-level lf-log-option ?dup
  if lf-log-held lf-log-run else lf-log-stop then ;
\ The test preset: every context starts logging.
: lf-log-auto ( -- )
  true lf-log-state lf-logs-auto ! 0 lf-logopt-level lf-log-option lf-log-start ;
: lf-log-setup ( -- ) 0 lf-logopt-auto lf-log-option if lf-log-auto then ;
' lf-log-setup context-setup

\ Truncation (L3): the first bound reached wins.
: lf-log-live? ( -- flag ) lf-log-complete? lf-log-level 0<> and ;
: lf-log-truncate ( bound -- )
  lf-log-state lf-logs-cut @ if drop exit then lf-log-state lf-logs-bound !
  lf-log-count 1+ lf-log-state lf-logs-cut ! 0 lf-logs-active lf-log-zero ;
: lf-log-unreadable ( x -- false ) drop lf-bound-unreadable lf-log-truncate false ;
\ A preset log restarts when its outermost rule ends after a truncation,
\ unless it is a check's.
: lf-log-again? ( -- flag )
  lf-log-state dup lf-logs-auto @ over lf-logs-held @ 0= and swap lf-logs-opens @ 0= and
  lf-log-complete? 0= and ;
: lf-log-settle ( -- )
  lf-log-again? if 1 lf-log-state lf-logs-restarts +! lf-log-level lf-log-run then ;

\ Opening a rule: a mark with its inputs, their identities, the depth and
\ the records written so far. Without room the log is truncated; the
\ rule still counts as open, so that its close balances. While the log
\ records, every open rule has its mark.
: lf-log-opens ( -- addr ) lf-log-state lf-logs-opens ;
: lf-log-mark ( k -- mark ) /lf-logmark * lf-log-state lf-logs-marks + ;
: lf-log-depth ( -- depth )
  lf-log-opens @ dup 0> lf-log-live? and if 1- lf-log-mark logmark-depth @
  else drop 0 then ;
: lf-log-id ( x kind -- id )
  case lf-ref-term of lf-term-identity 0= if 0 then endof
    lf-ref-level of lf-level-identity 0= if 0 then endof nip 0 swap endcase ;
: lf-log-arg ( x rule shift -- x id ) lf-log-kind over swap lf-log-id ;
: lf-log-set-a ( a rule mark -- ) >r 0 lf-log-arg r@ logmark-a-id ! r> logmark-a ! ;
: lf-log-set-b ( b rule mark -- ) >r 2 lf-log-arg r@ logmark-b-id ! r> logmark-b ! ;
: lf-log-mark! ( a b rule depth mark -- )
  tuck logmark-depth ! 2dup logmark-rule ! lf-log-count over logmark-start !
  >r tuck r@ lf-log-set-b r> lf-log-set-a ;
: lf-log-room? ( -- flag ) lf-log-opens @ lf-log-state lf-logs-marks-max @ < ;
: lf-log-push ( a b rule depth -- )
  lf-log-live? 0= if 2drop 2drop exit then
  lf-log-room? if lf-log-opens @ lf-log-mark lf-log-mark! exit then
  2drop 2drop lf-bound-marks lf-log-truncate ;
: lf-log-enter ( a b rule depth -- ) lf-log-push 1 lf-log-opens +! ;
\ Open a rule with inputs a and b (lf-log-none when unused).
: lf-log-open ( a b rule -- ) lf-log-depth lf-log-enter ;
\ Open an inference visit of node at the binder context's depth.
: lf-log-infer ( node depth -- node )
  >r dup lf-log-none over lf-log-node-rule r> lf-log-enter ;

\ The copier, one descriptor per store (a CREATE table, read-only). Its
\ cells name offsets in lf-log-state and the store's words. A memo entry
\ holds a node's index, its identity and its copy's reference; a live
\ node's identity is never 0, so a cleared entry never matches.
begin-structure /lf-copier
  field: copier-mark       \ offset in lf-log-state of the input mark
  field: copier-memo       \ ... of the memo
  field: copier-reach      \ ... of the reach flags
  field: copier-made       \ ... of the count of copies
  field: copier-max        \ ... of their limit
  field: copier-pool       \ xt ( k -- addr ): copy k's slot
  field: copier-read       \ xt ( index -- tag first second true | false )
  field: copier-identity   \ xt ( index -- identity true | false )
  field: copier-arity      \ xt ( tag -- n ): children in first (1) or both (2)
  field: copier-leaf       \ xt ( tag first second -- tag first' second' true | false )
  field: copier-bound      \ the bound when its pool is full
end-structure
/lf-copier 11 cells <> [if] .( derivation-log.fs: copier layout) cr abort [then]
: lf-copier@ ( copier field -- addr ) + @ lf-log-state + ;
: lf-copier-mark ( copier -- n ) 0 copier-mark lf-copier@ @ ;
: lf-copier-flag ( index copier -- addr ) 0 copier-reach lf-copier@ swap cells + ;
: lf-copier-made@ ( copier -- addr ) 0 copier-made lf-copier@ ;
: lf-copier-memo ( index copier -- entry )
  0 copier-memo lf-copier@ swap lf-log-memo-size mod 3 * cells + ;
: lf-copier-input? ( index copier -- flag ) lf-copier-mark < ;
: lf-copier-identity ( index copier -- identity )
  copier-identity @ execute 0= if 0 then ;
: lf-copier-arity ( tag copier -- n ) copier-arity @ execute ;
\ The memo: a node's copy, when the memo holds it; remembering one.
: lf-memo-match? ( index identity entry -- flag ) tuck cell+ @ = -rot @ = and ;
: lf-copier-hit ( index copier -- ref true | false )
  2dup lf-copier-memo >r over swap lf-copier-identity r@ lf-memo-match?
  if r> 2 cells + @ true else r> drop false then ;
: lf-copier-remember ( ref index copier -- )
  2dup lf-copier-memo >r over swap lf-copier-identity r@ cell+ ! r@ ! r> 2 cells + ! ;
\ A child's reference: itself below the mark, else its copy, made before
\ its parent (unkept cannot happen for a child the pass down reached).
: lf-copier-child ( child copier -- ref )
  2dup lf-copier-input? if drop exit then lf-copier-hit 0= if lf-log-unkept then ;
: lf-copier-children ( first second copier -- first' second' )
  tuck lf-copier-child >r lf-copier-child r> ;
\ Pass down, from the node to the mark: a reachable node not yet copied
\ is counted and its scratch children are marked reachable.
: lf-copier-flag! ( index copier -- )
  2dup lf-copier-input? if 2drop exit then lf-copier-flag true swap ! ;
: lf-copier-kids ( index copier -- )
  tuck copier-read @ execute 0= if drop exit then
  rot 3 pick lf-copier-arity case
    2 of rot tuck lf-copier-flag! lf-copier-flag! endof
    1 of drop swap lf-copier-flag! endof >r 2drop drop r> endcase ;
: lf-copier-needs ( n index copier -- n' )
  2dup lf-copier-flag @ 0= if 2drop exit then
  2dup lf-copier-hit if drop 2drop exit then lf-copier-kids 1+ ;
: lf-copier-clear ( node copier -- )
  tuck lf-copier-mark - 1+ cells >r dup lf-copier-mark swap lf-copier-flag r> erase ;
: lf-copier-need ( node copier -- n )
  2dup lf-copier-clear 2dup lf-copier-flag true swap !
  0 -rot dup lf-copier-mark rot do tuck i swap lf-copier-needs swap -1 +loop drop ;
\ Pass up, from the mark to the node: each reachable node not yet copied
\ is copied, its children first.
: lf-copier-append ( tag first second copier -- ref )
  dup lf-copier-made@ dup @ >r 1 swap +! r@ swap copier-pool @ execute
  node! r> 1+ negate ;
: lf-copier-fields ( tag first second copier -- tag first' second' true | false )
  >r 2 pick r@ lf-copier-arity case
    2 of r> lf-copier-children true endof
    1 of swap r> lf-copier-child swap true endof
    drop r> copier-leaf @ execute 0 endcase ;
: lf-copier-node ( index copier -- flag )
  2dup copier-read @ execute 0= if drop lf-log-unreadable exit then
  3 pick lf-copier-fields 0= if 2drop false exit then
  3 pick lf-copier-append -rot lf-copier-remember true ;
: lf-copier-one ( index copier -- flag )
  2dup lf-copier-flag @ 0= if 2drop true exit then
  2dup lf-copier-hit if drop 2drop true exit then lf-copier-node ;
: lf-copier-pass ( node copier -- flag )
  swap 1+ over lf-copier-mark ?do i over lf-copier-one 0= if drop false unloop exit then
  loop drop true ;
: lf-copier-room? ( n copier -- flag )
  dup 0 copier-max lf-copier@ @ swap lf-copier-made@ @ - upto? ;
\ The reference of a live scratch node's copy, made now if needed:
\ (ref true), or false with the log truncated (no room, unreadable).
: lf-copier-copy ( node copier -- ref true | false )
  2dup lf-copier-hit if nip nip true exit then
  2dup lf-copier-need over lf-copier-room? 0=
  if nip copier-bound @ lf-log-truncate false exit then
  2dup lf-copier-pass 0= if 2drop false exit then lf-copier-hit ;
: lf-log-copying? ( -- flag ) lf-log-level lf-log-terms = ;
: lf-log-scratch ( node copier -- ref true | false )
  lf-log-copying? if lf-copier-copy else 2drop lf-log-unkept true then ;

\ Levels: succ has one child (its first field), max and imax two; the zero
\ level and a parameter (its name ID) are kept as they are.
: lf-log-level-arity ( tag -- n )
  dup lf-level-tag-succ = if drop 1 else lf-level-binary-tag? if 2 else 0 then then ;
: lf-log-level-leaf ( tag first second -- tag first second true | false )
  2 pick dup lf-level-tag-zero = swap lf-level-tag-param = or
  if true else 2drop lf-log-unreadable then ;
create lf-log-level-copier
  0 lf-logs-level-mark , 0 lf-logs-level-memo , 0 lf-logs-level-reach ,
  0 lf-logs-levels , 0 lf-logs-levels-max ,
  ' lf-log-level-slot , ' lf-level-read , ' lf-level-identity , ' lf-log-level-arity ,
  ' lf-log-level-leaf , lf-bound-levels ,
\ A level reference: input below the mark, a copy at level terms, unkept
\ at level steps; a level not live with the identity expected is
\ unreadable.
: lf-log-live-level? ( level id -- flag ) swap lf-level-identity if = else
  drop false then ;
: lf-log-level-ref ( level id -- ref true | false )
  over swap lf-log-live-level? 0= if lf-log-unreadable exit then
  dup lf-log-level-copier lf-copier-input? if true exit then
  lf-log-level-copier lf-log-scratch ;

\ Terms: application, lambda and Pi have two children; a symbolic Sort's
\ first field is a level reference; a constant is kept when its reference
\ lies below the input mark; a concrete Sort and a variable are kept as
\ they are; any other tag is unreadable.
: lf-log-term-arity ( tag -- n ) lf-term-binary-tag? if 2 else 0 then ;
: lf-log-cref-input? ( cref -- flag ) lf-log-state lf-logs-cref-mark @ < ;
: lf-log-sort-level ( tag level second -- tag ref second true | false )
  swap dup lf-level-identity 0= if nip lf-log-unreadable nip exit then
  lf-log-level-ref if swap true else 2drop false then ;
: lf-log-cref ( tag cref id -- tag cref id true | false )
  over lf-log-cref-input? if true else 2drop lf-log-unreadable then ;
: lf-log-term-leaf ( tag first second -- tag first' second' true | false )
  2 pick case lf-tag-sort of true endof lf-tag-bvar of true endof
    lf-tag-symbolic-sort of lf-log-sort-level endof
    lf-tag-constant of lf-log-cref endof >r 2drop lf-log-unreadable r> endcase ;
create lf-log-term-copier
  0 lf-logs-term-mark , 0 lf-logs-term-memo , 0 lf-logs-term-reach ,
  0 lf-logs-terms , 0 lf-logs-terms-max ,
  ' lf-log-term-slot , ' lf-term-read , ' lf-term-identity , ' lf-log-term-arity ,
  ' lf-log-term-leaf , lf-bound-terms ,
: lf-log-live-term? ( node id -- flag ) swap lf-term-identity if = else drop false then ;
: lf-log-term-ref ( node id -- ref true | false )
  over swap lf-log-live-term? 0= if lf-log-unreadable exit then
  dup lf-log-term-copier lf-copier-input? if true exit then
  lf-log-term-copier lf-log-scratch ;

\ A reference of a kind: (ref true), or false with the log truncated.
: lf-log-keep ( x id kind -- ref true | false )
  case lf-ref-none of 2drop lf-log-none true endof
    lf-ref-number of drop true endof
    lf-ref-term of lf-log-term-ref endof
    lf-ref-level of lf-log-level-ref endof >r 2drop false r> endcase ;

\ Closing a rule: the record from its mark, its outcome and, when the
\ outcome is ok, its result. A full record buffer or a copy that fails
\ truncates the log instead, and nothing is written.
: lf-log-keep-a ( mark -- ref true | false )
  dup logmark-a @ over logmark-a-id @ rot logmark-rule @ 0 lf-log-kind lf-log-keep ;
: lf-log-keep-b ( mark -- ref true | false )
  dup logmark-b @ over logmark-b-id @ rot logmark-rule @ 2 lf-log-kind lf-log-keep ;
: lf-log-keep-out ( result outcome mark -- ref true | false )
  logmark-rule @ 4 lf-log-kind swap ok? 0= if 2drop lf-log-none true exit then
  2dup lf-log-id swap lf-log-keep ;
: lf-log-refs ( result outcome mark -- a b out true | false )
  >r r@ lf-log-keep-a 0= if 2drop r> drop false exit then
  r@ lf-log-keep-b 0= if drop 2drop r> drop false exit then
  2swap r> lf-log-keep-out if true else 2drop false then ;
: lf-log-fields! ( a b out outcome rule start depth rec -- )
  tuck logrec-depth ! tuck logrec-start ! tuck logrec-rule ! tuck logrec-outcome !
  tuck logrec-out ! tuck logrec-b ! logrec-a ! ;
: lf-log-from ( mark -- rule start depth )
  dup logmark-rule @ over logmark-start @ rot logmark-depth @ ;
: lf-log-new? ( -- flag ) lf-log-count lf-log-state lf-logs-records-max @ < ;
: lf-log-append ( a b out outcome rule start depth -- )
  lf-log-count 1+ lf-log-record lf-log-fields! 1 lf-log-state lf-logs-count +!
  1 lf-log-state lf-logs-written +! ;
: lf-log-top ( -- mark ) lf-log-opens @ lf-log-mark ;
: lf-log-write ( result outcome -- )
  lf-log-new? 0= if 2drop lf-bound-records lf-log-truncate exit then
  dup >r lf-log-top lf-log-refs 0= if r> drop exit then
  r> lf-log-top lf-log-from lf-log-append ;
\ Leaving the innermost open rule; a close without an open (a fault in
\ the caller) truncates the log.
: lf-log-leave ( -- flag )
  lf-log-opens @ 0> if -1 lf-log-opens +! true exit then
  lf-bound-marks lf-log-truncate false ;
\ Close the innermost open rule with its result and outcome, unchanged.
: lf-log-close ( result outcome -- result outcome )
  lf-log-leave lf-log-live? and if 2dup lf-log-write then lf-log-settle ;
\ Close a rule without a result.
: lf-log-decided ( outcome -- outcome ) lf-log-none swap lf-log-close nip ;
\ Close a rule whose result is a (result identity outcome) triple.
: lf-log-close-handle ( result id outcome -- result id outcome ) >r over r>
  lf-log-close nip ;
\ Close a rule whose result is (index id 0) on success, else a status.
: lf-log-close-maybe ( index id 0 | status -- index id 0 | status )
  dup ok? if lf-log-close-handle else -1 swap lf-log-close nip then ;
\ Close a whnf: a reduction that changed nothing applied no rule and
\ writes no record (its mark is dropped).
: lf-log-same? ( index outcome -- flag )
  ok? lf-log-live? and if lf-log-opens @ 1- lf-log-mark logmark-a @ = else
  drop false then ;
: lf-log-drop ( -- ) lf-log-leave drop lf-log-settle ;
: lf-log-close-whnf ( index id outcome -- index id outcome )
  2 pick over lf-log-same? if lf-log-drop else lf-log-close-handle then ;
\ Close every rule still open, each with outcome: the end of a check
\ whose type-formation rule (opened at step 4) never closed.
: lf-log-close-all ( outcome -- outcome )
  begin lf-log-opens @ 1 > while lf-log-decided repeat lf-log-decided ;

\ The end of a check (lf-env-step, after the hand-over, whatever the log
\ level): the publish record, whose one premise is the check's last record
\ (its start is that record's, so sub-derivations stay nested), with the
\ slot, its number of dependencies and the published outcome. The log
\ then stops recording and stays readable until the next lf-log-begin; a
\ preset log stays readable too, records on, and restarts only when it was
\ truncated and its next outermost rule ends.
: lf-log-last-start ( -- start ) lf-log-count ?dup if lf-log-premise else 0 then ;
: lf-log-publish-record ( slot deps outcome -- )
  lf-log-none swap lf-rule-publish lf-log-last-start 0 lf-log-append ;
: lf-log-rest ( -- )
  false lf-log-state lf-logs-held !
  lf-log-state lf-logs-auto @ 0= if 0 lf-logs-active lf-log-zero then ;
: lf-log-publish ( slot deps outcome -- )
  lf-log-live? 0= if 2drop drop lf-log-rest exit then
  lf-log-new? if lf-log-publish-record else 2drop drop lf-bound-records
  lf-log-truncate then
  lf-log-rest ;
