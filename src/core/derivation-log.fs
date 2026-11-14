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
\ only through lf-term-read, lf-term-identity, lf-level-read,
\ lf-level-identity, lf-cref-read and lf-cref-level (values only, never
\ an address of the stores; the input marks through lf-input-mark-count),
\ and walks a node
\ post-order with two bounded stacks of its own: it never recurses and
\ does not depend on the stores' capacities, which are per-context
\ settings of the heap stores. A constant whose reference lies below the
\ input marks is kept with its reference; any other reference is copied
\ with its name and its universe arguments' level references. A term is
\ copied in a context, the binders around it (the record's depth, see
\ lf-log-a-inner, and one more under each binder within it), and a free
\ variable of the local context (plan task 4.2.2a) becomes the bound
\ variable it stands for there (lf-log-fvar), so copies hold no free
\ variables; the memo is keyed by node and context.
\
\ Bounds (L3, owner decision D2). The first bound reached wins: no room for
\ a record, for an open rule (a mark), in a pool (terms, levels, constant
\ references and their arguments), a copy that needs more work or stack
\ than one copy may use, a node the copier cannot read (not live, or not
\ the node the rule opened with), a check that ended with rules still
\ open (a THROW; ADR 0013 L6's interrupted state), or no memory for the
\ pools. The log then records the step it could not write and the bound,
\ stops recording (lf-log? is false from then on) and stays a consistent
\ prefix: steps 1 to N-1 complete, nothing after. Only the log is
\ incomplete: it never changes an outcome, a result or fuel.
\
\ Why it cannot change a verdict (L5): it writes only its own context
\ record, its own heap pools and the shared options (only outside jobs, by
\ lf-log-set and lf-log-limits); it reads the checker's stores only
\ through the read-only words above; it never throws, aborts, prints or
\ notes a diagnostic; it allocates only when a log starts in a context
\ that has no pools (lf-log-run, before the check's first rule) and frees
\ them only when the log is switched off or the context is freed; every
\ bound is checked before use; and its open and close words leave the
\ stack as the kernel word left it. A kernel site reads lf-log? and runs
\ the same kernel word on both paths.
\
\ Lifetime. lf-env-begin calls lf-log-begin, which starts a fresh log for
\ the check at the options' level (or, when that is off, frees the pools
\ and clears the log); after the hand-over, lf-log-publish keeps the
\ published slot and outcome in the header (the printers compare them
\ with the verdict they are given), writes the publish record, and the
\ log stays readable, not recording, until the next lf-log-begin in that
\ context. The header also keeps the input's fingerprint from when the log
\ started, so a printer can tell that the input is still the one the log
\ was taken over. lf-log-start starts a log for work outside the checked
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
\ Limits per context: lf-log-record-capacity records,
\ lf-log-mark-capacity open rules, lf-log-term-capacity and
\ lf-log-level-capacity copies, lf-log-cref-capacity copied references
\ with lf-log-arg-capacity arguments in all, and per copy
\ lf-log-copy-work tasks, on stacks that hold whatever those tasks push,
\ so a copy's depth is bounded only by its work (plan task 6.2.0).
\ State: the shared options record lf-log-options (read-only during a
\ run), the code-indexed catalogue and the two copier descriptors
\ (constant), one small context record, lf-log-state (ADR 0009): the
\ header, counts and limits; and, only while a log is on in a context, one
\ heap block it points to (lf-log-pools: open rules, records, pools, memos
\ and the copiers' stacks, about 410 KiB), freed by lf-log-stop and by the
\ context's teardown (ADR 0009, amended 2026-11-03).

require ../lib/lib.fs
require ./terms.fs
require ./levels.fs
require ./constant-references.fs
require ./tagged-sort-boundary.fs
require ./constant-term-boundary.fs
require ./projections.fs
require ./input.fs
require ./local-context.fs

1024 constant lf-log-record-capacity
256 constant lf-log-mark-capacity
2048 constant lf-log-term-capacity
512 constant lf-log-level-capacity
1024 constant lf-log-memo-size        \ memo entries per store
4096 constant lf-log-copy-work        \ tasks one copy may run
\ The copier's stacks are as deep as one copy's work (plan task 6.2.0): a
\ copy that would hold more tasks or values could not finish within its
\ work anyway (every waiting task costs at least one unit, every value is
\ a task done), so a push past them truncates the log as the work would.
lf-log-copy-work constant lf-log-stack-capacity        \ values
lf-log-copy-work 2* constant lf-log-task-cells         \ a task is two cells
256 constant lf-log-cref-capacity     \ copied constant references
2048 constant lf-log-arg-capacity     \ their universe arguments, in all

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
6 constant lf-bound-work
7 constant lf-bound-refs
8 constant lf-bound-interrupted   \ the check ended with rules open (a THROW)
9 constant lf-bound-memory        \ no memory for the pools when the log started

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
44 constant lf-rule-inductive-block   \ an inductive block's check, as one step

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
  lf-rule-inductive-block lf-kinds-number s" inductive-block" lf-log-entry,
  0 0 s" unknown rule" lf-log-entry,
\ The catalogue indexed by code, filled once here: each code below
\ lf-rule-limit gives its entry, or 0 when it has none; the last entry
\ (code 0) answers for every other code.
64 constant lf-rule-limit
create lf-log-by-code lf-rule-limit cells allot
lf-log-by-code lf-rule-limit cells erase
: lf-log-index ( entry -- )
  dup lf-log-entry-code dup 1 lf-rule-limit within 0= abort" derivation-log: rule code"
  cells lf-log-by-code + ! ;
: lf-log-indexed ( -- last )
  lf-log-catalogue begin dup lf-log-entry-code while dup lf-log-index lf-log-entry-next
  repeat ;
lf-log-indexed constant lf-log-unknown
: lf-log-listed ( code -- entry|0 )
  dup 0 lf-rule-limit within if cells lf-log-by-code + @ else drop 0 then ;
\ The entry of code, or the last entry.
: lf-log-entry ( code -- entry ) lf-log-listed ?dup 0= if lf-log-unknown then ;
: lf-log-rule-name ( code -- c-addr u ) lf-log-entry lf-log-entry-name ;
\ The kind of a, b or out (shift 0, 2 or 4) of a rule.
: lf-log-kind ( rule shift -- kind )
  swap lf-log-entry lf-log-entry-kinds swap rshift 3 and ;
: lf-kind-a ( rule -- kind ) 0 lf-log-kind ;
: lf-kind-b ( rule -- kind ) 2 lf-log-kind ;
: lf-kind-out ( rule -- kind ) 4 lf-log-kind ;

\ The rule of an inference visit, from the node's tag; form for a node
\ inference does not handle or cannot read. A CASE with one arm per tag.
: lf-log-tag-rule ( tag -- rule )
  case lf-tag-sort of lf-rule-sort endof lf-tag-symbolic-sort of lf-rule-sort endof
    lf-tag-bvar of lf-rule-variable endof lf-tag-fvar of lf-rule-variable endof
    lf-tag-constant of lf-rule-constant endof
    lf-tag-app of lf-rule-application endof lf-tag-lam of lf-rule-lambda endof
    lf-tag-pi of lf-rule-pi endof lf-rule-form swap endcase ;
\ A projection (core/projections.fs; plan task 5.2.2), typed by
\ infer_proj, and a let term (core/let-terms.fs; plan task 4.2.3), typed
\ by infer_let, have tags of their own: their steps have the rule form,
\ whose premises are not counted (no rule of their own yet).
: lf-log-node-rule ( node -- rule )
  lf-term-read 0= if lf-rule-form exit then 2drop lf-log-tag-rule ;

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
\ The four limits, k = 0 records, 1 marks, 2 terms, 3 levels: contiguous
\ option fields, each at most its capacity.
create lf-log-caps
  lf-log-record-capacity , lf-log-mark-capacity , lf-log-term-capacity ,
  lf-log-level-capacity ,
0 lf-logopt-levels 0 lf-logopt-records - 3 cells <>
[if] .( derivation-log.fs: option layout) cr abort [then]
: lf-log-limit-at! ( n k -- )
  dup cells lf-log-caps + @ swap cells lf-logopt-records lf-log-limit! ;
: lf-log-limits ( records marks terms levels -- )
  context-in-job? if 2drop 2drop exit then 4 0 do 3 i - lf-log-limit-at! loop ;
: lf-log-capacities ( -- records marks terms levels )
  4 0 do i cells lf-log-caps + @ loop ;
: lf-log-set ( level -- )
  context-in-job? if drop exit then lf-log-terms 0 lf-logopt-level lf-log-limit! ;

\ The limits start at the capacities; the test preset (see the header) is
\ read once, here.
lf-log-capacities lf-log-limits
[defined] lf-log-preset-records [if] lf-log-preset-records 0 lf-log-limit-at! [then]
[defined] lf-log-preset-marks [if] lf-log-preset-marks 1 lf-log-limit-at! [then]
[defined] lf-log-preset-terms [if] lf-log-preset-terms 2 lf-log-limit-at! [then]
[defined] lf-log-preset-levels [if] lf-log-preset-levels 3 lf-log-limit-at! [then]
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
  field: logmark-extra     \ lf-log-extra when the rule opened
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

\ A copied constant reference: its name and name generation, the number
\ of its universe arguments, and where their level references start in
\ the argument pool.
begin-structure /lf-logcref
  field: logcref-name
  field: logcref-generation
  field: logcref-count
  field: logcref-args
end-structure

\ The log of one context: a small header in the context record, and the
\ pools in a heap block that exists only while a log is on (M3 of the
\ review of 2026-11-03: a context with the log off pays only the header).
\ The span from lf-logs-count to lf-logs-args is one log's counts, cleared
\ together when a log starts.
begin-structure /lf-logs
  field: lf-logs-active      \ the level while it records; 0 when off or truncated
  field: lf-logs-level       \ the level it started at; 0 for no log
  field: lf-logs-auto        \ restarts itself (the test preset)
  field: lf-logs-held        \ a check's log, kept until the next lf-log-begin
  field: lf-logs-decl        \ the declaration that check checked
  field: lf-logs-input       \ the input's fingerprint when the log started
  field: lf-logs-slot        \ the slot the check published; -1 before
  field: lf-logs-outcome     \ the outcome it published
  field: lf-logs-pools       \ the heap block of pools, or 0
  field: lf-logs-count       \ records written
  field: lf-logs-opens       \ rules open now
  field: lf-logs-cut         \ the step that could not be written; 0 while complete
  field: lf-logs-bound       \ the bound that stopped it
  field: lf-logs-terms       \ term copies made
  field: lf-logs-levels      \ level copies made
  field: lf-logs-crefs       \ constant references copied
  field: lf-logs-args        \ argument cells used
  field: lf-logs-records-max
  field: lf-logs-marks-max
  field: lf-logs-terms-max
  field: lf-logs-levels-max
  field: lf-logs-term-mark   \ input terms lie below
  field: lf-logs-level-mark  \ input levels lie below
  field: lf-logs-cref-mark   \ input constant references lie below
  field: lf-logs-copy-depth  \ the context a record's terms are copied in
  field: lf-logs-at-node     \ the node the copier combines now
  field: lf-logs-at-context  \ the binders around it (the record's and its own)
  field: lf-logs-term-work   \ work left in the current term copy
  field: lf-logs-level-work  \ work left in the current level copy
  field: lf-logs-written     \ statistics: records written in this context, in all
  field: lf-logs-restarts    \ statistics: preset logs restarted after truncation
  field: lf-logs-extra       \ free variables a conversion has open now (kernel/defeq.fs)
end-structure
/lf-logs context-record: lf-log-state
0 lf-logs-args 0 lf-logs-count - 7 cells <>
0 lf-logs-levels-max 0 lf-logs-records-max - 3 cells <> or
[if] .( derivation-log.fs: header layout) cr abort [then]
\ A memo entry (see the copier below): a node, its identity, the context
\ it was copied in and its copy's reference.
begin-structure /lf-memo
  field: lf-memo-index
  field: lf-memo-identity
  field: lf-memo-context
  field: lf-memo-ref
end-structure
begin-structure /lf-logpools
  lf-log-memo-size /lf-memo * +field lf-logp-term-memo
  lf-log-memo-size /lf-memo * +field lf-logp-level-memo
  lf-log-task-cells 1+ cells +field lf-logp-term-tasks
  lf-log-stack-capacity 1+ cells +field lf-logp-term-values
  lf-log-task-cells 1+ cells +field lf-logp-level-tasks
  lf-log-stack-capacity 1+ cells +field lf-logp-level-values
  lf-log-cref-capacity /lf-logcref * +field lf-logp-cref-pool
  lf-log-arg-capacity cells +field lf-logp-arg-pool
  lf-log-mark-capacity /lf-logmark * +field lf-logp-marks
  lf-log-record-capacity /lf-logrec * +field lf-logp-records
  lf-log-term-capacity /node * +field lf-logp-term-pool
  lf-log-level-capacity /node * +field lf-logp-level-pool
end-structure

\ The hot test: nonzero only while this context's log records.
: lf-log? ( -- flag ) lf-log-state lf-logs-active @ ;
\ The pools; 0 while no log is on in this context.
: lf-log-pools ( -- addr ) lf-log-state lf-logs-pools @ ;

\ Reading the log (the printers and tests; never the checker).
: lf-log-count ( -- n ) lf-log-state lf-logs-count @ ;
: lf-log-level ( -- level ) lf-log-state lf-logs-level @ ;
: lf-log-decl ( -- i ) lf-log-state lf-logs-decl @ ;
: lf-log-cut ( -- step bound ) lf-log-state dup lf-logs-cut @ swap lf-logs-bound @ ;
: lf-log-complete? ( -- flag ) lf-log-cut drop 0= ;
\ The input's fingerprint when the log started; the slot and outcome the
\ check published (slot -1 when none has been published since).
: lf-log-input ( -- h ) lf-log-state lf-logs-input @ ;
: lf-log-published ( -- slot outcome )
  lf-log-state dup lf-logs-slot @ swap lf-logs-outcome @ ;
\ Record of step s, 1 <= s <= lf-log-count. Unchecked.
: lf-log-record ( step -- rec ) 1- /lf-logrec * lf-log-pools lf-logp-records + ;
\ Statistics for tests and measurements: records written in this context
\ since it was made, and preset logs restarted after a truncation.
: lf-log-written ( -- n ) lf-log-state lf-logs-written @ ;
: lf-log-restarts ( -- n ) lf-log-state lf-logs-restarts @ ;
: lf-log-term-copies ( -- n ) lf-log-state lf-logs-terms @ ;
: lf-log-level-copies ( -- n ) lf-log-state lf-logs-levels @ ;
\ Copy k's node (tag first second); unchecked.
: lf-log-term-slot ( k -- addr ) /node * lf-log-pools lf-logp-term-pool + ;
: lf-log-level-slot ( k -- addr ) /node * lf-log-pools lf-logp-level-pool + ;
\ Copied constant references, and the level references of their
\ arguments (logcref-args gives the first); unchecked.
: lf-log-cref-copies ( -- n ) lf-log-state lf-logs-crefs @ ;
: lf-log-cref-slot ( k -- addr ) /lf-logcref * lf-log-pools lf-logp-cref-pool + ;
: lf-log-arg-cell ( i -- addr ) cells lf-log-pools lf-logp-arg-pool + ;
: lf-log-arg-ref ( i -- ref ) lf-log-arg-cell @ ;
\ Whether ref is a copy, and which.
: lf-log-copy? ( ref -- flag ) dup 0< swap lf-log-unkept > and ;
: lf-log-copy-index ( ref -- k ) negate 1- ;
\ The premise before p in a record's chain: the record just before p's
\ own sub-derivation. The premises of s are s-1, then each start of the
\ last, while above s's start.
: lf-log-premise ( p -- p' ) lf-log-record logrec-start @ ;
\ The fields of step s's record, and the nodes and references the pools
\ hold, as values: the printers' and the validator's only way in (they
\ never get an address of the log's), unchecked like lf-log-record.
: lf-log-rule@ ( s -- rule ) lf-log-record logrec-rule @ ;
: lf-log-outcome@ ( s -- outcome ) lf-log-record logrec-outcome @ ;
: lf-log-depth@ ( s -- depth ) lf-log-record logrec-depth @ ;
: lf-log-a@ ( s -- ref ) lf-log-record logrec-a @ ;
: lf-log-b@ ( s -- ref ) lf-log-record logrec-b @ ;
: lf-log-out@ ( s -- ref ) lf-log-record logrec-out @ ;
: lf-log-term-node@ ( k -- tag first second ) lf-log-term-slot node@ ;
: lf-log-level-node@ ( k -- tag first second ) lf-log-level-slot node@ ;
: lf-log-cref@ ( k -- name generation count args )
  lf-log-cref-slot >r r@ logcref-name @ r@ logcref-generation @ r@ logcref-count @
  r> logcref-args @ ;

\ Truncation (L3): the first bound reached wins.
: lf-log-zero ( field -- ) lf-log-state + 0 swap ! ;
: lf-log-live? ( -- flag ) lf-log-complete? lf-log-level 0<> and ;
: lf-log-truncate ( bound -- )
  lf-log-state lf-logs-cut @ if drop exit then lf-log-state lf-logs-bound !
  lf-log-count 1+ lf-log-state lf-logs-cut ! 0 lf-logs-active lf-log-zero ;
: lf-log-unreadable ( x -- false ) drop lf-bound-unreadable lf-log-truncate false ;

\ The pools: allocated when a log starts in a context that has none, freed
\ when the log is switched off and by the context's teardown. A FREE that
\ fails keeps the block recorded, so that the teardown tries again and
\ reports it (context-free).
: lf-log-allocate ( -- flag )
  lf-log-pools if true exit then
  /lf-logpools allocate if drop false exit then lf-log-state lf-logs-pools ! true ;
: lf-log-release ( -- ior )
  lf-log-pools dup 0= if exit then free dup 0= if 0 lf-logs-pools lf-log-zero then ;
:noname ( -- ) lf-log-release throw ; context-teardown

\ Starting and stopping. The input marks are read when a log starts: the
\ objects below them never change during a check.
: lf-log-memos-clear ( -- )
  lf-log-pools ?dup if lf-logp-term-memo lf-log-memo-size 2* /lf-memo * erase then ;
0 lf-logp-level-memo 0 lf-logp-term-memo - lf-log-memo-size /lf-memo * <>
[if] .( derivation-log.fs: memo layout) cr abort [then]
: lf-log-mark-of ( k -- count )
  lf-input-intact? if lf-input-mark-count else drop 0 then ;
: lf-log-bases ( -- )
  0 lf-log-mark-of lf-log-state lf-logs-term-mark !
  1 lf-log-mark-of lf-log-state lf-logs-level-mark !
  3 lf-log-mark-of lf-log-state lf-logs-cref-mark ! ;
: lf-log-option ( field -- n ) lf-log-options + @ ;
: lf-log-limits! ( -- )
  lf-log-options lf-logopt-records lf-log-state lf-logs-records-max 4 cells move ;
: lf-log-empty ( -- ) lf-log-state lf-logs-count 8 cells erase lf-log-memos-clear ;
: lf-log-on ( level -- ) dup lf-log-state lf-logs-level ! lf-log-state lf-logs-active ! ;
: lf-log-input! ( -- ) lf-input-fingerprint lf-log-state lf-logs-input ! ;
\ A fresh log at level; truncated at its first step when there is no
\ memory for its pools.
: lf-log-run ( level -- )
  lf-log-allocate >r lf-log-empty lf-log-bases lf-log-limits! lf-log-input! lf-log-on
  r> 0= if lf-bound-memory lf-log-truncate then ;
\ Start a fresh log in this context at level (1 steps, 2 terms; anything
\ else is clamped), outside the checked environment, of no check (nothing
\ published: slot -1); it records until it is truncated, or until
\ lf-log-stop or the next lf-log-begin.
: lf-log-start ( level -- )
  1 max lf-log-terms min false lf-log-state lf-logs-held ! -1 lf-log-state lf-logs-slot !
  lf-log-run ;
\ No log: nothing recorded, nothing to read, no pools.
: lf-log-stop ( -- )
  lf-log-empty 0 lf-logs-level lf-log-zero 0 lf-logs-active lf-log-zero
  lf-log-release drop ;
\ A check of declaration i begins (lf-env-begin): a fresh log at the
\ options' level, held for the check, or none when that is off; nothing
\ published yet.
: lf-log-held ( -- ) true lf-log-state lf-logs-held ! ;
: lf-log-unpublished ( i -- )
  lf-log-state tuck lf-logs-decl ! -1 swap lf-logs-slot ! ;
: lf-log-begin ( i -- )
  lf-log-unpublished lf-log-input! 0 lf-logopt-level lf-log-option ?dup
  if lf-log-held lf-log-run else lf-log-stop then ;
\ The test preset: every context starts logging.
: lf-log-auto ( -- )
  true lf-log-state lf-logs-auto ! 0 lf-logopt-level lf-log-option lf-log-start ;
: lf-log-setup ( -- ) 0 lf-logopt-auto lf-log-option if lf-log-auto then ;
' lf-log-setup context-setup
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
: lf-log-mark ( k -- mark ) /lf-logmark * lf-log-pools lf-logp-marks + ;
\ The free variables a conversion has open (kernel/defeq.fs sets it) lie
\ around the rules opened meanwhile, so they count as binders: a rule's
\ depth is its enclosing rule's, plus the variables opened since.
: lf-log-extra ( -- addr ) lf-log-state lf-logs-extra ;
: lf-log-binders! ( n -- ) lf-log-extra ! ;
: lf-log-depth ( -- depth )
  lf-log-opens @ dup 0> lf-log-live? and
  if 1- lf-log-mark dup logmark-depth @ swap logmark-extra @ lf-log-extra @ swap - +
  else drop 0 then ;
: lf-log-id ( x kind -- id )
  case lf-ref-term of lf-term-identity 0= if 0 then endof
    lf-ref-level of lf-level-identity 0= if 0 then endof nip 0 swap endcase ;
\ The next mark: its rule, depth and start first; then each input with
\ its identity, the kind its rule gives it.
: lf-log-next-mark ( -- mark ) lf-log-opens @ lf-log-mark ;
: lf-log-mark-head! ( rule depth mark -- )
  lf-log-extra @ over logmark-extra !
  tuck logmark-depth ! tuck logmark-rule ! lf-log-count swap logmark-start ! ;
: lf-log-input-id ( x kind -- x id ) over swap lf-log-id ;
: lf-log-set-a ( a mark -- )
  >r r@ logmark-rule @ lf-kind-a lf-log-input-id r@ logmark-a-id ! r> logmark-a ! ;
: lf-log-set-b ( b mark -- )
  >r r@ logmark-rule @ lf-kind-b lf-log-input-id r@ logmark-b-id ! r> logmark-b ! ;
: lf-log-mark! ( a b rule depth -- )
  lf-log-next-mark dup >r lf-log-mark-head! r@ lf-log-set-b r> lf-log-set-a ;
: lf-log-room? ( -- flag ) lf-log-opens @ lf-log-state lf-logs-marks-max @ < ;
: lf-log-push ( a b rule depth -- )
  lf-log-live? 0= if 2drop 2drop exit then
  lf-log-room? if lf-log-mark! exit then 2drop 2drop lf-bound-marks lf-log-truncate ;
: lf-log-enter ( a b rule depth -- ) lf-log-push 1 lf-log-opens +! ;
\ Open a rule with inputs a and b (lf-log-none when unused).
: lf-log-open ( a b rule -- ) lf-log-depth lf-log-enter ;
\ Open an inference visit of node at the binder context's depth.
: lf-log-infer ( node depth -- node )
  >r dup lf-log-none over lf-log-node-rule r> lf-log-enter ;

\ The copier's stacks: a count cell, then limit cells
\ (lf-log-stack-capacity values, or as many tasks in lf-log-task-cells).
\ Popping is unchecked: the copier pops only what it pushed.
: lf-stack-clear ( stack -- ) 0 swap ! ;
: lf-stack-empty? ( stack -- flag ) @ 0= ;
: lf-stack-push ( x stack limit -- flag )
  over @ > if 1 over +! dup @ cells + ! true else 2drop false then ;
: lf-stack-pop ( stack -- x ) dup @ cells over + @ swap -1 swap +! ;

\ The copier, one descriptor per store (a CREATE table, read-only): its
\ cells name offsets in lf-log-state or in the pools and the store's
\ words. It copies a node post-order with two stacks of its own, so it
\ never recurses and never depends on the store's capacity: a task is a
\ node to expand (n >= 0) or to combine (-1-n) once its children's
\ references lie on the value stack, with its context c, the binders
\ around it (the record's, see lf-log-a-inner, and those of the copied
\ term above it); a child below 0 (a corrupted node) is unreadable. Only
\ a free variable's copy depends on c (it becomes the bound variable it
\ stands for, lf-log-fvar). The memo holds, for a node and a context, its
\ index, its identity, the context and its copy's reference,
\ direct-mapped by index; a live node's identity is never 0, and an
\ identity of 0 never matches, so a cleared entry never matches, and a
\ collision costs only a second copy. One copy may spend lf-log-copy-work
\ tasks; a formula that needs more truncates the log (lf-bound-work),
\ whatever its depth: the stacks are as deep as that work (a push past
\ them, which only a copy that the work would cut can make, truncates the
\ log the same way).
begin-structure /lf-copier
  field: copier-mark       \ offset in lf-log-state of the input mark
  field: copier-memo       \ offset in the pools of the memo
  field: copier-tasks      \ ... of the task stack
  field: copier-values     \ ... of the value stack
  field: copier-work       \ offset in lf-log-state of the work left in this copy
  field: copier-made       \ ... of the count of copies
  field: copier-max        \ ... of their limit
  field: copier-pool       \ xt ( k -- addr ): copy k's slot
  field: copier-read       \ xt ( index -- tag first second true | false )
  field: copier-identity   \ xt ( index -- identity true | false )
  field: copier-arity      \ xt ( tag -- n ): children in first (1) or both (2)
  field: copier-leaf       \ xt ( tag first second -- tag first' second' true | false )
  field: copier-bound      \ the bound when its pool is full
  field: copier-inner      \ xt ( tag -- n ): binders the second child lies under
end-structure
/lf-copier 14 cells <> [if] .( derivation-log.fs: copier layout) cr abort [then]
: lf-copier@ ( copier field -- addr ) + @ lf-log-state + ;
: lf-copier-pooled ( copier field -- addr ) + @ lf-log-pools + ;
: lf-copier-mark ( copier -- n ) 0 copier-mark lf-copier@ @ ;
: lf-copier-tasks ( copier -- stack ) 0 copier-tasks lf-copier-pooled ;
: lf-copier-values ( copier -- stack ) 0 copier-values lf-copier-pooled ;
: lf-copier-made@ ( copier -- addr ) 0 copier-made lf-copier@ ;
: lf-copier-memo ( index copier -- entry )
  0 copier-memo lf-copier-pooled swap lf-log-memo-size mod /lf-memo * + ;
: lf-copier-input? ( index copier -- flag ) lf-copier-mark < ;
: lf-copier-identity ( index copier -- identity )
  copier-identity @ execute 0= if 0 then ;
: lf-copier-arity ( tag copier -- n ) copier-arity @ execute ;
: lf-copier-inner ( tag copier -- n ) copier-inner @ execute ;
\ The memo: a node's copy in a context, when the memo holds it;
\ remembering one.
: lf-memo-match? ( index identity c entry -- flag )
  >r r@ lf-memo-context @ = swap dup 0<> swap r@ lf-memo-identity @ = and and
  swap r> lf-memo-index @ = and ;
: lf-copier-key ( index c copier -- index identity c entry )
  >r over r@ lf-copier-identity swap rot dup r> lf-copier-memo >r -rot r> ;
: lf-copier-hit ( index c copier -- ref true | false )
  lf-copier-key dup >r lf-memo-match? if r> lf-memo-ref @ true else r> drop false then ;
: lf-copier-remember ( ref index c copier -- )
  lf-copier-key >r r@ lf-memo-context ! r@ lf-memo-identity !
  r@ lf-memo-index ! r> lf-memo-ref ! ;
\ A node's reference when it needs no copy: itself below the mark (input
\ never holds a free variable), or the copy the memo holds.
: lf-copier-known ( n c copier -- ref true | false )
  2 pick over lf-copier-input? if 2drop true exit then lf-copier-hit ;

\ Pushing a task (two cells: its context, then the node) or a value; no
\ room truncates the log.
: lf-copier-deep ( copier -- false ) drop lf-bound-work lf-log-truncate false ;
: lf-copier-push ( x copier stack limit -- flag )
  >r rot swap r> lf-stack-push if drop true else lf-copier-deep then ;
: lf-copier-task-push ( x copier -- flag )
  dup lf-copier-tasks lf-log-task-cells lf-copier-push ;
: lf-copier-task ( x c copier -- flag )
  tuck lf-copier-task-push 0= if 2drop false exit then lf-copier-task-push ;
: lf-copier-next ( copier -- x c )
  dup lf-copier-tasks lf-stack-pop swap lf-copier-tasks lf-stack-pop ;
: lf-copier-value ( ref copier -- flag )
  dup lf-copier-values lf-log-stack-capacity lf-copier-push ;
: lf-copier-pop ( copier -- ref ) lf-copier-values lf-stack-pop ;
: lf-combine ( n -- task ) 1+ negate ;
: lf-combined ( task -- n ) negate 1- ;

\ Expanding a node: its reference when it needs no copy; else a combine
\ task, then its children's expand tasks (the second first, so that the
\ first child's value lies below the second's), the second in the context
\ of the binders it lies under; a child below 0 is unreadable.
: lf-copier-child ( n c copier -- flag )
  2 pick 0< if 2drop lf-log-unreadable exit then lf-copier-task ;
: lf-copier-single ( c copier tag first second -- flag ) drop nip -rot lf-copier-child ;
\ The context of the second child: c and the binders the tag puts it under.
: lf-copier-under ( c copier tag -- c copier c' ) over lf-copier-inner 2 pick + ;
: lf-copier-pair ( c copier tag first second -- flag )
  swap >r >r lf-copier-under r> swap 2 pick lf-copier-child
  r> swap >r -rot lf-copier-child r> and ;
: lf-copier-kids ( n c copier -- flag )
  rot over copier-read @ execute 0= if drop lf-log-unreadable exit then
  2 pick 4 pick lf-copier-arity case
    2 of lf-copier-pair endof 1 of lf-copier-single endof
    >r 2drop 2drop drop true r> endcase ;
: lf-copier-expand ( n c copier -- flag )
  >r 2dup r@ lf-copier-known if nip nip r> lf-copier-value exit then
  over lf-combine over r@ lf-copier-task 0= if 2drop r> drop false exit then
  r> lf-copier-kids ;

\ Combining a node: its fields with its children's references, popped
\ from the value stack (the second's on top); a leaf by the store's leaf
\ word; then the copy appended, remembered and pushed as a value.
: lf-copier-two ( tag first second copier -- tag first' second' )
  nip nip dup lf-copier-pop swap lf-copier-pop swap ;
: lf-copier-one ( tag first second copier -- tag first' second )
  rot drop lf-copier-pop swap ;
: lf-copier-fields ( tag first second copier -- tag first' second' true | false )
  3 pick over lf-copier-arity case
    2 of lf-copier-two true endof 1 of lf-copier-one true endof
    >r copier-leaf @ execute r> endcase ;
: lf-copier-append ( tag first second copier -- ref )
  dup lf-copier-made@ dup @ >r 1 swap +! r@ swap copier-pool @ execute
  node! r> 1+ negate ;
: lf-copier-room? ( copier -- flag )
  dup 0 copier-max lf-copier@ @ swap lf-copier-made@ @ > ;
: lf-copier-made! ( ref n c copier -- flag )
  >r 2 pick -rot r@ lf-copier-remember r> lf-copier-value ;
\ The node being combined and its context, for a leaf that needs them (a
\ free variable's); a nested copy (a constant's levels) runs only after
\ the leaf that reads them.
: lf-log-at! ( n c -- ) lf-log-state tuck lf-logs-at-context ! lf-logs-at-node ! ;
: lf-copier-combine ( n c copier -- flag )
  dup lf-copier-room? 0= if nip nip copier-bound @ lf-log-truncate false exit then
  >r 2dup lf-log-at! r> swap >r 2dup copier-read @ execute
  0= if drop lf-log-unreadable r> drop exit then
  3 pick lf-copier-fields 0= if 2drop r> drop false exit then
  3 pick lf-copier-append -rot r> swap lf-copier-made! ;

\ One copy: tasks until none is left, each one unit of the copy's work.
: lf-copier-spend ( copier -- flag )
  0 copier-work lf-copier@ dup @ 0> if -1 swap +! true else drop false then ;
: lf-copier-step ( copier -- flag )
  dup lf-copier-next rot 2 pick 0<
  if rot lf-combined -rot lf-copier-combine else lf-copier-expand then ;
: lf-copier-run ( copier -- flag )
  begin dup lf-copier-tasks lf-stack-empty? 0= while
    dup lf-copier-spend 0= if lf-copier-deep exit then
    dup lf-copier-step 0= if drop false exit then
  repeat drop true ;
: lf-copier-start ( node c copier -- )
  dup lf-copier-tasks lf-stack-clear dup lf-copier-values lf-stack-clear
  lf-log-copy-work over 0 copier-work lf-copier@ ! lf-copier-task drop ;
\ The reference of a live scratch node's copy in context c, made now if
\ needed: (ref true), or false with the log truncated (no room, too much
\ work, unreadable).
: lf-copier-copy ( node c copier -- ref true | false )
  >r 2dup r@ lf-copier-hit if nip nip r> drop true exit then
  r@ lf-copier-start r@ lf-copier-run if r> lf-copier-pop true else r> drop false then ;
: lf-log-copying? ( -- flag ) lf-log-level lf-log-terms = ;
: lf-log-scratch ( node c copier -- ref true | false )
  lf-log-copying? if lf-copier-copy else 2drop drop lf-log-unkept true then ;

\ Levels: succ has one child (its first field), max and imax two; the zero
\ level and a parameter (its name ID) are kept as they are.
: lf-log-level-arity ( tag -- n )
  dup lf-level-tag-succ = if drop 1 else lf-level-binary-tag? if 2 else 0 then then ;
: lf-log-level-leaf ( tag first second -- tag first second true | false )
  2 pick dup lf-level-tag-zero = swap lf-level-tag-param = or
  if true else 2drop lf-log-unreadable then ;
: lf-log-level-inner ( tag -- 0 ) drop 0 ;
create lf-log-level-copier
  0 lf-logs-level-mark , 0 lf-logp-level-memo , 0 lf-logp-level-tasks ,
  0 lf-logp-level-values , 0 lf-logs-level-work , 0 lf-logs-levels ,
  0 lf-logs-levels-max ,
  ' lf-log-level-slot , ' lf-level-read , ' lf-level-identity , ' lf-log-level-arity ,
  ' lf-log-level-leaf , lf-bound-levels , ' lf-log-level-inner ,
\ A level reference: input below the mark, a copy at level terms, unkept
\ at level steps; a level not live with the identity expected is
\ unreadable.
: lf-log-live-level? ( level id -- flag )
  swap lf-level-identity if = else drop false then ;
: lf-log-level-ref ( level id -- ref true | false )
  over swap lf-log-live-level? 0= if lf-log-unreadable exit then
  dup lf-log-level-copier lf-copier-input? if true exit then
  0 lf-log-level-copier lf-log-scratch ;

\ Constant references (variable-length universe arguments, ADR 0016 C2).
\ One below the input mark is kept as it is, with its identity. Another is
\ copied: its name and name generation, the number of its universe
\ arguments, and the offset of their level references in the argument
\ pool, each level copied as above. No room in either pool truncates the
\ log (lf-bound-refs).
: lf-log-cref-input? ( cref -- flag ) lf-log-state lf-logs-cref-mark @ < ;
: lf-log-cref-room? ( -- flag ) lf-log-state lf-logs-crefs @ lf-log-cref-capacity < ;
: lf-log-args-room? ( n -- flag ) lf-log-state lf-logs-args @ +
  lf-log-arg-capacity upto? ;
: lf-log-refs-full ( -- false ) lf-bound-refs lf-log-truncate false ;
: lf-log-arg+ ( ref -- )
  lf-log-state lf-logs-args dup @ lf-log-arg-cell rot swap ! 1 swap +! ;
\ Argument i of the reference, read as a value (lf-cref-level), copied.
: lf-log-arg-copy ( cref crid i -- flag )
  lf-cref-level 0= if 0 lf-log-unreadable exit then
  lf-log-level-ref if lf-log-arg+ true else false then ;
: lf-log-arg-copy-at ( cref crid i -- cref crid flag ) 2dup-under lf-log-arg-copy ;
: lf-log-args-copy ( cref crid count -- flag ) ['] lf-log-arg-copy-at all? nip nip ;
: lf-log-cref-args ( cref crid count -- offset true | false )
  dup lf-log-args-room? 0= if drop 2drop lf-log-refs-full exit then
  lf-log-state lf-logs-args @ >r lf-log-args-copy if r> true else r> drop false then ;
\ The next copy is written in place and counted only when complete.
: lf-log-cref-next ( -- addr ) lf-log-cref-copies lf-log-cref-slot ;
: lf-log-cref-head! ( name generation count -- )
  lf-log-cref-next tuck logcref-count ! tuck logcref-generation ! logcref-name ! ;
: lf-log-cref-made ( offset -- ref )
  lf-log-cref-next logcref-args ! lf-log-cref-copies 1 lf-log-state lf-logs-crefs +!
  1+ negate ;
: lf-log-cref-copy ( cref crid -- ref true | false )
  lf-log-cref-room? 0= if 2drop lf-log-refs-full exit then
  2dup lf-cref-read 0= if 2drop 0 lf-log-unreadable exit then
  dup >r lf-log-cref-head! r> lf-log-cref-args if lf-log-cref-made true else false then ;

\ Terms: application, lambda and Pi have two children (a binder's second
\ under one more binder); a symbolic Sort's first field is a level
\ reference; a constant's is its reference (kept, or copied with second
\ field 0); a concrete Sort and a bound variable are kept as they are; a
\ free variable (core/local-context.fs, plan task 4.2.2a) becomes the
\ bound variable it stands for under the c binders of its context: c - 1
\ - d for its binder's depth d, which inference records in its entry
\ (lf-fvar-depth); any other tag, or a free variable not live or whose
\ binder lies outside its context, is unreadable.
: lf-log-term-arity ( tag -- n ) lf-term-binary-tag? if 2 else 0 then ;
: lf-log-term-inner ( tag -- n ) lf-term-binder-tag? 1 and ;
: lf-log-at-index ( d -- index true | false )
  dup 0< if lf-log-unreadable exit then
  lf-log-state lf-logs-at-context @ swap - 1- dup 0< if lf-log-unreadable exit then true ;
: lf-log-at-fvar ( -- fvar true | false )
  lf-log-state lf-logs-at-node @ dup lf-fvar-live? if true else lf-log-unreadable then ;
: lf-log-fvar ( tag first second -- tag first' second' true | false )
  2drop drop lf-log-at-fvar 0= if false exit then
  lf-fvar-depth lf-log-at-index if lf-tag-bvar swap 0 true else false then ;
: lf-log-sort-level ( tag level second -- tag ref second true | false )
  swap dup lf-level-identity 0= if nip lf-log-unreadable nip exit then
  lf-log-level-ref if swap true else 2drop false then ;
: lf-log-cref ( tag cref 0 -- tag cref' 0 true | false )
  over lf-log-cref-input? if true exit then
  drop dup lf-cref-current lf-log-cref-copy if 0 true else drop false then ;
: lf-log-term-leaf ( tag first second -- tag first' second' true | false )
  2 pick case lf-tag-sort of true endof lf-tag-bvar of true endof
    lf-tag-proj of true endof  lf-tag-lit of true endof
    lf-tag-str of true endof
    lf-tag-symbolic-sort of lf-log-sort-level endof lf-tag-fvar of lf-log-fvar endof
    lf-tag-constant of lf-log-cref endof >r 2drop lf-log-unreadable r> endcase ;
create lf-log-term-copier
  0 lf-logs-term-mark , 0 lf-logp-term-memo , 0 lf-logp-term-tasks ,
  0 lf-logp-term-values , 0 lf-logs-term-work , 0 lf-logs-terms , 0 lf-logs-terms-max ,
  ' lf-log-term-slot , ' lf-term-read , ' lf-term-identity , ' lf-log-term-arity ,
  ' lf-log-term-leaf , lf-bound-terms , ' lf-log-term-inner ,
: lf-log-live-term? ( node id -- flag ) swap lf-term-identity if = else drop false then ;
: lf-log-term-ref ( node id -- ref true | false )
  over swap lf-log-live-term? 0= if lf-log-unreadable exit then
  dup lf-log-term-copier lf-copier-input? if true exit then
  lf-log-state lf-logs-copy-depth @ lf-log-term-copier lf-log-scratch ;

\ A reference of a kind: (ref true), or false with the log truncated. A
\ term input may be none: an axiom's or a quotient record's value.
: lf-log-keep ( x id kind -- ref true | false )
  2 pick lf-log-none = if drop lf-ref-none then
  case lf-ref-none of 2drop lf-log-none true endof
    lf-ref-number of drop true endof
    lf-ref-term of lf-log-term-ref endof
    lf-ref-level of lf-log-level-ref endof >r 2drop false r> endcase ;

\ Closing a rule: the record from its mark, its outcome and, when the
\ outcome is ok, its result. The next record is written in place, field
\ by field, and becomes part of the log only when the count advances
\ (lf-log-commit). A full record buffer or a copy that fails truncates the
\ log instead, and nothing is counted.
: lf-log-next ( -- rec ) lf-log-count 1+ lf-log-record ;
: lf-log-top ( -- mark ) lf-log-opens @ lf-log-mark ;
: lf-log-kept! ( ref true | false addr -- flag ) swap if ! true else drop false then ;
: lf-log-keep-a ( mark -- ref true | false )
  dup logmark-a @ over logmark-a-id @ rot logmark-rule @ lf-kind-a lf-log-keep ;
: lf-log-keep-b ( mark -- ref true | false )
  dup logmark-b @ over logmark-b-id @ rot logmark-rule @ lf-kind-b lf-log-keep ;
: lf-log-keep-out ( result outcome mark -- ref true | false )
  logmark-rule @ lf-kind-out swap ok? 0= if 2drop lf-log-none true exit then
  2dup lf-log-id swap lf-log-keep ;
\ The context terms are copied in (free variables become bound variables
\ there): the record's depth, except that the a of an instantiate or beta
\ step (a body) lies under one more binder and a shift's under amount
\ fewer, as log-view reads them.
: lf-log-a-inner ( mark -- n )
  dup logmark-rule @ case
    lf-rule-instantiate of drop 1 endof lf-rule-beta of drop 1 endof
    lf-rule-shift of logmark-b @ negate endof nip 0 swap endcase ;
: lf-log-copy-depth! ( mark n -- )
  swap logmark-depth @ + lf-log-state lf-logs-copy-depth ! ;
: lf-log-a-top ( -- mark ) lf-log-top dup dup lf-log-a-inner lf-log-copy-depth! ;
: lf-log-at-top ( -- mark ) lf-log-top dup 0 lf-log-copy-depth! ;
: lf-log-a! ( -- flag ) lf-log-a-top lf-log-keep-a lf-log-next logrec-a lf-log-kept! ;
: lf-log-b! ( -- flag ) lf-log-at-top lf-log-keep-b lf-log-next logrec-b lf-log-kept! ;
: lf-log-out! ( result outcome -- flag )
  lf-log-at-top lf-log-keep-out lf-log-next logrec-out lf-log-kept! ;
: lf-log-from! ( mark rec -- )
  over logmark-rule @ over logrec-rule ! over logmark-start @ over logrec-start !
  swap logmark-depth @ swap logrec-depth ! ;
: lf-log-counted ( -- )
  1 lf-log-state lf-logs-count +! 1 lf-log-state lf-logs-written +! ;
: lf-log-commit ( outcome -- )
  lf-log-next tuck logrec-outcome ! lf-log-top swap lf-log-from! lf-log-counted ;
: lf-log-new? ( -- flag ) lf-log-count lf-log-state lf-logs-records-max @ < ;
: lf-log-write ( result outcome -- )
  lf-log-new? 0= if 2drop lf-bound-records lf-log-truncate exit then
  lf-log-a! 0= if 2drop exit then lf-log-b! 0= if 2drop exit then
  tuck lf-log-out! if lf-log-commit else drop then ;
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
\ level): the published slot and outcome kept in the header; then, unless
\ a rule is still open (a check that threw: the log is truncated with
\ lf-bound-interrupted instead), the publish record, whose one premise is
\ the check's last record (its start is that record's, so sub-derivations
\ stay nested), with the slot, its number of dependencies and the
\ published outcome. The log then stops recording and stays readable until
\ the next lf-log-begin; a preset log stays readable too, records on, and
\ restarts only when it was truncated and its next outermost rule ends.
: lf-log-last-start ( -- start ) lf-log-count ?dup if lf-log-premise else 0 then ;
: lf-log-publish-head ( rec -- )
  lf-rule-publish over logrec-rule ! lf-log-last-start over logrec-start !
  0 over logrec-depth ! lf-log-none swap logrec-out ! ;
: lf-log-publish-fields ( slot deps outcome rec -- )
  tuck logrec-outcome ! tuck logrec-b ! logrec-a ! ;
: lf-log-publish-record ( slot deps outcome -- )
  lf-log-next dup lf-log-publish-head lf-log-publish-fields lf-log-counted ;
: lf-log-rest ( -- )
  false lf-log-state lf-logs-held !
  lf-log-state lf-logs-auto @ 0= if 0 lf-logs-active lf-log-zero then ;
: lf-log-published! ( slot outcome -- )
  lf-log-state tuck lf-logs-outcome ! lf-logs-slot ! ;
: lf-log-interrupted ( -- )
  lf-log-opens @ 0<> lf-log-level 0<> and if lf-bound-interrupted lf-log-truncate then ;
: lf-log-publish ( slot deps outcome -- )
  2 pick over lf-log-published! lf-log-interrupted
  lf-log-live? 0= if 2drop drop lf-log-rest exit then
  lf-log-new? if lf-log-publish-record else 2drop drop lf-bound-records
  lf-log-truncate then
  lf-log-rest ;
