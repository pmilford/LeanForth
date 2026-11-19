\ The instance table (plan FE1e3; docs/design/FE1E_APPLICATIONS.md §3.2,
\ §3.3 and §4; S1_INTERFACE.md §9): Lean 4.35.0's global instance index
\ (Lean/Meta/Instances.lean, a DiscrTree) rebuilt from the elaboration
\ data, its getUnify (DiscrTree/Main.lean:567), getInstances
\ (SynthInstance.lean:202), getDefaultInstances (Instances.lean:430),
\ isClass?'s quick test (Meta/Basic.lean:1384) and the check of the data
\ against the types (FE1E §4), each record checked when first needed
\ (MF2's rule, docs/design/MATHLIB_FRONT.md §3). The tree itself is
\ src/front/discr-tree.fs's (plan slice MF2+DT).
\ - lf-inst-classes ( -- outcome ): run by each query word below before
\   anything else: once per data read, the tree's roots, every value's
\   root key (a lib/htab.fs table in the tree); afterwards ok, or the
\   refusal's invalid. The checks run when a record is first needed:
\   before a root's tree is built, on each instance of the root, step 1
\   (its root key must be the constant of its recorded class, error 115;
\   its class recomputed from its type by forallTelescopeReducing at
\   default transparency and isClass?, error 112; the root key's arity
\   the type's number of arguments, else it is filed under another root,
\   error 115), then step 2 (below); before lf-default-instances answers,
\   on each default instance of the class, step 3 (its type must end in
\   its recorded class, error 116). So every value a search can be given
\   has been checked. A difference refuses the data: invalid, and the
\   same answer at every later query, whatever its root, until the data
\   is read again (elab-data.fs's elab-generation) or lf-inst-reset. A
\   record filed under a root, or a default instance under a class, that
\   no query asks is never checked (and never found). A check that cannot
\   finish (unsupported) leaves the record unverified: trusted for its
\   class, as the ranks are (S1 §9). Exhausted and full are answered
\   with nothing kept of them, the records finished staying finished.
\   Step 4 (a class's out-parameters recomputed by checkOutParam) is plan
\   row FE1e3b; until then they rest on pinned Lean.
\ - lf-inst-refusal ( -- code ): the refusal's code (112, 113, 115, 116),
\   0 when the data is not refused; lf-inst-refused-decl ( -- d ): the
\   data declaration of the record it refused (valid while the code is
\   not 0), for the elaborator's error (elab-pending.fs).
\ - lf-inst-telescope ( d -- body outcome ): forallMetaTelescopeReducing
\   (Basic.lean) over declaration d's type: the tactic library's
\   (telescope.fs: a new metavariable for each binder, synthetic for an
\   instance-implicit one, else natural; whnf where no pi is left, a pi it
\   makes entered, else the type as it was), the binder kinds d's own,
\   then the nodes' records past whnf (an unknown one unsupported).
\ - lf-class? ( type -- class true outcome | false outcome ): isClass?
\   through isClassQuick?: the class (its declaration in the data's stage)
\   at the head past the pis; false for a head that is no class (a
\   constant no declaration has included, as Lean's getConstTemp?); where
\   Lean would go on to isClassExpensive? (a definition the transparency
\   may unfold, a let, a projection, a lambda head, an assigned
\   metavariable whose value's head is no constant) unsupported (plan S2,
\   with delta).
\ - lf-inst-unify ( type -- addr n outcome ): getUnify at reducible
\   transparency: the values whose keys may unify with type, in Lean's
\   order, as cells: an instance i (0 or more) or a left-out instance j
\   as j invert (below 0: lf-inst-left-out?). The root keys are those of
\   the data's values (lf-inst-classes makes them): a query whose root key
\   none has answers no values at once. A root's tree is built at its
\   first query (discr-tree.fs's builder), its values inserted in rank
\   order so that every child list is in Lean's stored order (§3.2),
\   after step 1 and then step 2 on each instance of the root (step 2:
\   its keys recomputed at default transparency in a new depth): they
\   must equal the record's, else invalid (error 113); a
\   record whose star covers a term the type gives (Lean saw a no_index
\   annotation, an mdata node the export drops) is unverified (error
\   114). The tree counts only once complete: a failure keeps none of it.
\   An unverified or left-out candidate answers unsupported only when a
\   search tries it (S1 §9). A star root key (a bare metavariable goal) is
\   unsupported: never an instance problem. The cells stay valid until the
\   next query (lf-inst-unify, lf-inst-candidates) or lf-inst-reset.
\ - lf-inst-candidates ( type -- addr n outcome ): getInstances: the goal
\   past its pis must be a class application (else invalid, error 110,
\   "type class instance expected"); getUnify; stably sorted by priority
\   (src/lib/sort.fs, as Lean's insertionSort), ascending; erased values
\   dropped. A search tries them from the last. Unsupported: a goal that
\   is or becomes a pi, a local instance of the class in the context
\   (FE1E §2.7; invalid when the context's view is not live). The cells
\   live as lf-inst-unify's.
\ - lf-default-instances ( class -- addr n outcome ): getDefaultInstances:
\   one cell per rank of the class's default instances, from rank 0 (Lean's
\   list, the most recent first): the default-instance record
\   (elab-default@), or a gap, lf-default-gap? ( v -- flag ), where none
\   is usable: the export lacks it (no record of that rank,
\   ELABORATION_DATA.md) or its step 3 could not finish. A caller that
\   reaches a gap answers unsupported. At most 65,536 cells (the
\   reader's elab-default-rank-most); they stay valid until the next
\   lf-default-instances or lf-inst-reset.
\ - lf-inst-priority ( v -- p ), lf-inst-left-out? ( v -- flag ),
\   lf-inst-verified? ( v -- flag ) (an instance whose class and keys were
\   checked equal; false for any other value), lf-inst-check ( i --
\   outcome ) (§4 steps 1-2 alone, nothing kept: ok, invalid on a
\   difference, else why it could not finish), lf-default-check ( j --
\   outcome ) (step 3 alone, for default instance j), lf-inst-checked# and
\   lf-inst-unverified# ( -- n ): the instances whose check is final, and
\   those of them unverified.
\ - lf-inst-error ( -- code ): the error code (src/author/errors.fs) the
\   last query or check set, 0 when it set none. Each starts at 0; an
\   answer that is not ok sets its code when it has one of the table's
\   own (none for a term or context view that is not live, a constant the
\   data's stage lacks, a rank the reader should have refused), and an ok
\   answer may leave 114 from a record it found unverified on the way.
\   Only a refusal's code (112, 113, 115, 116) refuses the data.
\   lf-inst-reset ( -- ) forgets the trees, checks and the pass (a new
\   read of the data does too).
\ Outcomes: ok; invalid as above; lf-meta-stuck from a query key (Meta
\ layer only); unsupported; exhausted; full when a slab cannot grow.
\ Untrusted. State: the record it (the last error, the counts, the
\ roots' pass or the refusal, the data's generation, the record checked
\ last, a key comparison's ends, the sort, and the tree, given back by
\ lf-inst-reset and the context's teardown) and the slabs it-status and
\ it-dstatus (per instance and default record: unchecked, class ok,
\ unverified or verified), it-ranked (a root's values by rank),
\ it-defaults (lf-default-instances' answer) and it-out (a query's
\ values), in the checker context (ADR 0009). Loads in decimal whatever
\ BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/sort.fs
require ../lib/bounds.fs
require ../author/errors.fs
require ./discr-keys.fs
require ./lctx-views.fs
require ./meta-must.fs
require ./telescope.fs
require ./discr-tree.fs

0 constant it-unchecked   1 constant it-class-ok   2 constant it-unverified
3 constant it-verified
1 constant it-passed      \ (it-pass) the roots made; 0: not yet; else a refusal's code
begin-structure /kcmp     \ a comparison of recorded keys with recomputed ones
  field: kc-d-end         \ the recorded keys' end
  field: kc-wide          \ true once a recorded star covered a term
end-structure
begin-structure /it
  field: it-error         \ the last error code, or 0
  field: it-checked       \ instances whose check is final
  field: it-unverified-n  \ of which unverified
  field: it-pass          \ lf-inst-classes: 0 not yet, it-passed, or a refusal's code
  field: it-data          \ the data's elab-generation the tables were made from
  field: it-blamed        \ the data declaration of the record checked last
  /kcmp +field it-kcmp
  /sorter +field it-sort-rec   \ getInstances' priority sort (lib/sort.fs)
  /dtree +field it-tree   \ the instance tree (discr-tree.fs), its roots the data's
end-structure
/it context-record: it
1 cells context-slab: it-status
1 cells context-slab: it-dstatus
1 cells context-slab: it-ranked
1 cells context-slab: it-defaults
1 cells context-slab: it-out
: it-dt ( -- tree ) it it-tree ;
:noname ( -- ) it-dt lf-dtree-free ; context-teardown

: lf-inst-reset ( -- )   \ tables of the data as it is now
  it-dt lf-dtree-free it-status slab-clear it-dstatus slab-clear it /it erase
  elab-generation it it-data ! ;
\ Tables of the data as it is: another read, or a reset of it
\ (elab-generation), forgets them before any query or count reads them.
: it-same-data ( -- ) elab-generation it it-data @ <> if lf-inst-reset then ;
: lf-inst-error ( -- code ) it it-error @ ;
: it-fail ( code -- outcome ) it it-error ! outcome-invalid ;
: it-no-error ( -- ) 0 it it-error ! ;   \ each query and check starts so
: lf-inst-checked# ( -- n ) it-same-data it it-checked @ ;
: lf-inst-unverified# ( -- n ) it-same-data it it-unverified-n @ ;
: lf-inst-left-out? ( v -- flag ) 0< ;
: lf-inst-priority ( v -- p )
  dup lf-inst-left-out? if invert elab-left-out@ 2drop else elab-instance@ nip nip then ;
: it-keys ( v -- k n ) dup lf-inst-left-out? if invert elab-left-out-keys else
  elab-instance-keys then ;
: it-root-key ( v -- k ) it-keys drop ;
: it-rank ( v -- rank )
  dup lf-inst-left-out? if invert elab-left-out@ drop nip else elab-instance-rank then ;
: it-erased? ( v -- flag )
  dup lf-inst-left-out? if invert elab-left-out@ nip nip elab-erased = else drop false
  then ;
\ Every value, as cells: the left-out ones (below 0), then the instances;
\ it-value gives the k-th of them, from 0.
: it-values# ( -- n ) elab-instance elab-count elab-left-out elab-count + ;
: it-value ( k -- v ) elab-left-out elab-count - ;
: it-cells ( outcome slab -- addr n outcome ) dup slab-base swap slab-count rot ;

\ ---- forallMetaTelescopeReducing over declaration d's type, its binder
\ kinds d's own (telescope.fs; the metavariables are not kept).
: it-body ( d -- body )
  0 over lf-menv-type rot ['] 2drop lf-forall-meta-telescope-reducing nip ;
: lf-inst-telescope ( d -- body outcome ) ['] it-body 1 1 lf-meta-catch ;

\ ---- isClass? by isClassQuick? (an undefined answer is unsupported).
: it-defn-temp? ( d -- flag )   \ getConstTemp? gives a definition
  dup lf-menv-kind lf-kind-definition <> if drop false exit then
  lf-defeq-mode dup lf-tr-all = swap lf-tr-default = or if drop true exit then
  lf-menv-status drop elab-reducible = ;
\ No class: getConstTemp? decides (none for a constant no declaration has;
\ a declaration that could not be decoded passes its outcome on).
: it-unknown ( d outcome -- false outcome )
  nip dup outcome-invalid = if drop outcome-ok then false swap ;
: it-not-class ( const -- false outcome )
  lf-meta-const-decl ok-then? 0= if -1 swap it-unknown exit then
  it-defn-temp? if false outcome-unsupported else false outcome-ok then ;
: it-class-of ( const -- d true | false )   \ its declaration, if a class
  lf-dt-const-decl 0= if false exit then
  dup elab-class-of if drop true else drop false then ;
: it-class-const ( const -- class true outcome | false outcome )
  dup it-class-of if nip true outcome-ok else it-not-class then ;
\ An application's head: a constant, an assigned metavariable's value's
\ constant head (else undefined), a lambda undefined; anything else none.
: it-mvar-head ( mvar -- class true outcome | false outcome )
  lf-mvar-value 0= if false outcome-ok exit then
  lf-meta-head lf-dt-const? if it-class-const else false outcome-unsupported then ;
: it-quick-head ( head -- class true outcome | false outcome )
  dup lf-term-tag@ case
    lf-tag-constant of it-class-const endof   lf-tag-mvar of it-mvar-head endof
    lf-tag-lam of drop false outcome-unsupported endof   >r drop false outcome-ok r>
    endcase ;
\ isClassQuick?'s answer by the tag past the pis: the head decides (an
\ application, a constant, a metavariable), undefined, or none (a bound
\ or free variable, a literal, a Sort, a lambda).
0 constant iq-none   1 constant iq-undef   2 constant iq-head
: it-quick-kind ( tag -- kind )
  case lf-tag-app of iq-head endof  lf-tag-constant of iq-head endof
    lf-tag-mvar of iq-head endof  lf-tag-let of iq-undef endof
    lf-tag-let-nondep of iq-undef endof  lf-tag-projection of iq-undef endof
    iq-none swap endcase ;
: lf-class? ( type -- class true outcome | false outcome )
  lf-meta-forall-body dup lf-term-tag@ it-quick-kind case
    iq-none of drop false outcome-ok endof
    iq-undef of drop false outcome-unsupported endof
    >r lf-meta-head it-quick-head r> endcase ;

\ ---- The checks (§4). A check runs xt ( body r -- outcome ) on record
\ r and the telescope of declaration d's type, in Lean's default
\ configuration, one metavariable depth deeper; the keys, marks and
\ metavariables it made are forgotten after.
: it-on-type ( r d xt -- outcome )
  >r lf-inst-telescope ok-then? if swap r> execute else nip r> drop then ;
: it-deeper ( r d xt -- outcome )
  false lf-mctx-depth{ ok-then? 0= if nip nip nip exit then
  >r ['] it-on-type lf-dt-scoped r> }lf-mctx-depth outcome-and ;
: it-at-default ( r d xt -- outcome )
  ['] it-deeper lf-meta-default lf-tr-default lf-meta-with ;
: it-decl ( i -- d outcome ) elab-instance@ 2drop lf-menv-of-data ;
: it-record-class ( i -- class ) elab-instance@ drop nip ;
: it-checked-by ( i xt -- outcome )
  over it-decl ok-then? 0= if nip nip exit then swap it-at-default ;
\ Step 1: isClass? of the body is the record's class (else error 112),
\ and the record's root key, already its class's constant, has the
\ body's arity (else it is filed under another root: error 115).
: it-class-of? ( body i -- flag outcome )
  swap lf-class? ok-then? 0= if nip false swap exit then
  if swap it-record-class = else drop false then outcome-ok ;
: it-root-arity? ( body i -- flag ) it-root-key elab-key-arity swap lf-meta-args# = ;
: it-class-verdict ( body i -- outcome )
  2dup it-class-of? ok-then? 0= if nip nip exit then
  0= if 2drop lfa-e-inst-class it-fail exit then
  it-root-arity? if outcome-ok else lfa-e-inst-root it-fail then ;
\ Step 2: the recorded keys against the recomputed: the same; wider, the
\ record has a star where the type gives a term (unverified, error
\ 114); or different (invalid, error 113). Both are one term (the reader
\ checks the record's, mkPath makes one), so a walk of the record's keys
\ that finds no difference ends both at once.
0 constant it-same   1 constant it-wider   2 constant it-differ
: it-kc ( -- kcmp ) it it-kcmp ;
: it-over? ( d c -- flag ) elab-key-star? 0= swap elab-key-star? and ;
: it-more? ( d c -- d c flag ) over it-kc kc-d-end @ < ;
: it-covered ( d c -- d' c' ) elab-term-end swap 1+ swap true it-kc kc-wide ! ;
: it-advance ( d c -- d' c' flag )
  2dup it-over? if it-covered true exit then
  2dup elab-key= dup if >r 1+ swap 1+ swap r> then ;
: it-walk-keys ( d c -- result )
  begin it-more? while it-advance 0= if 2drop it-differ exit then repeat
  2drop it-kc kc-wide @ if it-wider else it-same then ;
: it-compare ( kc nc i -- result )
  elab-instance-keys over + it-kc kc-d-end ! -rot drop false it-kc kc-wide !
  it-walk-keys ;
: it-path-result ( body i -- result outcome )
  swap lf-dt-path ok-then2? 0= if nip -1 swap exit then rot it-compare outcome-ok ;
: it-verdict ( result -- outcome )
  case it-same of outcome-ok endof
    it-wider of lfa-e-inst-wide it it-error ! outcome-unsupported endof
    lfa-e-inst-keys it-fail swap endcase ;
: it-keys-verdict ( body i -- outcome ) it-path-result ok-then? if it-verdict then ;
: it-both-verdict ( body i -- outcome )
  2dup it-class-verdict ok-then2? if it-keys-verdict then ;
: lf-inst-check ( i -- outcome ) it-no-error ['] it-both-verdict it-checked-by ;
\ Step 3: the head of a default instance's conclusion is its class.
: it-default-class ( j -- class ) elab-default@ 2drop ;
: it-head-class? ( body class -- flag )
  swap lf-meta-head lf-dt-const? if lf-dt-const-decl if = exit then then drop false ;
: it-default-verdict ( body j -- outcome )
  it-default-class it-head-class? if outcome-ok else lfa-e-default-class it-fail then ;
: it-default-decl ( j -- d outcome ) elab-default@ drop nip lf-menv-of-data ;
: lf-default-check ( j -- outcome )
  it-no-error dup it-default-decl ok-then? 0= if nip exit then
  ['] it-default-verdict it-at-default ;

\ ---- What the checks found, kept per record: only a final outcome (ok,
\ or unsupported: unverified) is kept and answered ok; any other is
\ answered as it is and the record stays as it was.
: it-final? ( outcome -- flag ) dup ok? swap outcome-unsupported = or ;
: it-status@ ( i -- s ) it-status slab-at @ ;
: it-dstatus@ ( j -- s ) it-dstatus slab-at @ ;
: it-tally ( s -- )
  dup it-class-ok = if drop exit then
  1 it it-checked +! it-unverified = negate it it-unverified-n +! ;
: it-new-status ( outcome s -- s' ) swap ok? if exit then drop it-unverified ;
: it-keep ( outcome s addr -- outcome )   \ s, or unverified, kept at addr when final
  rot dup it-final? 0= if nip nip exit then rot it-new-status swap ! outcome-ok ;
: it-record ( outcome i s -- outcome )   \ an instance's: the counts follow
  over >r swap it-status slab-at it-keep
  r> over ok? if it-status@ it-tally else drop then ;
: it-slab-ready ( n slab -- outcome )   \ n zeroed cells, once
  dup slab-count if 2drop outcome-ok exit then
  2dup slab-claim nip ok-then? 0= if nip exit then slab-base swap cells erase outcome-ok ;

\ ---- Each record checked when first needed (MATHLIB_FRONT.md §3): step
\ 1 by its root's build, step 3 by its class's default instances; the
\ record a check is about is blamed first (lf-inst-refused-decl).
: it-blame ( d -- ) it it-blamed ! ;
: it-root-class? ( i -- flag )   \ its root key is its recorded class's constant
  dup it-root-key swap it-record-class swap
  dup elab-key-tag elab-key-const = if elab-key-decl = else 2drop false then ;
: it-class-pass ( i -- outcome )
  dup it-status@ it-unchecked <> if drop outcome-ok exit then
  dup elab-instance@ 2drop it-blame
  dup it-root-class? 0= if drop lfa-e-inst-root it-fail exit then
  dup ['] it-class-verdict it-checked-by swap it-class-ok it-record ;
: it-default-pass ( j -- outcome )
  dup it-dstatus@ it-unchecked <> if drop outcome-ok exit then
  dup elab-default@ drop nip it-blame
  dup lf-default-check it-verified rot it-dstatus slab-at it-keep ;
: it-records-ready ( -- outcome )
  elab-instance elab-count it-status it-slab-ready
  dup ok? if drop elab-default elab-count it-dstatus it-slab-ready then ;
\ A refusal of the data, an invalid answer with a refusal's code (112,
\ 113, 115, 116), answers every later query the same until another read
\ or lf-inst-reset; any other invalid (no code: a term or context view
\ that is not live, below the table; or the 114 an unverified record
\ left) is the query's alone.
: it-refusal? ( code -- flag )
  dup lfa-e-inst-wide <> swap lfa-e-inst-class lfa-e-default-class 1+ within and ;
: it-refused ( outcome -- outcome )
  dup outcome-invalid = lf-inst-error it-refusal? and if lf-inst-error it it-pass ! then ;
: it-pass-keep ( outcome -- outcome )
  dup ok? if it-passed it it-pass ! exit then it-refused ;
\ Each query starts with no error code, and with tables of the data as it
\ is (it-same-data).
: it-query ( -- ) it-same-data it-no-error ;
: lf-inst-verified? ( v -- flag )
  it-same-data dup it-status slab-count index? if it-status@ it-verified = else drop false
  then ;
\ The refusal's code (0: none) and the record it refused.
: lf-inst-refusal ( -- code ) it-same-data it it-pass @ dup it-passed = if drop 0 then ;
: lf-inst-refused-decl ( -- d ) it it-blamed @ ;

\ ---- A root's tree (discr-tree.fs's builder): its values placed by rank,
\ step 1 for its instances, then step 2, then inserted in rank order, so
\ that every child list is Lean's stored order; nothing kept of a failure.
: it-grow-to ( n slab -- outcome )   \ at least n cells, the new ones -1
  tuck slab-count - dup 0> 0= if 2drop outcome-ok exit then
  2dup swap slab-claim ok-then? 0= if nip nip exit then
  rot slab-at swap cells -1 fill outcome-ok ;
: it-put ( v rank slab -- outcome )
  over 1+ over it-grow-to ok-then? 0= if nip nip exit then slab-at ! outcome-ok ;
: it-place ( v -- outcome ) dup it-rank it-ranked it-put ;
: it-root-of? ( v k -- flag ) swap it-root-key elab-key= ;
: it-counted ( n outcome -- n' outcome ) dup ok? if swap 1+ swap then ;
: it-gathered ( n idx k -- n' outcome )   \ value idx placed, and counted, when under k
  swap it-value tuck swap it-root-of? if it-place it-counted else drop outcome-ok then ;
\ The n values placed fill every rank (the reader refuses a gap, which
\ would read as left-out 0, and two values of one rank): else invalid.
: it-gapless ( n outcome -- outcome )
  ok-then? if it-ranked slab-count = flag>outcome then ;
: it-gather ( k -- k outcome )
  it-ranked slab-clear dup 0 it-values# rot ['] it-gathered ok-fold it-gapless ;
: it-ranked@ ( r -- v ) it-ranked slab-at @ ;
: it-keys-pass ( i -- outcome )
  dup it-status@ it-class-ok <> if drop outcome-ok exit then
  dup elab-instance@ 2drop it-blame
  dup ['] it-keys-verdict it-checked-by swap it-verified it-record ;
\ Step xt ( i -- outcome ) on each instance of the root's ranks.
: it-on-rank ( xt r -- xt outcome )
  it-ranked@ dup 0< if drop outcome-ok else over execute then ;
: it-ranks-pass ( xt -- outcome ) it-ranked slab-count ['] it-on-rank ok-each nip ;
: it-keys-ranks ( -- outcome ) ['] it-keys-pass it-ranks-pass ;
: it-root-checks ( -- outcome )   \ step 1 on every instance of the root, then step 2
  ['] it-class-pass it-ranks-pass ['] it-keys-ranks ok-and ;
: it-prepared ( k -- outcome ) it-gather nip ['] it-root-checks ok-and ;
: it-insert-rank ( r -- outcome ) it-ranked@ dup it-keys rot it-dt lf-dtree-insert ;
: it-insert-ranked ( -- outcome ) it-ranked slab-count ['] it-insert-rank ok-each ;
: it-root-build ( r tree -- outcome )
  lf-dtree-root-key it-prepared it-refused ['] it-insert-ranked ok-and ;

\ ---- The roots: every value's root key, made once per data read
\ (lf-inst-classes), by lib/htab.fs in the tree (discr-tree.fs).
: it-value-root ( k -- outcome ) it-value it-root-key it-dt lf-dtree-root-add nip ;
: it-roots-made ( -- outcome ) it-values# ['] it-value-root ok-each ;
: it-tree-ready ( -- outcome )
  it-dt lf-dtree-ready dup ok? if ['] it-root-build it-dt lf-dtree-builder! then ;
: it-pass-run ( -- outcome )
  it-records-ready ['] it-tree-ready ok-and ['] it-roots-made ok-and ;
: lf-inst-classes ( -- outcome )
  it-query it it-pass @ ?dup 0= if it-pass-run it-pass-keep exit then
  dup it-passed = if drop outcome-ok else it-fail then ;

\ ---- getUnify (discr-tree.fs), at reducible transparency.
: it-unify ( type -- outcome ) it-dt it-out lf-dtree-unify ;
: lf-inst-unify ( type -- addr n outcome )
  it-out slab-clear lf-inst-classes ok-then?
  if ['] it-unify lf-tr-reducible lf-meta-at then it-out it-cells ;

\ ---- getInstances.
: it-goal-body ( type -- body outcome )
  dup lf-term-pi? if drop -1 outcome-unsupported exit then
  dup lf-meta-whnf ok-then? 0= if nip no-result exit then
  lf-term-pi? if drop -1 outcome-unsupported else outcome-ok then ;
: it-local? ( name view i -- flag ) lf-view-local lf-local-class = ;
\ Unsupported when the context has a local instance of the class.
\ The class's name in the context's names (fed or run mode).
: it-class-name ( class -- name outcome )
  lf-menv-of-data ok-then? if lf-menv-name outcome-ok then ;
: it-local-free ( class -- outcome )
  it-class-name ok-then? 0= if exit then
  lf-mctx-view dup lf-view-valid? 0= if 2drop outcome-invalid exit then
  dup lf-view-count 0 ?do 2dup i it-local? if 2drop outcome-unsupported unloop exit then
  loop 2drop outcome-ok ;
\ Lean's insertionSort by priority (SynthInstance.lean:214), ascending:
\ lib/sort.fs sorts stably, so equal priorities keep getUnify's order.
: it-prio-at ( a-addr -- p ) @ lf-inst-priority ;
: it-sorter ( -- sorter ) it it-sort-rec ;
: it-sorter-ready ( -- outcome )
  1 cells ['] sort-signed it-sorter sorter-init ['] it-prio-at it-sorter sorter-key! ;
: it-sorted ( -- outcome ) it-out slab-base it-out slab-count it-sorter sort-records ;
: it-sort ( -- outcome ) it-sorter-ready ['] it-sorted ok-and ;
: it-kept ( w v -- w' ) dup it-erased? if drop else over it-out slab-at ! 1+ then ;
: it-drop-erased ( -- )
  0 it-out slab-count 0 ?do i it-out slab-at @ it-kept loop
  it-out slab-cut ;
: it-class-body ( type -- body class outcome )
  it-goal-body ok-then? 0= if -1 -1 rot exit then
  dup lf-class? ok-then? 0= if nip -1 -1 rot exit then
  if outcome-ok else lfa-e-not-class it-fail -1 swap then ;
: it-candidates ( type -- outcome )
  it-class-body ok-then2? 0= if exit then
  it-local-free dup ok? 0= if nip exit then drop
  lf-inst-unify nip nip dup ok? if drop it-sort dup ok? if it-drop-erased then then ;
: lf-inst-candidates ( type -- addr n outcome )
  it-out slab-clear lf-inst-classes ok-then? if it-candidates then it-out it-cells ;

\ ---- getDefaultInstances: the class's default instances by rank, each
\ checked (step 3) before it is placed.
-1 constant it-gap
: lf-default-gap? ( v -- flag ) 0< ;
: it-dvalue ( j -- v ) dup it-dstatus@ it-verified <> if drop it-gap then ;
: it-dplace ( j -- outcome ) dup it-dvalue swap elab-default-rank it-defaults it-put ;
: it-default-of? ( class j -- flag ) it-default-class = ;
: it-default-one ( class j -- class outcome )
  2dup it-default-of? if dup it-default-pass ok-then? if it-dplace then
  else drop outcome-ok then ;
: it-defaults-of ( class -- outcome )
  elab-default elab-count ['] it-default-one ok-each nip it-refused ;
: lf-default-instances ( class -- addr n outcome )
  it-defaults slab-clear lf-inst-classes ok-then? if it-defaults-of then
  it-defaults it-cells ;

base !   \ the BASE this file was loaded with
