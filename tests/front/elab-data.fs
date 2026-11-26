\ Unit tests of src/front/elab-data.fs and src/front/elab-keys.fs (plan
\ rows FE1d and FE1e1), the words around the reader;
\ tests/front/test_elab_data.py runs every damaged file through the
\ command line. Here: the key store's words on keys made by hand (each
\ form, equality, hash, one term, full when the heap has no room); the
\ slice's format-3 data read against the init slice's stage, every kind
\ of record read back by number and by declaration (instances with their
\ keys and ranks, left-out instances with foreign keys and literals,
\ classes, tags, matchers, projections, Nat.add's smart-unfolding body
\ node by node); the synthetic eliminators found by kind and type, and
\ the fixture's nodes of every other form, one naming a structure the
\ slice lacks (the body foreign); a refused read keeps nothing (every table empty,
\ nothing loaded), a later read works again and replaces the earlier one;
\ a missing file, a call during a read, a sealed stage and a name two
\ declarations of the stage have (error 13) refused; every allocation
\ that fails gives full or ok, never anything else, and leaks no heap
\ block; the reader and its JSON view give back their blocks after every
\ read; the default-rank limit; each read and reset a new generation.
\ Loaded under HEX: loading must not depend on BASE, and must leave
\ BASE as it found it.
include ../support/tester.fs
include ../support/heap-watch.fs
hex require ../../src/front/elab-data.fs base @ decimal constant base-after-load

T{ base-after-load elab-kinds elab-instance-reducible elab-tag-brec-on -> 16 11 4 6 }T

\ ---- The key store, on keys made by hand (it is empty before any read).
: new-key ( tag -- k ) elab-key-new drop ;
: text-key ( c-addr u tag -- k )
  new-key dup elab-key-text-start >r dup elab-text-room drop swap move r@ elab-key-text-end r> ;
: const-key ( d n -- k ) elab-key-const new-key tuck elab-key-arity! tuck elab-key-ref! ;
T{ elab-keys# elab-key-star elab-key-new -> 0 0 outcome-ok }T
T{ 0 elab-key-tag 0 elab-key-arity 0 elab-key-text nip -> elab-key-star 0 0 }T
T{ elab-key-arrow new-key elab-key-arity elab-key-other new-key elab-key-arity -> 1 0 }T
T{ 7 2 const-key dup elab-key-decl over elab-key-arity rot elab-key-tag -> 7 2 elab-key-const }T
T{ elab-key-proj new-key 9 over elab-key-ref! 3 over elab-key-idx! 2 over elab-key-arity!
   dup elab-key-arity over elab-key-idx rot elab-key-decl -> 3 3 9 }T
T{ s" 18446744073709551616" elab-key-lit text-key elab-key-text s" 18446744073709551616"
   compare -> 0 }T
T{ s" str" elab-key-str text-key dup elab-key-text nip swap elab-key-arity -> 3 0 }T
\ Equality: tags, arity fields, then declarations and fields or texts.
: same? ( k1 k2 -- flag ) elab-key= ;
T{ 7 2 const-key 7 2 const-key 2dup same? -rot elab-key-hash swap elab-key-hash = -> true true }T
T{ 7 2 const-key 7 1 const-key same? 7 2 const-key 8 2 const-key same? -> false false }T
T{ s" 5" elab-key-lit text-key s" 5" elab-key-lit text-key same? -> true }T
T{ s" 5" elab-key-lit text-key s" 5" elab-key-str text-key same? -> false }T
T{ s" 5" elab-key-lit text-key s" 6" elab-key-lit text-key same? -> false }T
T{ s" ab" elab-key-foreign text-key 1 over elab-key-arity! s" ab" elab-key-foreign text-key
   1 over elab-key-arity! 2dup same? -rot elab-key-hash swap elab-key-hash = -> true true }T
T{ s" ab" elab-key-foreign text-key s" ab" elab-key-foreign text-key 1 over elab-key-arity!
   same? -> false }T
T{ elab-key-star new-key elab-key-star new-key same? elab-key-star new-key elab-key-other new-key same?
   -> true false }T
\ One term: OfNat Nat * is one, OfNat Nat is not, OfNat Nat * * is two;
\ arrow and a projection take one term more than their arity field.
: path ( -- k ) elab-keys# ;
T{ path 7 2 const-key drop 8 0 const-key drop elab-key-star new-key drop 3 elab-one-term? -> true }T
T{ path 7 2 const-key drop 8 0 const-key drop 2 elab-one-term? -> false }T
T{ path 7 2 const-key drop 8 0 const-key drop elab-key-star new-key elab-key-star new-key 2drop
   4 elab-one-term? -> false }T
T{ path 0 elab-one-term? path elab-key-arrow new-key drop 1 elab-one-term? -> false false }T
T{ path elab-key-arrow new-key drop elab-key-star new-key drop 2 elab-one-term? -> true }T
T{ path elab-key-proj new-key 0 over elab-key-arity! drop elab-key-star new-key drop 2 elab-one-term?
   -> true }T
\ Full when the heap has no room (in a new context, whose slabs have no
\ block yet): no key, no text, the outcome full, no block kept.
: fresh ( -- context ) context-new throw dup context-use 1 heap-refusals ! ;
: back ( context -- ) 0 heap-refusals ! context-main context-use context-free throw ;
T{ live-blocks @ fresh elab-key-star elab-key-new rot back live-blocks @ 3 roll -
   -> -1 outcome-full 0 }T
T{ fresh 4 elab-text-room rot back -> -1 outcome-full }T
T{ elab-keys-clear elab-keys# -> 0 }T

\ ---- The slice's data.
create lib /stage allot
create sealed /stage allot
create zero-sha 32 allot  zero-sha 32 erase
: slice ( -- c-addr u ) s" tests/author/init-slice.ndjson" ;
: good ( -- c-addr u ) s" tests/front/init-slice.elab.ndjson" ;
: elims ( -- c-addr u ) s" tests/front/eliminators.elab.ndjson" ;
: digest ( -- sha ) lib stage-manifest manifest-digest ;
T{ 12 lib stage-init slice lib stage-read -> outcome-ok outcome-ok }T

\ Declarations of the slice by name, looked up in its tier.
: part ( n c-addr u -- n' ) lib stage-tier name-seek-str drop ;
: decl ( n -- d ) lib stage-find drop ;
: top ( c-addr u -- d ) 0 -rot part decl ;
: nat ( c-addr u -- d ) 0 s" Nat" part -rot part decl ;
: dotted ( c-addr1 u1 c-addr2 u2 -- d ) 2swap 0 -rot part -rot part decl ;
: why? ( c-addr u -- flag ) elab-error-why compare 0= ;
: counts ( -- n1 .. n10 ) elab-binders 0 do i elab-count loop ;   \ format 3's kinds

\ Before any read: nothing loaded, no eliminator found (the table is made
\ by the first read), nothing failed.
T{ elab-loaded? counts s" Nat" top elab-induction elab-eliminator-for
   -> false 0 0 0 0 0 0 0 0 0 0 false }T
T{ elab-error s" none" compare -> 0 0 }T

\ The slice's data: 3 instances, 2 default instances, 18 reducibility
\ statuses, no eliminator, 54 instances left out, 3 classes, 10 tags, 4
\ matchers, 3 projections and 1 smart-unfolding body; nothing failed.
T{ good lib digest elab-read elab-loaded? counts
   -> outcome-ok true 3 2 18 0 54 3 10 4 3 1 }T
\ Read against lib, not against another stage.
T{ lib elab-read-against? sealed elab-read-against? 0 elab-read-against? -> true false false }T
T{ elab-error-line s" none" why? -> 0 true }T
T{ 0 elab-instance@ -> s" instAddNat" top s" Add" top 1000 }T
T{ 2 elab-instance@ -> s" instOfNatNat" top s" OfNat" top 1000 }T
T{ 0 elab-instance-order nip 1 elab-instance-order swap @ -> 0 1 1 }T
T{ s" instHAdd" top elab-instance-of s" Nat" top elab-instance-of -> 1 true false }T
T{ 0 elab-default@ -> s" HAdd" top s" instHAdd" top 1000 }T
T{ 1 elab-default@ -> s" OfNat" top s" instOfNatNat" top 100 }T
T{ 0 elab-default-rank 1 elab-default-rank -> 0 0 }T
T{ s" instAddNat" top elab-status s" Id" top elab-status s" outParam" top elab-status
   -> elab-instance-reducible elab-implicit-reducible elab-reducible }T
T{ s" Nat" top elab-status s" succ" nat elab-status -> elab-semireducible elab-semireducible }T
T{ s" Nat" top elab-induction elab-eliminator-for -> false }T

\ Instances' keys and ranks: instAddNat is Add Nat, rank 17 among Add's
\ values; instHAdd is HAdd * * *, rank 0; instOfNatNat OfNat Nat *, 15.
: key@ ( k -- tag arity d ) dup elab-key-tag over elab-key-arity rot elab-key-decl ;
T{ 0 elab-instance-keys nip 1 elab-instance-keys nip 2 elab-instance-keys nip -> 2 4 3 }T
T{ 0 elab-instance-rank 1 elab-instance-rank 2 elab-instance-rank -> 17 0 15 }T
T{ 0 elab-instance-keys drop key@ -> elab-key-const 1 s" Add" top }T
T{ 0 elab-instance-keys drop 1+ key@ -> elab-key-const 0 s" Nat" top }T
T{ 1 elab-instance-keys drop 3 + elab-key-tag 2 elab-instance-keys drop 2 + elab-key-tag
   -> elab-key-star elab-key-star }T
T{ 0 elab-instance-keys elab-one-term? 1 elab-instance-keys elab-one-term? -> true true }T
T{ 0 elab-instance-keys drop 1+ 2 elab-instance-keys drop 1+ elab-key= -> true }T

\ Left out: 0 is Lean.Grind.AddCommMonoid.toAdd, Add *, rank 0, priority
\ 100; 2 is Dyadic.instAdd, Add Dyadic, Dyadic foreign (s, 6, Dyadic);
\ 26 is Zero.toOfNat0, OfNat * 0, with the literal 0; 28 is
\ Dyadic.instOfNat, whose Dyadic equals 2's.
: left-key ( j i -- k ) swap elab-left-out-keys drop + ;
T{ 0 elab-left-out@ 0 elab-left-out-keys nip -> 100 0 elab-not-exported 2 }T
T{ 0 0 left-key 0 elab-instance-keys drop elab-key= 0 1 left-key elab-key-tag
   -> true elab-key-star }T
T{ 2 1 left-key dup elab-key-tag swap elab-key-arity -> elab-key-foreign 0 }T
T{ 2 1 left-key elab-key-text nip 2 1 left-key elab-key-text drop u32-le@ -> 14 0 }T
T{ 2 1 left-key elab-key-text drop 4 + u32-le@ 2 1 left-key elab-key-text 8 /string s" Dyadic" compare
   -> 6 0 }T
T{ 2 1 left-key 28 1 left-key elab-key= 2 1 left-key 4 1 left-key elab-key= -> true false }T
T{ 26 2 left-key dup elab-key-tag swap elab-key-text s" 0" compare -> elab-key-lit 0 }T
T{ 26 elab-left-out@ -> 300 1 elab-not-exported }T

\ Classes: Add (0), HAdd (1, out-parameter 2 and out-level 2), OfNat (2).
T{ s" Add" top elab-class-of s" HAdd" top elab-class-of s" Nat" top elab-class-of
   -> 0 true 1 true false }T
\ Counts first, so that a wrong span fails here and is never read.
T{ 1 elab-class-out-params nip 1 elab-class-out-levels nip 2 elab-class-out-params nip
   2 elab-class-out-levels nip -> 1 1 0 0 }T
T{ 1 elab-class@ 1 elab-class-out-params drop @ 1 elab-class-out-levels drop @
   -> s" HAdd" top 2 2 }T
T{ s" instAddNat" top elab-class-of -> false }T

\ Tags.
T{ s" casesOn" nat elab-tag-cases-on elab-tagged? s" casesOn" nat elab-tag-aux-recursor
   elab-tagged? s" casesOn" nat elab-tag-rec-on elab-tagged? -> true true false }T
T{ s" below" nat elab-tag-aux-recursor elab-tagged? s" brecOn" nat elab-tag-brec-on
   elab-tagged? s" add" nat elab-tag-as-elim elab-tagged? -> true true false }T
T{ s" add" nat elab-tag-match-pattern elab-tagged? s" casesOn" nat elab-tag-match-pattern
   elab-tagged? -> true false }T

\ Matchers: Nat.add.match_1 (0): no parameter, two discriminants, its
\ elimination universe parameter 0, alternatives of 1 and 2 fields;
\ Nat.zero_add's private matcher (3): Prop only, its first alternative a
\ Unit thunk.
: add-match ( -- d ) 0 s" Nat" part s" add" part s" match_1" part decl ;
T{ add-match elab-matcher-of -> 0 true }T
T{ 0 elab-matcher@ 0 elab-matcher-elim -> add-match 0 2 0 true }T
T{ 0 elab-matcher-alts nip 0 elab-matcher-alts drop elab-alt@ -> 2 1 0 false }T
T{ 0 elab-matcher-alts drop 1+ elab-alt@ -> 2 0 false }T
T{ 3 elab-matcher-elim 3 elab-matcher-alts drop elab-alt@ -> false 0 0 true }T
T{ s" Nat" top elab-matcher-of -> false }T

\ Projections: Add.add (0) of Add.mk, 1 parameter, field 0, a class.
T{ s" Add" s" add" dotted elab-projection-of -> 0 true }T
T{ 0 elab-projection@ 0 elab-projection-class? 0 elab-projection-decl
   -> s" Add" s" mk" dotted 1 0 true s" Add" s" add" dotted }T
T{ 1 elab-projection@ 2drop -> s" HAdd" s" mk" dotted }T
T{ s" instHAdd" top elab-projection-of -> false }T

\ Smart-unfolding bodies: Nat.add's (0), recursion argument 1, root node
\ 23 of its 24: fun x y => [sunfoldMatch] Nat.add.match_1 (fun _ _ =>
\ Nat) x y (fun a => [sunfoldMatchAlt] a) (fun a b => [sunfoldMatchAlt]
\ Nat.succ (Nat.add a b)), every name the slice's.
T{ s" add" nat elab-sunfold-of s" Nat" top elab-sunfold-of -> 0 true false }T
T{ 0 elab-sunfold-decl 0 elab-sunfold-value 0 elab-sunfold-rec-arg 0 elab-sunfold-foreign?
   -> s" add" nat 23 1 true false }T
T{ 23 elab-node-kind 23 elab-node-b 23 elab-node-c 23 elab-node-d -> elab-node-lam 0 22 0 }T
T{ 1 elab-node-kind 1 elab-node-a 1 elab-node-levels nip -> elab-node-const add-match 1 }T
T{ 1 elab-node-levels drop @ dup elab-level-kind swap elab-level-a elab-level-kind
   -> elab-level-succ elab-level-zero }T
T{ 21 elab-node-kind 21 elab-node-a 21 elab-node-c -> elab-node-mdata elab-sunfold-match 20 }T
T{ 9 elab-node-a 5 elab-node-kind 5 elab-node-a -> elab-sunfold-match-alt elab-node-bvar 1 }T
T{ 4 elab-node-kind 4 elab-node-a 4 elab-node-b 12 elab-node-a -> elab-node-app 1 3 s" succ" nat }T
\ A binder's name is a key of its parts, as a foreign key's: a is 0, 1, "a".
T{ 10 elab-node-a dup elab-key-tag swap elab-key-text nip -> elab-key-foreign 9 }T
T{ 10 elab-node-a elab-key-text 8 /string s" a" compare -> 0 }T
\ Loose bound variables, 1 + the largest: none at the root.
T{ 23 ed-loose 22 ed-loose 21 ed-loose 19 ed-loose 5 ed-loose -> 0 1 2 0 2 }T

\ The synthetic eliminators (test_elab_data.py writes them): one per
\ kind and type list; a key of two types is found by neither of them alone.
T{ elims lib digest elab-read counts -> outcome-ok 3 2 18 4 54 3 10 4 3 1 }T
T{ s" Nat" top elab-induction elab-eliminator-for -> 0 true }T
T{ 0 elab-eliminator@ -> elab-induction s" rec" nat }T
T{ s" Nat" top elab-cases elab-eliminator-for over elab-eliminator@ -> 1 true elab-cases
   s" casesOn" nat }T
T{ s" And" top elab-induction elab-eliminator-for s" And" top elab-cases elab-eliminator-for
   -> 2 true false }T
T{ 3 elab-eliminator-types nip 3 elab-eliminator-types drop 1 cells + @ -> 2 s" Nat" top }T
T{ s" Eq" top elab-induction elab-eliminator-for -> false }T
\ The fixture's BitVec.instAdd (left out 20) has a projection of BitVec,
\ which the slice lacks: a foreign key of Key.arity 1 whose text is 2, the
\ field 0 and BitVec's name; BitVec.instOfNat (44) has the constant
\ BitVec, a foreign key of arity 1 too: the two differ.
T{ 20 1 left-key dup elab-key-tag over elab-key-arity rot elab-key-text nip
   -> elab-key-foreign 1 22 }T
T{ 20 1 left-key elab-key-text drop dup u32-le@ swap 4 + u32-le@ -> 2 0 }T
T{ 20 1 left-key elab-key-text 16 /string s" BitVec" compare -> 0 }T
T{ 44 1 left-key dup elab-key-arity swap elab-key-text nip -> 1 14 }T
T{ 20 1 left-key 44 1 left-key elab-key= -> false }T
\ The fixture's Nat.add body: after its root, nodes 24-32 of every other
\ form; 29 projects Prod, which the slice lacks, so the body is foreign.
T{ 0 elab-sunfold-foreign? 0 elab-sunfold-value -> true 23 }T
T{ 0 elab-sunfold-inert? 0 elab-sunfold-usable? -> false false }T
T{ 24 elab-node-kind 24 elab-node-a elab-level-kind -> elab-node-sort elab-level-succ }T
T{ 25 elab-node-kind 25 elab-node-b 25 elab-node-c 25 elab-node-d
   -> elab-node-forall 24 0 3 }T
T{ 25 elab-node-a elab-key-text nip -> 0 }T
T{ 26 elab-node-kind 26 elab-node-b 26 elab-node-c 26 elab-node-d 31 elab-node-kind
   -> elab-node-have 0 7 5 elab-node-let }T
T{ 27 elab-node-kind 27 elab-node-a elab-key-text s" 18446744073709551616" compare
   -> elab-node-lit 0 }T
T{ 28 elab-node-kind 28 elab-node-a elab-key-text s" ab" compare -> elab-node-str 0 }T
T{ 29 elab-node-kind 29 elab-node-a 29 elab-node-b 29 elab-node-c -> elab-node-proj -1 1 0 }T
T{ 32 elab-node-a 32 elab-node-c 30 elab-node-a 30 elab-node-c
   -> s" Nat" top 26 elab-borrowed 27 }T
T{ 24 ed-loose 25 ed-loose 26 ed-loose 32 ed-loose -> 0 0 1 1 }T
\ Its levels max 0 1 and imax 1 0 (levels 2 and 3), the sorts of 33, 34.
T{ 33 elab-node-a dup elab-level-kind over elab-level-a rot elab-level-b
   -> elab-level-max 0 1 }T
T{ 34 elab-node-a dup elab-level-kind over elab-level-a rot elab-level-b
   -> elab-level-imax 1 0 }T

\ Format 3.1 (MATHLIB_FRONT.md O1, O2; test_elab_data.py writes the
\ fixture): Nat.add's body with an inert node of each kind after its root
\ (24-26) and a lambda with an anonymous binder (27): read, the body inert
\ and not usable, not foreign; an inert node an mdata of elab-inert around
\ its term. instHAdd a default instance of HAdd at ranks 0 and 1: both kept.
\ Format 3.2 (plan FE1c-bk; test_elab_data.py writes the fixture): Lean's
\ binder kinds of Nat.add (1 0) and Nat.rec (10, 0, 010, 0) read back, the
\ domain of a binder beyond them none, a declaration without a record none.
: v32 ( -- c-addr u ) s" tests/front/format32.elab.ndjson" ;
: kinds@ ( d -- k0 .. kn-1 n ) elab-binder-kinds-of drop elab-binder-kinds dup >r
  cells bounds ?do i @ 1 cells +loop r> ;
: domain@ ( d k -- k0 .. kn-1 n )
  swap elab-binder-kinds-of drop swap elab-binder-domain dup >r cells bounds ?do i @ 1 cells
  +loop r> ;
T{ v32 lib digest elab-read counts elab-binders elab-count
   -> outcome-ok 3 2 18 0 54 3 10 4 3 1 2 }T
T{ s" add" nat kinds@ s" rec" nat kinds@ -> 1 0 2 1 0 0 0 4 }T
T{ s" rec" nat 0 domain@ s" rec" nat 2 domain@ s" rec" nat 1 domain@ s" rec" nat 4 domain@
   -> 0 1 1 0 2 0 0 }T
T{ s" add" nat elab-binder-kinds-of nip s" Nat" top elab-binder-kinds-of
   0 elab-binder-decl s" add" nat = -> true false true }T
\ A later read of format 3 has none.
T{ good lib digest elab-read s" add" nat elab-binder-kinds-of elab-binders elab-count
   -> outcome-ok false 0 }T
: v31 ( -- c-addr u ) s" tests/front/format31.elab.ndjson" ;
T{ v31 lib digest elab-read counts -> outcome-ok 3 3 18 0 54 3 10 4 3 1 }T
T{ 0 elab-sunfold-inert? 0 elab-sunfold-foreign? 0 elab-sunfold-usable? 0 elab-sunfold-value
   -> true false false 23 }T
T{ 24 elab-node-kind 24 elab-node-a 24 elab-node-c 25 elab-node-c 26 elab-node-a
   -> elab-node-mdata elab-inert 0 24 elab-inert }T
T{ 25 ed-loose 27 elab-node-kind 27 elab-node-a elab-key-text nip -> 0 elab-node-lam 0 }T
T{ 0 elab-default@ 0 elab-default-rank -> s" HAdd" top s" instHAdd" top 1000 0 }T
T{ 1 elab-default@ 1 elab-default-rank -> s" HAdd" top s" instHAdd" top 1000 1 }T
T{ 2 elab-default@ 2drop -> s" OfNat" top }T
\ A format-3 read after it: the version and every body usable again.
T{ elab elab-v31 @ good lib digest elab-read elab elab-v31 @ 0 elab-sunfold-usable?
   -> true outcome-ok false true }T

\ A refused read keeps nothing; the next read works and replaces it.
: forgotten? ( d -- flag )
  dup elab-status 0= over elab-instance-of 0= and over elab-class-of 0= and
  over elab-matcher-of 0= and over elab-sunfold-of 0= and swap elab-projection-of 0= and ;
: empty? ( -- flag )
  elab-loaded? 0= counts + + + + + + + + + 0= and s" instAddNat" top forgotten? and
  s" add" nat forgotten? and
  s" Add" top forgotten? and add-match forgotten? and s" casesOn" nat elab-tag-cases-on elab-tagged? 0=
  and s" Nat" top elab-induction elab-eliminator-for 0= and elab-keys# 0= and ;
T{ elims lib zero-sha elab-read empty? elab-error-line s" elaboration data of another export"
   why? elab-error-code -> outcome-invalid true 1 true 9 }T
T{ lib elab-read-against? -> false }T
T{ good lib digest elab-read counts elab-error-code -> outcome-ok 3 2 18 0 54 3 10 4 3 1 0 }T
\ M6: a binding (elab-bind!) holds for the next read only: bound to other
\ records that read is refused (error 39), the next, unbound, works.
: other-records ( -- c-addr u )
  s" 0000000000000000000000000000000000000000000000000000000000000000" ;
T{ other-records elab-bind! good lib digest elab-read elab-error-code
   good lib digest elab-read -> outcome-invalid 39 outcome-ok }T
\ Refused after its last line: none of the records it read stays.
T{ s" tests/front/cut-off.elab.ndjson" lib digest elab-read empty? elab-error-line
   s" records differ in number from the header" why? elab-error-code
   -> outcome-invalid true 102 true 20 }T
\ Every code has its text, the first and the last as documented.
T{ 0 ed-message s" none" compare 1 ed-message s" file missing or unreadable" compare
   38 ed-message s" a record kind this reader does not read yet" compare
   45 ed-message s" an annotation this reader does not know" compare
   46 ed-message s" binder kinds named twice" compare
   48 ed-message s" congruence lemmas out of their function's order" compare
   49 ed-message s" a function's realized congruence theorem given twice" compare
   50 ed-message s" a simp lemma's rfl flag not its proof's defeq tag" compare
   52 ed-message s" a simp set other than the default one, or given twice" compare 53 ed-message nip
   -> 0 0 0 0 0 0 0 0 0 0 }T
T{ 16 ed-message s" a default instance of two classes" compare -> 0 }T
\ elab-unhashed: error 26 at line 0, the outcome kept, nothing loaded.
T{ good lib digest elab-read outcome-full elab-unhashed elab-error-code elab-error-line
   empty? -> outcome-ok outcome-full 26 0 true }T
T{ elims lib digest elab-read good lib digest elab-read counts
   -> outcome-ok outcome-ok 3 2 18 0 54 3 10 4 3 1 }T
T{ elab-reset empty? -> true }T
T{ s" tests/front/no-such.ndjson" lib digest elab-read elab-error-line
   s" file missing or unreadable" why? empty? -> outcome-invalid 0 true true }T

\ A read while one is in progress is refused and changes nothing loaded.
T{ good lib digest elab-read -> outcome-ok }T
T{ true elab elab-reading ! good lib digest elab-read s" a read in progress" why?
   false elab elab-reading ! counts -> outcome-invalid true 3 2 18 0 54 3 10 4 3 1 }T

\ A sealed stage: its names cannot be looked up; refused, nothing kept.
T{ 12 sealed stage-init slice sealed stage-load -> outcome-ok outcome-ok }T
T{ good sealed sealed stage-manifest manifest-digest elab-read empty?
   -> outcome-invalid true }T
T{ s" the library's stage is sealed: its names cannot be looked up" why? -> true }T

\ A name two declarations have (error 13): the slice read, then one more
\ read into the same stage (stage-extend, stage-produce) declaring
\ instAddNat again, as an axiom of type Prop; the data's first record
\ naming it (an instance, line 5) is refused.
create twice /stage allot
create line-buf 256 allot
: produce ( c-addr u -- outcome ) tuck line-buf swap move line-buf swap twice stage-line ;
\ The pinned metadata line, built in line-buf piece by piece.
: +line ( offset c-addr u -- offset' ) rot 2dup + >r line-buf + swap move r> ;
: meta-line ( -- c-addr u )
  0 s\" {\"meta\":{\"exporter\":{\"name\":\"lean4export\",\"version\":\"3.1.0\"}," +line
  s\" \"format\":{\"version\":\"3.1.0\"},\"lean\":{\"githash\":" +line
  s\" \"eb6cafb7290e8bd5f2937522d8d804f58f02bafc\",\"version\":\"4.35.0\"}}}" +line
  line-buf swap ;
: produced? ( outcome -- flag ) ok? ;
: second-decl ( -- outcome )
  meta-line twice stage-line dup produced? 0= if exit then drop
  s\" {\"in\":1,\"str\":{\"pre\":0,\"str\":\"instAddNat\"}}" produce
  dup produced? 0= if exit then drop
  s\" {\"ie\":0,\"sort\":0}" produce dup produced? 0= if exit then drop
  s\" {\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":0}}" produce ;
T{ 12 twice stage-init slice twice stage-read twice stage-extend
   ' second-decl twice stage-produce -> outcome-ok outcome-ok outcome-ok outcome-ok }T
T{ good twice digest elab-read elab-error-line elab-error-code empty?
   -> outcome-invalid 5 13 true }T
T{ twice stage-free -> }T

\ Resources: the k-th allocation refused, for every k until a read needs
\ none, each in a new context, whose tables all start empty: full or ok,
\ never another outcome, and no block kept once the context is freed;
\ then the next read in the main context is ok.
: blocks ( -- n ) live-blocks @ ;
defer refusal-data ( -- c-addr u )   ' elims is refusal-data
: refused-read ( k -- outcome )
  heap-refusals ! refusal-data lib digest elab-read 0 heap-refusals ! ;
: full-or-ok? ( outcome -- flag ) dup ok? swap outcome-full = or ;
: fresh-read ( k -- outcome flag )
  blocks >r context-new throw dup context-use swap refused-read
  context-main context-use swap context-free throw blocks r> = ;
\ Add one read's results: how many were full, and whether all were well.
: tally ( fulls flag outcome kept? -- fulls' flag' )
  >r dup full-or-ok? r> and rot and swap outcome-full = rot swap - swap ;
: refusals ( -- fulls flag ) 0 true 160 1 do i fresh-read tally loop ;
T{ refusals swap 0> -> true true }T
T{ elims lib digest elab-read counts -> outcome-ok 3 2 18 4 54 3 10 4 3 1 }T
\ The same for the format-3.2 fixture: its binder kinds' records and
\ domain spans refused in turn too (plan FE1c-bk).
' v32 is refusal-data
T{ refusals swap 0> -> true true }T
' elims is refusal-data

\ The reader and the view give their blocks back after every read, ok or
\ not; the data's slabs and tables keep theirs until the context goes.
T{ blocks good lib digest elab-read drop blocks = -> true }T
T{ blocks elims lib zero-sha elab-read drop blocks = -> true }T

\ A default instance's rank is at most 65535 (error 40, invalid; every
\ refused file is in test_elab_data.py), an earlier failure passed on.
T{ 65535 outcome-ok ed-rank-most 65536 outcome-ok ed-rank-most elab-error-code
   99999 outcome-full ed-rank-most
   -> 65535 outcome-ok 65536 outcome-invalid 40 99999 outcome-full }T
\ Every read and every reset gives the data a new generation.
T{ elab-generation elab-reset elab-generation swap -
   elab-generation good lib digest elab-read drop elab-generation swap - 0>
   -> 1 true }T
\ ed-failed (reuse-d, the room and lookup failures): an ok outcome passes
\ and records nothing; a failure records its code.
T{ elab-reset outcome-ok ed-e-room ed-failed elab-error-code -> outcome-ok 0 }T
T{ outcome-full ed-e-room ed-failed elab-error-code -> outcome-full ed-e-room }T
T{ outcome-invalid ed-e-lookup ed-failed elab-error-code -> outcome-invalid ed-e-lookup }T
\ An entry's number checked against the room left (ed-entry-in, split out
\ of ed-entry-below by cleanup-families-3): inside it, first + number;
\ at or past it, invalid with the code ed-e-order.
T{ 10 3 2 ed-entry-in 10 3 3 ed-entry-in nip elab-error-code
   -> 12 outcome-ok outcome-invalid ed-e-order }T
T{ elab-reset -> }T
T{ lib stage-free sealed stage-free -> }T
bye
