\ Unit tests of the importer stage (src/import/stage.fs and
\ stage-records.fs; ADR 0016 C9 step 2): the life cycle and its refusals;
\ the declarations of two reference exports read back field by field
\ (definitions with their hints, a theorem, an inductive block with its
\ types, constructors and recursor rules); finding each declaration by
\ name and each constant's resolution; a read that fails (a manifest of
\ another file, the memory limit, a handler's THROW) rolled back to
\ empty, so that the stage then loads exactly as a fresh one; a bad
\ reference refused by the stage's own checks, through forged records; an
\ mdata expression staged but marked, with the declarations that hold it
\ through a type, a letE's body, a recursor rule or a projection, its
\ bitset counted against the memory limit; stage-unmap before sealing;
\ a scratch tier over the sealed input as a checker-context member, freed
\ by its teardown word, also after a THROW; and every heap block given
\ back by stage-free (heap-watch.fs). tests/core/test_stage.py covers the
\ cases that need a changed export: unknown constants, duplicate names,
\ truncated files. Loaded under HEX: loading must not depend on BASE.
include ../support/tester.fs
include ../support/checks.fs
include ../support/heap-watch.fs
hex require ../../src/import/stage.fs base @ decimal constant base-after-load

T{ base-after-load -> 16 }T
live-blocks @ constant blocks-at-start
create st /stage allot  st /stage erase
: composition ( -- c-addr u ) s" tests/reference/composition.ndjson" ;
: fixture ( -- c-addr u ) s" tests/reference/constant-fixture.ndjson" ;
: block-file ( -- c-addr u ) s" tests/core/ndjson-block.ndjson" ;
: kinds ( -- c-addr u ) s" tests/core/reexport/kinds.ndjson" ;
: why ( -- c-addr u ) st stage-error 2swap 2drop rot drop ;
: tier ( -- tier ) st stage-tier ;
: phase ( -- n ) st stage-state @ ;

\ ---------------------------------------------------------------------------
\ The life cycle. A blank stage refuses everything; an empty one refuses
\ sealing; a sealed one refuses reading and sealing again.
T{ fixture st stage-read st stage-seal -> outcome-invalid outcome-invalid }T
T{ 12 st stage-init phase -> outcome-ok staging-empty }T
T{ st stage-seal phase st stage-decls -> outcome-invalid staging-empty 0 }T
T{ fixture st stage-load phase st stage-sealed? -> outcome-ok staging-sealed true }T
T{ fixture st stage-read composition st stage-load st stage-seal
   -> outcome-invalid outcome-invalid outcome-invalid }T

\ ---------------------------------------------------------------------------
\ constant-fixture: two regular definitions and a theorem, in file order.
: name' ( i -- n ) st export>name ;
: expr' ( i -- e ) st export>expr ;
T{ st stage-decls 0 st staged-kind@ 1 st staged-kind@ 2 st staged-kind@
   -> 3 kind-def kind-def kind-thm }T
T{ 0 st staged-name@ 1 st staged-name@ 2 st staged-name@ -> 1 name' 5 name' 6 name' }T
T{ 0 st staged-type@ 0 st staged-value@ 2 st staged-type@ 2 st staged-value@
   -> 4 expr' 6 expr' 13 expr' 18 expr' }T
T{ 0 st staged-hints@ 0 st staged-hint@ 1 st staged-hint@ 0 st staged-safety@
   -> 2 1 2 0 }T
T{ 2 st staged-hints@ 2 st staged-hint@ 2 st staged-unsafe? 2 st staged-marked?
   -> 0 0 false false }T
\ Universe parameters and `all`, as tuples of names.
T{ 0 st staged-params@ tier tier-tuples tuple-length 0 0 st staged-params@ tier
   tier-tuples tuple-item
   -> 1 2 name' }T
T{ 2 st staged-params@ tier tier-tuples tuple-length 2 st staged-items 0 2 st staged-item
   -> 0 1 6 name' }T
\ Finding by name: the newest declaration, nothing before it; names
\ without a declaration and numbers beyond the names are not found.
T{ 1 name' st stage-find 6 name' st stage-find -> 0 true 2 true }T
T{ 0 st stage-previous 2 name' st stage-find 0 st stage-find 99999 st stage-find
   -> false false false false }T
\ Both constants name fixtureId, which has one declaration: resolved to it.
T{ 7 expr' tier expr-tag@ 7 expr' st stage-resolved 14 expr' st stage-resolved
   -> tag-const 0 true 0 true }T
T{ 7 expr' tier expr-payload@ 4 expr' st stage-resolved -> 1 false }T
\ The tier is sealed: no record can be added.
T{ 0 tier expr-bvar nip 1 st stage-decl? 3 st stage-decl? -> outcome-invalid true false }T
st stage-free
T{ phase live-blocks @ blocks-at-start - -> staging-blank 0 }T

\ ---------------------------------------------------------------------------
\ An inductive block (unchecked: the file has no manifest): the block,
\ then its two types, two constructors and one recursor, then a theorem.
T{ 12 st stage-init block-file st stage-load-unchecked -> outcome-ok outcome-ok }T
: kinds-of ( -- k0 .. k6 ) 7 0 do i st staged-kind@ loop ;
T{ st stage-decls kinds-of -> 7 kind-inductive kind-type kind-type kind-ctor kind-ctor
   kind-recursor kind-thm }T
\ The block: no name, parameters, type or value; [types ctors recursors].
T{ 0 st staged-name@ 0 st staged-params@ 0 st staged-type@ 0 st staged-value@
   -> 0 staged-none staged-none staged-none }T
T{ 0 st staged-items 0 0 st staged-item 1 0 st staged-item 2 0 st staged-item
   -> 3 2 2 1 }T
\ A type: [numParams numIndices all ctors numNested] and its flags.
T{ 1 st staged-items 0 1 st staged-item 4 1 st staged-item 1 st staged-rec?
   -> 5 0 0 false }T
T{ 2 1 st staged-item tier tier-tuples tuple-length 0 3 1 st staged-item tier tier-tuples
   tuple-item -> 2 3 name' }T
\ A constructor: [induct cidx numParams numFields].
T{ 3 st staged-items 0 3 st staged-item 1 4 st staged-item 3 4 st staged-item
   -> 4 1 name' 0 0 }T
T{ 4 st staged-name@ 0 4 st staged-item -> 4 name' 2 name' }T
\ The recursor: [all numParams numIndices numMotives numMinors rules],
\ its rules [ctor nfields rhs] each; universe parameter u; not k.
T{ 5 st staged-items 3 5 st staged-item 4 5 st staged-item 5 st staged-k?
   -> 6 2 2 false }T
: rules ( -- t ) 5 5 st staged-item ;
: rule ( k -- u ) rules tier tier-tuples tuple-item ;
T{ rules tier tier-tuples tuple-length 0 rule 1 rule 2 rule 3 rule
   -> 6 3 name' 0 0 expr' 4 name' }T
T{ 0 5 st staged-params@ tier tier-tuples tuple-item -> 6 name' }T
\ The constants A and B resolve to their types, declarations 1 and 2.
T{ 1 expr' st stage-resolved 2 expr' st stage-resolved -> 1 true 2 true }T
T{ 2 name' st stage-find 3 name' st stage-find 7 name' st stage-find
   -> 2 true 3 true 6 true }T
\ Once unmapped, export indices map to nothing.
st stage-unmap
T{ 1 st export>name 0 st export>expr -> staged-none staged-none }T
st stage-free

\ ---------------------------------------------------------------------------
\ A failed read rolls back to empty: the stage then loads exactly as a
\ fresh one. The numbers a fresh load of the fixture gives:
: counts ( -- names levels tuples exprs decls used )
  tier tier-names cons-numbers tier tier-levels cons-numbers
  tier tier-tuples cons-numbers tier tier-exprs cons-numbers st stage-decls
  tier tier-used ;
T{ 12 st stage-init -> outcome-ok }T
counts 2constant empty-counts-2 2constant empty-counts-1 2constant empty-counts-0
: empty-counts ( -- x1 .. x6 ) empty-counts-0 empty-counts-1 empty-counts-2 ;
T{ fixture st stage-load -> outcome-ok }T
counts 2constant fixture-2 2constant fixture-1 2constant fixture-0
: fixture-counts ( -- x1 .. x6 ) fixture-0 fixture-1 fixture-2 ;
st stage-free
\ 1. The fixture read with composition's manifest: the whole file is read,
\    then refused; the stage is empty again and then loads as fresh.
T{ 12 st stage-init -> outcome-ok }T
s" tests/reference/composition.ndjson.manifest.json" st stage-manifest-use
T{ fixture st stage-read phase -> outcome-invalid staging-empty }T
T{ why s" export differs from its manifest" compare counts -> 0 empty-counts }T
T{ fixture st stage-load counts -> outcome-ok fixture-counts }T
st stage-free
\ 2. The memory limit: full, with its reason, then rolled back; a later
\    read without the limit loads as fresh.
T{ 12 st stage-init -> outcome-ok }T
st stage-allocated 64 + st stage-limit!
T{ fixture st stage-read phase counts -> outcome-full staging-empty empty-counts }T
T{ why s" memory limit of the stage reached" compare -> 0 }T
0 st stage-limit!
T{ fixture st stage-load counts -> outcome-ok fixture-counts }T
st stage-free
\ 3. A handler's THROW passes on after the rollback.
: throws ( record -- outcome ) drop 77 throw ;
T{ 12 st stage-init -> outcome-ok }T
' throws kind-app st stage-export export-handler !
T{ fixture st ' stage-read catch nip nip nip phase counts
   -> 77 staging-empty empty-counts }T
st handlers-set
T{ fixture st stage-load counts -> outcome-ok fixture-counts }T
st stage-free
T{ live-blocks @ blocks-at-start - -> 0 }T

\ ---------------------------------------------------------------------------
\ Bad references, refused by the stage itself even if the reader let one
\ through: forged records handed straight to the handlers of an empty
\ stage, each referring to an index no map holds.
T{ 12 st stage-init -> outcome-ok }T
: forged ( kind -- record )
  st stage-export export-record dup record-unset tuck record-kind !
  st stage-export over record-export ! -1 over record-generation ! ;
: named ( record c-addr u -- record ) rot dup >r name-part 2! r> ;
T{ kind-app forged 0 over app-fn ! 5 over app-arg ! put-app -> outcome-invalid }T
T{ kind-succ forged 9 over succ-of ! put-succ -> outcome-invalid }T
T{ kind-name-str forged 3 over name-prefix ! s" x" named put-name-str
   -> outcome-invalid }T
T{ kind-sort forged 0 over sort-level ! put-sort -> outcome-ok }T
\ A theorem whose type is the sort just made but whose value is no
\ expression, and one with both: only the second is kept. (Their lists
\ read as empty: a forged record is of no line.)
T{ kind-name-str forged 0 over name-prefix ! s" t" named put-name-str -> outcome-ok }T
: theorem ( value -- record )
  kind-thm forged 1 over decl-name ! 0 over decl-type ! tuck decl-value ! ;
T{ 7 theorem put-decl st stage-decls -> outcome-invalid 0 }T
T{ 0 theorem put-decl st stage-decls 0 st staged-value@ -> outcome-ok 1 0 }T
st stage-free

\ ---------------------------------------------------------------------------
\ mdata, staged but marked (kinds.ndjson, Lean's export of every record
\ kind, has one: a `borrowed` annotation reachable only from Nat.add's
\ type): Nat.add is marked, and no other declaration (an independent walk
\ of the file in Python finds the same one).
T{ 12 st stage-init kinds st stage-load-unchecked -> outcome-ok outcome-ok }T
: marked ( -- n last )
  0 0 st stage-decls 0 ?do i st staged-marked? if nip i swap 1+ then loop swap ;
marked constant marked-decl constant marked-count
T{ st stage-mdata @ st stage-marks @ marked-count marked-decl st staged-kind@
   -> 1 1 1 kind-def }T
T{ marked-decl st staged-name@ tier name-text@ s" add" compare -> 0 }T
T{ marked-decl st staged-name@ tier name-prefix@ tier name-text@ s" Nat" compare -> 0 }T

\ ---------------------------------------------------------------------------
\ A scratch tier over the sealed input as a context member (the release
\ hook of lib/context.fs): extended in a new context, it holds heap blocks
\ that context-free gives back, also after a THROW in the middle of a
\ check.
/tier context-record: check-scratch
: check-scratch-free ( -- ) check-scratch tier-free ;
' check-scratch-free context-teardown
live-blocks @ constant blocks-with-input
: in-scratch ( context -- ) context-use tier check-scratch tier-extend ok? 0=
  abort" extend" ;
: built ( e outcome -- e ) ok? 0= abort" build" ;
: build ( -- e ) 0 check-scratch expr-bvar built dup check-scratch expr-app built ;
: build-throw ( context -- ) in-scratch build drop 55 throw ;
context-new throw constant ctx
T{ ctx in-scratch build tier tier-exprs cons-numbers u< context-main context-use
   -> false }T
T{ live-blocks @ blocks-with-input > ctx context-free live-blocks @ blocks-with-input -
   -> true 0 0 }T
context-new throw constant ctx2
T{ ctx2 ' build-throw context-catch nip lf-context @ context-main = -> 55 true }T
T{ ctx2 context-free live-blocks @ blocks-with-input - -> 0 0 }T
st stage-free

\ ---------------------------------------------------------------------------
\ The marks through each way a declaration can hold mdata
\ (stage-cases/marks.ndjson, from the independent review): a constructor
\ whose type is a letE with the mdata in its body (declaration 4), a
\ recursor one of whose rules has a lambda over an application with it as
\ argument (5), and a theorem whose value projects out of it (6); not the
\ block, the types or the other constructor. In unref.ndjson the same
\ mdata record is staged, but no declaration holds it.
: marks-file ( -- c-addr u ) s" tests/core/stage-cases/marks.ndjson" ;
: unref-file ( -- c-addr u ) s" tests/core/stage-cases/unref.ndjson" ;
: marked-set ( -- bits )
  0 st stage-decls 0 ?do i st staged-marked? if 1 i lshift or then loop ;
T{ 12 st stage-init marks-file st stage-load-unchecked -> outcome-ok outcome-ok }T
T{ st stage-decls st stage-mdata @ st stage-marks @ marked-set -> 7 1 3 112 }T
st stage-free
T{ 12 st stage-init unref-file st stage-load-unchecked -> outcome-ok outcome-ok }T
T{ st stage-decls st stage-mdata @ st stage-marks @ marked-set -> 7 1 0 0 }T
st stage-free
\ The marks' bitset is counted against the memory limit: with no room
\ left, sealing is full, with the reason, and the stage broken.
T{ 12 st stage-init marks-file st stage-read-unchecked -> outcome-ok outcome-ok }T
st stage-allocated st stage-limit!
T{ st stage-seal phase -> outcome-full staging-broken }T
T{ why s" memory limit of the stage reached" compare -> 0 }T
st stage-free
\ Before sealing, stage-unmap does nothing: a read afterwards works.
T{ 12 st stage-init -> outcome-ok }T
st stage-unmap
T{ fixture st stage-load st stage-decls -> outcome-ok 3 }T
T{ st stage-other? 3 st stage-meta-text s" 4.35.0" compare -> false 0 }T
st stage-free
\ An export of another Lean version, with sparse and repeated indices
\ (lean4export's own parser reads them): unsupported unless
\ stage-any-version! says otherwise (stage-init says not); then read, the
\ metadata's texts kept (stage-other?, stage-meta-text).
: other-file ( -- c-addr u ) s" tests/core/other-lean.ndjson" ;
T{ 12 st stage-init other-file st stage-load-unchecked st stage-other?
   -> outcome-ok outcome-unsupported false }T
st stage-free
T{ 12 st stage-init true st stage-any-version! other-file st stage-load-unchecked
   -> outcome-ok outcome-ok }T
T{ st stage-other? st stage-decls 3 st stage-meta-text s" 4.29.1" compare
   0 st stage-meta-text s" handcrafted" compare -> true 1 0 0 }T
T{ 1 st stage-meta-text s" 0.1.0" compare 2 st stage-meta-text s" 3.1.0" compare
   4 st stage-meta-text s" 2fcce7258eeb6e324366bc25f9058293b04b7547" compare -> 0 0 0 }T
st stage-free
T{ live-blocks @ blocks-at-start - -> 0 }T
T{ depth -> 0 }T
bye
