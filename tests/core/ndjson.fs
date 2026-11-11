\ Unit tests of src/import/ndjson.fs: every record kind of lean4export
\ format 3.1.0 decoded field by field, the metadata rules, and for each
\ kind the malformed, unsupported and limit cases that must fail closed;
\ handler outcomes; list and rule readers; whole fixture files; the tap
\ and the tally of records by kind, which the manifest check uses.
\ Lines are fed one at a time to export-line from memory; file framing is
\ tested by tests/core/test_ndjson_reader.py on temporary files.
\ The reader is loaded under HEX (and the heap watched): loading must not
\ depend on BASE, and must leave BASE as it found it; every decoding test
\ below then shows the numbers came out right.
include ../support/tester.fs
include ../support/checks.fs
include ../support/heap-watch.fs
hex require ../../src/import/ndjson.fs base @ decimal constant base-after-load

T{ base-after-load export-line-limit export-token-limit export-depth-limit kind-count
   -> 16 67108864 65536 64 27 }T
live-blocks @ constant blocks-at-start
export: ex
T{ ex export-init -> outcome-ok }T

\ A handler that keeps a copy of each record and a log of record kinds.
create snap /record allot
create kinds-seen 32 cells allot
variable calls
: logged ( kind -- ) calls @ 32 < if calls @ cells kinds-seen + ! else drop then 1 calls +! ;
: capture ( record -- outcome ) dup record-kind @ logged snap /record move outcome-ok ;
: kind-at ( n -- kind ) cells kinds-seen + @ ;
: capture-all ( -- ) kind-count 0 do ['] capture i ex export-handler ! loop ;
capture-all
: fresh ( -- ) ex export-restart 0 calls ! ;

\ Feed one line from a writable copy.
create line 1024 allot
: feed ( c-addr u -- outcome ) tuck line swap move line swap ex export-line ;
: why ( -- c-addr u ) ex export-error 2swap 2drop rot drop ;
: failed-field ( -- c-addr u ) ex export-error 2drop rot drop ;
: kind@ ( -- kind ) snap record-kind @ ;
: index@ ( -- n ) snap record-index @ ;
: text@ ( addr -- c-addr u ) 2@ ;

: meta-line ( -- c-addr u )
  s\" {\"meta\":{\"exporter\":{\"name\":\"lean4export\",\"version\":\"3.1.0\"},\"format\":{\"version\":\"3.1.0\"},\"lean\":{\"githash\":\"eb6cafb7290e8bd5f2937522d8d804f58f02bafc\",\"version\":\"4.35.0\"}}}" ;
: started ( -- outcome ) fresh meta-line feed ;

\ Metadata: first, once, pinned versions.
T{ started kind@ index@ ex export-metas @ -> outcome-ok kind-meta 0 1 }T
T{ snap meta-exporter text@ s" lean4export" compare snap meta-lean-version text@ s" 4.35.0" compare -> 0 0 }T
T{ meta-line feed why s" repeated metadata" compare -> outcome-invalid 0 }T
T{ fresh s\" {\"in\":1,\"str\":{\"pre\":0,\"str\":\"x\"}}" feed why s" first record is not metadata" compare
   -> outcome-invalid 0 }T
T{ fresh s\" {\"meta\":{\"exporter\":{\"name\":\"lean4export\",\"version\":\"3.2.0\"},\"format\":{\"version\":\"3.1.0\"},\"lean\":{\"githash\":\"eb6cafb7290e8bd5f2937522d8d804f58f02bafc\",\"version\":\"4.35.0\"}}}" feed
   -> outcome-unsupported }T
T{ fresh s\" {\"meta\":{\"exporter\":{\"name\":\"lean4export\",\"version\":\"3.1.0\"},\"format\":{\"version\":\"3.1.0\"},\"lean\":{\"githash\":\"0\",\"version\":\"4.35.0\"}}}" feed
   -> outcome-unsupported }T
\ Each version alone, with every other field pinned, is refused: the
\ format, the Lean version and the exporter's name.
: unpinned ( c-addr u -- outcome flag )
  feed why s" unsupported exporter, format or Lean version" compare 0= ;
T{ fresh s\" {\"meta\":{\"exporter\":{\"name\":\"lean4export\",\"version\":\"3.1.0\"},\"format\":{\"version\":\"3.2.0\"},\"lean\":{\"githash\":\"eb6cafb7290e8bd5f2937522d8d804f58f02bafc\",\"version\":\"4.35.0\"}}}" unpinned
   -> outcome-unsupported true }T
T{ fresh s\" {\"meta\":{\"exporter\":{\"name\":\"lean4export\",\"version\":\"3.1.0\"},\"format\":{\"version\":\"3.1.0\"},\"lean\":{\"githash\":\"eb6cafb7290e8bd5f2937522d8d804f58f02bafc\",\"version\":\"4.36.0\"}}}" unpinned
   -> outcome-unsupported true }T
T{ fresh s\" {\"meta\":{\"exporter\":{\"name\":\"lean4import\",\"version\":\"3.1.0\"},\"format\":{\"version\":\"3.1.0\"},\"lean\":{\"githash\":\"eb6cafb7290e8bd5f2937522d8d804f58f02bafc\",\"version\":\"4.35.0\"}}}" unpinned
   -> outcome-unsupported true }T
T{ fresh s\" {\"meta\":{\"exporter\":{\"name\":\"lean4export\",\"version\":3},\"format\":{\"version\":\"3.1.0\"},\"lean\":{\"githash\":\"0\",\"version\":\"4.35.0\"}}}" feed
   failed-field s" version" compare -> outcome-invalid 0 }T
T{ fresh s\" {\"meta\":{\"exporter\":{\"name\":\"lean4export\",\"version\":\"3.1.0\"},\"format\":{\"version\":\"3.1.0\"}}}" feed
   -> outcome-invalid }T
T{ fresh s\" {\"meta\":{},\"x\":1}" feed -> outcome-invalid }T
T{ fresh s" [1]" feed why s" record is not an object" compare -> outcome-invalid 0 }T

\ Names: str and num, indices from 1, earlier prefixes.
T{ started s\" {\"in\":1,\"str\":{\"pre\":0,\"str\":\"Nat\"}}" feed kind@ index@ snap name-prefix @
   -> outcome-ok outcome-ok kind-name-str 1 0 }T
T{ snap name-part text@ s" Nat" compare -> 0 }T
T{ s\" {\"in\":2,\"num\":{\"i\":123456789012345678901234567890,\"pre\":1}}" feed kind@ snap name-prefix @
   -> outcome-ok kind-name-num 1 }T
T{ snap name-part text@ s" 123456789012345678901234567890" compare ex export-names @ -> 0 3 }T
T{ s\" {\"str\":{\"pre\":0,\"str\":\"\\u00e9\"},\"in\":3}" feed snap name-part text@ s\" \xc3\xa9" compare
   -> outcome-ok 0 }T
: bad-name ( c-addr u -- outcome ) feed ex export-names @ 4 <> if drop -9 then ;
\ An index is any natural number up to max-n (sparse and repeated
\ indices: "Indices as Lean's reader takes them", below).
T{ s\" {\"in\":-5,\"str\":{\"pre\":0,\"str\":\"y\"}}" bad-name why s" bad index" compare
   -> outcome-invalid 0 }T
T{ s\" {\"in\":5.5,\"str\":{\"pre\":0,\"str\":\"y\"}}" bad-name -> outcome-invalid }T
T{ s\" {\"in\":123456789012345678901234567890,\"str\":{\"pre\":0,\"str\":\"y\"}}" bad-name
   why s" index too large" compare -> outcome-full 0 }T
T{ s\" {\"in\":4,\"str\":{\"pre\":4,\"str\":\"y\"}}" bad-name failed-field s" pre" compare -> outcome-invalid 0 }T
T{ s\" {\"in\":4,\"str\":{\"pre\":0}}" bad-name -> outcome-invalid }T
T{ s\" {\"in\":4,\"str\":{\"pre\":0,\"str\":\"y\",\"z\":1}}" bad-name -> outcome-invalid }T
T{ s\" {\"in\":4,\"str\":{\"pre\":0,\"str\":5}}" bad-name -> outcome-invalid }T
T{ s\" {\"in\":4,\"str\":{\"pre\":0,\"pre\":0}}" bad-name -> outcome-invalid }T
T{ s\" {\"in\":4,\"str\":{\"pre\":0,\"str\":\"y\"},\"x\":1}" bad-name -> outcome-invalid }T
T{ s\" {\"in\":4,\"bad\":{}}" bad-name why s" unknown record kind" compare -> outcome-invalid 0 }T
T{ s\" {\"in\":4,\"num\":{\"pre\":0,\"i\":-1}}" bad-name -> outcome-invalid }T
T{ s\" {\"in\":4,\"num\":{\"pre\":0,\"i\":1.5}}" bad-name -> outcome-invalid }T
T{ s\" {\"in\":\"4\",\"num\":{\"pre\":0,\"i\":1}}" bad-name -> outcome-invalid }T
T{ s\" {\"in\":4,\"in\":4}" bad-name -> outcome-invalid }T
T{ s\" {\"in\":4}" bad-name -> outcome-invalid }T
T{ s\" {\"in\":4,\"str\":{\"pre\":0,\"str\":\"y\"}}" feed ex export-names @ -> outcome-ok 5 }T

\ Levels: succ, max, imax, param; earlier operands; param not anonymous.
T{ s\" {\"il\":1,\"succ\":0}" feed kind@ snap succ-of @ -> outcome-ok kind-succ 0 }T
T{ s\" {\"il\":2,\"max\":[0,1]}" feed kind@ snap max-left @ snap max-right @ -> outcome-ok kind-max 0 1 }T
T{ s\" {\"imax\":[2,1],\"il\":3}" feed kind@ snap max-left @ snap max-right @ -> outcome-ok kind-imax 2 1 }T
T{ s\" {\"il\":4,\"param\":1}" feed kind@ index@ snap param-name @ -> outcome-ok kind-param 4 1 }T
: bad-level ( c-addr u -- outcome ) feed ex export-levels @ 5 <> if drop -9 then ;
T{ s\" {\"il\":5,\"param\":0}" bad-level -> outcome-invalid }T
T{ s\" {\"il\":5,\"param\":5}" bad-level -> outcome-invalid }T
T{ s\" {\"il\":5,\"succ\":5}" bad-level -> outcome-invalid }T
T{ s\" {\"il\":5,\"max\":[0]}" bad-level -> outcome-invalid }T
T{ s\" {\"il\":5,\"max\":[0,1,2]}" bad-level -> outcome-invalid }T
T{ s\" {\"il\":5,\"max\":[0,5]}" bad-level -> outcome-invalid }T
T{ s\" {\"il\":5,\"max\":{\"a\":1}}" bad-level -> outcome-invalid }T
T{ s\" {\"il\":5,\"zero\":0}" bad-level -> outcome-invalid }T
T{ s\" {\"il\":5,\"mvar\":0}" bad-level -> outcome-invalid }T
T{ s\" {\"il\":-6,\"succ\":0}" bad-level -> outcome-invalid }T

\ Expressions: every kind, then the failures.
T{ s\" {\"ie\":0,\"sort\":4}" feed kind@ index@ snap sort-level @ -> outcome-ok kind-sort 0 4 }T
T{ s\" {\"bvar\":3,\"ie\":1}" feed kind@ snap bvar-index @ -> outcome-ok kind-bvar 3 }T
T{ s\" {\"const\":{\"name\":1,\"us\":[0,4,2]},\"ie\":2}" feed kind@ snap const-name @ -> outcome-ok kind-const 1 }T
T{ snap const-levels @ snap list-count 1 snap const-levels @ snap list-item -> 3 4 }T
\ List readers check their index and their list.
T{ 2 snap const-levels @ snap list-item 3 snap const-levels @ snap list-item -> 2 -1 }T
T{ -1 snap const-levels @ snap list-item -> -1 }T
T{ -1 snap list-count 0 snap list-count 1 snap list-count 99 snap list-count -> 0 0 0 0 }T
T{ 0 -1 snap list-item -> -1 }T
T{ s\" {\"app\":{\"arg\":1,\"fn\":2},\"ie\":3}" feed kind@ snap app-fn @ snap app-arg @ -> outcome-ok kind-app 2 1 }T
T{ s\" {\"ie\":4,\"lam\":{\"binderInfo\":\"implicit\",\"body\":1,\"name\":0,\"type\":0}}" feed
   kind@ snap binder-name @ snap binder-type @ snap binder-body @ snap binder-info @
   -> outcome-ok kind-lam 0 0 1 1 }T
T{ s\" {\"forallE\":{\"binderInfo\":\"instImplicit\",\"body\":4,\"name\":2,\"type\":0},\"ie\":5}" feed
   kind@ snap binder-info @ -> outcome-ok kind-forall 3 }T
T{ s\" {\"ie\":6,\"letE\":{\"body\":0,\"name\":1,\"nondep\":true,\"type\":0,\"value\":5}}" feed
   kind@ snap let-value @ snap let-nondep @ -> outcome-ok kind-let 5 true }T
T{ s\" {\"ie\":7,\"proj\":{\"idx\":2,\"struct\":6,\"typeName\":1}}" feed
   kind@ snap proj-type-name @ snap proj-idx @ snap proj-struct @ -> outcome-ok kind-proj 1 2 6 }T
T{ s\" {\"ie\":8,\"natVal\":\"123456789012345678901234567890\"}" feed kind@ snap literal-text text@ nip
   -> outcome-ok kind-natval 30 }T
T{ s\" {\"ie\":9,\"strVal\":\"a\\nb\"}" feed kind@ snap literal-text text@ s\" a\nb" compare
   -> outcome-ok kind-strval 0 }T
T{ s\" {\"ie\":10,\"mdata\":{\"data\":{\"k\":[1]},\"expr\":9}}" feed kind@ snap mdata-expr @
   -> outcome-ok kind-mdata 9 }T
T{ s\" {\"ie\":11,\"natVal\":\"0\"}" feed ex export-exprs @ -> outcome-ok 12 }T
: bad-expr ( c-addr u -- outcome ) feed ex export-exprs @ 12 <> if drop -9 then ;
T{ s\" {\"app\":{\"arg\":12,\"fn\":0},\"ie\":12}" bad-expr failed-field s" arg" compare -> outcome-invalid 0 }T
T{ s\" {\"app\":{\"arg\":1,\"fn\":0},\"ie\":true}" bad-expr -> outcome-invalid }T
T{ s\" {\"app\":{\"arg\":1},\"ie\":12}" bad-expr -> outcome-invalid }T
T{ s\" {\"app\":{\"arg\":1,\"fn\":0,\"f\":0},\"ie\":12}" bad-expr -> outcome-invalid }T
T{ s\" {\"app\":{\"arg\":1,\"fn\":true},\"ie\":12}" bad-expr -> outcome-invalid }T
T{ s\" {\"ie\":12,\"lam\":{\"binderInfo\":\"bogus\",\"body\":1,\"name\":0,\"type\":0}}" bad-expr
   why s" unknown enumeration value" compare -> outcome-invalid 0 }T
T{ s\" {\"ie\":12,\"lam\":{\"binderInfo\":0,\"body\":1,\"name\":0,\"type\":0}}" bad-expr -> outcome-invalid }T
T{ s\" {\"ie\":12,\"natVal\":\"012\"}" bad-expr -> outcome-invalid }T
T{ s\" {\"ie\":12,\"natVal\":\"\"}" bad-expr -> outcome-invalid }T
T{ s\" {\"ie\":12,\"natVal\":12}" bad-expr -> outcome-invalid }T
T{ s\" {\"ie\":12,\"natVal\":\"1e3\"}" bad-expr -> outcome-invalid }T
T{ s\" {\"ie\":12,\"strVal\":null}" bad-expr -> outcome-invalid }T
T{ s\" {\"const\":{\"name\":0,\"us\":[]},\"ie\":12}" bad-expr -> outcome-invalid }T
T{ s\" {\"const\":{\"name\":1,\"us\":[5]},\"ie\":12}" bad-expr -> outcome-invalid }T
T{ s\" {\"const\":{\"name\":1,\"us\":0},\"ie\":12}" bad-expr why s" expected a list" compare -> outcome-invalid 0 }T
T{ s\" {\"ie\":12,\"letE\":{\"body\":0,\"name\":1,\"nondep\":1,\"type\":0,\"value\":5}}" bad-expr -> outcome-invalid }T
T{ s\" {\"ie\":12,\"proj\":{\"idx\":2,\"struct\":6,\"typeName\":0}}" bad-expr -> outcome-invalid }T
T{ s\" {\"ie\":12,\"proj\":{\"idx\":123456789012345678901234567890,\"struct\":6,\"typeName\":1}}" bad-expr
   why s" natural number too large" compare -> outcome-full 0 }T
T{ s\" {\"bvar\":123456789012345678901234567890,\"ie\":12}" bad-expr -> outcome-full }T
T{ s\" {\"bvar\":-1,\"ie\":12}" bad-expr -> outcome-invalid }T
T{ s\" {\"bvar\":-0,\"ie\":12}" feed snap bvar-index @ ex export-exprs @ -> outcome-ok 0 13 }T
: bad-expr13 ( c-addr u -- outcome ) feed ex export-exprs @ 13 <> if drop -9 then ;
T{ s\" {\"ie\":13,\"mdata\":{\"data\":[],\"expr\":9}}" bad-expr13 -> outcome-invalid }T
T{ s\" {\"ie\":13,\"fvar\":0}" bad-expr13 -> outcome-invalid }T
T{ s\" {\"ie\":13,\"ie\":13}" bad-expr13 -> outcome-invalid }T
T{ s\" {\"ie\":13,\"sort\":0,\"bvar\":0}" bad-expr13 -> outcome-invalid }T
T{ s\" {\"ie\":13,\"in\":5}" bad-expr13 -> outcome-invalid }T
T{ s\" {\"ie\":13,\"meta\":{}}" bad-expr13 -> outcome-invalid }T

\ Declarations.
T{ 0 calls ! s\" {\"thm\":{\"all\":[1],\"levelParams\":[3,1],\"name\":1,\"type\":0,\"value\":3}}" feed
   kind@ index@ snap decl-name @ snap decl-type @ snap decl-value @ -> outcome-ok kind-thm 0 1 0 3 }T
T{ snap decl-params @ snap list-count 0 snap decl-params @ snap list-item snap decl-all @ snap list-count
   -> 2 3 1 }T
T{ s\" {\"def\":{\"all\":[1],\"hints\":{\"regular\":4294967295},\"levelParams\":[],\"name\":1,\"safety\":\"partial\",\"type\":0,\"value\":3}}" feed
   kind@ index@ snap decl-hints @ snap decl-safety @ -> outcome-ok kind-def 1 2 2 }T
T{ snap decl-height @ 4294967294 ( fits a cell as an unsigned number ) 1+ = -> true }T
T{ s\" {\"def\":{\"all\":[1],\"hints\":\"abbrev\",\"levelParams\":[],\"name\":1,\"safety\":\"safe\",\"type\":0,\"value\":3}}" feed
   snap decl-hints @ snap decl-safety @ -> outcome-ok 1 0 }T
T{ s\" {\"axiom\":{\"isUnsafe\":false,\"levelParams\":[1],\"name\":2,\"type\":0}}" feed kind@ snap decl-unsafe @
   -> outcome-ok kind-axiom false }T
T{ s\" {\"opaque\":{\"all\":[1],\"isUnsafe\":true,\"levelParams\":[],\"name\":1,\"type\":0,\"value\":3}}" feed
   kind@ snap decl-unsafe @ -> outcome-ok kind-opaque true }T
T{ s\" {\"quot\":{\"kind\":\"lift\",\"levelParams\":[1,3],\"name\":1,\"type\":0}}" feed kind@ snap decl-quot-kind @
   -> outcome-ok kind-quot 2 }T
T{ ex export-decls @ -> 6 }T
: plain-thm ( -- c-addr u )
  s\" {\"thm\":{\"all\":[1],\"levelParams\":[],\"name\":1,\"type\":0,\"value\":0}}" ;
: bad-decl ( c-addr u -- outcome ) feed ex export-decls @ 6 <> if drop -9 then ;
T{ s\" {\"def\":{\"all\":[1],\"hints\":{\"regular\":4294967296},\"levelParams\":[],\"name\":1,\"safety\":\"safe\",\"type\":0,\"value\":3}}" bad-decl
   why s" height beyond UInt32" compare -> outcome-invalid 0 }T
T{ s\" {\"def\":{\"all\":[1],\"hints\":\"never\",\"levelParams\":[],\"name\":1,\"safety\":\"safe\",\"type\":0,\"value\":3}}" bad-decl -> outcome-invalid }T
T{ s\" {\"def\":{\"all\":[1],\"hints\":{\"regular\":1,\"x\":2},\"levelParams\":[],\"name\":1,\"safety\":\"safe\",\"type\":0,\"value\":3}}" bad-decl -> outcome-invalid }T
T{ s\" {\"def\":{\"all\":[1],\"hints\":\"abbrev\",\"levelParams\":[],\"name\":1,\"safety\":\"maybe\",\"type\":0,\"value\":3}}" bad-decl -> outcome-invalid }T
T{ s\" {\"thm\":{\"all\":[1],\"levelParams\":[],\"name\":0,\"type\":0,\"value\":3}}" bad-decl -> outcome-invalid }T
T{ s\" {\"thm\":{\"all\":[1],\"levelParams\":[0],\"name\":1,\"type\":0,\"value\":3}}" bad-decl
   why s" bad reference in list" compare -> outcome-invalid 0 }T
T{ s\" {\"thm\":{\"all\":[9],\"levelParams\":[],\"name\":1,\"type\":0,\"value\":3}}" bad-decl -> outcome-invalid }T
T{ s\" {\"thm\":{\"all\":[1],\"levelParams\":[],\"name\":1,\"type\":0,\"value\":13}}" bad-decl -> outcome-invalid }T
T{ s\" {\"thm\":{\"all\":[1],\"levelParams\":[],\"name\":1,\"type\":0}}" bad-decl -> outcome-invalid }T
T{ s\" {\"quot\":{\"kind\":\"other\",\"levelParams\":[],\"name\":1,\"type\":0}}" bad-decl -> outcome-invalid }T
T{ s\" {\"axiom\":{\"isUnsafe\":\"no\",\"levelParams\":[],\"name\":2,\"type\":0}}" bad-decl -> outcome-invalid }T
T{ s\" {\"thm\":{},\"def\":{}}" bad-decl -> outcome-invalid }T
T{ s\" {\"lemma\":{}}" bad-decl why s" unknown record kind" compare -> outcome-invalid 0 }T
T{ s" {}" bad-decl -> outcome-invalid }T

\ An inductive block: the block, then its types, constructors and recursors.
: type-json ( -- c-addr u ) s\" {\"all\":[1],\"ctors\":[2],\"isRec\":false,\"isReflexive\":false,\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"numIndices\":0,\"numNested\":0,\"numParams\":1,\"type\":0}" ;
: ctor-json ( -- c-addr u ) s\" {\"cidx\":0,\"induct\":1,\"isUnsafe\":false,\"levelParams\":[],\"name\":2,\"numFields\":2,\"numParams\":1,\"type\":3}" ;
: rec-json ( -- c-addr u ) s\" {\"all\":[1],\"isUnsafe\":false,\"k\":true,\"levelParams\":[3],\"name\":4,\"numIndices\":0,\"numMinors\":1,\"numMotives\":1,\"numParams\":1,\"rules\":[{\"ctor\":2,\"nfields\":2,\"rhs\":5},{\"ctor\":4,\"nfields\":0,\"rhs\":6}],\"type\":0}" ;
create block-text 1024 allot  variable block-length
: +block-text ( c-addr u -- ) tuck block-text block-length @ + swap move block-length +! ;
: block-of ( c-addr u c-addr u c-addr u -- c-addr u )
  0 block-length ! 2>r 2>r s\" {\"inductive\":{\"ctors\":[" +block-text +block-text s\" ],\"recs\":[" +block-text
  2r> +block-text s\" ],\"types\":[" +block-text 2r> +block-text s" ]}}" +block-text block-text block-length @ ;
T{ 0 calls ! ctor-json rec-json type-json block-of feed calls @ -> outcome-ok 4 }T
T{ 0 kind-at 1 kind-at 2 kind-at 3 kind-at -> kind-inductive kind-type kind-ctor kind-recursor }T
T{ kind@ index@ snap decl-name @ snap recursor-num-minors @ snap recursor-k @ -> kind-recursor 0 4 1 true }T
T{ snap recursor-rules @ snap list-count -> 2 }T
T{ 1 snap recursor-rule dup rule-ctor @ over rule-fields @ rot rule-rhs @ -> 4 0 6 }T
T{ 0 snap recursor-rule rule-rhs @ -> 5 }T
T{ 2 snap recursor-rule -1 snap recursor-rule -> 0 0 }T
T{ ex export-decls @ -> 7 }T
\ A bad block hands nothing over, not even the block's own record.
: bad-block ( c-addr u c-addr u c-addr u -- outcome )
  0 calls ! block-of feed ex export-decls @ 7 <> calls @ 0<> or if drop -9 then ;
\ No type, but a constructor or a recursor: malformed.
T{ ctor-json s" " s" " bad-block why s" inductive block without types" compare
   -> outcome-invalid 0 }T
T{ s" " rec-json s" " bad-block why s" inductive block without types" compare
   -> outcome-invalid 0 }T
T{ ctor-json rec-json s" 1" bad-block -> outcome-invalid }T
T{ ctor-json s\" {\"all\":[1]}" type-json bad-block -> outcome-invalid }T
T{ s\" {\"cidx\":0,\"induct\":0,\"isUnsafe\":false,\"levelParams\":[],\"name\":2,\"numFields\":2,\"numParams\":1,\"type\":3}"
   rec-json type-json bad-block -> outcome-invalid }T
T{ ctor-json s\" {\"all\":[1],\"isUnsafe\":false,\"k\":true,\"levelParams\":[3],\"name\":4,\"numIndices\":0,\"numMinors\":1,\"numMotives\":1,\"numParams\":1,\"rules\":[{\"ctor\":2,\"nfields\":2,\"rhs\":13}],\"type\":0}"
   type-json bad-block failed-field s" rhs" compare -> outcome-invalid 0 }T
\ An empty block (no type, constructor or recursor) is read and handed
\ over alone: Lean's kernel rejects such a declaration (emptyBlock), and
\ the importer stages it for the checker to say so (ADR 0016 amendment 1).
T{ 0 calls ! s" " s" " s" " block-of feed calls @ ex export-decls @ -> outcome-ok 1 8 }T

\ Handlers: a missing one is unsupported; their outcomes stop reading, with
\ a reason and no field left over from decoding.
: refuse-app ( -- ) ['] export-refused kind-app ex export-handler ! ;
: allow-app ( -- ) ['] capture kind-app ex export-handler ! ;
: app-handler ( xt -- ) kind-app ex export-handler ! ;
: says-rejected ( record -- outcome ) drop outcome-rejected ;
: says-garbage ( record -- outcome ) drop 77 ;
: app-13 ( -- c-addr u ) s\" {\"app\":{\"arg\":1,\"fn\":2},\"ie\":13}" ;
T{ refuse-app app-13 feed ex export-exprs @ -> outcome-unsupported 13 }T
T{ why s" no handler for this record kind" compare failed-field nip -> 0 0 }T
T{ ' says-rejected app-handler app-13 feed why s" handler refused the record" compare
   failed-field nip -> outcome-rejected 0 0 }T
T{ ' says-garbage app-handler app-13 feed why s" handler refused the record" compare
   -> outcome-invalid 0 }T
\ The handler contract: exactly one outcome, checked by depth.
: says-twice ( record -- outcome x ) drop outcome-ok 5 ;
: says-nothing ( record -- ) drop ;
: takes-two ( x record -- ) 2drop ;
T{ ' says-twice app-handler app-13 feed why s" handler left no outcome or extra items" compare
   ex export-exprs @ -> outcome-invalid 0 13 }T
T{ ' says-nothing app-handler app-13 feed -> outcome-invalid }T
\ Taking more than the record throws -4, and the THROW ends the busy mark.
T{ ' takes-two app-handler app-13 ' feed catch nip nip ex export-busy @ -> -4 0 }T
\ So does taking more but leaving one item, or replacing the item under
\ the record: the export lies there as a canary. Nothing is counted, and
\ the replacement is never written through.
variable victim
: swaps-under ( x record -- y outcome ) 2drop victim outcome-ok ;
: takes-two-gives-one ( x record -- outcome ) 2drop outcome-ok ;
T{ ' swaps-under app-handler app-13 ' feed catch nip nip ex export-busy @ ex export-exprs @
   victim @ -> -4 0 13 0 }T
T{ ' takes-two-gives-one app-handler app-13 ' feed catch nip nip ex export-exprs @ -> -4 13 }T
\ Two cells under the record are canaries: reaching two cells down (the
\ third review's probe, which once made the reader count through victim)
\ throws as well. Below them lies only the caller's data, never anything
\ of the reader's, such as its count or a declaration's kind: a handler
\ that reaches three cells down changes the caller's 77, and the record
\ is counted as usual (more cases under export-read and in a block below).
: reaches-two ( y canary record -- y' canary outcome ) drop nip victim swap outcome-ok ;
: reaches-three ( z c c record -- z' c c outcome ) drop 2>r drop victim 2r> outcome-ok ;
T{ ' reaches-two app-handler app-13 ' feed catch nip nip ex export-exprs @ victim @
   -> -4 13 0 }T
T{ 77 ' reaches-three app-handler app-13 feed ex export-exprs @ victim @
   -> victim outcome-ok 14 0 }T
T{ 77 ' reaches-three kind-thm ex export-handler ! plain-thm feed ex export-decls @
   -> victim outcome-ok 9 }T
T{ victim @ ' capture kind-thm ex export-handler ! -> 0 }T
\ export-restart starts again; then 13 sorts again.
T{ ex export-restart ex export-busy @ ex export-exprs @ -> 0 0 }T
: sort-line ( n -- c-addr u )
  0 block-length ! s\" {\"ie\":" +block-text 0 <# #s #> +block-text
  s\" ,\"sort\":0}" +block-text block-text block-length @ ;
: thirteen ( -- outcome ) started 13 0 do i sort-line feed or loop ;
T{ thirteen ex export-exprs @ -> outcome-ok 13 }T
\ No reading the same export again from its handler.
: reads-line ( record -- outcome ) drop app-13 ex export-line ;
: reads-file ( record -- outcome ) drop s" tests/reference/identity.ndjson" ex export-read ;
T{ ' reads-line app-handler app-13 feed why s" export read again by its own handler" compare
   ex export-busy @ -> outcome-invalid 0 0 }T
T{ ' reads-file app-handler app-13 feed ex export-busy @ ex export-exprs @
   -> outcome-invalid 0 13 }T
\ Nor resetting or freeing it from its handler: that throws, the export is
\ idle again, and it keeps its buffers and counts.
: inits ( record -- outcome ) drop ex export-init ;
: frees ( record -- outcome ) drop ex export-free outcome-ok ;
: restarts ( record -- outcome ) drop ex export-restart outcome-ok ;
: thrown-by ( xt -- n ) app-handler app-13 ['] feed catch nip nip ;
T{ ' inits thrown-by ' frees thrown-by ' restarts thrown-by ex export-busy @ -> -2 -2 -2 0 }T
T{ ex export-reader reader-buffer @ 0<> ex export-json json-tape @ 0<> ex export-exprs @
   -> true true 13 }T
T{ allow-app app-13 feed ex export-exprs @ -> outcome-ok 14 }T

\ Framing and syntax inside a line.
T{ s\" {\"ie\":14,\"sort\":0}\r" feed why s" carriage return or byte-order mark" compare -> outcome-invalid 0 }T
T{ s\" \xef\xbb\xbf{\"ie\":14,\"sort\":0}" feed -> outcome-invalid }T
T{ s\" {\"ie\":14,\"sort\":0" feed why s" unexpected end of text" compare -> outcome-invalid 0 }T
T{ s" " feed -> outcome-invalid }T
T{ s\" {\"ie\":14,\"strVal\":\"\xff\"}" feed -> outcome-invalid }T
T{ s\" {\"ie\" : 14 , \"sort\" : 0 }" feed ex export-exprs @ -> outcome-ok 15 }T

\ Whole files: every reference fixture reads to the end.
: read-fixture ( c-addr u -- outcome calls ) fresh ex export-read calls @ ;
T{ s" tests/reference/composition.ndjson" read-fixture -> outcome-ok 35 }T
T{ s" tests/reference/constant-fixture.ndjson" read-fixture -> outcome-ok 32 }T
T{ s" tests/reference/identity.ndjson" read-fixture -> outcome-ok 12 }T
T{ s" tests/reference/poly-identity.ndjson" read-fixture -> outcome-ok 30 }T
T{ s" tests/reference/type-identity.ndjson" read-fixture -> outcome-ok 29 }T
T{ s" tests/reference/no-such.ndjson" read-fixture -> outcome-invalid 0 }T
T{ why s" cannot open the file" compare -> 0 }T
T{ refuse-app s" tests/reference/composition.ndjson" read-fixture drop ex export-error 2drop 2drop -> outcome-unsupported 27 }T
T{ allow-app s" tests/reference/composition.ndjson" ex ' export-read rs-checked -> outcome-ok }T
\ A THROW from a handler passes on, with the file closed and the export idle.
: throws ( record -- outcome ) drop 77 throw ;
T{ ' throws app-handler s" tests/reference/composition.ndjson" ex ' export-read catch
   nip nip nip ex export-reader reader-fid @ ex export-busy @ -> 77 0 0 }T
T{ ' inits app-handler s" tests/reference/composition.ndjson" ex ' export-read catch
   nip nip nip ex export-reader reader-fid @ ex export-busy @ -> -2 0 0 }T
T{ allow-app s" tests/reference/composition.ndjson" read-fixture -> outcome-ok 35 }T
\ Under a handler's canaries lies only its caller's data, nothing of the
\ reader's (the fourth review found there the export being read, and a
\ block list's visit and export). A handler that reaches three cells down
\ during export-read and puts another, finished export there (the
\ review's probe, which once ended the reading ok after two records)
\ changes only its caller's 77, and every record is handed over. Thrown
\ from such a handler, -77 still closes the file the export reads.
export: other
: ignores ( record -- outcome ) drop outcome-ok ;
: other-read ( -- outcome )
  other export-init drop kind-count 0 do ['] ignores i other export-handler ! loop
  s" tests/reference/identity.ndjson" other export-read ;
T{ other-read -> outcome-ok }T
variable fired  variable deep-cell
\ Once, the value of deep-cell three or four cells under the record;
\ otherwise as capture.
: reaches-three-once ( z c c record -- z' c c outcome )
  fired @ if capture exit then true fired ! capture >r 2>r drop deep-cell @ 2r> r> ;
: reaches-four-once ( y z c c record -- y' z c c outcome )
  fired @ if capture exit then true fired ! capture >r 2>r nip deep-cell @ swap 2r> r> ;
: reaches ( x xt kind -- ) ex export-handler ! deep-cell ! 0 fired ! ;
T{ other ' reaches-three-once kind-name-str reaches
   77 s" tests/reference/composition.ndjson" read-fixture -> other outcome-ok 35 }T
: throws-deep ( z c c record -- ) drop 2>r drop other 2r> -77 throw ;
T{ ' throws-deep kind-name-str ex export-handler !
   66 s" tests/reference/composition.ndjson" ex ' export-read catch nip nip nip
   ex export-reader reader-fid @ ex export-busy @ -> other -77 0 0 }T
T{ capture-all s" tests/reference/composition.ndjson" read-fixture -> outcome-ok 35 }T
\ Nor in a block's walk under export-read (the fifth review's test): a
\ handler that zeroes every cell of its caller's under the canaries, down
\ to stack-floor, still gets all 19 records of a block of two types, two
\ constructors and a recursor, and the reading is ok.
variable stack-floor
: zero-cells ( i*x i -- i*0 ) dup >r 0 ?do drop loop r> 0 ?do 0 loop ;
: zeroes-under ( i*x c c record -- i*0 c c outcome )
  capture >r 2>r depth stack-floor @ - zero-cells 2r> r> ;
: zeroing-all ( -- ) kind-count 0 do ['] zeroes-under i ex export-handler ! loop ;
T{ zeroing-all depth stack-floor ! 11 22 33 s" tests/core/ndjson-block.ndjson" read-fixture
   -> 0 0 0 outcome-ok 19 }T
T{ 12 kind-at 13 kind-at 14 kind-at 15 kind-at 16 kind-at 17 kind-at 18 kind-at
   -> kind-inductive kind-type kind-type kind-ctor kind-ctor kind-recursor kind-thm }T
T{ ex export-decls @ capture-all -> 2 }T
\ The end of input needs metadata and a declaration.
T{ fresh ex export-end why s" missing metadata or declaration" compare -> outcome-invalid 0 }T
T{ started ex export-end -> outcome-ok outcome-invalid }T

\ A fresh prefix: names 1 to 4, expressions 0 to 7 (sorts).
: name-line ( n -- c-addr u )
  0 block-length ! s\" {\"in\":" +block-text 0 <# #s #> +block-text
  s\" ,\"str\":{\"pre\":0,\"str\":\"x\"}}" +block-text block-text block-length @ ;
: prefix ( -- outcome ) started 5 1 do i name-line feed or loop 8 0 do i sort-line feed or loop ;
T{ prefix ex export-names @ ex export-exprs @ -> outcome-ok 5 8 }T
\ export-line numbers the lines it is given from export-restart on: the
\ last record came from line 13, and a failure on the next is at line 14.
T{ ex export-at @ snap record-line @ -> 13 13 }T
T{ s\" {\"ie\":-9,\"sort\":0}" feed ex export-error 2drop 2drop -> outcome-invalid 14 }T

\ Decoding never depends on BASE: heights, and numbers as wide as max-n.
: def-1000 ( -- c-addr u )
  s\" {\"def\":{\"all\":[1],\"hints\":{\"regular\":1000},\"levelParams\":[],\"name\":1,\"safety\":\"safe\",\"type\":0,\"value\":0}}" ;
T{ hex def-1000 feed decimal snap decl-height @ -> outcome-ok 1000 }T
T{ 2 base ! def-1000 feed decimal snap decl-height @ -> outcome-ok 1000 }T
: max-n-text ( -- c-addr u ) max-n 0 <# #s #> ;
\ Expression n: a bvar whose index has the digits of max-n.
: bvar-max ( n -- c-addr u )
  0 block-length ! s\" {\"ie\":" +block-text 0 <# #s #> +block-text
  s\" ,\"bvar\":" +block-text max-n-text +block-text s" }" +block-text block-text block-length @ ;
T{ 8 bvar-max 2 base ! feed decimal snap bvar-index @ -> outcome-ok max-n }T
T{ 9 bvar-max hex feed decimal snap bvar-index @ ex export-exprs @ -> outcome-ok max-n 10 }T

\ No field survives from an earlier record: a field the kind does not
\ have reads -1, in declarations and in the elements of a block.
: unsafe-axiom ( -- c-addr u )
  s\" {\"axiom\":{\"isUnsafe\":true,\"levelParams\":[],\"name\":1,\"type\":0}}" ;
: abbrev-def ( -- c-addr u )
  s\" {\"def\":{\"all\":[1],\"hints\":\"abbrev\",\"levelParams\":[],\"name\":1,\"safety\":\"safe\",\"type\":0,\"value\":0}}" ;
T{ unsafe-axiom feed snap decl-unsafe @ -> outcome-ok true }T
T{ plain-thm feed snap decl-unsafe @ snap decl-hints @ snap decl-height @ -> outcome-ok -1 -1 -1 }T
T{ def-1000 feed abbrev-def feed snap decl-hints @ snap decl-height @ -> outcome-ok outcome-ok 1 -1 }T
T{ 0 calls ! ctor-json s" " type-json block-of feed calls @ -> outcome-ok 3 }T
T{ kind@ index@ snap ctor-unsafe @ snap type-reflexive @ -> kind-ctor 0 false -1 }T
T{ 0 snap recursor-rule -> 0 }T

\ The token limit bounds one line's tape: expression n, a constant with k
\ level arguments, has 9 + k tokens.
140000 constant big-room
create big-line big-room allot  variable big-length
: big+ ( c-addr u -- )
  dup big-length @ + big-room > abort" big-line too small"
  tuck big-line big-length @ + swap move big-length +! ;
: zeros+ ( k -- ) 0 ?do s" 0," big+ loop -1 big-length +! ;
: const-line ( n k -- c-addr u )
  0 big-length ! s\" {\"ie\":" big+ swap 0 <# #s #> big+
  s\" ,\"const\":{\"name\":1,\"us\":[" big+ zeros+ s" ]}}" big+ big-line big-length @ ;
T{ 10 export-token-limit 9 - const-line ex export-line ex export-json json-count @
   -> outcome-ok export-token-limit }T
T{ 11 export-token-limit 8 - const-line ex export-line why s" too many tokens" compare
   -> outcome-full 0 }T
T{ ex export-json json-room @ export-token-limit <= -> true }T

\ The depth limit through the reader: expression 8, an mdata whose data
\ holds n nested arrays, is nested n + 3 deep (the line's object, mdata's
\ and data's); 64 containers deep pass, 65 are full.
: nested-line ( n -- c-addr u )
  0 big-length ! s\" {\"ie\":8,\"mdata\":{\"data\":{\"k\":" big+
  dup 0 ?do s" [" big+ loop 0 ?do s" ]" big+ loop s\" },\"expr\":0}}" big+
  big-line big-length @ ;
T{ prefix 62 nested-line ex export-line why s" nested too deeply" compare ex export-exprs @
   -> outcome-ok outcome-full 0 8 }T
T{ 61 nested-line ex export-line ex export-exprs @ -> outcome-ok 9 }T

\ A reference never reads as a list, not even one that equals the token
\ index of an array (here const-name 4, the token of the us array).
T{ s\" {\"const\":{\"us\":[0,0,0],\"name\":4},\"ie\":9}" feed
   snap const-name @ snap list-count 0 snap const-name @ snap list-item
   snap const-levels @ snap list-count -> outcome-ok 0 -1 3 }T
\ A line's failed field and reason never carry over to the next line.
T{ s\" {\"in\":5,\"str\":{\"pre\":7,\"str\":\"x\"}}" feed failed-field s" pre" compare
   -> outcome-invalid 0 }T
T{ s\" {\"in\":5,\"str\":{\"pre\":0" feed failed-field nip why s" unexpected end of text" compare
   -> outcome-invalid 0 0 }T

\ A block of four types. list-item refuses a list of objects; and a type
\ handler that renumbers its record does not change the next type's number.
create types-text 1024 allot  variable types-length
: +types ( c-addr u -- ) tuck types-text types-length @ + swap move types-length +! ;
: four-types ( -- c-addr u )
  0 types-length ! type-json +types 3 0 do s" ," +types type-json +types loop
  types-text types-length @ ;
variable block-items  variable block-item  variable type-numbers
: types-of ( record -- list record ) dup block-types @ swap ;
: on-block ( record -- outcome )
  dup types-of list-count block-items ! 3 swap types-of list-item block-item ! outcome-ok ;
: renumbers ( record -- outcome )
  dup record-index @ type-numbers +! 99 swap record-index ! outcome-ok ;
: four-type-block ( -- outcome ) s" " s" " four-types block-of feed ;
T{ 0 type-numbers ! ' on-block kind-inductive ex export-handler !
   ' renumbers kind-type ex export-handler ! four-type-block
   block-items @ block-item @ type-numbers @ -> outcome-ok 4 -1 6 }T
\ A handler must not write its record, and what it writes there changes
\ nothing the reader does next. A block's lists are found again in the
\ line's JSON view: a handler that points block-ctors at an empty array
\ of the same line (the third review's probe, which once handed no
\ constructor over) and spoils the other two lists still gets every
\ element handed over. A changed kind changes nothing either: the reader
\ read it before the handler.
: empty-array? ( index -- flag ) json-array ex export-json json-items-of if 0= else false then ;
: empty-list ( -- list )
  ex export-json json-count @ 0 do i empty-array? if i invert unloop exit then loop -1 ;
variable redirected
: redirects ( record -- outcome )
  empty-list dup redirected ! over block-ctors ! 0 over block-types !
  -1 swap block-recursors ! outcome-ok ;
: makes-block ( record -- outcome ) kind-inductive swap record-kind ! outcome-ok ;
T{ capture-all ' redirects kind-inductive ex export-handler ! 0 calls !
   ctor-json rec-json type-json block-of feed calls @ redirected @ -1 <> -> outcome-ok 3 true }T
T{ 0 kind-at 1 kind-at 2 kind-at -> kind-type kind-ctor kind-recursor }T
T{ capture-all ' makes-block kind-thm ex export-handler ! 0 calls ! plain-thm feed calls @
   -> outcome-ok 0 }T
\ Only a handler that writes the export's JSON view can lose a list, here
\ the constructors (token 3 is the key "ctors"): that is invalid, and
\ nothing after the types is handed over.
: hides-ctors ( record -- outcome ) drop 0 3 ex export-json json-token token-size ! outcome-ok ;
T{ capture-all ' hides-ctors kind-inductive ex export-handler ! 0 calls !
   ctor-json rec-json type-json block-of feed why s" handler changed the export" compare
   calls @ 0 kind-at -> outcome-invalid 0 1 kind-type }T
T{ capture-all ctor-json rec-json type-json block-of feed -> outcome-ok }T
\ In a block's walk too, only the caller's data lies under the canaries.
\ A constructor handler that reaches four cells down and puts a visit
\ that skips its items there (the fourth review's probe, which once
\ replaced the list's visit, so that a constructor was skipped and the
\ line ok), and a type handler that reaches three cells down and puts
\ another export there, change only their caller's cells, and every
\ element is handed over.
: skips ( item x export -- outcome ) 2drop drop outcome-ok ;
0 ' skips visit: skipper
: two-of ( c-addr u -- c-addr u )
  0 types-length ! 2dup +types s" ," +types +types types-text types-length @ ;
: two-ctor-block ( -- c-addr u ) ctor-json two-of rec-json type-json block-of ;
T{ skipper ' reaches-four-once kind-ctor reaches 0 calls !
   55 66 two-ctor-block feed calls @ -> skipper 66 outcome-ok 5 }T
T{ capture-all other ' reaches-three-once kind-type reaches 0 calls !
   66 two-ctor-block feed calls @ -> other outcome-ok 5 }T
T{ capture-all other export-free -> }T

\ A rule record's header: kind-rule, the rule's index, the line and the
\ export. Kept after its handler, a recursor's rules are gone once the next
\ line is read: recursor-rule then gives 0 and leaves export-error as it
\ was, even after a failed line.
: marks ( -- key-u why-u ) ex export-error nip >r nip nip r> ;
: head@ ( record -- kind index export line )
  >r r@ record-kind @ r@ record-index @ r@ record-export @ r> record-line @ ;
T{ capture-all ctor-json rec-json type-json block-of feed kind@ -> outcome-ok kind-recursor }T
T{ 1 snap recursor-rule head@ snap record-line @ = -> kind-rule 1 ex true }T
\ Expression n (10 or 11, two digits), whose data holds one-item arrays,
\ one of them at the token index of the kept recursor's rules (tokens 0
\ to 8 lead to the data's array), and whose expr is e.
create kept /record allot  snap kept /record move
: stale-index ( -- index ) kept recursor-rules @ invert ;
: arrays-line ( n e -- c-addr u )
  swap 0 block-length ! s\" {\"ie\":" +block-text 0 <# #s #> +block-text
  s\" ,\"mdata\":{\"data\":{\"k\":[" +block-text stale-index 1 and 0= if s" 0," +block-text then
  40 0 do s" [0]," +block-text loop s\" [0]]},\"expr\":" +block-text
  0 <# #s #> +block-text s" }}" +block-text block-text block-length @ ;
T{ 10 0 arrays-line feed stale-index ex export-json json-kind-at -> outcome-ok json-array }T
T{ 0 kept recursor-rule marks -> 0 0 0 }T
\ Its lists are gone too: one of those arrays lies at the index of its
\ all list, and is not read as that list.
: all-index ( -- index ) kept recursor-all @ invert ;
T{ all-index ex export-json json-kind-at kept recursor-all @ kept list-count
   0 kept recursor-all @ kept list-item -> json-array 0 -1 }T
T{ 11 99 arrays-line feed stale-index ex export-json json-kind-at -> outcome-invalid json-array }T
T{ 0 kept recursor-rule failed-field s" expr" compare why s" bad reference" compare -> 0 0 0 }T
\ Nor are objects shaped like rules at the index of its rules (the fourth
\ review's probe once read one as rule 0, of 77 fields): not a line later,
\ and not at the same line number given again after export-restart.
\ Expression n is an mdata whose data holds one-rule arrays, eight tokens
\ each from token 9 on, one of them at the index.
: rule-array ( -- c-addr u ) s\" [{\"ctor\":1,\"nfields\":77,\"rhs\":0}]," ;
: rule-items ( -- )
  stale-index 9 - 8 mod 0 ?do s" 0," +block-text loop
  stale-index 8 / 2 + 0 do rule-array +block-text loop ;
: rules-line ( n -- c-addr u )
  0 block-length ! s\" {\"ie\":" +block-text 0 <# #s #> +block-text
  s\" ,\"mdata\":{\"data\":{\"k\":[" +block-text rule-items
  s\" 0]},\"expr\":0}}" +block-text block-text block-length @ ;
: rule-there ( -- kind ) stale-index 1+ ex export-json json-kind-at ;
T{ 11 rules-line feed rule-there 0 kept recursor-rule -> outcome-ok json-object 0 }T
\ From export-restart, sorts up to the line before the kept recursor's.
: fed-to ( line -- outcome )
  prefix swap 1- ex export-at @ ?do ex export-exprs @ sort-line feed or loop ;
T{ kept record-line @ fed-to ex export-exprs @ rules-line feed -> outcome-ok outcome-ok }T
T{ ex export-at @ kept record-line @ = rule-there 0 kept recursor-rule
   -> true json-object 0 }T

\ The tap (export-tap!, for the manifest check): shown every line that
\ export-read reads, once and before decoding, with the cell given; each
\ followed by a line feed, they are the whole file. Nothing given to
\ export-line is shown; a THROW from the tap passes on with the file
\ closed; export-init removes the tap.
create tapped 4096 allot
variable tapped-size
variable tap-cells   \ cells given to the tap that were not 4242
: tap-copy ( c-addr u -- ) tuck tapped tapped-size @ + swap move tapped-size +! ;
: tap-line ( c-addr u x -- ) 4242 <> 1 and tap-cells +! tap-copy s\" \n" tap-copy ;
create file-copy 4096 allot
: file-read ( c-addr u -- c-addr' u' )
  r/o bin open-file throw >r file-copy 4096 r@ read-file throw r> close-file throw
  file-copy swap ;
: tap-fresh ( -- ) 0 tapped-size ! 0 tap-cells ! 4242 ['] tap-line ex export-tap! ;
T{ capture-all tap-fresh s" tests/reference/composition.ndjson" read-fixture -> outcome-ok 35 }T
T{ tapped tapped-size @ s" tests/reference/composition.ndjson" file-read compare tap-cells @
   -> 0 0 }T
T{ tap-fresh s" tests/core/ndjson-block.ndjson" read-fixture -> outcome-ok 19 }T
T{ tapped-size @ tapped tapped-size @ s" tests/core/ndjson-block.ndjson" file-read compare -> 1362 0 }T
T{ tap-fresh fresh s\" {\"meta\":{}}" feed drop tapped-size @ -> 0 }T
: tap-throws ( c-addr u x -- ) drop 2drop 99 throw ;
T{ 0 ' tap-throws ex export-tap! s" tests/reference/composition.ndjson" ex ' export-read catch
   nip nip nip ex export-reader reader-fid @ ex export-busy @ -> 99 0 0 }T
T{ tap-fresh ex export-init ex export-tap @ ex export-tap-x @ -> outcome-ok 0 0 }T
capture-all

\ Indices as Lean's reader takes them (lean4export's Export.Parse): any
\ natural number in any order; an index given again names the new record
\ from then on; each reference is the ordinal its index has when it is
\ read. Records are handed over under their family's next ordinal.
T{ started ex export-map-bytes -> outcome-ok 0 }T
T{ s\" {\"in\":7,\"str\":{\"pre\":0,\"str\":\"a\"}}" feed index@ ex export-names @
   -> outcome-ok 1 2 }T
T{ ex export-map-bytes 0> -> true }T
T{ s\" {\"in\":3,\"str\":{\"pre\":7,\"str\":\"b\"}}" feed index@ snap name-prefix @
   -> outcome-ok 2 1 }T
\ 7 again: its own prefix is the old 7; from then on 7 is the new one.
T{ s\" {\"in\":7,\"str\":{\"pre\":7,\"str\":\"c\"}}" feed index@ snap name-prefix @
   -> outcome-ok 3 1 }T
T{ s\" {\"in\":9,\"str\":{\"pre\":7,\"str\":\"d\"}}" feed snap name-prefix @ -> outcome-ok 3 }T
\ 0, the anonymous name, given again: a reference to 0 names the new
\ record, which is not anonymous; ordinal 0 stays the anonymous name.
T{ s\" {\"in\":0,\"str\":{\"pre\":0,\"str\":\"e\"}}" feed index@ snap name-prefix @
   -> outcome-ok 5 0 }T
T{ s\" {\"il\":5,\"param\":0}" feed index@ snap param-name @ -> outcome-ok 1 5 }T
\ Level 0 given again: its succ is of level zero, then 0 is the new level.
T{ s\" {\"il\":0,\"succ\":0}" feed index@ snap succ-of @ -> outcome-ok 2 0 }T
T{ s\" {\"ie\":4,\"sort\":0}" feed index@ snap sort-level @ -> outcome-ok 0 2 }T
T{ s\" {\"ie\":4,\"bvar\":1}" feed index@ -> outcome-ok 1 }T
T{ s\" {\"app\":{\"arg\":4,\"fn\":4},\"ie\":2}" feed index@ snap app-fn @ snap app-arg @
   -> outcome-ok 2 1 1 }T
\ No reference to an index no record has, nor to one beyond a cell, nor
\ to the record's own index before it has it.
: bad-sparse ( c-addr u -- outcome ) feed ex export-exprs @ 3 <> if drop -9 then ;
T{ s\" {\"app\":{\"arg\":5,\"fn\":4},\"ie\":6}" bad-sparse failed-field s" arg" compare
   -> outcome-invalid 0 }T
T{ s\" {\"app\":{\"arg\":6,\"fn\":4},\"ie\":6}" bad-sparse -> outcome-invalid }T
T{ s\" {\"app\":{\"arg\":123456789012345678901234567890,\"fn\":4},\"ie\":6}" bad-sparse
   why s" bad reference" compare -> outcome-invalid 0 }T
T{ s\" {\"ie\":4294967295,\"sort\":0}" feed index@ -> outcome-ok 3 }T
T{ s\" {\"app\":{\"arg\":4294967295,\"fn\":4},\"ie\":0}" feed snap app-arg @ -> outcome-ok 3 }T
\ A record its handler refuses gives its index nothing.
T{ refuse-app s\" {\"app\":{\"arg\":4,\"fn\":4},\"ie\":8}" feed allow-app
   s\" {\"app\":{\"arg\":8,\"fn\":4},\"ie\":9}" feed -> outcome-unsupported outcome-invalid }T
\ export-restart empties the maps: 7 is no name's index again, and
\ indices that are their ordinals keep nothing.
T{ started s\" {\"in\":1,\"str\":{\"pre\":7,\"str\":\"x\"}}" feed -> outcome-ok outcome-invalid }T
T{ s\" {\"in\":1,\"str\":{\"pre\":0,\"str\":\"x\"}}" feed index@ -> outcome-ok 1 }T
\ An index that was its ordinal, given again, then keeps its new ordinal.
T{ 0 sort-line feed 1 sort-line feed s\" {\"bvar\":0,\"ie\":0}" feed index@
   -> outcome-ok outcome-ok outcome-ok 2 }T
T{ s\" {\"app\":{\"arg\":1,\"fn\":0},\"ie\":3}" feed snap app-fn @ snap app-arg @
   -> outcome-ok 2 1 }T

\ The tally (export-kind-count): records handed over and accepted, by
\ kind, with a block's types, constructors and recursors; reset when a
\ reading starts; a refused record is not counted; only a record kind.
: tallies ( k1 .. kn n -- c1 .. cn ) dup 0 ?do >r r@ 1- roll ex export-kind-count r> loop drop ;
T{ s" tests/reference/composition.ndjson" read-fixture drop kind-meta kind-name-str kind-name-num
   kind-sort kind-app kind-lam kind-forall kind-bvar kind-thm kind-def 10 tallies
   -> outcome-ok 1 11 1 1 2 6 7 5 1 0 }T
T{ s" tests/core/ndjson-block.ndjson" read-fixture drop
   kind-inductive kind-type kind-ctor kind-recursor kind-thm 5 tallies -> outcome-ok 1 2 2 1 1 }T
T{ ex export-restart kind-inductive ex export-kind-count -> 0 }T
T{ refuse-app s" tests/reference/composition.ndjson" read-fixture drop
   kind-app ex export-kind-count kind-forall ex export-kind-count 0<> -> outcome-unsupported 0 true }T
allow-app
T{ kind-count ex ' export-kind-count catch nip nip -1 ex ' export-kind-count catch nip nip
   -> -2 -2 }T

\ export-handler takes only a record kind.
T{ kind-count ex ' export-handler catch nip nip -1 ex ' export-handler catch nip nip -> -2 -2 }T
T{ kind-recursor ex export-handler ex export-handlers - -> kind-recursor cells }T

\ export-init again frees the old buffers and the index maps, and refuses
\ every kind; while it is ready, an export holds three heap blocks (the
\ line buffer, the token tape and the container stack), and none after
\ export-free. Here it also holds the three index maps the tests of
\ sparse indices made, a table and a slab each, which export-restart
\ empties but keeps.
: export-blocks ( -- n ) live-blocks @ blocks-at-start - ;
T{ export-blocks ex export-init kind-app ex export-handler @ ' export-refused = export-blocks
   -> 9 outcome-ok true 3 }T
T{ ex export-map-bytes -> 0 }T
T{ ex export-free ex export-json json-tape @ ex export-reader reader-buffer @ export-blocks
   -> 0 0 0 }T
cases-done
bye
