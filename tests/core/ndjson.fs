\ Unit tests of src/import/ndjson.fs: every record kind of lean4export
\ format 3.1.0 decoded failed-field by failed-field, the metadata rules, and for each
\ kind the malformed, unsupported and limit cases that must fail closed;
\ handler outcomes; list and rule readers; whole fixture files.
\ Lines are fed one at a time to export-line from memory; file framing is
\ tested by tests/core/test_ndjson_reader.py on temporary files.
include ../support/tester.fs
include ../support/checks.fs
require ../../src/import/ndjson.fs

decimal
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
T{ s\" {\"in\":5,\"str\":{\"pre\":0,\"str\":\"y\"}}" bad-name why s" bad or out-of-order index" compare
   -> outcome-invalid 0 }T
T{ s\" {\"in\":3,\"str\":{\"pre\":0,\"str\":\"y\"}}" bad-name -> outcome-invalid }T
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
T{ s\" {\"il\":6,\"succ\":0}" bad-level -> outcome-invalid }T

\ Expressions: every kind, then the failures.
T{ s\" {\"ie\":0,\"sort\":4}" feed kind@ index@ snap sort-level @ -> outcome-ok kind-sort 0 4 }T
T{ s\" {\"bvar\":3,\"ie\":1}" feed kind@ snap bvar-index @ -> outcome-ok kind-bvar 3 }T
T{ s\" {\"const\":{\"name\":1,\"us\":[0,4,2]},\"ie\":2}" feed kind@ snap const-name @ -> outcome-ok kind-const 1 }T
T{ snap const-levels @ snap list-count 1 snap const-levels @ snap list-item -> 3 4 }T
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
T{ s\" {\"app\":{\"arg\":1,\"fn\":0},\"ie\":13}" bad-expr -> outcome-invalid }T
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

\ An inductive block-text: the block-text, then its types, constructors and recursors.
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
T{ ex export-decls @ -> 7 }T
: bad-block ( c-addr u c-addr u c-addr u -- outcome ) block-of feed ex export-decls @ 7 <> if drop -9 then ;
T{ s" " s" " s" " bad-block why s" inductive block without types" compare -> outcome-invalid 0 }T
T{ ctor-json rec-json s" 1" bad-block -> outcome-invalid }T
T{ ctor-json s\" {\"all\":[1]}" type-json bad-block -> outcome-invalid }T
T{ s\" {\"cidx\":0,\"induct\":0,\"isUnsafe\":false,\"levelParams\":[],\"name\":2,\"numFields\":2,\"numParams\":1,\"type\":3}"
   rec-json type-json bad-block -> outcome-invalid }T
T{ ctor-json s\" {\"all\":[1],\"isUnsafe\":false,\"k\":true,\"levelParams\":[3],\"name\":4,\"numIndices\":0,\"numMinors\":1,\"numMotives\":1,\"numParams\":1,\"rules\":[{\"ctor\":2,\"nfields\":2,\"rhs\":13}],\"type\":0}"
   type-json bad-block failed-field s" rhs" compare -> outcome-invalid 0 }T

\ Handlers: a missing one is unsupported; their outcomes stop reading.
: refuse-app ( -- ) ['] export-refused kind-app ex export-handler ! ;
: allow-app ( -- ) ['] capture kind-app ex export-handler ! ;
: says-rejected ( record -- outcome ) drop outcome-rejected ;
: says-garbage ( record -- outcome ) drop 77 ;
T{ refuse-app s\" {\"app\":{\"arg\":1,\"fn\":2},\"ie\":13}" feed ex export-exprs @ -> outcome-unsupported 13 }T
T{ ' says-rejected kind-app ex export-handler ! s\" {\"app\":{\"arg\":1,\"fn\":2},\"ie\":13}" feed -> outcome-rejected }T
T{ ' says-garbage kind-app ex export-handler ! s\" {\"app\":{\"arg\":1,\"fn\":2},\"ie\":13}" feed -> outcome-invalid }T
T{ allow-app s\" {\"app\":{\"arg\":1,\"fn\":2},\"ie\":13}" feed ex export-exprs @ -> outcome-ok 14 }T

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
T{ refuse-app s" tests/reference/composition.ndjson" read-fixture drop ex export-error 2drop 2drop -> outcome-unsupported 27 }T
T{ allow-app s" tests/reference/composition.ndjson" ex ' export-read rs-checked -> outcome-ok }T
\ The end of input needs metadata and a declaration.
T{ fresh ex export-end why s" missing metadata or declaration" compare -> outcome-invalid 0 }T
T{ started ex export-end -> outcome-ok outcome-invalid }T

T{ ex export-free ex export-json json-tape @ ex export-reader reader-buffer @ -> 0 0 }T
cases-done
bye
