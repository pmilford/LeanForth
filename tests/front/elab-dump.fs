\ The declarations a natural LeanForth text makes, as the elaborator
\ (src/front/elab-decl.fs) builds them: for each, "NAME type SX" and
\ "NAME value SX", SX the S-expression of tests/front/s1-now.lean's
\ printer ((app F A), (lam T B), (pi T B), #i, Name.{levels}, Sort l, a
\ literal's value; (let T V B) and (let-nd T V B), batch-b.lean's; (proj S i E),
\ simp-2.lean's), so tests/front/check_elab.py compares them with pinned
\ Lean's node for node. The library and its elaboration data are the S1
\ slice's (run mode, as the command line binds them).
\ Usage: gforth tests/front/elab-dump.fs -e 's" FILE.lf" elab-dump bye'
require ../../src/load/checker.fs
require ../../src/load/front.fs
require ../../src/cli/check-lf.fs
decimal

\ The S1 slice by default; s2-dump uses S2's (tests/front/check_s2.py).
defer dump-lib ( -- c-addr u )
defer dump-data ( -- c-addr u )
:noname s" tests/front/s1-slice.ndjson" ; is dump-lib
:noname s" tests/front/s1-slice.elab.ndjson" ; is dump-data
: dump-must ( outcome -- ) ok? 0= abort" elab-dump: a loading step failed" ;
: .nm ( name -- ) dup lf-name-prefix@ ?dup if recurse ." ." then lf-name-text type ;
: .lv ( level -- )
  0 swap begin dup lf-level-tag@ lf-level-tag-succ = while lf-level-first@ swap 1+ swap repeat
  lf-level-tag@ lf-level-tag-zero = if 0 .r else drop ." ?l" then ;
: .levels ( slot -- )
  lf-cref-pairs 0 ?do i if ." ," then dup i lf-cref-pair@ drop .lv loop drop ;
: .const ( t -- ) lf-term-first@ lf-cref-slot dup lf-cref-name@ drop .nm ." .{" .levels ." }" ;
defer .t
: .pair ( t c-addr u -- ) ." (" type space dup lf-term-first@ .t space lf-term-second@ .t ." )" ;
\ A let, LET (v, fun x : T => b), as Lean's letE x T v b: (let T v b),
\ (let-nd T v b) for a have (tests/front/tactics/batch-b/batch-b.lean).
: .let ( t c-addr u -- )
  ." (" type space dup lf-term-second@ dup lf-term-first@ .t space swap lf-term-first@ .t
  space lf-term-second@ .t ." )" ;
\ A projection e.i of the structure S, as Lean's proj S i e: (proj S i e).
: .proj ( t -- )
  ." (proj " dup lf-proj-leaf dup lf-proj-name .nm space lf-proj-idx 0 .r space
  lf-proj-struct .t ." )" ;
:noname ( t -- )
  dup lf-term-tag@ lf-tag-symbolic-sort = if ." Sort " lf-term-first@ .lv exit then
  dup lf-lit-leaf? if lf-lit-cell 0 .r exit then
  dup lf-term-tag@ case
    lf-tag-let of s" let" .let endof  lf-tag-let-nondep of s" let-nd" .let endof
    lf-tag-app of s" app" .pair endof  lf-tag-lam of s" lam" .pair endof
    lf-tag-pi of s" pi" .pair endof  lf-tag-bvar of ." #" lf-term-first@ 0 .r endof
    lf-tag-constant of .const endof  lf-tag-projection of .proj endof
    >r drop ." ??" r> endcase ; is .t
: .decl ( decl -- )
  dup lf-fdecl-name @ .nm ."  type " dup lf-fdecl-type @ .t cr
  dup lf-fdecl-name @ .nm ."  value " lf-fdecl-value @ .t cr ;
: dump-own ( i -- ) dup lfa-library? if drop else lf-author-decl .decl then ;
: elab-dump ( c-addr u -- )
  dump-lib true lfc-library-open dump-must
  dump-data ck-stage ck-stage stage-manifest manifest-digest elab-read dump-must
  lfc-rooms dump-must lf-author-begin lf-author-file
  dup ok? 0= if ." stopped: " lf-author-error. cr drop exit then drop
  lf-author-count 0 ?do i dump-own loop ;
: s2-dump ( c-addr u -- )
  [: s" tests/front/s2-slice.ndjson" ;] is dump-lib
  [: s" tests/front/s2-slice.elab.ndjson" ;] is dump-data elab-dump ;
\ by-decide's slice (tests/front/tactics/decide/check.py; plan S3a).
: decide-dump ( c-addr u -- )
  [: s" tests/front/decide-slice.ndjson" ;] is dump-lib
  [: s" tests/front/decide-slice.elab.ndjson" ;] is dump-data elab-dump ;
\ Simp's slice (tests/front/tactics/simp-1/check.py; plan row FE9).
: simp-dump ( c-addr u -- )
  [: s" tests/front/simp-slice.ndjson" ;] is dump-lib
  [: s" tests/front/simp-slice.elab.ndjson" ;] is dump-data elab-dump ;
\ The case patterns' slice (tests/front/tactics/batch-h2/check.py; plan
\ row TB2, piece E).
: patterns-dump ( c-addr u -- )
  [: s" tests/front/patterns-slice.ndjson" ;] is dump-lib
  [: s" tests/front/patterns-slice.elab.ndjson" ;] is dump-data elab-dump ;
\ The command line's own check, after src/main.fs, each declaration of
\ the text printed as it is handed to the kernel (lf-front-closing runs
\ with the type and value below it; decide's check.py --init, against
\ Init's snapshot, plan S3a-ops); its exit code:
\   gforth-fast src/main.fs tests/front/elab-dump.fs -e "cli-dump (bye)" check ...
\ Only after src/main.fs, which has the command line.
[defined] cli-line [if]
variable dump-real
: dump-handed ( type value -- type value )
  lfa-this lf-fdecl-name @ dup .nm ."  type " 2 pick .t cr .nm ."  value " dup .t cr ;
: dump-closing ( type value -- type value ) dump-real @ execute dump-handed ;
: cli-dump ( -- code )
  action-of lf-front-closing dump-real ! ['] dump-closing is lf-front-closing cli-line ;
[then]
