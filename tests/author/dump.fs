\ Test support: a tree dump of a declaration, written without the term
\ printer, so that the round trip compares terms by an independent path:
\ every node, de Bruijn index, level, constant name and universe argument,
\ binder name and kind, and every label and note with its kind. Source
\ positions are not dumped (the printed layout differs from the input).
\ Output goes to dump-out ( c-addr u -- ), which the caller sets.
\ Test-only; not a public interface.
require ../../src/author/runner.fs

defer dump-out ( c-addr u -- )
: d ( c-addr u -- ) dump-out ;
: d# ( n -- ) base @ >r decimal dup abs 0 <# #s rot sign #> r> base ! d ;

\ Names: parts joined by dots, a numeric part as #n.
: dump-part ( id -- )
  dup lf-name-tag@ lf-name-tag-str = if lf-name-text d else s" #" d lf-name-payload d# then ;
: dump-name ( id -- )
  dup 0= if drop s" [anonymous]" d exit then
  dup lf-name-prefix@ ?dup if recurse s" ." d then dump-part ;

: dump-level ( l -- )
  dup lf-level-tag@ case
    lf-level-tag-zero of drop s" 0" d endof
    lf-level-tag-succ of s" (succ " d lf-level-first@ recurse s" )" d endof
    lf-level-tag-max of s" (max " d dup lf-level-first@ recurse s"  " d lf-level-second@
      recurse s" )" d endof
    lf-level-tag-imax of s" (imax " d dup lf-level-first@ recurse s"  " d lf-level-second@
      recurse s" )" d endof
    lf-level-tag-param of s" (param " d lf-level-first@ dump-name s" )" d endof
    s" (bad level)" d nip endcase ;

: dump-note ( i -- )
  s"  [" d dup lf-note-kind@ d# s" :" d lf-note-text@ d s" ]" d ;
: dump-notes ( term -- )
  lf-note-count 0 ?do dup i lf-note-on? if i dump-note then loop drop ;
: dump-binder ( term -- )
  lf-pres-binder@ if s"  " d swap dump-name s"  " d d# else s"  (no entry)" d then ;
: dump-levels ( addr n -- ) 0 ?do s"  " d dup i lf-cref-pair@ drop dump-level loop drop ;
: dump-const ( term -- )
  s" (const " d dup lf-term-first@ swap lf-term-second@ 2dup lf-cref-read
  0= abort" dump: stale reference" 2drop dump-name lf-cref-levels drop dump-levels s" )" d ;
defer dump-sub ( term -- )
: dump-node ( term -- )
  dup lf-term-tag@ case
    lf-tag-bvar of s" #" d lf-term-first@ d# endof
    lf-tag-sort of s" (Sort# " d lf-term-first@ d# s" )" d endof
    lf-tag-symbolic-sort of s" (Sort " d lf-term-first@ dump-level s" )" d endof
    lf-tag-constant of dump-const endof
    lf-tag-app of s" (app " d dup lf-term-first@ dump-sub s"  " d lf-term-second@ dump-sub
      s" )" d endof
    lf-tag-lam of s" (lam" d dup dump-binder s"  " d dup lf-term-first@ dump-sub s"  " d
      lf-term-second@ dump-sub s" )" d endof
    lf-tag-pi of s" (pi" d dup dump-binder s"  " d dup lf-term-first@ dump-sub s"  " d
      lf-term-second@ dump-sub s" )" d endof
    s" (bad term)" d nip endcase ;
: dump-term ( term -- ) dup 0< if drop s" none" d exit then dup dump-node dump-notes ;
' dump-term is dump-sub

create dump-eol 10 c,
: dump-decl ( decl -- )
  dup lf-fdecl-kind @ d# s"  " d dup lf-fdecl-name @ dump-name
  dup lf-fdecl-universes @ 0 ?do s"  u:" d dup lf-fdecl-universe i cells + @ dump-name loop
  dump-eol 1 d s"   type " d dup lf-fdecl-type @ dump-term dump-eol 1 d
  s"   value " d lf-fdecl-value @ dump-term dump-eol 1 d ;
