\ Throwaway probe for ADR 0019, mode shift option (b) on Gforth 1.0 only:
\ a real third state of Gforth's own text interpreter. translate-method:
\ adds a "verifying" action to every translation (Gforth 1.0's
\ recognizer results); in that state the interpreter performs it for each
\ token. Only two translations get one here: a found word (the
\ verification semantics of ms.fs's table, by the word's identity) and a
\ single-cell number (checked against its text). Every other translation
\ (strings, floats, doubles, ->x, ${NAME}, ...) keeps Gforth's default
\ for an unset method, which throws -13, so it is refused. gforth-
\ experimental words; does not load on 0.7.3.
\ Usage: gforth cv.fs ms.fs ms-gforth1.fs -e 's" FILE" g1-run-file ...'

translate-method: verifying ( ... translation -- ... )
: g1-token ( -- ) cv-token-end dup cv-token-start dup cv-tok ! - cv-tok# ! ;
: g1-read ( -- ) cv-in cv-synced ! ;
\ Gforth 1.0 also finds words through other token forms (forth:dup is
\ FORTH's DUP), which 0.7.3 does not read: only a token that is the
\ word's own name, found by itself, is accepted.
: g1-plain? ( nt c-addr u -- flag )
  forth-wordlist search-wordlist if swap name>interpret = else drop false then ;
translate-name :method verifying ( nt -- )
  g1-token cv-token 2dup cv-prog @ search-wordlist
  if nip nip nip >body cv-call g1-read exit then
  rot >r 2dup r> -rot g1-plain? 0= if 2drop why-unknown cv-unsupported! then
  2dup forth-wordlist search-wordlist drop ms-host g1-read ;
translate-cell :method verifying ( n -- )
  g1-token cv-token cv-literal? 0= if drop why-unknown cv-unsupported! then
  over <> if drop why-host-literal cv-invalid! then cv-lit g1-read ;

\ A line in verifying state; Gforth's own INTERPRET reads it.
: g1-run-line ( c-addr u -- )
  1 cv-line# +! 0 cv-synced ! 0 cv-out# !
  dup 128 < 0= if 2drop s" " 0 why-unreadable cv-invalid cv-fail then
  cv-line-len ! cv-line-addr ! cv-check-chars
  ['] verifying set-state cv-text ['] evaluate catch ['] interpreting set-state throw
  depth cv-base @ <> if s" " 0 why-interrupted cv-invalid cv-fail then ;
: g1-lines ( -- )
  begin cv-rest 2@ nip while cv-split if cv-cr then g1-run-line repeat cv-end-of-text ;
: g1-run ( c-addr u c-addr2 u2 -- outcome )
  cv-reset cv-quiet @ if 2drop else ." lf-ir 0.1" cr ." source " type cr then cv-rest 2!
  state @ if s" " 0 why-compiling cv-invalid cv-report cv-outcome @ exit then
  cv-save cv-prog @ forth-wordlist 2 set-order decimal depth cv-base ! 0 cv-in-offset !
  ['] g1-lines catch ?dup if cv-caught then cv-restore cv-outcome @ ;
: g1-run-file ( c-addr u -- outcome )
  2dup cv-slurp 0= if 2drop -1 exit then 2swap g1-run ;
