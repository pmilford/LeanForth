\ Adversarial inputs for correctness mode, beyond today's reader tests
\ (reader_cases.py replays those): Gforth 1.0's recognizer syntaxes and
\ every other number syntax, Forth words that change the interpreter or
\ compile, forged control structure, names, and a run started while Forth
\ is compiling. Each line prints the input, then the diagnostic, or "ok"
\ for the few that are meant to pass. Usage: gforth cv.fs adversarial.fs
true cv-quiet !
variable accepted  variable refused
: adv ( c-addr u -- )
  ." [" 2dup type ." ]  " s" t.fs" cv-run cv-ok = if ." ok" cr 1 accepted +! else
  1 refused +! then ;
\ A. Recognizer and number syntaxes inside a definition (Gforth 1.0 reads
\ most of these as values; 0.7.3 some): all refused at the token.
s\" : f \"x\" ;" adv            s\" : f \"x dup y\" ;" adv     s" : f `dup ;" adv
s" : f ``dup ;" adv             s" : f <dup> ;" adv            s" : f ->x ;" adv
s" : f +>x ;" adv               s" : f '>x ;" adv              s" : f ${HOME} ;" adv
s" : f forth:dup ;" adv         s" : f forth:bye ;" adv        s" : f 1. ;" adv
s" : f 1.5 ;" adv               s" : f .5 ;" adv               s" : f 1e ;" adv
s" : f 2p ;" adv                s" : f 'a' ;" adv              s" : f '' ;" adv
s" : f $10 ;" adv               s" : f #10 ;" adv              s" : f %10 ;" adv
s" : f &10 ;" adv               s" : f 0x10 ;" adv             s" : f 1_000 ;" adv
s" : f --5 ;" adv               s" : f +5 ;" adv               s" : f -2147483648 ;" adv
s" : f 2147483648 ;" adv        s" : f 18446744073709551616 ;" adv
s" -1 1e constant x" adv        s" 1. constant x" adv          s" $ff constant x" adv
\ B. Forth words that change the interpreter, compile, or reach the host.
s" : f immediate ;" adv         s" : f ; immediate" adv        s" : f postpone dup ;" adv
s" : f [ 1 throw ] ;" adv       s" : f ] ;" adv                s" : f ' dup ;" adv
s" : f ['] dup ;" adv           s" : f [ 5 ] literal ;" adv    s" state @ constant s" adv
s\" s\" bye\" evaluate" adv     s" hex : f 10 ;" adv           s" 16 base ! : f 10 ;" adv
s" bye" adv                     s" : f bye ;" adv              s" quit" adv
s" abort" adv                   s" :noname 1 ;" adv            s" : f does> ;" adv
s" : f recurse ;" adv           s" : f execute ;" adv          s\" : f s\" x\" ;" adv
s\" : f .\" hi\" ;" adv         s" .( hi)" adv                 s" : f char x ;" adv
s" marker m" adv                s" only forth" adv             s" forth-wordlist 1 set-order" adv
s" include /etc/passwd" adv     s" 0 0 ! 1 throw" adv          s" : f >in @ ;" adv
s" [defined] dup" adv           s" [if]" adv                   s" words" adv
\ C. Structure cannot be forged by a literal: frames are not on the stack.
s" : f 0 then ;" adv            s" : f 1 2 repeat ;" adv       s" : f if -1 ;" adv
s" : f begin 0 while 5 then ;" adv                             s" : f -1 if 1 then ;" adv
\ D. Names.
s" : dup ;" adv                 s" : DUP 1 ;" adv              s" : : ;" adv
s" : ; ;" adv                   s" : ( ;" adv                  s" : \ ;" adv
s" : foo 1 ; : bar foo ; : FOO 2 ;" adv                         s" : 5 7 ; : g 5 05 ;" adv
s" : x:dup 1 ; : g x:dup ;" adv s" : . drop ;" adv
\ E. Comments and lines.
s" : f ( no close ;" adv        s\" : f \\ ok ;\n;" adv         s" : f ) ;" adv
s\" : f\nf ;" adv               s\" :\nf ;" adv
\ F. A run started while Forth is compiling: refused before any line runs.
: while-compiling ( -- ) s" : f dup ;" adv ; immediate
: host-word ( -- ) while-compiling ;
cr .( adversarial: ) accepted @ . .( accepted, ) refused @ . .( refused) cr
bye
