\ Hostile and edge inputs for the draft IR v1 words (v1.fs), in either
\ design: set adv-mode to cv-run or ms-run before loading. Each line prints
\ the input, then the diagnostic, or "ok" for the few meant to pass.
true cv-quiet !
variable accepted  variable refused
: adv ( c-addr u -- )
  false region ! 0 kv# !
  ." [" 2dup type ." ]  " s" t.fs" adv-mode execute cv-ok = if ." ok" cr 1 accepted +! else
  1 refused +! then ;
s" : f do ;" adv                 s" : f loop ;" adv              s" : f i ;" adv
s" : f 2 0 do j loop ;" adv      s" : f leave ;" adv             s" : f begin until until ;" adv
s" : f if do then loop ;" adv    s" : f 2 0 do if loop then ;" adv
s" : f 2 0 do i leave loop ;" adv
s" : g create , does> @ ; : f 5 g x ;" adv
s" : g create dup , , does> @ ; 5 g x" adv
s" : g create , does> @ ; g x" adv
s" : g create , does> @ ; 1 2 g x" adv
s" : g create , does> if ; then" adv
s" create t 1 2 ," adv            s" 1 ," adv                      s" variable v 5 v !" adv
s" create t 1 , : f t 1 cells + @ ;" adv
s" : f recurse ;" adv            s" recurse" adv
cr .( v1 adversarial: ) accepted @ . .( accepted, ) refused @ . .( refused) cr
bye
