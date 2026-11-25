\ Test support: a theorem with a tactic proof run as LeanForth text (plan
\ row TB1), so that a tactic's unit tests (tests/front/tactics/NAME/
\ test.fs) run its plug-in's words on both engines, not only its
\ end-to-end .lf files. tactic-ran ( c-addr1 u1 c-addr2 u2 -- code ): the
\ theorem t whose statement (binders and type) is the first text and whose
\ proof, after := by, is the second, run in a new authoring run; its
\ authoring error code, 0 when the kernel accepted it (the error is left
\ recorded: lf-tac-forget clears it). Include after src/load/checker.fs,
\ src/load/front.fs and src/cli/check-lf.fs (or src/main.fs), with the
\ library and its elaboration data open. text-full ( c-addr1 u1 c-addr2
\ u2 -- code outcome ): the same run as a sweep's pass (meta-sweeps.fs):
\ -1 and full when the run ended with a full store or heap, else its
\ code and ok (a refusal must never become another error). State:
\ test-only buffer; single-threaded.
create tt-text 1024 allot  variable tt-text#
: tt+ ( c-addr u -- ) tuck tt-text tt-text# @ + swap move tt-text# +! ;
: tactic-ran ( c-addr1 u1 c-addr2 u2 -- code )
  2>r 0 tt-text# ! s" theorem t " tt+ tt+ s"  := by " tt+ 2r> tt+ s"  end t" tt+
  lf-author-begin tt-text tt-text# @ lf-author-text drop lf-author-code ;
: full-code? ( code -- flag ) dup if lf-author-outcome outcome-full = then ;
: text-full ( c-addr u c-addr' u' -- code outcome )
  tactic-ran dup full-code? if drop -1 outcome-full else outcome-ok then ;
