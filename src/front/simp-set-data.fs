\ The default simp set's records (simp group 4, step 3; plan
\ .claude/work/briefs/simp-group-4-architect.md section 1;
\ docs/programming/ELABORATION_DATA.md, "Format 4.1: the default simp
\ set"; SIMP_DATA.md section 3): kinds of format 4.1 added to
\ front/elab-data.fs's reader (elab-add-kind41), written by
\ scripts/export_simp.lean and finished by scripts/export_simp.py.
\ Untrusted and fail-closed like the rest of the data: a lemma named here
\ is only tried, its keys recomputed when it is first tried
\ (simp/theorems.fs) and its use checked by the kernel; a refused record
\ refuses the whole file (elab-error gives its line and code).
\
\ simp_set: the default set alone, name ["simp"], its simprocs
\   ["simprocAttr"] (Lean's simpAttrNameToSimprocAttrName), once (else
\   error 52).
\ simp_lemma: a lemma of the set's pre (post false) or post tree: set
\   ["simp"] (52), origin a declaration, proof a theorem (12, 14), inv,
\   perm, rfl, backward_rfl booleans, priority, keys (one term, every
\   constant the library's), rank; its rfl flag must be its proof's defeq
\   tag (Lean's isRflProof of a constant, SimpTheorems.lean:232; error 50).
\ simp_left_out: a lemma whose origin or proof the library lacks: set,
\   post, priority, keys (a constant the library lacks a foreign key),
\   rank, origin and proof well-formed names not both the library's
\   (else 51), reason not_exported.
\ simp_unfold: a definition the set unfolds (toUnfold): set, name (a
\   declaration).
\ simproc: an entry of the default simproc set: name (a Lean function,
\   kept as a well-formed name only, whatever the library holds), keys
\   (foreign constants allowed), post, rank, dsimproc.
\ Members, names and numbers are checked as elab-data.fs checks them
\ (errors 10-14, 19; 22 for no room). Ranks are checked when a root is
\ built (front/data-index.fs: a gap or two values of one rank invalid).
\
\ simp-default? ( -- flag ): data of format 4.1 holding the simp_set
\ record, so the default set is Lean's; else simp answers unsupported.
\ A lemma value v is a simp_lemma record i (v = i >= 0) or a
\ simp_left_out record j (v = j invert): simp-lemmas# ( post -- n ) and
\ simp-lemma-value ( k post -- v ) the values of one tree in file order,
\ simp-lemma-keys ( v -- k n ), simp-lemma-rank ( v -- rank ),
\ simp-lemma-prio ( v -- p ); of a record i: simp-lemma-proof ( i -- d ),
\ simp-lemma-rfl? and simp-lemma-perm? ( i -- flag ); simp-lemma-count
\ ( -- n ). A simproc p: simp-procs# ( post -- n ), simp-proc-value ( k
\ post -- p ), simp-proc-keys ( p -- k n ), simp-proc-rank ( p -- rank ),
\ simp-proc-dsimproc? ( p -- flag ), simp-proc-count ( -- n ).
\ simp-unfold? ( d -- flag ): the set unfolds declaration d. Unchecked:
\ numbers below their counts.
\
\ State: the context slabs of the records (ss-lemmas, ss-lefts,
\ ss-procs, ss-unfolds) and of each tree's values in file order
\ (ss-pre, ss-post, ss-proc-pre, ss-proc-post), and the record ss (the
\ simp_set read); emptied by every reset of the data (the kinds' clears).
\ Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/slab.fs
require ./elab-data.fs
require ./simp-data.fs

begin-structure /ssl   \ a lemma, kept or left out
  /elab-value +field ssl-value   \ its keys and rank (elab-data.fs's)
  field: ssl-post   field: ssl-prio
  field: ssl-proof   field: ssl-rfl   field: ssl-perm   \ a kept lemma's
end-structure
begin-structure /ssp   \ a simproc entry
  /elab-value +field ssp-value   field: ssp-post   field: ssp-dsimproc
end-structure
begin-structure /ss  field: ss-set-read  end-structure
/ss context-record: ss
/ssl context-slab: ss-lemmas
/ssl context-slab: ss-lefts
/ssp context-slab: ss-procs
1 cells context-slab: ss-unfolds
1 cells context-slab: ss-pre
1 cells context-slab: ss-post
1 cells context-slab: ss-proc-pre
1 cells context-slab: ss-proc-post

: ssl ( i -- addr ) ss-lemmas slab-at ;
: ssj ( j -- addr ) ss-lefts slab-at ;
: ssp ( p -- addr ) ss-procs slab-at ;
: ss-or ( flag code -- outcome ) swap if drop outcome-ok else elab-refuse then ;
: ss-at! ( a-addr x outcome -- outcome ) ['] noop elab-put ;

\ ---- Members several kinds share.
\ A one-part name: the array of the one string c-addr u (error 52).
: ss-part-is ( item c-addr u -- outcome ) elab-text= elab-e-simp-set ss-or ;
: ss-simp-part ( item -- outcome ) s" simp" ss-part-is ;
: ss-attr-part ( item -- outcome ) s" simprocAttr" ss-part-is ;
: ss-one? ( index -- flag ) elab-items# if 1 = else false then ;
: ss-one-part ( index xt -- outcome )
  over ss-one? 0= if 2drop elab-e-simp-set elab-refuse exit then elab-array-items ;
: ss-set ( value i -- outcome ) drop c" set" elab-member ['] ss-simp-part ss-one-part ;
: ss-bool-at ( value addr c-addr -- outcome ) rot swap elab-member elab-bool ss-at! ;
: ss-flag ( value c-addr -- outcome ) elab-member elab-bool nip ;
: ss-u32-at ( value addr c-addr -- outcome ) rot swap elab-member elab-u32 ss-at! ;
: ss-keys ( value addr foreign? -- outcome )
  rot c" keys" elab-member swap elab-keys-read ;
: ss-rank ( value addr -- outcome ) swap c" rank" elab-member elab-value-rank! ;
: ss-phase ( v post -- outcome ) if ss-post else ss-pre then slab-push elab-roomed ;

\ ---- simp_set: the default set, once.
: sss-ready ( value i -- outcome ) 2drop ss ss-set-read @ 0= elab-e-simp-set ss-or ;
: sss-name ( value i -- outcome ) drop c" name" elab-member ['] ss-simp-part ss-one-part ;
: sss-procs ( value i -- outcome )
  drop c" simprocs" elab-member ['] ss-attr-part ss-one-part ;
: sss-read ( value i -- outcome ) 2drop true ss ss-set-read ! outcome-ok ;
1 cells context-slab: ss-sets   \ the records' units (the one read)
here 0 , ' ss-sets ,
  ' sss-ready , ' sss-name , ' sss-procs , ' sss-read , 0 , constant sss-form
sss-form elab-keys-here  s" name" counted, s" simprocs" counted, 0 0 counted,
: sss-clear ( -- ) ss-sets slab-clear false ss ss-set-read ! ;
sss-form ' sss-clear s" simp_set" elab-add-kind41 constant simp-set-kind

\ ---- simp_lemma.
: ssl-origin ( value i -- outcome ) drop c" origin" elab-member elab-decl nip ;
: ssl-proof! ( value i -- outcome )
  ssl ssl-proof swap c" proof" elab-member sd-theorem ss-at! ;
: ssl-post! ( value i -- outcome ) ssl ssl-post c" post" ss-bool-at ;
: ssl-rfl! ( value i -- outcome ) ssl ssl-rfl c" rfl" ss-bool-at ;
: ssl-perm! ( value i -- outcome ) ssl ssl-perm c" perm" ss-bool-at ;
: ssl-flags ( value i -- outcome )
  drop dup c" inv" ss-flag ok-then? if c" backward_rfl" ss-flag then ;
: ssl-prio! ( value i -- outcome ) ssl ssl-prio c" priority" ss-u32-at ;
: ssl-keys! ( value i -- outcome ) ssl ssl-value false ss-keys ;
: ssl-rank! ( value i -- outcome ) ssl ssl-value ss-rank ;
\ Lean's rfl flag of a constant proof is its defeq tag (error 50).
: ssl-tagged? ( i -- flag ) ssl ssl-proof @ elab-tag-defeq elab-tagged? ;
: ssl-rfl-tag ( value i -- outcome )
  nip dup ssl-tagged? swap ssl ssl-rfl @ = elab-e-simp-rfl ss-or ;
: ssl-phase ( value i -- outcome ) nip dup ssl ssl-post @ ss-phase ;
: ssl-clear ( -- ) ss-lemmas slab-clear ss-pre slab-clear ss-post slab-clear ;
here 0 , ' ss-lemmas ,
  ' ss-set , ' ssl-origin , ' ssl-proof! , ' ssl-post! , ' ssl-rfl! , ' ssl-perm! ,
  ' ssl-flags , ' ssl-prio! , ' ssl-keys! , ' ssl-rank! , ' ssl-rfl-tag , ' ssl-phase ,
  0 , constant ssl-form
ssl-form elab-keys-here
  s" backward_rfl" counted, s" inv" counted, s" keys" counted, s" origin" counted,
  s" perm" counted, s" post" counted, s" priority" counted, s" proof" counted,
  s" rank" counted, s" rfl" counted, s" set" counted, 0 0 counted,
ssl-form ' ssl-clear s" simp_lemma" elab-add-kind41 constant simp-lemma-kind

\ ---- simp_left_out: origin and proof well-formed, not both the
\ library's (error 51).
: ss-known ( index -- flag outcome )   \ true: a declaration has the name
  dup elab-name-shape ok-then? 0= if false swap exit then
  elab-name ok-then? if elab-has? outcome-ok else false swap then ;
: ss-member-known ( value c-addr -- flag outcome ) elab-member ss-known ;
: ss-both-known ( value -- flag outcome )
  dup c" origin" ss-member-known ok-then? 0= if nip false swap exit then
  swap c" proof" ss-member-known ok-then? if and outcome-ok else nip false swap then ;
: ssj-names ( value j -- outcome )
  drop ss-both-known ok-then? if 0= elab-e-simp-left ss-or then ;
: ssj-reason ( value j -- outcome )
  drop c" reason" elab-member s" not_exported" elab-text=
  if outcome-ok else elab-malformed then ;
: ssj-post! ( value j -- outcome ) ssj ssl-post c" post" ss-bool-at ;
: ssj-prio! ( value j -- outcome ) ssj ssl-prio c" priority" ss-u32-at ;
: ssj-keys! ( value j -- outcome ) ssj ssl-value true ss-keys ;
: ssj-rank! ( value j -- outcome ) ssj ssl-value ss-rank ;
: ssj-phase ( value j -- outcome ) nip dup ssj ssl-post @ swap invert swap ss-phase ;
: ssj-clear ( -- ) ss-lefts slab-clear ;
here 0 , ' ss-lefts ,
  ' ss-set , ' ssj-names , ' ssj-reason , ' ssj-post! , ' ssj-prio! , ' ssj-keys! ,
  ' ssj-rank! , ' ssj-phase , 0 , constant ssj-form
ssj-form elab-keys-here
  s" keys" counted, s" origin" counted, s" post" counted, s" priority" counted,
  s" proof" counted, s" rank" counted, s" reason" counted, s" set" counted, 0 0 counted,
ssj-form ' ssj-clear s" simp_left_out" elab-add-kind41 constant simp-left-kind

\ ---- simp_unfold: a declaration the set unfolds.
: ssu-name! ( value u -- outcome )
  ss-unfolds slab-at swap c" name" elab-member elab-decl ss-at! ;
: ssu-clear ( -- ) ss-unfolds slab-clear ;
here 0 , ' ss-unfolds ,  ' ss-set , ' ssu-name! , 0 , constant ssu-form
ssu-form elab-keys-here  s" name" counted, s" set" counted, 0 0 counted,
ssu-form ' ssu-clear s" simp_unfold" elab-add-kind41 constant simp-unfold-kind

\ ---- simproc: an entry of the default simproc set.
: ssp-name ( value p -- outcome ) drop c" name" elab-member elab-name-shape ;
: ssp-keys! ( value p -- outcome ) ssp ssp-value true ss-keys ;
: ssp-post! ( value p -- outcome ) ssp ssp-post c" post" ss-bool-at ;
: ssp-rank! ( value p -- outcome ) ssp ssp-value ss-rank ;
: ssp-dsimproc! ( value p -- outcome ) ssp ssp-dsimproc c" dsimproc" ss-bool-at ;
: ssp-phase ( value p -- outcome )
  nip dup ssp ssp-post @ if ss-proc-post else ss-proc-pre then slab-push elab-roomed ;
: ssp-clear ( -- ) ss-procs slab-clear ss-proc-pre slab-clear ss-proc-post slab-clear ;
here 0 , ' ss-procs ,
  ' ssp-name , ' ssp-keys! , ' ssp-post! , ' ssp-rank! , ' ssp-dsimproc! , ' ssp-phase ,
  0 , constant ssp-form
ssp-form elab-keys-here
  s" dsimproc" counted, s" keys" counted, s" name" counted, s" post" counted,
  s" rank" counted, 0 0 counted,
ssp-form ' ssp-clear s" simproc" elab-add-kind41 constant simp-proc-kind

\ ---- The questions.
: simp-default? ( -- flag ) elab-format41? ss ss-set-read @ and ;
: ss-values ( post -- slab ) if ss-post else ss-pre then ;
: simp-lemmas# ( post -- n ) ss-values slab-count ;
: simp-lemma-value ( k post -- v ) ss-values slab-at @ ;
: ss-lemma ( v -- addr ) dup 0< if invert ssj else ssl then ;
: simp-lemma-keys ( v -- k n ) ss-lemma ssl-value elab-value-keys ;
: simp-lemma-rank ( v -- rank ) ss-lemma ssl-value elab-value-rank@ ;
: simp-lemma-prio ( v -- p ) ss-lemma ssl-prio @ ;
: simp-lemma-proof ( i -- d ) ssl ssl-proof @ ;
: simp-lemma-rfl? ( i -- flag ) ssl ssl-rfl @ ;
: simp-lemma-perm? ( i -- flag ) ssl ssl-perm @ ;
: simp-lemma-count ( -- n ) ss-lemmas slab-count ;
: ss-procs-of ( post -- slab ) if ss-proc-post else ss-proc-pre then ;
: simp-procs# ( post -- n ) ss-procs-of slab-count ;
: simp-proc-value ( k post -- p ) ss-procs-of slab-at @ ;
: simp-proc-keys ( p -- k n ) ssp ssp-value elab-value-keys ;
: simp-proc-rank ( p -- rank ) ssp ssp-value elab-value-rank@ ;
: simp-proc-dsimproc? ( p -- flag ) ssp ssp-dsimproc @ ;
: simp-proc-count ( -- n ) ss-procs slab-count ;
: simp-unfold? ( d -- flag ) ss-unfolds slab-data cells-has? ;

base !   \ the BASE this file was loaded with
