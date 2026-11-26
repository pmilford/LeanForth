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
\   whatever the library holds: a well-formed name, kept as text less its
\   macro scopes, which simp/simprocs.fs matches its ports by), keys
\   (foreign constants allowed), post, rank, dsimproc.
\ Members, names and numbers are checked as elab-data.fs checks them
\ (errors 10-14, 19; 22 for no room). Ranks are checked when a root is
\ built (front/data-index.fs: a gap or two values of one rank invalid).
\
\ simp-default? ( -- flag ): data of format 4.1 holding the simp_set
\ record, so the default set is Lean's; else simp answers unsupported.
\ simp-values# ( post procs? -- n ) and simp-value ( k post procs? -- v ):
\ the values of a tree of lemmas (procs? false) or of a phase's simprocs
\ (procs? true), in file order.
\ A lemma value v is a simp_lemma record i (v = i >= 0) or a
\ simp_left_out record j (v = j invert):
\ simp-lemma-keys ( v -- k n ), simp-lemma-rank ( v -- rank ),
\ simp-lemma-prio ( v -- p ), simp-lemma-post? ( v -- flag ); of a record
\ i: simp-lemma-proof ( i -- d ),
\ simp-lemma-rfl? and simp-lemma-perm? ( i -- flag ); simp-lemma-count
\ ( -- n ). A simproc p: simp-proc-keys ( p -- k n ), simp-proc-rank
\ ( p -- rank ), simp-proc-dsimproc? and simp-proc-post? ( p -- flag ),
\ simp-proc-name ( p --
\ c-addr u ) (valid until the next read), simp-proc-count ( -- n ).
\ simp-unfold? ( d -- flag ): the set unfolds declaration d. Unchecked:
\ numbers below their counts.
\
\ State: the context slabs of the records (ss-lemmas, ss-lefts,
\ ss-procs, ss-unfolds), of each tree's values in file order
\ (ss-pre, ss-post, ss-proc-pre, ss-proc-post) and of the simprocs' names
\ (ss-names), and the record ss (the simp_set read); emptied by every
\ reset of the data (the kinds' clears).
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
  field: ssp-name-at   field: ssp-name-u   \ its name's text in ss-names (2@: u at)
  field: ssp-scoped   \ its name's macro scopes reached (while it is read)
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
1 context-slab: ss-names   \ the simprocs' names, text after text

: ssl ( i -- addr ) ss-lemmas slab-at ;
: ssj ( j -- addr ) ss-lefts slab-at ;
: ssp ( p -- addr ) ss-procs slab-at ;
: ss-or ( flag code -- outcome ) swap if drop outcome-ok else elab-refuse then ;

\ ---- Members several kinds share.
\ A one-part name: the array of the one string c-addr u (error 52).
: ss-part-is ( item c-addr u -- outcome ) elab-text= elab-e-simp-set ss-or ;
: ss-simp-part ( item -- outcome ) s" simp" ss-part-is ;
: ss-attr-part ( item -- outcome ) s" simprocAttr" ss-part-is ;
: ss-one? ( index -- flag ) elab-items# if 1 = else false then ;
: ss-one-part ( index xt -- outcome )
  over ss-one? 0= if 2drop elab-e-simp-set elab-refuse exit then elab-array-items ;
: ss-set ( value i -- outcome ) drop c" set" elab-member ['] ss-simp-part ss-one-part ;
: ss-bool-at ( value addr c-addr -- outcome ) rot swap elab-member elab-bool sd-at! ;
: ss-flag ( value c-addr -- outcome ) elab-member elab-bool nip ;
: ss-u32-at ( value addr c-addr -- outcome ) rot swap elab-member elab-u32 sd-at! ;
: ss-keys ( value addr foreign? -- outcome )
  rot c" keys" elab-member swap elab-keys-read ;
: ss-rank ( value addr -- outcome ) swap c" rank" elab-member elab-value-rank! ;
\ A lemma's members, kept or left out, into its record at addr.
: ss-post! ( value addr -- outcome ) ssl-post c" post" ss-bool-at ;
: ss-prio! ( value addr -- outcome ) ssl-prio c" priority" ss-u32-at ;
: ss-rank! ( value addr -- outcome ) ssl-value ss-rank ;
\ The four value lists, in file order: a tree's lemmas, a phase's
\ simprocs; a value put on its list.
: ss-lemma-list ( post -- slab ) if ss-post else ss-pre then ;
: ss-proc-list ( post -- slab ) if ss-proc-post else ss-proc-pre then ;
: ss-list ( post procs? -- slab ) if ss-proc-list else ss-lemma-list then ;
: ss-phase ( v post procs? -- outcome ) ss-list slab-push elab-roomed ;

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
  ssl ssl-proof swap c" proof" elab-member sd-theorem sd-at! ;
: ssl-post! ( value i -- outcome ) ssl ss-post! ;
: ssl-rfl! ( value i -- outcome ) ssl ssl-rfl c" rfl" ss-bool-at ;
: ssl-perm! ( value i -- outcome ) ssl ssl-perm c" perm" ss-bool-at ;
: ssl-flags ( value i -- outcome )
  drop dup c" inv" ss-flag ok-then? if c" backward_rfl" ss-flag then ;
: ssl-prio! ( value i -- outcome ) ssl ss-prio! ;
: ssl-keys! ( value i -- outcome ) ssl ssl-value false ss-keys ;
: ssl-rank! ( value i -- outcome ) ssl ss-rank! ;
\ Lean's rfl flag of a constant proof is its defeq tag (error 50).
: ssl-tagged? ( i -- flag ) ssl ssl-proof @ elab-tag-defeq elab-tagged? ;
: ssl-rfl-tag ( value i -- outcome )
  nip dup ssl-tagged? swap ssl ssl-rfl @ = elab-e-simp-rfl ss-or ;
: ssl-phase ( value i -- outcome ) nip dup ssl ssl-post @ false ss-phase ;
: ssl-clear ( -- ) ss-lemmas ss-pre ss-post 3 slabs-clear ;
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
  elab-name dup ok? if drop elab-has? outcome-ok then ;   \ a failed lookup: -1 and why
: ss-member-known ( value c-addr -- flag outcome ) elab-member ss-known ;
: ss-both-known ( value -- flag outcome )
  dup c" origin" ss-member-known ok-then? 0= if nip false swap exit then
  swap c" proof" ss-member-known ok-then? if and outcome-ok else nip false swap then ;
: ssj-names ( value j -- outcome )
  drop ss-both-known ok-then? if 0= elab-e-simp-left ss-or then ;
: ssj-reason ( value j -- outcome )
  drop c" reason" elab-member s" not_exported" elab-text=
  if outcome-ok else elab-malformed then ;
: ssj-post! ( value j -- outcome ) ssj ss-post! ;
: ssj-prio! ( value j -- outcome ) ssj ss-prio! ;
: ssj-keys! ( value j -- outcome ) ssj ssl-value true ss-keys ;
: ssj-rank! ( value j -- outcome ) ssj ss-rank! ;
: ssj-phase ( value j -- outcome )
  nip dup ssj ssl-post @ swap invert swap false ss-phase ;
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
  ss-unfolds slab-at swap c" name" elab-member elab-decl sd-at! ;
: ssu-clear ( -- ) ss-unfolds slab-clear ;
here 0 , ' ss-unfolds ,  ' ss-set , ' ssu-name! , 0 , constant ssu-form
ssu-form elab-keys-here  s" name" counted, s" set" counted, 0 0 counted,
ssu-form ' ssu-clear s" simp_unfold" elab-add-kind41 constant simp-unfold-kind

\ ---- simproc: an entry of the default simproc set.
\ Its name kept as text (the simproc ports are found by it): the parts
\ joined by dots up to its macro scopes (Name.eraseMacroScopes: the parts
\ before _@, a macro's hygienic suffix) or a number part; the whole name's
\ form checked first (elab-name-shape). The record read is the newest.
: ssn-rec ( -- addr ) ss-procs slab-last ;
\ A part's text, after a dot when a part came before, in one claim.
: ssn-sep ( -- n ) ssn-rec ssp-name-u @ 0<> 1 and ;
: ssn-dot ( addr -- addr' ) s" ." rot 2dup + >r swap move r> ;
: ssn-put ( c-addr u addr -- ) ssn-sep if ssn-dot then swap move ;
: ssn-move ( c-addr u i -- outcome )
  ss-names slab-at over ssn-sep + >r ssn-put r> ssn-rec ssp-name-u +! outcome-ok ;
: ssn-bytes ( c-addr u -- outcome )
  dup ssn-sep + ss-names slab-claim elab-roomed ok-then? if ssn-move else nip nip then ;
: ssn-end ( -- outcome ) true ssn-rec ssp-scoped ! outcome-ok ;
: ssn-text ( c-addr u -- outcome )
  2dup s" _@" compare 0= if 2drop ssn-end else ssn-bytes then ;
: ssn-part ( item -- outcome )
  ssn-rec ssp-scoped @ if drop outcome-ok exit then
  elab-string if ssn-text else ssn-end then ;
: ssn-start ( p -- )
  ssp ss-names slab-count over ssp-name-at ! 0 over ssp-name-u ! false swap ssp-scoped ! ;
: ssp-name ( value p -- outcome )
  ssn-start c" name" elab-member dup elab-name-shape
  ok-then? if ['] ssn-part elab-array-items then ;
: ssp-keys! ( value p -- outcome ) ssp ssp-value true ss-keys ;
: ssp-post! ( value p -- outcome ) ssp ssp-post c" post" ss-bool-at ;
: ssp-rank! ( value p -- outcome ) ssp ssp-value ss-rank ;
: ssp-dsimproc! ( value p -- outcome ) ssp ssp-dsimproc c" dsimproc" ss-bool-at ;
: ssp-phase ( value p -- outcome ) nip dup ssp ssp-post @ true ss-phase ;
: ssp-clear ( -- ) ss-procs ss-proc-pre ss-proc-post ss-names 4 slabs-clear ;
here 0 , ' ss-procs ,
  ' ssp-name , ' ssp-keys! , ' ssp-post! , ' ssp-rank! , ' ssp-dsimproc! , ' ssp-phase ,
  0 , constant ssp-form
ssp-form elab-keys-here
  s" dsimproc" counted, s" keys" counted, s" name" counted, s" post" counted,
  s" rank" counted, 0 0 counted,
ssp-form ' ssp-clear s" simproc" elab-add-kind41 constant simp-proc-kind

\ ---- The questions.
: simp-default? ( -- flag ) elab-format41? ss ss-set-read @ and ;
: simp-values# ( post procs? -- n ) ss-list slab-count ;
: simp-value ( k post procs? -- v ) ss-list slab-at @ ;
: ss-lemma ( v -- addr ) dup 0< if invert ssj else ssl then ;
: simp-lemma-keys ( v -- k n ) ss-lemma ssl-value elab-value-keys ;
: simp-lemma-rank ( v -- rank ) ss-lemma ssl-value elab-value-rank@ ;
: simp-lemma-prio ( v -- p ) ss-lemma ssl-prio @ ;
: simp-lemma-post? ( v -- flag ) ss-lemma ssl-post @ ;
: simp-lemma-proof ( i -- d ) ssl ssl-proof @ ;
: simp-lemma-rfl? ( i -- flag ) ssl ssl-rfl @ ;
: simp-lemma-perm? ( i -- flag ) ssl ssl-perm @ ;
: simp-lemma-count ( -- n ) ss-lemmas slab-count ;
: simp-proc-keys ( p -- k n ) ssp ssp-value elab-value-keys ;
: simp-proc-rank ( p -- rank ) ssp ssp-value elab-value-rank@ ;
: simp-proc-dsimproc? ( p -- flag ) ssp ssp-dsimproc @ ;
: simp-proc-post? ( p -- flag ) ssp ssp-post @ ;
: simp-proc-count ( -- n ) ss-procs slab-count ;
: simp-proc-name ( p -- c-addr u ) ssp ssp-name-at 2@ ss-names slab-at swap ;   \ ( u at )
: simp-unfold? ( d -- flag ) ss-unfolds slab-data cells-has? ;

base !   \ the BASE this file was loaded with
