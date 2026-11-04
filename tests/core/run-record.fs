\ Run records and replay (plan task 2.2.5; src/import/run-record.fs and
\ run-replay.fs, driven through tests/support/run-records.fs): the five
\ pinned exports and the four broken copies of the composition export
\ each give a record with the verdicts the checker's own tests expect
\ (tests/core/check-declaration-ndjson.fs), read from the slots; a record
\ is the same text when the run is repeated; a record replays as
\ confirmed and a changed run is refused, finding by finding; and each
\ failure of the modules is reached. Nothing here writes a file: records
\ written to files, the schemas, the golden records, other processes and
\ tampered files are tested by tests/core/test_run_records.py. Test-only.
include ../support/tester.fs
include ../support/checks.fs
\ The publisher's test-only fault hook, lf-env-before-final, to stop a run.
: lf-env-fault-hooks ( -- ) ;
require ../support/run-records.fs

100000 constant fuel
: must ( flag -- ) 0= abort" run-record: refused" ;
: composition ( -- c-addr u ) s" tests/reference/composition.ndjson" ;
: identity ( -- c-addr u ) s" tests/reference/identity.ndjson" ;
: type-identity ( -- c-addr u ) s" tests/reference/type-identity.ndjson" ;
: poly-identity ( -- c-addr u ) s" tests/reference/poly-identity.ndjson" ;
: constant-fixture ( -- c-addr u ) s" tests/reference/constant-fixture.ndjson" ;
: wrong-argument ( -- c-addr u )
  s" tests/core/check-declaration-cases/composition-wrong-argument.ndjson" ;
: postulate-case ( -- c-addr u )
  s" tests/core/check-declaration-cases/composition-postulate.ndjson" ;
: literal-case ( -- c-addr u )
  s" tests/core/check-declaration-cases/composition-literal.ndjson" ;
: loose-case ( -- c-addr u )
  s" tests/core/check-declaration-cases/composition-loose.ndjson" ;
: no-export ( -- c-addr u ) s" tests/core/no-such-export.ndjson" ;
: not-export ( -- c-addr u ) s" tests/core/run-record.fs" ;

\ Whether the record text holds c-addr u.
: holds? ( c-addr u -- flag ) rr-text 2swap search nip nip ;
\ Run a file, then whether its record holds c-addr u; the run released.
: run-holds? ( c-addr1 u1 c-addr2 u2 -- outcome flag )
  2>r fuel ni-run 2r> holds? rr-release ;
: accepted ( -- c-addr u )
  s\" \"verdict\":\"accepted\",\"label\":\"experimental, not independently audited\"" ;
: no-axioms ( -- c-addr u ) s\" audited\",\"axioms\":[]}" ;
: third-accepted ( -- c-addr u )
  s\" {\"index\":2,\"name\":\"fixtureUse\",\"verdict\":\"accepted\"" ;
: manifest-ok ( -- c-addr u )
  s\" {\"outcome\":\"ok\",\"field\":\"\",\"reason\":\"\",\"enforced\":false}" ;
: pinned ( -- c-addr u )
  s\" \"lean\":\"4.35.0\",\"leanGithash\":\"eb6cafb7290e8bd5f2937522d8d804f58f02bafc\"" ;
: run-ok ( -- c-addr u )
  s\" \"check\":{\"read\":\"ok\",\"run\":\"ok\",\"mode\":\"final\"," ;

\ The pinned exports: every declaration accepted, labelled, no axioms, the
\ manifest ok, the pinned versions read from the metadata.
T{ composition accepted run-holds? -> outcome-ok true }T
T{ composition no-axioms run-holds? -> outcome-ok true }T
T{ identity accepted run-holds? -> outcome-ok true }T
T{ type-identity accepted run-holds? -> outcome-ok true }T
T{ poly-identity accepted run-holds? -> outcome-ok true }T
T{ constant-fixture third-accepted run-holds? -> outcome-ok true }T
T{ composition manifest-ok run-holds? -> outcome-ok true }T
T{ composition pinned run-holds? -> outcome-ok true }T
T{ composition run-ok run-holds? -> outcome-ok true }T

\ The broken copies: rejected, unsupported and invalid, each with the
\ diagnostic and step its check left; no manifest beside them.
: rejected-59 ( -- c-addr u )
  s\" \"verdict\":\"rejected\",\"diagnostic\":{\"code\":59," ;
: numbers-step ( -- c-addr u ) s\" \"numbers\":[4,0],\"step\":7}" ;
: no-manifest ( -- c-addr u ) s" manifest missing, unreadable or too large" ;
: unsupported-42 ( -- c-addr u )
  s\" \"verdict\":\"unsupported\",\"diagnostic\":{\"code\":42," ;
: unsupported-43 ( -- c-addr u )
  s\" \"verdict\":\"unsupported\",\"diagnostic\":{\"code\":43," ;
: invalid-23 ( -- c-addr u ) s\" \"verdict\":\"invalid\",\"diagnostic\":{\"code\":23," ;
T{ wrong-argument rejected-59 run-holds? -> outcome-ok true }T
T{ wrong-argument numbers-step run-holds? -> outcome-ok true }T
T{ wrong-argument no-manifest run-holds? -> outcome-ok true }T
T{ postulate-case unsupported-42 run-holds? -> outcome-ok true }T
T{ literal-case unsupported-43 run-holds? -> outcome-ok true }T
T{ loose-case invalid-23 run-holds? -> outcome-ok true }T
T{ wrong-argument s" accepted" run-holds? -> outcome-ok false }T

\ A file the transport cannot read: a record that says so, with no
\ declarations; a file that cannot be opened: no record.
: not-read ( -- c-addr u )
  s\" \"check\":{\"read\":\"invalid\",\"run\":\"not-run\",\"mode\":null," ;
: no-declarations ( -- c-addr u ) s\" \"allowlistVersion\":null},\"declarations\":[]}" ;
T{ not-export not-read run-holds? -> outcome-ok true }T
T{ not-export no-declarations run-holds? -> outcome-ok true }T
T{ no-export fuel ni-run -> outcome-invalid }T

\ Settings: with fuel 0 the check is exhausted, and the record says so.
T{ composition 0 ni-run -> outcome-ok }T
T{ s\" \"fuel\":0," holds? -> true }T
T{ s\" \"verdict\":\"exhausted\"" holds? -> true }T
rr-release

\ A run that stops: a THROW in the publisher before declaration 1's slot
\ is final. Its slot is not final: invalid, with the publisher's fault as
\ its diagnostic; declaration 2 was never checked; the run is invalid.
: throw-at-1 ( -- ) lf-env-limit 1 = if 4242 throw then ;
: fault-29 ( -- c-addr u )
  s\" \"verdict\":\"invalid\",\"diagnostic\":{\"code\":29,\"reason\":\"invalid:" ;
: unchecked-2 ( -- c-addr u )
  s\" {\"index\":2,\"name\":\"fixtureUse\",\"verdict\":\"not-checked\"}" ;
' throw-at-1 is lf-env-before-final
T{ constant-fixture fuel ni-run -> outcome-ok }T
' lf-env-no-fault is lf-env-before-final
T{ s\" \"run\":\"invalid\"" holds? fault-29 holds? unchecked-2 holds? -> true true true }T
T{ s\" \"numbers\":[1,4242]" holds? accepted holds? -> true true }T
rr-release

\ Verdicts only from the run's own environment (review F1). B: rr-check
\ cannot make its environment (a pool out of range) while the caller's
\ own environment over the same input is current: the record lists no
\ declaration, and says why. C: rr-check makes its environment and checks
\ with the same fuel, then the caller makes another current: no record,
\ though every verdict there agrees with the run's own.
variable foreign
: foreign-current ( -- ) fuel 64 lf-check-input ok? must foreign ! ;
: foreign-free ( -- ) foreign @ lf-env-free ok? must ;
: no-env ( -- c-addr u )
  s\" \"run\":\"invalid\",\"mode\":null,\"allowlistVersion\":null},\"declarations\":[]" ;
T{ constant-fixture rr-start -> outcome-ok }T
0 lf-env-pool-max 1+ rr-settings!
T{ false rr-import -> outcome-ok }T
foreign-current rr-check
T{ rr-finish rr-write -> outcome-ok outcome-ok }T
T{ no-env holds? s" accepted" holds? -> true false }T
foreign-free
\ C. rr-release then leaves both alone (rvRP3 L2): it frees only the
\ current environment with the run's identity, never through an address.
variable own-env
T{ constant-fixture rr-start -> outcome-ok }T
fuel 64 rr-settings!
T{ false rr-import -> outcome-ok }T
rr-check run-record rr-env @ own-env ! foreign-current
T{ rr-finish rr-write -> outcome-ok outcome-invalid }T
rr-release
T{ run-record rr-env @ foreign @ lf-env-live? own-env @ lf-env-live? -> 0 true true }T
foreign-free own-env @ lf-env-use ok? must rr-ours? 0= must own-env @ lf-env-free ok? must
\ A new run's kept outcomes are invalid, never ok, until its steps publish.
T{ rr-begun 0 rr-step-of kept-outcome @ lf-input-capacity 1- rr-step-of kept-outcome @
  -> outcome-invalid outcome-invalid }T
\ The run's environment freed and a new one made, at the same address,
\ before rr-write (rvRP round 2, its probe aba.fs): environments compare
\ by identity, so no record is written, and rr-release leaves the new one
\ alone. The run checked with fuel 0, the new environment with 100000.
\ Whether the address was reused is the allocator's choice: the test says
\ when it was not (rvRP3 L4), and the record is refused either way.
: aba ( fuel -- )
  constant-fixture rr-start ok? must 64 rr-settings! false rr-import ok? must
  rr-check run-record rr-env @ dup own-env ! lf-env-free ok? must foreign-current ;
: reused? ( -- flag ) foreign @ own-env @ = ;
0 aba
T{ rr-finish rr-write -> outcome-ok outcome-invalid }T
reused? [if] T{ reused? -> true }T [else] .( note: ABA not exercised, no reuse) cr [then]
rr-release
T{ foreign @ lf-env-live? -> true }T
foreign-free
\ The same with fuel 100000 for both, so that every verdict agrees and only
\ the identity tells the two environments apart.
fuel aba
T{ rr-finish rr-write -> outcome-ok outcome-invalid }T
reused? [if] T{ reused? -> true }T [else] .( note: ABA not exercised, no reuse) cr [then]
rr-release foreign-free

\ The file is rr-start's for every later read (rvRP3 M1): rr-import has no
\ name of its own, and without a started file it reads nothing. A read,
\ checked or not, whose bytes are not the ones rr-start hashed (here the
\ recorded digest is changed instead of the file; test_run_records.py
\ swaps the file itself) fails, and says so.
: hex-byte ( -- addr ) run-record rr-before facts-hex ;
constant-fixture rr-start ok? must fuel 64 rr-settings!
T{ true rr-import -> outcome-ok }T
rr-check
T{ rr-finish rr-write -> outcome-ok outcome-ok }T
T{ third-accepted holds? s\" \"enforced\":true}" holds? -> true true }T
T{ composition rr-start -> outcome-ok }T
char x hex-byte c!
T{ true rr-import rr-moved? -> outcome-invalid true }T
T{ false rr-import rr-moved? -> outcome-invalid true }T
\ The digest of a read that was ok is the file's (rr-hash's), checked or
\ not.
: digest-of ( c-addr u flag -- c-addr u )
  >r rr-start ok? must r> rr-import ok? must cin-digest ;
T{ composition true digest-of rr-recorded compare -> 0 }T
T{ composition false digest-of rr-recorded compare -> 0 }T
\ rr-file! and rr-read! are internal (rvRP3 R2-3): a recorded run reads
\ its input only through rr-import of rr-start's file. The tests below
\ reach them through rr-internal.
: found? ( c-addr -- flag ) find nip 0<> ;
: internal-found? ( -- flag1 flag2 ) c" rr-file!" found? c" rr-read!" found? ;
T{ internal-found? -> false false }T
rr-internal order+
T{ s" " rr-file! false rr-import rr-moved? -> true outcome-invalid false }T
order-
rr-release
\ A run read once, without rr-start (bin/leanforth check without
\ --record): checked as usual, never recorded, whatever facts an earlier
\ run left.
T{ constant-fixture true rr-read-once -> outcome-ok }T
fuel 64 rr-settings! rr-check
T{ run-record rr-run @ rr-started? rr-write -> outcome-ok false outcome-invalid }T
\ ... also when the manifest's outcome left in the record would pass.
outcome-ok run-record rr-manifest-outcome !
T{ rr-write -> outcome-invalid }T
rr-release
\ Checks run although the read was not ok (rvRP3 L1, its probe p8): the
\ input is still the earlier file's, so no record.
constant-fixture rr-start ok? must fuel 64 rr-settings!
T{ true rr-import -> outcome-ok }T
rr-check
T{ composition rr-start -> outcome-ok }T
rr-check
T{ rr-finish rr-write -> outcome-ok outcome-invalid }T
rr-release

\ Whether the input's manifest was enforced (rvRP round 2). rr-import with
\ the manifest checked says enforced, and composition matches its
\ manifest; without the check, through the driver, or after rr-read!, the
\ record says not enforced. A checked read of a copy without a manifest is
\ refused and says enforced. An enforced manifest that the read passed
\ although it did not match is a contradiction: no record.
: run-import ( c-addr u flag -- outcome )
  >r rr-start ok? must fuel 64 rr-settings! r> rr-import
  ok? if rr-check then rr-finish ok? must rr-write ;
: enforced ( -- c-addr u ) s\" \"reason\":\"\",\"enforced\":true}" ;
: not-enforced ( -- c-addr u ) s\" \"enforced\":false}" ;
: read-invalid ( -- c-addr u ) s\" \"check\":{\"read\":\"invalid\"" ;
T{ composition true run-import enforced holds? -> outcome-ok true }T
rr-internal order+ outcome-ok rr-read! order-
T{ rr-write not-enforced holds? -> outcome-ok true }T
rr-release
T{ composition false run-import not-enforced holds? -> outcome-ok true }T
rr-release
T{ composition fuel ni-run not-enforced holds? -> outcome-ok true }T
rr-release
T{ wrong-argument true run-import -> outcome-ok }T
T{ s\" \"enforced\":true}" holds? read-invalid holds? -> true true }T
rr-release
T{ composition true run-import -> outcome-ok }T
outcome-invalid run-record rr-manifest-outcome !
s" changed" run-record rr-manifest-reason rr-note! drop
T{ rr-write -> outcome-invalid }T
rr-release

\ The text rule (review F3): no control, format or separator character,
\ valid UTF-8; a shown text has a character other than a space.
create one-char 4 allot
: rule? ( code -- flag ) one-char utf8-put one-char swap tr-rule? ;
T{ $41 rule? $1f rule? $7f rule? $a0 rule? $ad rule? -> true false false true false }T
T{ $202e rule? $2028 rule? $feff rule? $1f600 rule? -> false false false true }T
T{ $e0041 rule? $110bd rule? -> false false }T
: bad-byte ( -- c-addr u ) s\" a\xff" ;
: no-break-x ( -- c-addr u ) s\" \xc2\xa0x" ;
: en-quad ( -- c-addr u ) s\" \xe2\x80\x80" ;
T{ bad-byte tr-rule? 0 0 tr-rule? -> false true }T
T{ 0 0 tr-shown? bl pad c! pad 1 tr-shown? -> false false }T
T{ no-break-x tr-shown? en-quad tr-shown? -> true false }T
\ Texts that look blank are not shown (rvRP round 2): the fillers, a
\ combining mark or a default-ignorable character alone; a letter with a
\ mark is shown, and so is a Greek letter.
: shown? ( code -- flag ) one-char utf8-put one-char swap tr-shown? ;
T{ $3164 shown? $115f shown? $1160 shown? $2800 shown? $ffa0 shown? -> 0 0 0 0 0 }T
T{ $301 shown? $34f shown? $fe0f shown? $e0100 shown? $20dd shown? -> 0 0 0 0 0 }T
T{ $41 shown? $3b1 shown? $1f600 shown? -> true true true }T
: marks-only ( -- c-addr u ) s\" \xcc\x81\xcc\x82" ;
: a-mark ( -- c-addr u ) s\" a\xcc\x81" ;
T{ marks-only tr-shown? a-mark tr-shown? -> false true }T
\ ... and the writer refuses one, by the same path as a blank text.
: filler ( -- c-addr u ) s\" \xe3\x85\xa4" ;
T{ composition fuel ni-run -> outcome-ok }T
filler run-record rr-lean rr-note! drop
T{ rr-write -> outcome-invalid }T
rr-release
\ Numbers within +-(2^53 - 1).
T{ 0 0 rr-exact? -1 s>d rr-exact? -> true true }T
T{ rr-exact rr-exact? rr-exact 1 m+ rr-exact? -> true false }T
\ The writer refuses what the schema refuses: a blank metadata text, and
\ fuel beyond I-JSON's range (where a cell can hold it).
: blank-text ( -- c-addr u ) s"   " ;
T{ composition fuel ni-run -> outcome-ok }T
blank-text run-record rr-lean rr-note! drop
T{ rr-write -> outcome-invalid }T
rr-release
: huge-fuel ( -- outcome ) max-n s>d rr-exact? if outcome-ok else outcome-invalid then ;
T{ composition max-n ni-run -> huge-fuel }T
rr-release

\ The verdicts are the slots' own: the same as lf-check-input's.
: slot-verdicts ( c-addr u -- o0 o1 o2 )
  cin-read ok? must fuel 64 lf-check-input ok? must >r lf-env-view ok? must
  0 lf-env-outcome 1 lf-env-outcome 2 lf-env-outcome r> lf-env-free ok? must ;
T{ constant-fixture slot-verdicts -> outcome-ok outcome-ok outcome-ok }T

\ Determinism: the same run twice gives the same text.
create first-text rr-text-room allot  variable first-size
: keep-text ( -- ) rr-text dup first-size ! first-text swap move ;
: kept-text ( -- c-addr u ) first-text first-size @ ;
: same-text? ( -- flag ) rr-text kept-text compare 0= ;
T{ constant-fixture fuel ni-run -> outcome-ok }T
keep-text rr-release
T{ constant-fixture fuel ni-run -> outcome-ok }T
T{ same-text? -> true }T
rr-release

\ The source: a commit of 40 lowercase hexadecimal digits, and the flag.
: commit ( -- c-addr u ) s" 0123456789abcdef0123456789abcdef01234567" ;
: commit-modified ( -- c-addr u )
  s\" {\"commit\":\"0123456789abcdef0123456789abcdef01234567\",\"modified\":true}" ;
: no-commit ( -- c-addr u ) s\" \"leanforth\":{\"commit\":null,\"modified\":null}" ;
T{ commit true rr-source! -> outcome-ok }T
T{ composition commit-modified run-holds? -> outcome-ok true }T
T{ s" 0123456789ABCDEF0123456789abcdef01234567" false rr-source! -> outcome-invalid }T
T{ s" 0123" false rr-source! -> outcome-invalid }T
rr-no-source
T{ composition no-commit run-holds? -> outcome-ok true }T

\ The writer's own failures. A slot whose outcome is not the one its step
\ published fails the text as invalid, and so does an accepted slot whose
\ axiom set is not empty, and a run whose environment is gone. A name
\ longer than the buffer fails it as full.
: slot0 ( -- slot ) 0 lf-env lf-env-slot ;
T{ composition fuel ni-run -> outcome-ok }T
outcome-rejected 0 rr-step-of kept-outcome !
T{ rr-write -> outcome-invalid }T
outcome-ok 0 rr-step-of kept-outcome !
T{ rr-write -> outcome-ok }T
1 slot0 lf-slot-axioms !
T{ rr-write -> outcome-invalid }T
0 slot0 lf-slot-axioms !
T{ rr-write -> outcome-ok }T
rr-release
T{ rr-write -> outcome-invalid }T
create long-name rr-name-room 1+ allot
: long-name-sink ( -- ) long-name rr-name-room 1+ rr-name-sink ;
T{ rr-begin-text long-name-sink run-record rr-fault @ -> outcome-full }T

\ The input must not change during the run: rr-finish reads the file
\ again (here the recorded size is changed instead of the file), and
\ fails when it cannot read it; a name too long to keep starts nothing.
T{ composition rr-start -> outcome-ok }T
T{ rr-finish -> outcome-ok }T
1 run-record rr-before facts-bytes rr-d+!
T{ rr-finish -> outcome-invalid }T
T{ no-export rr-start rr-finish -> outcome-invalid outcome-invalid }T
create long-file rr-file-room 1+ allot
T{ long-file rr-file-room 1+ rr-start rr-file nip -> outcome-full 0 }T

\ Hashing: SHA-256 of the bytes, the bytes and the lines; a last line
\ without a line feed counts. composition.ndjson's digest is its manifest's.
: before ( -- facts ) run-record rr-before ;
: composition-digest ( -- c-addr u )
  s" 7778d2ef5da2f0935fb0180c953afa9371843f4ceec2660122f8c792b9ca2fec" ;
T{ composition before rr-hash -> outcome-ok }T
T{ before facts-hex 64 composition-digest compare -> 0 }T
T{ before facts-bytes 2@ before facts-lines 2@ -> 1787 0 35 0 }T
T{ s\" a\nb\n" rr-feeds -> 2 }T
T{ s\" a\nb" rr-ends-open? -> true }T
T{ s\" a\n" rr-ends-open? -> false }T
\ "a\nb", taken in two pieces: three bytes, two lines, sha256sum's digest.
: a-lf-b-digest ( -- c-addr u )
  s" 7e18f737311b2dc3b2f269dd78396b0351f14fb66efa879f768cb23181883c78" ;
: take-a-lf-b ( -- )
  before rr-facts-start s\" a\n" before rr-take s" b" before rr-take before rr-facts-end ;
T{ take-a-lf-b before facts-bytes 2@ before facts-lines 2@ -> 3 0 2 0 }T
T{ before facts-hex 64 a-lf-b-digest compare -> 0 }T

\ Replay: confirmed against its own record, refused against another run
\ with each difference found, refused outright for a text that is not a
\ record of this format.
: finding@ ( k -- code ) rp-finding finding-code @ ;
: finding-path@ ( k -- c-addr u ) rp-finding dup finding-path swap finding-size @ ;
: total ( -- n ) run-replay rp-total @ ;
: replay ( c-addr u fuel -- outcome )
  ni-run ok? must kept-text rp-replay-text rr-release ;
T{ composition fuel ni-run -> outcome-ok }T
keep-text rr-release
T{ composition fuel replay -> outcome-ok }T
T{ total -> 0 }T
T{ composition 50 replay -> outcome-rejected }T
T{ total 0 finding@ 1 finding@ -> 2 rp-settings-differ rp-accepted-not-established }T
T{ 1 finding-path@ s" $.declarations[0].verdict" compare -> 0 }T
T{ wrong-argument fuel replay -> outcome-rejected }T
T{ 0 finding@ 0 finding-path@ s" $.input.sha256" compare -> rp-input-differs 0 }T
T{ type-identity fuel replay -> outcome-rejected }T
T{ total 3 finding@ -> 4 rp-declarations-differ }T
commit false rr-source! ok? must
T{ composition fuel replay -> outcome-rejected }T
T{ 0 finding@ 0 finding-path@ s" $.leanforth.commit" compare -> rp-tool-differs 0 }T
rr-no-source
T{ composition fuel ni-run -> outcome-ok }T
T{ composition rp-replay-text -> outcome-invalid }T
T{ 0 finding@ total -> rp-not-json 1 }T
T{ s" [1]" rp-replay-text -> outcome-invalid }T
T{ 0 finding@ -> rp-unknown-schema }T
: other-version ( -- c-addr u )
  s\" {\"schema\":\"leanforth-run-record\",\"schemaVersion\":\"0.2\"}" ;
T{ other-version rp-replay-text -> outcome-invalid }T
T{ 0 finding@ -> rp-unknown-schema }T
\ A record of the format with nothing in it: every member is missing,
\ within the sections as at the top.
: hollow ( -- c-addr u )
  s\" {\"schema\":\"leanforth-run-record\",\"schemaVersion\":\"0.1\",\"input\":{}}" ;
T{ hollow rp-replay-text -> outcome-rejected }T
T{ total 0 finding@ 9 finding@ -> 10 rp-missing-field rp-missing-field }T
T{ 0 finding-path@ s" $.input.sha256" compare -> 0 }T
T{ 9 finding-path@ s" $.declarations" compare -> 0 }T
T{ s" tests/core/no-such-record.json" rp-replay -> outcome-invalid }T
T{ 0 finding@ -> rp-unreadable }T
T{ first-text rp-room 1+ rp-replay-text -> outcome-invalid }T
T{ 0 finding@ -> rp-unreadable }T
T{ rp-report -> outcome-ok }T
rr-release
T{ rp-rerun-refused 0 finding@ -> outcome-invalid rp-rerun-failed }T

\ Paths are cut between characters (review F2): "a", then a two-byte é.
: a-e-acute ( -- c-addr u ) s\" a\xc3\xa9b" ;
T{ a-e-acute 2 rp-whole a-e-acute 3 rp-whole a-e-acute 4 rp-whole a-e-acute 9 rp-whole
  -> 1 3 4 4 }T
T{ s\" a\xff" 9 rp-whole -> 1 }T

\ Codes and their names; paths.
T{ rp-verdict-differs rp-code-name s" verdict-differs" compare -> 0 }T
T{ -1 rp-code-name s" ?" compare -> 0 }T
T{ s" host" rp-sections rp-named rp-entry-code -> rp-tool-differs }T
T{ s" nothing" rp-sections rp-named rp-entry-code -> -1 }T
T{ rp-start 3 rp-index+ s" verdict" rp-key+ rp-path s" $[3].verdict" compare -> 0 }T

cases-done
bye
