# Forth review: reuse-front-a2, e3c5297a..d16b10b5 (14 commits, tree 1ef9d5bef017), 2026-11-18
Findings: BLOCKS 1, should fix before merge 1, REUSE PASS 3, note 4.

## Verdict
Blocking: finding 1 only (the lifted value limit makes a small .lf file run for minutes). Everything else is
behaviour-preserving as far as I could probe: the shared offset walk, the 7 unknown-constant sites, the 9 tag sets,
mkAppRange in whnf/infer, and the runner on lib/text-run.fs. Mergeable once 1 is fixed, 2 is fixed or planned,
3-5 cited in 9.4.8k.

## For the owner (plain language)
- The cleanup removed copied code without changing results: on 500 random terms the old and new code built
  exactly the same terms (same numbering), and 120 of 128 deliberately broken .lf files gave the same answer.
- One real problem: a declaration may now hold any number of values (it was capped at 512). The code that
  looks for an existing identical term is slow, so a 3 KB statement of 500 arrows now takes 4 minutes (1000
  arrows: over 5 minutes, stopped), where main refused it at once with "out of room". Fix the slow search, or
  keep a cap until it is fixed. I recommend fixing the search (a hash table the library already has).
- Gates: [kernel] none (no src/core, src/kernel, src/import or src/cli file changed); [import] none (lib-decode.fs
  only swaps push/pop words); [format] none; [bypass] none (nothing here can make a theorem accepted).
  [parser]: src/author changed; text is read exactly as before (line ends, CR, last line, long lines, sealed
  word lists); the only change users see is the lifted limit. Recommend approving after finding 1.

## Findings
1. BLOCKS (resource bound lost, untested at scale) author/values.fs:49, form.fs:72, build.fs:51. With the
   512-value cap gone, lfa-find (a linear scan of the whole term store per new node; R3, not done) is reached
   without bound. Right-nested arrows `P x n, -> x (n-1)` (`bin/leanforth check`, gforth 1.0): main 128: 1.5 s,
   250: 16.8 s, 500 and 1000: exit 3 (error 64) in 0.3 s; head 128: 1.6 s, 250: 17.9 s, 500: 260 s, 1000: killed
   at 295 s. With lfa-find replaced by `drop false` in a scratch copy: 0.6 s at 128 and 250, so lfa-find is the
   whole cost (about n^3.5; the reports' "1/3/5 ms for 200/400/800 binders" measured a shape that never searches).
   Fix: index shareable nodes in a lib/memo.fs memo keyed (tag first second), a memo-check! hook calling
   lfa-shareable?, cleared with the run's term store; `: lfa-find ( node -- term true | false ) lfa-share-key
   lfa-shares memo-find ...`; or keep a default limit (lfa-store-limit -> 512 records) until then. Add a test of
   a 2,000-arrow statement under a time budget and a fault.
2. should fix: three changed branches no test reaches; my planted faults survive tests/front/*, tests/author/
   author.fs, check_author.py and check_whnf/check_defeq --golden: whnf.fs:696 (wc-smatch-head: an unknown head
   constant answers none; planted: answers unsupported), groups.fs:135 (lfa-order-index not found -> lfa-order#;
   planted: 0), build.fs:50 (lfa-term-is?'s lfa-shareable? test; planted: dropped). Add a test and a fault each.
3. REUSE PASS: tag sets. kabstract.fs:78-79 `kab-binders`/`kab-tag-only?` is core's `lf-term-binder-tag?`
   (terms.fs:141): call it. instantiate.fs:87 `in-holes` = term-eqv.fs:87 `eq-unshared?` = present/print-names.fs:23
   `lf-pp-identity-tag?`. `lf-meta-tags`/`-tag-of?`/`-tag-in?` (meta-spine.fs:120-122) are a general term-tag
   operation buried in a front module beside core's `lf-tag-bit` (terms.fs:135, whose lf-binary-tags at :136 is
   the same OR chain by hand); about 15 tag OR chains remain (front/meta-check.fs:101, core/terms.fs:784 =
   let-terms.fs:35 `lf-let-tag?`, kernel/whnf.fs:550, present/print-analysis.fs:24, ...). Plan row in 9.4.8k:
   `: lf-tags ( tag1 .. tagn n -- mask )` in core/terms.fs (core: [kernel] gate), copies replaced.
4. REUSE PASS: module boundaries. mvars.fs:333 `lf-meta-want-parts` is a dag-walk step used by assign-check.fs:
   move it to dag-walk.fs as `dw-want-parts ( node walk -- child true | false )` with the copies the report lists
   (level-params lp-parts-pending, goal-print, term-find). `lf-meta-rebuilt`/`lf-meta-annot-over`
   (offset-walk.fs:80,82) serve kabstract.fs and mvars.fs, which do not use the walk: move them to meta-spine.fs
   beside lf-meta-named. beta-inst.fs uses ow-* without `require ./offset-walk.fs` (reached through
   instantiate.fs); add it.
5. REUSE PASS: `X store-ready drop X store-new-slot` is now in values.fs:50 and form.fs:73-74 besides scopes.fs:58
   and core (names.fs:175, input.fs:444, constant-references.fs:308): one store.fs word
   `: store-new-grown ( store -- addr index true | false )`. The duplicates baseline's "planned" group
   3a5e73ad792e cites 9.4.8k, but 9.4.8k's text has no store.fs item: add one (a library proposal needs a row).
6. note: library form. find.fs's profile (FORTH_LIBRARY.md) has no measured speed and no caller sizes from a
   real run (the profile rule); LIBRARY_WORDS.md shows find-index's loop-trick comment instead of its interface
   (move the interface line directly above the definition). texts.fs: header, example, tests, profile complete.
7. note: ow-memo-make (offset-walk.fs:133) frees and re-makes the memo every run (2 blocks per run, 1 before;
   live blocks after my sweep 48 vs 46), justified in its comment; not measured on a long run.
8. note: lf-tag-bit on a negative tag shifts by a negative count (undefined in Forth-2012) where the old `=`
   chains were total (corrupt terms only); `texts+` would lay a `\ comment` on its line down as texts.
9. note (item 5): lf-term-cons's unshared append (terms.fs:868) is benign: the author run turns sharing off,
   so no code may rely on equal terms being identical; it only loses a fast path. No src/core file changed.

## Tests and faults
No golden, pinned-Lean or expected file changed; tests/front/front.fs's 513-numeral case now sets a limit of
512 to keep testing error 64 (the cap's removal). Re-targeted faults (17 + 6) read correctly against the new
code; fe-whnf-fields-no-max now reads past the slab (out of bounds) but is caught. Commit 5222dd94 and its
replacement 5be06755 have the same tree (16310d10). No coverage, forth-quality or duplicates baseline raised;
duplicates 284 -> 256; the "accepted" group c0d6944876ba (sunfold and matcher readers) is reasonable.
Item 7: lfa-find blocks (finding 1); dag-walk per-walk memo, module boundaries and the old missing tests
(prop-quick, meta-check, kab-same, lfh-shaped?, me-lib-d?) are named 9.4.8k follow-ups.

## Reuse (searched)
LIBRARY_WORDS.md for find/index/scan/tag words (cells-index, any?, lower-bound, byte-scan: none does
find-index's job); FORTH_LIBRARY.md; grep of src/ for tag and name OR chains, `store-ready drop`, `lf-name-dotted?
.* or`, requires of every changed file; check-duplicates.py: 256 groups, none new or grown; check-lib-callers.py:
every lib file used (bigint planned). Findings 3-5.

## Forth style
forth-metrics --words 10 on offset-walk, find, texts, instantiate, beta-inst, whnf, infer, meta-spine, runner,
values, form: 566 words, 64% of 1-2 lines, 35% of 3-5, one of 6 (values.fs:105 lfa-item-term, a CASE, older),
none longer; deep shuffles 23, return-stack ops 61, globals 1 (runner's, older). offset-walk.fs: 35 words, none
long, 4 deep shuffles, 14 return-stack ops. infer.fs:191 if-enter uses `2 pick` and `>r`:
  : if-pi-skip ( type j -- body j outcome ) swap lf-term-second@ swap outcome-ok ;
  : if-flush-at ( type j i -- body i outcome ) tuck >r if-flushed r> swap ;
  : if-enter ( type j i -- type' j' outcome ) >r over if-pi? r> swap if drop if-pi-skip else if-flush-at then ;
wc-sm-out kept as a register with a stated reason: accepted.

## Probes run (gforth 1.0.0 from .tools; git archives of e3c5297a and d16b10b5 in the scratchpad)
- Differential: 500 random terms (sharing on; shared subterms, lambdas, pis, loose bvars, an assigned and an
  unassigned mvar, annotations, beta redexes) through instantiate1 (closed and loose value), abstract,
  instantiateRevBeta (m=2,1), headBeta, instantiateMVars, kabstract: output byte-identical, term indices included.
- Heap refusal sweep, k = 1..59, 250 terms x 5 operations: every refusal gives full or the unrefused result
  (both trees).
- 128 hostile .lf files (CRLF, CR only, no final LF, NUL, control and non-UTF-8 bytes, 1023/1024-char lines,
  70,000-char token, Forth words base/order/evaluate/bye, ...): 120 identical exit and output; the 8 differing
  are the lifted limit (errors 66, 18, 300 instead of 64, and finding 1's time-outs).
- 27 planted faults of my own: 24 caught by the front and author unit tests; 3 survive (finding 2).
Not run: the implementers' suites, pinned-Lean comparisons, Gforth 0.7.3, coverage. An AI review does not
replace the owner's [parser] approval.
