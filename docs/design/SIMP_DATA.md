# Simp data: Lean's simp sets, simprocs and norm_num table for the front end

Design (2026-11-17), revised after its independent design review (verdict "ready after fixes", 15 findings, all
resolved: section 12); nothing built. Plan rows FE9 (`simp`), S7 (`by-ring`), S8 (`by-norm-num`); the owner's request
of 2026-11-17 (the path to real numbers and trigonometry). Lean references: pinned Lean 4.35.0's `src/lean/Lean/` and
Mathlib's `Mathlib/Tactic/` in `.tools/mathlib/mathlib4` (read-only). Counts come from the commands in
[the measurement folder](../development/measurements/simp-data-2026-11-17/README.md) unless marked as the reviewer's;
sizes in lines of Forth are estimates. Appendices: A counts, B Lean source notes, C simprocs and `norm_num` extensions.

## For the owner (one page)

**What.** A fourth version of the elaboration data (the second file `leanforth check --elab-data` reads beside a
library's export) that adds what Lean's `simp` and Mathlib's `norm_num` look up while they work: which theorems are
simp lemmas, in which simp sets, with their priority and index keys; the theorems `simp` uses to step inside `if`,
folds and the like (congruence lemmas); which definitions `simp` unfolds; which built-in procedures ("simprocs") are
switched on; and `norm_num`'s table of extensions. Then the order of the slices that build `simp`, `ring` and
`norm_num` on it.

**Why.** Proofs about real numbers go through `simp`, `ring` and `norm_num`. Lean keeps these lists in its own `.olean`
files, not in the export LeanForth reads, exactly as it kept the instance lists that format 2 brought in.

**How big (measured).** `Init`: 10,296 lemmas in the default simp set, 488 in 7 named sets, 341 simprocs on by
default, 59 congruence lemmas, 32 definitions to unfold. All of Mathlib: 101,283 default lemmas, 3,691 in 36 named
sets, 346 default simprocs, 111 congruence lemmas, 85 `norm_num` extensions. The records add about 4.5 MB to
`Init`'s data and 63 MB to Mathlib's (whose export is 6,258 MB).

**The gate ([import] and [format]).** The records are hints, not facts. `simp` uses a lemma by naming it in the proof
it builds, and LeanForth's kernel checks that proof against the lemma's statement in the export. A wrong record can
make `simp` fail, try a lemma that does not fit (its own matching then refuses it), take another route than Lean, or
build a proof the kernel rejects; it can never make a false theorem accepted. LeanForth also checks the records
against the export: every name, and, the first time a lemma is tried, its index keys and two flags recomputed from its
statement. A difference refuses the file, except where Lean's own records legitimately differ (a lemma marked
`no_index`, whose mark the export does not keep: then the recorded keys are used, as for instances). A lemma whose
theorem the export lacks keeps its place in the order and answers *unsupported* when `simp` reaches it.

**Risks.** (1) About one simp lemma in ten is used through a helper theorem Lean makes (`Foo._simp_1`) that the
export leaves out (1,009 of `Init`'s, 8,220 of Mathlib's, plus 1,039 private lemmas); so do the equation theorems
Lean makes on demand for `simp [f]` and for `match`. Until the export carries them, those answer unsupported
(question 2). (2) Simprocs are Lean programs: each needs a Forth port (341). (3) Mathlib's scale: 2.1 million index
keys, so branches are built only when first used. (4) Lemma order is Lean's only if the recorded ranks are.

**A finding that changes the order.** `ring` does not use `simp` or its lemma lists: it uses `norm_num`'s number
core (`derive` and the extension table). Only `ring_nf`, full `norm_num` and `simp` need the lemma database. So:
`norm_num`'s core, then `by-ring`, then full `by-norm-num`; and all three wait for a slice not yet planned, the
front end running on Mathlib (question 5).

**Recommendation.** Approve the format and the gate (questions 1-4); then build SP1a (the data and its checks), with
the simp core (SP1b) after the tactic plug-ins' first slices.

## 1. What `simp` reads, as Lean 4.35.0 keeps it

**A simp set** (`SimpTheorems`, `Meta/Tactic/Simp/SimpTheorems.lean:599`): two discrimination trees `pre` and `post`
of simp lemmas (tried before, `@[simp ↓]`, or after visiting the subterms); `lemmaNames`, the lemmas' identities (for
`simp [-foo]`); `toUnfold`, definitions marked `@[simp]`, with `toUnfoldThms`, their equation theorems; `erased`
(empty in `Init` and Mathlib: the tool stops otherwise).

**A simp lemma** (`SimpTheorem`, `:155`):

| Field | Meaning | In format 4 |
| --- | --- | --- |
| `keys` | the index path of the left side: `DiscrTree.mkPath lhs` under `simpGlobalConfig` (reducible, no iota, no projections, `:282`) | recomputed when first tried; a recorded star over a recomputed term is "wide" (§4) |
| `levelParams` | empty for every global lemma | the tool stops otherwise |
| `proof` | the constant used as proof: the theorem or a helper `Foo._simp_N` (`:465`) | a theorem of the export, else the record is `simp_left_out` |
| `priority` | 1000 unless set (104 in `Init`, 500 in Mathlib differ) | trusted |
| `post` | false for `↓` lemmas (1 in `Init`, 13 in Mathlib) | trusted |
| `perm` | the sides are equal up to renaming (`isPerm`, `:292`); rewriting then needs a term order | recomputed |
| `origin` | `.decl name post inv`: the theorem and whether it was given as `←` | name checked; `inv` is identity only |
| `rfl`, `backwardRfl` | proof by definition (`isRflProof`, `:232`, reads the `defeq` tags); `dsimp` uses only these | recomputed from the tags |

`inv` only names the lemma for `simp [-foo]` and `simp [← foo]` (`Origin`'s equality, `:105-112`); the direction of
the rewrite is read from the proof's own statement, which `preprocess` already swapped (`:338-343`), so a wrong `inv`
cannot turn a rewrite round.

**Preprocessing** (`preprocess`, `:319`): `p ↔ q` becomes `p = q` by `propext`, `a ≠ b` becomes `(a = b) = False`,
`¬p` becomes `p = False`, `p ∧ q` two lemmas, any other `p` becomes `p = True`, `←` swaps the sides. Each result is a
helper theorem made by `mkAuxLemma` (`Meta/Tactic/AuxLemma.lean:43`), named after the declaration being elaborated.

**Theorems Lean makes on demand.** Besides the `_simp_N` helpers of `@[simp]` lemmas, Lean makes, while `simp` runs:
a helper for each bracket lemma `simp [h]` that needs preprocessing (`:463-468`), named after the theorem being proved;
the equation theorems of a definition given in brackets (`getEqnsFor?`, `:567`); a `match`'s equation and splitter
theorems (`Match.getEquationsFor`, `Rewrite.lean:369`). All begin with `_` or are reserved names, so leanexport keeps
one only when an exported proof uses it (`dumpEnv` filters `isInternal`). The first kind LeanForth must make itself
(it is new for each proof) and hand to the kernel before the theorem; the others it can take from the export once the
export carries them (question 2).

**Lookup and order.** `rewrite?` (`Rewrite.lean:207`) asks the tree for every lemma that may match the term, including
those for a prefix of an over-applied term (`getMatchWithExtra`, `DiscrTree/Main.lean:489`), sorts them by priority
with a stable descending insertion sort (`:220`; not the instances' ascending sort tried from the last, which would
reverse equal priorities) and tries them in order. Within a priority the tree decides: the star branch before the
term's own key (`:453`), values in insertion order. Each record carries its rank, its place in a depth-first walk of
its root key's branch, as instance records do; LeanForth inserts in rank order. When matching, a metavariable in the
term is the key `other`, not a wildcard (`:393`). `simp [foo]` with `foo` already in the set replaces it in place,
since tree values compare equal by proof (`DiscrTree/Basic.lean:139-147`, `SimpTheorems.lean:276-277`).

**Sets.** `simp` uses the default set plus what is written in brackets; `simp only [..]` starts from `eq_self` and
`iff_self` (`Elab/Tactic/Simp.lean:512, 564`) and no simprocs (`:568`); both use the congruence lemmas (`:569`). Named
sets (`push_cast`, `mfld_simps`, ...) come from `register_simp_attr`, used by name in brackets or by tactics.

**Simprocs** are Lean functions keyed like lemmas (`Nat.reduceAdd` turns `2 + 3` into `5`): data can name one and give
its keys and phase (`Simprocs`, `Types.lean:417`); its behaviour is code to port. 390 are built into Lean; 341 are on
by default on `Init` (346 on Mathlib), 244 of them without a proof term ("dsimprocs").

**Congruence.** `@[congr]` lemmas (`SimpCongrTheorems.lean:23`) say how to step inside a function with dependent
arguments (`ite_congr`, `Finset.sum_congr`). Lean keeps a list per function, highest priority first and, among equal
priorities, the newest first (`:39-47`; `Init` has 15 `forIn'` lemmas, all at 1000), so records carry a rank. For
other functions `simp` builds a congruence lemma itself (`mkCongrSimp?`, `Meta/CongrTheorems.lean`): code, not data.

**Defaults** (`Init/MetaTypes.lean:154`): `decide := false`, `arith := false`, `ground := false`, `maxDischargeDepth :=
2`, `memoize := true`, `failIfUnchanged := true`, `zetaDelta := false`.

## 2. Counts

Commands and full tables: appendix A. "Not in export": no declaration of the export LeanForth reads.

| | `Init` | Mathlib |
| --- | ---: | ---: |
| default set: lemmas (pre / post); tree nodes | 10,296 (1 / 10,295); 60,303 | 101,283 (13 / 101,270); 1,477,322 |
| ... index keys; proved by `rfl` | 94,769; 898 | 2,133,211; 19,645 |
| ... proof a helper `_simp_N` / of which not in export | 1,917 / 1,009 | 13,966 / 8,220 |
| ... origin not in export (private, internal) | 18 | 1,039 |
| ... marked `no_index` (reviewer's count) | 84 | 20 |
| default set: definitions to unfold (with equations) | 31 (12) | 387 (340) |
| named simp sets registered / non-empty / their lemmas | 9 / 7 / 488 | 49 / 36 / 3,691 |
| simprocs declared (built in / in libraries); in the default set (dsimprocs) | 390 / 0; 341 (244) | 390 / 34; 346 (245) |
| congruence lemmas (functions) | 59 (43) | 111 (94) |
| `defeq` / `backward_defeq` tags | 1,691 / 3,220 | 31,096 / 62,658 |
| `norm_num` extensions (tree entries) | — | 85 (91) |
| records in the shape of section 3 | 4.5 MB | 63 MB |

## 3. Getting it out of pinned Lean: format 4

The tool stays (`scripts/export-elab.sh` runs `scripts/export_elab.lean`, then `scripts/export_elab.py` finishes and
binds) and gains record kinds; format 4 is format 3 plus:

*Numbering (2026-11-25, review of slice SD-a):* the number 4 is what slice SD-a writes and reads: format 3.2 plus
the `congr` records and the `defeq` tag ([ELABORATION_DATA.md](../programming/ELABORATION_DATA.md), "Format 4").
The other additions below come with slice SD-b as format `"4.1"` (a text, as `"3.1"` and `"3.2"` were introduced),
which SD-a's reader refuses as another version (error 7), never misreads.
*Format 4.1 (2026-11-26, simp group 3):* written and read for the `realized` kind alone (`name`, `fun`, `kind`
`congr_simp`, `arg_kinds`: the kinds `congrKindsExt` holds, which simp compares with those it computes); no
statement member, since the theorem is the export's own and the kernel checks it. The other kinds of the table
below are still to come ([ELABORATION_DATA.md](../programming/ELABORATION_DATA.md), "Format 4.1").
*Format 4.1, simp group 4 (2026-11-26):* the default sets alone, written by `scripts/export_simp.lean` and
finished by `scripts/export_simp.py`: `simp_set`, `simp` (written `simp_lemma`), `simp_left_out` (with the origin
and proof names the export lacks), `simp_unfold` (name only, read to answer unsupported) and one `simproc` record
per entry of the default simproc set (its declaration's keys, phase, rank and `dsimproc`), in place of the two
kinds `simproc` and `simproc_entry` below ([ELABORATION_DATA.md](../programming/ELABORATION_DATA.md), "Format 4.1:
the default simp set").

| Kind | Members | From |
| --- | --- | --- |
| `simp_set` | `name`, `simprocs` (its simproc set or null) | `simpExtensionMapRef`, `simpAttrNameToSimprocAttrName` |
| `simp` | `set`, `origin`, `inv`, `post`, `proof`, `priority`, `perm`, `rfl`, `backward_rfl`, `keys`, `rank` | each set's trees |
| `simp_left_out` | `set`, `post`, `keys`, `rank`, `priority`, `reason` (`not_exported`) | a value whose origin or proof the export lacks |
| `simp_unfold` | `set`, `name`, `eqns` | `toUnfold`, `toUnfoldThms` |
| `simproc` | `name`, `keys`, `dsimproc` | `simprocDeclExt`, `builtinSimprocDeclsRef` |
| `simproc_entry` | `set`, `name`, `post`, `rank` | each simproc set's trees |
| `congr` | `name`, `fun`, `hyps`, `priority`, `rank` (its place in its function's list) | `congrExtension` |
| `norm_num` | `name`, `pre`, `post`, `keys` (one list per pattern), `rank` | Mathlib's `normNumExt` |
| `tag` | gains `defeq`, `backward_defeq` | `defeqAttr`, `backwardDefeqAttr` |

Names and keys are written as in format 3. One line, from the measurement (its `level_params`, always 0, left out):

```json
{"simp":{"backward_rfl":true,"inv":false,"keys":[{"arity":6,"const":["HAdd","hAdd"]},{"arity":0,"const":["Nat"]},{"arity":0,"const":["Nat"]},{"arity":0,"const":["Nat"]},"star","star",{"lit":"0"}],"origin":["Nat","add_zero"],"perm":false,"post":true,"priority":1000,"proof":["Nat","add_zero"],"rank":33,"rfl":true,"set":["simp"]}}
```

That is `Nat.add_zero : n + 0 = n`: the left side `@HAdd.hAdd Nat Nat Nat inst n 0`, the instance and `n` stars. The
finisher sorts records by kind, then set, tree, root key and rank, so each branch of each tree is a run of lines.

**Bound to the export** as today: the header names the export's SHA-256, the finisher writes the records' SHA-256
into the export's manifest, and `leanforth check` refuses data for another export. Like `instance_left_out`, a tree
value whose origin or proof the export lacks becomes `simp_left_out` with its keys, rank and priority, so ranks run
0, 1, 2, ... without a gap and Lean's order is kept. Simproc names are kept whatever the export holds: they name Lean
functions, matched by name to LeanForth's ports.

**The tool stops** (exit status 1, nothing written) on what format 4 cannot say: a global lemma with universe
parameters of its own or a proof that is not a constant, an `fvar` key, a non-empty erased set, a value whose first
key is not its root, lemma names that differ from the trees' values. None occurs on `Init` or Mathlib.

**Size, time, determinism.** Measured: `Init`'s records 4.5 MB in about 2 s of Lean (2.0 GB); Mathlib's 63 MB in
13.5 s (28.6 s cold, 9.1 GB). With today's 3.7 MB, `Init`'s format-4 file is about 8.2 MB. Two runs on `Init` gave
byte-identical output (SHA-256 prefix `b477c852883d9f46`); the finisher sorts, so equal input gives equal bytes.

## 4. Trust and the gate, in plain language

The data says "this theorem is a simp lemma; try it on terms shaped like this, before that one". It never says "this
is true". Every lemma `simp` uses, every helper and every simproc result reaches the kernel by name, or as a step the
kernel's own definitional check must accept, inside the final proof; any helper LeanForth makes is kernel-checked
before the theorem and never enters the axiom allowlist. So:

- a lemma wrongly listed, left out, or with a wrong priority or rank: `simp` takes another route than Lean or fails;
- wrong keys: the lemma is tried on terms it does not fit, and `simp`'s matching refuses it, or it is never tried;
- a wrong "by definition" flag or `defeq` tag: `simp` leaves out a proof step; the kernel rejects the theorem, or,
  since the kernel's definitional check is stronger than `dsimp`'s, accepts a proof Lean's `dsimp` would not have
  made: a difference from Lean, never a false theorem;
- a wrong simproc entry: a Forth simproc runs where Lean's would not; its result is checked as above.

**Checked when the file is read** (fail closed: the whole file refused): form, counts and SHA-256; the export
binding; every `simp_set`, `simp_unfold`, `congr`, `simproc`, `simproc_entry`, `norm_num` and tag record in full
(names are declarations of the right kind, a congruence lemma's hypothesis positions within its binders, ranks
gapless); for `simp` and `simp_left_out`, the line form, that each branch's ranks run 0, 1, 2, ... and that each
`set` has a `simp_set`. The file's bytes stay in memory (63 MB for Mathlib), so what is parsed later is what was hashed.

**Checked when a branch is first reached** (its lines parsed): each origin and proof is a theorem of the export, and
each `simp_left_out` really names something the export lacks.

**Checked when a lemma is first tried** (kept in a memo): its keys recomputed from its proof's statement (Lean's
`mkSimpTheoremKeys`: telescope, `whnfR`, the equation's left side, `mkPath`), its `perm` by `isPerm`, its `rfl` from
the proof and the tags; a congruence lemma's positions by `mkSimpCongrTheorem` when first used. A recorded star
where the recomputed keys have a term is "wide" (Lean's `no_index`, whose mark the export drops; `instances.fs`
lines 51-54, error 114): the lemma is used with its recorded keys, since keys only choose what to try. Any other
difference refuses the data at that point and later. A check that cannot finish leaves the lemma unverified: it
answers unsupported if `simp` would use it, as does a `simp_left_out` reached in candidate order (its statement is
unknown, so LeanForth cannot tell whether Lean would have used it), and an unported simproc whose keys match.

**On trust from pinned Lean:** set membership, priority, `post`, `inv`, ranks (they depend on Lean's name hashes),
which simprocs are on, their keys and phases, unfolded definitions, the tags, the `norm_num` table.

**Axioms.** `simp`'s proofs use `propext` (every `↔` lemma) and, through lemmas, `Classical.choice`; the axiom report
lists them (plan FE9's [axiom] gate). Nothing here adds an axiom.

## 5. Storing and querying it in the front end

- **One discrimination tree for every user.** `instances.fs` holds a complete trie (nodes, children, values, insertion
  in rank order, the `getUnify` walk) private to instances. SP1a moves it into `src/front/discr-tree.fs` (values are
  cells; one tree per root key, built at first use; insertion that replaces an equal value in place), re-points
  `instances.fs` onto it, and adds `getMatch` and `getMatchWithExtra`.
- **Keys** stay in `elab-keys.fs`; recomputing uses `discr-keys.fs`'s `lf-dt-path` with a "match" mode for the
  metavariable rule (§1).
- **Records:** `elab-data.fs` reads the small kinds into slabs at once and keeps the `simp` lines as bytes with each
  branch's line range; a branch's records are parsed at its first lookup. Simp sets by name and lemmas by origin are
  `lib/htab.fs` tables; per-lemma check results a `lib/memo.fs` table; the candidates' priority sort `lib/sort.fs`
  (stable, descending).
- **Memory and time (estimates):** about 40 bytes per key, 100 per lemma, 40 per tree node: `Init` 3.8 + 1.0 + 2.4 MB
  if every branch were built; Mathlib 85 + 10 + 59 MB in that worst case, far less lazily (the reviewer counts 1,304 of
  `Init`'s lemmas under the `Eq` root alone, which is why keys are checked per lemma, not per branch). Hashing 63 MB at
  `lib/sha256.fs`'s measured 70 MB/s takes about 1 s; hashing Mathlib's 6.26 GB export (about 90 s) costs more.

## 6. What `simp` then needs (outline; each slice gets a short design)

- **Where it lives.** The simp core is Meta-level code that `by-simp`, `norm_num1`, `ring_nf`, `simp_all` and
  `field_simp` all call: `src/front/meta-tactic/simp*.fs`. Only the `by-simp*` words go into `src/front/tactics/`
  (error codes 500-539: 300-339, once reserved by the plug-in design, hold the runner's codes 300-309; see TACTIC_SIMP.md).
- **Runner services simp needs**, to be added to the plug-in design's list (its appendix D): the location reader
  (`at h`, `at *`); bracket modifiers (`-foo`, `*`, `↓`/`↑`, `←`, set and simproc names); a configuration reader
  (`+arith`, `(config := …)`); replacing or clearing a hypothesis; handing helper theorems to the kernel before the
  theorem (S4's service).
- **The core** (Lean `Simp/Main.lean`, `Rewrite.lean`, `Types.lean`: 4,556 lines with the sets' code;
  `Elab/Tactic/Simp.lean` 864): `Step` and `Result`, pre and post passes, `visit` and its cache, congruence (automatic
  through `fun-info.fs`, then `@[congr]`), instantiating a lemma, `perm`'s term order, `rfl` lemmas without proof
  steps, closing a goal by `of_eq_true`, `failIfUnchanged`; then conditional lemmas with the default discharger.
- **Simprocs**, most used first (appendix C): `reduceIte`, `reduceDIte`, `reduceCtorEq` and `Nat`'s 25, then `Int`,
  `Fin`, the fixed-width integers, `Char`, `String`, `BitVec` (`BuiltinSimprocs/`: 2,112 lines).
- **The other forms:** `dsimp`, `simp_all`, `simpa`, `simp at *`, `contextual`, `+arith` (`Arith/`: 783 lines),
  `decide := true`, `+ground`, `seval`.

## 7. What `norm_num` and `ring` add

- **`norm_num`'s core** (Mathlib `NormNum/Result.lean` 586 lines, `Core.lean` 376): results `IsNat`, `IsInt`, `IsRat`
  with proofs; `derive`, which looks extensions up in their tree (`Core.lean:98-106`); `norm_num1`, which runs them
  inside `simp`'s traversal without simp lemmas; `norm_num`, with the default set and simprocs (`:220-248`).
- **The extensions** (85, appendix C): `Basic.lean` (21: `+`, `*`, `-`, casts, `0`, `1`, `OfNat`; 736 lines), `Pow`,
  `Inv`, then `Eq`, `Ineq`, `DivMod`, `GCD`, `Prime` (`Nat.Prime 37`), `Parity`, `RealSqrt`, `OfScientific`.
- **`ring`** (`Ring/Common.lean` 1,342 lines, `Basic.lean` 602): the normal form `ExSum`/`ExProd`/`ExBase` over a
  `CommSemiring` found by type-class synthesis, coefficients from `NormNum.derive` (`Ring/Basic.lean:468` calls it,
  so it needs the table and the `Basic`, `Inv` and `Pow` extensions, not `norm_num1`'s traversal), atoms compared by
  `isDefEq` at reducible transparency. `ring` falls back to `ring_nf` (`RingNF.lean` 248), whose cleanup uses its own
  lemma list (`:103-117`), with `simp`'s core.
- **First needed:** the front end on Mathlib (slice MF below); type classes on Mathlib's hierarchy (FE3; instance
  search exists, `synth.fs`); numerals `OfNat`, `OfScientific` and rationals (FE2); `lib/bigint.fs`.

## 8. Slices

Each ends in a command a user can run, with its tests (seven classes, planted faults) and documentation
(`LANGUAGE_REFERENCE.md` for each new word) in the slice, and is sized for one agent (about 1,500 lines of Forth with
its tests). Sizes are estimates (about 1.2 lines of Forth per line of Lean ported).

| Slice | Command at the end | Contains | Forth | Needs |
| --- | --- | --- | ---: | --- |
| SP1a | `scripts/export-elab.sh init.elab.ndjson init.ndjson Init` writes format 4; `leanforth check --elab-data` accepts it and refuses each planted fault | the tool for every kind (Lean, Python: about 300 lines), the reader and load checks (amended 2026-11-18 by [LF_LIBRARIES.md](LF_LIBRARIES.md) §6, pending the owner's answer to its question 7: `discr-tree.fs`'s move out of `instances.fs` with replace in place goes to MF2, `getMatch` and `getMatchWithExtra` to SP1b with their first caller) | 1,200 less the move | the gate |
| SP1b | `by-simp-only[ Nat.add_zero ]` proves `n + 0 + 0 = n`, terms node for node Lean's | the core with `Eq` bracket lemmas only; other lemma forms and functions with `@[congr]` lemmas answer unsupported | 1,400 | SP1a, plug-ins (a2) |
| SP1c | `by-simp-only[ ]` with `↔`, `¬`, `←` and hypotheses, through `if` | `@[congr]`; `preprocess` and bracket helpers handed to the kernel | 1,200 | SP1b |
| SP2a | `by-simp` on one-line `by simp` proofs of `Init`, "K of N" | the default set, lazy branches, per-lemma checks, `simp_left_out`, unfolding, the 5 generic and 25 `Nat` simprocs | 1,500 | SP1c |
| SP2b | `by-simp` with conditional lemmas and `at h`; K of N rises | the discharger, locations, the export widened to the on-demand theorems (question 2) | 1,300 | SP2a |
| SP3 | `by-dsimp`, `by-simp-all`, `by-simpa`, `simp +arith`; `Init`'s `simp` proofs, K of N | the other forms; simproc families, one branch each, in parallel | 4,000 | SP2b |
| MF | `leanforth check` of a LeanForth statement about `ℝ` against Mathlib's snapshot and data | the front end on Mathlib: its export and format 3/4 data loaded, FE3 on Mathlib's hierarchy, memory measured; its own design | 1,500 | FE3 |
| SP4 | `by-simp` proves `(x : ℝ) * 1 = x` | Mathlib's simp data in use, lazy loading measured | 600 | SP2b, MF |
| S8a1 | `by-norm-num1` proves goals `derive` closes whole: `(2 : ℝ) ^ 10 = 1024`, `(7 : ℚ) / 2 < 4` | `Result`, `derive`, the extension table, `Basic`, `Inv`, `Pow`, `Ineq` | 1,500 | MF |
| S7 | `by-ring` proves $(a + b)^2 = a^2 + 2ab + b^2$ over `Nat`, `Int`, `ℝ` | `ring1`'s normal form (its own design may cut it in two) | 2,500 | S8a1 |
| S8a2 | `by-norm-num1` on numerals inside a goal | `norm_num1` on `simp`'s traversal | 800 | S8a1, SP1b |
| S8b | `by-norm-num` proves `Nat.Prime 37` and the S8 row's cases | full `norm_num` with the default set; `Prime`, `DivMod`, `GCD` | 1,500 | S8a2, SP4 |

**Can start in parallel:** SP1a's tool work (Lean and Python) right after the gate; the `discr-tree.fs` move, which
meets the front reuse pass (plan 1.1.8) in `instances.fs`; MF's design; SP3's simproc families once SP2a fixes the
simproc interface. `SP1a → SP1b → SP1c → SP2a → SP2b → SP4` and `MF → S8a1 → S7` are chains. SP1b starts after the
plug-in design's slice (a2) has merged, using its registration words.

## 9. Reuse

- **Uses:** `discr-keys.fs` (`lf-dt-path`, `lf-dt-key`, todo lists), `elab-keys.fs`, `elab-data.fs`'s reader and
  slabs, `instances.fs`'s trie (moved), `meta-env.fs`, `meta-config.fs` (simp's transparency and `simpGlobalConfig`),
  `fun-info.fs` (automatic congruence), `defeq.fs`, `whnf.fs`, `infer.fs`, `mvars.fs` (marks for trying a lemma),
  `tactic-rewrite.fs`'s `Eq.mpr` construction, `handover.fs` (helper theorems to the kernel); `lib/htab.fs`,
  `lib/memo.fs`, `lib/sort.fs`, `lib/slab.fs`, `lib/runs.fs`, `lib/sha256.fs`, `lib/bigint.fs`, `lib/json.fs`; on the
  tool side `export_elab.py`'s `export_decls`, key and rank checks and manifest binding.
- **New shared module:** `src/front/discr-tree.fs`, replacing `instances.fs`'s private trie in the same branch
  (SP1a). LeanForth-specific (Lean's keys), so a module, not a `src/lib` library.
- **Not re-implemented:** no second key store, sort, hash table or JSON reader; the trie moves, it is not copied.

## 10. Work in flight on the same files

- `s2-finish` changes `elab-data.fs` and `meta-env.fs`: SP1a's reader starts after it merges.
- The tactic plug-in design (`TACTIC_PLUGINS.md` on branch `tactic-plugin-design`, not yet on main) changes
  `tactic-run.fs`, `errors.fs` and the registration words; SP1b waits for its slice (a2) and §6's services join its
  appendix D.
- The front reuse pass (plan 1.1.8) may touch `instances.fs`: whichever runs first moves the trie, the other rebases.

## 11. Questions for the owner

1. **Approve format 4 and its [import]/[format] gate** (the record kinds of section 3, the checks of section 4,
   including the "wide" rule for `no_index` lemmas and `simp_left_out` records)? *Recommendation: yes.* It is the
   kind of data you approved for instances on 2026-11-13, checked the same way; it can only steer which proof is
   tried, and the kernel checks the result.
2. **Theorems Lean makes on demand and the export leaves out** (`_simp_N` helpers, equation and `match` theorems):
   (a) export them with the library, (b) carry them in the data, or (c) make them in Forth? *Recommendation: (a) for
   those of the library, plus (c) for the helpers of the user's own bracket lemmas,* which Lean makes anew in each
   proof. (a) keeps proofs identical to Lean's; its cost is regenerating every export, snapshot and binding, under
   the same [import] gate. Until then those lemmas answer unsupported.
3. **Port simprocs family by family, most used first, each compared with pinned Lean; when an unported simproc
   matches a term, `simp` answers unsupported** rather than skipping it? *Recommendation: yes;* a silent skip could let
   `simp` succeed by another route than Lean's.
4. **Load Mathlib's simp data lazily:** hash the whole file and keep its bytes, parse a branch at first use, check a
   lemma when first tried? *Recommendation: yes;* it avoids building 1.5 million tree nodes no proof needs, with no gap
   between the check and the use.
5. **Order:** SP1a-SP2b; a new slice MF (the front end on Mathlib) that SP4, `norm_num` and `ring` wait for; then
   S8a1 (`norm_num`'s core), S7 (`by-ring`), S8a2 and S8b; and correct the plan's S7 and S8 rows: `ring` uses
   `norm_num`'s core, not the reverse? *Recommendation: yes;* `by-ring` then waits for neither `simp` nor its lemma
   database.

## 12. Review

The independent design review (2026-11-17, `.claude/work/pending-reports/2026-11-17-simp-data-design-review.md`,
"ready after fixes") made 15 findings; all are taken as proposed. Where each is answered:

| # | Finding | Answered in |
| --- | --- | --- |
| 1 | `no_index` stars would refuse Lean's own data (blocking) | §4 "wide" rule; §2 count; summary; Q1 |
| 2 | records missing from the export: keep their rank (blocking) | §3 `simp_left_out`; §4; Q1 |
| 3 | congruence lemmas need a rank | §1 Congruence; §3 `congr` |
| 4 | theorems Lean makes on demand; helper work into SP2 | §1; §6; §8 SP1c, SP2b; Q2 |
| 5 | lazy loading against the load-time hash and checks | §4 (bytes kept, what is checked when); §5; Q4 |
| 6 | check keys per lemma, not per branch | §4; §5 |
| 7 | SP1 and SP2 too big for one agent | §8 SP1a-c, SP2a-b |
| 8 | the core at Meta level; runner services for the plug-in design | §6; §10 |
| 9 | no slice for the front end on Mathlib | §8 MF; Q5 |
| 10 | `inv` is identity only | §1 |
| 11 | stable descending sort | §1; §5 |
| 12 | replace in place on re-adding | §1; §5 |
| 13 | a wrong `defeq` tag may also be accepted | §4 |
| 14 | reuse list | §9 |
| 15 | `norm_num` records' `pre`/`post` | §3 |

Also from the review: S8a cut into S8a1 (`derive` and the table, which `by-ring` needs) and S8a2 (`norm_num1`).

## Appendix A. Counts

From [the measurement folder](../development/measurements/simp-data-2026-11-17/README.md): `init.out`, `mathlib.out`,
`normnum.out`, `mentions.out`. Exports: S1's done-check `Init` export (59,349 declarations) and the night build's
Mathlib export (729,263). Tree nodes include the root.

**Named simp sets with lemmas, `Init`:** `int_toBitVec_meta` 356, `wf_preprocess` 50, `bitvec_to_nat` 36, `push_cast`
24, `method_specs_simp` 16, `bool_to_prop` 5, `mvcgen_simp` 1 (plus 1 unfold); empty: `seval`, `Std.Internal.tree_tac`.

**Named simp sets with lemmas, Mathlib (36):** `push_cast` 2,085, `int_toBitVec_meta` 401, `mfld_simps` 322,
`nontriviality` 164, `basify_simp` 111, `rclike_simps` 109, `coassoc_simps` 67, `mon_tauto` 52, `wf_preprocess` 50,
`Std.Internal.tree_tac` 47, `functor_norm` 42, `bitvec_to_nat` 36, `ghost_simps` 32, `parity_simps` 16, `mvcgen_simp`
16, `method_specs_simp` 16, `enat_to_nat_top` 14, `integral_simps` 12, `polynomial_pre` 10, `monad_norm` 10,
`rify_simps` 9, `enat_to_nat_coe` 9, `reduce_mod_char` 8, `qify_simps` 8, `pnat_to_nat_coe` 7, `bool_to_prop` 5,
`fin_omega` 5, `zify_simps` 5, `aesop_default` 4, `push_end` 4, `pull_end` 4, `polynomial_post` 4, `typevec` 2,
`aesop_SimpleGraph` 2, `aesop_Sym2` 2, `aesop_builtin` 1; 13 registered sets are empty.

**Default set details:**

| | `Init` | Mathlib |
| --- | ---: | ---: |
| lemma records / distinct origins | 10,296 / 10,295 | 101,283 / 101,278 |
| proof is the origin itself | 8,379 | 87,317 |
| proof in the export / not | 9,269 / 1,027 | 92,028 / 9,255 |
| `←` lemmas / `perm` lemmas | 0 / 0 | 11 / 1 |
| longest key list | 98 | 1,942 |
| first key a star or `other` | 0 | 0 |
| record bytes (default set) | 4,181,551 | 60,886,579 |
| unfold equations in the export | 13 of 13 | 611 of 613 |
| congruence lemmas in the export | 59 of 59 | 111 of 111 |

**`norm_num`:** 85 extensions in 91 tree entries (some have several patterns), all both `pre` and `post`, none erased;
15,771 bytes of records.

## Appendix B. Lean source notes

Lean 4.35.0, `src/lean/Lean/`:
- `Meta/Tactic/Simp/SimpTheorems.lean`: `Origin` 69-131 (equality distinguishes `←`); `SimpTheorem` 155-183;
  `isRflProof` 232; `simpGlobalConfig` 282; `isPerm` 292; `preprocess` 319-390; `mkSimpTheoremKeys` 396-417;
  `mkSimpTheoremCore` 424-447; `mkSimpTheoremFromConst` 453-473 (the `_simp` helper, 465); equation theorems for a definition, `getEqnsFor?` 567; `SimpTheorems` 599-609;
  `SimpExtension` 718; `simpExtensionMapRef` 751; option `backward.dsimp.useDefEqAttr` (default true) 40.
- `Meta/Tactic/Simp/Attr.lean`: `simpExtension` 87, `sevalSimpExtension` 89, `Simp.Context.mkDefault` 97.
- `Meta/Tactic/Simp/Simproc.lean`: `builtinSimprocDeclsRef` 34, `simprocDeclExt` 49, `builtinSimprocsRef` 116,
  `builtinSEvalprocsRef` 119, `simprocExtensionMapRef` 373, `simprocExtension` 382, `simprocSEvalExtension` 384,
  `simpAttrNameToSimprocAttrName` 428. `Types.lean`: `SimprocOLeanEntry` 398, `Simprocs` 417, `Methods` 424.
- `Meta/Tactic/Simp/SimpCongrTheorems.lean`: `SimpCongrTheorem` 23, the per-function list (newest first among equal
  priorities) 39-47, `congrExtension` 49, `mkSimpCongrTheorem` 56.
- `Meta/Tactic/Simp/Rewrite.lean`: `rewrite?` 207 (`getMatchWithExtra` 215, priority sort 220; `getMatchLiberal`
  247 when `index := false`), `Match.getEquationsFor` 369, `simpMatch` 376, `rewritePre`/`rewritePost` 389-399, `dischargeDefault?` 637.
- `Meta/DiscrTree/Main.lean`: `mkPath` 329, `getKeyArgs` 350 (a metavariable is `other` when matching, 393),
  `getMatchLoop` 438 (star first, 453), `getMatch` 483, `getMatchWithExtra` 489, `getUnify` 567.
- `Meta/Tactic/AuxLemma.lean`: `mkAuxLemma` 43 (not stored in `.olean` caches; names from `mkAuxDeclName`).
- `Meta/DefEqAttrib.lean`: `backwardDefeqAttr` 86, `defeqAttr` 111.
- `Elab/Tactic/Simp.lean`: `simpOnlyBuiltins` 512, `mkSimpContext` 554-580.
- `Init/MetaTypes.lean`: `Simp.Config` from 154.

Mathlib (`Mathlib/Tactic/`): `NormNum/Core.lean` `NormNumExt` 54, `NormNums` 76, `normNumExt` 84, `derive` 98
(`getMatch` 106), `methods` 220, `deriveSimp` 232, simp set choice 247-248; `Ring/Common.lean` imports 8-9,
`ExProd` 128; `Ring/Basic.lean` `NormNum.derive` called 468, `proveEq` 548, `ring1` 596; `RingNF.lean` cleanup lemmas 103-117.

## Appendix C. Simprocs and `norm_num` extensions

**Default simprocs by namespace** (`Init`; Mathlib adds `ExistsAndEq`, `Matrix`, `Complex`, one more `Nat` and the
root `cancelIso`): `BitVec` 65, `Fin` 33, `Int` 28, `Nat` 25, `Char` 24, `Int8`/`Int16`/`Int32`/`Int64` 19 each,
`UInt8`/`UInt16`/`UInt32`/`UInt64` 16 each, `String` 13, `Array` 3, `ISize` 2, `USize`, `Lean`, `List` 1 each, and five
at the root: `reduceIte`, `dreduceIte`, `reduceDIte`, `dreduceDIte`, `reduceCtorEq`.

**Simprocs named in source** (a lower bound on use: the default set runs them unnamed): in `Init`'s sources 29 of 346
are named, led by `reduceIte` 123, `reduceDIte` 47, `reduceCtorEq` 43, `Nat.reducePow` 32, `UInt32.reduceToNat` 17,
`Nat.reduceAdd` 11; in Mathlib's 19, led by `reduceIte` 175, `reduceDIte` 147, `Fin.isValue` 77, `reduceCtorEq` 60,
`Int.reduceNeg` 53, `Nat.reduceAdd` 45, `Fin.reduceFinMk` 17. Tactic calls in Mathlib's sources: `simp only` 28,003,
`simpa` 16,762 (`simpa only` 4,437), `dsimp` 5,841, `ring` 7,053, `ring_nf` 411, `norm_num` 839, `field_simp` 287.
Which simprocs a proof *ran* is not in its term; SP2 measures it by running pinned Lean with the simp trace on the
cases it targets.

**`norm_num` extensions by file** (count of `@[norm_num` in the source): `NormNum/Basic.lean` 21, `Ordinal` 8, `Inv` 5,
`GCD` 4, `Data/Rat/Floor` 4, `LegendreSymbol` 3, `IsSquare` 3, `DivMod` 3, two each in `RealSqrt`, `Prime`, `Pow`,
`Parity`, `NatLog`, `ModEq`, `Irrational`, `Ineq`, `BigOperators`, one each in eleven more files. Sizes of
`NormNum/`: 8,612 lines with `Ring/` (`Basic` 736, `Result` 586, `BigOperators` 412, `LegendreSymbol` 409, `Core` 376,
`Pow` 331, `Ineq` 327, `Irrational` 325).
