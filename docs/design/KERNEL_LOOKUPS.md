# Fewer table lookups by design (design, 2026-11-26)

Status: **designed, not reviewed, no code.** Base: branch `term-store-design` (8dd01528) and the
instantiation prototype that branch `kernel-speed-3` lands (memo reset in one step, stored hashes in table
slots, the lean instantiation walker, input leaf entries by a dense array; assumed landed). The owner's
route of 2026-11-25 ("Do 2b"): about 7-10 times Lean in pure Forth, native code only as a later proposal on
paper. Builds on [TERM_STORE.md](TERM_STORE.md) and its binding corrections, and the lessons of
[KERNEL_TERM_READS.md](KERNEL_TERM_READS.md) and [KERNEL_VALIDITY_CHECKS.md](KERNEL_VALIDITY_CHECKS.md).
Measurements: [kernel-lookups-2026-11-26](../development/measurements/kernel-lookups-2026-11-26/README.md).

## Summary for the owner (one page)

**What is slow after the landed changes.** Init's check takes **575.4 s at one thread** with the prototype's
four changes (measured; Lean's checker 31.0 s, nanoda 30.7 s): **18.6 times Lean**. The profile of that run
shows where: **universe substitution 138 s** (it walks every term twice, sorts what it reached and finds each
child's image by binary search), the **instantiation memo 60 s** (a hash-table lookup and insert at almost
every rebuilt node, though 90% of the lookups are a node's first sighting in its pass and only 0.3% of those hit), **hash-consing's two probes 52 s**, **reading the
input terms in their export format 57 s** (decoding each record on every read), and the per-operation layers
that remain (validity tests, frames, the base fetch on every read: about 100 s). All seconds are of the
check phase at one thread; shares of the profile converted at 5.9 s a point (estimate).

**What changes.** Three groups, each one review, one tier, one done check:

1. **One walker for every term pass, and a front memo.** The prototype's lean walker becomes one shared
   word with a small per-pass hook (as Lean's `replace_rec_fn`): instantiation, abstraction, shifting and
   universe substitution all use it. Universe substitution loses its second walk, its sort and its binary
   search. The memo gets a small direct-mapped front table: a first sighting costs one slot check instead
   of a hash probe, and an entry pushed out of the front table goes into today's table, so the memo answers
   exactly as today.
2. **Input terms decoded once, and two front tables.** At import each input node is written once in the
   store's 16-byte node format into a side array; every read then reads it like a store node. A small
   front table of recent conses answers up to about 40% of conses without either probe; most checker-cache
   lookups miss (72%), and a small presence filter per cache turns such a miss into one bit test.
3. **The remaining layers.** Validity tests move to the entry of each pass; whnf, inference and
   definitional equality use lean frames; the hottest read and probe words become Forth macros where
   measured.

**What it reaches** (estimates; basis in section 6): after group 1 about 445-485 s (14.4-15.7 times Lean),
after group 2 about 355-425 s (11.5-13.7 times), after group 3 about **265-375 s at one thread, 74-104 s at
four (8.5-12 times Lean, most likely about 10 times)**. This confirms the upper half of "7-10 times" and
corrects the lower half: 7 times (about 220 s) is not reachable with these levers in pure Forth; it needs
native primitives (the hashing, the probes, the node read), which stay a proposal on paper.

**Why it is safe.** Verdicts, diagnostics, reports and fuel stay identical: the front memo holds every
entry the table holds today, only in two places; the front tables answer only what the probes would
answer and check the node's identity; reading a decoded node gives the same fields. Every fail-closed
check stays where it is: an input node that is refused today is written with tag 0, which every read
refuses with today's diagnostic. No file, snapshot or certificate format changes.

**Memory and cost.** Groups 1 and 3 add under 1 MB a context. Group 2's side array adds about 60-100 MB on
Init's 779 MB peak (8-13%, estimate): that needs your approval (question 1). About 650-1,050 Forth lines
changed; about 1.3-1.5 M tokens a group, 4.2 M in all, plus a 0.3 M first experiment.

**Risks.** Universe substitution's fuel must come out identical on the new walker (question 2); the front
memo's spill and rollback rules are new trusted kernel code (planted faults and the identical-fuel check on
Init cover them); the side array's memory. **Recommendation:** do the 0.3 M experiment on the side array
first (section 8), then groups 1, 2, 3 in that order.

## 1. Where the 575.4 s goes

Basis: the prototype's profile of Init (58,163 samples, `check.prof`, measured 2026-11-25), its report
(575.4 s check phase, fuel 654,719,715, peak 778.8 MB, measured) and the counts on the decide slice
(Appendix A, measured on the prototype's tree, fuel 2,649,895 identical to main). Inclusive shares overlap.

| Part | Share | Seconds | Note |
| --- | ---: | ---: | --- |
| universe substitution (`lf-mixed-level-substitute`) | 23.4% incl. | 138 | audit walk and set 42, sort 14, level work 22, cons 19 |
| instantiation (`lf-open-pass`) | 34.1% incl. | 201 | of which the memo 60, conses 53 |
| hash-consing (`lf-term-cons`, all callers) | 12.7% incl. | 75 | input probe 24, store probe 28, append 15 |
| reads, exclusive: input decoding / base fetch / field words / store reads | 9.6 / 4.3 / 3.1 / 9.8% | 57 / 25 / 18 / 58 | `groups.py` |
| hash tables and hashing, exclusive | 12.7% | 75 | every table |
| checker caches: lookups, stores, key facts | about 13% incl. | about 75 | `lf-term-facts` 28 is mostly reads |
| validity, frames, outcome values, exclusive | 6.7 / 4.8 / 1.2% | 39 / 29 / 7 | |

Per unit of fuel on the decide slice: 0.247 memo lookups and 0.224 memo inserts, 0.315 conses (each an
input-tier attempt, 0.291 store probes), 0.079 checker-cache lookups (Appendix A).

## 2. The memo (question 1 of the brief)

**Counts** (decide slice, Appendix A): 655,857 lookups, 62,065 hits (9.5%), 593,792 inserts. Only
**62,673 lookups (9.6%) are of a node already seen in the same pass**; 60,339 hits are such second
sightings, 1,726 come from an earlier call (stamped "scope" calls keep their entries across calls while
they succeed), 457 hit at another binder offset than the node's first sighting. 61% of the lookups and
88% of the hits are on input-tier nodes.

**Lean** consults its cache only when `!is_likely_unshared(e)` (reference count above 1, `replace_fn.cpp`
34), and its cache lives for one call. LeanForth has no reference counts and a cross-call memo for
stamped calls whose hits save fuel, so the test must answer exactly as today's table.

**Candidates, measured or sized:**

- *A shared bit set when a second parent takes a node* (counted with a parent column): only 13,517 of
  258,355 store-node lookups (5.2%) are on nodes with at most one parent, and none hits; input nodes would
  need the importer's parent counts. It saves almost nothing. Rejected.
- *A per-node mark column* (pass serial, offset, result: 8-12 bytes a node over 12.2 M input expressions
  and the store's nodes): exact, but 150-270 MB (20-35% of the peak). Rejected for memory; a generation
  stamp alone is the same at 4-8 bytes and still needs the result somewhere.
- **A direct-mapped front memo with exact spill (recommended).** A per-context table of 4,096 slots of
  24 bytes (node, offset and call tag, result, the result's identity: 96 KB, in the L2 cache), slot =
  `hash-fmix(node) and mask`. Rules: (1) a lookup checks one slot; on a miss the memo table is probed
  only if this call, or for a stamped call its stamp, has spilled or kept entries there (a count per call
  and a small table of stamps: one probe per call, not per node); (2) an insert writes the slot; if the
  slot holds a live entry that today's table would still hold (this call's, or a successful stamped
  call's), that entry is first put into the table ("spilled"); (3) a hit checks the result's identity as
  `lf-kept-node?` does today; (4) an unstamped call ends by advancing the call serial (no clearing); a
  failed stamped call clears its slots by one scan (failures only) and its spilled entries by today's cut;
  the crowded rule counts front and table entries together and empties both by advancing an epoch.
  **Every entry lives in exactly one place, so every lookup gives today's answer: the same hits at the
  same visits, the same fuel.** Input-tier nodes are covered alike (keys are node numbers; no column over
  the tier). The store's growth does not matter (no address is kept; slots hold numbers).

Gain (estimate): today's 60 s is about 309 M table operations at about 190 ns; a slot check or write costs
about 20-50 ns (one or two loads in L2, a hash of one cell). With 90% first sightings and spills unknown
(counted by the experiment): **25-40 s**. Memory: 96 KB a context.

## 3. The cons (question 2)

**Counts**: 833,837 conses; the input tier gives 62,068 (7.4%), the store's table finds 375,752 (45.1%),
396,017 are new (47.5%). A key seen among the last conses: 41.9% of conses in a 1,024-entry direct-mapped
table, 62.4% in 65,536 entries (upper bounds: rollback frees store numbers and remakes some keys at the same
number; a real front table checks identity and misses there).

- *Probe only the store tier*: input duplicates would become store copies with other identities; the
  infer, whnf and defeq caches (keyed by identity, `caches.fs` 33-45) and defeq's pointer test would miss
  where they hit today: more fuel (the P5 experiment showed what losing sharing costs: fuel +37.6%).
  A fuel change: rejected without the owner.
- *A smaller key compare*: done by the landed stored hashes (a record is compared only on equal hashes).
- *Lazy conses of applications with a closed head*: changes identities. Rejected.
- **A front table of recent conses (recommended, group 2)**: 1,024-4,096 slots (tag, first, second,
  node, identity: 24 KB-96 KB a context). A hit whose node still has its identity and passes today's
  `lf-term-reusable?` and findability tests is today's answer: the store holds one live node per key, and
  the input tier's answer never changes within a context (the experiment confirms that the findability
  hook is stable within a context; if not, the hit re-asks it). A miss runs today's two probes and fills
  the slot. Gain (estimate): about 40% of the probes' 52 s less the slot check on every cons: **10-20 s**.

## 4. The reads (question 3, the biggest lever)

Today an input node is read in place from the decoded export (ADR 0016 C3): each field read fetches the
base, decides the tier, finds the record, reads its head, looks up the code by tag and parity, tests the
mode, reads the field and converts the child reference; a leaf's fields come from its leaf entry through
the dense array. Counted: 6.97 M field reads and 2.29 M data words on input nodes, 16.76 M record decodes
(Appendix A); profiled: input decoding 57 s exclusive.

| Option | Gain (estimate) | Memory (Init, estimate) | Gates |
| --- | --- | --- | --- |
| (a) one word reads a node's tag, first, second and data at once, used by every walker and cache key | 10-20 s | none | refactoring |
| (b) copy the input into the store tier's format at import and drop the tier | 50-60 s | +196 MB nodes, -180 MB stage only if the stage is freed | **format and gate change**: the stage records are what `--save-snapshot` writes (ADR 0020) and hold binder names (C1); refusals of malformed data would move to import; workers need a shared read-only segment, so it becomes (c) anyway |
| **(c) a decoded side array beside the stage** (recommended, group 2) | 40-50 s | +60-100 MB net | memory above 5%: owner; ADR 0016 C3 note |

**(c) in detail.** After the feed's checks, the importer writes for each input node one 16-byte node in the
store's format (tag and summary bits, first and second as node numbers, the data word) into a side array,
from the stage record and, for a leaf, its leaf entry. Reads of an input node then are the store's read with
another block address: one compare, one base, four 32-bit loads. The stage stays (snapshots, names,
printing); the side array is derived data, never written to disk, built once and borrowed read-only by
workers like the view tables. **Fail-closed checking keeps its places**: the stage and the feed refuse what
they refuse today; an input number with no node (an expression copied to the store, a leaf left without an
entry on purpose) gets tag 0, which the walkers' unknown-tag test and `lf-term-valid?` refuse at the same
read with the same diagnostic (the malformed-export tests must stay byte-identical). The P4 dense array and
the leaf-by-node table go (their only readers are the decode words). Layout: one slot per expression when at
most one parity of an expression is a node; the experiment counts the even (leaf and let twin) numbers that
are nodes and picks the layout (per input number would double the memory and is rejected). Import cost:
12.2 M nodes at 40-120 ns, 0.5-1.5 s a run, once (estimate).

(a) and (c) together: **50-70 s**, less about 10 s already taken by group 1's one read per visit.

## 5. One walker for every pass (question 4)

Lean's `replace_rec_fn` takes a function `f(e, offset) -> optional<expr>` and does the rest: cache, kind
switch, offsets under binders, `update_app`/`update_binding`. The shared walker does the same in Forth, with
the prototype's lean frames (a frame only for a node it rebuilds) and today's fuel rule:

```
lf-replace ( root job -- result outcome )
  job: closed? ( data offset job -- flag )         \ the pass's skip test on the node's data word
       leaf    ( node tag offset job -- result outcome true | false )  \ the pass's answer, or descend
       memo    ( job -- front )                     \ the front memo of section 2, or 0 for none
```

Each visit charges one unit after the same exhaustion test as today; a kept child (closed, a leaf the hook
keeps, a memo hit) is charged inline by `frame-charge`; the second child is charged only after the first
child's subtree returns; the binder check comes before any child is charged; every per-leaf fail-closed
test stays (unknown tag, well-formed bound variable, live free variable). Hooks per pass:

| Pass | closed? | leaf hook | Memo |
| --- | --- | --- | --- |
| instantiate, instantiate_rev, scope (`mixed-open.fs`) | loose range at most offset and no free variable | bound variable at or above offset | yes |
| abstract (`mixed-open.fs`, today the frame machine) | no free variable | free variable of the list | yes |
| shift (`mixed-shift.fs`) | loose range at most offset | bound variable at or above offset | yes |
| universe substitution (`mixed-level-substitute.fs`) | no universe parameter | Sort and constant: substitute the levels | yes, per call |

Beta (`mixed-beta.fs`) is instantiation and gets the walker through it; whnf, inference and definitional
equality call these passes and change only in group 3's frames. **Fuel per pass**: instantiate, abstract
and shift charge one unit a visit, as the prototype showed identical on Init. Universe substitution today
charges by its own walks; group 1 first writes its charges as a formula of the reached terms and
reproduces them exactly on the walker (Init and every pinned comparison); if that fails it stops and asks
(question 2). Gain (estimate): universe substitution 138 s to 48-69 s (one walk at instantiation's
per-visit cost, about 280 k visits on the decide slice against today's 0.644 s timed), **65-90 s**;
abstract and shift 2-4 s.

## 6. The caches (question 5)

Counts on the decide slice (hits / misses; Appendix A): infer 27,542 / 75,618 (27% hits), infer-only
4,628 / 7,196 (39%), whnf_core 901 / 59,579 (1.5%), whnf 4,085 / 4,579 (47%), unfold 6,882 / 2,542 (73%),
success pairs 1,202 / 13,474 (8%), failure pairs 2 / 326. Lookups per unit of fuel: 0.079 in all; 72% miss.
Keys: a node's identity and 0, or a sorted pair of identities (two cells), in `lib/memo.fs` tables.

**What Lean does.** The same caches at the same places (`caches.fs` header, Lean's `type_checker.cpp`
lines there); Lean 4.35.0 has **no** union-find of equal terms (type_checker.h 33-39: is_def_eq is not
transitive), so that option is not Lean's and is not proposed.

**Without changing verdicts or fuel**: (1) a **presence filter per cache** (a 1-Mbit bitmap by hash of the
identity, set on store, cleared with its cache by a list of the bits set): a miss whose bit is clear needs
no probe; false positives only cost the probe they cost today. Gain 8-12 s (the lookups' 21 s, 72%
misses). (2) Cheaper keys through (a) and (c): the key's facts are 28 s today, mostly input decoding,
counted in section 4. **What would change fuel**: dropping a cache (whnf_core hits only 1.5%, but each hit
saves units), keying by structure instead of identity (more hits), or Lean's per-call replace cache instead
of the stamped cross-call memo (1,726 fewer hits on the decide slice). None is proposed; each would need the
owner with a before/after fuel table.

## 7. Groups, gains and gates (questions 6 and 7)

Baseline: 575.4 s at one thread (measured); four threads about 159.6 s (estimate: main's 182.1 / 656.5).
Ratios against Lean's 31.0 s at one thread; nanoda 30.7 s at one, 9.7 s at four. Gains are net of
overlaps (Appendix B).

| Group | Contents | Forth lines | Saves (s) | After, 1 / 4 threads (s) | Times Lean | Memory | Tokens |
| --- | --- | ---: | ---: | --- | ---: | --- | ---: |
| 1 | shared walker `lf-replace` (prototype P3 generalised); abstract, shift and universe substitution on it (set, sort, binary search retired); front memo with exact spill in `lib/memo.fs` | 250-400 | 90-130 | 445-485 / 123-135 | 14.4-15.7 | +0.1 MB a context | 1.4-1.5 M |
| 2 | decoded side array (c) and the one-read word (a); cons front table; cache presence filters | 200-300 | 60-90 | 355-425 / 98-118 | 11.5-13.7 | +60-100 MB | 1.3-1.4 M |
| 3 | validity at pass entry (KERNEL_VALIDITY_CHECKS slices 2-3); lean frames in whnf, inference, defeq; measured Forth macros (`POSTPONE`) for the node read, the slot probe and the frame step | 200-350 | 50-90 | 265-375 / 74-104 | 8.5-12.1 | none | 1.3-1.4 M |

Each group ends in Init at 1 and 4 threads beside Lean (31.0 s) and nanoda (30.7 s, 9.7 s at four), the
decide slice at 1 and 4, identical reports outside `measured`, `settings` and `run`, identical fuel, and a
profile of Init (the next group's input). **The design reaches about 9-12 times Lean, most likely about
10** (estimate, midpoint 320 s). **Left for a native-code proposal** after group 3 (estimate): hashing and
probes about 40-50 s, the node read and frame step's instruction count about 100 s, memory misses about
40-55 s (as in C); the six primitives of TERM_STORE section 2 could bring 4-6 times (corrections, item 7).

**Gates.** Behaviour-preserving refactoring (owner, 2026-11-19; review and full tier, reported afterwards):
the walker, the front memo, the cons front table, the presence filters, the one-read word, the validity
move, lean frames and Forth macros, each with identical verdicts, diagnostics and fuel. **The owner's
gate:** group 2's memory growth above 5% (question 1); any fuel change, in particular universe substitution
if its charges cannot be reproduced (question 2); option (b) or anything else that changes what the
importer reads, where malformed data is refused, or the snapshot and certificate formats (not proposed);
native code (not proposed). The front memo and the macros are trusted kernel code (corrections, item 5):
reviewed as such, with planted faults (a stale slot, a spill skipped, a hit without the identity check).

**Reuse.** `lib/memo.fs` gains the front level (its own tests and faults; the checker caches may use it
later); `lib/htab.fs`, `lib/hash32.fs` (`hash-fmix`), `lib/frame.fs` (`frame-charge`),
`lib/store-columns.fs` unchanged; the presence filter is a small library (`lib/bitfilter.fs`, a bitmap
with a list of set bits) with the caches as its first caller; the walker lives in `kernel/mixed-rebuild.fs`
and replaces the visit words of `mixed-open.fs`, `mixed-shift.fs` and `mixed-level-substitute.fs` (the
latter's `lib/sort.fs` call and binary search go). No hand-written table, sort or stack.

**Work in flight.** `kernel-speed-3` (landing now) is the base; group 1 starts after it merges. The
front-end simp branch reads terms by name only and is not touched. KERNEL_VALIDITY_CHECKS slices 2-3 are
group 3.

## 8. The first experiment (question 8)

The riskiest lever is the side array (memory, layout, refusals). In a scratch copy of the prototype
(never merged, under 0.3 M tokens): build the side array in `feed.fs` after the leaf entries; switch the
input branches of `lf-term-tag@`, `lf-term-first@`, `lf-term-second@`, `lf-term-data-word`,
`lf-term-valid?` and `lf-tin-leaf#` to it; count the even numbers that are nodes. **Numbers that decide**,
on the decide slice (identical report and fuel) and one Init run at one thread by the coordinator: check
phase down at least 35 s on Init (go), peak memory up at most 100 MB (else the per-expression layout
fails: stop and report), every malformed-export test of `tests/import` byte-identical. In the same copy,
count the front memo's spills (slots of 1,024 and 4,096) on the decide slice: below 5% of inserts confirms
section 2's gain.

## 9. Questions for the owner

1. **Memory.** Group 2 keeps each input term once more, decoded, beside the export's copy: Init's peak
   grows from about 780 MB to about 840-880 MB (8-13%) for about 40-50 s. Allow it? *Recommendation: yes, if
   the first experiment measures at least 35 s for at most 100 MB; the export's copy must stay because
   snapshots are written from it.*
2. **Fuel of universe substitution.** If its charges cannot be reproduced exactly on the shared walker, may
   Init's fuel numbers change once (verdicts unchanged, a before/after table shown)? *Recommendation: only
   if the exact formula fails; try it first.*
3. **Target.** The three groups reach about 9-12 times Lean, likely about 10, not 7. Go on with them, and
   write the native-code proposal (hashing, probes, node read: 4-6 times) on paper after group 3?
   *Recommendation: yes; 7 times needs native code, and the proposal needs your approval anyway.*

## Appendix A. Counts (decide slice, prototype tree edcb539, 2026-11-25 23:57)

`count-patch.py` on a scratch export; fuel 2,649,895 (identical to main); load 7.7-14.0 (counts only).

| Count | Value | Count | Value |
| --- | ---: | --- | ---: |
| walks set up / their visits (closed roots not counted) | 98,493 / 1,237,176 | memo lookups / hits / inserts | 655,857 / 62,065 / 593,792 |
| second sightings in a pass | 62,673 | hits: same pass / earlier call / other offset | 60,339 / 1,726 / 457 |
| stamped lookups / hits | 294,669 / 50,873 | input-node lookups / hits | 397,502 / 54,549 |
| store lookups on nodes with at most one parent / hits | 13,517 / 0 | conses in instantiation / substitution | 585,650 / 141,915 |
| conses: input / store found / new | 62,068 / 375,752 / 396,017 | recent-key table 1 K / 64 K (same node) | 349,545 (336,565) / 520,579 (481,485) |
| field reads input / store | 6.97 M / 8.11 M | data words input / store | 2.29 M / 2.01 M |
| input record decodes | 16.76 M | substitutions / Sorts / images / binary rebuilds | 14,985 / 21,775 / 175,110 / 131,928 |

## Appendix B. How the seconds were estimated

- Profile points to seconds: 575.4 s / 97.62 (the check phase's share) = 5.9 s a point.
- Group 1: universe substitution's 138 s keeps its level work (22 s) and conses (19 s, less after group 2)
  and walks about 280 k visits on the decide slice (two per binary rebuild plus roots) at the prototype's
  601 ns a visit, against 0.644 s timed today: 35-50% remains, 48-69 s, saving 65-90 s; the memo 25-40 s
  (section 2); abstract and shift 2-4 s (`lf-abstract` 0.68%). Sum 92-134, rounded 90-130.
- Group 2: side array 40-50 s (input decoding 57 s to about 10); one-read word 10-20 s less 10 s taken by
  group 1; cons front 10-20 s; presence filters 8-12 s. Sum 58-92, rounded 60-90.
- Group 3: validity family 39 s exclusive, of which about half moves to pass entry (KERNEL_SPEED's 13-17
  of 36 points on the older main): 15-25 s; frames 29 s exclusive and outcome plumbing 7 s, lean frames
  halve them: 15-20 s; macros halve the instruction part of the remaining reads and probes (about 40-90 s
  after group 2, as the chase benchmark's col to raw step): 20-45 s. Sum 50-90.
- Four threads: each one-thread figure times 182.1 / 656.5 (main's measured scaling; memory-bound parts
  may scale worse).
