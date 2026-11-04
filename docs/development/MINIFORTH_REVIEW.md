# MiniForth (Leonardo de Moura) — research review for LeanForth

*Research review written 2026-11-03 for plan workstream W9 ([plan](../project/PLAN_DRAFT.md#w9-related-work)); recommendations are proposals, not decisions. MiniForth has no licence: LeanForth takes ideas only and copies no code.*

Prepared 2026-11-03 by a Claude Code research agent. Untrusted analysis, not a
design decision. LeanForth was read, not changed.

**Source.** <https://github.com/leodemoura/MiniForth>, cloned read-only to
`.claude/work/MF/download/MiniForth/` at commit `e8756e2` (the head of
`main`). Nothing from it was built or run. All 36 tracked files were read in
full: README, `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, the
CI workflow, `Main.lean`, `MiniForth.lean` and the 28 modules under
`MiniForth/`, 3,133 Lean lines in all.

**Not done.**
- I did not compile MiniForth. That its proofs build rests on its own CI run
  [39718826223](https://github.com/leodemoura/MiniForth/actions/runs/39718826223),
  which reports *success* on `e8756e2`.
- I did not export any Lean closure, so the closure claims in §4 are
  reasoned, not measured.
- I did not read the ADR 0019 draft that another agent is writing.

Paths such as `Deep.lean:280` mean `MiniForth/Deep.lean` line 280 at
`e8756e2`.

---

## 1. What MiniForth is

**Purpose.** It is a Lean tutorial on programming-language semantics, not a
Forth system. The README opens with "A small Lean tutorial for programming
language semantics" and says: "This is a teaching language inspired by
Forth, not an implementation of a Forth standard. In particular, its global
dictionary does not model an interactive dictionary with successive
redefinitions."

**Facts.**

| Item | Value |
| --- | --- |
| Author | Leonardo de Moura, 12 commits |
| First commit | 2026-10-20 15:05 −0700 (`c6d1a87`, "Add MiniForth semantics and verification course examples") |
| Last commit | 2026-10-21 20:47 −0700 (`e8756e2`) |
| Other commit messages | all "Checkpoint" |
| GitHub repository created | 2026-10-22T03:43Z |
| Licence | **none**: no LICENSE file, and the GitHub API reports `"license": null` (queried 2026-11-03) |
| Toolchain | `leanprover/lean4:v4.35.0`, the same pin as LeanForth |
| Packages | none (`"packages": []`); it imports only `Std` and `Lean` |
| CI | `leanprover/lean-action@v1` runs `lake build` |

### Language scope

`Basic.lean`, `Quotation.lean`:
- integer literals, including negative ones;
- primitives `+ - * = DUP SWAP DROP` (`Prim`, 7 constructors);
- calls by name;
- `IF … ELSE … THEN`, where **ELSE is mandatory**: `[forth| IF 1 THEN]` is a
  parse error that a test requires (`Quotation.lean:186`).

It has:
- no loops, so recursion is the only iteration;
- no `EXIT`, return stack, memory, constants, variables, I/O or execution
  tokens;
- no `STATE`, `IMMEDIATE` or defining words other than `:`.

Names are case-sensitive (README:37).

### Values, stack and failures

`Basic.lean:15-37`:
- `abbrev Stack := List Int`, with the head as the top of the stack;
- unbounded mathematical integers: "Integers are mathematical integers, not
  bounded machine words";
- `=` gives −1 or 0, and `IF` treats any nonzero value as true;
- `RuntimeError` is `stackUnderflow | unknownWord`;
- `Result := Except RuntimeError Stack`.

### Dictionary and program

- `Env := String → Option Body` is global.
- `Program.env` finds the first declaration with the name
  (`Basic.lean:68-72`).
- Forward references and recursion are allowed.
- `Program.link` (`Link.lean:50`) rejects duplicate names and unresolved
  calls, "including calls in unselected branches".
- `Program.link_ok_iff` proves that the executable linker is exactly the
  `WellFormed` predicate.
- `Program.link_no_unknown` (`LinkCorrectness.lean:90`) proves that a linked
  program never fails with `unknownWord` on any input stack.

### Compile and interpret state

There is none. Programs are written as Lean term quotations: `[forth| …]`,
`[forthDecl| : NAME … ;]` and `[forthProgram| …]`.
- **Lean's parser** handles them through syntax categories and macros
  (`Quotation.lean:32-116`). No Forth outer interpreter is involved.
- A bare name bound to a Lean local variable becomes a literal push, and
  `{term}` pushes any Lean expression.
- `CALL name` forces a call. These "construct syntax trees parameterized by
  Lean values; they do not add runtime variables" (README:43-45).
- A delaborator, `PrettyPrinter.lean`, prints syntax trees back as Forth
  inside proof goals.

### Representations

| Layer | File | Form |
| --- | --- | --- |
| Shallow | `Shallow.lean` | `Prog := Stack → Result`; combinators `seq` (`>>>`), `push`, `bin`, `branch` |
| Deep big-step | `Deep.lean:12-26` | mutual inductive predicates `Exec env : Instr → Stack → Result → Prop` and `Eval env : Body → Stack → Result → Prop`; **no fuel** |
| Deep small-step | `Deep.lean:72-101` | `Config := run code stack \| error e`; `Step`; `Steps` (reflexive-transitive) |
| Executable | `Deep.lean:243-292` | `transition` (the unique next configuration); `runFrom env fuel config : Option Result`; "Fuel counts machine transitions"; `none` = "exhausted fuel, not a runtime error or a proof of divergence" |
| Bridge | `Denote.lean` | `denote prog : Body → Shallow.Prog`, correct under `CallsAgree env prog` |

`Instr` is `push | prim | call | branch (yes no : List Instr)`, a **nested**
inductive type: `Instr` occurs inside `List Instr`.

### What is proved

The project has no `sorry`, `axiom` or `native_decide` in any file. It does
not run `#print axioms`.

- **Semantics adequacy** (`Deep.lean`):
  - `eval_iff_steps`: big-step equals small-step on every finite outcome,
    errors included;
  - `eval_deterministic`;
  - `runFrom_sound` and `runFrom_complete`;
  - `eval_iff_run : Eval env code s r ↔ ∃ fuel, run env fuel code s = some r`.

  The fuel interpreter is therefore proved sound and complete against a
  semantics that has no fuel.
- **Linking**: `link_ok_iff` and `link_no_unknown`.
- **Equivalence** (`Equivalence.lean`):
  - `Equiv env a b := ∀ s r, Eval env a s r ↔ Eval env b s r`, which keeps
    errors observable;
  - congruence lemmas `Equiv.append` and `Equiv.cons`;
  - inlining, `call_equiv`;
  - a verified constant folder, `constantFold_correct`;
  - `swap_swap_not_equiv_nil`: dropping `SWAP SWAP` is unsound, because
    underflow changes.
- **Contracts** (`WeakestPrecondition.lean`):
  - `WP` (total correctness), `Hoare`, `WLP`, `Safe` and `SafeWLP`, kept
    deliberately apart;
  - the rules `wp_append` (`WP (a ++ b) Q = WP a (WP b Q)`), `wp_push`,
    `wp_prim`, `wp_call`, `wp_branch_*`, `hoare_seq` and
    `hoare_consequence`;
  - `wp_implies_safeWLP`, which follows from determinism.
- **Programs**:
  - `factorial_correct` for every natural number and every stack below it,
    by induction (`Recursion.lean:41`);
  - `forever_no_eval`: `: FOREVER FOREVER ;` has no finite outcome, shown by
    `run_forever` for every fuel plus `run_complete` (`Divergence.lean`);
  - the exact WP of the branch-dependent word `ADD-WHEN`, and
    `IF + ELSE THEN ≡ 0 = IF ELSE + THEN` (`Conditionals.lean`);
  - eight algebraic program laws (`ProgramEquivalence.lean`).
- **A `grind` version** of each lesson (`MiniForth/Grind/`):
  - `Rules.lean` registers the generic semantic equations;
  - the call rule is guarded with `=?=` and multi-pattern `guard`
    constraints;
  - `Tactics.lean` defines `forth_wp`, a `simp` set of proved WP rules that
    turns a Hoare triple into an arithmetic verification condition, and
    `forth_unfold`, which expands one call.

### How it is tested

Everything is tested inside Lean:
- `example … := rfl` and `by cbv`;
- `#guard` and `#eval`;
- `#guard_msgs` on printed goals;
- a `run_elab` loop that requires malformed quotations not to parse;
- printer round trips (`PrettyPrinterTests.lean`): print, re-parse,
  re-elaborate, then `isDefEq` at widths 120, 30 and 10, including adversarial
  names (`«DUP»`, `«IF»`, `""`, `"λ"`, a local called `SQUARE`).

Two kinds of testing are missing:
- **No Forth host or differential testing.** It is never compared with
  Gforth or any Forth system.
- **Little execution evidence.** `Main.lean` prints sample runs and a
  small-step trace, and that is all.

---

## 2. Comparison with LeanForth's program IR and its Lean semantics

LeanForth side: `docs/programming/PROGRAM_IR.md`,
`tests/reference/program-ir.lean`, `docs/programming/PROGRAM_VC.md` and
`docs/programming/PROGRAM_IR_RUN.md`.

| Aspect | MiniForth | LeanForth IR 0.1 |
| --- | --- | --- |
| Cells | `Int`, unbounded | `Cells` of any width ≥ 2 bits; two's-complement `wrap`; literals must `Fits`; bitwise words act on `unsigned`/`signed` bit patterns |
| Primitives | 7 | 38, with Forth-2012 stack effects |
| Partial operations | none (no `/`) | `/`, `MOD`, `RSHIFT` outside the agreed domain give **unmodeled**, never a guess |
| Control | `IF ELSE THEN` (ELSE required), calls, recursion | `IF [ELSE] THEN`, `BEGIN WHILE REPEAT`, `EXIT`; the reader refuses recursion |
| Return stack | none | separate; a fresh, empty one per call, which must be empty on return (**unbalanced**) |
| Definitions | `:` only | words and `CONSTANT`s (**badConstant**) |
| Dictionary | global and late-bound; forward refs; first match; linker rejects duplicates | Lean `lookup` is also first match over the whole list; the *reader* allows only earlier definitions, refuses redefinitions in any case of letters, and lower-cases names as Gforth finds them |
| Failures | `stackUnderflow`, `unknownWord`; divergence = no derivation | `underflow`, `unmodeled`, `unbalanced`, `unknownWord`, `badConstant`, `outOfFuel`; divergence is not expressible |
| Fuel | only in the executable, counted in small steps; **the semantics has none**; adequacy proved | **part of the normative `run`**: it bounds call depth and loop repetitions; theorems state how much fuel is enough (`enough : b.toNat + 3 ≤ fuel`) |
| Recursion scheme of `run` | `runFrom` is structural on fuel | `termination_by fuel code => (fuel, sizeOf code)`: well-founded recursion |
| Memory | none | none in the IR; separate Lean models with function-backed bounded memory (`tests/reference/program-contracts.lean`, `MEMORY_PROGRAM_REFERENCE.md`) |
| Specification style | `Eval` relation, `Equiv`, WP/WLP/SafeWLP/Hoare as Lean lemmas | the word's result equals a reference model (`callWord … = .next …`); a contract theorem `∃ out, … ∧ post`; obligations written by an untrusted Python generator, then proved by Lean |
| Automation | `grind` annotations; `forth_wp` | `ir_simp` (`simp only` with `step.eq_1`…`eq_38`), `omega` |
| Link to real Forth | none | reader from real source; Gforth vs Forth IR interpreter vs Lean, three ways (5,152 cases, plus 1,200 runs of 300 random IR programs per seed against Lean) |
| Source locations, receipts, assumptions | none | yes (`@line:col`, receipt schema 0.2, seven listed assumptions) |

### Where MiniForth's model is better or more complete

1. **Semantics without fuel, and adequacy.**
   - MiniForth defines meaning by derivations and proves the fuel
     interpreter sound and complete (`eval_iff_run`).
   - In LeanForth fuel is part of the meaning, so every theorem carries a
     fuel hypothesis, and partial correctness and divergence cannot be
     stated.
   - LeanForth also has no lemma that more fuel never changes a result that
     is not out-of-fuel. I found none in `program-ir.lean`.
2. **Several correctness notions, kept apart.** MiniForth has total (`WP`),
   safe partial (`SafeWLP`) and liberal (`WLP`) correctness, and says when
   each applies. LeanForth's contract theorem is total correctness only. Its
   receipts do not name which notion is proved.
3. **Program equivalence that keeps errors.** `Equiv`, with congruence and a
   verified transformation, gives tools that LeanForth will need for
   translation validation (plan 8.4.3). They would also let LeanForth relate
   two IRs of one source, for example from the old reader and the new
   vocabulary.
4. **The weakest-precondition calculus as proved Lean lemmas.** In
   MiniForth, generating verification conditions *is* rewriting with proved
   rules (`forth_wp`), and it handles branch-dependent stack depth exactly
   (`Conditionals.wp_exact`). LeanForth gets the same assurance differently:
   a Python generator writes per-path obligations, and a final theorem about
   `callWord` makes it safe.
5. **Linking as a separate, proved stage.** `link_no_unknown` removes a
   failure kind for well-formed programs. LeanForth's reader refuses unknown
   names, but no Lean theorem uses that fact.

### Where LeanForth is ahead

MiniForth's own exercise list ends with "Replace mathematical integers with
bounded words": LeanForth has already done that, and has:
- loops, the return stack, `EXIT`, constants and 38 primitives;
- explicit *unmodeled* failures instead of invented results;
- Gforth's handling of upper and lower case in names;
- a tested connection to a real Forth host;
- receipts.

For anything run on Gforth, LeanForth's model is the more faithful of the
two.

### Where aligning would help

- Adopt points 1, 2 and 4 above, *additively*. Keep `run` as the executable
  and as the three-way comparison's reference.
- Do not align the cell model or the dictionary: see §5, "Not to adopt".

---

## 3. What it suggests for the two-mode design (ADR 0019)

**MiniForth has no outer interpreter, compile state or `IMMEDIATE` words.**
Lean's parser does all its parsing. So it gives **no direct recipe** for a
correctness vocabulary's `:`, `IF`, literals or defining words. What it does
suggest:

1. **Syntax, linking and semantics are three separate stages, each with its
   own guarantee** (README tutorial step 3: "Explain that quotation is
   convenient notation, not a new semantics").
   - For ADR 0019, running the source in correctness mode is the "syntax
     plus linking" stage. It is untrusted, and it produces IR.
   - The IR semantics stays the only thing proved.
   - A Lean predicate `WellFormed` on the emitted IR, checked by `decide`,
     plus a `link_no_unknown`-style theorem, would let contracts drop
     `unknownWord` formally instead of relying on the vocabulary.
2. **Keep control flow structured.**
   - MiniForth's `branch (yes no : List Instr)` makes the branch WP rule one
     line (`Grind/Rules.lean:194`, `wp_branch_result`). LeanForth's IR is
     already nested.
   - Correctness-mode `IF`/`ELSE`/`THEN`/`BEGIN`/`WHILE`/`REPEAT` should
     build nested blocks with a compile-time control-flow stack, in the
     style of Forth's own origin and destination entries, not jumps.
   - `LEAVE` and `EXIT` stay structured exits.
3. **Bind calls when they are compiled; do not copy MiniForth's late-bound
   global `Env`.**
   - In Forth, a definition refers to the *latest earlier* definition of a
     name, and to itself only through `RECURSE`.
   - MiniForth's README says its dictionary does not model this.
   - In two-mode, Forth's own `FIND` resolves each name when it is compiled.
     The IR should record that resolution as a definition identity, for
     example its index, not a name looked up later.
   - Otherwise `: foo 1 ; : bar foo ; : foo 2 ;` is modelled wrongly once
     redefinition is possible. Today the reader refuses redefinition, and the
     Lean `lookup` takes the first match.
   - The vocabulary must either keep refusing redefinitions or emit identities.
4. **Round-trip tests.** MiniForth checks print, then re-parse, then
   re-elaborate, giving the identical term, at several widths, with
   adversarial names. For ADR 0019, the matching test is:
   1. IR text, or the receipt's source;
   2. printed as Forth;
   3. loaded in correctness mode;
   4. giving byte-identical IR.

   Test names that collide with vocabulary words, look like numbers (`5`,
   `-0`) or differ only in letter case.
5. **Literals and defining words are LeanForth's own design problem.**
   - MiniForth avoids the hardest two-mode question: numbers are not words,
     so the vocabulary cannot see a literal unless correctness mode controls
     number conversion.
   - The options are LeanForth's own compile loop over the Forth
     dictionary, Gforth recognizers (not Forth-2012) or tagged symbolic
     handles.
   - MiniForth gives nothing for `CONSTANT`, `CREATE`/`DOES>`, `VARIABLE` or
     `VALUE`.

**Can MiniForth's semantics serve as an independent reference?**
- **For Gforth: no.** It was never compared with a Forth system. Unbounded
  integers differ from cells, ELSE is required, names are case-sensitive and
  there is no return stack.
- **For LeanForth's IR: only marginally.** The shared fragment is 7
  primitives, branches and calls, without overflow. A Lean simulation
  theorem from MiniForth's `Eval` to `ProgramIR.run`, on programs whose
  values all fit in a cell, is possible but proves little.
- **It cannot be vendored**, because it has no licence (§6).
- Gforth, already the authority in the three-way comparison, and the
  Forth-2012 text remain the right references.
- **Worth borrowing:** the *style* of `Main.lean`'s `showTrace`, which prints
  "the same transitions used by the verified evaluator". A step-trace
  comparison between `src/program/ir-run.fs` and Lean, not only final
  results, would sharpen the three-way comparison and its diagnostics.

---

## 4. What it suggests for the theorem side

1. **A small real-Lean corpus on the same pin.**
   - Lean 4.35.0, with no packages.
   - `Basic`, `Shallow`, `Deep`, `Equivalence`, `WeakestPrecondition` and
     `Divergence` import only `Std` and each other. `Link`, `Denote` and the
     tests import `MiniForth.Syntax`, hence `Lean`.
   - That Std-only slice exercises features the checker must handle:
     - mutual inductive predicates (`Exec`/`Eval`), with
       `Eval.rec (motive_1 := …)`;
     - a nested inductive (`Instr` contains `List Instr`);
     - structural recursion over it (`Body.calls`, `denote`);
     - `Except`, and `String` and `Int` literals;
     - `omega`, `decide` and `cbv` proofs.
   - The `Grind/` files are a heavier stress test.
   - It fits plan 5.2.5 (mutual and nested inductives) and 6.4.1 (corpus
     differential), checked locally only (§6).
2. **LeanForth's own IR model needs nested inductives and well-founded
   recursion** (this is a finding about LeanForth, made visible by
   comparison).
   - `ProgramIR.Instr` has `ifElse (yes no : List Instr)` and
     `loop (test body : List Instr)`, a nested inductive.
   - `ProgramIR.run` uses `termination_by (fuel, sizeOf code)`, so it is
     well-founded recursion.
   - So plan task **5.5.1**, "clamp obligations … checked by LeanForth",
     needs **5.2.5**, mutual and nested inductives, which is scheduled last
     in phase 5. It also needs well-founded recursion support. Yet 5.5.1
     lists only 5.4.1 and 2.5.5.
   - The older `LeanForthStackModel.Code` (`done | op … next |
     branch …`, copied into `program-ir.lean:66-69`) is *not* nested.
   - Either record the dependency, or make IR v1's Lean model checkable
     sooner: give it a non-nested code type and structural recursion on
     fuel (as `runFrom` does).
   - To confirm, export the closure of `ProgramVC.LfClamp0.contract` and
     count its record kinds. I have not done this.
3. **How the Lean is written.**
   - Semantic equations are kept as an opt-in annotation layer
     (`Grind/Rules.lean`), and the original lessons never import it.
   - Rules compute the intermediate state instead of asking for existential
     witnesses (README:321-324: "This avoids asking proof search to discover
     that stack as an existential witness").
   - Callee contracts are rewrite rules over an arbitrary continuation
     (`Grind/Examples.lean:22`, `square_step`), so larger proofs never
     re-open a callee.
   - LeanForth already uses the last pattern (`run_max`, `run_min`,
     `run_call_word`). For SHA-256 it should become the standard shape for
     the eight helper words.
4. **`grind` is not free for LeanForth.**
   - For proofs that LeanForth's checker must check itself (5.5.1, SHA-5),
     `grind` and `omega` proof terms bring in large parts of Lean core and
     its axioms.
   - Measure the closure and `#print axioms` before choosing proof style.
     Prefer `simp only` and explicit lemmas where the closure matters.
   - This is reasoned, not measured.
5. **Authoring syntax is the mirror image.**
   - MiniForth embeds Forth in Lean with Lean's extensible grammar.
     LeanForth (ADR 0017) embeds Lean terms in Forth as words. LeanForth's
     rules forbid MiniForth's approach as the canonical form.
   - The useful part is the test discipline of `PrettyPrinterTests.lean`:
     round trips at narrow widths, a local that shadows a word, names that
     need escaping, empty and non-ASCII names, and a goal display test
     (`#guard_msgs` on `trace_state`).
   - Those cases transfer to plan 8.1.2, the Forth-mode printer round trip.

---

## 5. Recommendations, ranked

| # | Recommendation | Plan task affected | Why (MiniForth evidence) |
| --- | --- | --- | --- |
| 1 | In ADR 0019, bind each call to the definition Forth resolved when it was compiled (an identity, not a name), or keep refusing redefinition; model `RECURSE` explicitly. Do not use a late-bound global dictionary. | ADR 0019; IR next version; G1 (`RECURSE`); G3 | MiniForth's README says its global `Env` does not model Forth's successive redefinitions; LeanForth's `lookup` is the same first-match search |
| 2 | In ADR 0019: correctness mode is untrusted notation that emits **structured** IR (nested blocks from immediate control words); add a Lean `WellFormed` check on the emitted IR and a `link_no_unknown`-style theorem; test the round trip IR → Forth → correctness mode → identical IR, with adversarial names. | ADR 0019 prototype; [parser] gate evidence | `Link.lean`, `LinkCorrectness.lean`, `PrettyPrinterTests.lean`; the one-line branch WP rule |
| 3 | Add a fuel-free relational semantics `Eval` for the IR beside `run`, and prove `run` sound and complete for it (`eval_iff_run`) and fuel monotone. This is additive: `run` stays the executable. It makes divergence and partial correctness expressible and lets contracts drop fuel bounds. | 4.4.1 (IR v1); SHA-3/SHA-4 (64 rounds, messages of any length); G1 | `Deep.lean:280-337`, `Divergence.lean` |
| 4 | Decide now how IR v1's Lean model will be checked by LeanForth: record that 5.5.1 needs 5.2.5 and well-founded recursion, or give IR v1 a non-nested code type with structural recursion on fuel. | 4.4.1; 5.5.1; SHA-5 | Comparing both models showed LeanForth's `Instr`/`run` encoding; `runFrom` is structural |
| 5 | Build verification-condition generation v1 as a Lean library of proved WP rules (`wp_append`; one rule per primitive that computes the next state; `wp_if`; `wp_call` with callee contracts; a while rule with invariant and variant) plus a `forth_wp`-style tactic. The Python generator then only translates contracts. | 4.4.2; SHA-2, SHA-3 | `WeakestPrecondition.lean`, `Grind/Tactics.lean`, `Grind/VerificationConditions.lean` |
| 6 | For SHA-256 proofs, state every helper word's contract as a rewrite over an arbitrary continuation, register it, and never re-open a callee. | SHA-2, SHA-3 | `Grind/Examples.lean:22-41`; already partly done (`run_max`) |
| 7 | Ask the receipt-schema review whether VERIFY should name the correctness kind (total / safe-partial / partial). | 2.5.1 (review open); P1 | `WP`, `SafeWLP`, `WLP` |
| 8 | Once mutual and nested inductives are supported, check MiniForth's Std-only modules locally as a small real-Lean corpus; do not commit them or their exports unless it is licensed. | 5.2.5; 6.4.1 | Same Lean pin, no dependencies |
| 9 | Compare step traces, not only final results, between `ir-run.fs` and Lean. | 2.5.4 follow-up; diagnostics | `Main.lean` `showTrace` |

### Not to adopt, and why

- **Unbounded `Int` cells.** SHA-256 needs 32-bit wrapping, Forth-2012 needs
  cells, and MiniForth itself lists bounded words as an exercise.
- **A global, order-independent, late-bound dictionary with forward
  references.** That is not Forth's semantics; see recommendation 1.
- **Lean syntax-extension quotations (`[forth| …]`) as the canonical program
  or theorem form.**
  - `AGENTS.md` requires ordinary Forth words and no competing grammar.
  - ADR 0017 rejected parsing strings.
  - MiniForth's names are case-sensitive, unlike Gforth's.
  - A Lean-side *display* delaborator for IR in goals is harmless, but keep
    it out of any module LeanForth must check, because it imports `Lean`.
- **A mandatory ELSE.** Forth has `IF … THEN`.
- **`grind` as the default proof method for receipts LeanForth will check
  itself**, until the closure is measured.
- **MiniForth as a test oracle for Gforth or the IR.** The fragment is too
  small, the number model differs, and it has no licence.
- **Copying or vendoring any MiniForth file.** See §6.

---

## 6. Licence and attribution

- MiniForth has **no licence**. There is no LICENSE file, the README states
  no terms, and the GitHub API reports `"license": null` (2026-11-03).
- By default that grants no right to copy, modify or redistribute its code.
  GitHub's terms allow viewing and forking on GitHub only.
- Ideas such as big-step and small-step semantics, weakest preconditions and
  fuel adequacy are standard and free to use. LeanForth should **write its
  own code**.
- If any of the above is adopted, cite MiniForth as prior art in the
  relevant ADR and in `docs/project/DECISIONS.md` (URL and commit `e8756e2`).
- Do not commit MiniForth files, or Lean exports built from them, to the
  repository.
- To reuse code or a corpus, ask the author to add a licence. Lean itself is
  Apache-2.0.
- (Not legal advice.)
- The local clone in `.claude/work/MF/download/` is git-ignored
  (`.gitignore:7`, `/.claude/work/`). It should stay out of the repository.
