# ADR 0015: inductive types, constructors and recursors as Lean's kernel checks them

Status: task **5.2.1a implemented and approved** [kernel][import] by the owner on 2026-11-04, on condition that its three cautious differences from Lean are closed so the default is 100% Lean ([decisions](../project/OWNER_DECISIONS.md#data-types-first-step-approved-with-a-condition-2026-11-04)). **Condition met** (owner, 2026-11-04, after review rvI21 rounds 4–6; [decisions](../project/OWNER_DECISIONS.md#data-types-first-step-condition-met-2026-11-04-late)): the remaining differences are temporary, each closed by a named later task. **Accepted** as a design, 2026-11-03 (owner; questions Q1–Q5 answered
in §15 and in [OWNER_DECISIONS](../project/OWNER_DECISIONS.md#data-types-axioms-and-imports-2026-11-03-late-night));
each implementation task of §12 still passes its own gate. Proposed 2026-11-03 (plan tasks 5.1.1–5.1.5, phase 5, "Data
types and the first real Lean code"). A [kernel] and [import] design, with
an [axiom] part (§8) and one [bypass]-class risk (§7, L5). **Task 5.2.1a
is implemented** (2026-11-04, experimental, its [kernel][import] gate
open: [Implementation](#implementation-plan-task-521a)): a block of one
non-recursive inductive type is checked, its recursor generated and
compared, and the block published. **Task 5.2.1b is implemented**
(2026-11-04, experimental, its [kernel] gate open:
[Implementation](#implementation-plan-task-521b)): recursive blocks of
one type, with positivity and induction hypotheses. **Task 5.2.5a, mutual
blocks, is implemented** (2026-11-04, experimental, gate open:
[Implementation](#implementation-plan-task-525a)); nested blocks (task
5.2.5b) have a [written plan](#plan-task-525b-nested-blocks) and are
still *unsupported*, as is every quotient, literal and projection (ADR
0011 rules U1, U2). It extends ADR 0011 (rejection rules) and ADR 0012
(the checked environment) and supersedes neither. Each implementation task
of §12 passes its own review gate (`AGENTS.md`): Lean's published rules,
agreeing pinned-Lean differential tests reaching every outcome, an
independent AI review, and the owner's approval of a plain summary.

## Summary in plain words

Almost every real Lean statement mentions a **data type**: the natural
numbers, equality, "and", lists. Lean calls them *inductive types*. Each is
given by its **constructors**, the ways of building an element (a natural
number is either zero or the successor of a natural number). From that list
Lean's kernel derives the type's **recursor**: the principle of induction
and of definition by recursion, with **computation rules** saying what a
recursive definition gives on each constructor. Lean's kernel never takes a
recursor from anyone: it builds it itself, after checking that the type is
safe to have (for example, that `Bad` built from functions `Bad → Nat`
cannot be declared, since that would prove a contradiction).

LeanForth will do exactly what Lean does. When it reads an exported data
type, it runs Lean's checks in Lean's order, **builds the recursor itself**,
and compares it with the one in the file; the file's recursor is never
trusted. A difference means the file is not what Lean's kernel produced, and
LeanForth rejects it, as Lean's own export checker does (evidence:
`replay.*` rows). Then come the computations a data type brings — a
recursive definition applied to a constructor (`iota`), the special rule for
equality proofs (`K`), records and their fields (structures, projections,
"eta"), quotients, and Lean's built-in arithmetic on number literals — each
ported from Lean's source with its exact limits.

The evidence is 100 cases on which the pinned Lean 4.35.0 kernel was asked
for its verdict (`tests/reference/inductive-expected.tsv`, run by
`make check`): 53 accepted, 47 refused, each with the outcome LeanForth must
give and the plan task that delivers it, plus three small real exports that
show what LeanForth will read. Two findings need the owner (§15): Lean's
kernel computes on numbers **by the names** `Nat.add` and so on, so an
export that defines its own `Nat.add` gets `5 = 2` accepted by Lean
(Q1); and Lean's export checker ignores some exported fields that LeanForth
could check (Q2). Four places where Lean's procedure rejects or cannot
decide something true are recorded in `docs/project/BEYOND_LEAN.md`
(BL-5 to BL-8); LeanForth copies Lean there.

The first real target (plan 5.4.1) is `n + 0 = n` and `0 + n = n`. Their
exported dependency closure has **44 constants** in 29 export records: 7
data types with 8 constructors and 7 recursors, 19 definitions and 3
theorems, using projections, one number literal and no axioms (§11).

## 1. Three examples

Mathematics, LeanForth words (ADR 0017 §15 sketch syntax, not implemented)
and Lean, for the three data types the first target needs. Lean's kernel
form of each is in `tests/reference/inductive/blocks.ndjson` (the
`LeanForthBlocks` names) and, for Lean's own `Nat` and `Eq`, in
`nat-add-zero.ndjson`.

**Natural numbers.**

- Mathematics: ℕ is generated by $0$ and $n \mapsto n+1$. Induction and
  recursion: for every family $C : ℕ \to \mathrm{Sort}\,u$, from $z : C\,0$
  and $s : \forall n, C\,n \to C\,(n+1)$ we get $\mathrm{rec}\,z\,s :
  \forall n, C\,n$, with $\mathrm{rec}\,z\,s\,0 = z$ and
  $\mathrm{rec}\,z\,s\,(n+1) = s\,n\,(\mathrm{rec}\,z\,s\,n)$.
- LeanForth words:

  ```text
  inductive MyNat
    0 Type
  where
    MyNat  constructor: zero
    MyNat explicit: n  MyNat  constructor: succ
  end MyNat
  ```

- Lean: `inductive Nat where | zero : Nat | succ (n : Nat) : Nat`. The
  kernel generates (pinned Lean, `pp.explicit`):

  ```text
  Nat.rec.{u} : {motive : Nat → Sort u} → motive Nat.zero →
    ((n : Nat) → motive n → motive n.succ) → (t : Nat) → motive t
  rule Nat.zero, 0 fields: fun motive zero succ => zero
  rule Nat.succ, 1 field:  fun motive zero succ n => succ n (@Nat.rec motive zero succ n)
  ```

**Equality.**

- Mathematics: for a fixed $a : \alpha$, the family $a = \cdot$ is
  generated by one proof, $\mathrm{refl} : a = a$. Its recursor is
  substitution: from $c : C\,a\,\mathrm{refl}$ we get $C\,b\,h$ for every
  $h : a = b$, and $\mathrm{rec}\,c\,\mathrm{refl} = c$.
- LeanForth words:

  ```text
  inductive MyEq
    universe u
    u Sort implicit: α
    α explicit: a
    α Prop ->
  where
    MyEq u ^ α $ a $ a $  constructor: refl
  end MyEq
  ```

- Lean: `inductive Eq : α → α → Prop | refl (a : α) : Eq a a`, with two
  parameters (`α`, `a`) and one index (the right side). Generated:

  ```text
  Eq.rec.{u, u_1} : {α : Sort u_1} → {a : α} → {motive : (a_1 : α) → a = a_1 → Sort u} →
    motive a (Eq.refl a) → {a_1 : α} → (t : a = a_1) → motive a_1 t
  k = true; rule Eq.refl, 0 fields: fun {α} a motive refl => refl
  ```

**Conjunction.**

- Mathematics: a proof of $a \wedge b$ is a pair of proofs; from $f :
  \forall (x : a)(y : b), C\,(x, y)$ we get $C\,t$ for every $t : a \wedge
  b$, with $\mathrm{rec}\,f\,(x, y) = f\,x\,y$. Its projections give $a$
  and $b$.
- LeanForth words:

  ```text
  structure MyAnd
    Prop explicit: a
    Prop explicit: b
    Prop
  where
    a explicit: left
    b explicit: right
    MyAnd a $ b $  constructor: intro
  end MyAnd
  ```

- Lean: `structure And (a b : Prop) : Prop where intro :: left : a; right :
  b`. Generated:

  ```text
  And.rec.{u} : {a b : Prop} → {motive : a ∧ b → Sort u} →
    ((left : a) → (right : b) → motive ⟨left, right⟩) → (t : a ∧ b) → motive t
  k = false; rule And.intro, 2 fields: fun a b motive intro left right => intro left right
  ```

`And.rec` has its own universe `u`: proofs of `a ∧ b` may be used to build
data ("large elimination"), because its constructor's fields are proofs.
`Or.rec` has none (`∀ {a b : Prop} {motive : a ∨ b → Prop}, …`): with two
constructors, a proof of `a ∨ b` must not reveal which one was used, so it
eliminates only into `Prop` (§3, E1).

## 2. The referee

- **Lean 4.35.0**, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` (the
  pinned toolchain's `lean --githash`). The kernel files were fetched
  read-only on 2026-11-03 from
  `raw.githubusercontent.com/leanprover/lean4/<commit>/src/kernel/` into
  the agents' work folder (`.claude/work/lean-src/`); hashes under
  *Reproduction*. `type_checker.cpp`, `type_checker.h`, `environment.cpp`,
  `declaration.h`, `declaration.cpp`, `inductive.h` and `quot.h` are byte
  for byte the files ADR 0011 read, so its line numbers still hold. The
  Lean-side files are the toolchain's own sources
  (`.tools/elan/toolchains/leanprover--lean4---v4.35.0/src/lean/`).
- **A declaration's verdict** is that of `Kernel.Environment.addDeclCore`
  (ADR 0011, *The referee*). An inductive declaration
  (`Declaration.inductDecl lparams nparams types isUnsafe`, `Lean/Declaration.lean`
  178–197) holds only the types and their constructors; `environment::add`
  sends it to `add_inductive` (`environment.cpp` 279), which adds the types,
  constructors and recursors it generates. A quotient declaration goes to
  `add_quot` (278).
- **An exported block's verdict** is that of Lean's own checker for exports,
  `Kernel.Environment.replay` (`Lean/Replay.lean`, used by `leanchecker`):
  it rebuilds the declaration from the exported types (`levelParams`,
  `numParams`, the `all` list) and constructor types (102–120), always with
  `isUnsafe := false` (120), sends it to `addDeclCore`, and afterwards
  requires every exported constructor and recursor to be `==` to the one the
  kernel generated (`checkPostponedConstructors` 148–153,
  `checkPostponedRecursors` 159–164). `==` on expressions is alpha
  equivalence that ignores binder names and binder annotations
  (`Lean/Expr.lean` 804–811); on `RecursorVal` it compares every field,
  universe parameter names included (`deriving BEq`, `Declaration.lean`
  338, 355, 382). Replay skips unsafe and partial constants (180–183) and never compares
  the exported `InductiveVal` fields other than those it uses.
- **What LeanForth reads.** lean4export 3.1.0 writes a whole block on one
  line, `{"inductive":{"types":[…],"ctors":[…],"recs":[…]}}`, types in the
  order of their `all` list, constructors in the order of each type's
  `ctors`, recursors in name order (a `NameSet`), after every constant they
  use (`LeanExport/Basic.lean` 323–412); for a nested block the recursors
  include the auxiliary `T.rec_1`, … (Tree in `blocks.ndjson`). The four
  quotient constants come as four `quot` records after `Eq` (308–322). The
  reader hands each element over as its own record
  ([NDJSON_READER.md](../development/NDJSON_READER.md#record-kinds-and-their-fields))
  and the stage keeps them as declaration records (`src/import/stage-records.fs`:
  a block record, then its types, constructors and recursors with their
  numbers, flags and rules).

## 3. Lean's procedure: `add_inductive`, in order

`environment::add_inductive` (`inductive.cpp` 1235–1350) runs these steps;
the first failure ends the check with its exception. Rule IDs are used by
the evidence table. "Typed" means checked with Lean's type checker in the
inductive's universe parameters; its own failures (`typeExpected`,
`appTypeMismatch`, …) are ADR 0011's.

| Step | Rule | What Lean checks | Source (`inductive.cpp`) | Lean's exception |
| --- | --- | --- | --- | --- |
| 1 | V1 | No free or meta variables in any type or constructor type | 1237–1247 (`check_no_metavar_no_fvar`) | `declHasFVars`/`declHasMVars` (LeanForth: *invalid*, the format cannot express them) |
| 1 | T0 | No constant or projection whose name starts with `_nested` | 1222–1233, 1241, 1244 | `other`: "uses the reserved prefix" |
| 2 | C1 | Every occurrence of a type being declared in a constructor type is applied to the block's universe parameters and to exactly its parameters, as the bound variables of the first `nparams` binders, syntactically; over-applied occurrences are searched inside | 134–164 (`check_uniform_ind_occs`) | `other`: "invalid occurrence of datatype … must be applied to the parameters …" |
| 3 | T1 | The block is not empty; the first type has at least `nparams` Π binders (raw, before reduction) | 1150–1155, 1138–1146 | `other`: "invalid empty (mutual) inductive …", "incorrect number of parameters" |
| 3 | N1, N2 | Nested occurrences `I Ds is` of an earlier inductive `I` whose parameters `Ds` mention a type being declared are replaced by auxiliary types `_nested.I_k` copied from `I`'s block (all its types), until none is left; `Ds` must not mention a constructor's own variables | 985–1180 (`replace_if_nested` 1066–1131, `is_nested_inductive_app` 1023–1055) | `other`: "nested inductive datatypes parameters cannot contain local variables" |
| 4 | T5 | Universe parameters distinct | 869 (`check_duplicated_univ_params`) | `other`: "duplicate universe level parameter" |
| 5 | T5, T2, T3, T4 | For each type: its name and `name.rec` unused; type well typed; the first `nparams` binders (after `whnf`) are the parameters, and in a mutual block definitionally equal to the first type's; exactly `nparams` of them; the rest are indices; the result is a `Sort`; all types of a mutual block have equivalent result levels | 254–305 (`check_inductive_types`) | `alreadyDeclared`; `typeExpected`; `other`: "parameters of all inductive datatypes must match", "number of parameters mismatch", "mutually inductive types must live in the same universe" |
| 6 | — | `isRec` (a constructor field's type mentions a type of the block, syntactically, without reduction) and `isReflexive` (a field is a function returning one); types added | 308–375 | — |
| 7 | C4, T5 | For each constructor: no duplicate name in its type; name unused; type well typed | 456–469 | `other`: "duplicate constructor name"; `alreadyDeclared`; typing |
| 7 | C2 | Its first `nparams` binders are definitionally the parameters' types | 472–476 | `other`: "arg #i of … does not match inductive datatypes parameters" |
| 7 | U1 | Each field's type lives in a universe `≤` the result level (Lean's `is_geq`, after `normalize`), unless the type is a proposition (result level `normalizes_to_zero`) | 478–485 | `other`: "universe level of type_of(arg #i) … is too big" |
| 7 | P1, P2 | Unless unsafe, each field's type after `whnf` has occurrences only strictly positively: not in a binder domain, and at the end as a valid application `I As is` (parameters exactly the block's, indices free of the block's types) | 436–452 (`check_positivity`), 381–409 (`is_valid_ind_app`) | `other`: "non positive occurrence", "non valid occurrence" |
| 7 | C3 | The constructor's result is a valid application of its own type | 493–494 | `other`: "invalid return type for …" |
| 8 | — | Constructors added with `cidx`, `numParams`, `numFields` (binders after the parameters) | 499–519 | — |
| 9 | E0–E4 | Elimination level: a motive universe `u` (or `u_1`, `u_2`, … if taken), or `Prop` only | 522–592 | — |
| 10 | K1 | `k` (K-like reduction) for a single, non-mutual inductive predicate with one constructor and no fields | 594–616 | — |
| 11 | G1, G2 | Recursors built: motives, minor premises, indices, major premise; computation rules | 632–819 | `alreadyDeclared` for `T.rec` |
| 12 | G4 | Defensive: each recursor's type is well typed, and each rule preserves types | 829–866 | `other`: "generated recursor computation rule … is not type-preserving" |
| 13 | N3 | Nested: auxiliary types restored to the nested occurrences in every constructor and recursor (auxiliary recursors renamed `T.rec_1`, …), the replaced `I Ds` typed, and everything rewritten typed again | 1253–1349 (`restore_nested` 927–975, `mk_aux_rec_name_map` 1191–1217) | `other`: "failed to restore nested inductive types" (defensive) |

**Order matters for the reason.** Lean checks a constructor field's
universe (U1) before its positivity (row `pos.universe-checked-first`), the
uniform-parameter rule C1 before the parameter count (row
`replay.parameters-changed`), and a constructor's parameters (C2) before its
result type (row `params.constructor-mismatch`). LeanForth checks in the
same order so that a rejected block names Lean's reason.

**Elimination level** (`elim_only_at_universe_zero`, 522–577). The
recursor gets its own motive universe, and so eliminates into every
`Sort u`, except where marked "only `Prop`":

- E0: the result level is never zero (`is_not_zero`): every universe;
- E1: otherwise, a mutual block, or two or more constructors: only `Prop`;
- E2: no constructors (`False`): every universe;
- E3: one constructor, and every field that is not a proof appears among
  the arguments of the constructor's result type (Lean's comment: then
  nothing secret is revealed): every universe;
- E4: one constructor otherwise: only `Prop`.

Rows: `ind.or` and `ind.prop-two-empty-ctors` (E1), `ind.empty-prop` (E2),
`ind.and`, `ind.true`, `ind.eq`, `ind.exists-prop-witness`,
`ind.field-in-index` (E3), `ind.exists`, `universe.predicate-any-field`
(E4), `mutual.single-ctor-props` (E1 for a mutual block where each type
alone would be E3: BL-6).

**The recursor** of type `I` with parameters `As`, motives `Cs` (one per
type of the block, `motive` or `motive_1`, …), minor premises (one per
constructor, named by the constructor's last name part), indices `is` and
major premise `t : I As is` (`mk_rec_infos` 632–717,
`declare_recursors` 795–819):

```text
I.rec.{u?, lparams} : (As) → (Cs) → (minors) → (is) → (t : I As is) → C_I is t
minor for c : (fields b) → (ih for each recursive field u_i) → C_J js (c As b)
ih for u_i : (xs) → C_K ks (u_i xs)          -- u_i : (xs) → K As ks
rule for c : fun As Cs minors b => minor_c b (fun xs => K.rec As Cs minors ks (u_i xs))…
```

Binder information is made implicit by `infer_implicit` (810). A field is
recursive when its type, after `whnf` through its Π binders, is a valid
application of a type of the block (`is_rec_argument` 426–433). The
recursor's numbers are `numParams`, `numIndices` (of its type),
`numMotives` = types in the block, `numMinors` = constructors in the block;
its major premise is argument `numParams + numMotives + numMinors +
numIndices` (`declaration.h` 382).

**Mutual and nested blocks** share the motives and minors of the whole
block: a mutual block's recursors take every type's motive and every
constructor's minor (rows `mutual.even-odd`: motives 2, minors 3). A nested
block `Tree | node : List Tree → Tree` is checked as the mutual block
`Tree`, `_nested.List_1` (a copy of `List` at `Tree`) and restored, so
`Tree.rec` has two motives and three minors, and the auxiliary recursor
`Tree.rec_1` eliminates `List Tree` (row `nested.tree`, `blocks.ndjson`).
The boundary for LeanForth: nested and mutual blocks are the last task of
phase 5 (5.2.5); until then such a block, and everything that uses it, is
*unsupported* (ADR 0011 K5 propagation).

## 4. How LeanForth checks an exported block

Each block is **one check** that ends in one outcome for all its
declarations; the publisher (ADR 0012 E4) makes all its slots final
together, under one lock, or none of them.

1. **B0 Shape** (invalid on failure; fail-closed, before any typing). The
   block's types are exactly the `all` list of its first type, in that
   order, each with the same `all`, `levelParams` and `numParams`; its
   constructors are exactly the types' `ctors` lists, each naming its type
   (`induct`); every recursor names this block in its `all` list; names
   distinct. Anything else cannot have come from lean4export and is
   *invalid*. Unsafe elements are *unsupported* (replay skips them). A
   recursor whose name Lean does not generate is left to B3, a missing one
   to B4.
2. **B1 Rebuild** the declaration as replay does: `inductDecl lparams
   nparams types false`, from the exported types and constructor types
   (pointers into the input; nothing copied).
3. **B2 Check and generate** with Lean's procedure (§3), in its order, in
   the check's context: rejected with Lean's exception, *unknown* where a
   `whnf` or comparison needs a rule LeanForth does not have yet (as ADR
   0011 K1), or the generated types, constructors and recursors in scratch.
4. **B3 Compare** each exported constructor and recursor with the generated
   one by Lean's `==`: every field equal, universe parameter names equal,
   types and rule right-hand sides alpha-equivalent, binder names and
   annotations ignored. A difference, or a recursor Lean does not
   generate, is *rejected* (Lean's replay: "Invalid constructor", "Invalid
   recursor", "No such recursor"; rows
   `replay.rule-right-sides-swapped`, `recursor-k-set`,
   `recursor-motives-changed`, `constructor-fields-changed`,
   `constructor-type-changed`).
5. **B4 Exported fields replay ignores**: `numIndices`, `isRec`,
   `isReflexive`, `numNested` of a type, and a recursor missing from the
   block. Lean's replay accepts such a file and uses the kernel's values
   (rows `replay.isRec-changed`, `indices-changed`, `recursor-left-out`).
   Proposed (owner question Q2): LeanForth accepts as Lean does, never uses
   the exported value, and records a diagnostic.
6. **B5 Publish.** The environment records point at the **input's** terms,
   which B3 proved equal to the generated ones (ADR 0012 E1: the checked
   claim is the stored claim). The numbers and flags the checker uses
   (indices, `isRec`, `numNested`, `k`, rule field counts, the elimination
   universe) are LeanForth's generated values, which B3 compared where Lean
   compares and which B4 never takes from the file. The axiom set of the
   block is the union of what its types and constructor types use.

The generated recursor is never trusted in place of the comparison, and the
exported recursor is never used without it (rejected alternatives).

## 5. Reductions an inductive type brings

They enter Lean's `whnf_core` and `is_def_eq_core`, which phase 4 ports
(plan 4.1.1, ADR 0014 to come); this record adds the routes that need an
inductive declaration. LeanForth must take them **in Lean's order**, since
Lean's comparison is deterministic but incomplete and LeanForth must fail
where Lean fails (owner rule; BL-7, BL-8).

| Rule | What | Lean source | Rows |
| --- | --- | --- | --- |
| R1 iota | A recursor applied to at least its major premise: the major is put in `whnf`; a `Nat` literal becomes `Nat.zero` or `Nat.succ (n-1)`, a `String` literal its `String.ofList` form; if it is a constructor application with at least the rule's fields, the rule's right side is instantiated at the recursor's universe arguments and applied to the parameters, motives and minors, then the constructor's fields, then any further arguments. Universe arity must match. | `inductive_reduce_rec` (`inductive.h` 77–121) from `whnf_core` 511–541 via `reduce_recursor` 393–407 | `iota.nat-literal-major`, `-wrong`, `iota.stuck-on-variable` |
| R2 K-like | For a recursor with `k`, before `whnf`: the major premise is replaced by the nullary constructor at the parameters of its type when that constructor's type is definitionally the major's type (`h : a = a` acts as `Eq.refl a`) | `to_cnstr_when_K` (`inductive.h` 30–50), `mk_nullary_cnstr` (`inductive.cpp` 88–97) | `k.eq-variable-proof`, `k.eq-different-ends` |
| R3 structure eta in iota | A major premise that is not a constructor application, of a non-recursive structure (one constructor, no indices, not recursive) **not in `Prop`**, is expanded to `mk p.1 … p.n` | `to_cnstr_when_structure` (`inductive.h` 62–74), `expand_eta_struct` (`inductive.cpp` 99–112) | `iota.structure-eta`, `iota.prop-structure-stuck` (BL-8) |
| R4 structure eta | `t =?= mk s₁ … sₙ` for a non-recursive structure holds when the types are equal and `t.i =?= sᵢ` for every field; tried in both directions after function eta | `try_eta_struct_core` 856–872, `type_checker.h` 97–99, called at 1197 | `eta.structure`, `unit.pair-of-units` (BL-7) |
| R5 unit-like | Two terms whose type (after `whnf`) is a non-recursive structure whose constructor has no fields are equal when their types are; the last route of `is_def_eq_core` | `is_def_eq_unit_like` 1119–1130, called at 1203 | `unit.punit`, `unit.bool-not-unit-like` |
| J1 projections | `.proj S i e`: typed by `infer_proj` (`whnf` of `e`'s type is `S As is` with `S` having exactly one constructor; the field's type is read off the constructor's type, earlier fields replaced by projections); reduced when `whnf` of `e` is a constructor of `S` (a string literal first expanded) | `infer_proj` 247–292, `reduce_proj` 444–454, `reduce_proj_core` 420–441, `whnf_core` 504–510; in comparison `lazy_delta_proj_reduction` 1084–1101 at 1177–1182 | `proj.data`, `proj.proof-of-proof` |
| J2 invalid projections | `invalidProj` when the index exceeds 32 bits or the fields, the type is not `S` or not a one-constructor inductive, the argument count is wrong, or a data field is projected out of a proof | `to_proj_idx` 237–245, `infer_proj` 250–290 | `proj.data-from-proof`, `proj.wrong-structure`, `proj.index-out-of-range` |

`whnf_core` reduces a recursor or quotient application only when its head
is unchanged by `whnf_core` (525–533), and with `cheap_rec`/`cheap_proj`
the major premise and the projected term are reduced without unfolding
definitions (466–468); `is_def_eq_core` uses `cheap_proj` first
(1155–1156). These flags change only how far a step goes before the next
route is tried, so LeanForth keeps them.

## 6. Quotients (`quot.cpp`, `quot.h`)

- **Q1 Initialisation.** `Declaration.quotDecl` adds the four constants
  only if not yet present, after checking that `Eq` exists with exactly one
  universe parameter, one constructor, the type `{α : Sort u} → α → α →
  Prop` and the constructor type `{α : Sort u} → (a : α) → Eq a a`
  (`check_eq_type`, `quot.cpp` 19–45; `add_quot` 47–104). The kernel
  **builds the four types itself**; the exported `quot` records are never
  checked against them by replay (`Replay.lean` 129–133). Lean's types:

  ```text
  Quot.{u}      : {α : Sort u} → (α → α → Prop) → Sort u
  Quot.mk.{u}   : {α : Sort u} → (r : α → α → Prop) → α → Quot r
  Quot.lift.{u,v} : {α : Sort u} → {r : α → α → Prop} → {β : Sort v} → (f : α → β) →
                    (∀ (a b : α), r a b → f a = f b) → Quot r → β
  Quot.ind.{u}  : ∀ {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop},
                    (∀ (a : α), β (Quot.mk r a)) → ∀ (q : Quot r), β q
  ```

  LeanForth builds the same four and never uses the exported records;
  since Lean's replay ignores them, a difference is treated as a B4 field
  (owner question Q2: accepted with a diagnostic, as Lean). Rows
  `quotinit.with-eq`, `quotinit.without-eq` (`unknownConstant`),
  `quotinit.eq-wrong-shape`.
- **Q2 Reduction.** `Quot.lift f h q` (argument 5 the quotient, 3 the
  function) and `Quot.ind h q` (argument 4, 3): when `whnf q` is
  `Quot.mk r a` with exactly three arguments, the result is `f a` applied
  to any further arguments (`quot_reduce_rec`, `quot.h` 39–70), tried
  before inductive recursors and only once quotients are initialised
  (`reduce_recursor` 394–398). Rows `quot.lift-on-mk`, `-wrong`,
  `quot.lift-stuck-on-variable`.
- **Q3 `Quot.sound`** is not a kernel constant: it is an ordinary axiom,
  declared in `Init/Prelude.lean` (543) after `init_quot` (450) has made
  the four quotient constants:
  `Quot.sound.{u} : ∀ {α : Sort u} {r : α → α → Prop} {a b : α}, r a b → Quot.mk r a = Quot.mk r b`,
  and the one allowlisted axiom among the quotient constants (owner
  decision 4). Its exact exported record, with those of `propext` and
  `Classical.choice`, is in `tests/reference/inductive/axioms.ndjson`
  (SHA-256 under *Reproduction*); the allowlist v1 (plan 5.3.1) matches the
  axiom's type against that record's term exactly. Measured: all of
  Mathlib's export (2026-11-02) contains four axioms — `propext` (line
  21,615), `Quot.sound` (33,151), `Classical.choice` (38,324) and
  `sorryAx` (105,523,904); the last is not allowlisted (Q5).

## 7. Nat and String literals

- **L1 Computed operations** (`reduce_nat`, `type_checker.cpp` 672–703,
  called from `whnf` 732 and, when neither side has free variables, from
  `lazy_delta_reduction` 1060–1066). After `whnf`, both arguments must be
  literals or the constant `Nat.zero` (`is_nat_lit_ext` 607). Exactly
  these, matched by name (1287–1302): `Nat.succ`, `Nat.add`, `Nat.sub`,
  `Nat.mul`, `Nat.pow`, `Nat.gcd`, `Nat.mod`, `Nat.div`, `Nat.beq`,
  `Nat.ble`, `Nat.land`, `Nat.lor`, `Nat.xor`, `Nat.shiftLeft`,
  `Nat.shiftRight` (`Nat.beq`, `Nat.ble` give `Bool.true`/`Bool.false`).
  `src/lib/bignum.fs` implements each with Lean's runtime semantics (its
  header lists them with sources), and its size limit (2³⁰ bits, Lean's
  default `LEAN_NAT_MAX_SIZE` of 128 MiB, `type_checker.cpp` 36,
  296–313): the kernel integration throws Lean's exception where Lean does
  (literal size in `infer_lit` 315–321; results of `succ`, `add`, `sub`,
  `mul`; `pow` and `shiftLeft` arguments). `Nat.log2` is **not** computed
  (BL-2). Rows `lit.*`.
- **L2 Literal to constructors**, in iota only (`inductive.h` 94–97): a
  major premise `n` becomes `Nat.zero` or `Nat.succ (n-1)`
  (`nat_lit_to_constructor`, `inductive.cpp` 1359–1366); a string literal
  becomes `String.ofList` of `List.cons (Char.ofNat c) …` over its UTF-8
  code points, then `whnf` (1368–1380). Nowhere else does a literal unfold:
  `whnf` of a literal is the literal (709–711).
- **L3 Offsets**: before unfolding, `is_def_eq_offset` (1043–1052) equates
  `0` with `Nat.zero` and compares `n+1` (a literal or `Nat.succ x`)
  argument by argument; two literals compare by value (`quick_is_def_eq`
  821–822). Rows `lit.literal-against-constructors`,
  `lit.offset-with-variable`.
- **L4 String literals** equal `String.ofList …` by expansion
  (`try_string_lit_expansion` 1104–1117); a projection of a string literal
  expands it first (421–422). The literal's type is the constant `String`,
  a natural literal's the constant `Nat` (`infer_lit`), whether or not they
  are declared. Rows `lit.string-expansion`, `-wrong`.
- **L5 Primitive names** (owner question Q1). Lean's kernel recognises
  `Nat`, `Nat.zero`, `Nat.succ`, the fourteen operations, `Bool.true`
  (also used for reflection proofs, 1142–1146), `String.ofList`,
  `List.cons`/`List.nil` at `Char` and `Char.ofNat` **by name only**; it
  never checks what they are defined as. In an environment where
  `Nat.add a b := a`, Lean accepts `Nat.add 2 3 = 5` (computed on
  literals) and `∀ b, Nat.add 2 b = 2` (unfolded), and therefore the
  theorem `5 = 2` (rows `primitive.forged-add-computes`, `-unfolds`,
  `primitive.five-is-two`, all accepted by Lean 4.35.0). Lean's own
  `Init` defines them correctly, so no export of a normal Lean file is
  affected; a file that starts with `prelude` declares them itself (as
  `Init/Prelude.lean` does), and an NDJSON file is untrusted input. (The
  rows build the declarations directly for the kernel; a `prelude` source
  file producing them was not tried.) Proposed: LeanForth uses L1–L4 only when
  each of these names is declared exactly as in Lean 4.35.0's `Init` (their
  exported records and closures equal pinned ones), and otherwise answers
  *unsupported* for every declaration whose check meets one of them.

## 8. The axiom allowlist, as far as this record needs it

Quotients bring `Quot.sound`; the first target needs no axiom (§11). The
allowlist (plan 5.3.1, [axiom] gate) is a versioned file holding the exact
exported statements of `propext`, `Classical.choice` and `Quot.sound`
(`axioms.ndjson`); an axiom whose name is listed but whose type differs,
and an unlisted one, are *unsupported* with everything that uses them
(ADR 0011 K5; Q5); `Lean.ofReduceBool` and `Lean.trustCompiler` never.

## 9. Evidence

`tests/reference/inductive-expected.lean` (pinned Lean 4.35.0, run by
`make reference-inductive`, part of `make check`) builds every case, adds it
to a scratch kernel environment and fails unless Lean's verdict is the
recorded one; its 100 rows must equal `inductive-expected.tsv`. Inductive
declarations are written in Lean syntax and elaborated with each type as a
local variable, then the variables replaced by constants, so the kernel and
not the elaborator decides. Columns: Lean's verdict (checked), LeanForth's
required outcome, the rule, the plan task, and for an accepted block what
the kernel generated.

| Group | Rows | Lean accepted / refused | Shows |
| --- | ---: | --- | --- |
| `ind.*` | 18 | 18 / 0 | the three examples and others; elimination level E0–E4; `k`; reflexive; indices; universes `max` |
| `pos.*` | 6 | 1 / 5 | negative, doubly negative, through a definition (`id (Bad → Nat)`), erased by a definition (`Function.const`), a non-valid occurrence (`f (Bad f)`), universe checked before positivity |
| `uniform.*` | 3 | 0 / 3 | another argument, a definitionally equal argument (`T (id α)`, BL-5), a constructor returning `T Nat` |
| `universe.*` | 5 | 2 / 3 | field too big (concrete, with a parameter), field that fits one universe up, a predicate taking any field, a declared type that is not a sort |
| `result.*` | 2 | 0 / 2 | a constructor returning another type; an index mentioning the type being declared |
| `params.*` | 5 | 2 / 3 | too few parameter binders; a constructor's parameter of another type; one definitionally equal (`id Type`); an index forcing a larger universe, and the same one universe up |
| `mutual.*` | 6 | 3 / 3 | even/odd predicates, tree/forest data, two single-constructor propositions (BL-6); universe, parameter and parameter-count mismatches |
| `nested.*` | 3 | 1 / 2 | `List Tree` with its auxiliary recursor; a non-positive nested occurrence; a nested parameter mentioning a constructor's variable |
| `names.*` | 5 | 0 / 5 | an existing name (`Nat`), a duplicate constructor, a duplicate universe parameter, an empty block, the reserved `_nested` prefix |
| `iota.*`, `k.*`, `eta.*`, `unit.*` | 11 | 5 / 6 | R1–R5, including the two Lean limitations BL-7 and BL-8 |
| `proj.*` | 5 | 2 / 3 | J1, J2 |
| `quot.*`, `quotinit.*` | 6 | 2 / 4 | Q1, Q2 |
| `lit.*` | 12 | 10 / 2 | L1, L3, L4 (L2 in `iota.nat-literal-major`) |
| `replay.*` | 10 | 4 / 6 | B1–B4: Lean's export checker on the `ind.nat` block, unchanged and with nine mutations |
| `primitive.*` | 3 | 3 / 0 | L5: `5 = 2` accepted with a forged `Nat.add` |
| **Total** | **100** | **53 / 47** | LeanForth must give: 50 accepted, 47 rejected, 3 unsupported |

**Exports** (`tests/reference/inductive/`, each reproduced byte for byte
with its manifest by the same make target, then staged by the Forth
importer with the manifest checked and re-emitted equal to the reader's
dump, `tests/core/compact-verify.sh`):

| File | Lines | What it shows |
| --- | ---: | --- |
| `blocks.ndjson` (from `blocks.lean`) | 505 | one block per kind: recursive (`N`), a `Prop` structure (`Both`), an indexed family with `k` (`Same`), `Prop`-only elimination (`Either`, no universe on its recursor), a mutual block (`Even`/`Odd`, recursors in name order), a nested block (`Tree`, `Tree.rec_1` with rules for `List.nil`/`List.cons`), a structure and its projection function (`Point.x`, an `Expr.proj`) |
| `nat-add-zero.ndjson` | 804 | the closure of `Nat.add_zero` and `Nat.zero_add` (§11) |
| `axioms.ndjson` | 225 | `propext`, `Classical.choice`, `Quot.sound`, their closure and the four `quot` records |

Five planted faults, each made `make reference-inductive` fail, one at a
time, each restored afterwards (2026-11-03): a changed verdict in the
table; a negative case made positive in the Lean file (`(Nat → Bad) → Bad`
for `pos.negative`, so Lean accepts it); a wrong expected Lean verdict; a
changed name in `blocks.ndjson`; a changed count in the manifest of
`nat-add-zero.ndjson`. The staging step relies on `compact-verify.sh`,
whose own planted faults are in `tests/mutants/faults.toml` (`stage-…`).

This is evidence about Lean, not about LeanForth: no LeanForth code checks
these cases yet. Each row's task (§12) turns its outcome from *unsupported*
into the required one.

## 10. Order of work and dependencies

Lean's `add_inductive` calls `whnf` and `is_def_eq` (parameters, positivity,
recursive fields, the recursor check), so in general it needs unfolding
(phase 4). Where a block's checks need only beta and structural comparison,
today's cautious checker could run them, answering *unknown* where Lean
might unfold (ADR 0011 K1). The checker reads the compact store (ADR 0016
C9 step 3) before it can see real exports. The Nat target needs delta with
reducibility hints (`abbrev`, `regular n`), so 5.4.1 follows 4.2.2.

## 11. The first real Lean target: `Nat.add_zero` and `Nat.zero_add`

`leanexport Init.Data.Nat.Basic -- Nat.add_zero Nat.zero_add` (pinned
toolchain; `nat-add-zero.ndjson`, 804 lines, 44,600 bytes, SHA-256
`6a7d05a2…853e5f1ebf`): 29 declaration records, **44 constants**: 7
inductive blocks (7 types, 8 constructors, 7 recursors), 19 definitions, 3
theorems; no axiom, opaque or quotient. Terms: 246 applications, 115 λ, 146
Π, 61 constants, 12 sorts, 7 bound variables, **5 projections**, **1 natural
literal (0)**; no `let`, string literal or `mdata`. Levels: 4 parameters, 7
successors, 4 `max`, no `imax`. Names: 136 string and 30 numeric parts,
including the private `_private.Init.Data.Nat.Basic.0.Nat.zero_add.match_1_1`.

The proofs: `Nat.add_zero := fun n => @rfl Nat (n + 0)`, so the kernel must
show `n + 0 ≡ n` — unfolding `HAdd.hAdd`, `instHAdd`, `Add.add`,
`instAddNat`, `Nat.add`, `Nat.brecOn`, … through projections, until
`Nat.rec` meets the literal `0` (`OfNat.ofNat Nat 0 (instOfNatNat 0)`,
reduced to the literal, then to `Nat.zero`, L2) and iota (R1) gives `n`.
`Nat.zero_add := fun x => Nat.brecOn x Nat.zero_add._f` (structural
recursion compiled to `Nat.rec` through `Nat.below`/`Nat.brecOn`), whose
cases need `0 + 0 ≡ 0` (literal arithmetic, L1, or iota) and, in the
successor case, iota on `Nat.succ n` and the first projection of a `PProd`.

Checklist, in export order (each line one record; "needs" lists the
features beyond phase 2's, with the plan task that provides them):

| # | Record | Kind | Needs |
| ---: | --- | --- | --- |
| 1 | `Nat` (`Nat.zero`, `Nat.succ`, `Nat.rec`) | block, recursive | B0–B5, recursor generation (5.2.1b) |
| 2 | `Eq` (`Eq.refl`, `Eq.rec`, `k`) | block, 2 parameters, 1 index | indexed family, K target (5.2.1c) |
| 3 | `outParam` | definition, regular 1 | phase 2 |
| 4 | `HAdd` (`HAdd.mk`, `HAdd.rec`) | block, structure, 3 parameters, universes `u v w` | non-recursive block (5.2.1a) |
| 5 | `HAdd.hAdd` | definition, abbrev | projection `HAdd.0` (5.2.2) |
| 6 | `Add` (`Add.mk`, `Add.rec`) | block, structure | 5.2.1a |
| 7 | `Add.add` | definition, abbrev | projection `Add.0` (5.2.2) |
| 8 | `instHAdd` | definition, regular 1 | constructor application |
| 9 | `PUnit` (`PUnit.unit`, `PUnit.rec`) | block, `Sort u`, unit-like | 5.2.1a; R5 available (5.2.2) |
| 10 | `PProd` (`PProd.mk`, `PProd.rec`) | block, structure, `max` levels | 5.2.1a |
| 11 | `Nat.below` | definition, abbrev | `Nat.rec` into `Sort (max 1 u)` (large elimination) |
| 12 | `Nat.brecOn.go` | definition, abbrev | `Nat.rec`, `PProd.mk`, `PUnit.unit` |
| 13 | `Nat.brecOn` | definition, abbrev | projection `PProd.0` |
| 14 | `Nat.casesOn` | definition, abbrev | `Nat.rec` |
| 15 | `Nat.add.match_1` | definition, abbrev | `Nat.casesOn` |
| 16 | `Nat.add._f` | definition, abbrev | projection `PProd.0` |
| 17 | `Nat.add` | definition, regular 1 | `Nat.brecOn` |
| 18 | `instAddNat` | definition, regular 2 | `Add.mk` |
| 19 | `OfNat` (`OfNat.mk`, `OfNat.rec`) | block, structure, a `Nat` parameter | 5.2.1a |
| 20 | `OfNat.ofNat` | definition, abbrev | projection `OfNat.0` |
| 21 | `instOfNatNat` | definition, regular 1 | `OfNat.mk` |
| 22 | `rfl` | definition, regular 1 | `Eq.refl` |
| 23 | **`Nat.add_zero`** | theorem | literal `0` (L2), delta with hints (phase 4), projections (J1), iota (R1) |
| 24 | `Unit` | definition, abbrev | `PUnit.{1}` |
| 25 | `Unit.unit` | definition, abbrev | `PUnit.unit` |
| 26 | `…Nat.zero_add.match_1_1` | definition, abbrev, private name | `Nat.casesOn`, literal `0` |
| 27 | `congrArg` | theorem | `Eq.rec` (typing only) |
| 28 | `Nat.zero_add._f` | definition, abbrev | iota on `Nat.succ n`, `PProd.0`, `Nat.add` on literals (L1, likely) |
| 29 | **`Nat.zero_add`** | theorem | `Nat.brecOn` (typing: beta) |

Counts by task: 5.2.1a five structure blocks (rows 4, 6, 9, 10, 19);
5.2.1b `Nat`; 5.2.1c `Eq`; 5.2.2 five projection records, used by six
declarations (rows 5, 7, 13, 16, 20, 28; the exporter writes the shared
`PProd.0` projection of rows 16 and 28 once); 5.2.3 the literal `0`
(rows 23, 26, 28) and likely `Nat.add` on literals; phase 4 delta with
hints for rows 23 and 28.
Not needed: quotients, axioms, strings, nested or mutual blocks, `let`. The
exact list of reductions the kernel performs will be confirmed by
LeanForth's derivation log (ADR 0013) when the closure is checked; this
table is read off the terms, not traced from Lean's kernel.

## 12. Implementation tasks

| ID | Task | Rules | Acceptance | Needs | Gates | Size |
| --- | --- | --- | --- | --- | --- | --- |
| 5.2.1a | Non-recursive blocks (`Bool`, `And`, structures `HAdd`, `PProd`, `PUnit`, `OfNat`): B0–B5, steps 1–12 of §3 without recursive fields, elimination level, recursor and rules generated and compared; block publication | V1, T0–T5, C1–C4, U1, E0–E4, G1–G4, B0–B5 | every `5.2.1a` row of the table; generated blocks equal to every non-recursive block of `Init`; mutated recursors rejected | phase 2; C9 step 3 | [kernel], [import] | M |
| 5.2.1b | Recursive blocks (`Nat`, `List`, reflexive): positivity, recursive fields, induction hypotheses; iota (R1) with literal majors (L2); the replay rows. *Implemented 2026-11-04 except iota (behind task 4.2.2c's hook) and the positivity that needs unfolding (4.2.2); gate open* | P1, P2, R1, L2 | every `5.2.1b` row; all recursive non-nested blocks of `Init` regenerated equal | 5.2.1a; phase 4 delta | [kernel] | M |
| 5.2.1c | Indexed families (`Eq`, vectors): indices, K target, K-like reduction | K1, R2 | every `5.2.1c` row | 5.2.1b | [kernel] | M |
| 5.2.2 | Structures and projections: `infer_proj`, `reduce_proj`, R3, R4, R5 in Lean's order | J1, J2, R3–R5 | every `5.2.2` row; BL-7 and BL-8 rows rejected as by Lean | 5.2.1a; phase 4 | [kernel], [import] | M |
| 5.2.3 | Literals: `bignum.fs` in `reduce_nat` with Lean's size exceptions, L2–L4, and the primitive check of Q1 | L1–L5 | every `5.2.3` row; bignum differential (exists) | 5.2.1b; Q1 | [kernel] | M |
| 5.2.4 | Quotients: Q1 initialisation and comparison, Q2 reduction | Q1, Q2 | every `5.2.4` row | 5.2.1c, 5.3.1 | [kernel], [axiom] | S |
| 5.2.5 | Mutual and nested blocks: shared motives, auxiliary types, restoration, `T.rec_k`. *In two parts: 5.2.5a mutual blocks, implemented 2026-11-04, gate open; 5.2.5b nested blocks, planned (below)*; the table's rows carry `5.2.5a` and `5.2.5b` | N1–N3, T3, T4 | every `5.2.5` row; all of `Init`'s blocks, then Std's and Mathlib's 7,013 | 5.2.1c | [kernel] | L (two M) |
| 5.3.1 | Allowlist v1 from `axioms.ndjson` | Q3 | altered and unlisted axioms not accepted | Q5 | [axiom], [owner] | S |
| 5.4.1 | Corpus C-Nat: `nat-add-zero.ndjson` | all above | 44 constants accepted; mutants rejected | 5.2.1a–5.2.3, 4.2.2 | — | M |

## 13. Test plan

1. **The table as specification.** A LeanForth differential reads the 100
   cases (written as NDJSON by a small writer added to the same Lean file,
   since a block Lean rejects cannot be exported by `leanexport`) and
   requires the `leanforth` column for every row whose task is done,
   and *unsupported* — never *accepted* — for the others. Each task's gate
   shows every outcome it can produce reached.
2. **Regeneration on real exports.** Every inductive block of `Init`, then
   Std and Mathlib (7,013 blocks, 7,046 types, 9,863 constructors, 7,162
   recursors), regenerated and compared (B3): all equal, with time and
   memory measured (plan W3). Lean's own replay of the same file is the
   oracle where a block differs.
3. **Mutations.** For a seeded sample of real blocks, one field of one
   constructor or recursor changed (a rule's right side, `k`, `nfields`,
   `numMotives`, a universe parameter name, a binder type): each must be
   *rejected*; a binder name or annotation changed must be accepted (Lean's
   `==` ignores them); the B4 fields changed: as Q2 decides.
4. **Reductions.** Seeded terms over the table's small types compared with
   `Kernel.isDefEq` and `Kernel.whnf`, as `tests/core/level-kernel-differential.py`
   does for levels.
5. **Failure paths** (ADR 0012 test matrix): fuel and room exhausted at
   every step of a block's check; a block's slots final all together or
   not at all; allocation failure injection.
6. **End to end.** `nat-add-zero.ndjson` checked: 44 accepted, axioms none;
   mutants (the statement `n + 0 = 0`, `Nat.rec`'s rules swapped, `Eq.rec`'s
   `k` cleared, `instOfNatNat` changed) rejected.
7. **Planted faults** in each implementation (`tests/mutants/faults.toml`):
   a skipped positivity check, a wrong elimination level, `k` always set,
   structure eta allowed for `Prop`, a literal operation by another name,
   the comparison B3 skipped — each caught.

## 14. Rejected alternatives

- **Trust the exported recursor.** A changed rule proves anything: the
  rule `zero ↦ succ` would make `Nat.rec` compute wrongly. Lean's replay
  never trusts it (rows `replay.*`).
- **Type-check the exported recursor instead of generating it.** A
  well-typed recursor can still have a wrong rule, `k` flag or elimination
  level; Lean's own comment says checking only a rule's type is
  insufficient (`inductive.cpp` 821–828).
- **Generate the recursor and store it without comparing.** The stored
  claim would differ from the input (ADR 0012 E1), and a file with a wrong
  recursor would be accepted where Lean's replay rejects it.
- **Compare with binder names.** Stricter than Lean's `==`; a file Lean
  accepts could be rejected.
- **Accept more than Lean** (definitional parameters, large elimination
  for mutual propositions, eta for products of units, iota for `Prop`
  structures): recorded in `BEYOND_LEAN.md` for a later improved mode.
- **Translate nested blocks our own way.** The auxiliary recursors' names,
  order and rules must equal Lean's (`T.rec_1`, …) for B3.
- **One ADR per plan task 5.1.1–5.1.5.** The rules interlock (literals in
  iota, structures in iota, quotients before recursors), so one record with
  rule IDs per section; the gates stay per implementation task (Q3).

## 15. Questions for the owner

**Answers (owner, 2026-11-03).** With no options, LeanForth's verdicts are
always Lean's; every stricter behaviour below is an opt-in flag.
Q1: copy Lean's by-name arithmetic by default; `--strict-builtins` answers
*unsupported* unless `Nat`, its operations, `Bool`, `String`, `Char` and
`List` are exactly Lean 4.35.0's (the recommendation below became the flag).
Q2: as recommended, accept as Lean does with a warning; a strict import that
refuses inconsistent fields is a later option (plan W8). Q3 and Q4: as
recommended; 5.2.1a starts now. Q5, amending decision 4: an axiom outside
the three (or an altered statement) gets Lean's verdict, labelled
**NOT PROVED: depends on** that axiom, as is everything that uses it, with
its own exit code; `--standard-axioms-only` answers *unsupported* instead.
(The exit code was changed by the owner on 2026-11-04, late: NOT PROVED
keeps Lean's exit status, 0 when everything is accepted, and the opt-in
`--strict-axioms` gives such a run status 6; `docs/project/OWNER_DECISIONS.md`,
"Command line: NOT PROVED exit status and the default engine".)
The questions as asked follow.

**Q1. Built-in arithmetic and the names it trusts (L5; [bypass]).** Lean's
kernel computes `2 + 3` itself for anything named `Nat.add`, without
checking its definition. With a deliberately wrong `Nat.add` in the input,
Lean accepts the theorem `5 = 2` (evidence rows `primitive.*`). Lean's
standard library cannot contain this (its `Init` defines `Nat.add`
correctly), but a Lean file that starts with `prelude` declares these
names itself, and LeanForth reads files that anyone can write. *Recommendation:* use the
built-in arithmetic only when `Nat`, its operations, `Bool`, `String`,
`Char` and `List` are exactly Lean 4.35.0's own (checked against pinned
records); otherwise answer *unsupported*. *Reasons:* it closes a way to get
a false theorem accepted; it never changes the answer for a file Lean's
`Init` produced; the alternative, copying Lean, would make "accepted"
depend on trusting the file's author. *Cost:* a pinned list and a check
when the environment is made.

**Q2. Exported fields that Lean's own checker ignores (B4).** When Lean
re-checks an exported library, it rebuilds a data type from its
constructors and compares the induction principle, but ignores some
recorded numbers (for example "is recursive") and a missing induction
principle. *Recommendation:* behave as Lean does — accept, use LeanForth's
own computed values, never the file's, and print a warning. The same for
the four quotient records, which Lean's checker also rebuilds and ignores
(§6). *Reasons:* identical to Lean; nothing from the file is trusted; the
warning shows a tampered file (lean4export never writes one). *Alternative:*
reject any inconsistency as *invalid* (stricter than Lean).

**Q3. One design record for phase 5's five design tasks.** This record
covers plan tasks 5.1.1–5.1.5 together. *Recommendation:* approve the
design section by section now (§3–§8), and keep one gate per implementation
task (§12). *Reason:* the rules depend on each other; the gates stay small.

**Q4. Start before phase 4 is finished?** *Recommendation:* yes for
5.2.1a only — non-recursive blocks with the cautious checker, *unknown*
wherever Lean might unfold — and the rest after 4.2.2 (unfolding). *Reasons:*
the block checker, comparison and publication can be built and reviewed
early; recursive types and the Nat target need unfolding anyway.

**Q5. Axioms other than the three.** Mathlib's export contains a fourth
axiom, `sorryAx` (what an unfinished Lean proof uses). *Recommendation:*
an axiom not on the allowlist, or listed with a different statement, is
*unsupported*, and so is everything that uses it; never *accepted* and
never silently skipped. *Reason:* owner decision 4; *unsupported* keeps
*rejected* meaning "Lean rejects" (ADR 0011 open question 1).

## 16. Consequences

- The checked environment (ADR 0012) gets block publication: several slots
  made final together; E5 lookups find constructors and recursors by
  name; dependencies and axiom sets per block.
- `docs/project/BEYOND_LEAN.md` gains BL-5 to BL-8; nothing changes in
  LeanForth's compatible answers.
- ADR 0011's U1 and U2 shrink task by task; K5 propagation covers blocks
  that stay *unsupported*.
- Phase 4's ADR 0014 must leave room for the routes of §5 in Lean's order
  of `is_def_eq_core` (1132–1207) and `whnf_core` (468–551).

## Implementation (plan task 5.2.1a)

Written 2026-11-03/04 by agent I21; experimental [kernel] and [import]
code, **not through its gate** (Lean's rules, the differential evidence
below, an independent AI review and the owner's approval are still
needed). Developer notes, with the steps, their outcomes and the limits:
[INDUCTIVE_BLOCKS.md](../programming/INDUCTIVE_BLOCKS.md).

**What.** `src/kernel/check-block.fs` runs §3's steps 1–11 for a block
of one non-recursive type in Lean's order (rules V1, T0–T5, C1–C4, U1,
E0–E4, K1, G1, G2), compares with the file (B3), records B4's ignored
fields as warnings and hands the block to the publisher (B5), which
makes every member's slot final together (`env-publish.fs`: the
candidate's span). `inductive-block.fs` holds B0, the audit and the
checks that need no typing (T0, C1, T1); `inductive-recursor.fs` builds
the recursor and its rules with bound variables, as `mk_rec_infos`,
`declare_recursors` and `mk_rec_rules` build them with free ones;
`level-geq.fs` ports `is_geq` (U1). The feed carries each block's header
and its members' exported data into the input (`core/input.fs`,
`lf-input-more`).

**Decisions**, none of which adds or widens a rule beyond Lean's:

1. *Scope.* A block is in scope when it has one type and each
   constructor mentions the type only as the head of its result: Lean's
   `is_rec` is false and no index holds the type. Indices are allowed,
   so non-recursive indexed families such as `Eq` are decided (the row
   `ind.eq`, of task 5.2.1c, gives Lean's verdict); `k` is computed (step
   10), and K-like reduction (R2) is not part of the task. Anything else
   is *unsupported* (diagnostic 63), found by the audit before any
   typing, as ADR 0011's U1.
2. *Constructors of one name* are not a B0 failure but reach C4: Lean's
   replay looks both up by name and its kernel throws
   `duplicateConstructor` (row `names.duplicate-constructor`). Every other
   repeated name in a block is B0 (*invalid*).
3. *Unfolding* (phase 4): where Lean's `whnf` or `is_def_eq` might unfold
   a definition -- a telescope headed by a constant, a field type such as
   `outParam (Type w)` (`HAdd`), a parameter domain `id Type` -- the block
   is *unknown* (K1), never rejected.
4. *Lean's local types.* Each parameter, index and field is given its
   binder's type with outer `outParam`, `semiOutParam`, `optParam` and
   `autoParam` removed, as Lean's `mk_local_decl_for` does
   (`consume_type_annotations`), in the recursor and in the contexts that
   type the constructors' fields.
5. *The block's own type* is visible to inference while its constructors
   are checked, through a hook in `env-signature.fs` (`lf-envsig-local`),
   with L1 and L2 as for any constant and no dependency.
6. *P4, a new precondition of rules D3 and D5* (ADR 0011). Once a
   structure like `PUnit` can be accepted, Lean's `is_def_eq_unit_like`
   equates any two terms of its type, also after `is_def_eq_app` failed;
   D3 and D5 now call two variable-headed terms apart only when the left
   one's type, inferred aside, is visibly headed by no constant. Without
   it, a theorem Lean accepts would be rejected (row
   `unit.punit-variables`, added). It only turns *rejected* into
   *unknown*.
7. *G4* (`check_recursors`) is not run: it checks Lean's own generation,
   which B3 compares with directly; for a non-recursive block each rule's
   reduct is the minor premise applied to the fields, whose type is the
   recursor's result type by construction.
8. *B4* differences set a warning bit per block (`lf-block-warnings`,
   owner answer Q2), kept on the accepted block's slots
   (`lf-env-warnings`; review rvI21 M2). Since 2026-11-04 `bin/leanforth
   check` stages and feeds the export, so inductive blocks get the
   checker's verdicts from the command line, but it prints no B4 warning
   yet (plan task 6.5.2's per-declaration report is where it belongs);
   `check --record`, `replay` and `print` still read with
   `import/checker-input.fs`, which refuses inductive types: a temporary
   gap, closed by a run record version for any size (6.5.2) and by
   moving `print` onto the feed (3.4.1). B5's generated values are not
   yet published: the slots hold the file's data, whose recursor and
   constructor numbers B3 proved equal to LeanForth's, but whose type
   fields `numIndices`, `isRec`,
   `isReflexive`, `numNested` are the file's and untrusted (the warning
   bits say which differ from LeanForth's); tasks 5.2.1b and 5.2.2, the
   first to read them, must use LeanForth's values.
9. *A recursor missing from the block* (B4) is accepted, as Lean's replay
   accepts it. Lean's kernel then holds the recursor it generated. Its
   name is reserved (review rvI21 B2): N2, the publisher's re-check and the
   scheduler's readiness treat `T.rec` of an earlier type `T` as declared
   when `T` is accepted or added (decision 11; K5 when undecided or
   unsupported), and `T.rec_<n>` likewise for a type not accepted. A later
   use of it gets LeanForth's generated recursor, which is Lean's (decision
   12), and a file that uses it but declares it nowhere is checked as Lean
   checks it (ADR 0016 amendment 1; until then the importer refused it as
   *invalid*). Only a tampered file can do any of this. *An empty block*
   (no type, constructor or recursor) is staged by the importer as one
   declaration without a name (ADR 0016 amendment 1), which the block
   check rejects at step 4 as Lean's kernel does (`emptyBlock`,
   diagnostic 78); the file goes on. *A file naming any other constant it
   never declares*, or holding a block with no type but with constructors
   or recursors, is refused by the importer (*invalid*) before any check.
10. *Capacity.* A block of more than 512 constructors is *full*, found
    when it is opened, before anything is written for its constructors
    (review rvI21 B1). T1 also counts each constructor's binders, as
    Lean's `get_params` does (L1). is_geq's recursion is counted on
    normalize's frame counter, so a deep one is *full* (review of the heap
    stores).
11. *A block rejected only by B3 keeps its names* (review rvI21 round 2,
    R2-1, which found that a later definition of `T.rec`, `T` or a
    constructor was accepted where Lean answers `alreadyDeclared`). Lean's
    replay compares after its kernel added the block, so `T`, its
    constructors and `T.rec` are declared although the file's records are
    refused. The check marks such a block (`lf-env-added!`); the publisher
    re-checks it as an accepted block and records its slots (declaration,
    dependencies, axioms, the recipe of decision 12), and marks its type's
    and constructors' slots added (not the file's recursors, which the
    kernel may not have added), each constructor with the type's universe
    parameters, as the kernel declares it. N2, the publisher's re-check and
    the holders of `T.rec` count the names as declared (*rejected*,
    `alreadyDeclared`); lookups find the added slots usable
    (`lf-slot-usable?`), so a later use of the type, a constructor or
    `T.rec` (decision 12) gets Lean's verdict (owner's condition of
    2026-11-04: rows `after.b3-*`). The block's own outcome stays
    *rejected*. Their types were checked by steps 1–12, so nothing from the
    file is trusted that Lean does not trust.
12. *The generated recursor for later declarations* (owner's condition of
    2026-11-04). When no slot holds `T.rec` (the file left it out, or holds
    a different or renamed one in a block rejected by B3), Lean's kernel
    still holds the recursor it generated. The block check leaves a recipe
    on the block's slots (`lf-env-recipe!`: whether the recursor eliminates
    into every universe, and whether the telescope it walked after whnf was
    the raw one). A later lookup of `T.rec` that no slot holds answers (-1
    ok), the type's slot given apart (`lf-env-genrec-of`; review rvI21
    R4-5: no caller, log or outline takes `T`'s slot for `T.rec`).
    Inference applies L1 against the recursor's own universe parameters
    (the motive's first), L2, records the block as the dependency, and
    builds the recursor in its own scratch at the use's universe
    arguments, from the block's input, with the same builder
    (`generated-recursor.fs`; `inductive-recursor.fs`
    `lf-recursor-build-at`): the motive's Sort at the first argument, the
    block's constants at the others, and every binder domain read from
    instances of the block's type and constructor types with the block's
    universe parameters replaced by those arguments
    (`lf-mixed-level-substitute`; review rvI21 R5-1, which found the
    domains left at the block's own universes). That is the recursor's
    type instantiated, as Lean's `instantiate_type_lparams` gives it
    (rows `after.eq-at-*`, `after.exists-at-*`, `after.universe-max-at-*`:
    renamed, concrete, swapped and applied universes). No universe name of the
    recursor's own is made, so its motive universe need not be a level of
    the file (R4-1: such a file was *invalid*), and its universe parameters
    have no limit of their own (R4-3: they were capped at 64). A block
    whose type is a Sort only after whnf has no recipe: a use of its
    `T.rec` stays *unknown* (diagnostic 77; row
    `after.redex-type-left-out-then-use-rec`, a block such as `IE.U2 :
    (fun x : Type 1 => x) Type`), a temporary gap until task 4.2.2 brings
    whnf and unfolding to a lookup (steps 4.2.2b-e). The P4 guard of
    decision 6 is a temporary gap until task 5.2.2 (structure eta and
    unit-like comparison): it can only turn *rejected* into *unknown*.
    The other temporary gaps of the default mode, each with its task:
    the capacities (512 constructors, 64 parameters plus indices or
    fields, 16 dependencies: *full*; task 6.2.0); a file that names an
    undeclared constant or holds a block with constructors or recursors
    but no type (*invalid* as a whole, where Lean rejects the declaration
    concerned; task 5.2.6); a binder whose type's type is a Sort only
    after whnf (*unknown*; task 4.2.2).

**Evidence** (2026-11-04, Gforth 1.0.0, Lean 4.35.0):

- The table grew from 100 to 120 rows, every verdict Lean's (checked by
  `inductive-expected.lean`, which also prints every case as the export of
  what Lean checked): twins of four task 5.2.1a rows that use `Nat` or
  unfolding (T2, C3 and C2 without `Nat`, a block declared twice for N2, a
  β-redex parameter for C2), Lean's replay of the non-recursive `Bool`
  block unchanged and with twelve mutations (B3, B4), and the two
  unit-like rows of P4.
- `make test-inductive-table` runs LeanForth on all 120 files. Of task
  5.2.1a's 44 rows, 38 give Lean's verdict (19 accepted, 19 rejected, each
  with its rule's diagnostic; `ind.universe-max` and `ind.sort-max` were
  *unknown* until the fix of level normalization under the feed's name
  view, the review rvKC's finding H1, 2026-11-04); six are pending, each
  with its reason: four use or redeclare `Nat`
  (task 5.2.1b; K5), `params.constructor-binder-defeq` needs unfolding,
  and `names.empty-block` is refused by the reader. Of the 76 later rows,
  64 are *unsupported*, 7 *unknown*, 3 give Lean's verdict (`ind.eq`,
  `params.index-one-universe-up`, `params.index-instead-of-parameter`),
  and 2 whose files name an undeclared constant are *invalid*; none is
  accepted or rejected against Lean.
- The review rvI21 (2026-11-04) added 19 rows (139 in all): its probes as
  Lean's replays, `optParam`/`outParam` fields, T0, T1 and N2 cases, and
  five rows of declarations after a block (decision 9). Its second round
  added seven rows after a block (decision 11; 146 in all). The owner's
  condition (2026-11-04) added five more (151): uses after a block
  rejected by B3 (the type, a constructor, `T.rec`, the renamed recursor)
  and `T.rec` without its universe argument, with
  `after.recursor-left-out-then-use-rec` and `after.b3-ctor-then-use` now
  giving Lean's verdict (decisions 11, 12; ADR 0016 amendment 1). Of task
  5.2.1a's 75 rows, 70 give Lean's verdict (27 accepted, 43 rejected, the
  empty block among them since the importer stages it) and 5 are
  pending, each naming the later task that closes it: 5.2.1b (four rows
  using or redeclaring `Nat`) and 4.2.2 (one needing unfolding). The
  review's fourth round added 15 rows that strip a block's recursors and
  use the generated one (166 in all), and its fifth 10 that use it at
  universes other than its own names (176): of task 5.2.1a's 94 rows, 88
  give Lean's verdict (45 accepted, 43 rejected) and 6 are pending
  (5.2.1b four, 4.2.2 two). 67 planted faults are caught.
- `make test-check-block` (41 committed table files, 60 since the review; blocks published
  together; the reference export tampered field by field; fuel bisection;
  a full store), eighteen planted faults (`ind-*`) all caught, and the
  real exports: in `blocks.ndjson` `Both`, `Same` and `Either` are
  accepted; in `nat-add-zero.ndjson` `Eq`, `Add`, `PUnit` and, since the
  name-view fix (rvKC H1, 2026-11-04), `PProd` (and so `rfl` and `Unit`),
  with `HAdd` unknown (unfolding `outParam`); in `axioms.ndjson` `Iff`,
  `Eq` and `Nonempty`.
- Lean's `Init` checked whole (2026-11-04, a probe kept in the agents'
  work folder; `leanexport Init`, SHA-256 `c1b2071a…a179`, the export
  `reference-compact-init` checks; 59,349 declarations, 604 blocks;
  `gforth-fast`, fuel 100,000 per check; 896 s: staging with the manifest
  26 s, the feed 126 s, every check 744 s). 53 blocks are outside task
  5.2.1a (mutual, recursive or nested, or the type in a result index:
  *unsupported*). Of the 551 in scope, **142 are accepted**: their 142
  recursors and 182 constructors, generated by LeanForth, equal Lean's
  (among them `Bool`, `True`, `False`, `And`, `Or`, `Iff`, `Exists`, `Eq`,
  `HEq`, `Subtype`, `Option`, `Decidable`, `PUnit`, `Add`, `Mul`, `Max`).
  144 are *unknown*: 30 by the name-view defect at U1 (such as `Prod`,
  `PProd`, `Sigma`, `Functor`), 37 where a field's type needs unfolding
  (32 sorts such as `outParam (Type w)`, 5 function types), 24 at a
  comparison that needs unfolding, 53 because a dependency was undecided
  (K5). 265 are *unsupported*: 216 because a dependency is (mostly
  `Nat`), 49 with a literal, projection or other U2 form. **None is
  rejected or invalid**, and no block has a B4 warning. With them, 763 of
  Init's definitions and theorems are accepted.
- The same probe after the name-view fix (rvKC H1, 2026-11-04; staging
  20 s, the feed 33 s, every check 291 s): all 30 blocks the defect left
  *unknown* are accepted, and 12 more whose dependency was undecided
  (K5); 12 such blocks are now *unsupported*, as a dependency of theirs
  is. Of the 551 blocks in scope, **184 are accepted**, 90 *unknown*,
  277 *unsupported*; still none is rejected or invalid. 1,014 of Init's
  definitions and theorems are accepted.

## Implementation (plan task 5.2.1b)

Written 2026-11-04 by agent N1; experimental [kernel] code, **not
through its gate** (Lean's rules, the differential evidence below, an
independent AI review and the owner's approval are still needed). It
extends 5.2.1a's check to recursive blocks of one type, as Lean's
`add_inductive` checks them; developer notes in
[INDUCTIVE_BLOCKS.md](../programming/INDUCTIVE_BLOCKS.md).

**What.** The audit (`inductive-block.fs`) admits a block whose fields
mention its type and refuses a nested one (an earlier inductive type
applied to arguments mentioning the type, Lean's
`elim_nested_inductive` test: *unsupported*, task 5.2.5), recording
Lean's `is_rec` and `is_reflexive` for B4. Step 9 (`check-block.fs`)
runs Lean's `check_positivity` on each field after its universe check
(P1, P2; diagnostics 79, 80), and C3 tests that the result's indices do
not mention the type. The builder (`inductive-recursor.fs`) finds the
recursive fields (`is_rec_argument`), gives each minor premise its
induction hypotheses and each rule its recursive calls at Lean's
recursor levels; the generated recursor of decision 12 gets them too.

**Decisions**, none of which adds or widens a rule beyond Lean's:

13. *whnf where Lean reduces.* Lean's positivity, recursive-field test
    and telescope put terms in `whnf`. *Since the switch of 2026-11-04
    (below, "Iota and the switch to Lean's whnf"), LeanForth calls task
    4.2.2c's port of Lean's `whnf` (`whnf.fs`) there; what follows was the
    stand-in until then.* Until task 4.2.2's whnf (agent
    U4) is on main, LeanForth uses whnfB and goes on only where Lean's
    whnf provably stops: a Sort, Pi, lambda or variable head, or a
    constant head named none of `reduce_nat`'s fifteen operations
    (`Nat.succ`, `Nat.add`, …; matched by name only, `type_checker.cpp`
    672–703) that is the type itself or a constant declared as an
    inductive type, constructor, axiom or opaque constant; elsewhere the
    block is *unknown* (diagnostic 64). The name test comes first, for the
    type itself too: Lean's `whnf` computes on a block's own type named
    `Nat.add` as on Lean's `Nat.add` (review rvN1 B2, corrected
    2026-11-04; rows `forged.type-named-nat-add*`). A variable head stops
    Lean's `whnf` only while no variable has a value: task 4.2.3 (`let`)
    must revisit this test, as `mixed-head.fs` says for its own rules.
    The same test lets step 8 reject a telescope ending in such a
    constant (`T : Nat`, Lean's `typeExpected`), where 5.2.1a said
    *unknown*.
14. *Fields without an occurrence* are not put in whnf: reduction never
    makes an occurrence of a type being declared (Lean's own comment,
    `inductive.cpp` 129–133), so positivity passes and the field is not
    recursive whatever whnf gives. Lean computes that whnf and drops it,
    so LeanForth may skip it only if Lean's `whnf` of a type-correct term
    cannot refuse it. *Corrected 2026-11-04 (review rvN1 B1):* the first
    version said only a resource exception could, which is false. Lean's
    `whnf` computes `Nat.pow` and `Nat.shiftLeft` by name and refuses a
    second argument of 2³² or more (`get_count_arg`, `type_checker.cpp`
    308–313), a fixed rule, not a setting; a forged file reaches it
    (rows `forged.pow-*`, `forged.shiftleft-field`: Lean refuses, the
    first version accepted). So, until task 5.2.3 brings Lean's
    arithmetic on literals, a definition, theorem or block member named
    `Nat.pow` or `Nat.shiftLeft` is *unsupported* (diagnostic 86), and by
    K5 so is every declaration whose check meets one: a term reaches
    them in Lean's `whnf` only by naming them or through a definition
    whose value does (delta), every recursor rule being built from
    constructor types that cannot name them. The other refusals of
    `type_checker.cpp` met in `whnf` of a type-correct term are resource
    refusals (`deepRecursion`, heartbeats) or settings (`LEAN_NAT_MAX_SIZE`,
    the owner's question L1 of review rvN1). Lean-produced exports are not
    affected: `Init`'s `Nat.pow` and `Nat.shiftLeft` are *unsupported*
    already (their closures hold literals and projections).
15. *The nested test may find more* than Lean's: an earlier type that is
    not usable (undecided, unsupported) has every argument tested, its
    exported `numParams` not being known to be Lean's. Only
    *unsupported* can follow.
16. *Iota* (R1, with literal majors L2) lives in Lean's `whnf_core`;
    agent U4's port leaves a hook for it. It is not implemented here (a
    second whnf is not to be written): plan task 4.2.2c's hook, then the
    5.2.1b follow-up. Rows `iota.*` stay *unsupported* (they use
    literals, task 5.2.3). *Done 2026-11-04: `iota.fs`, below.*
17. *A rebuild keeps the interrupted block's domains.* The generated
    recursor (decision 12), built during another block's check, wrote
    over that block's parameter domains; it now copies them aside and
    gives them back (row `after.list-left-out-then-lookup-during-param-block`,
    *invalid* before).
18. *G4* stays unrun (decision 7): a recursive rule's reduct is the
    minor premise applied to the fields and the recursive calls, whose
    types are its induction hypotheses by construction.

**Evidence** (2026-11-04, Gforth 1.0.0, Lean 4.35.0):

- The table grew from 176 to 198 rows, every verdict Lean's: recursive
  and reflexive blocks, negative and non-valid occurrences reached
  through beta, in later binders and fields, and uses of the generated
  recursor of recursive blocks at other universes and during another
  block's check. Task 5.2.1b's 46 rows: 41 give Lean's verdict (25
  accepted, 16 rejected), five are pending (positivity through a
  definition: task 4.2.2; the three `iota.*` theorems: literals, task
  5.2.3, and iota, task 4.2.2c). Task 5.2.1a's four rows using `Nat` now
  give Lean's verdict (92 of 94; two pending on 4.2.2). No row of a later
  task is decided against Lean.
- `make test-check-block` (145 committed files), 15 new planted faults
  and three re-targeted ones, all caught.
- Lean's `Init` checked whole before and after (probe, `gforth-fast`):
  blocks accepted 184 → 261 of 604; of its 53 blocks whose fields
  mention their type, 29 accepted with recursors equal to Lean's, 23
  stopped by a dependency (K5), one nested (*unsupported*); none rejected
  or invalid. Other declarations accepted 1,015 → 1,609. Details in
  [INDUCTIVE_BLOCKS.md](../programming/INDUCTIVE_BLOCKS.md#evidence).

**Review rvN1 and its corrections** (2026-11-04). The independent review
of the change (`.claude/work/rvN1/REVIEW.md` in the main checkout; 98
probes against pinned Lean) found two cases where the first version
accepted what Lean refuses, both reachable only from a hand-written file
that declares its own `Nat` operations; they are fixed:

- **B1**: decision 14's premise was false (above): a definition or
  block member named `Nat.pow` or `Nat.shiftLeft` is now *unsupported*
  (diagnostic 86, `lf-nat-counted?` in `inductive-block.fs`, used by both
  audits).
- **B2**: `lf-blk-stuck?` tested for the block's own type before the
  names of `reduce_nat`'s operations; the name test now comes first
  (decision 13), and those names are one table (`lf-nat-ops`).
- **M1**: the review's probes are table rows now, Lean-checked, with
  committed files: a W type, an `Acc`, indexed recursive blocks (task
  5.2.1c's rows, decided already), reflexive fields with annotated
  binders or a redex in a Pi body, a redex in a Pi's domain, the type as
  another type's index, a telescope ending in a definition, uses of
  their generated recursors, and the forged cases of B1 and B2 (rows
  `forged.*`, task 5.2.3). The review's six surviving planted faults are
  caught.
- **L2**: `make test-check-block` refuses each allocation of a block's
  check in turn (`tests/support/alloc-fail.fs`): the block must end
  *full*. This catches a dropped failure of positivity's or the
  builder's whnf; a dropped failure of the occurrence walk stays a
  recorded gap (`faults.toml`: its stack grows on the heap, which no test
  hook refuses, and its fuel failures leave none for the next step).
- **L3, L4**: the documentation below and in `INDUCTIVE_BLOCKS.md`;
  `lf-ind-inner-run` refuses a negative budget as `lf-ind-run` does.

Owner question L1 of the review stays open: whether Lean's refusals that
name `LEAN_NAT_MAX_SIZE` (a setting) count as resource refusals, like
`deepRecursion`, or are reproduced as rejections in task 5.2.3 as §7 L1
plans.

**Iota and the switch to Lean's whnf** (2026-11-04, agent N1, the rest of
task 5.2.1b; experimental [kernel] code, gate open). Task 4.2.2c's port
of Lean's `whnf` (`whnf.fs`, agent U4) is on main, so:

- **Iota** (R1): `iota.fs` ports `inductive_reduce_rec` (`inductive.h`
  77–116; `get_rec_rule_for`, `is_constructor_app`, `inductive.cpp` 53–60,
  114–122) behind `whnf.fs`'s hook `lf-whnf-iota`. For a recursor that a
  usable slot holds (B3 made its numbers, `k` and rules Lean's), the
  major premise is put in Lean's `whnf`; a constructor application gets
  its rule, at the application's universe arguments, applied to the
  parameters, motives and minor premises, the constructor's fields and
  the arguments after the major premise; no rule applies where Lean's
  `inductive_reduce_rec` returns none. *Unknown* (diagnostic 81), as not
  ported: a major premise that is no constructor application when `k` is
  set (`to_cnstr_when_K` needs inference and comparison) or when its
  type may be a non-recursive structure (`to_cnstr_when_structure`
  eta-expands with projections, task 5.2.2); and Lean's generated
  recursor that no slot holds (decision 12). With `k` set, a major
  premise whose `whnf` is the constructor gets the rule Lean's K path
  gives (the one constructor, no fields). Literal majors (L2) stay with
  task 5.2.3; `whnf.fs` answers *unknown* where Lean's `reduce_nat` could
  make one (K7: `Nat.succ` with one argument, so `Nat.rec` on `Nat.succ n`
  is *unknown*).
- **The switch** (decision 13): `check-block.fs` puts the telescope
  (step 8, every type) and positivity's field types (step 9) in Lean's
  `whnf` on the step's inference job (`lf-minfer-whnf-job`), and the
  recursor builder its recursive fields' types on a frames record of its
  own (`lf-rcr-frames`), so the two agree on which fields are recursive.
  The stand-in `lf-blk-left?` and its name test are gone; B2's case is
  now `whnf.fs`'s K7 (diagnostic 82). A rebuild of a generated recursor
  (decision 12) uses the same `whnf`; it starts no other rebuild, since
  `whnf` and iota answer *unknown* for a generated recursor. Decision 14
  stands: a field type without an occurrence is still not put in whnf.
- **Evidence** (2026-11-04, Gforth 1.0.0, Lean 4.35.0): 12 new table rows
  (256 cases): iota without literals on `Bool`, `List` and `Nat.zero`
  (a rule's fields, its induction hypothesis, an argument after the major
  premise), `Eq.refl` (k), a stuck major premise, `Nat.succ` (K7), and
  positivity through `Bool.rec` (recursive, and erasing a negative
  occurrence). Rows that now give Lean's verdict: `pos.through-definition`
  (rejected), `pos.erased-by-definition`, `universe.type-a-sort-by-definition`
  (accepted), the six iota rows Lean accepts and the two positivity rows.
  Pending (each with its task): the three iota rows Lean refuses
  (*unknown*: the port's "no" decides nothing until task 4.2.2d), the
  generated recursor of a type that is a Sort only after whnf (the
  rebuild still reads the raw telescope; a follow-up). Tasks 5.2.1a,
  5.2.1b and 5.2.5a: 181 rows, ok 100, rejected 71, unknown 6, unsupported
  4 (10 pending); none of the 256 decided against Lean. Planted faults:
  four new on iota, five re-targeted, three deleted with the stand-in
  they broke; all caught.

## Implementation (plan task 5.2.5a)

Written 2026-11-04 by agent N1, the first part of task 5.2.5; experimental
[kernel] code, **not through its gate**. It extends the block check to
**mutual blocks** as Lean's `add_inductive` checks them; nested blocks
(5.2.5b) stay *unsupported*.

**What.** B0 checks each type's `all` list (the block's types, in order),
universe parameters and `numParams` against the first type's, and the
constructors as the types' `ctors` lists in order (`inductive-block.fs`).
Steps 6 to 8 run for each type in order, as `check_inductive_types`
(`inductive.cpp` 254–299) does: N2 on `T` and `T.rec`, the type's type,
its telescope; a later type's parameter domains must be the first type's
(`is_def_eq`, T3: diagnostic 83, D1–D5 reject, else unknown), it must
have `numParams` of them (T3: 84), and its universe must be
`is_equivalent` to the first's (T4: 85). Step 9 checks C4 within each
type (Lean's name set is per type, 459–465), C2 against the first type's
parameters, C3 against the constructor's own type, positivity and
recursive fields across the block (`is_valid_ind_app` for any type), and
then a constructor named as another type's is `alreadyDeclared`
(`declare_constructors`, 499–519). E1 makes a mutual block of
propositions eliminate only into `Prop` (529–532); `k` is never set for
one (599). The builder (`inductive-recursor.fs`) makes one motive per
type and one minor premise per constructor of the block; a recursive
field's hypothesis uses the motive of the type its type ends in, and its
rule calls that type's recursor (`mk_rec_infos` 663–716, `mk_rec_rules`
770–785). B3 compares each exported recursor with the generated
recursor of the same name (`all`, `numMotives`, `numMinors`, the rules of
its own type's constructors); B4 tests each type. The generated recursor
of a later type (decision 12) is built from the whole block, its records
kept aside during another block's check.

**Decisions**, none of which adds or widens a rule beyond Lean's:

19. *Steps 6 to 8 per type*, each reporting its own step number, as
    Lean interleaves them per type; the step table keeps its numbers.
20. *A later type's parameter domains are bound with the first type's*
    after the comparison, as Lean instantiates them with `m_params`; its
    index domains, read under its own parameter binders, stand for the
    same positions.
21. *The table's task 5.2.5 is split* into 5.2.5a (mutual rows) and
    5.2.5b (nested rows), so the mutual rows are held to Lean's verdicts
    now.

**Evidence** (2026-11-04, Gforth 1.0.0, Lean 4.35.0): the table has 209
cases (11 new, every verdict Lean's: even and odd with an index, indexed
data, three types with a parameter and a universe, a function field
into the other type, a negative occurrence of the other type, one
constructor in the whole block (E1), and uses of the generated recursor
of the first and of a later type at their own, concrete and renamed
universes). Task 5.2.5a's 18 rows: 17 give Lean's verdict (13 accepted,
4 rejected: T3 twice, T4, P1); `mutual.even-odd` is pending (Nat
literals, task 5.2.3). `make test-check-block` checks them with their
diagnostics and steps; 8 new planted faults (`mut-*`) are caught.
Lean's `Init` has no mutual block, so its numbers stay 261 of 604 blocks
accepted, none rejected or invalid (whole-`Init` probe).

## Plan (task 5.2.5b): nested blocks

Lean checks a nested block (`Tree | node : List Tree → Tree`;
`Lean.Syntax`, with `Array Syntax`) by checking an **auxiliary mutual
block** and translating its results back (`add_inductive`, 1248–1349).
LeanForth will port each step, citing `inductive.cpp`:

1. **Auxiliary block** (`elim_nested_inductive_fn`, 985–1180). With the
   first type's parameters as locals (`get_params`, 1138–1146), walk each
   constructor's type after its parameters top-down (`replace`): an
   application `I Ds is` of an earlier inductive type `I` whose first
   `numParams(I)` arguments `Ds` mention a type of the block (the test
   the audit runs now, 1023–1055) and have no loose bound variable (else
   `nestedLocalVariable`, rejected) becomes `Iaux As is`. The first time
   `I Ds` (its parameters abstracted, compared structurally, 1081–1091)
   is met, every type `J` of `I`'s block becomes an auxiliary type named
   `_nested.J_k` (`mk_unique_name`: `k` from 1, the first name no
   declaration of the environment has, 1001–1007), its type `J`'s at
   `I`'s universe levels with `Ds` for `J`'s parameters, re-abstracted
   over the block's parameters, and its constructors `J.c` renamed
   `_nested.J_k.c` with their types likewise (1098–1127). The queue goes
   on over the auxiliary types' constructors, so `List (List T)` gives
   two auxiliary types. LeanForth needs: names made in the name store's
   scratch tier (`_nested.List_1`); the types and constructor types as
   scratch terms (level substitution: `lf-mixed-level-substitute`;
   parameters: instantiate and abstract on frame steps); the block
   record grown by the auxiliary types (type records are a growable slab
   already; their constructors count against the 512 of
   `lf-ind-ctor-capacity`, task 6.2.0).
2. **Check the auxiliary block** with steps 6 to 12 as a mutual block
   (task 5.2.5a's code), `numNested` the number of auxiliary types: its
   types and constructors are terms in scratch rather than input
   declarations, so the steps read them through the block's records
   (as `lf-recursor-build-at` reads instances) instead of `lf-input-decl`.
3. **Restore** (`restore_nested` 927–975 and 1257–1314): in every
   constructor type, recursor type and rule, an auxiliary type applied to
   the parameters becomes `I Ds` again, an auxiliary constructor becomes
   `J.c` at `I`'s levels applied to `Ds`, and an auxiliary recursor
   `_nested.J_k.rec` becomes `T.rec_1`, `T.rec_2`, ... (named after the
   block's first type in order, `mk_aux_rec_name_map` 1191–1217); the
   restored recursors keep the auxiliary block's numbers (motives and
   minors of all types), with `all` the block's own types. A rewriting
   pass on frame steps (no host recursion), into scratch.
4. **Type the nested applications** `I Ds` under the parameters
   (1319–1324): their parameters never appear in the auxiliary block, so
   this is where an ill-typed `Ds` is rejected. The re-check of the
   restored terms (1333–1347) is defensive, as G4 is (decision 7): B3
   compares them with Lean's instead.
5. **Compare** (B3): the block's constructors, whose restored types must
   equal the file's, and every recursor, `T.rec` and each `T.rec_k`, by
   name; B4 with `numNested`.
6. **Environment**: an accepted nested block's first type holds the names
   `T.rec_1`, ... (`environment.fs`, `lf-env-reserving`, which now gives
   them only to types not accepted); a use of `T.rec_k` that no slot
   holds gets the generated recursor (decision 12), which rebuilds the
   auxiliary block.
7. **Tests**: the rows `nested.*` (5.2.5b); Lean-checked rows for a
   parameterised tree (`Tree α` with `List (Tree α)`), `List (List T)`,
   `Array` and `Option` children, nesting inside a mutual block, an
   earlier declaration named `_nested.List_1` (the next name taken),
   Lean's replay of a nested block mutated (rules of `T.rec_1`, its name,
   a restored constructor type), and stripped `T.rec_1` uses; planted
   faults for each step; `Init`'s `Lean.Syntax`.

Size: comparable to tasks 5.2.1b and 5.2.5a together (two batches):
the auxiliary block's construction and the restoring pass are new
term-rewriting passes, and the steps must read types and constructors
that are not input declarations. Until it is done a nested block, and
everything that uses it, is *unsupported* (diagnostic 63, reason 3).

## Reproduction

```sh
make reference-inductive        # Lean verdicts, exports, Forth staging
LEAN=.tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean \
  bash scripts/export.sh OUT.ndjson Init.Data.Nat.Basic -- Nat.add_zero Nat.zero_add
curl -fsSL -o inductive.cpp \
  https://raw.githubusercontent.com/leanprover/lean4/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/kernel/inductive.cpp
```

SHA-256 of the Lean files read (kernel files fetched 2026-11-03 at the
commit above): `src/kernel/inductive.cpp`
`ad549d9a85bf75ea0405cd84f2c6759651c193474f7865ffc823d1467a79c7d6`,
`inductive.h` `61bd41532dc7bd3c0632130c3bf718975094be36740cd1189f1885e6656d398a`,
`quot.cpp` `500621538bfa97cd63ebf0c4b0e111b69232f5d4fa34aa56b5f6482599782627`,
`quot.h` `17105c835e79ccb397194e9663dba71b5515edbc89c9698b0d58a95dc30a8243`,
`type_checker.cpp` `26eae5ebb88f6f7da2c0a91f470aae4b74d370569dc5ca81b44b2d5c24c8df4e`,
`type_checker.h` `251e5910586972445d0ebd317a056e27d8f124515f19ae7865560526fa7935b0`,
`environment.cpp` `0930ff37576a02240dcc16a2089d3280dcc58898ccbc772b620be031089c30b2`,
`environment.h` `95e9b7aad9f138830197972c1812ca206317dae059ace9b7815674beec8500ed`,
`declaration.h` `eb9c497bb19dab26550cbb5196a13e0a925896c6d357a8faa2f3794c1e798a51`,
`declaration.cpp` `1d4751c0a2a1e0663cc08dfb00941164c7fb61b16f885c2722cf24422b2ca454`,
`src/Lean/Declaration.lean` `1cf2f06d848086f165b3df0afe494924ae26aaea248d5e0135d5efc2d588948f`.
Toolchain sources: `Lean/Replay.lean`
`251ed00e1cedd95c5d1fc4104ac191beb1de618abbc2fc49319ff0e37d139329`,
`Lean/Expr.lean` `b9a91d9d170201c2a3622b9c55d694466f54e0e1b8f6068a2d296ff98650169c`,
`LeanExport/Basic.lean` `2e839d4ac1ef1992cfe09c489a97928ad8f8eaea3925bc76b511c6bf85e1b8aa`.
`inductive.h`, `quot.h`, `type_checker.cpp`, `type_checker.h`,
`environment.cpp`, `declaration.h`, `declaration.cpp` and
`Declaration.lean` equal the files ADR 0011 read.

Exports (`tests/reference/inductive/`): `blocks.ndjson`
`fcaa1b751c55afd836c460aeb1fb927cdfcad8f9abfaed7df9be29606b967f51`,
`nat-add-zero.ndjson`
`6a7d05a2727d7c33b69124e7eb0ca8365fba9c6f8fe610e245264d853e5f1ebf`,
`axioms.ndjson`
`3161cada6d59c35be1776a7eabb803f99522c465c37af56ec7972cc6d56821b0`.
Mathlib's axioms: `LC_ALL=C grep -n '^{"axiom"' .tools/mathlib/mathlib.ndjson`
and the name records they refer to (Mathlib export of 2026-11-02,
SHA-256 `18448e5d…59c6`).
