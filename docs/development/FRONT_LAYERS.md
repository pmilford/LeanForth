# The front end's layers: Lean's library in LeanForth

Lean writes its tactics on layers: `Lean.Meta` (whnf, isDefEq, inferType, instantiateMVars), `Meta/AppBuilder.lean`
and `Meta/Basic.lean` (term builders, binders, telescopes), `Meta/Tactic` (the `MVarId` goal operations) and
`Elab/Tactic` (the tactic elaborators). LeanForth's front end (`src/front/`, untrusted: only the kernel's check
decides) ports them as public Forth words, one file per layer where practical, so that a tactic is mostly calls
(design [TACTIC_PLUGINS.md](../design/TACTIC_PLUGINS.md) section 1, appendix F). This table is where to look before
writing a word: a Lean function a port calls is a public word of its layer, never a private copy in a tactic file.
It started from the architecture review of 2026-11-18 (table (a)) and is kept current by each slice that adds a
layer word (the architect role, `.claude/agents/architect.md`, checks it).

Library words of the tactic layer throw on failure, as Lean's do (`meta-must.fs`: the code carries the outcome,
`lf-meta-catch` hands it back to outcome code); the Meta core below returns outcomes. No throwing word runs inside a
`dw-run` walk (`dag-walk.fs`).

## The layers (2026-11-18, slices a2-i to a2-iii)

| Lean layer | Forth file | Public words (Lean function) |
| --- | --- | --- |
| `Lean.Meta` core | `whnf.fs`, `defeq.fs`, `infer.fs`, `mvars.fs`, `instantiate.fs`, `meta-env.fs`, `kabstract.fs`, `meta-check.fs`, `fun-info.fs`, `synth.fs`, `instances.fs`, `discr-keys.fs`, `discr-tree.fs` (the index of library 2, shared by the instance table and simp), `meta-config.fs` | `lf-meta-whnf`, `lf-meta-whnf-r`, `lf-whnf-core` (whnf, whnfR, whnfCore); `lf-meta-defeq` (isDefEq); `lf-infer`, `lf-get-level` (inferType, getLevel); `lf-instantiate-mvars`; `lf-mvar-new`, `lf-meta-const-fresh` (mkFreshExprMVar, mkConstWithFreshMVarLevels); `lf-meta-const-at` (mkConst's core); `lf-meta-abstract`, `lf-meta-instantiate1`, `lf-meta-head-beta`; `lf-meta-kabstract`; `lf-meta-check`; `lf-meta-fun-info`, `lf-meta-is-prop`; `lf-synth-instance`; `lf-mctx-mark`, `-rollback-to`, `-commit`, `lf-mctx-depth{` (saveState, withNewMCtxDepth); `lf-meta-at`, `lf-meta-with` (withTransparency, withConfig); `lf-with-reducible`, `lf-with-assignable-opaque`, `lf-with-approx` (withReducible, withAssignableSyntheticOpaque, approxDefEq: each sets only its own part); `lf-term-holds?`, `lf-term-holds-with?` (term-find.fs: findMVar? with a closure) |
| throwing faces and scopes | `meta-must.fs` | `lf-must`; `lf-whnf!`, `lf-whnf-r!`, `lf-whnf-d!`, `lf-infer!`, `lf-level!`, `lf-defeq!`, `lf-instantiate!`, `lf-made!`; `lf-meta-catch` (try/catch from outcome code); `lf-commit-when` (commitWhen); `lf-with-goal` (MVarId.withContext); `lf-goal-type`, `lf-goal-tag`, `lf-goal-view`, `lf-goal-kind` (getType, getTag, getDecl; a missing record thrown); `lf-with-view` (withLCtx); `lf-with-record` (a call's frame on a slab, freed on both paths); `lf-tac-defeq` (the tactics' isDefEq) |
| `Meta/AppBuilder`, `Expr` builders | `app-builder.fs` | `lf-mk-const`, `-const0`, `-const1` (mkConst); `lf-mk-app`, `lf-mk-app-n` (mkApp, mkAppN); `lf-mk-eq`, `lf-mk-eq-refl`, `lf-mk-eq-symm`, `lf-mk-eq-trans`, `lf-mk-expected-prop-hint`, `lf-mk-congr-arg`, `lf-mk-app-m`, `lf-mk-app-m-of`, `lf-mk-eq-mp`, `lf-mk-eq-mpr` (mkEq ... mkEqMPR); `lf-mk-const-id`; core's `lf-const-levels`, `lf-const-level@` (Expr.constLevels!); `lf-eq?` (Expr.eq?); `lf-match-eq?` (matchEq?); `lf-meta-has-mvar?` (Expr.hasMVar) |
| `Meta/Basic` binders and telescopes | `telescope.fs` | `lf-with-local-decl` (withLocalDecl); `lf-local-decl-new` (mkFreshFVarId and mkLocalDecl); `lf-forall-meta-telescope-reducing`, `lf-forall-meta-bounded-telescope` (maxMVars); `lf-expected-num-args` (getExpectedNumArgsAux); `lf-mk-lambda-fvars`, `lf-mk-forall-fvars` (with elimMVar's case); `lf-binder-mvar`; `lf-binder-kind-at`, `lf-binder-kind!`, `lf-walk-kind`, `lf-binder-of`, `lf-binder-name` (the one source of binder kinds: the declaration's, else the node's record) |
| `Meta/Tactic` (`MVarId.*`) | `goals.fs`, `meta-tactic/goal.fs`, `apply.fs`, `assumption.fs`, `constructor.fs`; still inside `tactic-rewrite.fs` (rewrite), `tactic-induction.fs` (ElimApp) | `lf-goal-new`, `lf-goal-clear`, `lf-goal-rename`, `lf-mvar-assign`; `lf-goal-not-assigned` (checkNotAssigned), `lf-goal-replace-target-eq` (replaceTargetEq), `lf-goal-head-beta-type` (headBetaType), `lf-goal-tag-append`, `lf-name-append-tag` (appendTag, with modifyBase and eraseMacroScopes); `lf-mvar-open?` (mvars.fs: getMVarsNoDelayed's test); `lf-goal-apply` (MVarId.apply with synthAppInstances, appendParentTag, reorderGoals), `lf-goal-assumption`, `lf-goal-constructor` (constructorCore); `lf-goal-intro-n` (introN with mkAuxName), `lf-goal-refl` (MVarId.refl, applyRfl's Eq path), `lf-goal-checked-assign` (checkedAssign) |
| `Elab.Term` | `elab-term.fs`, `elab-app.fs`, `elab-pending.fs`, `elab-decl.fs` | `lf-elab-term`, `lf-elab-ensuring` (elabTerm, elabTermEnsuringType), `lf-elab-type`, elabAppArgs, `lf-elab-with-synth` (withSynthesize), synthesizeSyntheticMVars |
| tactic messages | `tactic-msg.fs` (below `meta-tactic/`, so the goal layer needs no tactic file) | `lf-tac-indented.`, `lf-tac-inline.`, `lf-tac-line.` (indentExpr, inlineExpr), `lf-tac-goal-of.`, `lf-tac-.name`, `lf-has-type-but-expected.` (throwTypeMismatchError with mkHasTypeButIsExpectedMsg), `lf-tac-inline`, `lf-tac-failed`, `lf-tac-lean-error?`, `lf-tac-forget-lean` (the errors try and observing? catch) |
| `Elab.Tactic` | `tactic-run.fs`, `tactic-core.fs`, `tactic-api.fs`, `tactics/*.fs` | evalTactic (the rows, `lf-tac-eval`), getMainGoal (`lf-tac-main`), focus, done, saveState/restore (`lf-tac-try`); `lf-tac-step-run` (withMainContext, the step record `tb`), `lf-tac-pop-main` (popMainGoal), `lf-lift-meta-tactic` (liftMetaTactic), `lf-tac-elab` (Tactic.elabTerm's hook), `lf-tac-elab-for-apply` (elabTermForApply), `lf-tac-arg`, `lf-tac-args#`, `lf-tac-arg-at` (getArg), `lf-tac-only` (setGoals [g]), `lf-tac-with-synth` (withSynthesize), `lf-tac-try-lean` (try, observing?), `lf-tac-elab-term` and `lf-tac-elab-ensuring` (Tactic.elabTerm, elabTermEnsuringType), `lf-close-main-goal-using` (closeMainGoalUsing), `lf-tac-intro1` (liftMetaTactic of introN 1); the registry `lf-tactic:`; the tactic files `tactics/intro.fs`, `exact.fs`, `rfl.fs` set the fixed kinds' rows (scripts/check-tactic-plugins.py's ownership table) |

## Not ported yet, by the slice that brings them

- Still to move (plan 9.4.8l-I C3, C4): rewrite's goal operation and induction's ElimApp into `meta-tactic/`, and rw, induction and case into `tactics/`. Moved in C2 (2026-11-19): intro, exact and rfl (`tactic-basic.fs` deleted).
- `mkAppOptM` (no caller yet); `getMVarsNoDelayed` (apply refuses a term that keeps a metavariable, unsupported).
- S3: `mkDecide`, `mkDecideProof`, `mkExpectedTypeHint`, `zetaReduce`. S4: `getLocalHyps`, `exfalso`, Int literals.
- The simp core: `mkCongr`, `mkCongrFun`, `mkEqNDRec`, `mkOfEqTrue`, `mkEqTrue` (with their first callers).
- `forallTelescope` and `lambdaTelescope` (no caller yet). `lf-mk-nat-lit` (mkNatLit) waits for the reuse pass of
  `nat-offset.fs`; the Meta files' own binder locals (`defeq.fs`, `whnf.fs`, `infer.fs`, `fun-info.fs`,
  `meta-check.fs`) move onto `lf-with-local-decl` in that pass.

## Measured sizes (Lean lines against Forth lines, 2026-11-18)

Lean's lines are the definition and the private helpers it calls in pinned Lean 4.35.0 (`src/lean/Lean/`); Forth's
are code lines of the words that port it, without comments, stack comments on their own lines or tests. The shared
helpers (`abl-eq`, `abl-infer-d`, `abl-eq-app`, the binder-kind words) are counted with the first row that uses them.

| Lean function (file:line) | Lean lines | Forth lines |
| --- | ---: | ---: |
| `mkConst`, `mkAppN` (Expr.lean:618, 772) | 4 | 10 |
| `mkEq`, `mkEqRefl` (AppBuilder.lean:40, 65) | 10 | 4 |
| `mkEqSymm` with `infer` (98, 84) | 14 | 12 |
| `mkEqTrans` (110) | 17 | 4 |
| `mkExpectedPropHint` (23-30) | 4 | 2 |
| `mkCongrArg` with `isRefl?`, `congrArg?` (212, 189, 199) | 35 | 24 |
| `mkAppM` with `mkAppMArgs`, `mkAppMFinal`, `mkFun` (345, 284, 275, 312) | 45 | 50 |
| `mkEqMP`, `mkEqMPR` (444-448) | 5 | 3 |
| `forallMetaTelescopeReducing` (Basic.lean:1751-1792) | 29 | 33 |
| `withLocalDecl` (Basic.lean:1825-1837) | 13 | 7 |
| `mkLambdaFVars`, `mkForallFVars` with `mkBinding` and `elimMVar`'s ported case (Basic.lean:1174-1185; MetavarContext.lean:1201-1254, 1337-1380) | about 110 | 57 |
| `commitWhen`, `withContext`, the throwing faces (MonadBacktrack.lean:50; Basic.lean) | about 15 | 28 |

The builders are about Lean's size or smaller; the walk with a frame (`mkAppM`, the telescope) is a little larger,
as Lean's recursion becomes a frame on a heap stack.
