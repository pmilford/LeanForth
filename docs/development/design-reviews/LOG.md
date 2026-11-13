# Design reviews

Every design is reviewed by an independent reviewer before code starts, and the owner approves a one-page summary
(owner, 2026-11-13; [DESIGN_STAGE_REVIEW.md](../DESIGN_STAGE_REVIEW.md), plan 9.4.7). Reports are saved here and logged
below, newest last.

| Date | Design | Reviewer | Report | Verdict | Follow-up |
| --- | --- | --- | --- | --- | --- |
| 2026-11-13 | FRONT_END, FE1E, FE1G, FE1I, FE2 (together) | independent design reviewer (Opus) | [report](2026-11-13-front-end.md) | BLOCKING for S1: B1 library not visible during a `.lf` run; B2 FE1e0 not done; B3 two undo-trail designs; B4 no binder-kind source; B5 error-code ranges collide | the S1 interface note (being written) settles B1-B5 and M2-M5; the trims to about 300 lines are a later task |
| 2026-11-13 | VERIFY_COMMAND (8.4.1) | independent design reviewer (Opus) | [report](2026-11-13-verify.md) | BLOCKING for V1: B1 contract text reaches the Lean file unparsed (a false contract accepted by Lean; also in main's 5.5.1 generator) | hotfix on main first, then B1's rest, M1-M4 on `verify-b`; the owner's verify questions before steps c, d, n |
| 2026-11-13 | the hotfix of main's contract generator (vc-hotfix 2cff2572, 5a73ba08) | the VERIFY_COMMAND reviewer (probe), then the coordinator (probe) | [report](2026-11-13-verify.md), last sections | not blocking for main: no contract text reaches Lean as code; hidden-line separators, repeated inputs, unbound names and zero cases refused | merged to main 2026-11-13 by fast-forward; V1's rest on `verify-b` |
| 2026-11-13 | S1_INTERFACE (the S1 interface note) | a fresh independent design reviewer (Opus) | [report](2026-11-13-front-end.md), last section | blocking on two text fixes (R1 error ranges shared by parallel branches; R2 four whnf words needed earlier), fixed in 45031427 with M-a to M-d | approved by the owner 2026-11-13 |
| 2026-11-13 | S2_INTERFACE (slice S2: FE1 by induction and rewriting) | a fresh independent design reviewer (Opus) | [report](2026-11-13-s2.md) | BLOCKING for s2-unfold merge A (B1: format-2 data read as "no smart unfolding") and for s1-elab (B2: S1's `#check` midpoint needs lazy delta); M1-M4, L1-L8 | all fixed in the note's text (format 3; S1 §11 amendment: s1-elab merges after merge A); the owner's one-page approval |
