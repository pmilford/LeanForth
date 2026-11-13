# Design reviews

Every design is reviewed by an independent reviewer before code starts, and the owner approves a one-page summary
(owner, 2026-11-13; [DESIGN_STAGE_REVIEW.md](../DESIGN_STAGE_REVIEW.md), plan 9.4.7). Reports are saved here and logged
below, newest last.

| Date | Design | Reviewer | Report | Verdict | Follow-up |
| --- | --- | --- | --- | --- | --- |
| 2026-11-13 | FRONT_END, FE1E, FE1G, FE1I, FE2 (together) | independent design reviewer (Opus) | [report](2026-11-13-front-end.md) | BLOCKING for S1: B1 library not visible during a `.lf` run; B2 FE1e0 not done; B3 two undo-trail designs; B4 no binder-kind source; B5 error-code ranges collide | the S1 interface note (being written) settles B1-B5 and M2-M5; the trims to about 300 lines are a later task |
| 2026-11-13 | VERIFY_COMMAND (8.4.1) | independent design reviewer (Opus) | [report](2026-11-13-verify.md) | BLOCKING for V1: B1 contract text reaches the Lean file unparsed (a false contract accepted by Lean; also in main's 5.5.1 generator) | hotfix on main first, then B1's rest, M1-M4 on `verify-b`; the owner's verify questions before steps c, d, n |
