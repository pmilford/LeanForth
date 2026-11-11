\ Loaded after src/main.fs by tests/cli/shared_depths.py: the per-check audit
\ memo (ADR 0014 Amendment 4) is an optimisation, so verdicts must not depend
\ on it. Turns it off in the (single) context of the run.
lf-memo-off lf-audit-memo!
