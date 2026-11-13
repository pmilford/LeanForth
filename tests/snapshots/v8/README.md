# Snapshot fixtures of verdict version 8

Written by `scripts/write-snapshot-fixtures.sh 2ad871e` (plan step 6.2.5c2;
[SNAPSHOT_COMPATIBILITY.md](../../../docs/design/SNAPSHOT_COMPATIBILITY.md)
section 6): the build of commit `2ad871ec31cbd97f5a8c6662c0717a8bd8c395a5`, run on
`gforth 1.0.0 amd64`, checked this checkout's exports
(paths below are relative to `tests/`) and saved each snapshot; `dependent`
is a layer on `inductive`. Each build that bumps the verdict version writes
its own set; a set that leaves the window of two versions is deleted by name.

| File | Command |
| --- | --- |
| `inductive.lfsnap` | `check --save-snapshot inductive.lfsnap cli/inductive.ndjson` |
| `nested.lfsnap` | `check --save-snapshot nested.lfsnap cli/nested.ndjson` |
| `kinds.lfsnap` | `check --save-snapshot kinds.lfsnap --no-manifest core/reexport/kinds.ndjson` |
| `unfold.lfsnap` | `check --save-snapshot unfold.lfsnap cli/unfold.ndjson` |
| `let-b.lfsnap` | `check --save-snapshot let-b.lfsnap cli/let-b.ndjson` |
| `init-slice.lfsnap` | `check --save-snapshot init-slice.lfsnap author/init-slice.ndjson` |
| `dependent.lfsnap` | `check --save-snapshot dependent.lfsnap --snapshot snapshots/v8/inductive.lfsnap cli/dependent.ndjson` |

SHA-256 of each file:

```text
d984fe6f978492d0c8401bd9358cc679ca47f24fea275000689c40d9b81286f2  inductive.lfsnap
fda650d43922d8ba1a5e346952980b272a5c269f78c355f8be109caa284ae904  nested.lfsnap
eb2ad3500ced77f4f2b7399e0d8c105cef8d598c11d5fd2ba772820b241c5817  kinds.lfsnap
d426dad5d38c38d2ac3f933f56994e308d0807df93e1d833139a16250954e7aa  unfold.lfsnap
ff935ef618d05acef83418d2746f7340158cab6c528ed65a2ec4bf4b0c736f5f  let-b.lfsnap
56f8430ee547614537924c06e7c89b27c3412cd9d3babce30b5862cf789bc8a3  init-slice.lfsnap
ef914645351ba2f0c9d51155ca8c07163b2061bfcdf52dce133d1e63e4dfe80d  dependent.lfsnap
```
