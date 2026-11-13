# Snapshot fixtures of verdict version 9

Written by `scripts/write-snapshot-fixtures.sh HEAD` (plan step 6.2.5c2;
[SNAPSHOT_COMPATIBILITY.md](../../../docs/design/SNAPSHOT_COMPATIBILITY.md)
section 6): the build of commit `025f4ebb9f14d4cebd974815fb1303971f161bf1`, run on
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
| `dependent.lfsnap` | `check --save-snapshot dependent.lfsnap --snapshot snapshots/v9/inductive.lfsnap cli/dependent.ndjson` |

SHA-256 of each file:

```text
c78e3770145799fdaebbfb0e02f47aa3579b4c478b2b8d548439a685e0a95746  inductive.lfsnap
dbab7fc3f18600ddce6ca4fcc3cee0cc2d0b7a6a4fad9ca49a1a062c6d313212  nested.lfsnap
11645c1b8bfa930b05bc2ec16eb7b46b339f6a40fee4b5335abe2480d6a8259f  kinds.lfsnap
d4ce7a080e9dee80888d12fa27606e8b943ff696a652fb9c3374f56374032077  unfold.lfsnap
df49073fe2a4f330706a9f866efc9594a90be1986b2b8519955872a7144515cc  let-b.lfsnap
fbddbb5107a2f2a8a587dd8c3e1346c9a7fa3eb55419aaa017d5178871cc511b  init-slice.lfsnap
9dd9f7bf8342c12e7fc501718d1ab7b080d6439ff2abd3c69a95e46fd91c9efe  dependent.lfsnap
```
