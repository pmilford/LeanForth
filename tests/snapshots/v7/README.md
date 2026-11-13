# Snapshot fixtures of verdict version 7

Written by `scripts/write-snapshot-fixtures.sh 7301204` (plan step 6.2.5c2;
[SNAPSHOT_COMPATIBILITY.md](../../../docs/design/SNAPSHOT_COMPATIBILITY.md)
section 6): the build of commit `730120437964302f5798bce3f1d28843af2134b6`, run on
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
| `dependent.lfsnap` | `check --save-snapshot dependent.lfsnap --snapshot snapshots/v7/inductive.lfsnap cli/dependent.ndjson` |

SHA-256 of each file:

```text
2d21a3fba49784eb14f07d85d39aa69a97b6edc582281135e4d2f68ee196ef23  inductive.lfsnap
f54101b1fe69ee422c4809ecf8099b4600b3ef97fe1238d6685273cee0a354e7  nested.lfsnap
cda8682a185733c57eaf39becf9beda7a4688caea4cac7e8109bae76b8defa1d  kinds.lfsnap
a713f917d1608d54c4f8f9d2a9a589693609572363c8aea8b052383444442013  unfold.lfsnap
60ba2df30075a8002981b4b4773b72e90f215a8eb6af1a89226f1e6888249a44  let-b.lfsnap
46f76f9c3d693d4a111d8ab149f4bf7dadac5dc5afe56bf89f5bb1a440260631  init-slice.lfsnap
857bfad6e1c45e9c36f0f6114846227b6eca808039da4e91b09d2ecdd62e180e  dependent.lfsnap
```
