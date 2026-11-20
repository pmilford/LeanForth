\ Layer entry: the importer, on the general library (lib/) and Lean's data
\ model (core/), without the kernel. Staging of decoded Lean exports into
\ the term store and the reader of lean4export NDJSON files; the importer
\ stage (ADR 0016 C9 step 2): an export, checked against its manifest,
\ staged into a compact input tier (core/compact*.fs) with its
\ declarations, declaring no context member and allocating nothing while
\ loading; the feed (C9 step 3, plan task 3.2.2), which makes a sealed
\ stage the checker's input in file order, its names read from the input
\ tier; and the input tier saved to and loaded from a sectioned file (ADR
\ 0020, plan step SN2), which a fresh check never runs.
\ src/main.fs loads it through src/load/checker.fs, after the kernel.
require ../import/load.fs
require ../import/ndjson.fs
require ../import/stage.fs
require ../import/feed.fs
require ../import/snapshot-tier.fs
