\ Every tactic file of src/front/tactics/, one require each, sorted
\ (tactic plug-in design 4; tests/front/check_registry.py refuses this
\ list unless it is sorted, has no repeat and names every tactic file).
\ src/main.fs loads it; a tactic registers itself as it loads.
require ./apply.fs
require ./assumption.fs
require ./constructor.fs
require ./exact.fs
require ./intro.fs
require ./rfl.fs
