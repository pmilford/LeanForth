\ Every tactic file of src/front/tactics/, one require each, sorted
\ (tactic plug-in design 4; tests/front/check_registry.py refuses this
\ list unless it is sorted, has no repeat and names every tactic file).
\ src/main.fs loads it; a tactic registers itself as it loads.
require ./absurd.fs
require ./and-intros.fs
require ./apply.fs
require ./assumption.fs
require ./blocks.fs
require ./by-cases.fs
require ./by-contra.fs
require ./case.fs
require ./change.fs
require ./clear.fs
require ./constructor.fs
require ./contradiction.fs
require ./decide.fs
require ./delta.fs
require ./exact.fs
require ./exacts.fs
require ./exfalso.fs
require ./exists.fs
require ./have.fs
require ./induction.fs
require ./intro.fs
require ./intros.fs
require ./left.fs
require ./obtain.fs
require ./refine.fs
require ./rename-i.fs
require ./replace.fs
require ./revert.fs
require ./rewrite.fs
require ./rfl.fs
require ./rintro.fs
require ./right.fs
require ./rwa.fs
require ./specialize.fs
require ./subst.fs
require ./swap.fs
require ./symm.fs
require ./trivial.fs
