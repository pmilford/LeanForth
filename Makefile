GFORTH ?= $(if $(wildcard .tools/gforth/bin/gforth),.tools/gforth/bin/gforth,gforth)
LEAN ?= lean

.PHONY: smoke reference reference-export test-harness test-core test-scope-differential test-shift-differential test-instantiate-differential test-program test-program-differential
smoke:
	$(GFORTH) tests/smoke/smoke.fs

reference:
	LEAN=$(LEAN) bash tests/reference/check.sh

reference-export:
	LEAN=$(LEAN) bash tests/reference/export-check.sh

test-harness:
	GFORTH=$(GFORTH) bash tests/harness/check.sh

test-core:
	$(GFORTH) tests/core/arena.fs
	$(GFORTH) tests/core/terms.fs
	$(GFORTH) tests/core/scope.fs
	$(GFORTH) tests/core/shift.fs
	$(GFORTH) tests/core/instantiate.fs
	$(GFORTH) tests/core/beta.fs

test-scope-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/core/scope-differential.sh

test-shift-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/core/shift-differential.sh

test-instantiate-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/core/instantiate-differential.sh

test-program:
	$(GFORTH) tests/program/clamp.fs

test-program-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/program/differential.sh
