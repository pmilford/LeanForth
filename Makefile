GFORTH ?= $(if $(wildcard .tools/gforth/bin/gforth),.tools/gforth/bin/gforth,gforth)
LEAN ?= lean

.PHONY: smoke reference test-harness test-core
smoke:
	$(GFORTH) tests/smoke/smoke.fs

reference:
	LEAN=$(LEAN) bash tests/reference/check.sh

test-harness:
	GFORTH=$(GFORTH) bash tests/harness/check.sh

test-core:
	$(GFORTH) tests/core/arena.fs
