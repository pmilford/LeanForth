GFORTH ?= $(if $(wildcard .tools/gforth/bin/gforth),.tools/gforth/bin/gforth,gforth)

.PHONY: smoke
smoke:
	$(GFORTH) tests/smoke/smoke.fs
