# Structural arena prototype

`src/core/arena.fs` is a bounded experiment in storing integer-indexed nodes.
It does not represent Lean expressions, validate terms, check types, issue
theorem handles or establish mathematical truth. It is not a kernel API.

The arena stores at most 64 nodes. An atom contains an opaque cell payload; a
pair contains two indices of already allocated nodes, so constructed pairs
cannot reference later nodes. Constructors return an index and true on success,
or false on invalid references or exhaustion, without advancing the count.
`lf-arena-reset` invalidates all existing indices; an index may be reused and
must never be retained across a reset. The prototype is global, mutable and not
thread-safe. Its raw address word assumes a valid index; it must not be exposed
to untrusted inputs. Cell layout is host-specific and is not serialization.

`make test-core` exercises construction, cell layout, invalid references,
capacity and reset through the Gforth test harness. Future designs must address
ownership, stale handles, input validation, portability, resource limits and
an audited logical representation. Any change that confers proof validity
requires the kernel review gate.
