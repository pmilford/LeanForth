# Architecture and principal data structures

How the Forth code is organised, where the trust boundary will be, how
parallel checking is laid out, and what the main records look like. As of
2026-11-02 (commit `fc558cc`); every name below is a real file or word
unless a box is dashed, which marks a plan. Nothing is trusted yet: the
checker in `src/kernel/` becomes trusted only after the review gate in
`AGENTS.md`. The user-level view is in [workflows](../user/WORKFLOWS.md);
the folder rules are in the [source layout](../../src/README.md).

## Layers and trust

Each module `require`s exactly the modules whose words it uses, and
dependencies point one way: `lib` ← `core` ← `kernel`. `import`, `program`
and `present` use the library and the data model but nothing in `kernel`,
and the checker never loads `present`. `src/main.fs` requires the top
modules: the definition probe, the loader, the NDJSON reader, the three
program files, the IR reader and the term printer.

```mermaid
flowchart TB
  subgraph kernel ["src/kernel"]
    passes["Checking passes, experimental:<br/>level-value, level-compare, level-substitute,<br/>mixed-level-substitute, mixed-shift, mixed-instantiate,<br/>mixed-beta, mixed-rebuild, mixed-compare, mixed-convert,<br/>mixed-signature-probe, mixed-signature-audit,<br/>mixed-infer, mixed-definition-probe"]
    first["First checker and checked environment<br/>ADR 0011, ADR 0012"]
  end
  subgraph core ["src/core"]
    model["Lean's data model:<br/>terms.fs, levels.fs, names.fs (64-entry stores),<br/>level-scope, tagged-sort-boundary, symbolic-session,<br/>generation-handles, constant-references,<br/>constant-term-boundary, constant-term-scope"]
  end
  subgraph import ["src/import"]
    ndjson["ndjson.fs: lean4export 3.1.0 reader<br/>ndjson-count.fs: counting tool"]
    load["load.fs: test staging"]
  end
  subgraph program ["src/program"]
    words["clamp.fs, examples.fs: example words<br/>ir-reader.fs: Forth source to IR 0.1<br/>program-depth.fs: depth analyzer"]
  end
  subgraph present ["src/present"]
    printer["term-printer.fs and print-*.fs, latex-text.fs:<br/>Lean notation, ASCII, LaTeX<br/>binder-table.fs: names, kinds, sources"]
    outline["Proof-outline printer<br/>task 2.4.4"]
  end
  subgraph lib ["src/lib"]
    libcore["lib.fs: portability, bounds, store:, nodes,<br/>outcomes, walk:, walk2:, frames:, contexts"]
    task["task.fs: job pool"]
    text["bytes.fs: lines, UTF-8<br/>json.fs: JSON views"]
  end
  sched["Scheduler and publisher<br/>ADR 0009, ADR 0012"]

  passes --> model
  first -.-> model
  model --> libcore
  ndjson --> text
  text --> libcore
  task --> libcore
  load --> model
  words --> libcore
  printer --> model
  outline -.-> printer
  sched -.-> task
  sched -.-> first

  classDef planned stroke-dasharray: 6 4
  classDef gate stroke-width: 3px
  class first,outline,sched planned
  class passes,first gate
```

Arrows point from a module to what it uses. The thick border marks the
part that is to become the trusted checker; the data model and library
beneath it fall under the same review, because its verdicts depend on them.
Everything that reads input — `bytes.fs`, `json.fs`, `ndjson.fs`,
`ir-reader.fs` — is untrusted and fail-closed: it can refuse input, or at
worst hand over a different claim, but it cannot decide *accepted*. The
printer in `src/present/` is presentation only: a wrong name changes the
text, never a verdict.

| Folder | Files | State today |
| --- | ---: | --- |
| `src/lib/` | 12 | Records only: stores, walks and frames are passed by address; contexts and the job pool exist, but no module keeps its state in a context yet |
| `src/core/` | 10 | Each module's state is in named records listed on its "State:" header line, still one global copy per module |
| `src/kernel/` | 14 | Same; the passes return the shared outcomes; none returns *rejected* yet |
| `src/import/` | 3 | The reader keeps all state in the `export:` record passed to it |
| `src/program/` | 4 | Example words, depth analyzer, IR reader with one reader record |
| `src/present/` | 8 | Term printer with its print-job record and the presentation side table (64 term entries, 32 declarations) |

## Tasks, contexts and the shared environment

[ADR 0009](../adr/0009-reentrant-state-and-parallel-checking.md) (accepted)
puts all of one check's mutable state in a *context*, so several checks can
run as Forth tasks in one image;
[ADR 0012](../adr/0012-checked-environment.md) (design accepted) adds the
shared library of accepted declarations with a single publisher. The job
pool and contexts exist (`src/lib/task.fs`, `src/lib/context.fs`); moving
the modules' state into contexts, the scheduler, the publisher and the
environment do not.

```mermaid
flowchart TB
  subgraph main ["Main task"]
    sched["Scheduler<br/>starts a check when its dependencies are final"]
    drive["Drives the pool<br/>pool-start, job-submit, job-wait, pool-stop"]
    pub["Publisher<br/>the only writer of the environment"]
  end
  queue["Bounded job queue: task-pool, task-queue<br/>Gforth 1.0 threads, 0.7.3 cooperative, else serial"]
  subgraph workers ["Worker tasks"]
    w1["Worker<br/>its own lf-context and lf-owner"]
    w2["Worker"]
  end
  subgraph contexts ["Contexts"]
    c1["Context, ALLOCATEd, owned by one job until job-wait<br/>members: context-store:, context-walk:,<br/>context-frames:, context-record:"]
    c2["Context"]
  end
  subgraph shared ["Shared, read-only"]
    input["Input stores<br/>names, levels, terms from the export"]
    env["Checked environment<br/>one slot per declaration, written once"]
    layout["context-layout<br/>load-time tables"]
  end

  sched -.-> drive
  drive --> queue
  queue --> w1
  queue --> w2
  w1 --> c1
  w2 --> c2
  w1 -. "reads" .-> input
  w1 -. "reads final slots below its own" .-> env
  w1 -- "outcome and candidate record" --> pub
  pub -- "ok only, then marks the slot final" --> env

  classDef planned stroke-dasharray: 6 4
  class sched,pub,input,env planned
```

Rules that already hold in code: a context is idle or owned by exactly one
job; a task may select only a context it owns; a job may not submit, wait
for, make or free contexts or jobs; `job-wait` gives 0 only when the word
returned with a balanced stack, and 0 never means a check was accepted;
nothing may `ALLOT` or compile while jobs run. Measured on the 12-thread
development machine, twelve workers ran twelve test jobs about 5.7–6.3
times faster than one task ([library inventory](FORTH_LIBRARY.md)). Each
context holds a full copy of every module's stores, so memory grows with
the number of workers ([scale assessment](../project/SCALE_ASSESSMENT.md)).

## Principal records

All state lives in records defined with `BEGIN-STRUCTURE` and named fields.
Record layouts are host-specific (cell size, alignment) and are never
written to files; identities and indices, not addresses, cross module
boundaries.

```mermaid
classDiagram
  class StoreHeader {
    store-capacity
    store-width
    store-base
    store-seal
    store-count
    store-generation
    store-serial
  }
  class Identities {
    one identity per record
    never repeats, never rewinds
  }
  class Node {
    node-tag
    node-first
    node-second
  }
  class NameEntry {
    lf-entry-tag
    lf-entry-prefix
    lf-entry-payload
    lf-entry-length
  }
  class ConstantReference {
    lf-crec-identity
    lf-crec-name
    lf-crec-generation
    lf-crec-arity
    lf-crec-levels: 8 level handles
  }
  class WalkHeader {
    walk-fuel
    walk-node
    walk-context
    walk-arg
    walk-pending
    walk-capacity
    walk-width
  }
  class Frames {
    frame-fuel
    frame-depth
    frame-limit
    frame-visitor
    frame-context
    frame-job
  }
  class ContextHeader {
    context-size
    context-owner
    then each member's data
  }
  class ContextLayout {
    layout-bytes
    layout-first
    layout-last
    layout-main
    layout-sealed
  }
  class Member {
    member-offset
    member-init
    member-link
    member-capacity
    member-width
    member-base
    member-xt
  }
  class Job {
    job-xt
    job-context
    job-done
    job-ior
  }
  class Export {
    export-reader
    export-json
    export-record
    export-handlers
    export-names, export-levels
    export-exprs, export-decls
  }
  StoreHeader *-- Identities : capacity cells
  StoreHeader *-- Node : lf-terms, lf-levels
  StoreHeader *-- NameEntry : lf-names
  StoreHeader *-- ConstantReference : lf-crefs
  Node --> Node : children are earlier indices
  ConstantReference --> NameEntry : name index and generation
  ContextLayout --> Member : layout-first, then member-link
  Member ..> ContextHeader : member-offset locates its data
  ContextLayout --> ContextHeader : layout-main
  Job --> ContextHeader : owns one context
  WalkHeader ..> Node : visits by index
  Frames ..> Node : visits by index
```

- **Stores** (`src/lib/store.fs`): a header, then one identity cell per
  record, then the records. `store-new` hands out the next index and a new
  identity; a reset (`store-clear`) advances the generation and invalidates
  every index; a spent serial or generation *poisons* the store so every
  check fails. A *handle* is an index with its identity, so a handle from
  before a reset or rollback no longer matches (`src/core/generation-handles.fs`).
- **Term and level nodes** (`src/lib/node.fs`): a tag and two fields.
  Terms (`src/core/terms.fs`): tag 1 concrete `Sort` (unused by the
  checker), 2 bound variable (de Bruijn index), 3 application (function,
  argument), 4 λ and 5 Π (domain, body), 6 symbolic `Sort` (level index,
  `src/core/tagged-sort-boundary.fs`) and 7 constant (reference index and
  identity, `src/core/constant-term-boundary.fs`). Levels
  (`src/core/levels.fs`): 0 zero (always record 0), 1 successor, 2 max,
  3 imax, 4 parameter (an opaque positive identifier).
- **Names** (`src/core/names.fs`): a prefix name and a string or number
  component; equal names are stored once, string bytes in a 2,048-byte pool.
- **Walk and frames records** (`src/lib/walk.fs`, `src/lib/frame.fs`): the
  fuel, the current node and a bounded work stack of one walk; or the fuel,
  depth limit and visitor of a bounded recursive pass. Running out of fuel
  gives *exhausted*, out of room *full*.
- **Contexts** (`src/lib/context.fs`): a header (size, owner) followed by
  the data of every declared member at its offset. The member records
  themselves live in the dictionary, linked from `context-layout`, which
  also points at the main context and is sealed by the first
  `context-new`.
- **Export record** (`src/import/ndjson.fs`): the line reader, the JSON
  view, the decoded record handed to handlers, the handler table and the
  counters of one reader.

One term as it is stored — the polymorphic identity of
[Concepts](../user/CONCEPTS.md#term), $\lambda (A : \mathrm{Sort}\ u)\ (x : A).\ x$
of type $\Pi (A : \mathrm{Sort}\ u),\ A \to A$. Indices are the term-store
indices that example prints; node 1 is shared.

```mermaid
flowchart TD
  n4["4: Π"] -- domain --> n0["0: Sort, level 1"]
  n4 -- body --> n3["3: Π"]
  n3 -- domain --> n1["1: bound variable 0"]
  n3 -- body --> n2["2: bound variable 1"]
  n6["6: λ"] -- domain --> n0
  n6 -- body --> n5["5: λ"]
  n5 -- domain --> n1
  n5 -- body --> n1
  n0 -- level --> l1["level 1: parameter u"]
```

## Data planned at Mathlib scale

The pinned Mathlib export has 105,894,257 expression nodes, 4,241,558 names
and up to 30 universe arguments per constant, against 64-entry stores and 8
level arguments today. The [scale assessment](../project/SCALE_ASSESSMENT.md)
lists the changes: heap-allocated and growable stores, hash-consing of
names, levels and terms, variable-length argument lists, explicit stacks
instead of host recursion in the rebuild passes, and per-declaration
scratch released after each check (plan tasks 6.2.0–6.2.3).
