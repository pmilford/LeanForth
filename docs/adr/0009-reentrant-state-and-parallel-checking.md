# ADR 0009: re-entrant state and parallel checking — proposal

Status: **proposed**, 2026-11-02. Shapes the code structure of untrusted,
in-progress modules; changes no typing or conversion rule. It answers roadmap
item C1 in part and sets the direction for C2.

## Problem

Checking a large development is mostly independent work: once the
declarations a theorem depends on are checked, many theorem bodies can be
checked at the same time. Lean's own build checks files in parallel the same
way. The owner expects complex theorems with many sub-theorems and
substantial Mathlib use, and wants the 12-core development machine used in
parallel.

Today almost every mutable cell is a global: 337 `VARIABLE`s, 73 `CREATE`d
tables, and 7 tables made by the library's defining words
(`make forth-metrics`, 2026-11-02). Many are used as registers between
words. Two kernel modules even borrow another module's scratch work stack.
Nothing can run twice at once in one Forth image.

## Facts measured (2026-11-02, this machine: 12 logical cores, WSL2)

- Gforth 1.0 has a native multitasker built on POSIX threads (`newtask4`,
  `execute-task`, `pass`, `semaphore`, `lock`/`unlock`) and per-task
  `USER` variables. Twelve CPU-bound tasks finished in 0.31 s against about
  1.8 s for the same work in sequence, using 1118% CPU: about 6×, which is
  consistent with 6 physical cores with two hardware threads each.
- Gforth 0.7.3 (the CI portability host) has only the cooperative
  multitasker. Forth-2012 standardizes no multitasking at all.

## Decision (proposed)

1. **All per-check state lives in records, passed by address.** No word may
   keep state for one check in a global. Long-lived stores are records made
   by defining words (`store:`); each walk's stack, fuel and current node is
   a walk record (`walk:`). Scratch borrowed across modules is replaced by
   each module's own record. The metrics script counts every such table as
   a global, so progress stays measurable.
2. **One checker context per worker.** A check's records (term, level and
   name stores, walk records, session) are grouped into one context record.
   Module words reach their state through a single current-context pointer,
   so their stack effects stay short. On Gforth 1.0 that pointer is a `USER`
   variable, giving each native task its own context; elsewhere it is an
   ordinary variable and there is one worker per process.
3. **The checked environment is append-only, then read-only.** A declaration
   joins the shared environment only after it is checked, and is never
   modified afterwards. Workers read it without locks. A scheduler hands out
   declarations whose dependencies are all checked, and publishes results in
   dependency order. No worker can see another worker's partial results,
   scratch or assumptions (roadmap C2).
4. **Two ways to run in parallel, the portable one first.**
   - *Processes:* several Gforth processes, each with one context, loading a
     serialized checked environment. Portable to every host, with crash
     isolation, but it needs a serialization format and per-process loading.
     This is the baseline and what CI can test.
   - *Native tasks:* Gforth 1.0 pthread tasks in one image, sharing one
     copy of the environment, each with its own context through its `USER`
     pointer. Less memory and fast start-up; an optimization, enabled only
     when the host provides the multitasker, and validated against serial
     runs (roadmap C3).
5. **Parallelism never bypasses checking.** A result checked in parallel
   must equal the serial result; tests compare them.

## Order of work

1. Done: `store:` and `walk:` records; the term, level and name stores and
   the four lowest walkers converted (roadmap Q10).
2. Convert the remaining modules' registers and borrowed stacks to records
   during the refactor.
3. Introduce the context record and current-context pointer, with a test
   that runs two contexts interleaved in one image and compares with serial
   runs.
4. Serialization of the checked environment (needed by processes), then a
   dependency-ordered scheduler, then native tasks.

## Rejected alternatives

- **Pass a context on the stack to every word.** Most transparent and
  portable, but it adds a stack item to nearly every word, against the style
  guide's limit of about three inputs. A single current-context pointer
  gives the same isolation.
- **Locks around shared mutable stores.** Serializes the hot paths and
  invites races; an append-only environment and per-worker scratch need no
  locks on the read path.
- **Native tasks only.** Not available on Gforth 0.7.3 or in Forth-2012,
  and gives no crash isolation.
- **Processes only.** Each process holds its own copy of the environment,
  which at Mathlib scale may be the limiting memory cost; the scale
  assessment under way will size this.
