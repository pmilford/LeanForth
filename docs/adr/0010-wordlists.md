# ADR 0010: wordlists and module boundaries — proposal

Status: **accepted** by the owner on 2026-11-03, with decisions 1–3 of "What the owner must decide" as recommended
([OWNER_DECISIONS.md](../project/OWNER_DECISIONS.md#gate-answers-and-working-guidelines-2026-11-03)).
Previously: **proposed**, 2026-11-02 (plan task 1.1.7, plan
[§6.9](../project/PLAN_DRAFT.md#69-wordlists-and-namespaces)). A
code-structure decision for untrusted, in-progress modules: it changes no
typing or conversion rule and no stack effect. Nothing here is
implemented; the pilot below ran on a scratch copy of the tree. The
handoff's provisional names (`LF.CORE`, `LF.KERNEL`, …) are replaced by
the ones below; the style guide's section 7 asked for this ADR.

## Summary in plain words

Every LeanForth word lives today in one big list of names, Forth's
FORTH-WORDLIST, so any code loaded afterwards can call any word, including
internal helpers that change shared state. Forth can keep several lists
(*wordlists*) and choose which ones it searches. This record proposes one
public and one private list per part of the program: the public list holds
the words other parts and the documentation use; the private list holds
the helpers, which other parts cannot name by accident. Tests that need a
helper say so in one line. This tidies the code and catches mistakes; it
is not a security wall, because Forth code in the same program can still
read and write any memory. Untrusted code therefore keeps running in a
separate program (open question OQ-1).

## Facts measured (2026-11-02, Gforth 0.7.3 and 1.0.0)

- **Search-order depth.** Both hosts start with three entries (FORTH,
  FORTH, Root). Gforth 0.7.3 accepts at most 1,024 entries and throws −49
  (search-order overflow) on the next. Gforth 1.0 has no fixed limit: the
  probe stopped at 4,087 entries, when `GET-ORDER` itself overflowed the
  data stack (−3). Forth-2012 guarantees at least eight.
- **Case.** Wordlists made by `WORDLIST` ignore ASCII case on both hosts:
  `SEARCH-WORDLIST` finds `MixedCase` given `MIXEDCASE`, and so does the
  text interpreter. A hidden name stays hidden in every spelling.
- **Redefinitions.** Both hosts print "redefined" only when a name is
  defined again in the *current* compilation wordlist. A name defined in
  another wordlist — even `DUP`, or a word another module defines — prints
  nothing, whether or not that wordlist is searched.
- **Saving the compilation wordlist on the data stack** across colon
  definitions, `BEGIN-STRUCTURE … END-STRUCTURE`, `CREATE`, `CONSTANT` and
  `VARIABLE` works on both hosts, as `tests/support/heap-watch.fs` already
  does for its own wordlist.
- **Optional words.** `SYNONYM` and `TRAVERSE-WORDLIST` exist on Gforth
  1.0, not on 0.7.3 (`tests/program/ir-reader.fs` has a 0.7.3 fallback for
  the second, on Gforth's internals).
- **Who uses which words** (names defined at the top level of each
  folder's files, compared case-insensitively with every token of `src/`,
  `tests/`, the documentation's code blocks and `scripts/`; each name is
  counted in the first column that applies):

  | Group | Names | Used by another group's source | Else named in docs code or scripts | Else used by tests | Else by other files of the group | Else only in its own file |
  | --- | --- | --- | --- | --- | --- | --- |
  | `lib/` | 638 | 150 | 28 | 107 | 3 | 350 |
  | `core/` | 479 | 147 | 31 | 96 | 4 | 201 |
  | `kernel/` | 827 | 0 | 30 | 137 | 47 | 613 |
  | `import/` | 392 | 1 | 30 | 104 | 3 | 254 |
  | `program/` | 643 | 0 | 8 | 79 | 0 | 556 |
  | `present/` | 437 | 0 | 14 | 30 | 72 | 321 |

  The docs column is mostly record fields drawn in the architecture
  diagrams and defining words the metrics script lists.

  No other group's source uses a kernel word (`main.fs` only loads the
  kernel), so the kernel's public interface is what its documentation
  describes and its tests and the coming command line use.

## Decision (proposed)

1. **Wordlists.** One file, `src/lib/module.fs`, makes every project
   wordlist once (guarded, so a second `REQUIRE` changes nothing) and
   defines four words, all in FORTH-WORDLIST, the one list every search
   order holds:

   | Wordlist | Holds |
   | --- | --- |
   | `lf-lib`, `lf-lib-private` | `src/lib/` |
   | `lf-core`, `lf-core-private` | `src/core/` |
   | `lf-kernel`, `lf-kernel-private` | `src/kernel/` |
   | `lf-env-private` | the checked environment's internals (`environment.fs`, `env-publish.fs`), hidden from the other kernel modules too |
   | `lf-import`, `lf-import-private` | `src/import/` |
   | `lf-program`, `lf-program-private` | `src/program/` |
   | `lf-present`, `lf-present-private` | `src/present/` |

   ```forth
   : order+ ( wid -- ) >r get-order r> swap 1+ set-order ;
   : order- ( -- ) get-order nip 1- set-order ;
   : module-open ( private -- previous ) dup order+ get-current swap set-current ;
   : module-close ( previous -- ) set-current order- ;
   ```

   Only Forth-2012 Search-Order words: `WORDLIST`, `GET-ORDER`,
   `SET-ORDER`, `GET-CURRENT`, `SET-CURRENT`, and `SEARCH-WORDLIST` in the
   checks. `DEFINITIONS` is not enough on its own: it can only make the
   top of the search order the compilation wordlist, and cannot give the
   caller's back.

2. **A module's shape.** After its header and `require`s:

   ```forth
   lf-kernel-private module-open    \ helpers by default
   : helper ( -- ) … ;
   lf-kernel set-current
   : lf-public-word ( -- ) … helper … ;
   lf-kernel-private set-current
   …
   module-close
   ```

   The previous compilation wordlist waits on the data stack between
   `module-open` and `module-close`, so nested loading balances, and
   `make smoke` still sees an empty stack after every module. A file that
   keeps `BASE` on the stack (`bytes.fs`, `json.fs`) opens after saving it
   and closes before restoring it. A host library loaded in the middle of
   a module (`tasker.fs` in `task.fs`) is loaded with FORTH-WORDLIST
   current.

3. **What is public.** A word is public when another group's source uses
   it or its module's header or the user and programming documentation
   names it as the interface; everything else, field names included, is
   private. A group's public wordlist is pushed onto the search order once,
   when the group's first module loads (for the library, by `module.fs`),
   and stays there, so loading a group makes its interface visible to
   everything loaded afterwards, as today. A private wordlist is searched
   only between `module-open` and `module-close` of its own modules, and
   by tests that ask (decision 6).

4. **`require` and each module requiring its dependencies.** Unchanged
   and still sufficient. `REQUIRE` loads a file once, whatever the search
   order; each module sets and restores its own compilation wordlist, so
   it does not matter which module loads it first. The `require`s come
   before `module-open`, so a dependency loads with its includer's
   wordlist current and replaces it itself. Requiring a group makes its
   public words visible (decision 3). A module that uses a word of a group
   it did not require still fails `make smoke` when it loads on its own.
   Guards with `[DEFINED]` and `[UNDEFINED]` name only words that stay in
   FORTH-WORDLIST or the host's words (`lf-lib-loaded`, `task-serial-only`,
   `lf-env-fault-hooks`, `udp`): a guard on a word that moved into a
   private wordlist would silently take the other branch outside its
   module.

5. **`make smoke`.** It still loads `src/main.fs` and every module on its
   own and requires silence (the pilot shows it). What it loses is the
   "redefined" warning between modules, since every module now defines
   into wordlists of its own (see *Redefinitions* above): two modules
   could each define a word of the same name, or a helper could shadow a
   host word such as `WITHIN` for every module of its group, and nothing
   would print. `make smoke` therefore gains a **duplicate-name check**:
   after loading `src/main.fs` and `task.fs`, no name may be in two
   project wordlists, or in a project wordlist and FORTH-WORDLIST (the
   host's words and any project words not yet moved). It traverses the
   wordlists with `TRAVERSE-WORDLIST` on Gforth 1.0 and with the IR reader
   test's fallback on 0.7.3. Tests are not loaded by `make smoke`, so a
   static scan (the tokenizer `scripts/forth-metrics.py` already has)
   compares each test file's own definitions with the private names.

6. **Tests and internals.** A test that needs helpers says so after its
   `require`s, for example `lf-lib-private order+`; the private list then
   comes before FORTH-WORDLIST in its search order. That line is the only
   way in, so reaching internals is explicit and easy to find. A check
   refuses `order+` of a private wordlist in `src/` outside its group. A
   test word with the same name as a helper would now be hidden by the
   helper; the static scan of decision 5 reports it. (Two exist today and
   are harmless: `guards` in `tests/core/export-signature-stream.fs`, also
   a `task.fs` helper, and `context-claim` in
   `tests/core/mixed-infer-coverage.fs`, also in `context.fs`.)

7. **Per-task contexts.** Unaffected. A context member's name is a colon
   definition that `context-record:` and its siblings compile into the
   declaring module's *current* wordlist (`lib/context.fs`), so a member
   is public or private like any other word: `lf-terms`, which every
   module uses, is public; `lf-mls-walker`, which only the hand-kept list
   in `tests/core/contexts.fs` names, stays private and that test asks for
   it. Offsets and the context layout do not depend on wordlists, and a
   member's body refers to `lf-context` by execution token, found when
   `context.fs` was compiled. Jobs never compile or interpret text (ADR
   0009), so the search order matters only while the program loads.

8. **Depth.** Fully adopted, the search order holds the host's 3 entries,
   the 6 public lists and, while a module loads, its private list (two
   for the environment's files): at most 11, and 12 in a test that also
   asks for helpers. Gforth 0.7.3 allows 1,024 and 1.0 has no limit;
   Forth-2012 guarantees only 8. On such a host, `module.fs` can make the
   six public names one wordlist, and the private names another, without
   changing any module.

9. **What wordlists protect, and what not.** They stop code compiled later
   — another group, the NDJSON reader, the program reader, a test, a user
   at the prompt — from *naming* a helper by accident, in any spelling;
   and with the duplicate-name check they stop collisions between modules.
   They do not protect memory or execution: any Forth code in the same
   program can push any wordlist (its constant is in FORTH-WORDLIST),
   traverse every wordlist, run an execution token it has kept, or store
   into any address, such as a context member's (`lf-context @` plus an
   offset). So wordlists are a code-quality and review tool, not a trust
   boundary: where untrusted code — tactics, LLM output, user Forth
   programs — runs in the checker's program, its results cannot be
   trusted. (This sentence first said such code must not run there, the
   owner's OQ-1 answer of 2026-11-02. Since ADR 0017 Amendment 1, accepted
   2026-11-04, it may: such results are labelled *checked in this session*
   and become claims only when re-checked by `leanforth check` in a fresh
   process, where only LeanForth's code and sealed text run.)

10. **Worked example: the publisher.** `src/kernel/env-publish.fs` defines
    63 names. Its interface is four words, `lf-env-hand-over`,
    `lf-env-step`, `lf-env-run` and `lf-env-thrown` (with the test-only
    `lf-env-before-final` hook); 55 names are used only inside the file,
    among them `lf-env-unpublish`, and `lf-env-guarded` is used outside it
    only by one white-box test. The review of the environment asked for
    these two to be hidden. Today any code loaded later can call them:
    - `lf-env-guarded ( slot -- outcome fault? )` publishes the candidate
      into the slot it is given, skipping `lf-env-hand-over`'s refusal
      inside a job (G-P1) and its choice of slot;
    - `lf-env-unpublish ( slot ior -- )` rolls the publisher's pool back
      to its last mark. Called after a successful publication, it gives
      back the pool entries that publication appended, so the next one
      overwrites the dependency list of an accepted declaration.

    Under this ADR both files open `lf-env-private`, and only the
    documented interface (the 18 `lf-env-` words of
    `docs/programming/CHECKED_ENVIRONMENT.md`) goes to `lf-kernel`. The one
    white-box test of `lf-env-guarded` (`tests/core/environment.fs`) adds
    `lf-env-private order+`; nothing else in `src/` could name either word.

## The pilot: `src/lib`

A scratch copy of `16bdc2f` with `src/lib/module.fs` (the four words of
decision 1, `lf-lib` and `lf-lib-private` only) and every library file
converted by a script: `lf-lib-private module-open` after the `require`s,
`module-close` at the end, and `lf-lib set-current` or `lf-lib-private
set-current` before each definition whose visibility differs from the one
before (and after every `[IF]`, `[ELSE]` or `[THEN]`). Public were the
words another group's source uses or the library notes or a header name;
the 20 test files that use any other library word got `lf-lib-private
order+`.

| Measure | Result |
| --- | --- |
| Names hidden | 432 of 638 (68%); 206 public. After `src/main.fs` loads: 171 words in `lf-lib`, 326 in `lf-lib-private` (`task.fs` is not loaded by `main.fs`) |
| Every test still passes? | Yes: every target of `make test` except the two that need a git checkout (`check-docs`, `check-lean-sources`), on Gforth 1.0 and 0.7.3, including `make smoke` (silent) and the dictionary check of `tests/core/contexts.fs` |
| Tests that reach library helpers | 20 of 125 test files, one line each |
| Lines added | `module.fs` 26 (10 of code); 3 per library file (33); 182 visibility switches, one per 3.5 definitions on average, in 1,901 library lines |
| Dictionary | +600 bytes (Gforth 1.0) and +584 (0.7.3) on the 474 KB and 480 KB that `src/main.fs` lays down |
| Load time of `src/main.fs` | median 42.9 → 43.7 ms (Gforth 1.0, 7 runs each), 50.7 → 53.2 ms (0.7.3, 5 runs): within the noise of the runs |
| Run time | unchanged: the compiled code is the same (100,000 level substitutions took 2,946–3,103 ms against 2,877–3,049 ms before) |
| Search order after `src/main.fs` | 4 entries (the host's 3 and `lf-lib`); 5 while a library module loads |
| Planted faults | a file outside the library that names `store-shape@`, or `STORE-SHAPE@`, fails to load ("Undefined word") on both hosts and loads after `lf-lib-private order+`; the duplicate-name check finds no clash in `lf-lib` and `lf-lib-private`, and reports a helper planted as `WITHIN`, which loaded without a warning |

Making every word a test uses public as well would need 167 switches, and
also making a record's fields public together 155: the alternation of
helpers and public words is how factored Forth reads, so the number
hardly depends on the policy.

## Migration order

Each step is one commit with `make test` on both hosts, `make check` and
the duplicate-name check, and changes no stack effect.

1. **The library** (plan 1.1.7): `module.fs`, the duplicate-name check in
   `make smoke`, the library files and the 20 tests' `order+` lines. The
   parallel refactor briefs forbid other agents to edit `src/lib/`, so
   nothing in flight touches it; the test lines are single insertions
   that merge cleanly.
2. **The checked environment** (`environment.fs`, `env-publish.fs`), the
   worked example: the highest value, two files, once no agent is working
   on them.
3. **The kernel's passes**, after the refactor groups touching them have
   merged.
4. **The data model** (`core/`).
5. **`import/`, `program/` and `present/`**, in any order; each is
   self-contained.

## Rejected alternatives

- **Export lists** (define every word privately, then `SYNONYM name name`
  into the public list at the end of the file). The public interface would
  be one reviewed list, and the default safe. Measured: on Gforth 1.0 a
  synonym keeps the execution token and works with `TO`, `IS` and `>BODY`,
  and a two-word adapter on 0.7.3's non-standard `ALIAS` and `NEXTNAME`
  does the same; but `SYNONYM` is outside the word set chosen for this
  design, Forth-2012 leaves `>BODY` and `TO` through a synonym ambiguous,
  and every public word gets a second header. Kept as the alternative if
  the switches prove hard to read.
- **One wordlist per module** (about 60). Strongest hiding, but most
  helpers shared within a group would need explicit exports between
  modules, and search orders would grow with every dependency. Used only
  where a module's internals write shared state (`lf-env-private`).
- **One public wordlist for all groups.** Fewer search-order entries, but
  no record of which group a word belongs to; kept as the fallback for a
  host with only eight entries (decision 8).
- **Tests putting private lists at the bottom of the search order**, so
  that a test's own words win. Inserting below the host's lists needs
  stack juggling of a variable depth; the duplicate-name check prevents
  the clash instead.
- **Keeping everything in FORTH-WORDLIST.** `make smoke` would keep
  catching collisions, but nothing would stop accidental use of words
  such as `lf-env-unpublish`.

## What the owner must decide

1. **Adopt the design** — a public and a private word list for each part
   of the program, helpers private, tests asking explicitly for helpers,
   and a new check that no name is defined twice. *Recommendation: yes.*
   The library pilot hid 68% of its names with every test passing on
   both Gforths, at no run-time cost and 2–5% more loading time; and
   it would hide the publisher's two dangerous internal words from
   everything outside the checked environment.
2. **How a file marks its public words**: a one-line switch before each
   group of public or private definitions (as piloted), or one list of
   public words at the end of each file. *Recommendation: the switches*,
   because they use only standard Forth and work on both Gforths as they
   are; they add about one line per three or four definitions.
3. **Order**: the library first, now, then the checked environment.
   *Recommendation: yes*; nobody else edits the library, and the
   environment is where hiding matters most.

## Reproduction

Gforth 1.0.0 and 0.7.3 (the CI hosts), 2026-11-02. The facts come from
small probes: pushing FORTH-WORDLIST with `GET-ORDER`/`SET-ORDER` under
`CATCH` until it throws; defining the same name in a second wordlist,
searched or not, and `DUP` in another wordlist, and watching for
"redefined"; `SEARCH-WORDLIST` and the interpreter with names in other
cases. The usage table counts names defined at the top level of each
folder (after `:`, `CONSTANT`, `VARIABLE`, `CREATE`, `VALUE`, `DEFER`,
`USER`, structure and field words and the project's defining words) and
compares them with the tokens of every other file, comments and strings
removed.
