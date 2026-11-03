\ Checker modules keep no state in the dictionary (review M2 of the
\ context conversion, ADR 0009): the data space laid down while the
\ library, the job pool and the modules loaded, from dict-start to
\ dict-end (constants the test file defines around its REQUIREs), must be
\ unchanged, byte for byte, after real checker work in contexts. A
\ VARIABLE or CREATEd buffer that a checker word writes, even one used
\ only as a register within one call, changes a byte, and so does a member
\ left global; a context member never does, since contexts are ALLOCATEd.
\ The work: a 2,000-step trial (checker-trial.fs) in one new context, and
\ in another, which holds the world and input of env-cases.fs and an
\ environment made over it beforehand, a serial run of the synthetic
\ checks with every publication. Allowed by name is the one record that
\ shared state only the publishing task writes, outside jobs: the
\ environment registry lf-envs (environment.fs); the environments
\ themselves, with the publisher's pool mark, are on the heap. The layout is
\ sealed before the copy is taken, since the first context-new sets its
\ flag once. Include after checker-trial.fs and env-cases.fs. Test-only.

dict-end dict-start - constant dict-bytes
dict-bytes allocate throw constant dict-copy
variable dict-trial    \ the trial's context
variable dict-lane     \ the environment run's context

\ The two contexts, the environment, the sealed layout, then the copy.
: dict-lane-ready ( -- ) world-again main-input 8 fresh-env ;
: dict-prepare ( -- )
  context-new throw dict-trial !
  context-new throw dup dict-lane ! context-use dict-lane-ready context-main context-use ;
: dict-snap ( -- ) dict-start dict-copy dict-bytes move ;

\ The work; the environment run's outcome (ok when every declaration ran).
: dict-trial-run ( -- ) dict-trial @ context-use 3 2000 0 trial-start trial-run ;
: dict-env-run ( -- outcome ) dict-lane @ context-use ['] syn-check ['] main-maker lf-env-run ;
: dict-work ( -- outcome ) dict-trial-run dict-env-run context-main context-use ;

\ Bytes that differ from the copy, outside the allowed record.
: dict-shared? ( addr -- flag ) lf-envs dup /lf-envs + within ;
: dict-changed? ( i -- flag )
  dup dict-start + dup dict-shared? if 2drop false exit then c@ swap dict-copy + c@ <> ;
: dict-changes ( -- n ) 0 dict-bytes 0 ?do i dict-changed? - loop ;
\ The first changed address, or 0, to find the module that wrote it.
: dict-first ( -- addr|0 )
  dict-bytes 0 ?do i dict-changed? if dict-start i + unloop exit then loop 0 ;

\ Free the environment and both contexts.
: dict-finish ( -- )
  dict-lane @ context-use env-free context-main context-use
  dict-lane @ context-free throw dict-trial @ context-free throw ;
