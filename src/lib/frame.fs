\ Bounded recursion for passes that visit a DAG node by node on the host
\ stacks. A frames record holds the fuel left, the number of visits in
\ progress (frames) and their limit, the visitor, a context cell for the
\ visit in progress (such as the number of binders around its node), and a
\ job cell for the pass's own use, 0 unless it sets one. A record stands
\ alone (frames:) or is a field of a larger record (frame-init). A pass
\ whose record is a member of a checker context (lib/context.fs) must not
\ keep an address in the job cell, since the address of a context member
\ goes stale when the main context moves while modules load: it embeds
\ the frames first in its own record, so the visitor finds the pass's
\ inputs at the frames address it is given (mixed-shift.fs). Every word
\ here takes the record's address, so separate records are independent
\ and this module has no state.
\
\ frame-call spends one unit of fuel and one frame, calls the visitor
\ ( x frames -- result outcome ) on x and releases the frame; frame-call2
\ does the same for a visitor of two values ( x y frames -- outcome ), such
\ as a comparison. They visit nothing when no fuel is left (exhausted) or
\ when every frame is in use (full); with neither, the fuel decides:
\ exhausted. A record whose limit is below 1 (frame-init never makes one)
\ is corrupted, which is invalid. On any failure frame-call also gives -1,
\ no result. The visitor visits a child by calling frame-call, frame-call2
\ or frame-under (one context level deeper; a context at max-n cannot grow,
\ which is full, and again the fuel decides first) on the record it was
\ given, so a node shared by several parents is visited, and charged, once
\ per path. A visitor result outside the outcome vocabulary counts as
\ invalid. The fuel-first rule covers only the admission of a visit here: a
\ limit that a visitor checks itself, inside a visit already paid for (such
\ as mixed-rebuild.fs's binder check), is independent of fuel (ADR 0008).
\
\ A record is busy while a visit is in progress. A busy record refuses a
\ new budget and a new pass, so a pass cannot be restarted from inside
\ itself. A THROW out of a visit (such as a host stack overflow) leaves the
\ record busy and its context changed: the code that catches it must
\ discard whatever the pass changed and call frame-reset.
\
\ Host stacks: values a visitor keeps across a child's visit stay on the
\ data stack, and every nested visit also holds a few return-stack cells.
\ The limit bounds the nesting of one record only; a module whose passes
\ nest checks at load time that the host's stacks hold all of them (see
\ mixed-beta.fs).

require ./outcome.fs
require ./portability.fs

begin-structure /frames
  field: frame-fuel      \ visits left
  field: frame-depth     \ visits in progress
  field: frame-limit     \ most visits in progress at once
  field: frame-visitor   \ xt ( x frames -- result outcome ) or ( x y frames -- outcome )
  field: frame-context   \ context of the visit in progress
  field: frame-job       \ for the pass; never a context member's address
end-structure

\ Initialise a record in place: idle, no fuel, no job, allowing limit
\ nested visits of the visitor xt, which is set once here. A limit below 1
\ aborts. frames: defines a standalone record, name ( -- frames ).
: frame-init ( limit xt frames -- )
  rot dup 0> 0= abort" frames: bad limit"
  over /frames erase over frame-limit ! frame-visitor ! ;
: frames: ( limit xt "name" -- ) create here /frames allot frame-init ;

\ Busy while a visit is in progress (or after a THROW out of one); a
\ corrupted depth also counts as busy. frame-reset makes a record idle.
: frame-busy? ( frames -- flag ) frame-depth @ 0<> ;
: frame-reset ( frames -- ) 0 swap frame-depth ! ;

\ Set the budget for a pass. A negative fuel or a busy record is refused
\ and stores nothing.
: frame-budget ( fuel frames -- flag )
  over 0< over frame-busy? or if 2drop false else frame-fuel ! true then ;

\ Visiting. A visit opens (ok) when the limit is sound, fuel is left and a
\ frame is free; otherwise the limit decides first (below 1 is invalid),
\ then the fuel (none left, or a corrupted negative fuel, is exhausted),
\ then the frames (all in use is full). Signed comparisons.
: frame-free? ( frames -- flag ) dup frame-depth @ swap frame-limit @ < ;
: frame-room ( frames -- outcome )
  dup frame-limit @ 0> 0= if drop outcome-invalid exit then
  dup frame-fuel @ swap frame-free? visit-outcome ;
: frame-enter ( frames -- ) -1 over frame-fuel +! 1 swap frame-depth +! ;
: frame-leave ( frames -- ) -1 swap frame-depth +! ;
\ frame-visit takes a frame the caller found open (frame-room gave ok) and
\ runs the visitor on the values below the record, any number of them.
\ frame-call does the same for one value with the record kept on the data
\ stack instead: the passes recurse through frame-call, and every word and
\ return-stack cell between a visitor and its child's visit is held once
\ per nested frame.
: frame-visit ( i*x frames -- j*x outcome )
  dup frame-enter dup >r dup frame-visitor @ execute outcome-sane r> frame-leave ;
: frame-call ( x frames -- result outcome )
  dup frame-room ok-then? 0= if nip no-result exit then
  dup frame-enter tuck dup frame-visitor @ execute outcome-sane rot frame-leave ;
: frame-call2 ( x y frames -- outcome )
  dup frame-room ok-then? if frame-visit else nip nip then ;

\ One context level deeper, restored afterwards. The visit must open
\ (frame-room, so the fuel decides before the context), and then a context
\ that cannot grow (max-n) is full; a refused visit changes nothing.
: frame-context+! ( n frames -- ) frame-context +! ;
: frame-deeper ( frames -- outcome )
  dup frame-room ok-then? if frame-context @ max-n <> room>outcome then ;
: frame-under ( x frames -- result outcome )
  dup frame-deeper ok-then? 0= if nip no-result exit then
  1 over frame-context+! tuck frame-call rot -1 swap frame-context+! ;

\ A pass: an idle record takes the root's context, then the root is
\ visited. A busy record refuses, changing nothing: no result, invalid.
: frame-start ( context frames -- flag )
  dup frame-busy? if 2drop false else frame-context ! true then ;
: frame-run ( x context frames -- result outcome )
  tuck frame-start if frame-call else 2drop -1 outcome-invalid then ;
