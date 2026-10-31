\ Untrusted staging of decoded expression records into the experimental arena.
\ This is not an NDJSON parser, declaration checker, or theorem interface.
\ The caller resolves exported universe references to concrete levels and
\ supplies zero-based record indices and children relative to this batch.
\ The global transaction assumes no concurrent or external arena mutation.
include ../core/terms.fs

variable lf-load-start
variable lf-load-active

\ Begin a batch at the current arena count. An already open batch cannot be
\ replaced. Failure leaves the arena and any active batch unchanged.
: lf-load-begin ( -- flag )
  lf-load-active @ if false exit then
  lf-term-count-valid? 0= if false exit then
  lf-term-count @ lf-load-start ! true lf-load-active ! true ;

\ Abort a batch and discard its nodes. Existing indices before the batch remain
\ valid provided callers obey the no-external-mutation precondition.
: lf-load-abort ( -- )
  lf-load-active @ if lf-load-start @ lf-term-count ! then
  false lf-load-active ! ;

\ Finish staging without checking types. Returned indices remain mutable and
\ are invalid after an arena reset; success is not a proof judgment.
: lf-load-finish ( -- flag )
  lf-load-active @ 0= if false exit then
  false lf-load-active ! true ;

\ Decode one integer record into a batch-local node. Binary children must
\ refer to earlier nodes in this same batch; unused leaf fields must be zero.
\ Any malformed record or capacity failure aborts the entire active batch.
: lf-load-node ( index tag first second -- flag )
  lf-load-active @ 0= if 2drop 2drop false exit then
  lf-term-count-valid? 0= if 2drop 2drop lf-load-abort false exit then
  3 pick lf-term-count @ lf-load-start @ - <> if
    2drop 2drop lf-load-abort false exit
  then
  2 pick lf-tag-sort = 3 pick lf-tag-bvar = or if
    dup 0<> if 2drop 2drop lf-load-abort false exit then drop
    swap lf-tag-sort = if lf-term-sort else lf-term-bvar then
  else
    2dup 0< swap 0< or if 2drop 2drop lf-load-abort false exit then
    2dup lf-term-count @ lf-load-start @ - >= swap
         lf-term-count @ lf-load-start @ - >= or if
      2drop 2drop lf-load-abort false exit
    then
    lf-load-start @ + swap lf-load-start @ + swap
    rot lf-term-binary
  then
  if 2drop true else drop lf-load-abort false then ;

false lf-load-active !
