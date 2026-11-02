\ Untrusted staging of decoded expression records into the experimental
\ arena. This is not an NDJSON parser, declaration checker, or theorem
\ interface. The caller resolves exported universe references to concrete
\ levels and supplies zero-based record indices and children relative to
\ this batch.
\ State: one batch record, lf-load-batch: whether a batch is open and the
\ term count where it began. The transaction assumes no concurrent or
\ external arena mutation; single-threaded and not re-entrant.

require ../lib/lib.fs
require ../core/terms.fs

begin-structure /lf-batch
  field: lf-batch-open     \ true while a batch is open
  field: lf-batch-start    \ term count when the open batch began
end-structure
create lf-load-batch /lf-batch allot
lf-load-batch /lf-batch erase

: lf-load-open? ( -- flag ) lf-load-batch lf-batch-open @ ;
: lf-load-close ( -- ) false lf-load-batch lf-batch-open ! ;
: lf-load-base ( -- start ) lf-load-batch lf-batch-start @ ;
\ Records staged so far in the open batch: the next batch-local index.
: lf-load-staged ( -- n ) lf-term-count @ lf-load-base - ;

\ Begin a batch at the current arena count. An already open batch cannot be
\ replaced. Failure leaves the arena and any active batch unchanged.
: lf-load-start ( -- )
  lf-term-count @ lf-load-batch lf-batch-start ! true lf-load-batch lf-batch-open ! ;
: lf-load-begin ( -- flag )
  lf-load-open? lf-term-count-valid? 0= or if false else lf-load-start true then ;

\ Abort a batch and discard its nodes. Existing indices before the batch remain
\ valid provided callers obey the no-external-mutation precondition.
: lf-load-abort ( -- ) lf-load-open? if lf-load-base lf-term-count ! then lf-load-close ;

\ Finish staging without checking types. Returned indices remain mutable and
\ are invalid after an arena reset; success is not a proof judgment.
: lf-load-finish ( -- flag ) lf-load-open? if lf-load-close true else false then ;

\ Decoding one record. A Sort or bound-variable leaf keeps its payload and
\ must have a zero second field. Any other tag is staged as a binary node
\ whose children are earlier records of this batch; lf-term-binary refuses
\ a tag that is not binary.
: lf-load-leaf ( first second tag -- index true | false )
  swap 0<> if 2drop false else lf-term-leaf then ;
: lf-load-child? ( child -- flag ) dup 0< 0= swap lf-load-staged < and ;
: lf-load-children? ( first second -- flag ) lf-load-child? swap lf-load-child? and ;
: lf-load-rebase ( first second -- first' second' ) lf-load-base tuck + >r + r> ;
: lf-load-binary ( first second tag -- index true | false )
  >r 2dup lf-load-children? if lf-load-rebase r> lf-term-binary
  else 2drop r> drop false then ;
: lf-load-record ( first second tag -- index true | false )
  dup lf-term-leaf-tag? if lf-load-leaf else lf-load-binary then ;

\ A record must carry the next batch-local index of a valid arena.
: lf-load-next? ( index -- flag ) lf-load-staged = lf-term-count-valid? and ;
: lf-load-fail ( x1 x2 -- false ) 2drop lf-load-abort false ;
: lf-load-reject ( first second tag -- false ) drop lf-load-fail ;
: lf-load-stage ( first second tag -- flag )
  lf-load-record if drop true else lf-load-abort false then ;
: lf-load-checked ( index tag first second -- flag )
  2swap swap lf-load-next? if lf-load-stage else lf-load-reject then ;

\ Decode one integer record into a batch-local node. Binary children must
\ refer to earlier nodes in this same batch; unused leaf fields must be zero.
\ Any malformed record or capacity failure aborts the entire active batch;
\ without an open batch the record is refused and nothing changes.
: lf-load-node ( index tag first second -- flag )
  lf-load-open? if lf-load-checked else 2drop 2drop false then ;
