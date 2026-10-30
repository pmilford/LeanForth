\ Bootstrap host smoke-test word; this is not a verified LeanForth program.
\ Double a host cell using Gforth arithmetic; no overflow contract is provided.
: lf-double ( n -- 2n ) dup + ;
