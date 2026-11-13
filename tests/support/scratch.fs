\ Scratch file names for the tests that write files: in the folder that
\ LF_TEST_SCRATCH names, else in /tmp (a test run by hand). The Makefile
\ runs each such test through scripts/with-scratch.sh, which makes a new
\ folder for the command (mktemp -d) and removes it afterwards, and
\ scripts/mutants.py gives its run one of its own, so the same test run at
\ the same moment elsewhere (another worktree, another make) never writes
\ the same files (a push failed so on Gforth 0.7.3, 2026-11-12).
\ Gforth 0.7.3 and 1.0 (getenv). Test-only. Include it before
\ heap-watch.fs, so that its names are not counted as the module's blocks.
\
\ scratch-file ( c-addr u -- c-addr' u' ): the file name c-addr u (no
\ folder) in that folder, as a new heap string, never freed (tests are
\ short); make the names once, at load time.

\ The folder: LF_TEST_SCRATCH, or /tmp when it is unset or empty.
: scratch-folder ( -- c-addr u )
  s" LF_TEST_SCRATCH" getenv dup 0= if 2drop s" /tmp" then ;
\ c-addr u copied to addr; the address after the copy.
: scratch-put ( addr c-addr u -- addr' ) rot 2dup + >r swap move r> ;
\ The length of a name of u characters in the folder: folder, "/", name.
: scratch-length ( u -- u' ) scratch-folder nip + 1+ ;
: scratch-file ( c-addr u -- c-addr' u' )
  dup scratch-length dup >r allocate throw dup scratch-folder scratch-put
  [char] / over c! 1+ 2swap scratch-put drop r> ;
