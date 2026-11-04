\ tests/lib/sha256.fs with the plain FIPS 180-4 definitions of the round
\ and the message schedule, which hosts with cells narrower than 64 bits
\ always use: defining sha256-portable before the library loads selects
\ them on every host.
: sha256-portable ( -- ) ;
include ./sha256.fs
