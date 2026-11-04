\ Does SEARCH-WORDLIST give RECURSE the same xt every time?
: x ( -- xt ) s" recurse" forth-wordlist search-wordlist . ;
x . x . cr
s" recurse" forth-wordlist search-wordlist . . cr
s" recurse" forth-wordlist search-wordlist . . cr
s" does>" forth-wordlist search-wordlist . . cr
s" does>" forth-wordlist search-wordlist . . cr
bye
