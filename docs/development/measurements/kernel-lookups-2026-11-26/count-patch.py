#!/usr/bin/env python3
"""Counting patch for the kernel-lookups design (applied to a scratch export of
the instantiation prototype, edcb539 = P1-P4; never merged).
usage: count-patch.py ROOT"""
import sys, pathlib, re
root = pathlib.Path(sys.argv[1]).resolve()
C = root / "src/lib/lookups-probe.fs"
counters = """c-pass c-visit c-rm@ c-rm-hit c-seen2 c-hit-in c-hit-cross c-hit-otheroff
c-hit-stamped c-rm-stamped c-rm-intier c-hit-intier c-rm-unsh c-hit-unsh c-hit-unsh-in c-rm! c-oob
c-cons c-cons-open c-cons-mls c-tin-sought c-tin-hit c-store-hit c-new c-forget
c-fc1-hit c-fc1-same c-fc2-hit c-fc2-same
c-rd-in c-rd-st c-dw-in c-dw-st c-tin-dec
c-mls c-mls-sort c-mls-image c-mls-binary""".split()
src = "require ./hash32.fs\nget-current forth-wordlist set-current\n"
src += "".join(f"variable {n}  0 {n} !\n" for n in counters)
src += r"""
variable pass-ser 0 pass-ser !   variable in-open 0 in-open !   variable in-mls 0 in-mls !
variable cur-stamped 0 cur-stamped !   variable kn   variable ko   variable kseen
1 24 lshift constant maxn
maxn 4 * allocate throw constant st-tab  st-tab maxn 4 * erase
maxn 4 * allocate throw constant of-tab
maxn allocate throw constant pp-tab  pp-tab maxn erase
: in-range? ( n -- flag ) maxn u< ;
\ seen in this pass (marks it, with its offset, on first sight)
: seen-mark ( node off -- flag )
  over in-range? 0= if 2drop 1 c-oob +! false exit then
  over 4 * st-tab + ul@ pass-ser @ = if 2drop true exit then
  over 4 * of-tab + l!  4 * st-tab + pass-ser @ swap l! false ;
\ parents: 0 none, 1 one, 2 two or more (set when a new node takes a child)
: pp-take ( child -- ) dup in-range? 0= if drop exit then
  pp-tab + dup c@ 1+ 2 min swap c! ;
: pp-shared? ( node -- flag ) dup in-range? 0= if drop true exit then pp-tab + c@ 2 = ;
\ direct-mapped front caches of the last conses: tag first second index+1
create fc1 1024 4 * cells allot  fc1 1024 4 * cells erase
create fc2 65536 4 * cells allot  fc2 65536 4 * cells erase
variable fc-h  variable fc1-hit  variable fc2-hit
: fc-slot ( mask tab -- a ) swap fc-h @ and 4 * cells + ;
: fc-eq? ( t f s a -- t f s flag )
  >r r@ 3 cells + @ 0<> 3 pick r@ @ = and 2 pick r@ cell+ @ = and over r> 2 cells + @ = and ;
: fc-look ( t f s -- t f s )
  2 pick 2 pick 2 pick hash-3 fc-h !
  1023 fc1 fc-slot fc-eq? fc1-hit !  65535 fc2 fc-slot fc-eq? fc2-hit ! ;
: fc-store ( t f s index a -- ) >r 1+ r@ 3 cells + ! r@ 2 cells + ! r@ cell+ ! r> ! ;
: fc-note ( t f s index -- )
  fc1-hit @ if 1 c-fc1-hit +! dup 1+ 1023 fc1 fc-slot 3 cells + @ = if 1 c-fc1-same +! then then
  fc2-hit @ if 1 c-fc2-hit +! dup 1+ 65535 fc2 fc-slot 3 cells + @ = if 1 c-fc2-same +! then then
  2over 2over 1023 fc1 fc-slot fc-store 65535 fc2 fc-slot fc-store ;
create ch-tab 32 cells allot  ch-tab 32 cells erase
: .ch ( -- ) 8 0 do ." cache " i . ch-tab i 4 * cells + dup @ . dup cell+ @ . dup 2 cells + @ . drop cr loop ;
: .counters ( -- ) cr
"""
src += "".join(f'  ." {n} " {n} @ . cr\n' for n in counters)
src += "  .ch ;\nset-current\n"
C.write_text(src)

def edit(rel, fn):
    p = root / rel; t = p.read_text(); t2 = fn(t)
    assert t2 != t, rel
    if f"require {C}" not in t2: t2 = f"require {C}\n" + t2
    p.write_text(t2)

def wrap(rel, word, body):
    """Rename word to word0 and define word after its definition as body."""
    def fn(t):
        m = re.search(r"^: " + re.escape(word) + r"(?=\s)", t, re.M)
        assert m, word
        t = t[:m.start()] + ": " + word + "0" + t[m.end():]
        i = t.index("\n", m.start()) + 1
        while i < len(t) and t[i] in " \t":
            i = t.index("\n", i) + 1
        return t[:i] + f": {word} {body} ;\n" + t[i:]
    edit(rel, fn)

T = "src/core/terms.fs"; O = "src/kernel/mixed-open.fs"; K = "src/kernel/caches.fs"
M = "src/kernel/mixed-level-substitute.fs"
# reads
for w in ("lf-term-tag@", "lf-term-first@", "lf-term-second@"):
    wrap(T, w, f"dup lf-term-base u< if 1 c-rd-in +! else 1 c-rd-st +! then {w}0")
wrap(T, "lf-term-data-word", "dup lf-term-base u< if 1 c-dw-in +! else 1 c-dw-st +! then lf-term-data-word0")
wrap(T, "lf-tin-record", "1 c-tin-dec +! lf-tin-record0")
# cons: tiers, front caches, parents
wrap(T, "lf-tin-sought", "1 c-tin-sought +! lf-tin-sought0 dup if 1 c-tin-hit +! then")
wrap(T, "lf-term-append", "2 pick lf-term-binary-tag? if over pp-take dup pp-take then lf-term-append0")
wrap(T, "lf-term-forget", "1 c-forget +! lf-term-forget0")
def cons_body(t):
    old = "  lf-term-find 0= if lf-term-key@ lf-term-append lf-term-enter exit then\n  dup lf-term-reusable? if lf-term-found exit then\n"
    assert t.count(old) == 1
    return t.replace(old, "  lf-term-find 0= if 1 c-new +! lf-term-key@ lf-term-append lf-term-enter exit then\n  dup lf-term-reusable? if 1 c-store-hit +! lf-term-found exit then\n")
edit(T, cons_body)
wrap(T, "lf-term-cons", "1 c-cons +! in-open @ if 1 c-cons-open +! then in-mls @ if 1 c-cons-mls +! then "
     "fc-look 2 pick 2 pick 2 pick 2>r >r lf-term-cons0 dup if over r> 2r> 3 roll fc-note else r> 2r> 2drop drop then")
# the instantiation memo
wrap(O, "lf-open-begin", "lf-open-stamp 0<> cur-stamped ! 1 pass-ser +! 1 c-pass +! true in-open ! lf-open-begin0")
wrap(O, "lf-open-end", "false in-open ! lf-open-end0")
wrap(O, "lf-of-look", "1 c-visit +! lf-of-look0")
wrap(O, "lf-open-keep", "1 c-rm! +! lf-open-keep0")
wrap(O, "lf-open-known?",
     "over kn ! dup frame-context @ ko ! 1 c-rm@ +! kn @ ko @ seen-mark dup kseen ! if 1 c-seen2 +! then "
     "cur-stamped @ if 1 c-rm-stamped +! then "
     "kn @ lf-term-base u< if 1 c-rm-intier +! else kn @ pp-shared? 0= if 1 c-rm-unsh +! then then "
     "lf-open-known?0 dup if 1 c-rm-hit +! kseen @ if 1 c-hit-in +! "
     "kn @ dup in-range? if 4 * of-tab + ul@ ko @ <> if 1 c-hit-otheroff +! then else drop then "
     "else 1 c-hit-cross +! then cur-stamped @ if 1 c-hit-stamped +! then "
     "kn @ lf-term-base u< if 1 c-hit-intier +! else kn @ pp-shared? 0= if 1 c-hit-unsh +! kseen @ if 1 c-hit-unsh-in +! then then then then")
# universe substitution
wrap(M, "lf-mixed-level-substitute", "1 c-mls +! in-mls @ >r true in-mls ! lf-mixed-level-substitute0 r> in-mls !")
wrap(M, "lf-mls-sort", "1 c-mls-sort +! lf-mls-sort0")
wrap(M, "lf-mls-image-of", "1 c-mls-image +! lf-mls-image-of0")
wrap(M, "lf-mls-binary", "1 c-mls-binary +! lf-mls-binary0")
# the checker's caches: hits, misses, puts by cache number
wrap(K, "lf-cache-count", "2dup 0 lf-cache-nth - /lf-cache / 4 * cells ch-tab + swap if 1 swap +! else cell+ 1 swap +! then lf-cache-count0")
wrap(K, "lf-cache-node!", "dup 0 lf-cache-nth - /lf-cache / 4 * cells ch-tab + 2 cells + 1 swap +! lf-cache-node!0")
wrap(K, "lf-pair!", "dup 0 lf-cache-nth - /lf-cache / 4 * cells ch-tab + 2 cells + 1 swap +! lf-pair!0")
edit("src/cli/leanforth.fs", lambda t: t.replace(": cli-leave ( code -- ) 100 + (bye) ;",
  ": cli-leave ( code -- ) ['] .counters stderr outfile-execute 100 + (bye) ;"))
print("count patch applied")
