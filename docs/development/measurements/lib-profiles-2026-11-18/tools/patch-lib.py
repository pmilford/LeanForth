#!/usr/bin/env python3
"""lib-profiles 2026-11-18: put call counters into a scratch copy of src/ (never src/ itself).
usage: patch-lib.py ROOT   ROOT holds a copy of src/ and bin/ (git archive of the commit).
Each entry: file, word, prologue (stack-neutral, run first in the word), counter number and
what the size is. The counters (libcnt.fs) are printed when bin/leanforth leaves."""
import re
import shutil
import sys
from pathlib import Path

ROOT = Path(sys.argv[1])
HERE = Path(__file__).resolve().parent
COUNTERS = [
    # file, word, prologue, label
    ('sha256', 'sha256-update', 'over 0 lcnt-size', 'sha256-update: bytes a piece'),
    ('json', 'json-parse', 'over 1 lcnt-size', 'json-parse: bytes a text'),
    ('json-write', 'jw-start', '2 lcnt+', 'jw-start: texts written'),
    ('json-write', 'jw-end', 'dup jw-written @ 3 lcnt-size', 'jw-end: bytes a text'),
    ('bignum', 'big-binary', '2over @ swap @ max 4 lcnt-size', 'bignum operation: limbs of the larger operand'),
    ('htab', 'htab-find', 'dup htab-slots 5 lcnt-size', 'htab-find: slots of the table'),
    ('memo', 'memo-put', 'dup memo-count 6 lcnt-size', 'memo-put: entries already held'),
    ('memo', 'memo-find', 'dup memo-count 7 lcnt-size', 'memo-find: entries held'),
    ('slab', 'slab-init', '8 lcnt+', 'slab-init: slabs made'),
    ('slab', 'slab-grow', 'dup slab-capacity 9 lcnt-size', 'slab growth: capacity before'),
    ('sort', 'sort-records', 'over 10 lcnt-size', 'sort-records: records'),
    ('pqueue', 'pq-push', 'dup pq-count 11 lcnt-size', 'pq-push: cells queued'),
    ('bytes', 'reader-line', '12 lcnt+', 'reader-line: lines'),
    ('decimal', 'ud>decimal', '13 lcnt+', 'u>decimal and kin: numbers written'),
    ('sections', 'sections-add', '2over * 14 lcnt-size', 'sections-add: bytes a section'),
    ('sections', 'sections-read', '15 lcnt+', 'sections-read: sections read'),
    ('task', 'job-submit', '16 lcnt+', 'job-submit: jobs'),
    ('cons', 'cons-commit', 'dup cons-numbers 17 lcnt-size', 'cons-commit: records already held'),
    ('cons', 'cons-find', '18 lcnt+', 'cons-find: finds'),
    ('pools', 'text-intern', 'over 19 lcnt-size', 'text-intern: bytes a text'),
    ('runs', 'run-push', '20 lcnt+', 'run-push: cells pushed'),
    ('store', 'store-grow', '21 lcnt+', 'store-grow: growths'),
    ('store', 'store-heap-init', '2over drop 22 lcnt-size', 'store-heap-init: capacity'),
    ('walk', 'walk-run', '23 lcnt+', 'walk-run: walks'),
    ('frame', 'frame-run', '24 lcnt+', 'frame-run: passes'),
    ('frame', 'frame-call', '25 lcnt+', 'frame-call: child visits'),
    ('context', 'context-new', '26 lcnt+', 'context-new: contexts'),
    ('text-rule', 'tr-rule?', 'dup 27 lcnt-size', 'tr-rule?: bytes a text'),
    ('xt-table', 'xt-table@', '28 lcnt+', 'xt-table@: lookups'),
    ('blocks', 'block-resize', 'over 29 lcnt-size', 'block-resize: bytes asked'),
    ('blocks', 'allocate0', 'dup 30 lcnt-size', 'allocate0: bytes asked'),
    ('hash32', 'hash-bytes', 'dup 31 lcnt-size', 'hash-bytes: bytes'),
    ('bits', 'lower-bound', '2 pick 2 pick swap - 32 lcnt-size', 'lower-bound: range'),
    ('bounds', 'cells-index', 'dup 33 lcnt-size', 'cells-index: cells'),
    ('outcome', 'ok-each', 'over 34 lcnt-size', 'ok-each: steps'),
    ('bytes', 'utf8-valid?', 'dup 35 lcnt-size', 'utf8-valid?: bytes'),
    ('text-run', 'text-scan', 'over 36 lcnt-size', 'text-scan: characters'),
    ('text-run', 'text-any?', 'over 36 lcnt-size', 'text-any?: characters'),
    ('node', 'node-new', '37 lcnt+', 'node-new: nodes'),
    ('store-columns', 'columns-grow', '38 lcnt+', 'columns-grow: growths'),
    ('decimal', 'digits>u', 'dup 39 lcnt-size', 'digits>u: digits'),
    ('bignum', 'big-compare', '41 lcnt+', 'big-compare: comparisons'),
    ('bignum', 'decimal>big', 'over 45 lcnt-size', 'decimal>big: digits'),
    ('htab', 'htab-init', '48 lcnt+', 'htab-init: tables'),
    ('memo', 'memo-init', '49 lcnt+', 'memo-init: memos'),
    ('pools', 'tuple-end', '50 lcnt+', 'tuple-end: tuples'),
    ('frame', 'frame-grow', 'over 52 lcnt-size', 'frame-grow: cells needed'),
    ('runs', 'run-cat', '53 lcnt+', 'run-cat: joins'),
    ('pqueue', 'pq-init', '54 lcnt+', 'pq-init: queues'),
    ('bigint', 'int-binary', '55 lcnt+', 'bigint operation'),
    ('json-write', 'jw-copy', '56 lcnt+', 'jw-copy: values copied'),
    ('context', 'context-catch', '57 lcnt+', 'context-catch: catches'),
    ('slab', 'slab-push', 'dup slab-count 58 lcnt-size', 'slab-push: units held'),
    ('u32', 'u32s>le', 'dup 59 lcnt-size', 'u32s>le: fields'),
]

shutil.copy(HERE / 'libcnt.fs', ROOT / 'src/lib/libcnt.fs')
port = ROOT / 'src/lib/portability.fs'
text = port.read_text()
if not text.startswith('require ./libcnt.fs'):
    port.write_text('require ./libcnt.fs\n' + text)
labels = {}
for lib, word, prologue, label in COUNTERS:
    path = ROOT / 'src/lib' / (lib + '.fs')
    text = path.read_text()
    head = re.compile(r'^: ' + re.escape(word) + r' \([^)]*\)', re.M)
    found = head.findall(text)
    assert len(found) >= 1, (lib, word)
    m = head.search(text)
    text = text[:m.end()] + ' ' + prologue + ' ' + text[m.end():]
    path.write_text(text)
    labels[int(re.findall(r'(\d+) lcnt', prologue)[0])] = label
cli = ROOT / 'src/cli/leanforth.fs'
text = cli.read_text()
old = ': cli-leave ( code -- ) 100 + (bye) ;'
assert text.count(old) == 1
cli.write_text(text.replace(old, ': cli-leave ( code -- ) lcnt-dump 100 + (bye) ;'))
(ROOT / 'labels.txt').write_text(''.join(f'{k} {v}\n' for k, v in sorted(labels.items())))
print('patched', len(COUNTERS))
