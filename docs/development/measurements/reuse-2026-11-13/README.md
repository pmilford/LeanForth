# Reuse baseline, 2026-11-13 (plan 9.4.8)

Measured with [`metrics.py`](metrics.py) (`python3 docs/development/measurements/reuse-2026-11-13/metrics.py REV`) (lines per folder; per library: non-lib files requiring it, its words, those used outside `lib/`, and token call sites outside `lib/`, approximate).

```text
rev 14423237
folder   files  lines  code  words
author      14   2665  1756    601
cli          8   4001  2633   1011
core        31   7196  4148   1556
front       35   9294  6199   2723
import      13   6451  4332   1629
kernel      42  16771  9852   3758
lib         30   7145  3893   1637
(top)        1     89    33      0
present     17   4565  3047   1231
program     11   3000  1907    869
TOTAL      202  61177 37800  15015

lib file          req-by-nonlib  words  used-outside  call-sites
bigint.fs                     0    126            5          16
bignum.fs                     1    250           21          40
bounds.fs                     0      3            3          44
bytes.fs                     29     58           18         358
cons.fs                      10     59           28         129
context.fs                    0     81           22        3980
frame.fs                      0     40           23         450
hash32.fs                    18      5            3          54
htab.fs                      14     45           14         181
json-write.fs                 5    122           19          77
json.fs                       8    136           21         326
lib.fs                      138      1            0           0
module.fs                     1      6            2           2
node.fs                       0      4            4          12
outcome.fs                    9     18           16        2320
pools.fs                      4     24            7          55
portability.fs                4     15           11        3780
runs.fs                       4     31            9          35
sections.fs                   3    100           10          22
sha256.fs                     6     50           11          39
slab.fs                      27     55           23         717
sort.fs                       0     60            0           0
store-columns.fs              9     24            8          46
store.fs                      0     85           34         214
task.fs                       1    107            9          13
text-rule.fs                  7      8            3          10
text-run.fs                   4     20            6          10
u32.fs                       15     18            7         344
walk.fs                       0     49           18         108
xt-table.fs                   3     10            6          59
TOTAL                             1610          361       13441
```
