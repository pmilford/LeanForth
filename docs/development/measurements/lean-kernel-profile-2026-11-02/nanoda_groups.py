#!/usr/bin/env python3
"""Exclusive and inclusive shares by function family for a nanoda profile.

Usage: nanoda_groups.py STACKS
Exclusive: leaf frame's family. Inclusive: any frame of the family (once per sample).
Owner: first non-service family walking outwards from the leaf.
"""
import collections, re, sys

RULES = [
    ('parse_export', r'nanoda_lib::parser|serde|from_utf8|ExportJsonVal|json'),
    ('hashcons_alloc', r'TcCtx::alloc_expr|alloc_level|alloc_name|IndexMap|indexmap|insert_full|get_index_of|Equivalent'),
    ('nat_literals', r'try_reduce_nat|num_bigint|BigUint|biguint'),
    ('level_subst', r'subst_level|subst_expr_levels|subst_aux|abstr_aux_levels|level::'),
    ('instantiate_abstract', r'inst_aux|inst_beta|::inst::|abstr_aux|abstr\b|instantiate|lift|lower'),
    ('expr_construct', r'TcCtx::mk_|unfold_apps|foldl_apps|read_expr|view_expr'),
    ('hash_caches', r'hashbrown|HashMap|HashSet|FxHash|reserve_rehash'),
    ('memory', r'^__libc_malloc|^malloc|^cfree|^free$|realloc|raw_vec|RawVec|grow_one|finish_grow|drop_in_place|drop_slow|memcpy|memmove|^\[libc\.so\.6\+0xa'),
    ('defeq', r'def_eq|lazy_delta|eta|proof_irrel|unit_like'),
    ('whnf', r'whnf|unfold_def|reduce_rec|reduce_proj|reduce_quot|iota'),
    ('infer', r'::infer'),
    ('env_lookup', r'get_declar|Env::'),
    ('check_driver', r'check_declar|check_all|ExportFile'),
]
RULES = [(n, re.compile(r)) for n, r in RULES]
SERVICE = {'hashcons_alloc', 'expr_construct', 'hash_caches', 'memory', 'other'}
cache = {}


def fam(f):
    r = cache.get(f)
    if r is None:
        r = next((n for n, rx in RULES if rx.search(f)), 'other')
        cache[f] = r
    return r


tot = 0
ex, inc, own = collections.Counter(), collections.Counter(), collections.Counter()
for line in open(sys.argv[1]):
    frames = line.rstrip('\n').split('\t')[2].split(';')
    fams = [fam(f) for f in frames]
    tot += 1
    ex[fams[0]] += 1
    for x in set(fams):
        inc[x] += 1
    own[next((x for x in fams if x not in SERVICE), 'none')] += 1
print(f'samples {tot}')
print('| Family | Exclusive | Inclusive | Owner |\n| --- | ---: | ---: | ---: |')
for n, _ in RULES + [('other', None), ('none', None)]:
    print(f'| {n} | {100 * ex[n] / tot:.1f}% | {100 * inc[n] / tot:.1f}% | {100 * own[n] / tot:.1f}% |')
