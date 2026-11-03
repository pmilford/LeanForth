#!/usr/bin/env python3
"""Family time shares from unwound perf stacks (output of perfunwind.py).

Usage: analyze.py STACKS [--detail]

Each frame is classified by its function name (argument list stripped) with
the rules below; the first matching rule wins.

* Exclusive (self): the family of the leaf frame. Hash-table frames are split
  by the nearest calling function that is not a hash-table/std frame.
* Inclusive: the sample has a frame of that family anywhere in its chain
  (counted once per sample, so recursion is not double counted). Families
  overlap, so inclusive shares do not add up to 100%.
* Owner: walk from the leaf outwards, skipping service frames (memory, hash
  tables, structural equality, expression construction, resource checks), to
  the first frame of an algorithmic family. This partitions the samples.
"""
import collections, re, sys

R = lambda s: re.compile(s)
RULES = [
    ('nat_string_literals', R(r'__gmp|\bmpz|lean::mpz|lean_nat_big|lean_nat_|reduce_nat|reduce_bin_nat|reduce_pow|reduce_shiftLeft|nat_lit|string_lit|lean::nat::|lean_string_|is_nat_lit_ext|nat_lit_ext')),
    ('memory_alloc', R(r'^mi_malloc|^_mi_malloc|^mi_new|^_mi_page|^mi_page|mi_heap_malloc|lean_alloc|__libc_malloc|^malloc$|operator new|^realloc|lean_copy_expand_array|mi_page_free_list_extend|mi_segment|_mi_heap|_mi_os')),
    ('memory_free', R(r'^mi_free|^_mi_free|lean_free|lean_dec_ref|lean_del|lean::lean_del|^free$|^cfree$|operator delete|__deallocate_node|~object_ref|~buffer|_int_free|lean_dealloc|lean_mark_persistent|lean_mark_mt|^mi_|^_mi_')),
    ('sharecommon', R(r'sharecommon')),
    ('hash_table', R(r'__hash_table|__hash_iterator|__next_prime|__murmur2|cityhash|unordered_map|expr_pair_hash|expr_pair_eq|key_hasher')),
    ('tc_cache_api', R(r'succeeded_before|failed_before|cache_success|cache_failure')),
    ('structural_eq', R(r'expr_eq_fn|^lean::is_equal|lean_expr_eqv|lean_expr_equal|^lean::operator==|lean_name_eq|Name_quickCmp|Name_beq|lean_level_eq|expr_hash|hash_str|lean_expr_hash|lean_level_hash|lean_name_hash|^lean::hash$')),
    ('level_ops', R(r'^lean::level|replace_level_fn|is_equivalent|^lean::normalize|is_geq|^lean::mk_max|^lean::mk_imax|^lean::mk_succ|^lean_level_|has_univ_param|check_level|lean_expr_has_level_param|mk_univ_param|LEVELOVERLOAD')),
    ('instantiate_abstract', R(r'replace_rec_fn|^lean::replace$|__func<lean::replace|^lean::instantiate|__func<lean::instantiate|instantiate_rev|instantiate_lparams|instantiate_value_lparams|instantiate_type_lparams|^lean::abstract|abstract_|lift_loose_bvars|lower_loose_bvars|has_loose_bvar|loose_bvar_range|^lean::mk_binding|cheap_beta|head_beta|^lean::apply_beta|lean_expr_instantiate|lean_expr_abstract|lean_expr_lift|lean_expr_lower')),
    ('expr_construct', R(r'lean_expr_mk_|^lean::mk_app|^lean::mk_rev_app|^lean::update_|Expr_(app|lam|forallE|letE|const|proj|mdata|sort|bvar|fvar|lit)___override|^lean::get_app_|^lean::mk_lambda|^lean::mk_pi|^lean::mk_let|^lean::mk_constant|^lean::mk_proj|^lean::mk_sort|lean_expr_data|mk_app_data|^lean::is_app_of|^lean::expr::|^lean::mk_fvar|local_ctx|LocalContext|name_generator|^lean::get_dummy|lean_expr_binder_info|^lean::binding_|^lean::app_|^lean::const_|^lean::is_')),
    ('env_lookup', R(r'environment::find|lean_environment_find|Kernel_Environment_find|PersistentHashMap_find|SMap_find|DHashMap_Internal_Raw_u2080_Const_get|to_optional<lean::constant_info>|constant_info::|^lean::get_constant|environment::get$|is_quot_initialized|ConstantInfo_')),
    ('defeq', R(r'type_checker::is_def_eq|lazy_delta|quick_is_def_eq|try_eta|eta_expand|is_def_eq_proof_irrel|is_def_eq_unit_like|is_def_eq_offset|try_string_lit_expansion')),
    ('whnf', R(r'type_checker::whnf|whnf_core|whnf_fvar|unfold_definition|reduce_recursor|reduce_proj|inductive_reduce_rec|quot_reduce_rec|try_unfold_proj_app|type_checker::is_delta|get_first_rec_rule|^lean::inductive|reduce_quot|to_cnstr_when_K|mk_nullary_cnstr|expand_eta_struct|get_rec_rule|recursor_val|is_non_rec_structure|^lean::is_nat_succ|get_major_induct')),
    ('infer', R(r'type_checker::infer|type_checker::check$|ensure_sort|ensure_pi|type_checker::is_prop')),
    ('cache_teardown', R(r'type_checker::~type_checker|type_checker::state::~state')),
    ('kernel_entry', R(r'check_constant_val|check_no_metavar|check_duplicated_univ_params|check_name|^lean::environment::add|lean_add_decl|catch_kernel_exceptions|type_checker::type_checker|type_checker::state::state|add_inductive|lean_environment_add|Kernel_Environment_add|elim_only_at_universe_zero|add_inductive_fn')),
    ('resource_checks', R(r'check_system|scope_rec_depth|check_stack|check_memory|check_interrupted|check_heartbeat|add_heartbeats|^lean::throw_|interrupt')),
    ('replay_bookkeeping', R(r'Replay|FoldConsts|getUsedConstants|NameSet|NameMap|DTreeMap|^l_Lean_Name_|RBNode|DHashMap|replayFromFresh')),
    ('loading', R(r'importModules|readModuleData|finalizeImport|lean_read_module_data|^initialize_|_init_l_|lean_initialize|ld-linux|^_dl_|mkEmptyEnvironment|withImportModules|lean_run_init|registerEnvExtension|ImportM|setImportedEntries|freeRegions|lean_obj_once|runtime_initialize|LeanExport|parseStream|Json')),
]
FAMS = [n for n, _ in RULES] + ['other']
SERVICE = {'memory_alloc', 'memory_free', 'hash_table', 'structural_eq', 'expr_construct',
           'resource_checks', 'other', 'tc_cache_api'}
KERNEL = R(r'lean_add_decl|lean::environment::add|type_checker::')
LOAD = R(r'importModules|readModuleData|finalizeImport|lean_initialize|initialize_LeanChecker|ld-linux|mkEmptyEnvironment|LeanExport|parseStream|_init_l_|^initialize_')


def strip(frame):
    if frame.startswith(('lean::type_checker::is_def_eq(lean::level', 'lean::type_checker::is_def_eq(lean::list_ref<lean::level',
                         'lean::instantiate(lean::level', 'lean::is_def_eq(lean::level')):
        return 'LEVELOVERLOAD ' + frame[:40]
    return re.sub(r'\(.*', '', frame)


_cache = {}


def family(frame):
    f = _cache.get(frame)
    if f is None:
        name = strip(frame)
        f = 'other'
        for n, r in RULES:
            if r.search(name):
                f = n
                break
        _cache[frame] = f
    return f


def hash_owner(frames, fams, i):
    """Classify a hash-table frame by its nearest non-hash, non-std caller."""
    j = i + 1
    while j < len(frames) and (fams[j] == 'hash_table' or frames[j].startswith('std::')):
        j += 1
    caller = frames[j] if j < len(frames) else ''
    if 'replace_rec_fn' in caller:
        return 'hash: instantiate/abstract memo (replace_rec_fn)'
    if 'sharecommon' in caller:
        return 'hash: sharecommon (input hash-consing)'
    if 'expr_eq_fn' in caller:
        return 'hash: structural-equality visited pairs'
    if '~state' in caller or '~type_checker' in caller:
        return 'hash: cache teardown'
    if 'type_checker::' in caller:
        return 'hash: type-checker caches (infer, whnf, whnf_core, def-eq)'
    if 'instantiate_lparams' in caller or 'replace_level' in caller:
        return 'hash: level-parameter instantiation memo'
    return 'hash: other (' + strip(caller)[:50] + ')'


def main():
    path = sys.argv[1]
    total = kernel_total = trunc = 0
    excl, excl_k, incl, owner = (collections.Counter() for _ in range(4))
    region, hsplit, others = collections.Counter(), collections.Counter(), collections.Counter()
    for line in open(path):
        pid, t, chain = line.rstrip('\n').split('\t')
        frames = chain.split(';')
        total += 1
        trunc += t == '1'
        fams = [family(f) for f in frames]
        leaf = fams[0]
        if any(KERNEL.search(f) for f in frames):
            reg = 'kernel (inside lean_add_decl)'
        elif any('Replay' in f for f in frames):
            reg = 'replay bookkeeping (outside the kernel)'
        elif any(LOAD.search(strip(f)) for f in frames):
            reg = 'start-up, loading, parsing'
        else:
            reg = 'other (exit, teardown, unknown)'
        region[reg] += 1
        inker = reg.startswith('kernel')
        kernel_total += inker
        excl[leaf] += 1
        if inker:
            excl_k[leaf] += 1
        if leaf == 'hash_table':
            hsplit[hash_owner(frames, fams, 0)] += 1
        for f in set(fams):
            incl[f] += 1
        own = next((f for f in fams if f not in SERVICE), 'unattributed')
        owner[own] += 1
        if leaf == 'other':
            others[strip(frames[0])[:100]] += 1

    def pct(c, d=None):
        d = total if d is None else d
        return f'{100.0 * c / max(d, 1):5.1f}%'

    print(f'samples {total}; kernel samples {kernel_total}; truncated chains {trunc} ({pct(trunc)})')
    print('\n| Region | Share |\n| --- | ---: |')
    for r, c in region.most_common():
        print(f'| {r} | {pct(c)} |')
    print('\n| Family | Exclusive (self), all | Exclusive, within kernel | Inclusive | Owner (partition) |')
    print('| --- | ---: | ---: | ---: | ---: |')
    for f in FAMS:
        inc = pct(incl[f]) if f not in ('replay_bookkeeping', 'loading', 'kernel_entry', 'other') else 'n/a'
        print(f'| {f} | {pct(excl[f])} | {pct(excl_k[f], kernel_total)} | {inc} | {pct(owner[f])} |')
    print(f'| unattributed | | | | {pct(owner["unattributed"])} |')
    print('\nExclusive hash-table time split by caller:')
    for k, c in hsplit.most_common():
        print(f'  {pct(c)}  {k}')
    if '--detail' in sys.argv:
        print('\nTop leaf symbols classified "other":')
        for s, c in others.most_common(20):
            print(f'  {pct(c)}  {s}')


main()
