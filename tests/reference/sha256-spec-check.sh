#!/usr/bin/env bash
# Checks the Lean specification of SHA-256 (tests/reference/sha256-spec.lean,
# docs/programming/SHA256_SPEC.md) with pinned Lean. Run from the repository
# root, as tests/reference/check.sh (make reference) does:
#   LEAN=<pinned lean> bash tests/reference/sha256-spec-check.sh
# 1. Lean elaborates the file with warnings as errors, so every test vector
#    is evaluated by Lean's kernel and every theorem is proved.
# 2. Every theorem of the file has a `#print axioms` report, and each report
#    names only propext, Classical.choice and Quot.sound (owner's allowlist,
#    AGENTS.md). A planted report with another axiom must be refused first.
# 3. Mutants: the specification with one deliberate mistake each, cut down to
#    the "abc" vector. The unchanged cut-down file must pass, and each mutant
#    must be rejected by the kernel, so the vector would catch such a slip.
# Prints one summary line, or explains the failure and exits 1.
set -eu
lean=${LEAN:-lean}
spec=tests/reference/sha256-spec.lean
work=$(mktemp -d)
trap 'rm -r "$work"' EXIT

# The names of the theorems of $spec, one per line.
theorem_names() { sed -n 's/^theorem \([A-Za-z_][A-Za-z0-9_]*\).*/\1/p' "$spec"; }

# Fails unless every theorem of $spec has an axiom report in the Lean output
# $1 that lists allowed axioms only.
axioms_allowed() {
  local name report
  for name in $(theorem_names); do
    report=$(grep -F "'Sha256Spec.$name' " "$1" || true)
    case "$report" in
      "'Sha256Spec.$name' does not depend on any axioms") ;;
      "'Sha256Spec.$name' depends on axioms: ["*"]")
        local list=${report#*: [}
        list=${list%]}
        local axiom
        for axiom in ${list//,/ }; do
          case "$axiom" in
            propext | Classical.choice | Quot.sound) ;;
            *) printf '%s uses the axiom %s\n' "$name" "$axiom" >&2; return 1 ;;
          esac
        done ;;
      *) printf 'No single axiom report for theorem %s\n' "$name" >&2; return 1 ;;
    esac
  done
}

# The axiom check must refuse a report it should refuse.
first=$(theorem_names | head -n 1)
printf "'Sha256Spec.%s' depends on axioms: [propext, Lean.ofReduceBool]\n" "$first" \
  >"$work/planted.txt"
if axioms_allowed "$work/planted.txt" 2>"$work/planted-error.txt" ||
   ! grep -q 'uses the axiom Lean.ofReduceBool' "$work/planted-error.txt"; then
  printf '%s\n' 'The axiom check did not refuse a planted Lean.ofReduceBool' >&2
  exit 1
fi

start=$(date +%s)
if ! "$lean" -DwarningAsError=true "$spec" >"$work/out.txt" 2>&1; then
  cat "$work/out.txt" >&2
  printf '%s\n' 'Lean rejected the SHA-256 specification' >&2
  exit 1
fi
seconds=$(($(date +%s) - start))
axioms_allowed "$work/out.txt"
theorems=$(theorem_names | wc -l)
vectors=$(grep -cE '^theorem (nist|boundary)_' "$spec")

# The cut-down file: parts 1 to 4, the test helper utf8 and the "abc" vector.
small=$work/abc.lean
sed '/^\/-! ## Part 5\./,$d' "$spec" >"$small"
sed -n '/^def utf8 /p' "$spec" >>"$small"
sed -n '/^theorem nist_abc :/,/decide +kernel/p' "$spec" >>"$small"
printf '%s\n' 'end Sha256Spec' >>"$small"
if ! "$lean" -DwarningAsError=true "$small" >"$work/small.txt" 2>&1; then
  cat "$work/small.txt" >&2
  printf '%s\n' 'The cut-down "abc" check failed without a mutation' >&2
  exit 1
fi

# Each mutant: a sed expression applied to the cut-down file, and what it does.
mutants=(
  's/0xc67178f2]/0xc67178f3]/|the last constant K63 off by one'
  's/ROTR 2 x ^^^ ROTR 13 x/ROTR 2 x ^^^ ROTR 12 x/|ROTR^12 for ROTR^13 in Sigma0'
  's/ROTR 7 x ^^^ ROTR 18 x ^^^ SHR 3 x/ROTR 7 x ^^^ ROTR 18 x ^^^ ROTR 3 x/|ROTR for SHR in sigma0'
  's/(x &&& y) ^^^ (~~~x &&& z)/(x \&\&\& y) ^^^ (x \&\&\& z)/|Ch without the complement'
  's/W.getD (t - 7) 0/W.getD (t - 6) 0/|W(t-6) for W(t-7) in the schedule'
  's/e := v.d + T1/e := v.c + T1/|e = c + T1 for e = d + T1'
  's/bytesBE (BitVec.ofNat 64 l)/(bytesBE (BitVec.ofNat 64 l)).reverse/|the length little-endian'
)
for entry in "${mutants[@]}"; do
  edit=${entry%%|*}
  what=${entry#*|}
  sed "$edit" "$small" >"$work/mutant.lean"
  if cmp -s "$small" "$work/mutant.lean"; then
    printf 'Mutant "%s" changed nothing; update its edit\n' "$what" >&2
    exit 1
  fi
  if "$lean" -DwarningAsError=true "$work/mutant.lean" >"$work/mutant.txt" 2>&1; then
    printf 'Mutant "%s" was accepted\n' "$what" >&2
    exit 1
  fi
  if ! grep -q '(kernel) application type mismatch' "$work/mutant.txt"; then
    cat "$work/mutant.txt" >&2
    printf 'Mutant "%s" failed for an unexpected reason\n' "$what" >&2
    exit 1
  fi
done

printf 'SHA-256 specification: %s theorems (%s kernel-evaluated vectors) proved in %s s, ' \
  "$theorems" "$vectors" "$seconds"
printf 'axioms within the allowlist; %s mutants rejected by the kernel.\n' "${#mutants[@]}"
