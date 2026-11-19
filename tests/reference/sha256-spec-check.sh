#!/usr/bin/env bash
# Checks the Lean specification of SHA-256 (tests/reference/sha256-spec.lean,
# docs/programming/SHA256_SPEC.md) with pinned Lean. Run from the repository
# root, as tests/reference/check.sh (make reference) does:
#   LEAN=<pinned lean> bash tests/reference/sha256-spec-check.sh
# 1. Lean elaborates the file with warnings as errors, so every test vector
#    is evaluated by Lean's kernel and every theorem is proved.
# 2. The file's axiom audit lists every declaration of the file, whatever its
#    kind, attributes or modifiers, with its axioms; each must be within the
#    owner's allowlist propext, Classical.choice and Quot.sound (AGENTS.md).
#    The audit must cover every theorem of the source. First, the check must
#    refuse planted faults: private, attribute-carrying and protected
#    theorems that use an axiom outside the allowlist, an incomplete audit,
#    and a `lemma` (not a command of Lean without Mathlib, so Lean rejects it).
# 3. Mutants: the specification with one deliberate mistake each, cut down to
#    the "abc" vector. The unchanged cut-down file must pass, and each mutant
#    must be rejected by the kernel, so the vector would catch such a slip.
# Prints one summary line, or explains the failure and exits 1.
set -eu
. "$(dirname "${BASH_SOURCE[0]}")/../support/pinned-lean.sh"
spec=tests/reference/sha256-spec.lean
work=$(mktemp -d)
trap 'rm -r "$work"' EXIT

# The names of the theorems of the Lean file $1, whatever attributes and
# modifiers precede them on their line.
theorem_names() {
  sed -nE 's/^(@\[[^]]*\] *)?((private|protected|noncomputable|nonrec) +)*theorem +([A-Za-z_][A-Za-z0-9_]*).*/\4/p' "$1"
}

# The report lines of the axiom audit in the Lean output $1.
audit_lines() { sed -n '/^BEGIN AXIOM AUDIT$/,/^END AXIOM AUDIT/p' "$1" | sed '1d;$d'; }

# Fails, naming every offender, unless the Lean output $1 holds a complete
# axiom audit in which each declaration uses allowed axioms only.
audit_allowed() {
  local declared listed line name list axiom bad=0
  declared=$(sed -n 's/^END AXIOM AUDIT (\([0-9]*\) declarations)$/\1/p' "$1")
  listed=$(audit_lines "$1" | wc -l)
  if [ -z "$declared" ] || [ "$declared" -eq 0 ] || [ "$declared" -ne "$listed" ]; then
    printf 'Incomplete axiom audit: %s lines for %s declarations\n' "$listed" "${declared:-?}" >&2
    return 1
  fi
  while IFS= read -r line; do
    case "$line" in
      "'"*"' does not depend on any axioms") ;;
      "'"*"' depends on axioms: ["*"]")
        name=${line%%"' depends on axioms"*}
        name=${name#"'"}
        list=${line#*: [}
        list=${list%]}
        for axiom in ${list//,/ }; do
          case "$axiom" in
            propext | Classical.choice | Quot.sound) ;;
            *) printf '%s uses the axiom %s\n' "$name" "$axiom" >&2; bad=1 ;;
          esac
        done ;;
      *) printf 'Unexpected axiom audit line: %s\n' "$line" >&2; bad=1 ;;
    esac
  done < <(audit_lines "$1")
  return "$bad"
}

# Fails unless every theorem of the Lean file $1 appears in the audit in $2.
audit_covers() {
  local name bad=0
  for name in $(theorem_names "$1"); do
    if ! audit_lines "$2" | grep -qF "Sha256Spec.$name' "; then
      printf 'Theorem %s is missing from the axiom audit\n' "$name" >&2
      bad=1
    fi
  done
  return "$bad"
}

# Planted faults. A private theorem with an attribute and a protected one,
# both using an axiom outside the allowlist, next to the file's own audit.
planted=$work/planted.lean
{
  printf '%s\n' 'import Lean' 'namespace Sha256Spec' \
    'axiom planted_unlisted : (1 : Nat) = 2' \
    '@[simp] private theorem planted_private : (1 : Nat) = 2 := planted_unlisted' \
    'protected theorem planted_protected : (2 : Nat) = 1 := planted_unlisted.symm' \
    'end Sha256Spec'
  sed -n '/^\/-! ## Axiom audit/,$p' "$spec"
} >"$planted"
if [ "$(theorem_names "$planted" | tr '\n' ' ')" != 'planted_private planted_protected ' ]; then
  printf '%s\n' 'The theorem finder missed a private or protected theorem' >&2
  exit 1
fi
if ! "$lean" -DwarningAsError=true "$planted" >"$work/planted.txt" 2>&1; then
  cat "$work/planted.txt" >&2
  printf '%s\n' 'The planted file failed in Lean for an unexpected reason' >&2
  exit 1
fi
audit_covers "$planted" "$work/planted.txt"
if audit_allowed "$work/planted.txt" 2>"$work/planted-error.txt" ||
   ! grep -q 'Sha256Spec.planted_private uses the axiom Sha256Spec.planted_unlisted' \
     "$work/planted-error.txt" ||
   ! grep -q 'Sha256Spec.planted_protected uses the axiom Sha256Spec.planted_unlisted' \
     "$work/planted-error.txt"; then
  cat "$work/planted-error.txt" >&2
  printf '%s\n' 'The axiom audit did not refuse the planted axiom in both theorems' >&2
  exit 1
fi
# An audit with one report missing is refused.
sed '/planted_protected/d' "$work/planted.txt" >"$work/short.txt"
if audit_allowed "$work/short.txt" 2>"$work/short-error.txt" ||
   ! grep -q 'Incomplete axiom audit' "$work/short-error.txt"; then
  printf '%s\n' 'The axiom audit accepted an incomplete audit' >&2
  exit 1
fi
# A `lemma` cannot enter the file: Lean without Mathlib rejects the command.
printf '%s\n' 'theorem planted_ok : True := trivial' 'lemma planted_lemma : True := trivial' \
  >"$work/lemma.lean"
if "$lean" -DwarningAsError=true "$work/lemma.lean" >"$work/lemma.txt" 2>&1; then
  printf '%s\n' 'Lean accepted a lemma command' >&2
  exit 1
fi

start=$(date +%s)
if ! "$lean" -DwarningAsError=true "$spec" >"$work/out.txt" 2>&1; then
  cat "$work/out.txt" >&2
  printf '%s\n' 'Lean rejected the SHA-256 specification' >&2
  exit 1
fi
seconds=$(($(date +%s) - start))
audit_allowed "$work/out.txt"
audit_covers "$spec" "$work/out.txt"
theorems=$(theorem_names "$spec" | wc -l)
declarations=$(audit_lines "$work/out.txt" | wc -l)
vectors=$(grep -cE '^theorem (nist|cavp|published|boundary)_' "$spec")


# The cut-down file: parts 1 to 4, the test helper utf8 and the "abc" vector.
small=$work/abc.lean
sed -e '/^import Lean$/d' -e '/^\/-! ## Part 5\./,$d' "$spec" >"$small"
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

printf 'SHA-256 specification: %s theorems (%s kernel-evaluated vectors) proved in %s s; ' \
  "$theorems" "$vectors" "$seconds"
printf 'axioms of all %s declarations within the allowlist; ' "$declarations"
printf '%s mutants rejected by the kernel.\n' "${#mutants[@]}"
