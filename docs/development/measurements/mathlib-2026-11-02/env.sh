# Environment for the pinned-toolchain Mathlib measurement (source, do not run).
# REPO defaults to this checkout; logs go to $SP (default .tools/mathlib/logs).
REPO=${REPO:-$(git -C "$(dirname "${BASH_SOURCE[0]}")" rev-parse --show-toplevel)}
export ELAN_HOME=$REPO/.tools/elan
TC=$REPO/.tools/elan/toolchains/leanprover--lean4---v4.35.0/bin
export PATH="$TC:$PATH"
MROOT=$REPO/.tools/mathlib
export MATHLIB_CACHE_DIR="$MROOT/cache"
export XDG_CACHE_HOME="$MROOT/xdg-cache"
SP=${SP:-$MROOT/logs}
mkdir -p "$SP"
