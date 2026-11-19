# Sourced by every shell runner of Lean (Forth review of reuse-b, finding 4):
# sets lean to scripts/lean_pin.py pinned's Lean ($LEAN, else this checkout's
# pinned toolchain binary), or stops the runner with the reason. A Lean that
# is an elan proxy, not a toolchain's own binary or not Lean 4.35.0 is
# refused before it is run, so no runner can start elan's 3 GB download.
lean=$(python3 "$(dirname "${BASH_SOURCE[0]}")/../../scripts/lean_pin.py" pinned) || exit 1
