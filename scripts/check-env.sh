#!/usr/bin/env bash
# Read-only environment inventory; no tokens or user secrets collected.
# Reports tools on PATH and the project-local toolchains under .tools/.
# It never runs elan, or lean/lake from PATH, because an elan proxy without
# ELAN_HOME would download a toolchain into ~/.elan.
set -u
printf 'LeanForth environment inventory\n'
printf 'Date (UTC): '; date -u +'%Y-%m-%dT%H:%M:%SZ' || true
printf 'OS: '; uname -a || true
printf 'Working directory: '; pwd || true
for cmd in git gh gforth cc make python3 node npm codex claude lean lake elan bwrap; do
    if command -v "$cmd" >/dev/null 2>&1; then
        printf '%-9s %s\n' "$cmd" "$(command -v "$cmd")"
    else
        printf '%-9s MISSING\n' "$cmd"
    fi
done
printf '\nVersions (when available):\n'
for cmd in git gh gforth cc python3 node npm codex claude; do
    if command -v "$cmd" >/dev/null 2>&1; then
        printf '\n[%s]\n' "$cmd"
        case "$cmd" in
          gforth) printf 'bye\n' | gforth --version 2>&1 | head -n 3 ;;
          cc) cc --version 2>&1 | head -n 1 ;;
          *) "$cmd" --version 2>&1 | head -n 3 ;;
        esac
    fi
done

printf '\nProject-local toolchains (.tools/):\n'
local_gforth=.tools/gforth/bin/gforth
local_lean=.tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean
if [ -x "$local_gforth" ]; then
    printf '%-9s %s\n' gforth "$("$local_gforth" --version 2>&1 | head -n 1)"
else
    printf '%-9s MISSING (%s)\n' gforth "$local_gforth"
fi
if [ -x "$local_lean" ]; then
    printf '%-9s %s\n' lean "$("$local_lean" --version 2>&1 | head -n 1)"
else
    printf '%-9s MISSING (%s)\n' lean "$local_lean"
fi
