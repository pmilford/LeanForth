#!/usr/bin/env bash
# Read-only environment inventory; no tokens or user secrets collected.
set -u
printf 'LeanForth environment inventory\n'
printf 'Date (UTC): '; date -u +'%Y-%m-%dT%H:%M:%SZ' || true
printf 'OS: '; uname -a || true
printf 'Working directory: '; pwd || true
for cmd in git gh gforth cc make python3 node npm codex lean lake elan bwrap; do
    if command -v "$cmd" >/dev/null 2>&1; then
        printf '%-9s %s\n' "$cmd" "$(command -v "$cmd")"
    else
        printf '%-9s MISSING\n' "$cmd"
    fi
done
printf '\nVersions (when available):\n'
for cmd in git gh gforth cc python3 node npm codex lean lake elan; do
    if command -v "$cmd" >/dev/null 2>&1; then
        printf '\n[%s]\n' "$cmd"
        case "$cmd" in
          gforth) printf 'bye\n' | gforth --version 2>&1 | head -n 3 ;;
          cc) cc --version 2>&1 | head -n 1 ;;
          *) "$cmd" --version 2>&1 | head -n 3 ;;
        esac
    fi
done
