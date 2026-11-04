#!/bin/bash
# The hostile inputs of adversarial.fs in one mode: cv (alias vocabulary),
# ms (portable third state) or g1 (Gforth 1.0's own interpreter in a third
# state). Usage: adversarial.sh GFORTH MODE (from the repository root).
here=$(dirname "$0")
case $2 in
  cv) set -- "$1" "$here/cv.fs" ;;
  ms) set -- "$1" "$here/cv.fs" "$here/ms.fs" -e "' ms-run constant adv-mode" ;;
  g1) set -- "$1" "$here/cv.fs" "$here/ms.fs" "$here/ms-gforth1.fs" -e "' g1-run constant adv-mode" ;;
esac
g=$1; shift
exec timeout -k 5 60 "$g" "$@" "$here/adversarial.fs" </dev/null 2>/dev/null
