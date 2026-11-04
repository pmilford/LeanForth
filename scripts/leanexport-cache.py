#!/usr/bin/env python3
"""LEANEXPORT for the local test suites: the pinned toolchain's leanexport,
run through the cache of scripts/lean-cache.py (see there). Takes
leanexport's own arguments; the Makefile sets LEANEXPORT to this script
unless LEAN_CACHE=0."""
import os
import runpy
import sys

sys.argv[1:1] = ["--leanexport"]
runpy.run_path(os.path.join(os.path.dirname(os.path.abspath(__file__)), "lean-cache.py"),
               run_name="__main__")
