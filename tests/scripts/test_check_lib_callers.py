#!/usr/bin/env python3
"""Tests of scripts/check-lib-callers.py on throw-away source trees: used, unused, allowlisted, stale and
tests-only libraries, requires resolved relative to the file, and a check of today's tree."""
import importlib.util
import json
import pathlib
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("clc", ROOT / "scripts/check-lib-callers.py")
clc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(clc)


def tree(files):
    tmp = tempfile.TemporaryDirectory()
    for name, text in files.items():
        path = pathlib.Path(tmp.name) / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
    return tmp


class Callers(unittest.TestCase):
    def check(self, files, allow=None):
        with tree(files) as tmp:
            return clc.problems(pathlib.Path(tmp), allow or {})

    def test_direct_and_transitive_use_pass(self):
        files = {"src/lib/a.fs": "\\ a\n", "src/lib/b.fs": "require ./a.fs\n", "src/core/c.fs": "require ../lib/b.fs\n"}
        self.assertEqual(self.check(files)[0], [])

    def test_unused_lib_fails(self):
        files = {"src/lib/a.fs": "", "src/lib/b.fs": "", "src/core/c.fs": "require ../lib/b.fs\n"}
        bad = self.check(files)[0]
        self.assertEqual(len(bad), 1)
        self.assertIn("src/lib/a.fs", bad[0])

    def test_use_inside_lib_only_is_unused(self):
        files = {"src/lib/a.fs": "", "src/lib/b.fs": "require ./a.fs\n"}
        self.assertEqual(len(self.check(files)[0]), 2)

    def test_include_and_needs_and_comment_count(self):
        files = {"src/lib/a.fs": "", "src/lib/b.fs": "", "src/lib/c.fs": "",
                 "src/x.fs": "include lib/a.fs \\ note\n  NEEDS lib/b.fs\nrequire lib/c.fs\n"}
        self.assertEqual(self.check(files)[0], [])

    def test_paths_resolve_relative_to_the_requiring_file(self):
        files = {"src/lib/a.fs": "", "src/core/x.fs": "require ./a.fs\n"}   # core/a.fs does not exist
        self.assertEqual(len(self.check(files)[0]), 1)

    def test_allowlist_entry_excuses_an_unused_lib(self):
        allow = {"src/lib/a.fs": {"plan": "9.4.8a", "reason": "first caller soon"}}
        bad, _, listed = self.check({"src/lib/a.fs": ""}, allow)
        self.assertEqual((bad, listed), ([], ["src/lib/a.fs"]))

    def test_allowlist_entry_needs_plan_and_reason(self):
        for entry in ({"plan": "9.4.8a"}, {"reason": "x"}, {}):
            bad = self.check({"src/lib/a.fs": ""}, {"src/lib/a.fs": entry})[0]
            self.assertEqual(len(bad), 1, entry)

    def test_stale_and_unknown_allowlist_entries_fail(self):
        files = {"src/lib/a.fs": "", "src/x.fs": "require ./lib/a.fs\n"}
        entry = {"plan": "1", "reason": "r"}
        stale = self.check(files, {"src/lib/a.fs": entry})[0]
        self.assertEqual(len(stale), 1)
        self.assertIn("stale", stale[0])
        unknown = self.check(files, {"src/lib/gone.fs": entry})[0]
        self.assertIn("names no src/lib/ file", unknown[0])

    def test_tests_only_use_is_reported_not_failed(self):
        files = {"src/lib/a.fs": "", "tests/lib/a.fs": "require ../../src/lib/a.fs\n"}
        bad, tests_only, _ = self.check(files, {"src/lib/a.fs": {"plan": "1", "reason": "r"}})
        self.assertEqual((bad, tests_only), ([], ["src/lib/a.fs"]))

    def test_main_exit_codes(self):
        with tree({"src/lib/a.fs": ""}) as tmp:
            self.assertEqual(clc.main([tmp]), 1)
            (pathlib.Path(tmp) / "tests").mkdir()
            (pathlib.Path(tmp) / "tests/lib-callers-allowlist.json").write_text(
                json.dumps({"src/lib/a.fs": {"plan": "1", "reason": "r"}}))
            self.assertEqual(clc.main([tmp]), 0)


class Tree(unittest.TestCase):
    def test_todays_tree_holds(self):
        self.assertEqual(clc.main([]), 0)


if __name__ == "__main__":
    unittest.main()
