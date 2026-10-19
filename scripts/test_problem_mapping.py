"""Regression checks against problem statements, not numerical offsets."""

import json
import os
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory
import unittest

if __package__:
    from .problem_mapping import load_problem_mapping
else:
    from problem_mapping import load_problem_mapping


class ProblemMappingTests(unittest.TestCase):
    def test_statement_verified_pairs(self):
        mapping = json.loads(
            Path(__file__).with_name("jsp_erdos_map.json").read_text()
        )
        # Largest prime factors, integer-distance avoidance, logarithmic
        # capacity, and multipartite transversal cliques respectively.
        for jsp, erdos in {307: 372, 377: 465, 865: 1042, 896: 1078}.items():
            with self.subTest(jsp=jsp):
                self.assertEqual(mapping[str(jsp)], erdos)

    def test_loader_uses_project_table_from_another_directory(self):
        expected = {
            int(jsp): int(erdos)
            for jsp, erdos in json.loads(
                Path(__file__).with_name("jsp_erdos_map.json").read_text()
            ).items()
        }
        previous_cwd = Path.cwd()
        with TemporaryDirectory() as directory:
            try:
                os.chdir(directory)
                self.assertEqual(load_problem_mapping(), expected)
            finally:
                os.chdir(previous_cwd)

    def test_selectors_support_module_invocation(self):
        root = Path(__file__).resolve().parents[1]
        for module in ("select_top_targets", "select_batch_problems", "find_unformalized_targets"):
            with self.subTest(module=module):
                result = subprocess.run(
                    [sys.executable, "-B", "-m", f"scripts.{module}"],
                    cwd=root, capture_output=True, text=True, timeout=60,
                )
                self.assertEqual(result.returncode, 0, result.stderr)


if __name__ == "__main__":
    unittest.main()
