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
    def test_other_candidate_statement_pairs(self):
        # Original pages and catalogue sources checked in the 2026-10-20
        # other-candidates pass: entire functions, divisor pairs, cyclic
        # vertex subsets, and measurable translate differences.
        mapping = load_problem_mapping()
        for jsp, erdos in {204: 227, 364: 449, 503: 622, 753: 908}.items():
            with self.subTest(jsp=jsp):
                self.assertEqual(mapping.get(jsp), erdos)

    def test_previously_audited_submission_pairs(self):
        # These exact scopes were independently established in the repair
        # queue; the legacy discovery map must not contradict that audit.
        mapping = load_problem_mapping()
        for jsp, erdos in {500: 617, 403: 503, 247: 291, 780: 939,
                           58: 23, 280: 338, 569: 699, 395: 488,
                           210: 238, 579: 711}.items():
            with self.subTest(jsp=jsp):
                self.assertEqual(mapping.get(jsp), erdos)

    def test_newly_source_verified_pairs(self):
        # Exact statements and fixed-source evidence are recorded in
        # verification/2026-10-20-execution/MAPPINGS.md.
        mapping = load_problem_mapping()
        for jsp, erdos in {211: 240, 281: 339, 585: 717, 782: 941,
                           854: 1027, 857: 1031, 1010: 1205,
                           1018: 1213, 1019: 1214}.items():
            with self.subTest(jsp=jsp):
                self.assertEqual(mapping.get(jsp), erdos)

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
