"""Load discovery mappings without inventing missing problem numbers.

Unreviewed rows remain discovery hints. Check each mapping against the
original statement before using it for a proof or prize submission.
"""

import json
from pathlib import Path


def load_problem_mapping():
    path = Path(__file__).with_name("jsp_erdos_map.json")
    return {int(jsp): int(erdos) for jsp, erdos in json.loads(path.read_text()).items()}
