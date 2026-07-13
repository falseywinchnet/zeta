#!/usr/bin/env python3

import subprocess
import sys
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent


class FlowRoundTests(unittest.TestCase):
    def test_directed_bound_script(self):
        result = subprocess.run(
            [sys.executable, str(HERE / "check_bounds.py")],
            check=True,
            capture_output=True,
            text=True,
        )
        self.assertIn("endpoint_lower=", result.stdout)


if __name__ == "__main__":
    unittest.main()
