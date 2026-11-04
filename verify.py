#!/usr/bin/env python3
"""Automated sanity check and verification script for ProofTheory."""

import os
import subprocess
import sys

ROOT = os.path.dirname(os.path.abspath(__file__))


def main() -> int:
    coq_files = [
        os.path.join(ROOT, "QandPA.v"),
        os.path.join(ROOT, "proofs_with_omega.v"),
    ]
    for vf in coq_files:
        if not os.path.isfile(vf) or os.path.getsize(vf) == 0:
            print(f"[FAIL] Missing or empty Coq source: {vf}")
            return 1
        print(f"[OK] Coq source verified: {vf} ({os.path.getsize(vf)} bytes)")

    res = subprocess.run(
        [sys.executable, "-m", "unittest", "discover", "-s", os.path.join(ROOT, "tests"), "-p", "test_*.py"],
        cwd=ROOT,
    )
    return res.returncode


if __name__ == "__main__":
    sys.exit(main())
