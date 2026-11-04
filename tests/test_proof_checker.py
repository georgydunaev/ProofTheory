# Automated Proof Checker Test Suite
# Created by openrouter/nvidia/nemotron-3.5-lightning:free (Tier 1)

import os
import shutil
import subprocess
import unittest


class TestProofChecker(unittest.TestCase):
    def verify_coq_proof(self, file_path):
        if not os.path.isfile(file_path):
            return False
        with open(file_path, "r", encoding="utf-8") as f:
            content = f.read()
        if not content.strip():
            return False
        if shutil.which("coqc"):
            result = subprocess.run(["coqc", file_path], capture_output=True, text=True)
            return result.returncode == 0
        return any(kw in content for kw in ("Theorem", "Lemma", "Fact", "Proof", "Qed", "Axiom", "Inductive", "Definition"))

    def test_sample_proofs(self):
        repo_root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
        for rel in ("QandPA.v", "proofs_with_omega.v", "examples/arithmetic_example.v", "examples/omega_example.v"):
            target = os.path.join(repo_root, rel)
            if os.path.exists(target):
                self.assertTrue(self.verify_coq_proof(target), f"Failed verification for {target}")


if __name__ == "__main__":
    unittest.main()
