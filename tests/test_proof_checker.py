# [PROOFTHEORY] Automated Deductive Proof Checker Test Suite
# Part of Ticket 7646 / Ticket 7649

import os
import shutil
import subprocess
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from src.sequent_calculus import Formula, Atom, Not, And, Or, Imp, Sequent, ProofTree
from src.proof_checker import ProofChecker


class TestProofChecker(unittest.TestCase):
    def setUp(self):
        self.checker_lk = ProofChecker("LK")
        self.checker_lj = ProofChecker("LJ")

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

    def test_axiom_verification(self):
        A = Atom("A")
        ax = ProofTree("Ax", Sequent((A,), (A,)))
        valid, msg = self.checker_lk.verify_proof(ax)
        self.assertTrue(valid, msg)

        invalid_ax = ProofTree("Ax", Sequent((A,), (Atom("B"),)))
        valid, _ = self.checker_lk.verify_proof(invalid_ax)
        self.assertFalse(valid)

    def test_conjunction_and_implication_derivation(self):
        A = Atom("A")
        B = Atom("B")
        # Prove: A, B |- A /\ B
        ax1 = ProofTree("Ax", Sequent((A,), (A,)))
        ax2 = ProofTree("Ax", Sequent((B,), (B,)))
        tree_and = ProofTree("R_And", Sequent((A, B), (And(A, B),)), (ax1, ax2))

        valid, msg = self.checker_lk.verify_proof(tree_and)
        self.assertTrue(valid, msg)

        # Extend to: A |- B -> (A /\ B)
        tree_imp = ProofTree("R_Imp", Sequent((A,), (Imp(B, And(A, B)),)), (tree_and,))
        valid, msg = self.checker_lk.verify_proof(tree_imp)
        self.assertTrue(valid, msg)

        # Check in LJ (single succedent holds)
        valid_lj, msg_lj = self.checker_lj.verify_proof(tree_imp)
        self.assertTrue(valid_lj, msg_lj)

    def test_intuitionistic_succedent_constraint(self):
        A = Atom("A")
        B = Atom("B")
        # Multiple succedent formulas allowed in LK, forbidden in LJ
        multi_succedent = ProofTree("Ax", Sequent((A,), (A, B)))
        valid_lk, msg_lk = self.checker_lk.verify_proof(multi_succedent)
        self.assertTrue(valid_lk, msg_lk)

        valid_lj, _ = self.checker_lj.verify_proof(multi_succedent)
        self.assertFalse(valid_lj, "LJ must reject sequents with multiple succedent formulas")

    def test_subformula_property_verification(self):
        A = Atom("A")
        B = Atom("B")
        ax1 = ProofTree("Ax", Sequent((A,), (A,)))
        ax2 = ProofTree("Ax", Sequent((B,), (B,)))
        tree = ProofTree("R_And", Sequent((A, B), (And(A, B),)), (ax1, ax2))

        valid, msg = self.checker_lk.verify_subformula_property(tree)
        self.assertTrue(valid, msg)


if __name__ == "__main__":
    unittest.main()
