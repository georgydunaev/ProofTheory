# [PROOFTHEORY] Tests for Modular Cut-Elimination Procedure (Gentzen Hauptsatz)
# Part of Ticket 7454 / Ticket 7648: Complete Modular Cut Elimination with Rank and Degree Reduction

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from src.sequent_calculus import Formula, Atom, Not, And, Or, Imp, Sequent, ProofTree
from src.cut_elimination_modular import CutEliminationModular
from src.proof_checker import ProofChecker


class TestCutEliminationModular(unittest.TestCase):
    def setUp(self):
        self.cut_elimination = CutEliminationModular()
        self.checker = ProofChecker("LK")

    def test_formula_degree(self):
        A = Atom("A")
        B = Atom("B")
        self.assertEqual(self.cut_elimination.formula_degree(A), 0)
        self.assertEqual(self.cut_elimination.formula_degree(Not(A)), 1)
        self.assertEqual(self.cut_elimination.formula_degree(And(A, B)), 1)
        self.assertEqual(self.cut_elimination.formula_degree(Imp(A, Not(B))), 2)

    def test_cut_rank(self):
        A = Atom("A")
        # Left: Ax (A |- A), Right: Ax (A |- A)
        ax1 = ProofTree("Ax", Sequent((A,), (A,)))
        ax2 = ProofTree("Ax", Sequent((A,), (A,)))
        cut_node = ProofTree("Cut", Sequent((A,), (A,)), (ax1, ax2), cut_formula=A)
        self.assertEqual(self.cut_elimination.cut_rank(cut_node), 2)

    def test_degree_reduction(self):
        # Principal cut on And(A, B)
        A = Atom("A")
        B = Atom("B")
        AB = And(A, B)

        # Left derivation of |- A /\ B:
        # Premise 1: |- A (or Ax: A |- A)
        p1 = ProofTree("Ax", Sequent((A,), (A,)))
        p2 = ProofTree("Ax", Sequent((B,), (B,)))
        left = ProofTree("R_And", Sequent((A, B), (AB,)), (p1, p2), principal_formula=AB)

        # Right derivation: A /\ B |- A
        p3 = ProofTree("Ax", Sequent((A, B), (A,)))
        right = ProofTree("L_And", Sequent((AB,), (A,)), (p3,), principal_formula=AB)

        cut_proof = ProofTree("Cut", Sequent((A, B), (A,)), (left, right), cut_formula=AB)
        reduced = self.cut_elimination.degree_reduction(cut_proof)

        # Verify degree reduction decomposed cut on AB into cut on A or B
        self.assertTrue(reduced.rule == "Cut")
        self.assertNotEqual(reduced.cut_formula, AB)
        self.assertIn(reduced.cut_formula, (A, B))

    def test_rank_reduction(self):
        A = Atom("A")
        B = Atom("B")
        # Axiom base case rank reduction
        ax1 = ProofTree("Ax", Sequent((A,), (A,)))
        ax2 = ProofTree("Ax", Sequent((A,), (A,)))
        cut_node = ProofTree("Cut", Sequent((A,), (A,)), (ax1, ax2), cut_formula=A)

        reduced = self.cut_elimination.rank_reduction(cut_node)
        self.assertTrue(reduced.is_cut_free())

    def test_eliminate_cuts(self):
        A = Atom("A")
        B = Atom("B")
        AB = And(A, B)

        # Build proof with Cut: (A, B |- A /\ B) Cut (A /\ B |- A) => A, B |- A
        p1 = ProofTree("Ax", Sequent((A,), (A,)))
        p2 = ProofTree("Ax", Sequent((B,), (B,)))
        left = ProofTree("R_And", Sequent((A, B), (AB,)), (p1, p2), principal_formula=AB)

        p3 = ProofTree("Ax", Sequent((A, B), (A,)))
        right = ProofTree("L_And", Sequent((AB,), (A,)), (p3,), principal_formula=AB)

        cut_proof = ProofTree("Cut", Sequent((A, B), (A,)), (left, right), cut_formula=AB)
        self.assertEqual(cut_proof.count_cuts(), 1)

        cut_free = self.cut_elimination.eliminate_cuts(cut_proof)
        self.assertTrue(cut_free.is_cut_free())
        self.assertEqual(cut_free.count_cuts(), 0)

        # Subformula property holds for cut-free proof
        sub_ok, msg = self.checker.verify_subformula_property(cut_free)
        self.assertTrue(sub_ok, msg)


if __name__ == '__main__':
    unittest.main()
