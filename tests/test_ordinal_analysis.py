# [PROOFTHEORY] Tests for Ordinal Analysis up to Epsilon-0
# Part of Ticket 7455 / Ticket 7650: Modernize Ordinal Analysis Notation and Proof Tactics

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from src.ordinal_analysis import CNFOrdinal, OrdinalAnalysis


class TestOrdinalAnalysis(unittest.TestCase):
    def test_basic_ordinals(self):
        z = CNFOrdinal.zero()
        one = CNFOrdinal.from_int(1)
        two = CNFOrdinal.from_int(2)
        w = CNFOrdinal.omega()

        self.assertTrue(z.is_zero())
        self.assertFalse(one.is_zero())
        self.assertTrue(one.is_successor())
        self.assertTrue(w.is_limit())

        self.assertTrue(z < one)
        self.assertTrue(one < two)
        self.assertTrue(two < w)

    def test_ordinal_addition(self):
        one = CNFOrdinal.from_int(1)
        w = CNFOrdinal.omega()

        # In ordinal arithmetic: 1 + w = w
        left_add = one + w
        self.assertEqual(left_add, w)

        # But w + 1 > w
        right_add = w + one
        self.assertTrue(right_add > w)
        self.assertEqual(repr(right_add), "w + 1")

    def test_omega_powers(self):
        w = CNFOrdinal.omega()
        w2 = CNFOrdinal.omega_pow(CNFOrdinal.from_int(2))  # w^2
        ww = CNFOrdinal.omega_pow(w)                       # w^w

        self.assertTrue(w < w2)
        self.assertTrue(w2 < ww)

    def test_fundamental_sequences(self):
        w = CNFOrdinal.omega()
        # Fundamental sequence of w should be strictly increasing finite ordinals
        self.assertTrue(OrdinalAnalysis.verify_fundamental_sequence_strictly_increasing(w, steps=5))

        # Test fundamental sequence of w^2
        w2 = CNFOrdinal.omega_pow(CNFOrdinal.from_int(2))
        self.assertTrue(OrdinalAnalysis.verify_fundamental_sequence_strictly_increasing(w2, steps=5))

        # Test fundamental sequence of w^w
        ww = CNFOrdinal.omega_pow(w)
        self.assertTrue(OrdinalAnalysis.verify_fundamental_sequence_strictly_increasing(ww, steps=5))

    def test_peano_bound(self):
        self.assertEqual(OrdinalAnalysis.peano_arithmetic_ordinal_bound(), "epsilon_0")


if __name__ == '__main__':
    unittest.main()
