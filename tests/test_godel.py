# [PROOFTHEORY] Unit Tests for Gödel's First Incompleteness Theorem
# Part of Ticket 7653: Mechanization of Gödel's First Incompleteness Theorem for Q and PA

import unittest
from src.godel_incompleteness import (
    Term, Var, Zero, Succ, Numeral, Plus, Mult, numeral, eval_term_val,
    Formula, Eq, Not, And, Or, Imp, All, Ex, Iff, Bot,
    subst_term, subst_form,
    cantor_pair, cantor_unpair,
    godel_number_term, decode_term,
    godel_number_formula, decode_formula, code_numeral,
    diagonal_subst, diagonal_lemma,
    robinson_axioms, DerivationStep, ArithProofChecker,
    GodelIncompletenessMachine
)


class TestFirstOrderSyntax(unittest.TestCase):
    def test_term_constructors_and_free_vars(self):
        v = Var("x")
        self.assertEqual(v.free_variables(), {"x"})
        z = Zero()
        self.assertEqual(z.free_variables(), set())
        s = Succ(v)
        self.assertEqual(s.free_variables(), {"x"})
        p = Plus(v, Numeral(3))
        self.assertEqual(p.free_variables(), {"x"})
        m = Mult(Var("y"), p)
        self.assertEqual(m.free_variables(), {"x", "y"})

    def test_numeral_and_evaluation(self):
        num0 = numeral(0)
        self.assertEqual(eval_term_val(num0, {}), 0)
        num5 = numeral(5)
        self.assertEqual(eval_term_val(num5, {}), 5)
        env = {"x": 7, "y": 3}
        expr = Plus(Var("x"), Mult(Var("y"), Numeral(2)))
        self.assertEqual(eval_term_val(expr, env), 13)

    def test_formula_constructors_and_free_vars(self):
        f1 = Eq(Var("x"), Zero())
        self.assertEqual(f1.free_variables(), {"x"})
        f2 = All("x", Eq(Var("x"), Var("x")))
        self.assertEqual(f2.free_variables(), set())
        f3 = Ex("y", Eq(Var("x"), Var("y")))
        self.assertEqual(f3.free_variables(), {"x"})
        f4 = Imp(f1, f3)
        self.assertEqual(f4.free_variables(), {"x"})
        f_iff = Iff(f1, f3)
        self.assertIsInstance(f_iff, And)
        bot = Bot()
        self.assertIsInstance(bot, Eq)
        self.assertEqual(bot.free_variables(), set())


class TestSyntacticSubstitution(unittest.TestCase):
    def test_subst_term(self):
        t = Plus(Var("x"), Mult(Var("y"), Var("x")))
        res = subst_term(t, "x", Numeral(2))
        expected = Plus(Numeral(2), Mult(Var("y"), Numeral(2)))
        self.assertEqual(res, expected)

    def test_subst_form_basic(self):
        phi = Eq(Plus(Var("x"), Zero()), Var("x"))
        res = subst_form(phi, "x", Numeral(5))
        expected = Eq(Plus(Numeral(5), Zero()), Numeral(5))
        self.assertEqual(res, expected)

    def test_subst_form_quantifier_binding(self):
        # Bound variable should not be substituted
        phi = All("x", Eq(Var("x"), Var("y")))
        res = subst_form(phi, "x", Numeral(10))
        self.assertEqual(res, phi)

        # Free variable inside quantifier should be substituted
        res2 = subst_form(phi, "y", Numeral(10))
        expected2 = All("x", Eq(Var("x"), Numeral(10)))
        self.assertEqual(res2, expected2)


class TestGodelNumbering(unittest.TestCase):
    def test_cantor_pairing_bijection(self):
        test_pairs = [
            (0, 0), (0, 1), (1, 0), (1, 1), (2, 3), (7, 11),
            (42, 99), (123, 456), (1000, 2000)
        ]
        for a, b in test_pairs:
            z = cantor_pair(a, b)
            a_rec, b_rec = cantor_unpair(z)
            self.assertEqual((a_rec, b_rec), (a, b), f"Cantor unpairing failed for ({a}, {b})")

    def test_term_godel_roundtrip(self):
        terms = [
            Zero(),
            Numeral(0),
            Numeral(100),
            Var(0),
            Var("x"),
            Succ(Var(1)),
            Plus(Var("x"), Numeral(42)),
            Mult(Plus(Numeral(1), Var("y")), Succ(Zero()))
        ]
        for t in terms:
            code = godel_number_term(t)
            self.assertGreater(code, 0)
            decoded = decode_term(code)
            self.assertEqual(decoded, t, f"Term decoding mismatch for {t}")

    def test_formula_godel_roundtrip(self):
        formulas = [
            Eq(Zero(), Zero()),
            Not(Eq(Succ(Zero()), Zero())),
            And(Eq(Var("x"), Zero()), Eq(Var("y"), Numeral(1))),
            Or(Eq(Var(0), Zero()), Ex(1, Eq(Var(0), Succ(Var(1))))),
            Imp(Eq(Var("x"), Numeral(2)), Eq(Mult(Var("x"), Var("x")), Numeral(4))),
            All("x", Eq(Plus(Var("x"), Zero()), Var("x"))),
            Ex("y", Eq(Var("y"), Succ(Zero())))
        ]
        for f in formulas:
            code = godel_number_formula(f)
            self.assertGreater(code, 0)
            decoded = decode_formula(code)
            self.assertEqual(decoded, f, f"Formula decoding mismatch for {f}")

    def test_distinct_codes_for_distinct_formulas(self):
        f1 = Eq(Var("x"), Zero())
        f2 = Eq(Var("x"), Succ(Zero()))
        f3 = Eq(Var("y"), Zero())
        codes = {godel_number_formula(f1), godel_number_formula(f2), godel_number_formula(f3)}
        self.assertEqual(len(codes), 3, "Codes must be distinct for distinct formulas.")


class TestDiagonalLemma(unittest.TestCase):
    def test_diagonal_subst(self):
        phi = Eq(Var(0), Zero())
        code_phi = godel_number_formula(phi)
        diag = diagonal_subst(phi, 0)
        expected = Eq(numeral(code_phi), Zero())
        self.assertEqual(diag, expected)

    def test_diagonal_lemma_fixed_point(self):
        psi = Not(Eq(Var(0), Numeral(42)))
        G, biconditional = diagonal_lemma(psi, 0)
        gn_G = godel_number_formula(G)
        # biconditional is G <-> psi(numeral(gn(G)))
        expected_target = subst_form(psi, 0, numeral(gn_G))
        self.assertEqual(biconditional, Iff(G, expected_target))
        self.assertIsInstance(biconditional, And)


class TestRobinsonAndPeanoProofSystem(unittest.TestCase):
    def setUp(self):
        self.q_checker = ArithProofChecker("Q")
        self.pa_checker = ArithProofChecker("PA")

    def test_robinson_axioms_presence(self):
        axioms = robinson_axioms()
        for i in range(1, 8):
            self.assertIn(f"Q{i}", axioms)

    def test_valid_q_axiom_proof(self):
        q4 = robinson_axioms()["Q4"]
        steps = [DerivationStep(rule="Q4", formula=q4)]
        valid, msg = self.q_checker.check_proof(steps)
        self.assertTrue(valid, msg)

    def test_valid_modus_ponens_proof(self):
        ante = Eq(Numeral(2), Numeral(2))
        cons = Eq(Numeral(4), Numeral(4))
        imp = Imp(ante, cons)
        steps = [
            DerivationStep(rule="EqRefl", formula=ante),
            DerivationStep(rule="Hypothesis", formula=imp),
            DerivationStep(rule="MP", formula=cons, premises=[1, 0])
        ]
        valid, msg = self.q_checker.check_proof(steps)
        self.assertTrue(valid, msg)

    def test_invalid_modus_ponens_mismatch(self):
        f1 = Eq(Zero(), Zero())
        f2 = Eq(Succ(Zero()), Succ(Zero()))
        imp = Imp(f1, f2)
        wrong = Eq(Zero(), Succ(Zero()))
        steps = [
            DerivationStep(rule="EqRefl", formula=f1),
            DerivationStep(rule="Hypothesis", formula=imp),
            DerivationStep(rule="MP", formula=wrong, premises=[1, 0])
        ]
        valid, msg = self.q_checker.check_proof(steps)
        self.assertFalse(valid)

    def test_induction_disallowed_in_q(self):
        f = All("x", Eq(Var("x"), Var("x")))
        steps = [DerivationStep(rule="PA_Induction", formula=f)]
        valid, msg = self.q_checker.check_proof(steps)
        self.assertFalse(valid)
        self.assertIn("Induction rule is only available in PA", msg)


class TestGodelIncompletenessMachine(unittest.TestCase):
    def setUp(self):
        self.machine_q = GodelIncompletenessMachine("Q")
        self.machine_pa = GodelIncompletenessMachine("PA")

    def test_proof_registration_and_checking(self):
        ante = Eq(Numeral(1), Numeral(1))
        steps = [DerivationStep(rule="EqRefl", formula=ante)]
        p_code, f_code = self.machine_q.register_proof(steps)
        self.assertTrue(self.machine_q.prf(p_code, f_code))
        self.assertFalse(self.machine_q.prf(p_code, f_code + 1))
        self.assertFalse(self.machine_q.prf(p_code + 99, f_code))

    def test_godel_sentence_construction(self):
        G, fp, gn_G = self.machine_q.construct_godel_sentence()
        self.assertIsInstance(G, Not)
        self.assertIsInstance(G.sub, Ex)
        self.assertGreater(gn_G, 0)
        self.assertIsInstance(fp, And)

    def test_incompleteness_verification_q(self):
        report = self.machine_q.verify_incompleteness()
        self.assertEqual(report["system"], "Q")
        self.assertTrue(report["unprovable_G"])
        self.assertTrue(report["unprovable_not_G"])
        self.assertTrue(report["is_independent"])

    def test_incompleteness_verification_pa(self):
        report = self.machine_pa.verify_incompleteness()
        self.assertEqual(report["system"], "PA")
        self.assertTrue(report["unprovable_G"])
        self.assertTrue(report["unprovable_not_G"])
        self.assertTrue(report["is_independent"])

    def test_unprovability_holds_after_registering_other_proofs(self):
        # Register a valid theorem (e.g. Q4)
        q4 = robinson_axioms()["Q4"]
        self.machine_q.register_proof([DerivationStep(rule="Q4", formula=q4)])

        # Verify Gödel sentence G remains unprovable and independent
        report = self.machine_q.verify_incompleteness()
        self.assertTrue(report["is_independent"])


if __name__ == "__main__":
    unittest.main()
