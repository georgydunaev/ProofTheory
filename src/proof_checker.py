# [PROOFTHEORY] Deductive Proof Checker & Subformula Property Verifier
# Part of Ticket 7649: Implement Sound Deductive Proof Checker and Subformula Property Verifier

from typing import Tuple, List, Optional
from collections import Counter
from src.sequent_calculus import Formula, Atom, Not, And, Or, Imp, Sequent, ProofTree


class ProofChecker:
    """Rigorous deductive verifier for Gentzen LK and LJ sequent calculus derivations."""

    def __init__(self, system: str = "LK"):
        if system not in ("LK", "LJ"):
            raise ValueError(f"Unknown logical system '{system}'. Must be 'LK' or 'LJ'.")
        self.system = system

    def verify_proof(self, proof: ProofTree) -> Tuple[bool, str]:
        """Recursively checks that every node in the derivation tree is a valid inference step."""
        # 1. System check: LJ requires at most 1 formula in the succedent of every sequent
        if self.system == "LJ" and not proof.conclusion.is_intuitionistic():
            return False, f"LJ violation: succedent has {len(proof.conclusion.succedent)} formulas (max 1 permitted): {proof.conclusion}"

        # 2. Recursively verify all premise subtrees
        for i, prem in enumerate(proof.premises):
            valid, err = self.verify_proof(prem)
            if not valid:
                return False, f"Invalid premise {i} under rule '{proof.rule}': {err}"

        # 3. Check the rule at this node
        return self._check_rule(proof)

    def verify_subformula_property(self, proof: ProofTree) -> Tuple[bool, str]:
        """Verifies that every formula in the derivation tree is a subformula of the conclusion."""
        if not proof.is_cut_free():
            return False, "Subformula property is only guaranteed for cut-free proofs; proof contains Cut rules."
        
        conclusion_subformulas = proof.conclusion.all_subformulas()
        all_formulas = proof.get_all_formulas_in_proof()
        violators = [f for f in all_formulas if f not in conclusion_subformulas]
        if violators:
            return False, f"Subformula property violated by formulas: {violators}"
        return True, "Subformula property holds: all formulas in proof tree are subformulas of conclusion."

    def _check_rule(self, node: ProofTree) -> Tuple[bool, str]:
        rule = node.rule
        conc = node.conclusion
        prems = node.premises

        if rule == "Ax":
            if len(prems) != 0:
                return False, f"Axiom rule must have 0 premises, got {len(prems)}"
            if not conc.is_axiom():
                return False, f"Sequent {conc} is not an initial identity axiom (A |- A)"
            return True, "Valid Axiom"

        elif rule == "Cut":
            if len(prems) != 2:
                return False, f"Cut requires 2 premises, got {len(prems)}"
            p1, p2 = prems[0].conclusion, prems[1].conclusion
            cut_f = node.cut_formula
            if cut_f is None:
                # Deduce cut formula from right succedent of p1 and left antecedent of p2
                candidates = [f for f in p1.succedent if f in p2.antecedent]
                if not candidates:
                    return False, f"No common cut formula found between {p1} and {p2}"
                cut_f = candidates[0]

            if cut_f not in p1.succedent:
                return False, f"Cut formula {cut_f} missing from left premise succedent: {p1}"
            if cut_f not in p2.antecedent:
                return False, f"Cut formula {cut_f} missing from right premise antecedent: {p2}"

            # Check that conclusion contains remaining formulas
            p1_suc = list(p1.succedent)
            p1_suc.remove(cut_f)
            p2_ant = list(p2.antecedent)
            p2_ant.remove(cut_f)

            expected_ant = set(p1.antecedent) | set(p2_ant)
            expected_suc = set(p1_suc) | set(p2.succedent)
            if not expected_ant.issubset(set(conc.antecedent)):
                return False, f"Cut conclusion missing antecedent formulas: expected subset of {conc.antecedent}"
            if not expected_suc.issubset(set(conc.succedent)):
                return False, f"Cut conclusion missing succedent formulas: expected subset of {conc.succedent}"
            return True, "Valid Cut"

        elif rule == "L_And":
            if len(prems) != 1:
                return False, f"L_And requires 1 premise, got {len(prems)}"
            p = prems[0].conclusion
            # Look for And formula in conclusion's antecedent
            and_formulas = [f for f in conc.antecedent if isinstance(f, And)]
            valid = False
            for af in and_formulas:
                # Premise should have af.left and af.right or either of them in antecedent
                if (af.left in p.antecedent or af.right in p.antecedent or (af.left in p.antecedent and af.right in p.antecedent)):
                    valid = True
                    break
            if not valid:
                return False, f"L_And invalid: no conjunct from conclusion {conc} derived from premise {p}"
            return True, "Valid L_And"

        elif rule == "R_And":
            if len(prems) != 2:
                return False, f"R_And requires 2 premises, got {len(prems)}"
            p1, p2 = prems[0].conclusion, prems[1].conclusion
            and_formulas = [f for f in conc.succedent if isinstance(f, And)]
            valid = False
            for af in and_formulas:
                if af.left in p1.succedent and af.right in p2.succedent:
                    valid = True
                    break
            if not valid:
                return False, f"R_And invalid: conjuncts of {and_formulas} not in premises {p1}, {p2}"
            return True, "Valid R_And"

        elif rule == "L_Or":
            if len(prems) != 2:
                return False, f"L_Or requires 2 premises, got {len(prems)}"
            p1, p2 = prems[0].conclusion, prems[1].conclusion
            or_formulas = [f for f in conc.antecedent if isinstance(f, Or)]
            valid = False
            for of in or_formulas:
                if of.left in p1.antecedent and of.right in p2.antecedent:
                    valid = True
                    break
            if not valid:
                return False, f"L_Or invalid: disjuncts of {or_formulas} not in premises {p1}, {p2}"
            return True, "Valid L_Or"

        elif rule == "R_Or":
            if len(prems) != 1:
                return False, f"R_Or requires 1 premise, got {len(prems)}"
            p = prems[0].conclusion
            or_formulas = [f for f in conc.succedent if isinstance(f, Or)]
            valid = False
            for of in or_formulas:
                if of.left in p.succedent or of.right in p.succedent:
                    valid = True
                    break
            if not valid:
                return False, f"R_Or invalid: disjunct of {or_formulas} not in premise {p}"
            return True, "Valid R_Or"

        elif rule == "L_Imp":
            if len(prems) != 2:
                return False, f"L_Imp requires 2 premises, got {len(prems)}"
            p1, p2 = prems[0].conclusion, prems[1].conclusion
            imp_formulas = [f for f in conc.antecedent if isinstance(f, Imp)]
            valid = False
            for im in imp_formulas:
                if im.left in p1.succedent and im.right in p2.antecedent:
                    valid = True
                    break
            if not valid:
                return False, f"L_Imp invalid: antecedent/consequent of {imp_formulas} not matching {p1}, {p2}"
            return True, "Valid L_Imp"

        elif rule == "R_Imp":
            if len(prems) != 1:
                return False, f"R_Imp requires 1 premise, got {len(prems)}"
            p = prems[0].conclusion
            imp_formulas = [f for f in conc.succedent if isinstance(f, Imp)]
            valid = False
            for im in imp_formulas:
                if im.left in p.antecedent and im.right in p.succedent:
                    valid = True
                    break
            if not valid:
                return False, f"R_Imp invalid: antecedent/consequent of {imp_formulas} not in premise {p}"
            return True, "Valid R_Imp"

        elif rule == "L_Not":
            if len(prems) != 1:
                return False, f"L_Not requires 1 premise, got {len(prems)}"
            p = prems[0].conclusion
            not_formulas = [f for f in conc.antecedent if isinstance(f, Not)]
            valid = any(nf.sub in p.succedent for nf in not_formulas)
            if not valid:
                return False, f"L_Not invalid: negated formula in {not_formulas} not in succedent of premise {p}"
            return True, "Valid L_Not"

        elif rule == "R_Not":
            if len(prems) != 1:
                return False, f"R_Not requires 1 premise, got {len(prems)}"
            p = prems[0].conclusion
            not_formulas = [f for f in conc.succedent if isinstance(f, Not)]
            valid = any(nf.sub in p.antecedent for nf in not_formulas)
            if not valid:
                return False, f"R_Not invalid: negated formula in {not_formulas} not in antecedent of premise {p}"
            return True, "Valid R_Not"

        elif rule in ("L_Weak", "R_Weak", "Weakening"):
            if len(prems) != 1:
                return False, f"Weakening requires 1 premise, got {len(prems)}"
            p = prems[0].conclusion
            if not set(p.antecedent).issubset(set(conc.antecedent)):
                return False, f"Left weakening invalid: {p.antecedent} not subset of {conc.antecedent}"
            if not set(p.succedent).issubset(set(conc.succedent)):
                return False, f"Right weakening invalid: {p.succedent} not subset of {conc.succedent}"
            return True, "Valid Weakening"

        elif rule in ("L_Contr", "R_Contr", "Contraction", "Exchange"):
            if len(prems) != 1:
                return False, f"Contraction/Exchange requires 1 premise, got {len(prems)}"
            p = prems[0].conclusion
            if set(p.antecedent) != set(conc.antecedent) or set(p.succedent) != set(conc.succedent):
                return False, f"Contraction/Exchange invalid: formulas differ between {p} and {conc}"
            return True, "Valid Contraction/Exchange"

        return False, f"Unknown sequent rule '{rule}'"
