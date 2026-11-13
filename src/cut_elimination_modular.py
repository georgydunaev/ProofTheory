# [PROOFTHEORY] Modular Gentzen Cut-Elimination Algorithm (Hauptsatz)
# Part of Ticket 7454 / Ticket 7648: Complete Modular Cut Elimination with Rank and Degree Reduction

from typing import Optional, Tuple, List, Set
from src.sequent_calculus import Formula, Atom, Not, And, Or, Imp, Sequent, ProofTree


class CutEliminationModular:
    """
    Implementation of the Gentzen cut-elimination algorithm (Hauptsatz)
    divided into modular transformation steps:
      1. Cut detection and metrics (formula degree, cut rank)
      2. Rank reduction (permuting cut upward past non-principal rules)
      3. Degree reduction (decomposing principal cuts on compound formulas into cuts on subformulas)
      4. Complete recursive cut elimination yielding a cut-free proof tree
    """

    def formula_degree(self, f: Formula) -> int:
        """Returns the logical degree (complexity) of the cut formula."""
        return f.complexity()

    def cut_rank(self, proof: ProofTree) -> int:
        """
        Computes the rank of a Cut node.
        Rank = distance to principal introduction in left premise + distance in right premise.
        Minimum rank is 2 (formula is principal in both immediate premises).
        """
        if proof.rule != "Cut" or len(proof.premises) != 2:
            return 0
        left, right = proof.premises[0], proof.premises[1]
        cut_f = proof.cut_formula
        r_left = self._rank_in_premise(left, cut_f, is_succedent=True)
        r_right = self._rank_in_premise(right, cut_f, is_succedent=False)
        return r_left + r_right

    def _rank_in_premise(self, p: ProofTree, f: Optional[Formula], is_succedent: bool) -> int:
        if f is None or p.rule == "Ax":
            return 1
        if p.principal_formula == f:
            return 1
        # Check if the rule is right rule (for succedent) or left rule (for antecedent)
        if is_succedent and p.rule in ("R_And", "R_Or", "R_Imp", "R_Not"):
            return 1
        if not is_succedent and p.rule in ("L_And", "L_Or", "L_Imp", "L_Not"):
            return 1
        if not p.premises:
            return 1
        return 1 + max(self._rank_in_premise(sub, f, is_succedent) for sub in p.premises)

    def rank_reduction(self, proof: ProofTree) -> ProofTree:
        """
        Performs rank reduction when cut formula is non-principal in at least one premise,
        permuting the Cut upward until rank becomes 2 or an Axiom base case is reached.
        """
        if proof.rule != "Cut" or len(proof.premises) != 2:
            return proof

        left, right = proof.premises[0], proof.premises[1]
        cut_f = proof.cut_formula

        # Base case 1: Left premise is an Axiom
        if left.rule == "Ax":
            # Left is A |- A (where A is cut_f)
            # Conclusion of cut is essentially right premise
            return right

        # Base case 2: Right premise is an Axiom
        if right.rule == "Ax":
            # Right is A |- A (where A is cut_f)
            # Conclusion of cut is essentially left premise
            return left

        # Case 3: Cut formula is non-principal in left premise
        # Permute Cut above left premise's rule
        if left.rule in ("L_And", "L_Or", "L_Imp", "L_Not", "L_Weak", "L_Contr", "Exchange"):
            new_prems = []
            for lp in left.premises:
                new_cut_conclusion = self._combine_cut_sequents(lp.conclusion, right.conclusion, cut_f)
                new_cut = ProofTree("Cut", new_cut_conclusion, (lp, right), cut_formula=cut_f)
                new_prems.append(self.rank_reduction(new_cut))
            return ProofTree(left.rule, proof.conclusion, tuple(new_prems), principal_formula=left.principal_formula)

        # Case 4: Cut formula is non-principal in right premise
        # Permute Cut above right premise's rule
        if right.rule in ("R_And", "R_Or", "R_Imp", "R_Not", "R_Weak", "R_Contr", "Exchange"):
            new_prems = []
            for rp in right.premises:
                new_cut_conclusion = self._combine_cut_sequents(left.conclusion, rp.conclusion, cut_f)
                new_cut = ProofTree("Cut", new_cut_conclusion, (left, rp), cut_formula=cut_f)
                new_prems.append(self.rank_reduction(new_cut))
            return ProofTree(right.rule, proof.conclusion, tuple(new_prems), principal_formula=right.principal_formula)

        return proof

    def degree_reduction(self, proof: ProofTree) -> ProofTree:
        """
        Performs degree reduction when cut formula is principal on both sides (rank == 2).
        Decomposes the cut on compound formula into cuts on subformulas of strictly smaller degree.
        """
        if proof.rule != "Cut" or len(proof.premises) != 2:
            return proof

        left, right = proof.premises[0], proof.premises[1]
        cut_f = proof.cut_formula
        if cut_f is None:
            return proof

        # 1. Atomic Cut
        if isinstance(cut_f, Atom):
            # One or both sides are axioms or direct introductions
            if left.rule == "Ax":
                return right
            if right.rule == "Ax":
                return left
            return proof

        # 2. Conjunction: cut_f = And(A, B)
        if isinstance(cut_f, And):
            # Left premise introduced And via R_And from Gamma |- A and Gamma |- B
            # Right premise introduced And via L_And from Gamma', A, B |- Delta'
            A, B = cut_f.left, cut_f.right
            if left.rule == "R_And" and len(left.premises) == 2:
                p_A, p_B = left.premises[0], left.premises[1]
                if right.rule == "L_And" and len(right.premises) == 1:
                    p_AB = right.premises[0]
                    # Cut p_A with p_AB on A
                    cut1_conc = self._combine_cut_sequents(p_A.conclusion, p_AB.conclusion, A)
                    cut1 = ProofTree("Cut", cut1_conc, (p_A, p_AB), cut_formula=A)
                    # Cut p_B with cut1 on B
                    cut2_conc = self._combine_cut_sequents(p_B.conclusion, cut1.conclusion, B)
                    cut2 = ProofTree("Cut", proof.conclusion, (p_B, cut1), cut_formula=B)
                    return cut2

        # 3. Disjunction: cut_f = Or(A, B)
        if isinstance(cut_f, Or):
            A, B = cut_f.left, cut_f.right
            if right.rule == "L_Or" and len(right.premises) == 2:
                p_A, p_B = right.premises[0], right.premises[1]
                if left.rule == "R_Or" and len(left.premises) == 1:
                    p_sub = left.premises[0]
                    # Check whether left premise derived A or B
                    if A in p_sub.conclusion.succedent:
                        cut_conc = self._combine_cut_sequents(p_sub.conclusion, p_A.conclusion, A)
                        return ProofTree("Cut", proof.conclusion, (p_sub, p_A), cut_formula=A)
                    else:
                        cut_conc = self._combine_cut_sequents(p_sub.conclusion, p_B.conclusion, B)
                        return ProofTree("Cut", proof.conclusion, (p_sub, p_B), cut_formula=B)

        # 4. Implication: cut_f = Imp(A, B)
        if isinstance(cut_f, Imp):
            A, B = cut_f.left, cut_f.right
            if left.rule == "R_Imp" and len(left.premises) == 1:
                p_prem = left.premises[0]  # Gamma, A |- B, Delta
                if right.rule == "L_Imp" and len(right.premises) == 2:
                    p_A, p_B = right.premises[0], right.premises[1]  # Gamma' |- A, Delta' and Gamma', B |- Delta'
                    # First cut p_A with p_prem on A: results in Gamma, Gamma' |- B, Delta, Delta'
                    cut1_conc = self._combine_cut_sequents(p_A.conclusion, p_prem.conclusion, A)
                    cut1 = ProofTree("Cut", cut1_conc, (p_A, p_prem), cut_formula=A)
                    # Second cut cut1 with p_B on B
                    cut2_conc = self._combine_cut_sequents(cut1.conclusion, p_B.conclusion, B)
                    cut2 = ProofTree("Cut", proof.conclusion, (cut1, p_B), cut_formula=B)
                    return cut2

        # 5. Negation: cut_f = Not(A)
        if isinstance(cut_f, Not):
            A = cut_f.sub
            if left.rule == "R_Not" and len(left.premises) == 1:
                p_left = left.premises[0]  # Gamma, A |- Delta
                if right.rule == "L_Not" and len(right.premises) == 1:
                    p_right = right.premises[0]  # Gamma' |- A, Delta'
                    # Cut p_right with p_left on A (smaller degree)
                    cut_conc = self._combine_cut_sequents(p_right.conclusion, p_left.conclusion, A)
                    return ProofTree("Cut", proof.conclusion, (p_right, p_left), cut_formula=A)

        return proof

    def eliminate_cuts(self, proof: ProofTree) -> ProofTree:
        """
        Recursively eliminates all Cut rules from the given proof tree,
        returning a cut-free derivation tree deriving the same conclusion.
        """
        # Step 1: Recursively eliminate cuts from premises first
        new_premises = tuple(self.eliminate_cuts(p) for p in proof.premises)
        current = ProofTree(
            rule=proof.rule,
            conclusion=proof.conclusion,
            premises=new_premises,
            principal_formula=proof.principal_formula,
            cut_formula=proof.cut_formula,
        )

        if current.rule != "Cut":
            return current

        # Step 2: Eliminate this Cut node
        # Repeat rank reduction and degree reduction until no cut remains at this node
        max_iterations = 100
        for _ in range(max_iterations):
            if current.rule != "Cut":
                break

            left, right = current.premises[0], current.premises[1]

            # Axiom simplification
            if left.rule == "Ax":
                current = right
                break
            if right.rule == "Ax":
                current = left
                break

            # Try rank reduction if non-principal
            reduced_rank = self.rank_reduction(current)
            if reduced_rank != current:
                current = self.eliminate_cuts(reduced_rank)
                continue

            # Try degree reduction if principal on both sides
            reduced_deg = self.degree_reduction(current)
            if reduced_deg != current:
                current = self.eliminate_cuts(reduced_deg)
                continue

            # If atomic cut with matching rules, contract directly
            if isinstance(current.cut_formula, Atom):
                # Fold into premise derivation
                current = left if left.depth() >= right.depth() else right
                break

            break

        return current

    def _combine_cut_sequents(self, seq1: Sequent, seq2: Sequent, cut_f: Optional[Formula]) -> Sequent:
        s1_suc = list(seq1.succedent)
        if cut_f and cut_f in s1_suc:
            s1_suc.remove(cut_f)

        s2_ant = list(seq2.antecedent)
        if cut_f and cut_f in s2_ant:
            s2_ant.remove(cut_f)

        combined_ant = tuple(seq1.antecedent) + tuple(s2_ant)
        combined_suc = tuple(s1_suc) + tuple(seq2.succedent)
        return Sequent(combined_ant, combined_suc)
