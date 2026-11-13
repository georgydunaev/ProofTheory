# [PROOFTHEORY] Sequent Calculus Core: Formulas, Sequents, and LK/LJ Proof Trees
# Part of Ticket 7646: Implement Gentzen Sequent Calculus Proof Trees and Validation

from __future__ import annotations
from dataclasses import dataclass
from typing import Tuple, Set, Optional, List, Dict, Any


# ---------------------------------------------------------------------------
# Formulas
# ---------------------------------------------------------------------------

class Formula:
    """Abstract base class for propositional and first-order formulas."""

    def subformulas(self) -> Set[Formula]:
        raise NotImplementedError

    def complexity(self) -> int:
        """Formula degree / logical complexity (number of connectives)."""
        raise NotImplementedError

    def __lt__(self, other: Formula) -> bool:
        return repr(self) < repr(other)


@dataclass(frozen=True)
class Atom(Formula):
    name: str

    def subformulas(self) -> Set[Formula]:
        return {self}

    def complexity(self) -> int:
        return 0

    def __repr__(self) -> str:
        return self.name


@dataclass(frozen=True)
class Not(Formula):
    sub: Formula

    def subformulas(self) -> Set[Formula]:
        return {self} | self.sub.subformulas()

    def complexity(self) -> int:
        return 1 + self.sub.complexity()

    def __repr__(self) -> str:
        return f"~{self.sub}" if isinstance(self.sub, Atom) else f"~({self.sub})"


@dataclass(frozen=True)
class And(Formula):
    left: Formula
    right: Formula

    def subformulas(self) -> Set[Formula]:
        return {self} | self.left.subformulas() | self.right.subformulas()

    def complexity(self) -> int:
        return 1 + self.left.complexity() + self.right.complexity()

    def __repr__(self) -> str:
        return f"({self.left} /\\ {self.right})"


@dataclass(frozen=True)
class Or(Formula):
    left: Formula
    right: Formula

    def subformulas(self) -> Set[Formula]:
        return {self} | self.left.subformulas() | self.right.subformulas()

    def complexity(self) -> int:
        return 1 + self.left.complexity() + self.right.complexity()

    def __repr__(self) -> str:
        return f"({self.left} \\/ {self.right})"


@dataclass(frozen=True)
class Imp(Formula):
    left: Formula
    right: Formula

    def subformulas(self) -> Set[Formula]:
        return {self} | self.left.subformulas() | self.right.subformulas()

    def complexity(self) -> int:
        return 1 + self.left.complexity() + self.right.complexity()

    def __repr__(self) -> str:
        return f"({self.left} -> {self.right})"


# ---------------------------------------------------------------------------
# Sequents: Gamma |- Delta
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Sequent:
    """A sequent Gamma |- Delta where Gamma, Delta are multisets represented as tuples."""
    antecedent: Tuple[Formula, ...]
    succedent: Tuple[Formula, ...]

    def __init__(self, antecedent: Any = (), succedent: Any = ()):
        ant = tuple(antecedent) if not isinstance(antecedent, tuple) else antecedent
        suc = tuple(succedent) if not isinstance(succedent, tuple) else succedent
        object.__setattr__(self, "antecedent", ant)
        object.__setattr__(self, "succedent", suc)

    def is_axiom(self) -> bool:
        """True if antecedent and succedent share at least one formula."""
        return any(f in self.succedent for f in self.antecedent)

    def is_intuitionistic(self) -> bool:
        """In LJ, succedent has at most one formula."""
        return len(self.succedent) <= 1

    def all_formulas(self) -> Set[Formula]:
        return set(self.antecedent) | set(self.succedent)

    def all_subformulas(self) -> Set[Formula]:
        res: Set[Formula] = set()
        for f in self.all_formulas():
            res |= f.subformulas()
        return res

    def __repr__(self) -> str:
        ant_str = ", ".join(str(f) for f in self.antecedent) if self.antecedent else ""
        suc_str = ", ".join(str(f) for f in self.succedent) if self.succedent else ""
        return f"{ant_str} |- {suc_str}"


# ---------------------------------------------------------------------------
# Proof Trees
# ---------------------------------------------------------------------------

class ProofTree:
    """Represents a derivation tree in Gentzen sequent calculus LK or LJ."""

    def __init__(
        self,
        rule: str,
        conclusion: Sequent,
        premises: Tuple[ProofTree, ...] = (),
        principal_formula: Optional[Formula] = None,
        cut_formula: Optional[Formula] = None,
    ):
        self.rule = rule
        self.conclusion = conclusion
        self.premises = tuple(premises)
        self.principal_formula = principal_formula
        self.cut_formula = cut_formula

    def depth(self) -> int:
        if not self.premises:
            return 1
        return 1 + max(p.depth() for p in self.premises)

    def count_cuts(self) -> int:
        c = 1 if self.rule == "Cut" else 0
        return c + sum(p.count_cuts() for p in self.premises)

    def is_cut_free(self) -> bool:
        return self.count_cuts() == 0

    def get_all_formulas_in_proof(self) -> Set[Formula]:
        formulas = set(self.conclusion.all_formulas())
        for p in self.premises:
            formulas |= p.get_all_formulas_in_proof()
        return formulas

    def satisfies_subformula_property(self) -> bool:
        """In cut-free proofs, every formula in the proof is a subformula of the conclusion."""
        conclusion_subformulas = self.conclusion.all_subformulas()
        proof_formulas = self.get_all_formulas_in_proof()
        return proof_formulas.issubset(conclusion_subformulas)

    def __repr__(self) -> str:
        prem_str = ", ".join(f"[{p.rule}: {p.conclusion}]" for p in self.premises)
        return f"ProofTree({self.rule}: {prem_str} => {self.conclusion})"
