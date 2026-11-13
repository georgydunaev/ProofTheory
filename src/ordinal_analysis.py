# [PROOFTHEORY] Constructive Ordinal Analysis up to Epsilon-0
# Part of Ticket 7455 / Ticket 7650: Modernize Ordinal Analysis Notation and Proof Tactics

from __future__ import annotations
from typing import Tuple, List, Optional


class CNFOrdinal:
    """
    Constructive representation of ordinals below epsilon_0 in Cantor Normal Form (CNF):
    alpha = omega^(beta_1) * c_1 + omega^(beta_2) * c_2 + ... + omega^(beta_k) * c_k
    where beta_1 > beta_2 > ... > beta_k >= 0 and c_i in Z+ (positive integers).
    """

    def __init__(self, terms: Tuple[Tuple[CNFOrdinal, int], ...] = ()):
        # Normalize: drop zero coefficients and merge identical exponents
        normalized: List[Tuple[CNFOrdinal, int]] = []
        for exp, coeff in terms:
            if coeff <= 0:
                continue
            if normalized and normalized[-1][0] == exp:
                normalized[-1] = (exp, normalized[-1][1] + coeff)
            else:
                normalized.append((exp, coeff))
        # Ensure terms are strictly descending by exponent
        for i in range(len(normalized) - 1):
            if not (normalized[i + 1][0] < normalized[i][0]):
                raise ValueError("Cantor normal form exponents must be strictly decreasing.")
        self.terms = tuple(normalized)

    @classmethod
    def zero(cls) -> CNFOrdinal:
        return cls(())

    @classmethod
    def from_int(cls, n: int) -> CNFOrdinal:
        if n < 0:
            raise ValueError("Ordinals must be non-negative.")
        if n == 0:
            return cls.zero()
        return cls(((cls.zero(), n),))

    @classmethod
    def omega(cls) -> CNFOrdinal:
        """Ordinal omega = omega^1 * 1."""
        return cls(((cls.from_int(1), 1),))

    @classmethod
    def omega_pow(cls, exp: CNFOrdinal) -> CNFOrdinal:
        """Construct omega^exp."""
        return cls(((exp, 1),))

    def is_zero(self) -> bool:
        return len(self.terms) == 0

    def is_successor(self) -> bool:
        if self.is_zero():
            return False
        last_exp, _ = self.terms[-1]
        return last_exp.is_zero()

    def is_limit(self) -> bool:
        return not self.is_zero() and not self.is_successor()

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, CNFOrdinal):
            return False
        return self.terms == other.terms

    def __hash__(self) -> int:
        return hash(self.terms)

    def __lt__(self, other: CNFOrdinal) -> bool:
        # Lexicographical comparison of Cantor normal form terms
        for (e1, c1), (e2, c2) in zip(self.terms, other.terms):
            if e1 != e2:
                return e1 < e2
            if c1 != c2:
                return c1 < c2
        return len(self.terms) < len(other.terms)

    def __le__(self, other: CNFOrdinal) -> bool:
        return self == other or self < other

    def __gt__(self, other: CNFOrdinal) -> bool:
        return not (self <= other)

    def __ge__(self, other: CNFOrdinal) -> bool:
        return not (self < other)

    def __add__(self, other: CNFOrdinal) -> CNFOrdinal:
        """Ordinal addition: alpha + beta."""
        if self.is_zero():
            return other
        if other.is_zero():
            return self

        other_leading_exp = other.terms[0][0]
        other_leading_coeff = other.terms[0][1]
        kept_terms: List[Tuple[CNFOrdinal, int]] = []
        merged = False
        for exp, coeff in self.terms:
            if exp > other_leading_exp:
                kept_terms.append((exp, coeff))
            elif exp == other_leading_exp:
                kept_terms.append((exp, coeff + other_leading_coeff))
                merged = True
                break
            else:
                break

        if not merged:
            kept_terms.append(other.terms[0])

        # Append remaining terms of other
        kept_terms.extend(other.terms[1:])
        return CNFOrdinal(tuple(kept_terms))

    def fundamental_sequence(self, n: int) -> CNFOrdinal:
        """
        Computes the n-th element of the fundamental sequence alpha[n] for limit ordinals.
        For successor ordinals alpha = gamma + 1, alpha[n] = gamma.
        For 0, returns 0.
        """
        if self.is_zero():
            return CNFOrdinal.zero()

        if self.is_successor():
            # Drop 1 from last coefficient
            head = list(self.terms[:-1])
            last_exp, last_c = self.terms[-1]
            if last_c > 1:
                head.append((last_exp, last_c - 1))
            return CNFOrdinal(tuple(head))

        # self is a limit ordinal
        head = list(self.terms[:-1])
        last_exp, last_c = self.terms[-1]

        if last_c > 1:
            # (alpha + omega^beta * c)[n] = alpha + omega^beta * (c - 1) + (omega^beta)[n]
            rem = CNFOrdinal(((last_exp, last_c - 1),))
            omega_part = CNFOrdinal(((last_exp, 1),)).fundamental_sequence(n)
            return CNFOrdinal(tuple(head)) + rem + omega_part

        # Here last_c == 1: we compute (omega^beta)[n]
        if last_exp.is_successor():
            # omega^(gamma + 1)[n] = omega^gamma * (n + 1)
            gamma = last_exp.fundamental_sequence(0)
            tail = CNFOrdinal(((gamma, n + 1),))
            return CNFOrdinal(tuple(head)) + tail

        if last_exp.is_limit():
            # omega^beta[n] = omega^(beta[n])
            beta_n = last_exp.fundamental_sequence(n)
            tail = CNFOrdinal(((beta_n, 1),))
            return CNFOrdinal(tuple(head)) + tail

        return CNFOrdinal(tuple(head))

    def __repr__(self) -> str:
        if self.is_zero():
            return "0"
        parts = []
        for exp, coeff in self.terms:
            if exp.is_zero():
                parts.append(str(coeff))
            elif exp == CNFOrdinal.from_int(1):
                parts.append("w" if coeff == 1 else f"w*{coeff}")
            else:
                base = f"w^({exp})"
                parts.append(base if coeff == 1 else f"{base}*{coeff}")
        return " + ".join(parts)


class OrdinalAnalysis:
    """Proof-theoretic ordinal verification routines for arithmetic and sequent derivations."""

    @staticmethod
    def verify_fundamental_sequence_strictly_increasing(alpha: CNFOrdinal, steps: int = 5) -> bool:
        """Verifies that alpha[0] < alpha[1] < ... < alpha for a limit ordinal."""
        if not alpha.is_limit():
            return True
        prev = alpha.fundamental_sequence(0)
        for i in range(1, steps):
            curr = alpha.fundamental_sequence(i)
            if not (prev < curr):
                return False
            if not (curr < alpha):
                return False
            prev = curr
        return True

    @staticmethod
    def peano_arithmetic_ordinal_bound() -> str:
        """Returns the proof-theoretic ordinal of First-Order Peano Arithmetic."""
        return "epsilon_0"
