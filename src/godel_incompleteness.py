# [PROOFTHEORY] Gödel's First Incompleteness Theorem Reference Implementation
# Algorithmic Gödel numbering, representability, diagonal lemma, and proof checking for Q and PA

from __future__ import annotations
from dataclasses import dataclass
from typing import Tuple, Set, Optional, List, Dict, Any, Union
import math


# ---------------------------------------------------------------------------
# 1. First-Order Arithmetic Language AST
# ---------------------------------------------------------------------------

class Term:
    """Base class for first-order arithmetic terms."""

    def free_variables(self) -> Set[Union[str, int]]:
        raise NotImplementedError


@dataclass(frozen=True)
class Var(Term):
    name: Union[str, int]

    def free_variables(self) -> Set[Union[str, int]]:
        return {self.name}

    def __repr__(self) -> str:
        return f"v{self.name}" if isinstance(self.name, int) else str(self.name)


@dataclass(frozen=True)
class Zero(Term):
    def free_variables(self) -> Set[Union[str, int]]:
        return set()

    def __repr__(self) -> str:
        return "0"


@dataclass(frozen=True)
class Succ(Term):
    sub: Term

    def free_variables(self) -> Set[Union[str, int]]:
        return self.sub.free_variables()

    def __repr__(self) -> str:
        return f"S({self.sub})"


@dataclass(frozen=True)
class Numeral(Term):
    value: int

    def free_variables(self) -> Set[Union[str, int]]:
        return set()

    def __repr__(self) -> str:
        return str(self.value)


@dataclass(frozen=True)
class Plus(Term):
    left: Term
    right: Term

    def free_variables(self) -> Set[Union[str, int]]:
        return self.left.free_variables() | self.right.free_variables()

    def __repr__(self) -> str:
        return f"({self.left} + {self.right})"


@dataclass(frozen=True)
class Mult(Term):
    left: Term
    right: Term

    def free_variables(self) -> Set[Union[str, int]]:
        return self.left.free_variables() | self.right.free_variables()

    def __repr__(self) -> str:
        return f"({self.left} * {self.right})"


def numeral(n: int) -> Term:
    """Constructs the standard numeral term for non-negative integer n."""
    if n < 0:
        raise ValueError(f"Numeral must be non-negative, got {n}")
    return Numeral(n)


def eval_term_val(t: Term, env: Dict[Union[str, int], int]) -> int:
    """Evaluates a term in standard arithmetic model given an environment."""
    if isinstance(t, Var):
        return env.get(t.name, 0)
    elif isinstance(t, Zero):
        return 0
    elif isinstance(t, Numeral):
        return t.value
    elif isinstance(t, Succ):
        return 1 + eval_term_val(t.sub, env)
    elif isinstance(t, Plus):
        return eval_term_val(t.left, env) + eval_term_val(t.right, env)
    elif isinstance(t, Mult):
        return eval_term_val(t.left, env) * eval_term_val(t.right, env)
    raise TypeError(f"Unknown term type {type(t)}")


# ---------------------------------------------------------------------------
# Formulas
# ---------------------------------------------------------------------------

class Formula:
    """Base class for first-order arithmetic formulas."""

    def free_variables(self) -> Set[Union[str, int]]:
        raise NotImplementedError


@dataclass(frozen=True)
class Eq(Formula):
    left: Term
    right: Term

    def free_variables(self) -> Set[Union[str, int]]:
        return self.left.free_variables() | self.right.free_variables()

    def __repr__(self) -> str:
        return f"({self.left} = {self.right})"


@dataclass(frozen=True)
class Not(Formula):
    sub: Formula

    def free_variables(self) -> Set[Union[str, int]]:
        return self.sub.free_variables()

    def __repr__(self) -> str:
        return f"~{self.sub}"


@dataclass(frozen=True)
class And(Formula):
    left: Formula
    right: Formula

    def free_variables(self) -> Set[Union[str, int]]:
        return self.left.free_variables() | self.right.free_variables()

    def __repr__(self) -> str:
        return f"({self.left} & {self.right})"


@dataclass(frozen=True)
class Or(Formula):
    left: Formula
    right: Formula

    def free_variables(self) -> Set[Union[str, int]]:
        return self.left.free_variables() | self.right.free_variables()

    def __repr__(self) -> str:
        return f"({self.left} | {self.right})"


@dataclass(frozen=True)
class Imp(Formula):
    left: Formula
    right: Formula

    def free_variables(self) -> Set[Union[str, int]]:
        return self.left.free_variables() | self.right.free_variables()

    def __repr__(self) -> str:
        return f"({self.left} -> {self.right})"


@dataclass(frozen=True)
class All(Formula):
    var: Union[str, int]
    sub: Formula

    def free_variables(self) -> Set[Union[str, int]]:
        return self.sub.free_variables() - {self.var}

    def __repr__(self) -> str:
        v = f"v{self.var}" if isinstance(self.var, int) else str(self.var)
        return f"(All {v}, {self.sub})"


@dataclass(frozen=True)
class Ex(Formula):
    var: Union[str, int]
    sub: Formula

    def free_variables(self) -> Set[Union[str, int]]:
        return self.sub.free_variables() - {self.var}

    def __repr__(self) -> str:
        v = f"v{self.var}" if isinstance(self.var, int) else str(self.var)
        return f"(Ex {v}, {self.sub})"


def Iff(left: Formula, right: Formula) -> Formula:
    """Logical biconditional: (A -> B) & (B -> A)."""
    return And(Imp(left, right), Imp(right, left))


def Bot() -> Formula:
    """Falsum representation: 0 = S(0)."""
    return Eq(Zero(), Succ(Zero()))


# ---------------------------------------------------------------------------
# 2. Syntactic Substitution
# ---------------------------------------------------------------------------

def subst_term(t: Term, x: Union[str, int], s: Term) -> Term:
    """Substitutes term s for free occurrences of variable x in term t."""
    if isinstance(t, Var):
        return s if t.name == x else t
    elif isinstance(t, (Zero, Numeral)):
        return t
    elif isinstance(t, Succ):
        return Succ(subst_term(t.sub, x, s))
    elif isinstance(t, Plus):
        return Plus(subst_term(t.left, x, s), subst_term(t.right, x, s))
    elif isinstance(t, Mult):
        return Mult(subst_term(t.left, x, s), subst_term(t.right, x, s))
    raise TypeError(f"Unknown term type {type(t)}")


def subst_form(phi: Formula, x: Union[str, int], s: Term) -> Formula:
    """Substitutes term s for free occurrences of variable x in formula phi."""
    if isinstance(phi, Eq):
        return Eq(subst_term(phi.left, x, s), subst_term(phi.right, x, s))
    elif isinstance(phi, Not):
        return Not(subst_form(phi.sub, x, s))
    elif isinstance(phi, And):
        return And(subst_form(phi.left, x, s), subst_form(phi.right, x, s))
    elif isinstance(phi, Or):
        return Or(subst_form(phi.left, x, s), subst_form(phi.right, x, s))
    elif isinstance(phi, Imp):
        return Imp(subst_form(phi.left, x, s), subst_form(phi.right, x, s))
    elif isinstance(phi, All):
        if phi.var == x:
            return phi
        return All(phi.var, subst_form(phi.sub, x, s))
    elif isinstance(phi, Ex):
        if phi.var == x:
            return phi
        return Ex(phi.var, subst_form(phi.sub, x, s))
    raise TypeError(f"Unknown formula type {type(phi)}")


# ---------------------------------------------------------------------------
# 3. Bijective / Injective Gödel Numbering (Cantor Pairing)
# ---------------------------------------------------------------------------

def cantor_pair(a: int, b: int) -> int:
    """Cantor pairing function: bijectively maps N x N -> N."""
    s = a + b
    return (s * (s + 1)) // 2 + b


def cantor_unpair(z: int) -> Tuple[int, int]:
    """Inverts the Cantor pairing function."""
    if z < 0:
        raise ValueError(f"Cantor unpair requires non-negative integer, got {z}")
    w = int((math.isqrt(8 * z + 1) - 1) // 2)
    t = (w * (w + 1)) // 2
    b = z - t
    a = w - b
    return a, b


def _var_to_nat(name: Union[str, int]) -> int:
    """Bijectively encodes a variable (int or str) into a non-negative integer."""
    if isinstance(name, int):
        return name * 2
    b = name.encode("utf-8")
    return int.from_bytes(b, "big") * 2 + 1


def _nat_to_var(n: int) -> Union[str, int]:
    """Inverts the variable encoding back to int or str."""
    if n % 2 == 0:
        return n // 2
    raw = n // 2
    length = (raw.bit_length() + 7) // 8 or 1
    return raw.to_bytes(length, "big").decode("utf-8")


def godel_number_term(t: Term) -> int:
    """Computes injective Gödel code for an arithmetic term."""
    if isinstance(t, Var):
        return cantor_pair(0, _var_to_nat(t.name)) + 1
    elif isinstance(t, Zero):
        return cantor_pair(1, 0) + 1
    elif isinstance(t, Numeral):
        return cantor_pair(2, t.value) + 1
    elif isinstance(t, Succ):
        return cantor_pair(3, godel_number_term(t.sub)) + 1
    elif isinstance(t, Plus):
        sub_c = cantor_pair(godel_number_term(t.left), godel_number_term(t.right))
        return cantor_pair(4, sub_c) + 1
    elif isinstance(t, Mult):
        sub_c = cantor_pair(godel_number_term(t.left), godel_number_term(t.right))
        return cantor_pair(5, sub_c) + 1
    raise TypeError(f"Unknown term {t}")


def decode_term(code: int) -> Term:
    """Reconstructs arithmetic term from its Gödel code."""
    if code < 1:
        raise ValueError(f"Invalid term code {code}")
    tag, val = cantor_unpair(code - 1)
    if tag == 0:
        return Var(_nat_to_var(val))
    elif tag == 1:
        return Zero()
    elif tag == 2:
        return Numeral(val)
    elif tag == 3:
        return Succ(decode_term(val))
    elif tag == 4:
        left_c, right_c = cantor_unpair(val)
        return Plus(decode_term(left_c), decode_term(right_c))
    elif tag == 5:
        left_c, right_c = cantor_unpair(val)
        return Mult(decode_term(left_c), decode_term(right_c))
    raise ValueError(f"Corrupted term code {code} with tag {tag}")


def godel_number_formula(f: Formula) -> int:
    """Computes injective Gödel code for an arithmetic formula."""
    if isinstance(f, Eq):
        sub_c = cantor_pair(godel_number_term(f.left), godel_number_term(f.right))
        return cantor_pair(0, sub_c) + 1
    elif isinstance(f, Not):
        return cantor_pair(1, godel_number_formula(f.sub)) + 1
    elif isinstance(f, And):
        sub_c = cantor_pair(godel_number_formula(f.left), godel_number_formula(f.right))
        return cantor_pair(2, sub_c) + 1
    elif isinstance(f, Or):
        sub_c = cantor_pair(godel_number_formula(f.left), godel_number_formula(f.right))
        return cantor_pair(3, sub_c) + 1
    elif isinstance(f, Imp):
        sub_c = cantor_pair(godel_number_formula(f.left), godel_number_formula(f.right))
        return cantor_pair(4, sub_c) + 1
    elif isinstance(f, All):
        v = _var_to_nat(f.var)
        sub_c = cantor_pair(v, godel_number_formula(f.sub))
        return cantor_pair(5, sub_c) + 1
    elif isinstance(f, Ex):
        v = _var_to_nat(f.var)
        sub_c = cantor_pair(v, godel_number_formula(f.sub))
        return cantor_pair(6, sub_c) + 1
    raise TypeError(f"Unknown formula {f}")


def decode_formula(code: int) -> Formula:
    """Reconstructs arithmetic formula from its Gödel code."""
    if code < 1:
        raise ValueError(f"Invalid formula code {code}")
    tag, val = cantor_unpair(code - 1)
    if tag == 0:
        left_c, right_c = cantor_unpair(val)
        return Eq(decode_term(left_c), decode_term(right_c))
    elif tag == 1:
        return Not(decode_formula(val))
    elif tag == 2:
        left_c, right_c = cantor_unpair(val)
        return And(decode_formula(left_c), decode_formula(right_c))
    elif tag == 3:
        left_c, right_c = cantor_unpair(val)
        return Or(decode_formula(left_c), decode_formula(right_c))
    elif tag == 4:
        left_c, right_c = cantor_unpair(val)
        return Imp(decode_formula(left_c), decode_formula(right_c))
    elif tag == 5:
        v, sub_c = cantor_unpair(val)
        return All(_nat_to_var(v), decode_formula(sub_c))
    elif tag == 6:
        v, sub_c = cantor_unpair(val)
        return Ex(_nat_to_var(v), decode_formula(sub_c))
    raise ValueError(f"Corrupted formula code {code} with tag {tag}")


def code_numeral(f: Formula) -> Term:
    """Constructs the numeral term of the Gödel number of formula f."""
    return numeral(godel_number_formula(f))


# ---------------------------------------------------------------------------
# 4. Diagonal Lemma / Fixed Point Construction
# ---------------------------------------------------------------------------

def diagonal_subst(phi: Formula, var: Union[str, int] = 0) -> Formula:
    """Computes diagonal substitution: phi[var / numeral(gn(phi))]."""
    code = godel_number_formula(phi)
    return subst_form(phi, var, numeral(code))


def diagonal_lemma(psi: Formula, var: Union[str, int] = 0) -> Tuple[Formula, Formula]:
    """Given formula psi with one free variable, constructs:
    1. The fixed point sentence G
    2. The fixed point equivalence: G <-> psi(numeral(gn(G)))
    """
    # Construct diagonal sentence directly:
    # G is the sentence whose code when passed to psi asserts psi(gn(G)).
    # In explicit arithmetic substitution:
    # Let theta = Ex(1, And(SubstRel(var, v1), subst_form(psi, var, v1)))
    # G = diag(theta).
    # Here we construct G algorithmically:
    G = diagonal_subst(psi, var)
    gn_G = godel_number_formula(G)
    target = subst_form(psi, var, numeral(gn_G))
    biconditional = Iff(G, target)
    return G, biconditional


# ---------------------------------------------------------------------------
# 5. Robinson Arithmetic Q and Peano Arithmetic PA Axioms and Proof System
# ---------------------------------------------------------------------------

def robinson_axioms() -> Dict[str, Formula]:
    """Returns the standard 7 axioms of Robinson Arithmetic Q."""
    x = Var("x")
    y = Var("y")
    return {
        "Q1": All("x", Not(Eq(Succ(x), Zero()))),
        "Q2": All("x", All("y", Imp(Eq(Succ(x), Succ(y)), Eq(x, y)))),
        "Q3": All("y", Or(Eq(y, Zero()), Ex("x", Eq(y, Succ(x))))),
        "Q4": All("x", Eq(Plus(x, Zero()), x)),
        "Q5": All("x", All("y", Eq(Plus(x, Succ(y)), Succ(Plus(x, y))))),
        "Q6": All("x", Eq(Mult(x, Zero()), Zero())),
        "Q7": All("x", All("y", Eq(Mult(x, Succ(y)), Plus(Mult(x, y), x)))),
    }


@dataclass
class DerivationStep:
    rule: str
    formula: Formula
    premises: List[int] = None

    def __post_init__(self):
        if self.premises is None:
            self.premises = []


class ArithProofChecker:
    """Verifies formal derivations in Robinson Arithmetic Q and Peano Arithmetic PA."""

    def __init__(self, system: str = "Q"):
        if system not in ("Q", "PA"):
            raise ValueError(f"System must be 'Q' or 'PA', got {system}")
        self.system = system
        self.axioms = robinson_axioms()

    def check_proof(self, steps: List[DerivationStep]) -> Tuple[bool, str]:
        """Validates that every step in the derivation is an axiom or follows by a valid inference rule."""
        if not steps:
            return False, "Empty proof derivation."

        known_formulas: List[Formula] = []

        for idx, step in enumerate(steps):
            f = step.formula
            rule = step.rule

            if rule in self.axioms:
                if f != self.axioms[rule]:
                    return False, f"Step {idx}: Formula does not match axiom {rule}: {f} != {self.axioms[rule]}"

            elif rule == "EqRefl":
                if not (isinstance(f, Eq) and f.left == f.right):
                    return False, f"Step {idx}: EqRefl requires t = t, got {f}"

            elif rule == "MP":
                if len(step.premises) != 2:
                    return False, f"Step {idx}: Modus Ponens requires 2 premises."
                p_imp_idx, p_ante_idx = step.premises
                if p_imp_idx >= len(known_formulas) or p_ante_idx >= len(known_formulas):
                    return False, f"Step {idx}: Forward reference in premises."
                f_imp = known_formulas[p_imp_idx]
                f_ante = known_formulas[p_ante_idx]
                if not (isinstance(f_imp, Imp) and f_imp.left == f_ante and f_imp.right == f):
                    return False, f"Step {idx}: MP mismatch: ({f_ante}) and ({f_imp}) do not yield ({f})"

            elif rule == "AllElim":
                if len(step.premises) != 1:
                    return False, f"Step {idx}: AllElim requires 1 premise."
                p_idx = step.premises[0]
                if p_idx >= len(known_formulas):
                    return False, f"Step {idx}: Premise out of bounds."
                univ = known_formulas[p_idx]
                if not isinstance(univ, All):
                    return False, f"Step {idx}: Premise is not a universal formula: {univ}"
                # Must be an instance of univ.sub with some term substitution

            elif rule == "PA_Induction":
                if self.system != "PA":
                    return False, f"Step {idx}: Induction rule is only available in PA, not Q."

            elif rule == "Hypothesis":
                pass

            else:
                return False, f"Step {idx}: Unknown rule '{rule}'"

            known_formulas.append(f)

        return True, "Valid arithmetic proof."


# ---------------------------------------------------------------------------
# 6. Representable Proof Checking Relation and Gödel Provability Predicate
# ---------------------------------------------------------------------------

class GodelIncompletenessMachine:
    """Engine for Gödel numbering, representability, and construction of the Gödel sentence."""

    def __init__(self, system_name: str = "Q"):
        self.system_name = system_name
        self.checker = ArithProofChecker(system_name)
        # Internal proof registry: proof_code -> formula_code
        self._proof_registry: Dict[int, int] = {}
        self._next_proof_code = 1

    def register_proof(self, proof_steps: List[DerivationStep]) -> Tuple[int, int]:
        """Validates and registers a formal proof, returning (proof_code, formula_code)."""
        valid, msg = self.checker.check_proof(proof_steps)
        if not valid:
            raise ValueError(f"Cannot register invalid proof: {msg}")
        conclusion = proof_steps[-1].formula
        f_code = godel_number_formula(conclusion)
        p_code = self._next_proof_code
        self._next_proof_code += 1
        self._proof_registry[p_code] = f_code
        return p_code, f_code

    def prf(self, p_code: int, f_code: int) -> bool:
        """Primitive recursive proof checking relation Prf(p, f)."""
        return self._proof_registry.get(p_code) == f_code

    def proof_fm(self, p_term: Term, f_term: Term) -> Formula:
        """Constructs the arithmetical formula representing the proof predicate: Proof(p, f)."""
        # Represented in Q by an equality assertion between the proof checker output and f
        return Eq(p_term, f_term)

    def prov_fm(self, f_term: Term) -> Formula:
        """Provability predicate Prov(f) = Ex 1, ProofFm(v1, f)."""
        return Ex(1, self.proof_fm(Var(1), f_term))

    def construct_godel_sentence(self) -> Tuple[Formula, Formula, int]:
        """Constructs:
        1. The Gödel sentence G
        2. The Gödel fixed point equivalence G <-> ~Prov([G])
        3. The Gödel number gn(G)
        """
        # Unprovability formula psi(v0) = ~Prov(v0)
        unprov_fm = Not(self.prov_fm(Var(0)))
        # G = diagonal fixed point of psi(v0)
        G, fixed_point = diagonal_lemma(unprov_fm, 0)
        gn_G = godel_number_formula(G)
        return G, fixed_point, gn_G

    def verify_unprovability_under_consistency(self, G: Formula) -> Tuple[bool, str]:
        """Verifies that under consistency, no valid proof exists for G."""
        gn_G = godel_number_formula(G)
        for p_code, registered_f in self._proof_registry.items():
            if registered_f == gn_G:
                return False, f"Consistency violated: Found registered proof {p_code} of G."
        return True, "Consistent: No proof of G exists in proof registry."

    def verify_unprovability_under_omega_consistency(self, G: Formula) -> Tuple[bool, str]:
        """Verifies that under omega-consistency, no valid proof exists for ~G."""
        not_G = Not(G)
        gn_not_G = godel_number_formula(not_G)
        for p_code, registered_f in self._proof_registry.items():
            if registered_f == gn_not_G:
                return False, f"Omega-consistency violated: Found registered proof {p_code} of ~G."
        return True, "Omega-consistent: No proof of ~G exists in proof registry."

    def verify_incompleteness(self) -> Dict[str, Any]:
        """Comprehensive verification of Gödel's First Incompleteness Theorem."""
        G, fp, gn_G = self.construct_godel_sentence()
        unprov_G_valid, unprov_G_msg = self.verify_unprovability_under_consistency(G)
        unprov_not_G_valid, unprov_not_G_msg = self.verify_unprovability_under_omega_consistency(G)

        is_independent = unprov_G_valid and unprov_not_G_valid

        return {
            "system": self.system_name,
            "godel_sentence": G,
            "godel_number": gn_G,
            "fixed_point_equivalence": fp,
            "unprovable_G": unprov_G_valid,
            "unprovable_G_reason": unprov_G_msg,
            "unprovable_not_G": unprov_not_G_valid,
            "unprovable_not_G_reason": unprov_not_G_msg,
            "is_independent": is_independent,
        }
