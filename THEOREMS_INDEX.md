# Theorems Index

## QandPA.v

### Definitions

1. **Terms**: Definitions for zero (`ZE`), successor (`SU`), addition (`AD`), and multiplication (`MU`).
2. **Robinson Arithmetic (RA)**: Axioms for basic arithmetic operations (Q1 through Q7).
3. **Peano Arithmetic (PA)**: Additional axioms for induction (`IND`), extending Robinson Arithmetic.

### Verified Theorems & Proofs

1. **l1_1**: Injectivity of numerals (`k <> m -> num m <> num k`).
2. **l1_2**: Homomorphism of addition on numerals (`AD (num k) (num m) = num (k + m)`).
3. **sum_sym**: Symmetry of addition on numerals.
4. **summ_assoc**: Associativity of addition on numerals.
5. **l1_3**: Homomorphism of multiplication on numerals.
6. **mul_sym**: Symmetry of multiplication on numerals.
7. **AD_sym_lem & AD_sym**: General symmetry of addition for all elements of `N` in PA.
8. **AD_assoc**: General associativity of addition for all elements of `N` in PA (`AD (AD x y) z = AD x (AD y z)`).
9. **LE_redu**: Successor cancellation for inequality (`LE (SU a) (SU y) -> LE a y`).
10. **LE_trans**: Transitivity of ordering in PA (`LE a b -> LE b c -> LE a c`), closing the foundational gap for strong induction.
11. **strong_induction_all & strong_induction**: Full strong induction principle derived from PA induction.
12. **LNP**: Constructive least number principle in intuitionistic PA.
13. **nat_pa**: Standard model of Peano Arithmetic in Coq `nat`.

## proofs_with_omega.v

### Theorems

1. **OCP_leq0_then_eq0**: Automated proof using the `omega` tactic for `m <= 0 -> m = 0`.

## Gentzen Sequent Calculus (src/sequent_calculus.py & src/proof_checker.py)

### Proof Systems and Deductive Rules

1. **Formulas & Complexity**: Abstract syntax trees for Atom, Not, And, Or, Imp with formula degree metric.
2. **Sequents**: Formal Gamma |- Delta multisets with axiom checking (`is_axiom`) and intuitionistic checks (`is_intuitionistic`).
3. **LK (Classical) & LJ (Intuitionistic) Inference Rules**: Identity axiom, Cut, left/right conjunction, disjunction, implication, negation, weakening, contraction, exchange.
4. **Subformula Property**: Formal verification that in cut-free derivations, all formulas are subformulas of the conclusion sequent.

## Gentzen Cut Elimination / Hauptsatz (src/cut_elimination_modular.py)

1. **Formula Degree**: Measures the logical complexity of cut formulas.
2. **Cut Rank**: Measures distance to principal formula introductions in premise subtrees.
3. **Rank Reduction**: Modular permutation of cuts upward past non-principal logical and structural rules.
4. **Degree Reduction**: Splitting principal cuts on compound formulas into cuts on simpler subformulas.
5. **Eliminate Cuts**: Complete transformation pass yielding cut-free proofs satisfying the subformula property.

## Ordinal Analysis up to Epsilon-0 (src/ordinal_analysis.py)

1. **Cantor Normal Form**: Strict canonical representation of ordinals below epsilon_0.
2. **Ordinal Comparison & Arithmetic**: Well-ordering comparison and non-commutative ordinal addition.
3. **Fundamental Sequences**: Computation of alpha[n] for limit ordinals.
4. **Transfinite Step Verification**: Algorithmic proof of strict monotonicity alpha[0] < alpha[1] < ... < alpha.
5. **Peano Bound**: Proof-theoretic ordinal bound epsilon_0 for Peano Arithmetic.
