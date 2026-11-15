# Theorems Index

For detailed architectural descriptions, axiom systems, and open problems, see [ARCHITECTURE_AND_THEOREMS.md](file:///botworkspace/ProofTheory/ARCHITECTURE_AND_THEOREMS.md).

## 1. `QandPA.v` (Robinson Arithmetic Q and Peano Arithmetic PA)

### Definitions and Module Signatures
1. **`Ari`**: Signature module declaring carrier `N : Set`, zero `ZE`, successor `SU`, addition `AD`, and multiplication `MU`.
2. **`RA`**: Robinson Arithmetic module type axiomatizing `Q1` through `Q7`.
3. **`PA`**: Peano Arithmetic module type extending `RA` with higher-order induction `IND`.
4. **`TermsMod`**: Syntactic term model (`cZE`, `cSU`, `cAD`, `cMU`) implementing `Ari`.
5. **`FO_Term` and `FO_Formula`**: First-order syntax and environment evaluator (`eval_fo_term`, `eval_fo_formula`) over any model of `PA`.

### Verified Theorems and Proofs
1. **`l1_1`**: Injectivity of numerals (`not (k = m) -> not (num m = num k)`).
2. **`Q4_sym_num`**: Left zero identity on numerals (`AD ZE (num x) = num x`).
3. **`not_imp_or`**: Constructive disjunction elimination (`(A \/ B) -> ((A -> False) -> B)`).
4. **`l1_2`**: Homomorphism of addition on numerals (`AD (num k) (num m) = num (k + m)`).
5. **`sum_sym` & `summ_assoc`**: Symmetry and associativity of addition on numerals.
6. **`l1_3` & `mul_sym`**: Homomorphism and symmetry of multiplication on numerals.
7. **`RD` & `RD_sound`**: Inductive Hilbert-style derivability system for Robinson Arithmetic and its soundness proof (`forall P, RD P -> P`).
8. **`RD_Q4_inst` & `RD_Q6_inst`**: Object-level universal instantiations in `RD`.
9. **`Q_pred_or_zero`, `Q_succ_nonzero`, `Q_succ_inj`**: Structural lemmas in Robinson Arithmetic.
10. **`AD_sym_lem`, `AD_sym`, `AD_comm`**: General commutativity of addition in PA (`AD x y = AD y x`).
11. **`leq0_then_eq0`**: Zero upper bound property (`LE m ZE -> m = ZE`).
12. **`LE_redu`**: Successor cancellation for inequality (`LE (SU a) (SU y) -> LE a y`).
13. **`AD_assoc`**: General associativity of addition in PA (`AD (AD x y) z = AD x (AD y z)`).
14. **`AD_0_l` & `ad_4_swap`**: Left zero identity and 4-term middle-exchange lemma for addition.
15. **`MU_0_l` & `MU_SU_l`**: Left zero annihilation and left successor recursion for multiplication.
16. **`MU_sym`**: General commutativity of multiplication in PA (`MU x y = MU y x`).
17. **`distrib_r` & `distrib_l`**: Right and left distributivity of multiplication over addition.
18. **`MU_assoc`**: Associativity of multiplication in PA (`MU (MU x y) z = MU x (MU y z)`).
19. **`zero_product`**: Integrity domain / zero-product property (`MU x y = ZE -> x = ZE \/ y = ZE`).
20. **`PA_induction_instance`, `IND_param`, `IND_2var`, `PA_fo_induction_instance`**: Parametric, double, and first-order formula induction principles.
21. **`LE_trans`**: Transitivity of ordering (`LE a b -> LE b c -> LE a c`).
22. **`strong_induction_all` & `strong_induction`**: Course-of-values / strong induction derived from `IND`.
23. **`l1case0` & `wol0`**: Zero is the least element of `N` (`forall z, LE ZE z`).
24. **`LNP` (constructive)**: Intuitionistic contrapositive Least Number Principle (`(forall y, ~ F y \/ exists z, LT z y /\ F z) -> forall y, ~ F y`).
25. **`NatAri`, `NatRA`, `nat_pa`**: Verified standard model of `RA` and `PA` over Coq's `nat`.

## 2. `GodelFirst.v` and `src/godel_incompleteness.py` (Gödel's First Incompleteness Theorem)

1. **`numeral_inj`**: Injectivity of standard numeral embedding `numeral : nat -> Term`.
2. **`subst_term_var_same` & `subst_term_var_diff`**: Term substitution lookup identities.
3. **`cantor_pair`, `code_term`, `code_formula`**: Injective Gödel numbering of terms and formulas.
4. **`godel_fixed_point`**: Fixed-point equivalence `sys.(Prv) (Iff G (Not (ProvFm ps (code_numeral G))))`.
5. **`godel_first_unprovable_G`**: First part of Gödel's theorem (`Consistent sys -> ~ sys.(Prv) G`).
6. **`godel_first_unprovable_not_G`**: Second part of Gödel's theorem (`OmegaConsistent sys -> Consistent sys -> ~ sys.(Prv) (Not G)`).
7. **`godel_first_incompleteness`**: Combined independence of the Gödel sentence `G`.
8. **`arithmetic_theory_godel_first_incompleteness`**: General incompleteness theorem for any `ArithmeticTheoryOverQ`.
9. **`Robinson_Q_incompleteness` & `Peano_PA_incompleteness`**: Instantiations for Robinson Arithmetic `Q` and Peano Arithmetic `PA`.

## 3. `proofs_with_omega.v` and `examples/`

1. **`OCP_leq0_then_eq0`** (`proofs_with_omega.v`): Proof that `m <= 0 -> m = 0` via `lia`.
2. **`add_zero` & `mul_zero`** (`examples/arithmetic_example.v`): Proofs of `AD m ZE = m` and `MU m ZE = ZE` in `nat_pa`.
3. **`sum_of_two_evens_is_even`** (`examples/omega_example.v`): Proof that `Nat.divide 2 n -> Nat.divide 2 m -> Nat.divide 2 (n + m)`.

## 4. Python Proof Theory Engines (`src/`)

1. **Gentzen Sequent Calculus (`src/sequent_calculus.py` & `src/proof_checker.py`)**: LK and LJ proof tree validation and subformula property verification.
2. **Gentzen Cut Elimination / Hauptsatz (`src/cut_elimination_modular.py`)**: Rank reduction, degree reduction, and complete recursive cut elimination `eliminate_cuts`.
3. **Ordinal Analysis up to `epsilon_0` (`src/ordinal_analysis.py`)**: Cantor Normal Form ordinals (`CNFOrdinal`), non-commutative ordinal addition, fundamental sequences, and monotonicity checks.
