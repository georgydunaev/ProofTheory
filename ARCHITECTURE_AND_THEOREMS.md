# Architecture, Axiom Systems, Formalizations, and Theorems Guide

## 1. Repository Architecture Overview

`ProofTheory` is a dual-language (Coq and Python) formalization repository dedicated to structural proof theory, first-order arithmetic (`Q` and `PA`), Gödel's First Incompleteness Theorem, Gentzen sequent calculi (`LK` and `LJ`), cut elimination (Gentzen's *Hauptsatz*), and constructive ordinal analysis up to $\varepsilon_0$.

### Directory and File Structure

- **Coq Formalizations (Root & `examples/`)**:
  - [`QandPA.v`](file:///botworkspace/ProofTheory/QandPA.v): Modular Coq development of Robinson Arithmetic (`RA`), Peano Arithmetic (`PA`), an object-level Hilbert-style deductive calculus (`RD`) with soundness (`RD_sound`), full commutative semiring arithmetic, first-order formula evaluation and induction (`PA_fo_induction_instance`), course-of-values strong induction (`strong_induction`), constructive least number principle (`LNP`), and the standard model over `nat` (`NatAri`, `NatRA`, `nat_pa`).
  - [`GodelFirst.v`](file:///botworkspace/ProofTheory/GodelFirst.v): Mechanization of Gödel's First Incompleteness Theorem for abstract deductive systems and any arithmetic theory extending Robinson Arithmetic `Q` or Peano Arithmetic `PA`.
  - [`proofs_with_omega.v`](file:///botworkspace/ProofTheory/proofs_with_omega.v): Linear integer arithmetic (`lia`) proof of `OCP_leq0_then_eq0`.
  - [`examples/arithmetic_example.v`](file:///botworkspace/ProofTheory/examples/arithmetic_example.v): Instantiated arithmetic proofs in the standard model `nat_pa` (`add_zero`, `mul_zero`).
  - [`examples/omega_example.v`](file:///botworkspace/ProofTheory/examples/omega_example.v): Parity/divisibility proof (`sum_of_two_evens_is_even`) using `lia`.
- **Python Proof-Theoretic Engines (`src/`)**:
  - [`src/sequent_calculus.py`](file:///botworkspace/ProofTheory/src/sequent_calculus.py): AST for propositional formulas (`Atom`, `Not`, `And`, `Or`, `Imp`), multiset sequents (`Sequent`), and derivation trees (`ProofTree`) with cut-freeness and subformula property predicates.
  - [`src/proof_checker.py`](file:///botworkspace/ProofTheory/src/proof_checker.py): Soundness verifier (`ProofChecker`) for classical `LK` and intuitionistic `LJ` derivations (enforcing the intuitionistic restriction $|\Delta| \le 1$ in `LJ`) and subformula property checking.
  - [`src/cut_elimination_modular.py`](file:///botworkspace/ProofTheory/src/cut_elimination_modular.py): Modular Gentzen cut-elimination engine (`CutEliminationModular`) implementing `formula_degree`, `cut_rank`, `rank_reduction`, `degree_reduction`, and `eliminate_cuts`.
  - [`src/ordinal_analysis.py`](file:///botworkspace/ProofTheory/src/ordinal_analysis.py): Constructive Cantor Normal Form ordinals below $\varepsilon_0$ (`CNFOrdinal`), lexicographical well-ordering, non-commutative ordinal addition, fundamental sequences $\alpha[n]$, and monotonicity verification (`OrdinalAnalysis`).
  - [`src/godel_incompleteness.py`](file:///botworkspace/ProofTheory/src/godel_incompleteness.py): Executable reference engine for first-order arithmetic ASTs, bijective Cantor-pairing Gödel numbering (`godel_number_term`, `decode_term`, `godel_number_formula`, `decode_formula`), diagonal fixed-point construction (`diagonal_lemma`), Robinson/Peano proof checking (`ArithProofChecker`), and incompleteness verification (`GodelIncompletenessMachine`).
- **Verification and Test Suite (`verify.py`, `tests/`)**:
  - [`verify.py`](file:///botworkspace/ProofTheory/verify.py): Top-level verification runner checking Coq source integrity and running all unit tests.
  - [`tests/test_cut_elimination_modular.py`](file:///botworkspace/ProofTheory/tests/test_cut_elimination_modular.py), [`tests/test_godel.py`](file:///botworkspace/ProofTheory/tests/test_godel.py), [`tests/test_ordinal_analysis.py`](file:///botworkspace/ProofTheory/tests/test_ordinal_analysis.py), [`tests/test_proof_checker.py`](file:///botworkspace/ProofTheory/tests/test_proof_checker.py).

---

## 2. Formalized Axiom Systems

### 2.1 Robinson Arithmetic (`RA` / `Q`) in [`QandPA.v`](file:///botworkspace/ProofTheory/QandPA.v#L32-L46) and [`src/godel_incompleteness.py`](file:///botworkspace/ProofTheory/src/godel_incompleteness.py#L430-L443)
Over the signature $\mathcal{L}_A = (0, S, +, \cdot)$ (`ZE`, `SU`, `AD`, `MU` on carrier `N : Set`):
- **Q1**: $\forall x,\, S(x) \neq 0$ (`forall x:N, not (SU x = ZE)`).
- **Q2**: $\forall x\, y,\, S(x) = S(y) \implies x = y$ (`forall x y:N, SU x = SU y -> x = y`).
- **Q3**: $\forall y,\, y = 0 \lor \exists x,\, y = S(x)$ (`forall y:N, (y = ZE) \/ exists x:N, y = SU x`).
- **Q4**: $\forall x,\, x + 0 = x$ (`forall x:N, AD x ZE = x`).
- **Q5**: $\forall x\, y,\, x + S(y) = S(x + y)$ (`forall x y:N, AD x (SU y) = SU (AD x y)`).
- **Q6**: $\forall x,\, x \cdot 0 = 0$ (`forall x:N, MU x ZE = ZE`).
- **Q7**: $\forall x\, y,\, x \cdot S(y) = (x \cdot y) + x$ (`forall x y:N, MU x (SU y) = AD (MU x y) x`).

### 2.2 Robinson Deductive System (`RD`) in [`QandPA.v`](file:///botworkspace/ProofTheory/QandPA.v#L158-L174)
Inductive derivability predicate `RD : Prop -> Prop` comprising:
- Axioms `R_ax1` through `R_ax7` (corresponding to `Q1`–`Q7`).
- Logical rules: Modus Ponens (`R_mp`) and universal instantiation (`R_all_e`).
- Equality congruence rules: reflexivity (`R_refl`), symmetry (`R_sym`), transitivity (`R_trans`), and congruence for `SU`, `AD`, and `MU` (`R_congr_SU`, `R_congr_AD`, `R_congr_MU`).

### 2.3 Peano Arithmetic (`PA`) in [`QandPA.v`](file:///botworkspace/ProofTheory/QandPA.v#L48-L54)
Extends `RA` with the induction scheme `IND`:
- **Higher-Order / Predicate Form (`IND`)**:
  $$\forall P : N \to \mathrm{Prop},\, P(0) \implies (\forall y,\, P(y) \implies P(S(y))) \implies \forall y,\, P(y)$$
- **First-Order Formula Form (`PA_fo_induction_instance`)**: Derived for any object-level first-order formula $\phi \in \mathrm{FO\_Formula}$ evaluated under environment `env : nat -> N`.

### 2.4 Gentzen Sequent Calculi (`LK` and `LJ`) in [`src/sequent_calculus.py`](file:///botworkspace/ProofTheory/src/sequent_calculus.py) and [`src/proof_checker.py`](file:///botworkspace/ProofTheory/src/proof_checker.py)
- **Classical `LK`**: Multi-succedent sequents $\Gamma \vdash \Delta$ with identity axiom (`Ax`: $\Gamma, A \vdash A, \Delta$), `Cut`, left/right propositional rules (`L_And`, `R_And`, `L_Or`, `R_Or`, `L_Imp`, `R_Imp`, `L_Not`, `R_Not`), weakening (`L_Weak`, `R_Weak`), contraction (`L_Contr`, `R_Contr`), and `Exchange`.
- **Intuitionistic `LJ`**: Restricts every sequent in the derivation tree to at most one formula in the succedent ($|\Delta| \le 1$).

### 2.5 Abstract Incompleteness & Representability Axioms in [`GodelFirst.v`](file:///botworkspace/ProofTheory/GodelFirst.v#L132-L204)
- **`DeductiveSystem`**: Provability predicate `Prv : Formula -> Prop` closed under modus ponens (`prv_mp`), conjunction introduction/elimination (`prv_and_intro`, `prv_and_elim_l`, `prv_and_elim_r`), biconditional introduction/elimination (`prv_iff_intro`, `prv_iff_elim_l`, `prv_iff_elim_r`), existential introduction (`prv_ex_intro`), and negated biconditional elimination (`prv_iff_not_elim`, `prv_contra`).
- **`DiagonalSystem`**: `diag_sentence : Formula -> Formula` satisfying the fixed-point equivalence `Prv (Iff (diag_sentence psi) (subst_form psi 0 (code_numeral (diag_sentence psi))))`.
- **`ProofSystem` and `ProofRepresentation`**: Meta-level proof relation `Prf : nat -> nat -> Prop` represented by an arithmetic formula `ProofFm : Term -> Term -> Formula` satisfying soundness (`prf_sound`), completeness (`prf_complete`), positive representability (`prf_rep_pos`), and negative representability (`prf_rep_neg`).

---

## 3. Comprehensive Catalog of Verified Theorems

### 3.1 Theorems in [`QandPA.v`](file:///botworkspace/ProofTheory/QandPA.v)

| Theorem / Lemma | Line | Formal Statement Summary | Status |
|---|---:|---|---|
| `l1_1` | 75 | `forall k m, not (k = m) -> not (num m = num k)` (numeral injectivity in `RA`) | `Defined.` |
| `Q4_sym_num` | 98 | `forall x:nat, AD ZE (num x) = num x` | `Defined.` |
| `not_imp_or` | 103 | `forall A B:Prop, (A \/ B) -> ((A -> False) -> B)` | `Defined.` |
| `l1_2` | 111 | `forall m k, AD (num k) (num m) = num (k + m)` | `Defined.` |
| `sum_sym` | 120 | `forall k m, AD (num k) (num m) = AD (num m) (num k)` | `Defined.` |
| `summ_assoc` | 125 | `forall a b c, AD (AD (num a) (num b)) (num c) = AD (num a) (AD (num b) (num c))` | `Defined.` |
| `l1_3` | 134 | `forall m k, MU (num k) (num m) = num (k * m)` | `Defined.` |
| `mul_sym` | 142 | `forall k m, MU (num k) (num m) = MU (num m) (num k)` | `Defined.` |
| `RD_sound` | 175 | `forall P : Prop, RD P -> P` (soundness of Robinson deduction) | `Defined.` |
| `RD_Q4_inst` | 196 | `forall x:N, RD (AD x ZE = x)` | `Defined.` |
| `RD_Q6_inst` | 201 | `forall x:N, RD (MU x ZE = ZE)` | `Defined.` |
| `Q_pred_or_zero` | 206 | `forall y:N, y = ZE \/ exists x:N, y = SU x` | `Defined.` |
| `Q_succ_nonzero` | 209 | `forall x:N, not (SU x = ZE)` | `Defined.` |
| `Q_succ_inj` | 212 | `forall x y:N, SU x = SU y -> x = y` | `Defined.` |
| `AD_sym_lem` | 318 | `forall n m:N, AD m (SU n) = AD (SU m) n` | `Defined.` |
| `AD_sym` / `AD_comm` | 333 / 406 | `forall y x:N, AD x y = AD y x` | `Defined.` |
| `leq0_then_eq0` | 353 | `forall m:N, LE m ZE -> m = ZE` | `Defined.` |
| `LE_redu` | 371 | `forall a y:N, LE (SU a) (SU y) -> LE a y` | `Defined.` |
| `AD_assoc` | 384 | `forall x y z:N, AD (AD x y) z = AD x (AD y z)` | `Defined.` |
| `AD_0_l` | 399 | `forall x:N, AD ZE x = x` | `Defined.` |
| `ad_4_swap` | 411 | `forall a b c d:N, AD (AD a b) (AD c d) = AD (AD a c) (AD b d)` | `Defined.` |
| `MU_0_l` | 421 | `forall x:N, MU ZE x = ZE` | `Defined.` |
| `MU_SU_l` | 428 | `forall x y:N, MU (SU x) y = AD (MU x y) y` | `Defined.` |
| `MU_sym` | 438 | `forall x y:N, MU x y = MU y x` | `Defined.` |
| `distrib_r` | 445 | `forall x y z:N, MU (AD x y) z = AD (MU x z) (MU y z)` | `Defined.` |
| `distrib_l` | 454 | `forall x y z:N, MU x (AD y z) = AD (MU x y) (MU x z)` | `Defined.` |
| `MU_assoc` | 463 | `forall x y z:N, MU (MU x y) z = MU x (MU y z)` | `Defined.` |
| `zero_product` | 471 | `forall x y:N, MU x y = ZE -> x = ZE \/ y = ZE` | `Defined.` |
| `IND_param` | 492 | Parametric induction `forall y p : N, P y p` | `Defined.` |
| `IND_2var` | 503 | Double induction `forall x y : N, P x y` | `Defined.` |
| `PA_fo_induction_instance` | 556 | First-order induction for any `phi : FO_Formula` | `Defined.` |
| `LE_trans` | 568 | `forall a b c:N, LE a b -> LE b c -> LE a c` | `Defined.` |
| `strong_induction_all` | 586 | `forall n m, LE m n -> P m` under strong induction hypotheses | `Defined.` |
| `strong_induction` | 605 | `forall n, P n` (course-of-values induction in PA) | `Defined.` |
| `l1case0` / `wol0` | 616 / 629 | `forall z, LE ZE z` and `exists y, forall z, LE y z` | `Defined.` |
| `LNP` (constructive) | 685 | `(forall y, ~ F y \/ exists z, LT z y /\ F z) -> forall y, ~ F y` | `Defined.` |
| `NatRA` (`Q1`–`Q7`) & `nat_pa` (`IND`) | 724 / 746 | Standard model of `RA` and `PA` on Coq `nat` | `Defined.` |

### 3.2 Theorems in [`GodelFirst.v`](file:///botworkspace/ProofTheory/GodelFirst.v)

| Theorem / Lemma | Line | Formal Statement Summary | Status |
|---|---:|---|---|
| `numeral_inj` | 44 | `forall n m, numeral n = numeral m -> n = m` | `Qed.` |
| `subst_term_var_same` | 76 | `forall x s, subst_term (Var x) x s = s` | `Qed.` |
| `subst_term_var_diff` | 83 | `forall x y s, x <> y -> subst_term (Var y) x s = Var y` | `Qed.` |
| `godel_fixed_point` | 228 | `sys.(Prv) (Iff G (Not (ProvFm ps (code_numeral G))))` | `Qed.` |
| `godel_first_unprovable_G` | 246 | `Consistent sys -> ~ (sys.(Prv) G)` | `Qed.` |
| `godel_first_unprovable_not_G` | 269 | `OmegaConsistent sys -> Consistent sys -> ~ (sys.(Prv) (Not G))` | `Qed.` |
| `godel_first_incompleteness` | 301 | `OmegaConsistent sys -> Consistent sys -> ~ (sys.(Prv) G) /\ ~ (sys.(Prv) (Not G))` | `Qed.` |
| `arithmetic_theory_godel_first_incompleteness` | 327 | Incompleteness for any `T : ArithmeticTheoryOverQ` | `Qed.` |
| `Robinson_Q_incompleteness` | 344 | Incompleteness instantiated for Robinson Arithmetic `Q` | `Qed.` |
| `Peano_PA_incompleteness` | 359 | Incompleteness instantiated for Peano Arithmetic `PA` | `Qed.` |

### 3.3 Theorems in [`proofs_with_omega.v`](file:///botworkspace/ProofTheory/proofs_with_omega.v) and `examples/`

| Theorem | File | Statement | Status |
|---|---|---|---|
| `OCP_leq0_then_eq0` | [`proofs_with_omega.v`](file:///botworkspace/ProofTheory/proofs_with_omega.v#L7) | `forall m, m <= 0 -> m = 0` | `Defined.` |
| `add_zero` | [`examples/arithmetic_example.v`](file:///botworkspace/ProofTheory/examples/arithmetic_example.v#L10) | `forall m : N, AD m ZE = m` | `Qed.` |
| `mul_zero` | [`examples/arithmetic_example.v`](file:///botworkspace/ProofTheory/examples/arithmetic_example.v#L16) | `forall m : N, MU m ZE = ZE` | `Qed.` |
| `sum_of_two_evens_is_even` | [`examples/omega_example.v`](file:///botworkspace/ProofTheory/examples/omega_example.v#L5) | `Nat.divide 2 n -> Nat.divide 2 m -> Nat.divide 2 (n + m)` | `Qed.` |

---

## 4. Unfinished Problems and Preserved Proof Sketches

All active theorems in `GodelFirst.v`, `proofs_with_omega.v`, `examples/arithmetic_example.v`, and `examples/omega_example.v` close with `Qed.` or `Defined.` (zero `Admitted` statements across the entire repository). In [`QandPA.v`](file:///botworkspace/ProofTheory/QandPA.v), the following exploratory or classical-only items are preserved in accordance with the repository's non-deletion policy:

1. **Classical Well-Ordering and Existential Least Number Principles (`QandPA.v:639–675`)**:
   - `Lemma wol1` (line 639), `Theorem WO` (line 665), and the classical existential `Theorem LNP` (line 672) end with `Abort.`.
   - **Mathematical Reason**: In Intuitionistic Peano Arithmetic (IPA) over Coq's `Prop` without the Law of Excluded Middle ($P \lor \neg P$) or decidability of $F$ ($\forall x,\, F(x) \lor \neg F(x)$), the existence of a witness $\exists y,\, F(y)$ does not constructively compute the least witness $\exists y,\, F(y) \land \forall z \le y,\, \neg F(z)$. Immediately below (at line 685), the constructively valid contrapositive formulation `Theorem LNP` is stated and proved in full (`Defined.`).
2. **Commented-Out Term Model Exploration (`QandPA.v:215–234` and `251–294`)**:
   - Preserves an early attempt (`Module TheoremsAboutTerms`, `Lemma l_1_5`) to prove properties directly by structural induction on the free term algebra `TermsMod` without `PA`'s `IND` axiom. In `TheoremsPA`, the corresponding results (`AD_0_l`, `AD_sym`, etc.) are proved in full using `IND`.
3. **Future Extensions**:
   - Extending the Python Gentzen cut-elimination engine (`src/cut_elimination_modular.py`) from propositional `LK`/`LJ` to first-order quantifier rules (`L_All`, `R_All`, `L_Ex`, `R_Ex`) with explicit eigenvariable renaming.
   - Connecting the ordinal assignment of `src/ordinal_analysis.py` directly to ω-rule / Gentzen transfinite cut-reduction trees for `PA`.
