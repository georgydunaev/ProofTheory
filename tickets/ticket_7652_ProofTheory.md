# [PROOFTHEORY] Ticket 7652 : Fix Coq Compilation Regression in QandPA and Formalize Arithmetic Properties in Robinson and Peano Arithmetic

**Repository:** `ProofTheory`  
**Status:** `CLOSED`  
**Created:** `2026-11-13T22:53:00Z`  

## Task Description
Address Coq compilation regression in `QandPA.v` where legacy identifier `plus_0_r` caused compilation failure under modern Coq versions (Coq 8.20+). In addition, expand formalizations of Robinson Arithmetic (Q) axioms (R1-R7) and derivability, first-order Peano Arithmetic induction schemes, and algebraic properties including addition commutativity, associativity, and the zero-product property under induction.

## Root Cause Analysis
1. Modern Coq deprecated and removed legacy arithmetic lemmas such as `plus_0_r` and `mult_0_r` from standard scope in favor of `Nat.add_0_r` and `Nat.mul_0_r`.
2. The standard model `nat_pa` module type declaration contained a signature mismatch against module type `PA a ra`.
3. Auxiliary files and examples referenced deprecated `Omega` rather than `Lia`.

## Key Implementations
1. **Compilation Regression Fixes in QandPA.v**:
   - Replaced `plus_0_r` with `Nat.add_0_r` in `l1_2`.
   - Replaced `mult_0_r` with `Nat.mul_0_r` in `l1_3`.
   - Corrected standard model module hierarchy `NatAri <: Ari`, `NatRA <: RA NatAri`, and `nat_pa <: PA NatAri NatRA`.
2. **Robinson Arithmetic Q Axioms (R1-R7) and Derivability**:
   - Formulated explicit R1 through R7 definitions aliasing Q1 through Q7.
   - Defined inductive derivability system `RD` encoding Robinson Arithmetic inference rules (axioms R1-R7, modus ponens, universal instantiation, equality reflexivity, symmetry, transitivity, and congruence for successor, addition, and multiplication).
   - Proved foundational soundness `RD_sound : forall P, RD P -> P`.
   - Formulated derivability instances `RD_Q4_inst`, `RD_Q6_inst`, and predecessor/injectivity theorems `Q_pred_or_zero`, `Q_succ_nonzero`, `Q_succ_inj`.
3. **First-Order Peano Arithmetic Induction Schemes**:
   - Formalized induction scheme instances: `PA_induction_instance`, parameterized induction `IND_param`, and two-variable joint induction `IND_2var`.
   - Defined first-order arithmetical terms (`FO_Term`) and formulas (`FO_Formula`) over the signature (0, S, +, *).
   - Defined semantic denotation `eval_fo_term` and `eval_fo_formula` with environment updates `update_env`.
   - Verified schema theorem `PA_fo_induction_instance` establishing induction for any first-order arithmetical formula.
4. **Algebraic Laws and Zero-Product Property**:
   - Verified `AD_0_l : forall x : N, AD ZE x = x`.
   - Verified `AD_comm : forall x y : N, AD x y = AD y x`.
   - Verified 4-element addition swap `ad_4_swap`.
   - Verified multiplication identity and successor laws: `MU_0_l`, `MU_SU_l`.
   - Verified multiplication commutativity: `MU_sym`.
   - Verified right and left distributivity: `distrib_r`, `distrib_l`.
   - Verified multiplication associativity: `MU_assoc`.
   - Proved zero-product property under induction: `zero_product : forall x y : N, MU x y = ZE -> x = ZE \/ y = ZE`.
5. **Modern Coq Compatibility across Examples**:
   - Replaced legacy `Omega` references with modern `Lia` in `proofs_with_omega.v`, `examples/arithmetic_example.v`, and `examples/omega_example.v`.

## Verification
- `coqc QandPA.v`: Exited 0 with zero errors.
- `python3 -m unittest discover tests`: 15 of 15 tests passed.
- `python3 verify.py`: All Coq files and test suites verified cleanly.
- Security scanner: Passed with 0 secrets detected.
