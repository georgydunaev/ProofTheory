# ProofTheory

This repository contains formal logic, proof theory algorithms, and mechanized Coq proofs related to Robinson Arithmetic (Q), Peano Arithmetic (PA), Gödel's First Incompleteness Theorem, Gentzen sequent calculi (LK and LJ), cut elimination (Hauptsatz), and ordinal analysis up to `epsilon_0`.

## Modules and Architecture

1. **[src/sequent_calculus.py](file:///botworkspace/ProofTheory/src/sequent_calculus.py)**: Formal abstract syntax trees for propositional and first-order formulas, sequents (`Gamma |- Delta`), and Gentzen LK / LJ proof trees.
2. **[src/cut_elimination_modular.py](file:///botworkspace/ProofTheory/src/cut_elimination_modular.py)**: Modular Gentzen cut-elimination engine featuring formula degree, cut rank, modular rank reduction, and degree reduction passes.
3. **[src/proof_checker.py](file:///botworkspace/ProofTheory/src/proof_checker.py)**: Deductive proof checker validating inference rules in classical LK and intuitionistic LJ, and verifying the subformula property.
4. **[src/ordinal_analysis.py](file:///botworkspace/ProofTheory/src/ordinal_analysis.py)**: Constructive Cantor Normal Form ordinal arithmetic below `epsilon_0`, ordinal addition, fundamental sequences, and transfinite induction step verification.
5. **[src/godel_incompleteness.py](file:///botworkspace/ProofTheory/src/godel_incompleteness.py)**: Algorithmic reference implementation of Gödel numbering (via Cantor pairing), syntactic substitution, diagonal lemma fixed-point construction, proof checking for Q and PA, and verification of Gödel's First Incompleteness Theorem.
6. **[QandPA.v](file:///botworkspace/ProofTheory/QandPA.v)**: Coq formalization of Robinson Arithmetic (`RA`), Peano Arithmetic (`PA`), deductive soundness (`RD_sound`), commutative semiring laws (`AD_sym`, `AD_assoc`, `MU_sym`, `MU_assoc`, `distrib_l`, `distrib_r`, `zero_product`), first-order induction (`PA_fo_induction_instance`), order transitivity (`LE_trans`), strong induction (`strong_induction`), constructive least number principle (`LNP`), and the standard model (`nat_pa`).
7. **[GodelFirst.v](file:///botworkspace/ProofTheory/GodelFirst.v)**: Coq formalization of Gödel numbering (`code_term`, `code_formula`), diagonal substitution, abstract deductive and representation systems, the Gödel sentence `G`, and mechanized proofs of `godel_first_unprovable_G`, `godel_first_unprovable_not_G`, `godel_first_incompleteness`, `Robinson_Q_incompleteness`, and `Peano_PA_incompleteness`.
8. **[proofs_with_omega.v](file:///botworkspace/ProofTheory/proofs_with_omega.v)**, **[examples/arithmetic_example.v](file:///botworkspace/ProofTheory/examples/arithmetic_example.v)**, and **[examples/omega_example.v](file:///botworkspace/ProofTheory/examples/omega_example.v)**: Automated arithmetic proofs in Coq using `lia`.

## Documentation

- **[ARCHITECTURE_AND_THEOREMS.md](file:///botworkspace/ProofTheory/ARCHITECTURE_AND_THEOREMS.md)**: Comprehensive guide summarizing every formalization, theorem, axiom system, and unfinished problem in the repository.
- **[THEOREMS_INDEX.md](file:///botworkspace/ProofTheory/THEOREMS_INDEX.md)**: Concise index of formalized definitions and theorems.
- **[DOCS.md](file:///botworkspace/ProofTheory/DOCS.md)**: Component overview.

## Dependencies

- Python 3.10+
- Coq (optional for `.v` batch compilation; verified by `verify.py`)

## Verification and Testing

To run the automated verification and unit test suite:

```bash
python3 verify.py
python3 -m unittest discover -s tests -p 'test_*.py'
```
