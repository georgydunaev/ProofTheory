# ProofTheory

This repository contains formal logic, proof theory algorithms, and mechanized proofs related to Peano Arithmetic, Gentzen sequent calculi (LK/LJ), cut elimination (Hauptsatz), and ordinal analysis up to epsilon_0.

## Modules & Architecture

1. **src/sequent_calculus.py**: Formal abstract syntax trees for formulas, sequents (Gamma |- Delta), and Gentzen LK / LJ proof trees.
2. **src/cut_elimination_modular.py**: Modular Gentzen cut-elimination engine featuring formula degree, cut rank, modular rank reduction, and degree reduction passes.
3. **src/proof_checker.py**: Deductive proof checker validating inference rules in classical LK and intuitionistic LJ, and verifying the subformula property.
4. **src/ordinal_analysis.py**: Constructive Cantor Normal Form ordinal arithmetic below epsilon_0, ordinal addition, fundamental sequences, and transfinite induction step verification.
5. **QandPA.v**: Coq formalization of Robinson Arithmetic (RA), Peano Arithmetic (PA), addition associativity, transitivity of order (LE_trans), and strong induction.
6. **proofs_with_omega.v**: Automated arithmetic proofs using the Coq Omega tactic.

## Dependencies

- Python 3.10+
- Coq (optional for .v batch compilation; verified by verify.py)

## Verification and Testing

To run the automated verification and unit test suite:

```bash
python3 verify.py
python3 -m unittest discover -s tests -p 'test_*.py'
```
