# Project Overview: Sequent Calculus, Cut Elimination, and Arithmetic Proof Theory (`ProofTheory`)

## 1. Purpose and Scope
`ProofTheory` (`/botworkspace/ProofTheory`) implements mechanized Coq formalizations and executable Python engines covering Robinson Arithmetic (`Q`), Peano Arithmetic (`PA`), Goedel's First Incompleteness Theorem, Gentzen classical (`LK`) and intuitionistic (`LJ`) sequent calculi, modular cut elimination (`Hauptsatz`), and Cantor Normal Form ordinal analysis below `epsilon_0`. Compiled `.vo` files are strictly immutable per Fact 11.

## 2. Architecture and Modules
- **Coq Formalizations**:
  - [QandPA.v](file:///botworkspace/ProofTheory/QandPA.v) and [PA_Order_Completions.v](file:///botworkspace/ProofTheory/PA_Order_Completions.v) — Robinson Arithmetic (`RA`), Peano Arithmetic (`PA`), deductive soundness (`RD_sound`), semiring laws, induction schemas, linear order properties (`LE_trans`), strong induction, and Least Number Principle (`LNP`).
  - [GodelFirst.v](file:///botworkspace/ProofTheory/GodelFirst.v) — Goedel numbering (`code_term`, `code_formula`), diagonal substitution, the Goedel sentence `G`, and mechanized proofs of `godel_first_incompleteness`, `Robinson_Q_incompleteness`, and `Peano_PA_incompleteness`.
  - [proofs_with_omega.v](file:///botworkspace/ProofTheory/proofs_with_omega.v) and `examples/` — Automated Coq linear arithmetic proofs using `lia`.
- **Python Proof Theory Engines (`src/`)**:
  - [src/sequent_calculus.py](file:///botworkspace/ProofTheory/src/sequent_calculus.py) — First-order formula ASTs, sequents (`Gamma |- Delta`), and LK/LJ proof trees.
  - [src/cut_elimination_modular.py](file:///botworkspace/ProofTheory/src/cut_elimination_modular.py) — Gentzen cut-elimination engine with degree and rank reduction passes.
  - [src/proof_checker.py](file:///botworkspace/ProofTheory/src/proof_checker.py) — Deductive rule validator and subformula property verifier.
  - [src/ordinal_analysis.py](file:///botworkspace/ProofTheory/src/ordinal_analysis.py) — Cantor Normal Form ordinal arithmetic below `epsilon_0` and fundamental sequences.
  - [src/godel_incompleteness.py](file:///botworkspace/ProofTheory/src/godel_incompleteness.py) — Constructive Goedel numbering and diagonal fixpoint verifier.
- [ARCHITECTURE_AND_THEOREMS.md](file:///botworkspace/ProofTheory/ARCHITECTURE_AND_THEOREMS.md), [THEOREMS_INDEX.md](file:///botworkspace/ProofTheory/THEOREMS_INDEX.md), and [PA_ORDER_PROOF_NOTES.md](file:///botworkspace/ProofTheory/PA_ORDER_PROOF_NOTES.md) — Complete theorem catalog.

## 3. Verification
```bash
python3 -m unittest discover -s /botworkspace/ProofTheory/tests -p "test_*.py"
```
