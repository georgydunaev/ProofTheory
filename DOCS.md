# ProofTheory Documentation

This repository provides formalizations and verified algorithms in structural proof theory, formal arithmetic, incompleteness metatheory, and ordinal analysis.

See [ARCHITECTURE_AND_THEOREMS.md](file:///botworkspace/ProofTheory/ARCHITECTURE_AND_THEOREMS.md) for the complete architectural reference and theorem catalog.

## Core Components

### 1. Sequent Calculus (LK and LJ) (`src/sequent_calculus.py` and `src/proof_checker.py`)
- **Formulas**: Propositional connectives (`Atom`, `Not`, `And`, `Or`, `Imp`) with subformula generation and logical degree calculation.
- **Sequents**: `Gamma |- Delta` data structures supporting identity axiom checks (`is_axiom`) and intuitionistic single-succedent checks (`is_intuitionistic`).
- **Inference Rules**: Identity axiom (`Ax`), `Cut`, left/right conjunction (`L_And`, `R_And`), disjunction (`L_Or`, `R_Or`), implication (`L_Imp`, `R_Imp`), negation (`L_Not`, `R_Not`), weakening, contraction, and exchange.

### 2. Gentzen Cut Elimination (Hauptsatz) (`src/cut_elimination_modular.py`)
- **Cut Rank and Formula Degree**: Metrics governing termination of cut reductions.
- **Rank Reduction**: Permuting cuts upward when the cut formula is non-principal.
- **Degree Reduction**: Splitting principal cuts on compound formulas into cuts on subformulas of strictly lower degree.
- **Subformula Property**: Ensuring cut-free proofs only contain subformulas of the conclusion sequent.

### 3. Ordinal Analysis up to Epsilon-0 (`src/ordinal_analysis.py`)
- **Cantor Normal Form (`CNFOrdinal`)**: Ordinals below `epsilon_0` represented canonically as sums of `omega^beta * c`.
- **Ordinal Arithmetic**: Exact non-commutative ordinal addition obeying left-absorption laws (such as `1 + omega = omega`).
- **Fundamental Sequences**: Monotonically increasing sequences `alpha[n]` for limit ordinals, verified by `OrdinalAnalysis.verify_fundamental_sequence_strictly_increasing`.

### 4. Arithmetic in Coq (`QandPA.v`, `proofs_with_omega.v`, `examples/`)
- Formal module types for signatures (`Ari`), Robinson Arithmetic (`RA`), and Peano Arithmetic (`PA`).
- Inductive Robinson derivability predicate (`RD`) and its soundness theorem (`RD_sound`).
- Full proofs of addition and multiplication commutativity, associativity, distributivity, zero-product property, first-order induction (`PA_fo_induction_instance`), order transitivity (`LE_trans`), strong induction (`strong_induction`), constructive least number principle (`LNP`), and the standard `nat` model (`nat_pa`).

### 5. Gödel's First Incompleteness Theorem (`GodelFirst.v` and `src/godel_incompleteness.py`)
- Injective Cantor-pairing Gödel numbering for arithmetic terms and formulas (`code_term`, `code_formula` in Coq; bijective `godel_number_term`, `godel_number_formula` in Python).
- Formal diagonal substitution (`diag`, `DiagonalSystem`, `diagonal_lemma`) and provability representation (`ProofSystem`, `ProofRepresentation`, `ProvFm`).
- Complete Coq proofs of unprovability of the Gödel sentence `G` under consistency (`godel_first_unprovable_G`), unprovability of `Not G` under omega-consistency (`godel_first_unprovable_not_G`), and incompleteness for any arithmetic theory extending Robinson Arithmetic `Q` (`Robinson_Q_incompleteness`) and Peano Arithmetic `PA` (`Peano_PA_incompleteness`).
