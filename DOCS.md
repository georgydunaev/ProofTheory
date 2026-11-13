# ProofTheory Documentation

This repository provides formalizations and verified algorithms in structural proof theory, arithmetic, and proof analysis.

## Core Components

### 1. Sequent Calculus (LK and LJ)
- **Formulas**: Propositional connectives (Atom, Not, And, Or, Imp) with subformula generation and degree calculation.
- **Sequents**: Gamma |- Delta data structures supporting classical and intuitionistic checks.
- **Inference Rules**: Identity axiom, Cut, left/right conjunction, disjunction, implication, negation, weakening, contraction, and exchange.

### 2. Gentzen Cut Elimination (Hauptsatz)
- **Cut Rank & Formula Degree**: Metrics governing termination of cut reductions.
- **Rank Reduction**: Permuting cuts upward when the cut formula is non-principal.
- **Degree Reduction**: Splitting cuts on compound formulas into cuts on subformulas of strictly lower degree.
- **Subformula Property**: Ensuring cut-free proofs only contain subformulas of the conclusion sequent.

### 3. Ordinal Analysis up to Epsilon-0
- **Cantor Normal Form**: Ordinals represented as sums of omega^beta * c.
- **Ordinal Arithmetic**: Exact addition obeying absorption laws (e.g. 1 + omega = omega).
- **Fundamental Sequences**: Monotonically increasing approximations alpha[n] for limit ordinals.

### 4. Arithmetic in Coq (QandPA.v)
- Formal definitions of Robinson Arithmetic (RA) and Peano Arithmetic (PA).
- Proven addition associativity (AD_assoc) and transitivity of order (LE_trans).
- Derived strong induction and constructive least number principles.
