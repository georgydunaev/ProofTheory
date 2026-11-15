# Peano Arithmetic Order Properties and Constructive Proof Notes (`ProofTheory`)

This document details the mathematical analysis and constructive Coq proofs (`Qed.`) in [PA_Order_Completions.v](PA_Order_Completions.v) that complete the unfinished order lemmas, `LE_trans` applications, and well-ordering / least-number drafts in [QandPA.v](QandPA.v).

---

## 1. Summary of Historical Gaps in `QandPA.v`

In [QandPA.v](QandPA.v), the existential order relation on `N` is defined at line 147 by:
```coq
Definition LE (x y : N) := exists z, (AD x z = y).
Definition LT z y := (LE (SU z) y).
```
Several historical proof attempts were left inside commented blocks or terminated with `Abort.`:
1. **Lines 266–294 (`Q4_sym` and `l_1_5`)**:
   - Inside the commented-out exploratory module `TheoremsAboutTerms`, `Q4_sym : forall x : N, AD ZE x = x` was attempted by case analysis (`Q3`) without full induction `IND`, and `Lemma l_1_5 : forall (m : nat) (x : N), LE x (num m) \/ LE (num m) x` was left with `admit. ... Abort.` at lines 291–293.
   - **Why Robinson Arithmetic (`RA`) Alone Cannot Prove `AD ZE x = x`**: In standard non-commutative models of Robinson Arithmetic $Q$ (such as polynomial-like models with two infinite elements $a \neq b$ where $0 + a = b$ and $a + 0 = a$), the right-zero axiom `Q4` ($\forall x,\, x + 0 = x$) holds while the left-zero identity $\forall x,\, 0 + x = x$ fails. Once the Peano induction schema `IND` is available (`Module TheoremsPA`), `AD_0_l : forall x : N, AD ZE x = x` is proved in 4 lines.
2. **Line 568 (`LE_trans` and Strong Induction)**:
   - `LE_trans : forall a b c : N, LE a b -> LE b c -> LE a c` is proved at lines 568–579 using `AD_assoc` and immediately used at line 602 to close `strong_induction_all` and `strong_induction`.
   - However, the remaining order-theoretic properties of `LE` (reflexivity, successor monotonicity, additive cancellation, antisymmetry, discreteness dichotomy, totality `LE_total`, and decidability `LE_dec` / `eq_dec_N`) were not yet stated in `QandPA.v`.
3. **Lines 638–674 (`wol1`, `WO`, and Existential `LNP`)**:
   - `Lemma wol1` (line 638) was aborted at line 661 at the step requiring `forall q : N, X q -> LE (SU y) q` from the strong induction hypothesis `G : forall z : N, LE z y -> ~ X z`.
   - **Key Discovery**: Unlike `WO` and existential `LNP` (which genuinely require decidability of `F` in Intuitionistic PA), `Lemma wol1` (`~(exists y, X y /\ forall z, X z -> LE y z) -> forall z, ~ X z`) has a negated conclusion `~ X z` and is **constructively provable in pure Intuitionistic Peano Arithmetic without any excluded-middle or decidability assumption** once `LE_total` and `LE_eq_or_succ_le` are established!

---

## 2. Verified Constructive Theorems in `PA_Order_Completions.v`

All 19 theorems below are proved inside `Module PA_Order_Theorems (a : Ari) (ra : RA a) (pa : PA a ra)` in [PA_Order_Completions.v](PA_Order_Completions.v) and verified via `coqc`:

| # | Theorem | Statement | Status |
|---|---|---|---|
| 1 | `Q4_sym` | `forall x : N, AD ZE x = x` | `Qed.` |
| 2 | `LE_refl` | `forall x : N, LE x x` | `Qed.` |
| 3 | `LE_trans_qed` | `forall a b c : N, LE a b -> LE b c -> LE a c` | `Qed.` |
| 4 | `LE_succ_r` | `forall x y : N, LE x y -> LE x (SU y)` | `Qed.` |
| 5 | `LE_succ_self` | `forall x : N, LE x (SU x)` | `Qed.` |
| 6 | `LE_succ_iff` | `forall x y : N, LE x y <-> LE (SU x) (SU y)` | `Qed.` |
| 7 | `AD_eq_zero` | `forall x y : N, AD x y = ZE -> x = ZE /\ y = ZE` | `Qed.` |
| 8 | `neq_succ_add` | `forall x w : N, x = SU (AD x w) -> False` | `Qed.` |
| 9 | `AD_cancel_l` | `forall x y z : N, AD x y = AD x z -> y = z` | `Qed.` |
| 10 | `LE_antisym` | `forall x y : N, LE x y -> LE y x -> x = y` | `Qed.` |
| 11 | `LE_eq_or_succ_le` | `forall x y : N, LE x y -> x = y \/ LE (SU x) y` | `Qed.` |
| 12 | `LE_step_totality` | `forall x y : N, (LE x y \/ LE y x) -> (LE x (SU y) \/ LE (SU y) x)` | `Qed.` |
| 13 | `l_1_5` | `forall (m : nat) (x : N), LE x (num m) \/ LE (num m) x` | `Qed.` |
| 14 | `LE_total` | `forall x y : N, LE x y \/ LE y x` | `Qed.` |
| 15 | `LT_trichotomy` | `forall x y : N, LT x y \/ x = y \/ LT y x` | `Qed.` |
| 16 | `LT_not_LE` | `forall x y : N, LT x y -> LE y x -> False` | `Qed.` |
| 17 | `eq_dec_N` | `forall x y : N, x = y \/ x <> y` | `Qed.` |
| 18 | `LE_dec` | `forall x y : N, LE x y \/ ~ LE x y` | `Qed.` |
| 19 | `wol1` | `forall (X : N -> Prop), ~(exists y, X y /\ forall z, X z -> LE y z) -> forall z, ~ X z` | `Qed.` |
| 20 | `bounded_least_witness` | `forall F (Hdec : forall x, F x \/ ~ F x) n, (exists y, LE y n /\ F y /\ forall z, F z -> LE y z) \/ (forall z, LE z n -> ~ F z)` | `Qed.` |
| 21 | `WO_dec` | `forall F (Hdec : forall x, F x \/ ~ F x), (exists y, F y) -> (exists y, F y /\ forall z, F z -> LE y z)` | `Qed.` |
| 22 | `LNP_existential_dec` | `forall F (Hdec : forall x, F x \/ ~ F x), (exists y, F y) -> (exists y, F y /\ forall z, LT z y -> ~ F z)` | `Qed.` |

---

## 3. Proof Architecture Highlights

### 3.1 How `LE_eq_or_succ_le` Closes `l_1_5` and `LE_total`
Given `LE y x`, unpack the witness `z` such that `AD y z = x`. By `Q3 z`, either:
- `z = ZE`, so `x = AD y ZE = y` (`x = y`), or
- `z = SU z'`, so `x = AD y (SU z') = AD (SU y) z'` by `AD_sym_lem`, which witnesses `LE (SU y) x`.

In the inductive step of `l_1_5` (at `S m`, where `num (S m) = SU (num m)`):
- If `LE x (num m)`, then `LE x (SU (num m))` by `LE_succ_r`.
- If `LE (num m) x`, then by `LE_eq_or_succ_le`, either `num m = x` (so `LE x (SU (num m))` by `LE_succ_self`) or `LE (SU (num m)) x`.

### 3.2 How `LE_total` Closes `wol1` Without Excluded Middle
In `wol1`, given `G : forall z, LE z y -> ~ X z` and `hsy : X (SU y)`, to prove `forall z, X z -> LE (SU y) z`:
- By `LE_total (SU y) z`, either `LE (SU y) z` (done) or `LE z (SU y)`.
- In the second case, `LE_eq_or_succ_le z (SU y)` gives either `z = SU y` (so `LE (SU y) z` by `LE_refl`) or `LE (SU z) (SU y)`.
- Applying `LE_redu` to `LE (SU z) (SU y)` yields `LE z y`, which contradicts `G z : LE z y -> ~ X z` and `Hz : X z`.
