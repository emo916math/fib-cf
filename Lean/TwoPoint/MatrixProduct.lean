module

public import TwoPoint.HomogeneousEvaluation

/-!
# The ordered product of recurrence matrix powers

This module assembles Lemma `lem:F`: the homogeneous normalized matrix at
index `i` evaluates to `T₀^n ... Tᵢ₋₁^n`. The order is retained using list
products, because these matrices generally do not commute.
-/

@[expose] public section
noncomputable section

namespace TwoPoint

open Polynomial

variable {K : Type*} [Field K]

theorem NormalizedPadeBasis.matrix_zero {a b : K} {k : ℕ}
    (B : NormalizedPadeBasis a b k 0) : B.matrix = 1 := by
  apply Matrix.ext
  intro r c
  rw [eq_C_of_degree_le_zero (B.degree_entry r c), B.coeff_matrix]
  by_cases h : r = c <;> simp [Matrix.one_apply, h]

theorem NormalizedPadeBasis.homEval_zero {a b : K} {k : ℕ}
    (B : NormalizedPadeBasis a b k 0) (x y : K) : homEvalMatrix B.matrix 0 x y = 1 := by
  rw [B.matrix_zero]
  apply Matrix.ext
  intro r c
  by_cases h : r = c <;> simp [homEvalMatrix, homEval, Matrix.one_apply, h]

/-- A compatible family of normalized bases for all indices through `k`.
Compatibility follows from uniqueness; no extra choices are imposed. -/
structure PadeBasisChain (a b : K) (k : ℕ) where
  basis : (i : ℕ) → i ≤ k → NormalizedPadeBasis a b k i

theorem exists_padeBasisChain (a b : K) {k : ℕ} (hk : 0 < k)
    (hdelta : ∀ i, i ≤ k → deltaOver a b k i ≠ 0) : Nonempty (PadeBasisChain a b k) :=
  ⟨⟨fun i hi => Classical.choice (exists_normalizedPadeBasis a b hk hi (hdelta i hi))⟩⟩

/-- The unused transitions beyond `k` are set to the identity. -/
def PadeBasisChain.transition {a b : K} {k : ℕ} (S : PadeBasisChain a b k) (i : ℕ) :
    Matrix (Fin 2) (Fin 2) K :=
  if hi : i < k then
    (S.basis i (Nat.le_of_lt hi)).transitionMatrix (S.basis (i + 1) hi)
  else 1

theorem PadeBasisChain.transition_charpoly {a b : K} {k : ℕ}
    (S : PadeBasisChain a b k) (hdelta : ∀ i, i ≤ k → deltaOver a b k i ≠ 0)
    {i : ℕ} (hi : i < k) : (S.transition i).charpoly = characteristicPolynomial a b := by
  rw [transition, dite_eq_left hi]
  exact (S.basis i (Nat.le_of_lt hi)).transitionMatrix_charpoly
    (Nat.le_of_lt hi) (hdelta i (Nat.le_of_lt hi)) _

/-- Evaluation of every prefix is the ordered product of transition powers. -/
theorem PadeBasisChain.homEval_eq_prod (a b : ℤ) {k : ℕ}
    (S : PadeBasisChain (a : K) (b : K) k)
    (hdelta : ∀ i, i ≤ k → deltaOver (a : K) (b : K) k i ≠ 0)
    (n i : ℕ) (hi : i ≤ k) :
    homEvalMatrix (S.basis i hi).matrix i (u a b (n + 1) : K) (u a b n : K) =
      ((List.range i).map fun j => S.transition j ^ n).prod := by
  induction i with
  | zero => simpa using (S.basis 0 hi).homEval_zero (u a b (n + 1) : K) (u a b n : K)
  | succ i ih =>
    have hik : i < k := hi
    rw [(S.basis i (Nat.le_of_lt hik)).homEval_recurrence_step a b (Nat.le_of_lt hik)
      (hdelta i (Nat.le_of_lt hik)) (S.basis (i + 1) hi) n, ih (Nat.le_of_lt hik)]
    simp [List.range_succ, transition, hik]

/-- The first column of the complete product contains the required powers
of consecutive recurrence terms. -/
theorem PadeBasisChain.prod_first_column (a b : ℤ) {k : ℕ} (hk : 0 < k)
    (S : PadeBasisChain (a : K) (b : K) k)
    (hdelta : ∀ i, i ≤ k → deltaOver (a : K) (b : K) k i ≠ 0) (n : ℕ) :
    (((List.range k).map fun j => S.transition j ^ n).prod) 0 0 = (u a b (n + 1) : K) ^ k ∧
    (((List.range k).map fun j => S.transition j ^ n).prod) 1 0 = (u a b n : K) ^ k := by
  rw [← S.homEval_eq_prod a b hdelta n k le_rfl]
  exact (S.basis k le_rfl).homEval_terminal_column hk (hdelta k le_rfl) _ _

/-- The rational matrix factorization asserted in Lemma `lem:F`, expressed
without projective-line notation or a choice of a canonical continued fraction. -/
theorem exists_matrix_power_factorization (a b : ℤ) {k : ℕ} (hk : 0 < k)
    (hdelta : ∀ i, i ≤ k → delta a b k i ≠ 0) :
    ∃ T : ℕ → Matrix (Fin 2) (Fin 2) ℚ,
      (∀ i, i < k → (T i).charpoly = characteristicPolynomial (a : ℚ) (b : ℚ)) ∧
      ∀ n : ℕ,
        (((List.range k).map fun j => T j ^ n).prod) 0 0 = (u a b (n + 1) : ℚ) ^ k ∧
        (((List.range k).map fun j => T j ^ n).prod) 1 0 = (u a b n : ℚ) ^ k := by
  have hd : ∀ i, i ≤ k → deltaOver (a : ℚ) (b : ℚ) k i ≠ 0 := by
    intro i hi
    have hm := deltaOver_map (Int.castRingHom ℚ) a b k i
    dsimp at hm
    rw [← hm]
    exact_mod_cast (show deltaOver a b k i ≠ 0 by rw [← delta_eq_deltaOver]; exact hdelta i hi)
  obtain ⟨S⟩ := exists_padeBasisChain (a : ℚ) (b : ℚ) hk hd
  exact ⟨S.transition, fun _ hi => S.transition_charpoly hd hi,
    fun n => S.prod_first_column a b hk hd n⟩

end TwoPoint
