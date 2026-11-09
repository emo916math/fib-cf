module

public import TwoPoint.MatrixFactorization

/-!
# Homogeneous evaluation of the Padé matrix factorization

The homogenization is Mathlib's `Polynomial.homogenize`. The multiplication
lemma keeps the degree bounds explicit, including polynomials whose degree
is smaller than the homogenizing degree.
-/

@[expose] public section
noncomputable section

namespace TwoPoint

open Polynomial

variable {K : Type*} [Field K]

/-- Evaluation of the degree-`d` homogenization at `(x,y)`. -/
def homEval (p : Polynomial K) (d : ℕ) (x y : K) : K :=
  MvPolynomial.eval ![x, y] (p.homogenize d)

@[simp] theorem homEval_add (p q : Polynomial K) (d : ℕ) (x y : K) :
    homEval (p + q) d x y = homEval p d x y + homEval q d x y := by
  simp [homEval]

@[simp] theorem homEval_sub (p q : Polynomial K) (d : ℕ) (x y : K) :
    homEval (p - q) d x y = homEval p d x y - homEval q d x y := by
  simp [homEval]

@[simp] theorem homEval_C (c : K) (d : ℕ) (x y : K) :
    homEval (C c) d x y = c * y ^ d := by simp [homEval]

@[simp] theorem homEval_X (x y : K) : homEval (X : Polynomial K) 1 x y = x := by
  simp [homEval]

theorem homEval_mul (p q : Polynomial K) {m n : ℕ}
    (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ n) (x y : K) :
    homEval (p * q) (m + n) x y = homEval p m x y * homEval q n x y := by
  simp [homEval, homogenize_mul p q hp hq]

theorem homEval_pow (p : Polynomial K) {d : ℕ} (hp : p.natDegree ≤ d)
    (n : ℕ) (x y : K) : homEval (p ^ n) (d * n) x y = homEval p d x y ^ n := by
  induction n with
  | zero => simp [homEval]
  | succ n ih =>
    rw [pow_succ, Nat.mul_succ, homEval_mul _ _
      (by simpa [Nat.mul_comm] using natDegree_pow_le_of_le n hp) hp, ih, pow_succ]

theorem homEval_characteristicPolynomial (a b x y : K) :
    homEval (characteristicPolynomial a b) 2 x y = x ^ 2 - a * x * y - b * y ^ 2 := by
  simp [homEval, characteristicPolynomial, mul_assoc]

/-- Entrywise homogeneous evaluation of a polynomial matrix. -/
def homEvalMatrix (A : Matrix (Fin 2) (Fin 2) (Polynomial K)) (d : ℕ) (x y : K) :
    Matrix (Fin 2) (Fin 2) K := fun r c => homEval (A r c) d x y

theorem homEvalMatrix_mul (A B : Matrix (Fin 2) (Fin 2) (Polynomial K)) {m n : ℕ}
    (hA : ∀ r c, (A r c).natDegree ≤ m) (hB : ∀ r c, (B r c).natDegree ≤ n)
    (x y : K) :
    homEvalMatrix (A * B) (m + n) x y =
      homEvalMatrix A m x y * homEvalMatrix B n x y := by
  apply Matrix.ext
  intro r c
  simp only [homEvalMatrix, Matrix.mul_apply, Fin.sum_univ_two, homEval_add]
  rw [homEval_mul _ _ (hA r 0) (hB 0 c), homEval_mul _ _ (hA r 1) (hB 1 c)]

theorem homEvalMatrix_det (A : Matrix (Fin 2) (Fin 2) (Polynomial K)) {d : ℕ}
    (hA : ∀ r c, (A r c).natDegree ≤ d) (x y : K) :
    (homEvalMatrix A d x y).det = homEval A.det (2 * d) x y := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two, homEval_sub, show 2 * d = d + d by omega,
    homEval_mul _ _ (hA 0 0) (hA 1 1), homEval_mul _ _ (hA 0 1) (hA 1 0)]
  rfl

theorem NormalizedPadeBasis.homEval_det {a b : K} {k i : ℕ}
    (B : NormalizedPadeBasis a b k i) (x y : K) :
    (homEvalMatrix B.matrix i x y).det = (x ^ 2 - a * x * y - b * y ^ 2) ^ i := by
  rw [homEvalMatrix_det _ (fun r c => natDegree_le_iff_degree_le.mpr (B.degree_entry r c)),
    B.det, homEval_pow _ (characteristicPolynomial_natDegree_le a b),
    homEval_characteristicPolynomial]

theorem NormalizedPadeBasis.homEval_recurrence_det (a b : ℤ) {k i : ℕ}
    (B : NormalizedPadeBasis (a : K) (b : K) k i) (n : ℕ) :
    (homEvalMatrix B.matrix i (u a b (n + 1) : K) (u a b n : K)).det =
      (-(b : K)) ^ (n * i) := by
  rw [B.homEval_det]
  have hn : (u a b (n + 1) : K) ^ 2 - (a : K) * (u a b (n + 1) : K) * (u a b n : K) -
      (b : K) * (u a b n : K) ^ 2 = (-(b : K)) ^ n := by
    have hz := congrArg (fun z : ℤ => (z : K)) (u_norm a b n)
    push_cast at hz
    exact hz
  rw [hn, pow_mul]

theorem NormalizedPadeBasis.homEval_recurrence_isUnit (a b : ℤ) (hb : (b : K) ≠ 0)
    {k i : ℕ} (B : NormalizedPadeBasis (a : K) (b : K) k i) (n : ℕ) :
    IsUnit (homEvalMatrix B.matrix i (u a b (n + 1) : K) (u a b n : K)) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [B.homEval_recurrence_det a b n]
  apply isUnit_iff_ne_zero.mpr
  exact pow_ne_zero _ (neg_ne_zero.mpr hb)

theorem linearFactor_degree (M : Matrix (Fin 2) (Fin 2) K) (r c : Fin 2) :
    (linearFactor M r c).natDegree ≤ 1 := by
  by_cases h : r = c <;> simp [linearFactor, h]

theorem homEvalMatrix_linearFactor (M : Matrix (Fin 2) (Fin 2) K) (x y : K) :
    homEvalMatrix (linearFactor M) 1 x y = x • 1 + y • M := by
  apply Matrix.ext
  intro r c
  by_cases h : r = c <;>
    simp [homEvalMatrix, linearFactor, h, homEval, mul_comm]

/-- The homogeneous form of the factorization between consecutive bases. -/
theorem NormalizedPadeBasis.homEval_step {a b : K} {k i : ℕ} (hi : i ≤ k)
    (hdelta : deltaOver a b k i ≠ 0)
    (B : NormalizedPadeBasis a b k i) (B' : NormalizedPadeBasis a b k (i + 1)) (x y : K) :
    homEvalMatrix B'.matrix (i + 1) x y =
      homEvalMatrix B.matrix i x y * ((x - a * y) • 1 + y • B.transitionMatrix B') := by
  rw [B.step_factorization hi hdelta B',
    homEvalMatrix_mul _ _ (fun r c => natDegree_le_iff_degree_le.mpr (B.degree_entry r c))
      (linearFactor_degree _), homEvalMatrix_linearFactor]
  congr 1
  simp only [transitionMatrix, smul_add, smul_smul, sub_smul]
  module

/-- A version of the matrix-power identity valid also at index zero. -/
theorem NormalizedPadeBasis.transitionMatrix_pow_all (a b : ℤ) {k i : ℕ} (hi : i ≤ k)
    (hdelta : deltaOver (a : K) (b : K) k i ≠ 0)
    (B : NormalizedPadeBasis (a : K) (b : K) k i)
    (B' : NormalizedPadeBasis (a : K) (b : K) k (i + 1)) (n : ℕ) :
    B.transitionMatrix B' ^ n =
      ((u a b (n + 1) : K) - (a : K) * (u a b n : K)) • 1 +
      (u a b n : K) • B.transitionMatrix B' := by
  cases n with
  | zero => simp
  | succ n =>
    rw [B.transitionMatrix_pow a b hi hdelta B' n]
    rw [show n + 1 + 1 = n + 2 by omega, u_add_two]
    push_cast
    module

/-- Evaluation at the recurrence pair turns each homogeneous linear factor
into the corresponding matrix power. -/
theorem NormalizedPadeBasis.homEval_recurrence_step (a b : ℤ) {k i : ℕ} (hi : i ≤ k)
    (hdelta : deltaOver (a : K) (b : K) k i ≠ 0)
    (B : NormalizedPadeBasis (a : K) (b : K) k i)
    (B' : NormalizedPadeBasis (a : K) (b : K) k (i + 1)) (n : ℕ) :
    homEvalMatrix B'.matrix (i + 1) (u a b (n + 1) : K) (u a b n : K) =
      homEvalMatrix B.matrix i (u a b (n + 1) : K) (u a b n : K) *
        B.transitionMatrix B' ^ n := by
  rw [B.homEval_step hi hdelta B', B.transitionMatrix_pow_all a b hi hdelta B' n]

/-- The final normalized basis contains the exact rational function `X^k/1`
as its first column. -/
theorem NormalizedPadeBasis.terminal_column {a b : K} {k : ℕ} (hk : 0 < k)
    (hdelta : deltaOver a b k k ≠ 0) (B : NormalizedPadeBasis a b k k) :
    B.matrix 0 0 = X ^ k ∧ B.matrix 1 0 = 1 := by
  have h : IsPadePair a b k k (X ^ k) 1 := by
    refine ⟨degree_X_pow_le _, ?_, ?_⟩
    · simp
    · simp
  apply (B.isPade 0).eq_of_coeff_eq le_rfl hdelta h
  · simp [B.coeff_matrix]
  · rw [B.coeff_matrix]
    change 0 = (1 : Polynomial K).coeff k
    symm
    apply coeff_eq_zero_of_degree_lt
    simpa only [degree_one] using (show (0 : WithBot ℕ) < (k : WithBot ℕ) by exact_mod_cast hk)

/-- The final homogeneous column is precisely `(x^k,y^k)`. -/
theorem NormalizedPadeBasis.homEval_terminal_column {a b : K} {k : ℕ} (hk : 0 < k)
    (hdelta : deltaOver a b k k ≠ 0) (B : NormalizedPadeBasis a b k k) (x y : K) :
    homEvalMatrix B.matrix k x y 0 0 = x ^ k ∧
      homEvalMatrix B.matrix k x y 1 0 = y ^ k := by
  obtain ⟨hP, hQ⟩ := B.terminal_column hk hdelta
  simp [homEvalMatrix, hP, hQ, homEval]

end TwoPoint
