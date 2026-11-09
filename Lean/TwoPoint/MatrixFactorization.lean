module

public import TwoPoint.PadeBasis
public import TwoPoint.Recurrence
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.Algebra.Polynomial.Homogenize

/-!
# The linear factors between consecutive normalized Padé bases

This is the matrix step in Lemma `lem:F` of
`ODorney_TwoPoint_Fibonacci(4).tex`.
-/

@[expose] public section

noncomputable section

namespace TwoPoint

open Polynomial
open scoped BigOperators

variable {K : Type*} [Field K]

private theorem degree_sub_X_mul_le (P Q : Polynomial K) (i : ℕ)
    (hP : P.degree ≤ (i + 1 : ℕ)) (hQ : Q.degree ≤ i)
    (hc : P.coeff (i + 1) = Q.coeff i) : (P - X * Q).degree ≤ (i : WithBot ℕ) := by
  rw [degree_le_iff_coeff_zero]
  intro n hn
  have hni : i < n := by exact_mod_cast hn
  rw [coeff_sub]
  by_cases h : n = i + 1
  · subst n
    rw [coeff_X_mul, hc, sub_self]
  · have hp : P.coeff n = 0 := coeff_eq_zero_of_degree_lt
      (hP.trans_lt (by exact_mod_cast (show i + 1 < n by omega)))
    have hq : Q.coeff (n - 1) = 0 := coeff_eq_zero_of_degree_lt
      (hQ.trans_lt (by exact_mod_cast (show i < n - 1 by omega)))
    rw [hp, show n = (n - 1) + 1 by omega, coeff_X_mul, hq, sub_self]

/-- Subtracting `X` times the preceding basis cancels the highest-degree terms
and leaves columns in the preceding Padé space. -/
theorem NormalizedPadeBasis.step_difference {a b : K} {k i : ℕ}
    (B : NormalizedPadeBasis a b k i) (B' : NormalizedPadeBasis a b k (i + 1))
    (c : Fin 2) :
    IsPadePair a b k i (B'.matrix 0 c - X * B.matrix 0 c)
      (B'.matrix 1 c - X * B.matrix 1 c) where
  degree_num := degree_sub_X_mul_le _ _ i (B'.degree_entry 0 c) (B.degree_entry 0 c)
    ((B'.coeff_matrix 0 c).trans (B.coeff_matrix 0 c).symm)
  degree_den := degree_sub_X_mul_le _ _ i (B'.degree_entry 1 c) (B.degree_entry 1 c)
    ((B'.coeff_matrix 1 c).trans (B.coeff_matrix 1 c).symm)
  relation := by
    have hd := dvd_trans (pow_dvd_pow (characteristicPolynomial a b) (Nat.le_succ i))
      (B'.isPade c).relation
    convert dvd_sub hd (dvd_mul_of_dvd_right (B.isPade c).relation X) using 1; ring

/-- Constant coefficient matrix of the remainder after cancelling the top degree. -/
def NormalizedPadeBasis.stepMatrix {a b : K} {k i : ℕ}
    (B : NormalizedPadeBasis a b k i) (B' : NormalizedPadeBasis a b k (i + 1)) :
    Matrix (Fin 2) (Fin 2) K :=
  fun r c => (B'.matrix r c - X * B.matrix r c).coeff i

/-- `X I + M`, where `M` is a constant matrix. -/
def linearFactor (M : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2) (Fin 2) (Polynomial K) :=
  (X : Polynomial K) • (1 : Matrix (Fin 2) (Fin 2) (Polynomial K)) + M.map C

theorem NormalizedPadeBasis.step_factorization {a b : K} {k i : ℕ} (hi : i ≤ k)
    (hdelta : deltaOver a b k i ≠ 0)
    (B : NormalizedPadeBasis a b k i) (B' : NormalizedPadeBasis a b k (i + 1)) :
    B'.matrix = B.matrix * linearFactor (B.stepMatrix B') := by
  rw [linearFactor, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
  apply Matrix.ext
  intro r c
  have hs := B.span hi hdelta (B.step_difference B' c)
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.map_apply, stepMatrix]
  have hr : r = 0 ∨ r = 1 := by omega
  rcases hr with rfl | rfl
  · simpa only [mul_comm, add_comm, add_left_comm, add_assoc] using eq_add_of_sub_eq hs.1
  · simpa only [mul_comm, add_comm, add_left_comm, add_assoc] using eq_add_of_sub_eq hs.2

/-- Taking determinants gives the characteristic polynomial of a linear factor. -/
theorem NormalizedPadeBasis.det_linearFactor {a b : K} {k i : ℕ} (hi : i ≤ k)
    (hdelta : deltaOver a b k i ≠ 0)
    (B : NormalizedPadeBasis a b k i) (B' : NormalizedPadeBasis a b k (i + 1)) :
    (linearFactor (B.stepMatrix B')).det = characteristicPolynomial a b := by
  have hd := congrArg Matrix.det (B.step_factorization hi hdelta B')
  rw [Matrix.det_mul, B.det, B'.det, pow_succ] at hd
  exact mul_left_cancel₀ (pow_ne_zero _ (characteristicPolynomial_monic a b).ne_zero) hd.symm

/-- The characteristic polynomial of the negative step matrix is `h`. -/
theorem NormalizedPadeBasis.charpoly_neg_stepMatrix {a b : K} {k i : ℕ} (hi : i ≤ k)
    (hdelta : deltaOver a b k i ≠ 0)
    (B : NormalizedPadeBasis a b k i) (B' : NormalizedPadeBasis a b k (i + 1)) :
    (-(B.stepMatrix B')).charpoly = characteristicPolynomial a b := by
  rw [Matrix.charpoly]
  convert B.det_linearFactor hi hdelta B' using 2
  apply Matrix.ext
  intro r c
  simp [Matrix.charmatrix, linearFactor, Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]

/-- Reflection about half the trace preserves this quadratic characteristic
polynomial. In dimension two the reflected matrix is the adjugate. -/
theorem charpoly_reflection (a b : K) (A : Matrix (Fin 2) (Fin 2) K)
    (hA : A.charpoly = characteristicPolynomial a b) :
    (a • (1 : Matrix (Fin 2) (Fin 2) K) - A).charpoly = characteristicPolynomial a b := by
  have ht : A.trace = a := by
    have hc := congrArg (fun p : Polynomial K => p.coeff 1) hA
    simpa [Matrix.charpoly_fin_two, characteristicPolynomial] using hc
  have hd : A.det = -b := by
    have hc := congrArg (fun p : Polynomial K => p.coeff 0) hA
    simpa [Matrix.charpoly_fin_two, characteristicPolynomial] using hc
  have ht' : (a • (1 : Matrix (Fin 2) (Fin 2) K) - A).trace = a := by
    simp [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, ht]
    ring
  have hd' : (a • (1 : Matrix (Fin 2) (Fin 2) K) - A).det = -b := by
    simp only [Matrix.trace_fin_two] at ht
    simp only [Matrix.det_fin_two] at hd
    simp [Matrix.det_fin_two, Matrix.sub_apply, Matrix.smul_apply]
    linear_combination hd - a * ht
  rw [Matrix.charpoly_fin_two, ht', hd']
  simp [characteristicPolynomial, sub_eq_add_neg]

/-- The constant matrix `T_i` of Lemma `lem:F`. -/
def NormalizedPadeBasis.transitionMatrix {a b : K} {k i : ℕ}
    (B : NormalizedPadeBasis a b k i) (B' : NormalizedPadeBasis a b k (i + 1)) :
    Matrix (Fin 2) (Fin 2) K := a • 1 + B.stepMatrix B'

theorem NormalizedPadeBasis.transitionMatrix_charpoly {a b : K} {k i : ℕ} (hi : i ≤ k)
    (hdelta : deltaOver a b k i ≠ 0)
    (B : NormalizedPadeBasis a b k i) (B' : NormalizedPadeBasis a b k (i + 1)) :
    (B.transitionMatrix B').charpoly = characteristicPolynomial a b := by
  simpa only [transitionMatrix, sub_neg_eq_add] using
    charpoly_reflection a b (-(B.stepMatrix B')) (B.charpoly_neg_stepMatrix hi hdelta B')

/-- Cayley–Hamilton in the form used by the recurrence power identity. -/
theorem matrix_quadratic_of_charpoly (a b : K) (T : Matrix (Fin 2) (Fin 2) K)
    (hT : T.charpoly = characteristicPolynomial a b) :
    T * T = a • T + b • (1 : Matrix (Fin 2) (Fin 2) K) := by
  have hz := Matrix.aeval_self_charpoly T
  rw [hT] at hz
  simp only [characteristicPolynomial, map_sub, map_mul, aeval_X, aeval_C,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, pow_two] at hz
  exact (eq_add_of_sub_eq (sub_eq_zero.mp hz)).trans (add_comm _ _)

theorem NormalizedPadeBasis.transitionMatrix_quadratic {a b : K} {k i : ℕ} (hi : i ≤ k)
    (hdelta : deltaOver a b k i ≠ 0)
    (B : NormalizedPadeBasis a b k i) (B' : NormalizedPadeBasis a b k (i + 1)) :
    B.transitionMatrix B' * B.transitionMatrix B' =
      a • B.transitionMatrix B' + b • (1 : Matrix (Fin 2) (Fin 2) K) :=
  matrix_quadratic_of_charpoly a b _ (B.transitionMatrix_charpoly hi hdelta B')

/-- The transition matrices are invertible whenever `b` is nonzero. -/
theorem NormalizedPadeBasis.transitionMatrix_isUnit {a b : K} {k i : ℕ} (hi : i ≤ k)
    (hdelta : deltaOver a b k i ≠ 0) (hb : b ≠ 0)
    (B : NormalizedPadeBasis a b k i) (B' : NormalizedPadeBasis a b k (i + 1)) :
    IsUnit (B.transitionMatrix B') := by
  have hc := congrArg (fun p : Polynomial K => p.coeff 0)
    (B.transitionMatrix_charpoly hi hdelta B')
  have hd : (B.transitionMatrix B').det = -b := by
    simpa [Matrix.charpoly_fin_two, characteristicPolynomial] using hc
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [hd]
  exact isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr hb)

/-- The powers of each transition matrix are given by the original integer
recurrence, after changing the coefficient field. -/
theorem NormalizedPadeBasis.transitionMatrix_pow (a b : ℤ) {k i : ℕ} (hi : i ≤ k)
    (hdelta : deltaOver (a : K) (b : K) k i ≠ 0)
    (B : NormalizedPadeBasis (a : K) (b : K) k i)
    (B' : NormalizedPadeBasis (a : K) (b : K) k (i + 1)) (n : ℕ) :
    B.transitionMatrix B' ^ (n + 1) =
      (u a b (n + 1) : K) • B.transitionMatrix B' +
      ((b * u a b n : ℤ) : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
  have hT := B.transitionMatrix_quadratic hi hdelta B'
  simp only [Int.cast_smul_eq_zsmul] at hT ⊢
  exact pow_eq_recurrence a b _ hT n

end TwoPoint
