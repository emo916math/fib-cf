module

public import TwoPoint.Determinants
public import Mathlib.Algebra.Polynomial.OfFn

/-!
# The Toeplitz system for two-point Padé approximation

This module formalizes the coefficient calculation in Lemma 2.1 of
`ODorney_TwoPoint_Fibonacci(4).tex`. Vectors use increasing coefficient order:
the vector `e` represents `E = ∑ s, e s * X^s`.
-/

@[expose] public section

noncomputable section

namespace TwoPoint

open Polynomial
open scoped BigOperators

theorem characteristicPolynomial_natDegree_le {R : Type*} [CommRing R] (a b : R) :
    (characteristicPolynomial a b).natDegree ≤ 2 := by
  unfold characteristicPolynomial
  compute_degree!

theorem hPower_natDegree_le {R : Type*} [CommRing R] (a b : R) (i : ℕ) :
    (characteristicPolynomial a b ^ i).natDegree ≤ 2 * i := by
  simpa [Nat.mul_comm] using
    natDegree_pow_le_of_le i (characteristicPolynomial_natDegree_le a b)

/-- Rewrite the integer-indexed coefficient convention as an ordinary
coefficient shifted by the degree of a monomial in the error polynomial. -/
theorem hPowerCoeff_shift {R : Type*} [CommRing R] (a b : R) (i r s : ℕ) :
    hPowerCoeff a b i ((i : ℤ) + (s : ℤ) - (r : ℤ)) =
      if s ≤ i + r then (characteristicPolynomial a b ^ i).coeff (i + r - s) else 0 := by
  unfold hPowerCoeff
  by_cases hs : s ≤ i + r
  · rw [ite_eq_left hs]
    by_cases hj : 0 ≤ (i : ℤ) + (s : ℤ) - (r : ℤ)
    · rw [ite_eq_left ⟨hj, by omega⟩]
      congr 1
      omega
    · rw [ite_eq_right (by omega)]
      symm
      apply coeff_eq_zero_of_natDegree_lt
      have := hPower_natDegree_le a b i
      omega
  · rw [ite_eq_right hs, ite_eq_right (by omega)]

/-! ## Toeplitz matrices of an arbitrary contact polynomial

The Padé–Toeplitz matrix `C_{k,i}` is built from the coefficients of `h^i`.
Everything below works for any polynomial `G` of degree at most `2i` in place
of `h^i`; Exercise `exer:invisible` uses `G = h^(i-1) (x - α)^2`. -/

/-- The `(k-i) × (k-i)` Toeplitz matrix of `G`: entry `(r,s)` is the coefficient
of `x^(i+r-s)` in `G` (zero when `s > i + r`). -/
def toeplitzOf {R : Type*} [CommRing R] (G : Polynomial R) (k i : ℕ) :
    Matrix (Fin (k - i)) (Fin (k - i)) R :=
  fun r s => if s.val ≤ i + r.val then G.coeff (i + r.val - s.val) else 0

theorem padeToeplitz_eq_toeplitzOf {R : Type*} [CommRing R] (a b : R) (k i : ℕ) :
    padeToeplitz a b k i = toeplitzOf (characteristicPolynomial a b ^ i) k i := by
  ext r s
  exact hPowerCoeff_shift a b i r.val s.val

/-- Multiplication by the Toeplitz matrix computes precisely the forbidden
middle coefficients of `E * G`. -/
theorem toeplitzOf_mulVec_eq_coeff {R : Type*} [CommRing R] [DecidableEq R]
    (G : Polynomial R) (k i : ℕ) (e : Fin (k - i) → R) (r : Fin (k - i)) :
    (toeplitzOf G k i).mulVec e r = (ofFn (k - i) e * G).coeff (i + r.val) := by
  rw [ofFn_eq_sum_monomial, Finset.sum_mul, finsetSum_coeff]
  unfold Matrix.mulVec dotProduct
  apply Finset.sum_congr rfl
  intro s _
  rw [← C_mul_X_pow_eq_monomial, mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  unfold toeplitzOf
  split_ifs with h <;> simp [h, mul_comm]

/-- Multiplication by the Toeplitz matrix computes precisely the forbidden
middle coefficients of `E * h^i`. -/
theorem padeToeplitz_mulVec_eq_coeff {R : Type*} [CommRing R] [DecidableEq R]
    (a b : R) (k i : ℕ) (e : Fin (k - i) → R) (r : Fin (k - i)) :
    (padeToeplitz a b k i).mulVec e r =
      (ofFn (k - i) e * characteristicPolynomial a b ^ i).coeff (i + r.val) := by
  rw [padeToeplitz_eq_toeplitzOf, toeplitzOf_mulVec_eq_coeff]

variable {F : Type*} [Field F] [DecidableEq F]

/-- A singular Toeplitz matrix is equivalent to a nonzero low-degree error
polynomial `E` for which the middle coefficients of `E * G` vanish. -/
theorem det_toeplitzOf_eq_zero_iff_exists_error (G : Polynomial F) (k i : ℕ) :
    (toeplitzOf G k i).det = 0 ↔ ∃ E : Polynomial F,
      E ≠ 0 ∧ E.degree < (k - i : ℕ) ∧ ∀ r : Fin (k - i), (E * G).coeff (i + r.val) = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨e, he, hker⟩
    refine ⟨ofFn (k - i) e, ?_, ofFn_degree_lt e, ?_⟩
    · intro hz
      apply he
      apply injective_ofFn (k - i)
      simpa using hz
    · intro r
      rw [← toeplitzOf_mulVec_eq_coeff]
      exact congrFun hker r
  · rintro ⟨E, hE, hdeg, hcoeff⟩
    have hnat : E.natDegree < k - i := (natDegree_lt_iff_degree_lt hE).mpr hdeg
    have hrecover := ofFn_comp_toFn_eq_id_of_natDegree_lt hnat
    refine ⟨toFn (k - i) E, ?_, ?_⟩
    · intro hz
      apply hE
      rw [← hrecover, hz, map_zero]
    · ext r
      rw [toeplitzOf_mulVec_eq_coeff, hrecover]
      exact hcoeff r

/-- Recover the numerator and denominator by splitting off the low and high
coefficients. The vanishing middle block is exactly what makes this possible. -/
theorem exists_pade_of_error_gen {k i : ℕ} (G : Polynomial F) (hG : G.natDegree ≤ 2 * i)
    (E : Polynomial F) (hE : E ≠ 0) (hdeg : E.degree < (k - i : ℕ))
    (hcoeff : ∀ r : Fin (k - i), (E * G).coeff (i + r.val) = 0) :
    ∃ P Q : Polynomial F, P.degree < i ∧ Q.degree < i ∧ X ^ k * Q - P = E * G := by
  let F' := E * G
  let P := -ofFn i (toFn i F')
  let Q := ofFn i (fun s : Fin i => F'.coeff (k + s.val))
  have hnat := (natDegree_lt_iff_degree_lt hE).mpr hdeg
  have hF : F'.natDegree < k + i := by
    have hmul := natDegree_mul_le (p := E) (q := G)
    dsimp [F']
    omega
  refine ⟨P, Q, ?_, ofFn_degree_lt _, ?_⟩
  · simpa only [P, degree_neg] using ofFn_degree_lt (toFn i F')
  · ext n
    change (X ^ k * Q - P).coeff n = F'.coeff n
    rw [coeff_sub, coeff_X_pow_mul']
    by_cases hnk : n < k
    · rw [ite_eq_right (by omega)]
      by_cases hni : n < i
      · simp [P, ofFn_coeff_eq_val_of_lt _ hni, toFn]
      · have hz : F'.coeff n = 0 := by
          have := hcoeff ⟨n - i, by omega⟩
          simpa only [show i + (n - i) = n by omega] using this
        simp [P, ofFn_coeff_eq_zero_of_ge _ (by omega : i ≤ n), hz]
    · rw [ite_eq_left (by omega)]
      have hni : i ≤ n := by omega
      simp only [P, coeff_neg, ofFn_coeff_eq_zero_of_ge _ hni, neg_zero, sub_zero]
      by_cases hq : n - k < i
      · simp only [Q, ofFn_coeff_eq_val_of_lt _ hq,
          show k + (n - k) = n by omega]
      · rw [ofFn_coeff_eq_zero_of_ge _ (by omega : i ≤ n - k)]
        symm
        exact coeff_eq_zero_of_natDegree_lt (by omega)

/-- Lemma 2.1 for an arbitrary contact polynomial `G` of degree at most `2i`. -/
theorem det_toeplitzOf_eq_zero_iff_exists_pade {k i : ℕ} (G : Polynomial F)
    (hG : G.natDegree ≤ 2 * i) :
    (toeplitzOf G k i).det = 0 ↔ ∃ P Q E : Polynomial F,
      E ≠ 0 ∧ P.degree < i ∧ Q.degree < i ∧ E.degree < (k - i : ℕ) ∧
        X ^ k * Q - P = E * G := by
  rw [det_toeplitzOf_eq_zero_iff_exists_error]
  constructor
  · rintro ⟨E, hE, hdeg, hcoeff⟩
    obtain ⟨P, Q, hP, hQ, heq⟩ := exists_pade_of_error_gen G hG E hE hdeg hcoeff
    exact ⟨P, Q, E, hE, hP, hQ, hdeg, heq⟩
  · rintro ⟨P, Q, E, hE, hP, _, hdeg, heq⟩
    refine ⟨E, hE, hdeg, ?_⟩
    intro r
    rw [← heq, coeff_sub, coeff_X_pow_mul', ite_eq_right (by omega)]
    have hz : P.coeff (i + r.val) = 0 := by
      apply coeff_eq_zero_of_degree_lt
      exact lt_of_lt_of_le hP (by exact_mod_cast Nat.le_add_right i r.val)
    rw [hz, sub_self]

/-- Determinant vanishing is equivalent to a nonzero low-degree error
polynomial for which all intermediate coefficients vanish. -/
theorem delta_eq_zero_iff_exists_error (a b : ℤ) (k i : ℕ) :
    delta a b k i = 0 ↔ ∃ E : Polynomial ℚ,
      E ≠ 0 ∧ E.degree < (k - i : ℕ) ∧
        ∀ r : Fin (k - i),
          (E * characteristicPolynomial (a : ℚ) (b : ℚ) ^ i).coeff (i + r.val) = 0 := by
  rw [delta_eq_zero_iff_exists_rat_kernel, Matrix.exists_mulVec_eq_zero_iff,
    padeToeplitz_eq_toeplitzOf]
  exact det_toeplitzOf_eq_zero_iff_exists_error _ k i

/-- Recover the numerator and denominator by splitting off the low and high
coefficients. -/
theorem exists_pade_of_error (a b : ℚ) {k i : ℕ} (hi : i ≤ k)
    (E : Polynomial ℚ) (hE : E ≠ 0) (hdeg : E.degree < (k - i : ℕ))
    (hcoeff : ∀ r : Fin (k - i),
      (E * characteristicPolynomial a b ^ i).coeff (i + r.val) = 0) :
    ∃ P Q : Polynomial ℚ, P.degree < i ∧ Q.degree < i ∧
      X ^ k * Q - P = E * characteristicPolynomial a b ^ i :=
  exists_pade_of_error_gen _ (hPower_natDegree_le a b i) E hE hdeg hcoeff

/-- Lemma 2.1: a vanishing determinant is equivalent to a nonzero error
polynomial in a Padé relation of unusually low degrees. -/
theorem delta_eq_zero_iff_exists_pade (a b : ℤ) {k i : ℕ} (hi : i ≤ k) :
    delta a b k i = 0 ↔ ∃ P Q E : Polynomial ℚ,
      E ≠ 0 ∧ P.degree < i ∧ Q.degree < i ∧ E.degree < (k - i : ℕ) ∧
        X ^ k * Q - P = E * characteristicPolynomial (a : ℚ) (b : ℚ) ^ i := by
  rw [delta_eq_zero_iff_exists_rat_kernel, Matrix.exists_mulVec_eq_zero_iff,
    padeToeplitz_eq_toeplitzOf]
  exact det_toeplitzOf_eq_zero_iff_exists_pade _ (hPower_natDegree_le _ _ i)

end TwoPoint
