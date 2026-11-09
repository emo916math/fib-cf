module

public import TwoPoint.Pade
public import TwoPoint.PadeBasis

/-!
# No super-sized monsters

This module formalizes Lemma `lem:no_super` of the paper, in the stronger
form needed for the monster terms of Theorem 1.2(a): a nonzero Padé pair of
degree at most `d < k` has contact order at most `d + 1` with `h`.

The proof follows the paper's logarithmic derivative, cleared of
denominators: for `F = X^k Q - P`, the Wronskian-type polynomial
`X P' Q - X P Q' - k P Q` is a combination of `F` and `X F'`, so it inherits
all but one order of contact; its degree is too small unless it vanishes,
and its top coefficient shows that it does not vanish.
-/

@[expose] public section
noncomputable section

namespace TwoPoint

open Polynomial

variable {K : Type*} [Field K]

/-- The Euler operator `X d/dX` multiplies each coefficient by its index. -/
theorem coeff_X_mul_derivative (P : K[X]) (j : ℕ) :
    (X * derivative P).coeff j = (j : K) * P.coeff j := by
  cases j with
  | zero => simp
  | succ j =>
    rw [coeff_X_mul, coeff_derivative]
    push_cast
    ring

theorem natDegree_X_mul_derivative_le (P : K[X]) :
    (X * derivative P).natDegree ≤ P.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro j hj
  rw [coeff_X_mul_derivative, coeff_eq_zero_of_natDegree_lt (by exact_mod_cast hj), mul_zero]

/-- The cleared logarithmic derivative `X P' Q - X P Q' - k P Q`. -/
def padeWronskian (k : ℕ) (P Q : K[X]) : K[X] :=
  X * derivative P * Q - P * (X * derivative Q) - C (k : K) * (P * Q)

/-- The Wronskian is a combination of `F = X^k Q - P` and its Euler derivative. -/
theorem padeWronskian_eq (k : ℕ) (P Q : K[X]) :
    padeWronskian k P Q =
      -(X * derivative (X ^ k * Q - P)) * Q + (X ^ k * Q - P) * (X * derivative Q) +
        C (k : K) * ((X ^ k * Q - P) * Q) := by
  have hX : X * derivative (X ^ k : K[X]) = C (k : K) * X ^ k := by
    cases k with
    | zero => simp
    | succ k =>
      rw [derivative_X_pow]
      simp only [Nat.add_sub_cancel]
      ring
  have hd : X * derivative (X ^ k * Q - P) =
      (X * derivative (X ^ k : K[X])) * Q + X ^ k * (X * derivative Q) - X * derivative P := by
    rw [derivative_sub, derivative_mul]
    ring
  rw [padeWronskian, hd, hX]
  ring

theorem padeWronskian_natDegree_le (k : ℕ) (P Q : K[X]) :
    (padeWronskian k P Q).natDegree ≤ P.natDegree + Q.natDegree := by
  have h₁ : (X * derivative P * Q).natDegree ≤ P.natDegree + Q.natDegree :=
    natDegree_mul_le.trans (Nat.add_le_add_right (natDegree_X_mul_derivative_le P) _)
  have h₂ : (P * (X * derivative Q)).natDegree ≤ P.natDegree + Q.natDegree :=
    natDegree_mul_le.trans (Nat.add_le_add_left (natDegree_X_mul_derivative_le Q) _)
  have h₃ : (C (k : K) * (P * Q)).natDegree ≤ P.natDegree + Q.natDegree :=
    (natDegree_C_mul_le _ _).trans natDegree_mul_le
  unfold padeWronskian
  exact (natDegree_sub_le _ _).trans (max_le ((natDegree_sub_le _ _).trans (max_le h₁ h₂)) h₃)

/-- The top coefficient of the Wronskian. -/
theorem padeWronskian_coeff_top (k : ℕ) (P Q : K[X]) :
    (padeWronskian k P Q).coeff (P.natDegree + Q.natDegree) =
      ((P.natDegree : K) - Q.natDegree - k) * P.leadingCoeff * Q.leadingCoeff := by
  unfold padeWronskian
  rw [coeff_sub, coeff_sub, coeff_C_mul,
    coeff_mul_add_eq_of_natDegree_le (natDegree_X_mul_derivative_le P) le_rfl,
    coeff_mul_add_eq_of_natDegree_le le_rfl (natDegree_X_mul_derivative_le Q),
    coeff_mul_add_eq_of_natDegree_le le_rfl le_rfl,
    coeff_X_mul_derivative, coeff_X_mul_derivative]
  simp only [leadingCoeff]
  ring

/-- In characteristic zero, the Wronskian of two nonzero polynomials of
degree below `k` is nonzero: `P/Q` cannot be a constant multiple of `x^k`. -/
theorem padeWronskian_ne_zero [CharZero K] {k : ℕ} {P Q : K[X]} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hPk : P.natDegree < k) : padeWronskian k P Q ≠ 0 := by
  intro hW
  have hc := padeWronskian_coeff_top k P Q
  rw [hW, coeff_zero] at hc
  have hlc : P.leadingCoeff * Q.leadingCoeff ≠ 0 :=
    mul_ne_zero (leadingCoeff_ne_zero.mpr hP) (leadingCoeff_ne_zero.mpr hQ)
  have hz : ((P.natDegree : K) - Q.natDegree - k) = 0 := by
    rcases mul_eq_zero.mp (show ((P.natDegree : K) - Q.natDegree - k) *
        (P.leadingCoeff * Q.leadingCoeff) = 0 by rw [hc]; ring) with h | h
    · exact h
    · exact absurd h hlc
  have hn : (P.natDegree : K) = ((Q.natDegree + k : ℕ) : K) := by
    push_cast
    linear_combination hz
  have := Nat.cast_injective hn
  omega

/-- `h` is coprime to `X` when its constant term `-b` is nonzero. -/
theorem characteristicPolynomial_isCoprime_X (a b : K) (hb : b ≠ 0) :
    IsCoprime (characteristicPolynomial a b) X := by
  refine ⟨-C b⁻¹, C b⁻¹ * (X - C a), ?_⟩
  unfold characteristicPolynomial
  have : C b⁻¹ * C b = (1 : K[X]) := by rw [← C_mul, inv_mul_cancel₀ hb, C_1]
  linear_combination this

theorem characteristicPolynomial_ne_zero (a b : K) : characteristicPolynomial a b ≠ 0 :=
  (characteristicPolynomial_monic a b).ne_zero

theorem natDegree_hPower (a b : K) (m : ℕ) :
    (characteristicPolynomial a b ^ m).natDegree = 2 * m := by
  rw [hPower_natDegree]

/-- A polynomial of degree below `2 m` divisible by `h^m` vanishes. -/
theorem eq_zero_of_hPower_dvd (a b : K) {m : ℕ} {F : K[X]}
    (hdvd : characteristicPolynomial a b ^ m ∣ F) (hF : F.natDegree < 2 * m) : F = 0 :=
  eq_zero_of_dvd_of_natDegree_lt hdvd (by rwa [natDegree_hPower])

/-- In a nonzero Padé pair of contact order `m` with degrees below `2 m`,
both the numerator and the denominator are nonzero. -/
theorem padePair_both_ne_zero (a b : K) (hb : b ≠ 0) {k m : ℕ} {P Q : K[X]}
    (hP : P.natDegree < 2 * m) (hQ : Q.natDegree < 2 * m) (hPQ : ¬(P = 0 ∧ Q = 0))
    (hdiv : characteristicPolynomial a b ^ m ∣ X ^ k * Q - P) : P ≠ 0 ∧ Q ≠ 0 := by
  constructor
  · rintro rfl
    apply hPQ
    refine ⟨rfl, eq_zero_of_hPower_dvd a b ?_ hQ⟩
    have hc := ((characteristicPolynomial_isCoprime_X a b hb).pow (m := m) (n := k))
    rw [sub_zero] at hdiv
    exact hc.dvd_of_dvd_mul_left hdiv
  · rintro rfl
    apply hPQ
    refine ⟨eq_zero_of_hPower_dvd a b ?_ hP, rfl⟩
    rw [mul_zero, zero_sub, dvd_neg] at hdiv
    exact hdiv

/-- The Wronskian loses at most one order of contact. -/
theorem padeWronskian_dvd (a b : K) {k m : ℕ} {P Q : K[X]}
    (hdiv : characteristicPolynomial a b ^ m ∣ X ^ k * Q - P) :
    characteristicPolynomial a b ^ (m - 1) ∣ padeWronskian k P Q := by
  have hF : characteristicPolynomial a b ^ (m - 1) ∣ X ^ k * Q - P :=
    (pow_dvd_pow _ (Nat.sub_le m 1)).trans hdiv
  have hF' := pow_sub_one_dvd_derivative_of_pow_dvd hdiv
  rw [padeWronskian_eq]
  exact dvd_add (dvd_add (dvd_mul_of_dvd_left (dvd_neg.mpr (dvd_mul_of_dvd_right hF' _)) _)
    (dvd_mul_of_dvd_left hF _)) (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hF _) _)

/-- **No super-sized monsters.** A nonzero Padé pair of degree at most
`d < k` has contact order at most `d + 1` with `h`. -/
theorem pade_contact_le [CharZero K] (a b : K) (hb : b ≠ 0) {k d m : ℕ} (hdk : d < k)
    {P Q : K[X]} (hP : P.natDegree ≤ d) (hQ : Q.natDegree ≤ d) (hPQ : ¬(P = 0 ∧ Q = 0))
    (hdiv : characteristicPolynomial a b ^ m ∣ X ^ k * Q - P) : m ≤ d + 1 := by
  by_contra hm
  replace hm : d + 1 < m := lt_of_not_ge hm
  obtain ⟨hP0, hQ0⟩ := padePair_both_ne_zero a b hb (by omega) (by omega) hPQ hdiv
  have hW := padeWronskian_dvd a b hdiv
  have hW0 := eq_zero_of_hPower_dvd a b hW
    (lt_of_le_of_lt (padeWronskian_natDegree_le k P Q) (by omega))
  exact padeWronskian_ne_zero hP0 hQ0 (by omega) hW0

/-- Dividing a Padé pair by a common factor of degree at least `e` lowers
the available degree bound by `e`. -/
theorem pade_contact_add_le_of_factor [CharZero K] (a b : K) (hb : b ≠ 0) {k d m e : ℕ}
    (hdk : d < k) {z P Q : K[X]} (hz : z ≠ 0) (hze : e ≤ z.natDegree)
    (hP : (z * P).natDegree ≤ d) (hQ : (z * Q).natDegree ≤ d) (hPQ : ¬(P = 0 ∧ Q = 0))
    (hdiv : characteristicPolynomial a b ^ m ∣ X ^ k * Q - P) : m + e ≤ d + 1 := by
  have hbound (R : K[X]) (hR : (z * R).natDegree ≤ d) :
      R = 0 ∨ (e ≤ d ∧ R.natDegree ≤ d - e) := by
    by_cases h0 : R = 0
    · exact Or.inl h0
    · rw [natDegree_mul hz h0] at hR
      exact Or.inr ⟨by omega, by omega⟩
  have hed : e ≤ d := by
    by_cases h0 : P = 0
    · have hQ0 : Q ≠ 0 := fun h => hPQ ⟨h0, h⟩
      rcases hbound Q hQ with h | h
      · exact absurd h hQ0
      · exact h.1
    · rcases hbound P hP with h | h
      · exact absurd h h0
      · exact h.1
  have hdeg (R : K[X]) (hR : (z * R).natDegree ≤ d) : R.natDegree ≤ d - e := by
    rcases hbound R hR with h | h
    · simp [h]
    · exact h.2
  have := pade_contact_le a b hb (d := d - e) (by omega) (hdeg P hP) (hdeg Q hQ) hPQ hdiv
  omega

end TwoPoint
