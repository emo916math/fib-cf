module

public import TwoPoint.NoSuper
public import TwoPoint.Recurrence
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.Algebra.Polynomial.SpecificDegree

/-!
# The Padé approximant behind a monster term

When `Δ_{k,i}(a,b) = 0`, Lemma 2.1 gives a low-degree Padé pair. Combined with
`pade_contact_le`, this pair has exact contact order, coprime numerator and
denominator of the same exact degree, and nonvanishing denominator and error
at the dominant root `α`. These are the algebraic inputs to the monster-term
estimate of Theorem 1.2(a).
-/

@[expose] public section
noncomputable section

namespace TwoPoint

open Polynomial

/-! ## Irreducibility of `h` over `ℚ` -/

theorem GenAdmissible.characteristicPolynomial_irreducible {a b : ℤ} (hab : GenAdmissible a b) :
    Irreducible (characteristicPolynomial (a : ℚ) (b : ℚ)) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [characteristicPolynomial_natDegree]
    simp
  · intro r hr
    have hr' : r ^ 2 - (a : ℚ) * r - b = 0 := by
      simpa [characteristicPolynomial, IsRoot] using hr
    have hsq : (2 * r - a) * (2 * r - a) = ((a ^ 2 + 4 * b : ℤ) : ℚ) := by
      push_cast
      linear_combination 4 * hr'
    obtain ⟨s, hs⟩ := Rat.isSquare_intCast_iff.mp ⟨2 * r - a, hsq.symm⟩
    exact hab.discriminant_not_square s hs.symm

theorem aeval_alpha_characteristicPolynomial {a b : ℤ} (hab : GenAdmissible a b) :
    aeval (alpha a b) (characteristicPolynomial (a : ℚ) (b : ℚ)) = 0 := by
  simp only [characteristicPolynomial, map_sub, map_mul, aeval_X, aeval_C, map_pow,
    eq_ratCast, Rat.cast_intCast]
  rw [alpha_sq hab]
  ring

theorem minpoly_alpha {a b : ℤ} (hab : GenAdmissible a b) :
    minpoly ℚ (alpha a b) = characteristicPolynomial (a : ℚ) (b : ℚ) :=
  (minpoly.eq_of_irreducible_of_monic hab.characteristicPolynomial_irreducible
    (aeval_alpha_characteristicPolynomial hab) (characteristicPolynomial_monic _ _)).symm

/-- A rational polynomial vanishing at `α` is divisible by `h`. -/
theorem characteristicPolynomial_dvd_of_aeval_alpha {a b : ℤ} (hab : GenAdmissible a b)
    {F : ℚ[X]} (hF : aeval (alpha a b) F = 0) :
    characteristicPolynomial (a : ℚ) (b : ℚ) ∣ F := by
  rw [← minpoly_alpha hab]
  exact minpoly.dvd ℚ _ hF

/-! ## The exact Padé pair -/

/-- The algebraic data attached to a vanishing Padé–Toeplitz determinant:
a coprime pair of exact degree `d` with exact contact order `d + 1`. -/
structure MonsterPade (a b : ℚ) (k d : ℕ) (P Q E : ℚ[X]) : Prop where
  natDegree_num : P.natDegree = d
  natDegree_den : Q.natDegree = d
  relation : X ^ k * Q - P = E * characteristicPolynomial a b ^ (d + 1)
  coprime : IsCoprime P Q
  not_dvd_den : ¬ characteristicPolynomial a b ∣ Q
  not_dvd_err : ¬ characteristicPolynomial a b ∣ E

theorem natDegree_le_of_degree_lt_succ {K : Type*} [Field K] {P : K[X]} {d : ℕ}
    (h : P.degree < ↑(d + 1)) : P.natDegree ≤ d := by
  by_cases hP : P = 0
  · simp [hP]
  · exact Nat.lt_succ_iff.mp ((natDegree_lt_iff_degree_lt hP).mpr h)

/-- Lemma `lem:no_super`, second assertion, with the extra information used
for the monster estimate. -/
theorem exists_monsterPade {a b : ℤ} (hab : GenAdmissible a b) {k i : ℕ} (hi : i ≤ k)
    (hz : delta a b k i = 0) :
    ∃ d : ℕ, d < k ∧ ∃ P Q E : ℚ[X], MonsterPade (a : ℚ) (b : ℚ) k d P Q E := by
  obtain ⟨hi0, hik⟩ := delta_zero_index_bounds hi hz
  obtain ⟨P, Q, E, hE, hPdeg, hQdeg, -, hrel⟩ := (delta_eq_zero_iff_exists_pade a b hi).mp hz
  obtain ⟨d, rfl⟩ : ∃ d, i = d + 1 := ⟨i - 1, by omega⟩
  have hb : (b : ℚ) ≠ 0 := by exact_mod_cast hab.b_ne_zero
  set h := characteristicPolynomial (a : ℚ) (b : ℚ) with hh
  have hirr : Irreducible h := hab.characteristicPolynomial_irreducible
  have hP : P.natDegree ≤ d := natDegree_le_of_degree_lt_succ (by exact_mod_cast hPdeg)
  have hQ : Q.natDegree ≤ d := natDegree_le_of_degree_lt_succ (by exact_mod_cast hQdeg)
  have hdk : d < k := by omega
  have hPQ : ¬(P = 0 ∧ Q = 0) := by
    rintro ⟨rfl, rfl⟩
    have : E * h ^ (d + 1) = 0 := by rw [← hrel]; simp
    exact mul_ne_zero hE (pow_ne_zero _ (characteristicPolynomial_ne_zero _ _)) this
  have hdiv : h ^ (d + 1) ∣ X ^ k * Q - P := ⟨E, by rw [hrel, mul_comm]⟩
  -- The error is not divisible by `h`.
  have hnE : ¬ h ∣ E := by
    rintro ⟨E', rfl⟩
    have hdiv' : h ^ (d + 2) ∣ X ^ k * Q - P := ⟨E', by rw [hrel, pow_succ]; ring⟩
    have := pade_contact_le (a : ℚ) (b : ℚ) hb hdk hP hQ hPQ hdiv'
    omega
  -- The denominator is not divisible by `h`.
  have hnQ : ¬ h ∣ Q := by
    rintro ⟨Q', rfl⟩
    have hhP : h ∣ P := by
      have h1 : h ∣ X ^ k * (h * Q') := dvd_mul_of_dvd_right (dvd_mul_right _ _) _
      have h2 : h ∣ X ^ k * (h * Q') - P := (dvd_pow_self h (Nat.succ_ne_zero d)).trans hdiv
      simpa using dvd_sub h1 h2
    obtain ⟨P', rfl⟩ := hhP
    have hPQ' : ¬(P' = 0 ∧ Q' = 0) := by
      rintro ⟨rfl, rfl⟩
      exact hPQ ⟨by simp, by simp⟩
    have hdiv' : h ^ d ∣ X ^ k * Q' - P' := by
      have hcancel : h * (X ^ k * Q' - P') = h * (E * h ^ d) := by
        rw [pow_succ'] at hrel
        linear_combination hrel
      exact ⟨E, by rw [mul_left_cancel₀ (characteristicPolynomial_ne_zero _ _) hcancel,
        mul_comm]⟩
    have := pade_contact_add_le_of_factor (a : ℚ) (b : ℚ) hb (e := 2) hdk
      (characteristicPolynomial_ne_zero _ _)
      (by rw [characteristicPolynomial_natDegree]) hP hQ hPQ' hdiv'
    omega
  -- Numerator and denominator are coprime.
  have hcop : IsCoprime P Q := by
    apply isCoprime_of_irreducible_dvd hPQ
    intro z hz hzP hzQ
    by_cases hzh : IsCoprime z h
    · have hzE : z ∣ E := by
        have : z ∣ E * h ^ (d + 1) := hrel ▸ dvd_sub (dvd_mul_of_dvd_right hzQ _) hzP
        exact (hzh.pow_right).dvd_of_dvd_mul_right this
      obtain ⟨P', rfl⟩ := hzP
      obtain ⟨Q', rfl⟩ := hzQ
      obtain ⟨E', rfl⟩ := hzE
      have hz0 : z ≠ 0 := hz.ne_zero
      have hPQ' : ¬(P' = 0 ∧ Q' = 0) := by
        rintro ⟨rfl, rfl⟩
        exact hPQ ⟨by simp, by simp⟩
      have hdiv' : h ^ (d + 1) ∣ X ^ k * Q' - P' := by
        have hcancel : z * (X ^ k * Q' - P') = z * (E' * h ^ (d + 1)) := by
          linear_combination hrel
        exact ⟨E', by rw [mul_left_cancel₀ hz0 hcancel, mul_comm]⟩
      have hz1 : 1 ≤ z.natDegree := by
        by_contra h0
        have hdeg : z.natDegree = 0 := by omega
        exact hz.not_isUnit (isUnit_iff_degree_eq_zero.mpr
          (by rw [degree_eq_natDegree hz0, hdeg]; rfl))
      have := pade_contact_add_le_of_factor (a : ℚ) (b : ℚ) hb (e := 1) hdk hz0 hz1
        hP hQ hPQ' hdiv'
      omega
    · have hzh' : z ∣ h := by
        by_contra hn
        exact hzh ((Irreducible.coprime_iff_not_dvd hz).mpr hn)
      exact hnQ ((Irreducible.dvd_symm hz hirr hzh').trans hzQ)
  -- Both degrees are exact, by the Wronskian.
  obtain ⟨hP0, hQ0⟩ := padePair_both_ne_zero (a : ℚ) (b : ℚ) hb (by omega) (by omega) hPQ hdiv
  have hW0 := padeWronskian_ne_zero hP0 hQ0 (show P.natDegree < k by omega)
  have hWdvd := padeWronskian_dvd (a : ℚ) (b : ℚ) hdiv
  have hWdeg := natDegree_le_of_dvd hWdvd hW0
  rw [natDegree_hPower, Nat.add_sub_cancel] at hWdeg
  have hWle := padeWronskian_natDegree_le k P Q
  exact ⟨d, hdk, P, Q, E, ⟨by omega, by omega, hrel, hcop, hnQ, hnE⟩⟩

/-- Values at `α` of the denominator and the error are nonzero. -/
theorem MonsterPade.aeval_alpha_ne_zero {a b : ℤ} (hab : GenAdmissible a b) {k d : ℕ}
    {P Q E : ℚ[X]} (hM : MonsterPade (a : ℚ) (b : ℚ) k d P Q E) :
    aeval (alpha a b) Q ≠ 0 ∧ aeval (alpha a b) E ≠ 0 :=
  ⟨fun h => hM.not_dvd_den (characteristicPolynomial_dvd_of_aeval_alpha hab h),
    fun h => hM.not_dvd_err (characteristicPolynomial_dvd_of_aeval_alpha hab h)⟩

/-! ## Bézout identities with degree bounds -/

/-- For coprime `P`, `Q` with `deg P ≤ d = deg Q`, every polynomial of degree
at most `M ≥ 2d - 1` is a combination `A P + B Q` with `deg A, deg B ≤ M - d`.
This is the homogeneous form of the Bézout identity. -/
theorem exists_bezout_natDegree_le {K : Type*} [Field K] {P Q : K[X]} {d M : ℕ}
    (hcop : IsCoprime P Q) (hP : P.natDegree ≤ d) (hQ : Q.natDegree = d) (hQ0 : Q ≠ 0)
    (hM : 2 * d ≤ M + 1) (hdM : d ≤ M) (F : K[X]) (hF : F.natDegree ≤ M) :
    ∃ A B : K[X], A * P + B * Q = F ∧ A.natDegree ≤ M - d ∧ B.natDegree ≤ M - d := by
  obtain ⟨A₀, B₀, hAB⟩ := hcop
  let A := (F * A₀) % Q
  let B := F * B₀ + ((F * A₀) / Q) * P
  have hsum : A * P + B * Q = F := by
    have hdm := EuclideanDomain.div_add_mod (F * A₀) Q
    have : A = F * A₀ - Q * ((F * A₀) / Q) := by
      simp only [A]
      linear_combination hdm
    rw [this]
    simp only [B]
    linear_combination F * hAB
  have hA : A.natDegree + 1 ≤ d ∨ A = 0 := by
    by_cases hA0 : A = 0
    · exact Or.inr hA0
    · left
      have hlt := degree_mod_lt (F * A₀) hQ0
      rw [degree_eq_natDegree hA0, degree_eq_natDegree hQ0, hQ] at hlt
      exact_mod_cast hlt
  have hAle : A.natDegree ≤ M - d := by
    rcases hA with h | h
    · omega
    · simp [h]
  have hBQ : (B * Q).natDegree ≤ M := by
    have hBQ' : B * Q = F - A * P := by rw [← hsum]; ring
    rw [hBQ']
    refine (natDegree_sub_le _ _).trans (max_le hF ?_)
    rcases hA with h | h
    · exact natDegree_mul_le.trans (by omega)
    · simp [h]
  have hBle : B.natDegree ≤ M - d := by
    by_cases hB0 : B = 0
    · simp [hB0]
    · rw [natDegree_mul hB0 hQ0, hQ] at hBQ
      omega
  exact ⟨A, B, hsum, hAle, hBle⟩

end TwoPoint
