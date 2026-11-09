module

public import TwoPoint.Junction
public import TwoPoint.MonsterPade
public import TwoPoint.MatrixProduct
public import TwoPoint.MonsterAsymptotics

/-!
# Eigenvectors of the transition matrices

Each transition matrix `T_i` is rational with `T_i² = a T_i + b`, so it has
eigenvalues `α`, `β` (the roots of `h`). Its lower-left entry is nonzero, and
its eigenvectors are `(ξ_i, 1)` and `(ξ'_i, 1)` with
`ξ_i = (α - t₁₁)/t₁₀` and `ξ'_i = (β - t₁₁)/t₁₀`, a conjugate pair.
-/

@[expose] public section
noncomputable section

namespace TwoPoint

open Polynomial

variable {a b : ℤ}

/-! ## The roots `α` and `β` -/

theorem alpha_add_beta (a b : ℤ) : alpha a b + beta a b = a := by simp [beta]

theorem beta_sq (hab : GenAdmissible a b) : beta a b ^ 2 = (a : ℝ) * beta a b + b := by
  have := alpha_sq hab
  unfold beta
  nlinarith

theorem alpha_sub_beta_sq (hab : GenAdmissible a b) :
    (alpha a b - beta a b) ^ 2 = (a : ℝ) ^ 2 + 4 * b := by
  have h1 := alpha_add_beta a b
  have h2 := alpha_mul_beta hab
  have : (alpha a b - beta a b) ^ 2 = (alpha a b + beta a b) ^ 2 - 4 * (alpha a b * beta a b) := by
    ring
  rw [this, h1, h2]
  ring

theorem two_lt_alpha_sub_beta (hab : GenAdmissible a b) : 2 < alpha a b - beta a b := by
  have hpos := alpha_sub_beta_pos hab
  have hsq := alpha_sub_beta_sq hab
  have hD : (5 : ℝ) ≤ (a : ℝ) ^ 2 + 4 * b := by
    -- `D > 0` is a non-square congruent to `a^2` modulo `4`.
    have hmod : a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := by
      rcases Int.even_or_odd a with ⟨r, rfl⟩ | ⟨r, rfl⟩ <;> ring_nf <;> omega
    have hD := hab.2.1
    have h1 := hab.discriminant_not_square 1
    have h2 := hab.discriminant_not_square 2
    have : (5 : ℤ) ≤ a ^ 2 + 4 * b := by
      norm_num at h1 h2
      omega
    exact_mod_cast this
  nlinarith

/-- A rational root of `x^2 - a x - b` is impossible. -/
theorem no_rat_root (hab : GenAdmissible a b) (q : ℚ) : q ^ 2 - a * q - b ≠ 0 := by
  intro hq
  have hirr := hab.characteristicPolynomial_irreducible
  have hroot : (characteristicPolynomial (a : ℚ) (b : ℚ)).IsRoot q := by
    simp [characteristicPolynomial, IsRoot]
    linear_combination hq
  have := degree_eq_one_of_irreducible_of_root hirr hroot
  rw [degree_eq_natDegree (characteristicPolynomial_monic _ _).ne_zero,
    characteristicPolynomial_natDegree] at this
  norm_num at this

theorem irrational_alpha (hab : GenAdmissible a b) : Irrational (alpha a b) := by
  rintro ⟨q, hq⟩
  apply no_rat_root hab q
  have := alpha_sq hab
  rw [← hq] at this
  exact_mod_cast (by linarith : ((q : ℝ) ^ 2 - a * q - b) = 0)

/-! ## Eigenvectors of a rational matrix with characteristic polynomial `h` -/

/-- The real matrix of a rational matrix. -/
def ratToReal (A : Matrix (Fin 2) (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℝ := A.map (Rat.cast)

theorem IsRatMat.ratToReal (A : Matrix (Fin 2) (Fin 2) ℚ) : IsRatMat (ratToReal A) :=
  fun i j => ⟨A i j, rfl⟩

theorem ratToReal_mul (A B : Matrix (Fin 2) (Fin 2) ℚ) :
    ratToReal (A * B) = ratToReal A * ratToReal B := by
  ext i j
  simp [ratToReal, Matrix.mul_apply, Fin.sum_univ_two]

theorem ratToReal_pow (A : Matrix (Fin 2) (Fin 2) ℚ) (n : ℕ) :
    ratToReal (A ^ n) = ratToReal A ^ n := by
  induction n with
  | zero =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ratToReal]
  | succ n ih => rw [pow_succ, ratToReal_mul, ih, pow_succ]

theorem ratToReal_det (A : Matrix (Fin 2) (Fin 2) ℚ) : (ratToReal A).det = (A.det : ℝ) := by
  simp [ratToReal, Matrix.det_fin_two]

/-- A rational `T` with `T² = aT + b` is not upper triangular. -/
theorem lower_ne_zero_of_quadratic (hab : GenAdmissible a b) (T : Matrix (Fin 2) (Fin 2) ℚ)
    (hT : T * T = (a : ℚ) • T + (b : ℚ) • 1) : T 1 0 ≠ 0 := by
  intro h0
  have h := congrFun (congrFun hT 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, h0] at h
  exact no_rat_root hab (T 0 0) (by linear_combination h)

/-- Entry identities for `T² = aT + b`. -/
theorem quadratic_entries (T : Matrix (Fin 2) (Fin 2) ℚ)
    (hT : T * T = (a : ℚ) • T + (b : ℚ) • 1) (hne : T 1 0 ≠ 0) :
    T 0 0 + T 1 1 = a ∧ T 0 0 * T 1 1 - T 0 1 * T 1 0 = -b := by
  have h00 := congrFun (congrFun hT 0) 0
  have h01 := congrFun (congrFun hT 0) 1
  have h10 := congrFun (congrFun hT 1) 0
  have h11 := congrFun (congrFun hT 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  have htr : T 0 0 + T 1 1 = a := by
    have : T 1 0 * (T 0 0 + T 1 1 - a) = 0 := by linear_combination h10
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hne
    · linarith
  refine ⟨htr, ?_⟩
  have : T 1 1 = a - T 0 0 := by linarith
  rw [this] at h11 ⊢
  linear_combination -h11

/-- The slope of the eigenvector for the eigenvalue `ρ`. -/
def eigSlope (T : Matrix (Fin 2) (Fin 2) ℚ) (ρ : ℝ) : ℝ := (ρ - T 1 1) / T 1 0

theorem eigSlope_mulVec (T : Matrix (Fin 2) (Fin 2) ℚ) {ρ : ℝ} (hT10 : T 1 0 ≠ 0)
    (htr : (T 0 0 : ℝ) + T 1 1 = a) (hdet : (T 0 0 : ℝ) * T 1 1 - T 0 1 * T 1 0 = -b)
    (hρ : ρ ^ 2 = a * ρ + b) :
    (ratToReal T).mulVec ![eigSlope T ρ, 1] = ρ • ![eigSlope T ρ, 1] := by
  have h10 : (T 1 0 : ℝ) ≠ 0 := by exact_mod_cast hT10
  ext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, eigSlope, ratToReal]
    field_simp
    have : (T 1 1 : ℝ) = a - T 0 0 := by linarith
    rw [this] at hdet ⊢
    linear_combination (-1 : ℝ) * hρ - hdet
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, eigSlope, ratToReal]
    field_simp
    ring

/-- `mob` and `mobDen` from an eigenvector equation. -/
theorem mob_of_mulVec {A : Matrix (Fin 2) (Fin 2) ℝ} {x y c : ℝ} (hc : c ≠ 0)
    (h : A.mulVec ![x, 1] = c • ![y, 1]) : mob A x = y ∧ mobDen A x = c := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  have hd : mobDen A x = c := by rw [mobDen]; linarith
  refine ⟨?_, hd⟩
  rw [mob, hd, div_eq_iff hc]
  linarith

theorem eigSlope_conjPair (hab : GenAdmissible a b) (T : Matrix (Fin 2) (Fin 2) ℚ)
    (hT10 : T 1 0 ≠ 0) :
    ConjPair (eigSlope T (alpha a b)) (eigSlope T (beta a b)) := by
  have h10 : (T 1 0 : ℝ) ≠ 0 := by exact_mod_cast hT10
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : eigSlope T (alpha a b) = (T 1 0 : ℝ)⁻¹ * alpha a b + (-(T 1 1) / T 1 0 : ℚ) := by
      rw [eigSlope]
      push_cast
      field_simp
      ring
    rw [this]
    have hi := irrational_alpha hab
    have : Irrational ((((T 1 0)⁻¹ : ℚ) : ℝ) * alpha a b) := hi.ratCast_mul (inv_ne_zero hT10)
    push_cast at this
    exact this.add_ratCast _
  · intro h
    rw [eigSlope, eigSlope, div_left_inj' h10] at h
    have := alpha_sub_beta_pos hab
    linarith
  · refine ⟨(a - 2 * T 1 1) / T 1 0, ?_⟩
    rw [eigSlope, eigSlope]
    push_cast
    rw [← alpha_add_beta a b]
    field_simp
    ring
  · refine ⟨(-b - T 1 1 * a + T 1 1 ^ 2) / T 1 0 ^ 2, ?_⟩
    rw [eigSlope, eigSlope]
    push_cast
    rw [← alpha_add_beta a b, ← neg_neg (b : ℝ), ← alpha_mul_beta hab]
    field_simp
    ring

/-- Two conjugate pairs sharing a root, crosswise, are swapped. -/
theorem ConjPair.swap_of_eq {x x' y y' : ℝ} (hx : ConjPair x x') (hy : ConjPair y y')
    (h : x = y') : x' = y := by
  obtain ⟨s₁, hs₁⟩ := hx.sum
  obtain ⟨p₁, hp₁⟩ := hx.prod
  obtain ⟨s₂, hs₂⟩ := hy.sum
  obtain ⟨p₂, hp₂⟩ := hy.prod
  have hx2 : x * x = s₁ * x - p₁ := by rw [← hs₁, ← hp₁]; ring
  have hy2 : x * x = s₂ * x - p₂ := by rw [h, ← hs₂, ← hp₂]; ring
  have hlin : ((s₁ - s₂ : ℚ) : ℝ) * x + ((p₂ - p₁ : ℚ) : ℝ) = 0 := by
    push_cast
    linarith
  obtain ⟨h1, -⟩ := eq_zero_of_rat_lin hx.irrational hlin
  have : (s₁ : ℝ) = s₂ := by exact_mod_cast sub_eq_zero.mp h1
  linarith

end TwoPoint
