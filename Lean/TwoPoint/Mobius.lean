module

public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic

/-!
# Möbius transformations and conjugate pairs

Real `2 × 2` matrices act on `ℝ` by `x ↦ (A₀₀ x + A₀₁) / (A₁₀ x + A₁₁)`. A
*conjugate pair* `(x, x')` consists of an irrational `x` and a different `x'`
with rational sum and product; equivalently `x, x'` are the two roots of an
irreducible rational quadratic, as with a real quadratic irrational and its
Galois conjugate. Rational Möbius transformations preserve conjugate pairs,
and an integral transformation fixing `x` also fixes `x'`.
-/

@[expose] public section
noncomputable section

namespace TwoPoint

/-- Entries of a real matrix are rational. -/
def IsRatMat (A : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∀ i j, ∃ q : ℚ, A i j = q

/-- The real matrix of an integer matrix. -/
def intToReal (A : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℝ :=
  A.map (Int.cast)

theorem IsRatMat.intToReal (A : Matrix (Fin 2) (Fin 2) ℤ) : IsRatMat (intToReal A) :=
  fun i j => ⟨A i j, by simp [TwoPoint.intToReal]⟩

theorem intToReal_mul (A B : Matrix (Fin 2) (Fin 2) ℤ) :
    intToReal (A * B) = intToReal A * intToReal B := by
  ext i j
  simp [intToReal, Matrix.mul_apply, Fin.sum_univ_two]

theorem intToReal_det (A : Matrix (Fin 2) (Fin 2) ℤ) :
    (intToReal A).det = (A.det : ℝ) := by
  simp [intToReal, Matrix.det_fin_two]

/-- The denominator `A₁₀ x + A₁₁`. -/
def mobDen (A : Matrix (Fin 2) (Fin 2) ℝ) (x : ℝ) : ℝ := A 1 0 * x + A 1 1

/-- The Möbius action. -/
def mob (A : Matrix (Fin 2) (Fin 2) ℝ) (x : ℝ) : ℝ := (A 0 0 * x + A 0 1) / mobDen A x

theorem mob_mul (A B : Matrix (Fin 2) (Fin 2) ℝ) (x : ℝ) (hB : mobDen B x ≠ 0) :
    mob (A * B) x = mob A (mob B x) := by
  have hy : B 0 0 * x + B 0 1 = mob B x * mobDen B x := (div_mul_cancel₀ _ hB).symm
  have hy' : B 1 0 * x + B 1 1 = mobDen B x := rfl
  have hnum : (A * B) 0 0 * x + (A * B) 0 1 = mobDen B x * (A 0 0 * mob B x + A 0 1) := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination A 0 0 * hy + A 0 1 * hy'
  have hden : mobDen (A * B) x = mobDen B x * (A 1 0 * mob B x + A 1 1) := by
    have : mobDen (A * B) x = A 1 0 * (B 0 0 * x + B 0 1) + A 1 1 * (B 1 0 * x + B 1 1) := by
      simp only [mobDen, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    rw [this, hy, hy']
    ring
  rw [mob, hnum, hden, mul_div_mul_left _ _ hB]
  rfl

theorem mobDen_mul (A B : Matrix (Fin 2) (Fin 2) ℝ) (x : ℝ) (hB : mobDen B x ≠ 0) :
    mobDen (A * B) x = mobDen A (mob B x) * mobDen B x := by
  have hy : B 0 0 * x + B 0 1 = mob B x * mobDen B x := (div_mul_cancel₀ _ hB).symm
  have : mobDen (A * B) x = A 1 0 * (B 0 0 * x + B 0 1) + A 1 1 * (B 1 0 * x + B 1 1) := by
    simp only [mobDen, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  rw [this, hy]
  simp only [mobDen]
  ring

theorem mob_one (x : ℝ) : mob 1 x = x := by simp [mob, mobDen]

/-- `A (x, 1)ᵀ = mobDen A x • (mob A x, 1)ᵀ`. -/
theorem mulVec_eq_mobDen_smul (A : Matrix (Fin 2) (Fin 2) ℝ) (x : ℝ) (hA : mobDen A x ≠ 0) :
    A.mulVec ![x, 1] = mobDen A x • ![mob A x, 1] := by
  ext i
  fin_cases i
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, mob, Fin.zero_eta,
      Matrix.cons_val_zero, Matrix.cons_val_one, Pi.smul_apply, smul_eq_mul]
    rw [mul_div_cancel₀ _ hA]
    ring
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, mobDen]

/-! ## Irrationality -/

theorem eq_zero_of_rat_lin {x : ℝ} (hx : Irrational x) {c₁ c₀ : ℚ}
    (h : (c₁ : ℝ) * x + c₀ = 0) : c₁ = 0 ∧ c₀ = 0 := by
  by_cases h1 : c₁ = 0
  · subst h1
    simp at h
    exact ⟨rfl, by exact_mod_cast h⟩
  · exfalso
    apply hx
    refine ⟨-c₀ / c₁, ?_⟩
    have : (c₁ : ℝ) ≠ 0 := by exact_mod_cast h1
    push_cast
    field_simp
    linarith

theorem mobDen_ne_zero_of_irrational {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : IsRatMat A)
    (hdet : A.det ≠ 0) {x : ℝ} (hx : Irrational x) : mobDen A x ≠ 0 := by
  intro h
  obtain ⟨c, hc⟩ := hA 1 0
  obtain ⟨d, hd⟩ := hA 1 1
  rw [mobDen, hc, hd] at h
  obtain ⟨rfl, rfl⟩ := eq_zero_of_rat_lin hx h
  apply hdet
  rw [Matrix.det_fin_two, hc, hd]
  simp

theorem irrational_mob {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : IsRatMat A) (hdet : A.det ≠ 0)
    {x : ℝ} (hx : Irrational x) : Irrational (mob A x) := by
  rintro ⟨q, hq⟩
  have hden := mobDen_ne_zero_of_irrational hA hdet hx
  obtain ⟨a₀, ha₀⟩ := hA 0 0
  obtain ⟨a₁, ha₁⟩ := hA 0 1
  obtain ⟨c, hc⟩ := hA 1 0
  obtain ⟨d, hd⟩ := hA 1 1
  have h : ((a₀ - q * c : ℚ) : ℝ) * x + ((a₁ - q * d : ℚ) : ℝ) = 0 := by
    have : (q : ℝ) * mobDen A x = A 0 0 * x + A 0 1 := by
      rw [hq, mob, div_mul_cancel₀ _ hden]
    rw [mobDen, hc, hd, ha₀, ha₁] at this
    push_cast
    linear_combination -this
  obtain ⟨h1, h2⟩ := eq_zero_of_rat_lin hx h
  apply hdet
  rw [Matrix.det_fin_two, ha₀, ha₁, hc, hd]
  have e1 : (a₀ : ℝ) = q * c := by exact_mod_cast sub_eq_zero.mp h1
  have e2 : (a₁ : ℝ) = q * d := by exact_mod_cast sub_eq_zero.mp h2
  rw [e1, e2]
  ring

/-! ## Conjugate pairs -/

/-- `x` is irrational, `x' ≠ x`, and `x + x'`, `x x'` are rational. -/
structure ConjPair (x x' : ℝ) : Prop where
  irrational : Irrational x
  ne : x ≠ x'
  sum : ∃ s : ℚ, x + x' = s
  prod : ∃ p : ℚ, x * x' = p

theorem ConjPair.irrational' {x x' : ℝ} (h : ConjPair x x') : Irrational x' := by
  obtain ⟨s, hs⟩ := h.sum
  have : x' = (s : ℝ) - x := by linarith
  rw [this]
  exact h.irrational.ratCast_sub s

theorem ConjPair.symm {x x' : ℝ} (h : ConjPair x x') : ConjPair x' x where
  irrational := h.irrational'
  ne := h.ne.symm
  sum := by obtain ⟨s, hs⟩ := h.sum; exact ⟨s, by linarith⟩
  prod := by obtain ⟨p, hp⟩ := h.prod; exact ⟨p, by linarith⟩

/-- Rational Möbius transformations preserve conjugate pairs. -/
theorem ConjPair.mob {x x' : ℝ} (h : ConjPair x x') {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : IsRatMat A) (hdet : A.det ≠ 0) : ConjPair (TwoPoint.mob A x) (TwoPoint.mob A x') := by
  have hd := mobDen_ne_zero_of_irrational hA hdet h.irrational
  have hd' := mobDen_ne_zero_of_irrational hA hdet h.irrational'
  obtain ⟨s, hs⟩ := h.sum
  obtain ⟨p, hp⟩ := h.prod
  obtain ⟨a₀, ha₀⟩ := hA 0 0
  obtain ⟨a₁, ha₁⟩ := hA 0 1
  obtain ⟨c, hc⟩ := hA 1 0
  obtain ⟨d, hd₀⟩ := hA 1 1
  -- The common denominator `(c x + d)(c x' + d) = c² p + c d s + d²` is rational and nonzero.
  have hD : mobDen A x * mobDen A x' = ((c ^ 2 * p + c * d * s + d ^ 2 : ℚ) : ℝ) := by
    rw [mobDen, mobDen, hc, hd₀]
    push_cast
    rw [← hs, ← hp]
    ring
  have hD0 : (c ^ 2 * p + c * d * s + d ^ 2 : ℚ) ≠ 0 := by
    intro h0
    rw [h0, Rat.cast_zero] at hD
    exact mul_ne_zero hd hd' hD
  refine ⟨irrational_mob hA hdet h.irrational, ?_, ?_, ?_⟩
  · intro heq
    apply h.ne
    have := congrArg (fun y => y) heq
    simp only [TwoPoint.mob] at this
    rw [div_eq_div_iff hd hd'] at this
    have hdet' : (A 0 0 * A 1 1 - A 0 1 * A 1 0) * (x - x') = 0 := by
      simp only [mobDen] at this
      linear_combination this
    rcases mul_eq_zero.mp hdet' with h0 | h0
    · exact absurd (by rw [Matrix.det_fin_two]; exact h0) hdet
    · linarith
  · refine ⟨(a₀ * c * 2 * p + (a₀ * d + a₁ * c) * s + 2 * a₁ * d) / (c ^ 2 * p + c * d * s + d ^ 2), ?_⟩
    simp only [TwoPoint.mob]
    rw [div_add_div _ _ hd hd', hD]
    push_cast
    congr 1
    rw [mobDen, mobDen, ha₀, ha₁, hc, hd₀]
    rw [← hs, ← hp]
    ring
  · refine ⟨(a₀ ^ 2 * p + a₀ * a₁ * s + a₁ ^ 2) / (c ^ 2 * p + c * d * s + d ^ 2), ?_⟩
    simp only [TwoPoint.mob]
    rw [div_mul_div_comm, hD]
    push_cast
    congr 1
    rw [ha₀, ha₁]
    rw [← hs, ← hp]
    ring

/-- A rational transformation fixing `x` has its first row determined by its
second row `(r, s)`: `A = r [[x + x', -x x'], [1, 0]] + s I`. -/
theorem ConjPair.fix_rows {x x' : ℝ} (h : ConjPair x x') {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : IsRatMat A) (hdet : A.det ≠ 0) (hfix : TwoPoint.mob A x = x) :
    A 0 0 = A 1 0 * (x + x') + A 1 1 ∧ A 0 1 = -(A 1 0 * (x * x')) := by
  have hd := mobDen_ne_zero_of_irrational hA hdet h.irrational
  obtain ⟨s, hs⟩ := h.sum
  obtain ⟨p, hp⟩ := h.prod
  obtain ⟨a₀, ha₀⟩ := hA 0 0
  obtain ⟨a₁, ha₁⟩ := hA 0 1
  obtain ⟨c, hc⟩ := hA 1 0
  obtain ⟨d, hd₀⟩ := hA 1 1
  have hq : A 0 0 * x + A 0 1 = x * mobDen A x := by
    have := hfix
    rw [TwoPoint.mob, div_eq_iff hd] at this
    exact this
  -- `x² = s x - p`.
  have hx2 : x * x = s * x - p := by rw [← hs, ← hp]; ring
  have hlin : ((c * s + d - a₀ : ℚ) : ℝ) * x + ((- (c * p) - a₁ : ℚ) : ℝ) = 0 := by
    push_cast
    rw [mobDen, ha₀, ha₁, hc, hd₀] at hq
    linear_combination -hq - (c : ℝ) * hx2
  obtain ⟨h1, h2⟩ := eq_zero_of_rat_lin h.irrational hlin
  constructor
  · rw [ha₀, hc, hd₀, hs]
    have : (a₀ : ℝ) = c * s + d := by exact_mod_cast (by linarith : a₀ = c * s + d)
    rw [this]
  · rw [ha₁, hc, hp]
    have : (a₁ : ℝ) = -(c * p) := by exact_mod_cast (by linarith : a₁ = -(c * p))
    rw [this]

/-- A rational transformation fixing `x` fixes its conjugate `x'`. -/
theorem ConjPair.fix_conj {x x' : ℝ} (h : ConjPair x x') {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : IsRatMat A) (hdet : A.det ≠ 0) (hfix : TwoPoint.mob A x = x) :
    TwoPoint.mob A x' = x' := by
  obtain ⟨h0, h1⟩ := h.fix_rows hA hdet hfix
  have hd' := mobDen_ne_zero_of_irrational hA hdet h.irrational'
  rw [TwoPoint.mob, div_eq_iff hd', mobDen, h0, h1]
  ring

end TwoPoint
