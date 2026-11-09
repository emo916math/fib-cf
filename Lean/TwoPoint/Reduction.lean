module

public import TwoPoint.Stabilizer

/-!
# Reduction of quadratic irrationals

Every conjugate pair `(x, x')` is `GL₂(ℤ)`-equivalent to a *reduced* pair
`(σ, σ')` with `σ > 1` and `-1 < σ' < 0`.

We run the continued-fraction algorithm on `x`, applying the same Möbius
steps `z ↦ 1/(z - ⌊x_j⌋)` to `x'`. Once `x'_j < ⌊x_j⌋`, two more steps reach
a reduced pair. If that never happened, `x_j` and `x'_j` would share all
partial quotients; their difference stays below `1` but is multiplied by at
least `4` every two steps, which is impossible.
-/

@[expose] public section
noncomputable section

namespace TwoPoint

/-- The inverse of the term matrix `[a]`: `z ↦ 1/(z - a)`. -/
def stepE (a : ℤ) : GL2Z where
  val := !![0, 1; 1, -a]
  inv := !![a, 1; 1, 0]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

theorem mob_stepE (a : ℤ) (z : ℝ) : mob (intToReal (stepE a)) z = (z - a)⁻¹ := by
  simp [mob, mobDen, intToReal, stepE]
  ring_nf

/-- The matrices of the continued-fraction algorithm for `x`. -/
def redSeq (x : ℝ) : ℕ → GL2Z
  | 0 => 1
  | j + 1 => stepE ⌊mob (intToReal (redSeq x j)) x⌋ * redSeq x j

theorem mob_redSeq_succ (x : ℝ) (j : ℕ) {y : ℝ} (hy : Irrational y) :
    mob (intToReal (redSeq x (j + 1))) y =
      (mob (intToReal (redSeq x j)) y - ⌊mob (intToReal (redSeq x j)) x⌋)⁻¹ := by
  rw [redSeq, Units.val_mul, intToReal_mul, mob_mul _ _ _ (mobDen_GL2Z_ne_zero hy _), mob_stepE]

theorem ConjPair.mob_GL2Z {x x' : ℝ} (h : ConjPair x x') (K : GL2Z) :
    ConjPair (TwoPoint.mob (intToReal K) x) (TwoPoint.mob (intToReal K) x') :=
  h.mob (IsRatMat.intToReal K) K.det_real_ne_zero

/-- **Reduction.** -/
theorem exists_reduction {x x' : ℝ} (h : ConjPair x x') :
    ∃ K : GL2Z, 1 < mob (intToReal K) x ∧ -1 < mob (intToReal K) x' ∧
      mob (intToReal K) x' < 0 := by
  set z : ℕ → ℝ := fun j => mob (intToReal (redSeq x j)) x with hz
  set z' : ℕ → ℝ := fun j => mob (intToReal (redSeq x j)) x' with hz'
  have hpair (j : ℕ) : ConjPair (z j) (z' j) := h.mob_GL2Z _
  have hzs (j : ℕ) : z (j + 1) = (z j - ⌊z j⌋)⁻¹ := mob_redSeq_succ x j h.irrational
  have hzs' (j : ℕ) : z' (j + 1) = (z' j - ⌊z j⌋)⁻¹ := mob_redSeq_succ x j h.irrational'
  have hfr (j : ℕ) : 0 < z j - ⌊z j⌋ ∧ z j - ⌊z j⌋ < 1 := by
    have hne : z j - ⌊z j⌋ ≠ 0 := fun h0 =>
      (hpair j).irrational ⟨⌊z j⌋, by push_cast; linarith⟩
    exact ⟨lt_of_le_of_ne (Int.fract_nonneg (z j)) (Ne.symm hne), Int.fract_lt_one (z j)⟩
  have hz1 (j : ℕ) : 1 < z (j + 1) := by
    rw [hzs]
    exact (one_lt_inv₀ (hfr j).1).mpr (hfr j).2
  have hfl1 (j : ℕ) : 1 ≤ ⌊z (j + 1)⌋ := Int.le_floor.mpr (by exact_mod_cast (hz1 j).le)
  have hz'ne (j : ℕ) (c : ℤ) : z' j ≠ c := fun hc => (hpair j).irrational' ⟨c, by rw [hc]; simp⟩
  -- Step 1: some `z'_j` falls below `⌊z_j⌋`.
  obtain ⟨j₀, hj₀⟩ : ∃ j, z' j < ⌊z j⌋ := by
    by_contra H
    simp only [not_exists, not_lt] at H
    have hup (j : ℕ) : z' j < ⌊z j⌋ + 1 := by
      by_contra hge
      rw [not_lt] at hge
      have hd : 1 < z' j - ⌊z j⌋ := by
        rcases lt_or_eq_of_le hge with hlt | heq
        · linarith
        · exact absurd (by rw [← heq]; push_cast; ring) (hz'ne j (⌊z j⌋ + 1))
      have : z' (j + 1) < 1 := by
        rw [hzs']
        exact inv_lt_one_of_one_lt₀ hd
      have := H (j + 1)
      have := hfl1 j
      have : (1 : ℝ) ≤ ⌊z (j + 1)⌋ := by exact_mod_cast hfl1 j
      linarith
    have hfr' (j : ℕ) : 0 < z' j - ⌊z j⌋ ∧ z' j - ⌊z j⌋ < 1 := by
      refine ⟨lt_of_le_of_ne (by linarith [H j]) ?_, by linarith [hup j]⟩
      intro h0
      exact hz'ne j ⌊z j⌋ (by linarith)
    set Δ : ℕ → ℝ := fun j => |z j - z' j|
    have hΔ1 (j : ℕ) : Δ j < 1 := by
      simp only [Δ]
      rw [abs_lt]
      constructor <;> linarith [hfr j, hfr' j]
    have hΔs (j : ℕ) : Δ (j + 1) = Δ j * (z (j + 1) * z' (j + 1)) := by
      simp only [Δ]
      rw [hzs, hzs']
      have h1 := (hfr j).1
      have h2 := (hfr' j).1
      rw [show (z j - ⌊z j⌋)⁻¹ - (z' j - ⌊z j⌋)⁻¹ =
          (z j - z' j) * -((z j - ⌊z j⌋)⁻¹ * (z' j - ⌊z j⌋)⁻¹) by field_simp; ring]
      rw [abs_mul, abs_neg, abs_of_pos (mul_pos (inv_pos.mpr h1) (inv_pos.mpr h2))]
    -- Two steps multiply `Δ` by at least `4`.
    have hpair2 (j : ℕ) (w : ℕ → ℝ) (hw : ∀ j, w (j + 1) = (w j - ⌊z j⌋)⁻¹)
        (hwf : ∀ j, 0 < w j - ⌊z j⌋ ∧ w j - ⌊z j⌋ < 1) :
        2 ≤ w (j + 1) * w (j + 2) := by
      have hf := hwf (j + 1)
      have hw2 : w (j + 2) = (w (j + 1) - ⌊z (j + 1)⌋)⁻¹ := hw (j + 1)
      have hge : 1 + (w (j + 1) - ⌊z (j + 1)⌋) ≤ w (j + 1) := by
        have : (1 : ℝ) ≤ ⌊z (j + 1)⌋ := by exact_mod_cast hfl1 j
        linarith
      rw [hw2]
      set f := w (j + 1) - ⌊z (j + 1)⌋
      have hfinv : 1 ≤ f⁻¹ := (one_le_inv₀ hf.1).mpr hf.2.le
      calc 2 ≤ (1 + f) * f⁻¹ := by
            rw [add_mul, one_mul, mul_inv_cancel₀ hf.1.ne']
            linarith
        _ ≤ w (j + 1) * f⁻¹ := by gcongr
    have h4 (j : ℕ) : 4 * Δ j ≤ Δ (j + 2) := by
      rw [hΔs (j + 1), hΔs j]
      have a1 := hpair2 j z hzs hfr
      have a2 := hpair2 j z' hzs' hfr'
      have hΔ0 : 0 ≤ Δ j := abs_nonneg _
      calc 4 * Δ j = Δ j * (2 * 2) := by ring
        _ ≤ Δ j * ((z (j + 1) * z (j + 2)) * (z' (j + 1) * z' (j + 2))) := by
            gcongr
        _ = Δ j * (z (j + 1) * z' (j + 1)) * (z (j + 1 + 1) * z' (j + 1 + 1)) := by ring
    have hgrow (t : ℕ) : 4 ^ t * Δ 0 ≤ Δ (2 * t) := by
      induction t with
      | zero => simp
      | succ t ih =>
        rw [show 2 * (t + 1) = 2 * t + 2 by ring, pow_succ]
        nlinarith [h4 (2 * t)]
    have hΔ0 : 0 < Δ 0 := abs_pos.mpr (sub_ne_zero.mpr (hpair 0).ne)
    obtain ⟨t, ht⟩ := pow_unbounded_of_one_lt (1 / Δ 0) (by norm_num : (1 : ℝ) < 4)
    have := hgrow t
    have := hΔ1 (2 * t)
    rw [div_lt_iff₀ hΔ0] at ht
    linarith
  -- Step 2: two more steps reach a reduced pair.
  have hneg : z' (j₀ + 1) < 0 := by
    rw [hzs']
    exact inv_lt_zero.mpr (by linarith)
  have hd : z' (j₀ + 1) - ⌊z (j₀ + 1)⌋ < -1 := by
    have : (1 : ℝ) ≤ ⌊z (j₀ + 1)⌋ := by exact_mod_cast hfl1 j₀
    linarith
  refine ⟨redSeq x (j₀ + 2), hz1 (j₀ + 1), ?_, ?_⟩
  · show -1 < z' (j₀ + 1 + 1)
    rw [hzs']
    rw [lt_inv_of_neg (by norm_num) (by linarith)]
    linarith
  · show z' (j₀ + 1 + 1) < 0
    rw [hzs']
    exact inv_lt_zero.mpr (by linarith)

end TwoPoint
