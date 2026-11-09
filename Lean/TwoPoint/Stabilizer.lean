module

public import TwoPoint.Mobius
public import TwoPoint.WordCriterion
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Stabilizers of quadratic irrationals in `GL₂(ℤ)`

For a conjugate pair `(σ, σ')`, every element of `GL₂(ℤ)` fixing `σ` has the
form `r [[σ + σ', -σσ'], [1, 0]] + s I`, with eigenvalue `λ = rσ + s` at `σ`.

* If `σ` is reduced (`σ > 1`, `-1 < σ' < 0`), every stabilizer element with
  `λ > 1` is a continued-fraction word (via Mercat's criterion).
* The stabilizer is `±` an infinite cyclic group as soon as it contains an
  element with `λ > 1`: the eigenvalue is a multiplicative injection with
  discrete image.
-/

@[expose] public section
noncomputable section

namespace TwoPoint

/-- `GL₂(ℤ)`. -/
abbrev GL2Z := (Matrix (Fin 2) (Fin 2) ℤ)ˣ

theorem GL2Z.det_eq (M : GL2Z) : (M : Matrix (Fin 2) (Fin 2) ℤ).det = 1 ∨
    (M : Matrix (Fin 2) (Fin 2) ℤ).det = -1 :=
  Int.isUnit_iff.mp (M.isUnit.map Matrix.detMonoidHom)

theorem GL2Z.det_real_ne_zero (M : GL2Z) : (intToReal M).det ≠ 0 := by
  rw [intToReal_det]
  rcases M.det_eq with h | h <;> simp [h]

theorem intToReal_one : intToReal 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [intToReal]

theorem intToReal_neg (A : Matrix (Fin 2) (Fin 2) ℤ) : intToReal (-A) = -intToReal A := by
  ext i j
  simp [intToReal]

theorem mob_neg (A : Matrix (Fin 2) (Fin 2) ℝ) (x : ℝ) : mob (-A) x = mob A x := by
  simp only [mob, mobDen, Matrix.neg_apply]
  rw [show -A 0 0 * x + -A 0 1 = -(A 0 0 * x + A 0 1) by ring,
    show -A 1 0 * x + -A 1 1 = -(A 1 0 * x + A 1 1) by ring, neg_div_neg_eq]

/-- The eigenvalue at `σ`. -/
def lam (σ : ℝ) (M : GL2Z) : ℝ := mobDen (intToReal M) σ

/-- Integer `z` with `z > -1` is nonnegative. -/
theorem int_nonneg_of_gt_neg_one {z : ℤ} (h : (-1 : ℝ) < z) : 0 ≤ z := by
  have : (-1 : ℤ) < z := by exact_mod_cast h
  omega

/-! ## Reduced stabilizers are words -/

/-- For reduced `σ`, a stabilizer element with eigenvalue `> 1` is a word. -/
theorem exists_word_of_reduced_stabilizer {σ σ' : ℝ} (h : ConjPair σ σ') (hσ : 1 < σ)
    (hσ'₁ : -1 < σ') (hσ'₂ : σ' < 0) (M : GL2Z)
    (hfix : mob (intToReal M) σ = σ) (hlam1 : 1 < lam σ M) :
    ∃ w : CFWord, PositiveWord w ∧ w ≠ [] ∧ w.matrix = M := by
  have hA := IsRatMat.intToReal M
  have hdetA := M.det_real_ne_zero
  obtain ⟨h0, h1⟩ := h.fix_rows hA hdetA hfix
  set p := (M : Matrix (Fin 2) (Fin 2) ℤ) 0 0
  set q := (M : Matrix (Fin 2) (Fin 2) ℤ) 0 1
  set r := (M : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  set s := (M : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  have hAp : intToReal M 0 0 = p := by simp [intToReal, p]
  have hAq : intToReal M 0 1 = q := by simp [intToReal, q]
  have hAr : intToReal M 1 0 = r := by simp [intToReal, r]
  have hAs : intToReal M 1 1 = s := by simp [intToReal, s]
  rw [hAp, hAr, hAs] at h0
  rw [hAq, hAr] at h1
  set μ := (r : ℝ) * σ' + s with hμ
  have hlam : lam σ M = r * σ + s := by simp only [lam, mobDen, hAr, hAs]
  rw [hlam] at hlam1
  -- `λ μ = det M = ±1`.
  have hdet : (r * σ + s) * μ = ((M : Matrix (Fin 2) (Fin 2) ℤ).det : ℝ) := by
    rw [Matrix.det_fin_two]
    push_cast
    rw [h0, h1, hμ]
    ring
  have hμabs : |μ| < 1 := by
    have habs : |(r * σ + s : ℝ)| * |μ| = 1 := by
      rw [← abs_mul, hdet]
      rcases M.det_eq with hd | hd <;> simp [hd]
    rw [abs_of_pos (by linarith)] at habs
    nlinarith [abs_nonneg μ]
  obtain ⟨hμ1, hμ2⟩ := abs_lt.mp hμabs
  have hr : (0 : ℝ) < r := by
    have : (r : ℝ) * (σ - σ') = (r * σ + s) - μ := by rw [hμ]; ring
    have hpos : (0 : ℝ) < (r * σ + s) - μ := by linarith
    rw [← this] at hpos
    exact pos_of_mul_pos_left hpos (by linarith)
  have hs : 0 ≤ s := int_nonneg_of_gt_neg_one (by nlinarith)
  have hsr : s ≤ r := by
    have := int_nonneg_of_gt_neg_one (z := r - s) (by push_cast; nlinarith)
    omega
  have hsq : s ≤ q := by
    have := int_nonneg_of_gt_neg_one (z := q - s) (by
      push_cast
      rw [h1]
      nlinarith [mul_pos (mul_pos hr (neg_pos.mpr hσ'₂)) (sub_pos.mpr hσ)])
    omega
  have hqp : q ≤ p := by
    have := int_nonneg_of_gt_neg_one (z := p - q) (by
      push_cast
      rw [h0, h1]
      nlinarith [mul_pos (mul_pos hr (by linarith : (0 : ℝ) < σ)) (by linarith : (0 : ℝ) < 1 + σ')])
    omega
  have hrp : r ≤ p := by
    have := int_nonneg_of_gt_neg_one (z := p - r) (by push_cast; rw [h0]; nlinarith)
    omega
  exact exists_word_of_matrix M M.det_eq hs hsr hsq hqp hrp

/-! ## The stabilizer subgroup and its eigenvalue -/

theorem mobDen_GL2Z_ne_zero {σ : ℝ} (hσ : Irrational σ) (M : GL2Z) :
    mobDen (intToReal M) σ ≠ 0 :=
  mobDen_ne_zero_of_irrational (IsRatMat.intToReal _) M.det_real_ne_zero hσ

/-- The stabilizer of an irrational `σ` in `GL₂(ℤ)`. -/
def stab (σ : ℝ) (hσ : Irrational σ) : Subgroup GL2Z where
  carrier := {M | mob (intToReal M) σ = σ}
  one_mem' := by simp [intToReal_one, mob_one]
  mul_mem' := by
    intro M N hM hN
    simp only [Set.mem_ofPred_eq, Units.val_mul, intToReal_mul] at *
    rw [mob_mul _ _ _ (mobDen_GL2Z_ne_zero hσ N), hN, hM]
  inv_mem' := by
    intro M hM
    simp only [Set.mem_ofPred_eq] at *
    have h1 : intToReal (↑M⁻¹ : Matrix (Fin 2) (Fin 2) ℤ) * intToReal ↑M = 1 := by
      rw [← intToReal_mul, Units.inv_mul, intToReal_one]
    have := mob_mul (intToReal ↑M⁻¹) (intToReal ↑M) σ (mobDen_GL2Z_ne_zero hσ M)
    rw [h1, mob_one, hM] at this
    exact this.symm

variable {σ : ℝ} {hσ : Irrational σ}

theorem mem_stab {M : GL2Z} : M ∈ stab σ hσ ↔ mob (intToReal M) σ = σ := Iff.rfl

theorem lam_one (σ : ℝ) : lam σ 1 = 1 := by simp [lam, mobDen, intToReal_one]

theorem lam_mul (M : GL2Z) {N : GL2Z} (hN : N ∈ stab σ hσ) :
    lam σ (M * N) = lam σ M * lam σ N := by
  simp only [lam, Units.val_mul, intToReal_mul]
  rw [mobDen_mul _ _ _ (mobDen_GL2Z_ne_zero hσ N), mem_stab.mp hN]

theorem lam_ne_zero (hσ : Irrational σ) (M : GL2Z) : lam σ M ≠ 0 := mobDen_GL2Z_ne_zero hσ M

theorem lam_pow {M : GL2Z} (hM : M ∈ stab σ hσ) (n : ℕ) : lam σ (M ^ n) = lam σ M ^ n := by
  induction n with
  | zero => simp [lam_one]
  | succ n ih => rw [pow_succ, lam_mul _ hM, ih, pow_succ]

theorem lam_inv {M : GL2Z} (hM : M ∈ stab σ hσ) : lam σ M⁻¹ = (lam σ M)⁻¹ := by
  have h := lam_mul (hσ := hσ) M⁻¹ hM
  rw [inv_mul_cancel, lam_one] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem lam_zpow {M : GL2Z} (hM : M ∈ stab σ hσ) (e : ℤ) : lam σ (M ^ e) = lam σ M ^ e := by
  cases e with
  | ofNat n => simp only [Int.ofNat_eq_natCast, zpow_natCast, lam_pow hM]
  | negSucc n =>
    rw [zpow_negSucc, zpow_negSucc, lam_inv ((stab σ hσ).pow_mem hM _), lam_pow hM]

theorem lam_neg (M : GL2Z) : lam σ (-M) = -lam σ M := by
  simp only [lam, Units.val_neg, intToReal_neg, mobDen, Matrix.neg_apply]
  ring

theorem neg_mem_stab {M : GL2Z} (hM : M ∈ stab σ hσ) : -M ∈ stab σ hσ := by
  rw [mem_stab, Units.val_neg, intToReal_neg, mob_neg]
  exact hM

/-- Entries of a stabilizer element, in terms of its second row. -/
theorem stab_rows {σ' : ℝ} (h : ConjPair σ σ') {M : GL2Z} (hM : M ∈ stab σ h.irrational) :
    (((M : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ℝ) =
        ((M : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) * (σ + σ') + ((M : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) ∧
      (((M : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ℝ) =
        -(((M : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) * (σ * σ')) ∧
      lam σ M = ((M : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) * σ + ((M : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) ∧
      lam σ M * (((M : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) * σ' + ((M : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ)) =
        ((M : Matrix (Fin 2) (Fin 2) ℤ).det : ℝ) := by
  obtain ⟨h0, h1⟩ := h.fix_rows (IsRatMat.intToReal M) M.det_real_ne_zero hM
  simp only [intToReal, Matrix.map_apply] at h0 h1
  refine ⟨h0, h1, by simp [lam, mobDen, intToReal], ?_⟩
  simp only [lam, mobDen, intToReal, Matrix.map_apply]
  rw [Matrix.det_fin_two]
  push_cast
  rw [h0, h1]
  ring

theorem eq_one_of_lam_eq_one {σ' : ℝ} (h : ConjPair σ σ') {M : GL2Z}
    (hM : M ∈ stab σ h.irrational) (hl : lam σ M = 1) : M = 1 := by
  obtain ⟨h0, h1, hlm, hdet⟩ := stab_rows h hM
  set r := (M : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  set s := (M : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  rw [hl, one_mul] at hdet
  obtain ⟨S, hS⟩ := h.sum
  have hr : r = 0 := by
    rcases M.det_eq with hd | hd <;> rw [hd] at hdet <;> push_cast at hdet
    · have : (r : ℝ) * (σ - σ') = 0 := by linarith
      rcases mul_eq_zero.mp this with h' | h'
      · exact_mod_cast h'
      · exact absurd (sub_eq_zero.mp h') h.ne
    · exfalso
      have hlin : ((2 * r : ℤ) : ℚ) * σ + ((-(2 + r * S)) : ℚ) = 0 := by
        push_cast
        have : σ' = S - σ := by linarith
        rw [this] at hdet
        linarith
      have := eq_zero_of_rat_lin h.irrational (c₁ := ((2 * r : ℤ) : ℚ)) (c₀ := -(2 + r * S))
        (by exact_mod_cast hlin)
      obtain ⟨h2, h3⟩ := this
      have hr0 : r = 0 := by exact_mod_cast (by simpa using h2 : (r : ℚ) = 0)
      rw [hr0] at h3
      norm_num at h3
  have hs : s = 1 := by
    rw [hr] at hlm
    rw [hl] at hlm
    push_cast at hlm
    exact_mod_cast (by linarith : (s : ℝ) = 1)
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j
  · have : ((M : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℝ) = 1 := by rw [h0, hr, hs]; simp
    simpa using (by exact_mod_cast this : (M : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = 1)
  · have : ((M : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℝ) = 0 := by rw [h1, hr]; simp
    simpa using (by exact_mod_cast this : (M : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = 0)
  · simpa using hr
  · simpa using hs

/-! ## Cyclicity -/

/-- Stabilizer elements with eigenvalue in a bounded window are finite in number. -/
theorem stab_finite_window {σ' : ℝ} (h : ConjPair σ σ') (K : ℝ) :
    {M : GL2Z | M ∈ stab σ h.irrational ∧ 1 < lam σ M ∧ lam σ M ≤ K}.Finite := by
  let f : GL2Z → ℤ × ℤ := fun M =>
    ((M : Matrix (Fin 2) (Fin 2) ℤ) 1 0, (M : Matrix (Fin 2) (Fin 2) ℤ) 1 1)
  have hδ : 0 < |σ - σ'| := abs_pos.mpr (sub_ne_zero.mpr h.ne)
  set R : ℤ := ⌈(K + 1) / |σ - σ'|⌉ with hRdef
  set T : ℤ := ⌈K + R * |σ|⌉ with hTdef
  apply Set.Finite.of_finite_image (f := f)
  · apply ((Set.finite_Icc (-R) R).prod (Set.finite_Icc (-T) T)).subset
    rintro _ ⟨M, ⟨hM, h1, hK⟩, rfl⟩
    obtain ⟨-, -, hlm, hdet⟩ := stab_rows h hM
    set r := (M : Matrix (Fin 2) (Fin 2) ℤ) 1 0
    set s := (M : Matrix (Fin 2) (Fin 2) ℤ) 1 1
    set μ := (r : ℝ) * σ' + s
    have hμ : |μ| < 1 := by
      have habs : |lam σ M| * |μ| = 1 := by
        rw [← abs_mul, hdet]
        rcases M.det_eq with hd | hd <;> simp [hd]
      rw [abs_of_pos (by linarith)] at habs
      nlinarith [abs_nonneg μ]
    have hrσ : (r : ℝ) * (σ - σ') = lam σ M - μ := by rw [hlm]; ring
    have hrabs : |(r : ℝ)| ≤ R := by
      have h2 : |(r : ℝ)| * |σ - σ'| ≤ K + 1 := by
        rw [← abs_mul, hrσ]
        calc |lam σ M - μ| ≤ |lam σ M| + |μ| := abs_sub _ _
          _ ≤ K + 1 := by rw [abs_of_pos (by linarith)]; linarith
      calc |(r : ℝ)| ≤ (K + 1) / |σ - σ'| := by rw [le_div_iff₀ hδ]; exact h2
        _ ≤ R := Int.le_ceil _
    have hsabs : |(s : ℝ)| ≤ T := by
      have hs : (s : ℝ) = lam σ M - r * σ := by rw [hlm]; ring
      calc |(s : ℝ)| ≤ |lam σ M| + |(r : ℝ)| * |σ| := by
            rw [hs, ← abs_mul]; exact abs_sub _ _
        _ ≤ K + R * |σ| := by
            rw [abs_of_pos (by linarith)]
            gcongr
        _ ≤ T := Int.le_ceil _
    have hr' : |r| ≤ R := by exact_mod_cast hrabs
    have hs' : |s| ≤ T := by exact_mod_cast hsabs
    exact ⟨Set.mem_Icc.mpr (abs_le.mp hr'), Set.mem_Icc.mpr (abs_le.mp hs')⟩
  · intro M hM N hN hf
    simp only [f, Prod.mk.injEq] at hf
    obtain ⟨hr, hs⟩ := hf
    obtain ⟨hM0, hM1, -, -⟩ := stab_rows h hM.1
    obtain ⟨hN0, hN1, -, -⟩ := stab_rows h hN.1
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j
    · have : (((M : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ℝ) = ((N : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) := by
        rw [hM0, hN0, hr, hs]
      exact_mod_cast this
    · have : (((M : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ℝ) = ((N : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) := by
        rw [hM1, hN1, hr]
      exact_mod_cast this
    · exact hr
    · exact hs

/-- A stabilizer element of minimal eigenvalue `> 1`. -/
theorem exists_min_lam {σ' : ℝ} (h : ConjPair σ σ') {Z : GL2Z} (hZ : Z ∈ stab σ h.irrational)
    (hZl : 1 < lam σ Z) :
    ∃ P ∈ stab σ h.irrational, 1 < lam σ P ∧
      ∀ M ∈ stab σ h.irrational, 1 < lam σ M → lam σ P ≤ lam σ M := by
  obtain ⟨P, ⟨hP, hP1, hPK⟩, hmin⟩ := Set.exists_min_image _ (lam σ)
    (stab_finite_window h (lam σ Z)) ⟨Z, hZ, hZl, le_rfl⟩
  refine ⟨P, hP, hP1, fun M hM hM1 => ?_⟩
  by_cases hMK : lam σ M ≤ lam σ Z
  · exact hmin M ⟨hM, hM1, hMK⟩
  · linarith

/-- **The stabilizer is `±` cyclic.** -/
theorem stab_cyclic {σ' : ℝ} (h : ConjPair σ σ') {Z : GL2Z} (hZ : Z ∈ stab σ h.irrational)
    (hZl : 1 < lam σ Z) :
    ∃ P ∈ stab σ h.irrational, 1 < lam σ P ∧
      ∀ M ∈ stab σ h.irrational, ∃ e : ℤ, M = P ^ e ∨ M = -(P ^ e) := by
  obtain ⟨P, hP, hP1, hmin⟩ := exists_min_lam h hZ hZl
  refine ⟨P, hP, hP1, fun M hM => ?_⟩
  -- Normalize the sign of the eigenvalue.
  obtain ⟨M₁, hM₁, hM₁pos, hsign⟩ : ∃ M₁ ∈ stab σ h.irrational, 0 < lam σ M₁ ∧
      (M = M₁ ∨ M = -M₁) := by
    rcases lt_or_gt_of_ne (lam_ne_zero h.irrational M) with hneg | hpos
    · exact ⟨-M, neg_mem_stab hM, by rw [lam_neg]; linarith, Or.inr (neg_neg M).symm⟩
    · exact ⟨M, hM, hpos, Or.inl rfl⟩
  set l₀ := lam σ P
  set l₁ := lam σ M₁
  have hl₀ : 0 < Real.log l₀ := Real.log_pos hP1
  set e : ℤ := ⌊Real.log l₁ / Real.log l₀⌋
  have he₁ : (e : ℝ) * Real.log l₀ ≤ Real.log l₁ := by
    have := Int.floor_le (Real.log l₁ / Real.log l₀)
    rwa [le_div_iff₀ hl₀] at this
  have he₂ : Real.log l₁ < ((e : ℝ) + 1) * Real.log l₀ := by
    have := Int.lt_floor_add_one (Real.log l₁ / Real.log l₀)
    rwa [div_lt_iff₀ hl₀] at this
  have hl₀pos : 0 < l₀ := by linarith
  have hpowe : l₀ ^ e ≤ l₁ := by
    rw [← Real.log_le_log_iff (zpow_pos hl₀pos _) hM₁pos, Real.log_zpow]
    exact he₁
  have hpowe1 : l₁ < l₀ ^ (e + 1) := by
    rw [← Real.log_lt_log_iff hM₁pos (zpow_pos hl₀pos _), Real.log_zpow]
    push_cast
    exact he₂
  set N := M₁ * P ^ (-e)
  have hN : N ∈ stab σ h.irrational := (stab σ h.irrational).mul_mem hM₁ ((stab σ h.irrational).zpow_mem hP _)
  have hlN : lam σ N = l₁ / l₀ ^ e := by
    rw [lam_mul _ ((stab σ h.irrational).zpow_mem hP _), lam_zpow hP, zpow_neg, div_eq_mul_inv]
  have hlN1 : 1 ≤ lam σ N := by
    rw [hlN, le_div_iff₀ (zpow_pos hl₀pos _), one_mul]
    exact hpowe
  have hlN2 : lam σ N < l₀ := by
    rw [hlN, div_lt_iff₀ (zpow_pos hl₀pos _), mul_comm, ← zpow_add_one₀ hl₀pos.ne']
    exact hpowe1
  have hlNeq : lam σ N = 1 := by
    by_contra hne
    have := hmin N hN (lt_of_le_of_ne hlN1 (Ne.symm hne))
    linarith
  have hN1 := eq_one_of_lam_eq_one h hN hlNeq
  have hM₁e : M₁ = P ^ e := by
    have := mul_eq_one_iff_eq_inv.mp hN1
    rw [this, zpow_neg, inv_inv]
  refine ⟨e, ?_⟩
  rcases hsign with rfl | rfl
  · exact Or.inl hM₁e
  · exact Or.inr (by rw [hM₁e])

end TwoPoint
