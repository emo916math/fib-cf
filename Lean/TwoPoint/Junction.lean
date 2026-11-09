module

public import TwoPoint.Reduction
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Instances.Matrix

/-!
# The junction lemma

Section 3.4: if `P`, `Q` are hyperbolic stabilizer elements with attracting
fixed points `σ > 1`, `τ` and repelling fixed points `σ'`, `τ' ∈ (-1, 0)`, and
`J τ ≠ σ'`, then `±P^m J Q^m` is a continued-fraction word for some `m`.

Every stabilizer element decomposes as `M = λ E + λ' E'`, where `E`, `E'` are
the rank-one spectral projections. Normalizing by `λ^m μ^m`, the product tends
to the rank-one matrix `c (σ, 1)ᵀ (1, -τ')`, whose entries are positive and
strictly decreasing along rows and columns. Mercat's criterion then applies.
-/

@[expose] public section
noncomputable section

namespace TwoPoint

open Filter Topology

/-- The rank-one matrix `(x, 1)ᵀ (1, -y)`. -/
def rk1 (x y : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![x, -(x * y); 1, -y]

/-- The spectral projection onto the `x`-eigenline along the `y`-eigenline. -/
def specProj (x y : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := (x - y)⁻¹ • rk1 x y

/-! ## Words from rank-one limits -/

theorem tendsto_entry {f : ℕ → Matrix (Fin 2) (Fin 2) ℝ} {L : Matrix (Fin 2) (Fin 2) ℝ}
    (h : Tendsto f atTop (𝓝 L)) (i j : Fin 2) :
    Tendsto (fun m => f m i j) atTop (𝓝 (L i j)) := by
  have hc : Continuous fun A : Matrix (Fin 2) (Fin 2) ℝ => A i j :=
    (continuous_apply j).comp (continuous_apply i)
  exact (hc.tendsto L).comp h

private theorem exists_word_of_tendsto_pos (N : ℕ → GL2Z) (κ : ℕ → ℝ) (hκ : ∀ m, 0 < κ m)
    {c x y : ℝ} (hc : 0 < c) (hx : 1 < x) (hy1 : -1 < y) (hy2 : y < 0)
    (hT : Tendsto (fun m => (κ m)⁻¹ • intToReal (N m)) atTop (𝓝 (c • rk1 x y))) :
    ∃ m, ∃ w : CFWord, PositiveWord w ∧ w ≠ [] ∧ w.matrix = N m := by
  have he (i j : Fin 2) := tendsto_entry hT i j
  simp only [Matrix.smul_apply, smul_eq_mul, intToReal, Matrix.map_apply] at he
  simp only [rk1] at he
  -- Positive limits of differences give eventual strict inequalities.
  have ev (i j k l : Fin 2) (hlim : 0 < c * !![x, -(x * y); 1, -y] i j -
      c * !![x, -(x * y); 1, -y] k l) :
      ∀ᶠ m in atTop, ((N m : Matrix (Fin 2) (Fin 2) ℤ) k l) < (N m : Matrix (Fin 2) (Fin 2) ℤ) i j := by
    have := (tendsto_order.1 ((he i j).sub (he k l))).1 0 hlim
    filter_upwards [this] with m hm
    rw [← mul_sub] at hm
    have := (mul_pos_iff_of_pos_left (inv_pos.mpr (hκ m))).mp hm
    exact_mod_cast sub_pos.mp this
  have ev0 : ∀ᶠ m in atTop, 0 < (N m : Matrix (Fin 2) (Fin 2) ℤ) 1 1 := by
    have := (tendsto_order.1 (he 1 1)).1 0 (by simp; nlinarith)
    filter_upwards [this] with m hm
    have := (mul_pos_iff_of_pos_left (inv_pos.mpr (hκ m))).mp hm
    exact_mod_cast this
  have e1 := ev 1 0 1 1 (by simp; nlinarith)
  have e2 := ev 0 1 1 1 (by
    simp
    nlinarith [mul_pos (mul_pos hc (neg_pos.mpr hy2)) (sub_pos.mpr hx)])
  have e3 := ev 0 0 0 1 (by
    simp
    nlinarith [mul_pos (mul_pos hc (by linarith : (0 : ℝ) < x)) (by linarith : (0 : ℝ) < 1 + y)])
  have e4 := ev 0 0 1 0 (by simp; nlinarith)
  obtain ⟨m, h0, h1, h2, h3, h4⟩ := (ev0.and (e1.and (e2.and (e3.and e4)))).exists
  exact ⟨m, exists_word_of_matrix _ (N m).det_eq h0.le h1.le h2.le h3.le h4.le⟩

/-- If normalized integral matrices tend to a nonzero multiple of
`(x, 1)ᵀ (1, -y)` with `x > 1` and `-1 < y < 0`, then eventually `±N` is a word. -/
theorem exists_word_of_tendsto (N : ℕ → GL2Z) (κ : ℕ → ℝ) (hκ : ∀ m, 0 < κ m)
    {c x y : ℝ} (hc : c ≠ 0) (hx : 1 < x) (hy1 : -1 < y) (hy2 : y < 0)
    (hT : Tendsto (fun m => (κ m)⁻¹ • intToReal (N m)) atTop (𝓝 (c • rk1 x y))) :
    ∃ m, ∃ w : CFWord, PositiveWord w ∧ w ≠ [] ∧
      (w.matrix = N m ∨ w.matrix = -(N m : Matrix (Fin 2) (Fin 2) ℤ)) := by
  rcases lt_or_gt_of_ne hc with hneg | hpos
  · have hT' : Tendsto (fun m => (κ m)⁻¹ • intToReal ((-N m : GL2Z))) atTop
        (𝓝 ((-c) • rk1 x y)) := by
      have := hT.neg
      simp only [neg_smul] at this ⊢
      refine this.congr fun m => ?_
      rw [Units.val_neg, intToReal_neg, smul_neg]
    obtain ⟨m, w, hw, hw0, hwm⟩ :=
      exists_word_of_tendsto_pos (fun m => -N m) κ hκ (by linarith) hx hy1 hy2 hT'
    exact ⟨m, w, hw, hw0, Or.inr (by rw [hwm, Units.val_neg])⟩
  · obtain ⟨m, w, hw, hw0, hwm⟩ := exists_word_of_tendsto_pos N κ hκ hpos hx hy1 hy2 hT
    exact ⟨m, w, hw, hw0, Or.inl hwm⟩

/-! ## Spectral decomposition -/

theorem stab_mem_conj {σ σ' : ℝ} (h : ConjPair σ σ') {M : GL2Z}
    (hM : M ∈ stab σ h.irrational) : M ∈ stab σ' h.irrational' :=
  h.fix_conj (IsRatMat.intToReal M) M.det_real_ne_zero hM

/-- `M = λ E + λ' E'`. -/
theorem stab_spectral {σ σ' : ℝ} (h : ConjPair σ σ') {M : GL2Z}
    (hM : M ∈ stab σ h.irrational) :
    intToReal M = lam σ M • specProj σ σ' + lam σ' M • specProj σ' σ := by
  obtain ⟨h0, h1, hl, -⟩ := stab_rows h hM
  have hl' : lam σ' M = ((M : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) * σ' +
      ((M : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) := by simp [lam, mobDen, intToReal]
  have hne : σ - σ' ≠ 0 := sub_ne_zero.mpr h.ne
  have hne' : σ' - σ ≠ 0 := sub_ne_zero.mpr h.ne.symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [specProj, rk1, intToReal, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] <;>
    rw [hl, hl'] <;> field_simp
  · rw [h0]; ring
  · rw [h1]; ring
  · ring
  · ring

theorem abs_lam_conj_lt_one {σ σ' : ℝ} (h : ConjPair σ σ') {M : GL2Z}
    (hM : M ∈ stab σ h.irrational) (hl : 1 < lam σ M) : |lam σ' M| < 1 := by
  obtain ⟨-, -, -, hdet⟩ := stab_rows h hM
  have hl' : lam σ' M = ((M : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) * σ' +
      ((M : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) := by simp [lam, mobDen, intToReal]
  rw [← hl'] at hdet
  have habs : |lam σ M| * |lam σ' M| = 1 := by
    rw [← abs_mul, hdet]
    rcases M.det_eq with hd | hd <;> simp [hd]
  rw [abs_of_pos (by linarith)] at habs
  nlinarith [abs_nonneg (lam σ' M)]

/-- Normalized powers converge to the spectral projection. -/
theorem tendsto_normalized_pow {σ σ' : ℝ} (h : ConjPair σ σ') {M : GL2Z}
    (hM : M ∈ stab σ h.irrational) (hl : 1 < lam σ M) :
    Tendsto (fun m : ℕ => (lam σ M ^ m)⁻¹ • intToReal ((M ^ m : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ))
      atTop (𝓝 (specProj σ σ')) := by
  set ρ := lam σ' M / lam σ M
  have hl0 : 0 < lam σ M := by linarith
  have hρ : |ρ| < 1 := by
    rw [abs_div, abs_of_pos hl0, div_lt_one hl0]
    linarith [abs_lam_conj_lt_one h hM hl]
  have hlim : Tendsto (fun m : ℕ => specProj σ σ' + ρ ^ m • specProj σ' σ) atTop
      (𝓝 (specProj σ σ' + (0 : ℝ) • specProj σ' σ)) :=
    tendsto_const_nhds.add ((tendsto_pow_atTop_nhds_zero_of_abs_lt_one hρ).smul_const _)
  rw [zero_smul, add_zero] at hlim
  refine hlim.congr fun m => ?_
  have hMm := (stab σ h.irrational).pow_mem hM m
  rw [stab_spectral h hMm, lam_pow hM, lam_pow (stab_mem_conj h hM), smul_add, smul_smul,
    smul_smul, inv_mul_cancel₀ (pow_ne_zero _ (by linarith)), one_smul, div_pow,
    div_eq_mul_inv, mul_comm]

/-! ## Rank-one products -/

theorem rk1_mul_rk1 (x y : ℝ) (J : Matrix (Fin 2) (Fin 2) ℝ) (x' y' : ℝ) :
    rk1 x y * J * rk1 x' y' =
      ((J 0 0 * x' + J 0 1) - y * (J 1 0 * x' + J 1 1)) • rk1 x y' := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rk1, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] <;> ring

theorem mul_rk1 (J : Matrix (Fin 2) (Fin 2) ℝ) (x y : ℝ) (hd : mobDen J x ≠ 0) :
    J * rk1 x y = mobDen J x • rk1 (mob J x) y := by
  have key : mob J x * mobDen J x = J 0 0 * x + J 0 1 := div_mul_cancel₀ _ hd
  ext i j
  fin_cases i <;> fin_cases j
  · simp [rk1, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination -key
  · simp [rk1, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination y * key
  · simp [rk1, Matrix.mul_apply, Fin.sum_univ_two, mobDen]
  · simp [rk1, Matrix.mul_apply, Fin.sum_univ_two, mobDen]
    ring

/-! ## The junction lemma -/

/-- **Junction lemma.** -/
theorem exists_junction_word {σ σ' τ τ' : ℝ} (hs : ConjPair σ σ') (ht : ConjPair τ τ')
    (hσ : 1 < σ) (hτ'₁ : -1 < τ') (hτ'₂ : τ' < 0)
    {P Q : GL2Z} (hP : P ∈ stab σ hs.irrational) (hQ : Q ∈ stab τ ht.irrational)
    (hPl : 1 < lam σ P) (hQl : 1 < lam τ Q) (J : GL2Z)
    (hJ : mob (intToReal J) τ ≠ σ') :
    ∃ m : ℕ, ∃ w : CFWord, PositiveWord w ∧ w ≠ [] ∧
      (w.matrix = ((P ^ m * J * Q ^ m : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ) ∨
        w.matrix = -((P ^ m * J * Q ^ m : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ)) := by
  set J' := intToReal J
  have hdJ := mobDen_GL2Z_ne_zero ht.irrational J
  set c := (σ - σ')⁻¹ * (τ - τ')⁻¹ * ((J' 0 0 * τ + J' 0 1) - σ' * (J' 1 0 * τ + J' 1 1))
  have hc : c ≠ 0 := by
    have h1 : (σ - σ')⁻¹ ≠ 0 := inv_ne_zero (sub_ne_zero.mpr hs.ne)
    have h2 : (τ - τ')⁻¹ ≠ 0 := inv_ne_zero (sub_ne_zero.mpr ht.ne)
    refine mul_ne_zero (mul_ne_zero h1 h2) ?_
    intro h0
    apply hJ
    rw [mob, div_eq_iff hdJ, mobDen]
    linarith
  have hlimit : specProj σ σ' * J' * specProj τ τ' = c • rk1 σ τ' := by
    simp only [specProj, Matrix.smul_mul, Matrix.mul_smul, rk1_mul_rk1, smul_smul]
    congr 1
    simp only [c]
    ring
  have hT := ((tendsto_normalized_pow hs hP hPl).mul (tendsto_const_nhds (x := J'))).mul
    (tendsto_normalized_pow ht hQ hQl)
  rw [hlimit] at hT
  have hκ (m : ℕ) : 0 < lam σ P ^ m * lam τ Q ^ m := by
    have : 0 < lam σ P := by linarith
    have : 0 < lam τ Q := by linarith
    positivity
  refine exists_word_of_tendsto (fun m => P ^ m * J * Q ^ m) _ hκ hc hσ hτ'₁ hτ'₂ ?_
  refine hT.congr fun m => ?_
  simp only [Units.val_mul, intToReal_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  rw [mul_inv]
  ring

/-- **Left-end junction.** If `J τ > 1`, then `±J Q^m` is a word for some `m`. -/
theorem exists_left_junction_word {τ τ' : ℝ} (ht : ConjPair τ τ')
    (hτ'₁ : -1 < τ') (hτ'₂ : τ' < 0) {Q : GL2Z} (hQ : Q ∈ stab τ ht.irrational)
    (hQl : 1 < lam τ Q) (J : GL2Z) (hJ : 1 < mob (intToReal J) τ) :
    ∃ m : ℕ, ∃ w : CFWord, PositiveWord w ∧ w ≠ [] ∧
      (w.matrix = ((J * Q ^ m : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ) ∨
        w.matrix = -((J * Q ^ m : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ)) := by
  set J' := intToReal J
  have hdJ := mobDen_GL2Z_ne_zero ht.irrational J
  set c := (τ - τ')⁻¹ * mobDen J' τ
  have hc : c ≠ 0 := mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr ht.ne)) hdJ
  have hlimit : J' * specProj τ τ' = c • rk1 (mob J' τ) τ' := by
    rw [specProj, Matrix.mul_smul, mul_rk1 _ _ _ hdJ, smul_smul]
  have hT := (tendsto_const_nhds (x := J')).mul (tendsto_normalized_pow ht hQ hQl)
  rw [hlimit] at hT
  have hκ (m : ℕ) : 0 < lam τ Q ^ m := pow_pos (by linarith) m
  refine exists_word_of_tendsto (fun m => J * Q ^ m) _ hκ hc hJ hτ'₁ hτ'₂ ?_
  refine hT.congr fun m => ?_
  simp only [Units.val_mul, intToReal_mul, Matrix.mul_smul]
  rfl

end TwoPoint
