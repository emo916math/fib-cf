module

public import TwoPoint.Patches

/-!
# Patch words and exponents

The middle matrices `X_i(n)` lie in the stabilizer of `σ = σ_(i, n mod g_i)`
with eigenvalue `c · s_n · α^n`, where the scalar `s_n` satisfies
`|s_(n+L)| = |s_n| / √|b|^L` (compare determinants). So the eigenvalue grows
by `κ^L` with `κ = α / √|b| > 1` (that is, `κ² = |ρ|`). The stabilizer contains the
hyperbolic element `(X_i(ρ + L) X_i(ρ)⁻¹)²` of eigenvalue `κ^(2L)`, hence is `±` cyclic with a
generator `P_(i,ρ)` that is a continued-fraction word (since `σ` is reduced).
Writing `X_i(n) = ±P^(e(n))`, the exponent satisfies `e(n + L) = e(n) + δ`
with `δ > 0` depending only on `n mod g_i`.
-/

@[expose] public section
noncomputable section

namespace TwoPoint

/-- `κ = α / √|b|`, the growth rate of the patch eigenvalues; `κ² = |α/β|`. -/
def kappa (a b : ℤ) : ℝ := alpha a b / Real.sqrt |(b : ℝ)|

theorem kappa_sq_mul {a b : ℤ} (hab : GenAdmissible a b) :
    kappa a b ^ 2 * |(b : ℝ)| = alpha a b ^ 2 := by
  have hb : 0 < |(b : ℝ)| := abs_pos.mpr (by exact_mod_cast hab.b_ne_zero)
  rw [kappa, div_pow, Real.sq_sqrt hb.le, div_mul_cancel₀ _ hb.ne']

theorem kappa_pos {a b : ℤ} (hab : GenAdmissible a b) : 0 < kappa a b := by
  have hb : 0 < |(b : ℝ)| := abs_pos.mpr (by exact_mod_cast hab.b_ne_zero)
  exact div_pos (by linarith [one_lt_alpha hab]) (Real.sqrt_pos.mpr hb)

theorem one_lt_kappa {a b : ℤ} (hab : GenAdmissible a b) : 1 < kappa a b := by
  have hα := one_lt_alpha hab
  have hb : 0 < |(b : ℝ)| := abs_pos.mpr (by exact_mod_cast hab.b_ne_zero)
  -- `|b| = α |β| < α²`.
  have hβ := abs_beta_lt_alpha hab
  have hαβ : |(b : ℝ)| = alpha a b * |beta a b| := by
    have := congrArg abs (alpha_mul_beta hab)
    rw [abs_mul, abs_neg, abs_of_pos (show 0 < alpha a b by linarith)] at this
    exact this.symm
  have hlt : |(b : ℝ)| < alpha a b ^ 2 := by rw [hαβ]; nlinarith
  have h2 := kappa_sq_mul hab
  have hk := kappa_pos hab
  have hk2 : 1 < kappa a b ^ 2 := by
    by_contra h
    push_neg at h
    have := mul_le_mul_of_nonneg_right h hb.le
    linarith
  nlinarith

namespace Ctx

variable (C : Ctx)

theorem abs_det_GL2Z (G : GL2Z) : |(intToReal G).det| = 1 := by
  rw [intToReal_det]
  rcases G.det_eq with h | h <;> simp [h]

theorem abs_det_U {i : ℕ} (hi : i ≤ C.k) (n : ℕ) :
    |(C.U i n).det| = |(C.b : ℝ)| ^ (n * i) := by
  rw [U, ratToReal_det, C.Uq_eq_evalU hi, evalU_det]
  push_cast
  rw [abs_pow, abs_neg]

/-- Comparing determinants in the defining identity of `X_i(n)`. -/
theorem Xc_rel {i : ℕ} (hi : i < C.k) (n : ℕ) :
    |(C.b : ℝ)| ^ (n % C.m (i + 1) * (i + 1)) * |(C.b : ℝ)| ^ (n * i) =
      C.Xc i n ^ 2 * (|(C.b : ℝ)| ^ (n % C.m i * i) * |(C.b : ℝ)| ^ (n * (i + 1))) := by
  obtain ⟨-, hX⟩ := C.X_spec hi n
  have h := congrArg (fun M => |Matrix.det M|) hX
  simp only [Matrix.det_mul, Matrix.det_smul, abs_mul, abs_det_GL2Z, Fintype.card_fin, one_mul,
    abs_pow, sq_abs] at h
  have hT : |(C.U (i + 1) n).det| = |(C.U i n).det| * |(ratToReal (C.T i) ^ n).det| := by
    rw [U_succ, Matrix.det_mul, abs_mul]
  rw [← C.abs_det_U (Nat.succ_le_of_lt hi), ← C.abs_det_U hi.le, ← C.abs_det_U hi.le,
    ← C.abs_det_U (Nat.succ_le_of_lt hi), h, hT]
  ring


theorem add_mod_of_dvd {n d L : ℕ} (h : d ∣ L) : (n + L) % d = n % d := by
  obtain ⟨c, rfl⟩ := h
  exact Nat.add_mul_mod_self_left n d c

theorem mod_add_L {i n : ℕ} :
    (n + C.L i) % C.m i = n % C.m i ∧ (n + C.L i) % C.m (i + 1) = n % C.m (i + 1) ∧
      (n + C.L i) % C.g i = n % C.g i := by
  have h1 : C.m i ∣ C.L i := Nat.dvd_lcm_left _ _
  have h2 : C.m (i + 1) ∣ C.L i := Nat.dvd_lcm_right _ _
  have h3 : C.g i ∣ C.L i := (Nat.gcd_dvd_left _ _).trans h1
  exact ⟨add_mod_of_dvd h1, add_mod_of_dvd h2, add_mod_of_dvd h3⟩

/-- The constant `c` in the eigenvalue `c · α^n` of `X_i(n)`. -/
def cX (i n : ℕ) : ℝ :=
  (mobDen (intToReal (C.Hm i (n % C.m (i + 1)))) (C.sig i (n % C.g i)) /
      mobDen (C.U (i + 1) (n % C.m (i + 1))) (C.xi i)) *
    (mobDen (C.U i (n % C.m i)) (C.xi i) /
      mobDen (intToReal (C.Hp i (n % C.m i))) (C.sig i (n % C.g i)))

theorem cX_ne_zero {i : ℕ} (hi : i < C.k) (n : ℕ) : C.cX i n ≠ 0 := by
  have hs := (C.sig_pair hi (n % C.g i)).irrational
  have hξ := (C.xi_pair hi).irrational
  unfold cX
  refine mul_ne_zero (div_ne_zero (mobDen_GL2Z_ne_zero hs _)
    (C.mobDen_U_ne_zero (Nat.succ_le_of_lt hi) _ hξ))
    (div_ne_zero (C.mobDen_U_ne_zero hi.le _ hξ) (mobDen_GL2Z_ne_zero hs _))

theorem cX_add_L (i n : ℕ) : C.cX i (n + C.L i) = C.cX i n := by
  obtain ⟨h1, h2, h3⟩ := C.mod_add_L (i := i) (n := n)
  simp only [cX, h1, h2, h3]

theorem X_mob {i : ℕ} (hi : i < C.k) (n : ℕ) :
    mob (intToReal (C.X i n)) (C.sig i (n % C.g i)) = C.sig i (n % C.g i) ∧
      lam (C.sig i (n % C.g i)) (C.X i n) = C.cX i n * C.Xc i n * alpha C.a C.b ^ n := by
  have hne : C.cX i n * C.Xc i n * alpha C.a C.b ^ n ≠ 0 :=
    mul_ne_zero (mul_ne_zero (C.cX_ne_zero hi n) (C.X_spec hi n).1) (pow_ne_zero _ C.alpha_ne_zero)
  exact mob_of_mulVec hne (C.X_mulVec hi n)

theorem X_mem_stab {i : ℕ} (hi : i < C.k) (n : ℕ) :
    C.X i n ∈ stab (C.sig i (n % C.g i)) (C.sig_pair hi _).irrational :=
  (C.X_mob hi n).1

theorem Xc_add_L {i : ℕ} (hi : i < C.k) (n : ℕ) :
    C.Xc i (n + C.L i) ^ 2 * |(C.b : ℝ)| ^ C.L i = C.Xc i n ^ 2 := by
  have hB : 0 < |(C.b : ℝ)| := abs_pos.mpr (by exact_mod_cast C.hab.b_ne_zero)
  have e1 := C.Xc_rel hi n
  have e2 := C.Xc_rel hi (n + C.L i)
  obtain ⟨h1, h2, -⟩ := C.mod_add_L (i := i) (n := n)
  rw [h1, h2, show (n + C.L i) * i = n * i + C.L i * i by ring,
    show (n + C.L i) * (i + 1) = n * (i + 1) + (C.L i * i + C.L i) by ring,
    pow_add, pow_add, pow_add] at e2
  have hK : |(C.b : ℝ)| ^ (n % C.m i * i) * |(C.b : ℝ)| ^ (n * (i + 1)) *
      |(C.b : ℝ)| ^ (C.L i * i) ≠ 0 := by positivity
  have : (C.Xc i (n + C.L i) ^ 2 * |(C.b : ℝ)| ^ C.L i - C.Xc i n ^ 2) *
      (|(C.b : ℝ)| ^ (n % C.m i * i) * |(C.b : ℝ)| ^ (n * (i + 1)) *
        |(C.b : ℝ)| ^ (C.L i * i)) = 0 := by
    linear_combination |(C.b : ℝ)| ^ (C.L i * i) * e1 - e2
  rcases mul_eq_zero.mp this with h | h
  · linarith
  · exact absurd h hK

theorem abs_lam_X_add_L {i : ℕ} (hi : i < C.k) (n : ℕ) :
    |lam (C.sig i (n % C.g i)) (C.X i (n + C.L i))| =
      |lam (C.sig i (n % C.g i)) (C.X i n)| * kappa C.a C.b ^ C.L i := by
  have h := (C.X_mob hi (n + C.L i)).2
  rw [(C.mod_add_L (i := i) (n := n)).2.2, C.cX_add_L] at h
  rw [h, (C.X_mob hi n).2, ← abs_of_pos (pow_pos (kappa_pos C.hab) (C.L i)), ← abs_mul]
  apply (sq_eq_sq_iff_abs_eq_abs _ _).mp
  have hk := kappa_sq_mul C.hab
  have hX := C.Xc_add_L hi n
  have hκ : (kappa C.a C.b ^ C.L i) ^ 2 * |(C.b : ℝ)| ^ C.L i = alpha C.a C.b ^ (2 * C.L i) := by
    rw [← pow_mul, mul_comm (C.L i) 2, pow_mul, pow_mul, ← mul_pow, hk]
  have hB : (|(C.b : ℝ)| ^ C.L i) ≠ 0 :=
    pow_ne_zero _ (abs_ne_zero.mpr (by exact_mod_cast C.hab.b_ne_zero))
  apply mul_right_cancel₀ hB
  calc (C.cX i n * C.Xc i (n + C.L i) * alpha C.a C.b ^ (n + C.L i)) ^ 2 * |(C.b : ℝ)| ^ C.L i
      = (C.cX i n * alpha C.a C.b ^ n) ^ 2 * alpha C.a C.b ^ (2 * C.L i) *
          (C.Xc i (n + C.L i) ^ 2 * |(C.b : ℝ)| ^ C.L i) := by ring
    _ = (C.cX i n * alpha C.a C.b ^ n) ^ 2 * ((kappa C.a C.b ^ C.L i) ^ 2 * |(C.b : ℝ)| ^ C.L i) *
          C.Xc i n ^ 2 := by rw [hX, hκ]
    _ = _ := by ring

/-! ## Patch generators -/

theorem exists_patch {i : ℕ} (hi : i < C.k) (ρ : ℕ) :
    ∃ P ∈ stab (C.sig i (ρ % C.g i)) (C.sig_pair hi _).irrational,
      1 < lam (C.sig i (ρ % C.g i)) P ∧
      ∀ M ∈ stab (C.sig i (ρ % C.g i)) (C.sig_pair hi _).irrational,
        ∃ e : ℤ, M = P ^ e ∨ M = -(P ^ e) := by
  set r := ρ % C.g i
  have hr : r % C.g i = r := Nat.mod_mod _ _
  have h1 := C.X_mem_stab hi (r + C.L i)
  have h0 := C.X_mem_stab hi r
  rw [(C.mod_add_L (i := i) (n := r)).2.2, hr] at h1
  rw [hr] at h0
  have hZ := (stab _ _).mul_mem h1 ((stab _ _).inv_mem h0)
  refine stab_cyclic (C.sig_pair hi r) ((stab _ _).pow_mem hZ 2) ?_
  have hl := C.abs_lam_X_add_L hi r
  rw [hr] at hl
  rw [lam_pow hZ, lam_mul _ ((stab _ _).inv_mem h0), lam_inv h0, ← sq_abs, abs_mul, hl, abs_inv]
  have hX0 : |lam (C.sig i r) (C.X i r)| ≠ 0 :=
    abs_ne_zero.mpr (lam_ne_zero (C.sig_pair hi r).irrational _)
  rw [mul_comm (|lam (C.sig i r) (C.X i r)|), mul_assoc, mul_inv_cancel₀ hX0, mul_one, ← pow_mul]
  exact one_lt_pow₀ (one_lt_kappa C.hab) (by have := C.L_pos i; omega)

/-- The patch generator `P_(i,ρ)`, depending on `ρ mod g_i`. -/
def P (i ρ : ℕ) : GL2Z :=
  if hi : i < C.k then Classical.choose (C.exists_patch hi ρ) else 1

theorem P_spec {i : ℕ} (hi : i < C.k) (ρ : ℕ) :
    C.P i ρ ∈ stab (C.sig i (ρ % C.g i)) (C.sig_pair hi _).irrational ∧
      1 < lam (C.sig i (ρ % C.g i)) (C.P i ρ) ∧
      ∀ M ∈ stab (C.sig i (ρ % C.g i)) (C.sig_pair hi _).irrational,
        ∃ e : ℤ, M = C.P i ρ ^ e ∨ M = -(C.P i ρ ^ e) := by
  have : C.P i ρ = Classical.choose (C.exists_patch hi ρ) := by
    unfold P
    rw [dif_pos hi]
  rw [this]
  exact Classical.choose_spec (C.exists_patch hi ρ)

/-- The generator with eigenvalue `> 1` of a stabilizer is unique. -/
theorem stab_generator_unique {σ σ' : ℝ} (h : ConjPair σ σ') {P P' : GL2Z}
    (hP : P ∈ stab σ h.irrational) (hP' : P' ∈ stab σ h.irrational)
    (hl : 1 < lam σ P) (hl' : 1 < lam σ P')
    (gP : ∀ M ∈ stab σ h.irrational, ∃ e : ℤ, M = P ^ e ∨ M = -(P ^ e))
    (gP' : ∀ M ∈ stab σ h.irrational, ∃ e : ℤ, M = P' ^ e ∨ M = -(P' ^ e)) : P = P' := by
  have key : ∀ {A B : GL2Z}, A ∈ stab σ h.irrational → 1 < lam σ A → 1 < lam σ B →
      (∃ e : ℤ, B = A ^ e ∨ B = -(A ^ e)) → ∃ e : ℤ, 0 < e ∧ B = A ^ e ∧ lam σ B = lam σ A ^ e := by
    intro A B hA hlA hlB ⟨e, he⟩
    have hpos : 0 < lam σ A ^ e := zpow_pos (by linarith) e
    rcases he with rfl | rfl
    · refine ⟨e, ?_, rfl, lam_zpow hA e⟩
      by_contra hle
      push_neg at hle
      have := zpow_le_one_of_nonpos₀ hlA.le hle
      rw [lam_zpow hA] at hlB
      linarith
    · rw [lam_neg, lam_zpow hA] at hlB
      linarith
  obtain ⟨e, he, rfl, hle⟩ := key hP hl hl' (gP P' hP')
  obtain ⟨f, hf, hPf, hlf⟩ := key ((stab σ _).zpow_mem hP e) hl' hl (gP' P hP)
  rw [hle, ← zpow_mul] at hlf
  have hef : e * f = 1 := by
    have hpos : 0 < lam σ P := by linarith
    have := zpow_right_injective₀ hpos (ne_of_gt hl) (show lam σ P ^ (1 : ℤ) = lam σ P ^ (e * f) by
      rw [zpow_one]; exact hlf)
    exact this.symm
  have he1 : e = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hef with h1 | h1 <;> omega
  rw [he1, zpow_one]

/-- Equal representatives have equal patch generators. -/
theorem P_eq_of_sig_eq {i i' : ℕ} (hi : i < C.k) (hi' : i' < C.k) (ρ ρ' : ℕ)
    (h : C.sig i (ρ % C.g i) = C.sig i' (ρ' % C.g i')) : C.P i ρ = C.P i' ρ' := by
  obtain ⟨hP, hPl, hPg⟩ := C.P_spec hi ρ
  obtain ⟨hP', hPl', hPg'⟩ := C.P_spec hi' ρ'
  have hpair := C.sig_pair hi' (ρ' % C.g i')
  rw [h] at hPl
  refine stab_generator_unique hpair (mem_stab.mpr ?_) hP' hPl hPl' (fun M hM => hPg M ?_) hPg'
  · rw [← h]; exact mem_stab.mp hP
  · rw [mem_stab, h]; exact mem_stab.mp hM

/-- The patch word. -/
theorem exists_patch_word {i : ℕ} (hi : i < C.k) (ρ : ℕ) :
    ∃ w : CFWord, PositiveWord w ∧ w ≠ [] ∧ w.matrix = C.P i ρ := by
  obtain ⟨hP, hPl, -⟩ := C.P_spec hi ρ
  obtain ⟨h1, h2, h3⟩ := C.sig_reduced hi (ρ % C.g i)
  exact exists_word_of_reduced_stabilizer (C.sig_pair hi _) h1 h2 h3 _ hP hPl

/-! ## Exponents -/

theorem P_mod (i n : ℕ) : C.P i (n % C.g i) = C.P i n := by
  unfold P
  split_ifs with hi
  · congr 1
    simp only [Nat.mod_mod]
  · rfl

theorem exists_exponent {i : ℕ} (hi : i < C.k) (n : ℕ) :
    ∃ e : ℤ, C.X i n = C.P i n ^ e ∨ C.X i n = -(C.P i n ^ e) := by
  exact (C.P_spec hi n).2.2 _ (C.X_mem_stab hi n)

/-- The exponent `e_i(n)` with `X_i(n) = ±P_(i,n)^(e_i(n))`. -/
def e (i n : ℕ) : ℤ :=
  if hi : i < C.k then Classical.choose (C.exists_exponent hi n) else 0

theorem e_spec {i : ℕ} (hi : i < C.k) (n : ℕ) :
    C.X i n = C.P i n ^ C.e i n ∨ C.X i n = -(C.P i n ^ C.e i n) := by
  have : C.e i n = Classical.choose (C.exists_exponent hi n) := by
    unfold e
    rw [dif_pos hi]
  rw [this]
  exact Classical.choose_spec (C.exists_exponent hi n)

/-- The eigenvalue of the patch at `n`. -/
def lamP (i n : ℕ) : ℝ := lam (C.sig i (n % C.g i)) (C.P i n)

theorem one_lt_lamP {i : ℕ} (hi : i < C.k) (n : ℕ) : 1 < C.lamP i n := by
  exact (C.P_spec hi n).2.1

theorem abs_lam_X {i : ℕ} (hi : i < C.k) (n : ℕ) :
    |lam (C.sig i (n % C.g i)) (C.X i n)| = C.lamP i n ^ C.e i n := by
  have hP := (C.P_spec hi n).1
  have hpos : 0 < C.lamP i n := by linarith [C.one_lt_lamP hi n]
  rcases C.e_spec hi n with h | h
  · rw [h, lam_zpow hP]
    exact abs_of_pos (zpow_pos hpos _)
  · rw [h, lam_neg, lam_zpow hP, abs_neg]
    exact abs_of_pos (zpow_pos hpos _)

theorem lamP_add_L (i n : ℕ) : C.lamP i (n + C.L i) = C.lamP i n := by
  unfold lamP
  rw [(C.mod_add_L (i := i) (n := n)).2.2, ← C.P_mod i (n + C.L i),
    (C.mod_add_L (i := i) (n := n)).2.2, C.P_mod]

theorem lamP_pow_shift {i : ℕ} (hi : i < C.k) (n : ℕ) :
    C.lamP i n ^ (C.e i (n + C.L i) - C.e i n) = kappa C.a C.b ^ C.L i := by
  have hpos : 0 < C.lamP i n := by linarith [C.one_lt_lamP hi n]
  have h1 := C.abs_lam_X hi (n + C.L i)
  rw [(C.mod_add_L (i := i) (n := n)).2.2, C.lamP_add_L] at h1
  rw [C.abs_lam_X_add_L hi n, C.abs_lam_X hi n] at h1
  rw [zpow_sub₀ hpos.ne', ← h1]
  field_simp

theorem lamP_mod (i n : ℕ) : C.lamP i (n % C.g i) = C.lamP i n := by
  unfold lamP
  rw [Nat.mod_mod, C.P_mod]

/-- The shift `δ_(i,n) = e_i(n + L) - e_i(n)` depends only on `n mod g_i`. -/
theorem e_shift_eq {i : ℕ} (hi : i < C.k) {n n' : ℕ} (h : n % C.g i = n' % C.g i) :
    C.e i (n + C.L i) - C.e i n = C.e i (n' + C.L i) - C.e i n' := by
  have hl : C.lamP i n = C.lamP i n' := by
    rw [← C.lamP_mod i n, ← C.lamP_mod i n', h]
  have hpos : 0 < C.lamP i n := by linarith [C.one_lt_lamP hi n]
  have hne : C.lamP i n ≠ 1 := by linarith [C.one_lt_lamP hi n]
  apply zpow_right_injective₀ hpos hne
  simp only
  rw [C.lamP_pow_shift hi n, hl, C.lamP_pow_shift hi n']

theorem e_shift_pos {i : ℕ} (hi : i < C.k) (n : ℕ) : 0 < C.e i (n + C.L i) - C.e i n := by
  by_contra hle
  rw [not_lt] at hle
  have h1 := zpow_le_one_of_nonpos₀ (C.one_lt_lamP hi n).le hle
  rw [C.lamP_pow_shift hi n] at h1
  have := one_lt_pow₀ (one_lt_kappa C.hab) (C.L_pos i).ne'
  linarith

/-- On each residue class modulo `L_i`, `e_i` is affine with positive slope. -/
theorem e_affine {i : ℕ} (hi : i < C.k) (r j : ℕ) :
    C.e i (r + j * C.L i) = C.e i r + j * (C.e i (r + C.L i) - C.e i r) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hmod : (r + j * C.L i) % C.g i = r % C.g i := by
      have : C.g i ∣ C.L i := (Nat.gcd_dvd_left _ _).trans (Nat.dvd_lcm_left _ _)
      rw [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_zero_of_dvd this]
      simp
    have := C.e_shift_eq hi hmod
    rw [show r + (j + 1) * C.L i = r + j * C.L i + C.L i by ring]
    push_cast
    linarith

end Ctx

end TwoPoint
