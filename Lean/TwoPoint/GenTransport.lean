module

public import TwoPoint.GenModulus
public import TwoPoint.IntegralBasis

/-!
# The transport of Exercise `exer:main_gen`(c)

Let `t = a^2/b ∈ ℤ` and `v = u_(t+2,-1)` (so `v_0 = 0`, `v_1 = 1`,
`v_n = (t+2) v_(n-1) - v_(n-2)`), and `w_j = v_(j+1) - v_j`. Then

  `u_(2j+1) = b^j w_j`,  `u_(2j+2) = a b^j v_(j+1)`,

so `u_(2m)/(a b^(m-1)) = v_m`, and the pairs `(u_(n+1), u_n)` are, up to the scalars
`b^j` and `a b^j`, the points `(w_j, (a/b) v_j)` (for `n = 2j`) and
`(v_(j+1), w_j / a)` (for `n = 2j+1`). The norm identity `v_(j+1)^2 - (t+2) v_(j+1) v_j
+ v_j^2 = 1` gives `h(w_j, (a/b) v_j) = 1` and `h(v_(j+1), w_j/a) = -1/t`.

If `C` clears the denominators of `Φ_i(X, sY)` then `M(x, y) = Φ_i(x, sy) C` is
an integral homogeneous matrix of degree `i`. Its determinant at the points
above is `c(Φ_i(X, aY/b))`, respectively `±c(Φ_i(X, Y/a))/t^i`. Since
`(v_(j+m), w_(j+m)) ≡ v_(m+1) (v_j, w_j)` modulo `v_m`, the quotient
`M(j+m) M(j)⁻¹` is unimodular as soon as the determinant divides `v_m`. This
gives `G U_i(n) = b^(-im) U_i(n + 2m)` with `G ∈ GL₂(ℤ)`.
-/

@[expose] public section

noncomputable section

namespace TwoPoint

open Polynomial

variable {a b : ℤ}

/-! ## The sequences `v` and `w` -/

/-- `v = u_(t+2,-1)` with `t = a^2/b`. -/
def vSeq (a b : ℤ) : ℕ → ℤ := u (tRatio a b + 2) (-1)

theorem vSeq_add_two (a b : ℤ) (j : ℕ) :
    vSeq a b (j + 2) = (tRatio a b + 2) * vSeq a b (j + 1) - vSeq a b j := by
  simp only [vSeq, u_add_two]
  ring

theorem u_odd_even (hab : GenAdmissible a b) (j : ℕ) :
    u a b (2 * j + 1) = b ^ j * (vSeq a b (j + 1) - vSeq a b j) ∧
      u a b (2 * j + 2) = a * b ^ j * vSeq a b (j + 1) := by
  have ht := hab.tRatio_mul
  induction j with
  | zero => simp [vSeq, u]
  | succ j ih =>
    obtain ⟨h1, h2⟩ := ih
    have e1 : u a b (2 * (j + 1) + 1) = a * u a b (2 * j + 2) + b * u a b (2 * j + 1) := by
      rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by ring, u_add_two]
    have e2 : u a b (2 * (j + 1) + 2) = a * u a b (2 * (j + 1) + 1) + b * u a b (2 * j + 2) := by
      rw [show 2 * (j + 1) + 2 = (2 * j + 2) + 2 by ring, u_add_two]
      ring_nf
    have hv := vSeq_add_two a b j
    have hodd : u a b (2 * (j + 1) + 1) = b ^ (j + 1) * (vSeq a b (j + 1 + 1) - vSeq a b (j + 1)) := by
      rw [e1, h1, h2, show j + 1 + 1 = j + 2 by ring, hv]
      linear_combination (-(b ^ j * vSeq a b (j + 1))) * ht
    refine ⟨hodd, ?_⟩
    rw [e2, hodd, h2]
    ring

/-- `u_(2m) = a b^(m-1) v_m` for `m ≥ 1`. -/
theorem u_two_mul (hab : GenAdmissible a b) {m : ℕ} (hm : 0 < m) :
    u a b (2 * m) = a * b ^ (m - 1) * vSeq a b m := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rw [show 2 * (j + 1) = 2 * j + 2 by ring, (u_odd_even hab j).2, Nat.add_sub_cancel]

/-- The rational form `b u_(2j) = a b^j v_j`, valid also for `j = 0`. -/
theorem u_even_rat (hab : GenAdmissible a b) (j : ℕ) :
    (u a b (2 * j) : ℚ) * b = a * (b : ℚ) ^ j * vSeq a b j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [vSeq]
  · rw [u_two_mul hab hj]
    push_cast
    rw [show j = (j - 1) + 1 by omega, pow_succ, Nat.add_sub_cancel]
    ring

/-- The divisibility of the paper, `N ∣ u_(2m)/(a b^(m-1))`, is `N ∣ v_m`. -/
theorem dvd_u_two_mul_iff (hab : GenAdmissible a b) (N : ℤ) {m : ℕ} (hm : 0 < m) :
    N * (a * b ^ (m - 1)) ∣ u a b (2 * m) ↔ N ∣ vSeq a b m := by
  rw [u_two_mul hab hm, mul_comm (a * b ^ (m - 1))]
  exact mul_dvd_mul_iff_right (mul_ne_zero hab.a_pos.ne' (pow_ne_zero _ hab.b_ne_zero))

theorem vSeq_norm (a b : ℤ) (j : ℕ) :
    vSeq a b (j + 1) ^ 2 - (tRatio a b + 2) * vSeq a b (j + 1) * vSeq a b j + vSeq a b j ^ 2 = 1 := by
  have := u_norm (tRatio a b + 2) (-1) j
  simp only [neg_neg, one_pow] at this
  simp only [vSeq]
  linear_combination this

theorem vSeq_modEq (a b : ℤ) (j m : ℕ) :
    vSeq a b (j + m) ≡ vSeq a b (m + 1) * vSeq a b j [ZMOD vSeq a b m] :=
  u_add_modEq _ _ m j

/-- `v_m ≠ 0`-style existence: `v` has a positive zero index modulo every nonzero integer. -/
theorem exists_pos_dvd_vSeq (a b : ℤ) {N : ℤ} (hN : N ≠ 0) : ∃ m, 0 < m ∧ N ∣ vSeq a b m :=
  exists_pos_dvd_u (Or.inr rfl) N hN

theorem vSeq_dvd_mul (a b : ℤ) (m t : ℕ) : vSeq a b m ∣ vSeq a b (m * t) := by
  induction t with
  | zero => simp [vSeq]
  | succ t ih =>
    have h := vSeq_modEq a b (m * t) m
    rw [show m * (t + 1) = m * t + m by ring]
    obtain ⟨c, hc⟩ := (Int.ModEq.dvd h.symm)
    have : vSeq a b (m * t + m) = vSeq a b (m + 1) * vSeq a b (m * t) + vSeq a b m * c := by
      linarith
    rw [this]
    exact dvd_add (dvd_mul_of_dvd_right ih _) (dvd_mul_right _ _)

/-! ## Homogeneity -/

theorem homSum_reflect {R : Type*} [CommRing R] (p : R[X]) (i : ℕ) (x y : R) :
    homSum p i x y = ∑ ℓ ∈ Finset.range (i + 1), p.coeff (i - ℓ) * x ^ (i - ℓ) * y ^ ℓ := by
  rw [homSum, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  have hℓ' : ℓ ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hℓ)
  rw [show i + 1 - 1 - ℓ = i - ℓ by omega, show i - (i - ℓ) = ℓ by omega]

theorem homEvalMatrix_smul (A : Matrix (Fin 2) (Fin 2) ℚ[X]) (i : ℕ) (c x y : ℚ) :
    homEvalMatrix A i (c * x) (c * y) = c ^ i • homEvalMatrix A i x y := by
  ext r s
  simp only [homEvalMatrix, Matrix.smul_apply, smul_eq_mul, homEval_eq_homSum, homSum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [mul_pow, mul_pow, show c ^ i = c ^ j * c ^ (i - j) by rw [← pow_add, Nat.add_sub_cancel' hj']]
  ring

/-! ## Integral homogeneous matrices -/

variable {A : Matrix (Fin 2) (Fin 2) ℚ[X]} {i : ℕ} {s : ℚ} {C : Matrix (Fin 2) (Fin 2) ℤ}

/-- The integer coefficients of `A(X, sY) C`. -/
def intCoeff (hC : ClearsHom A i s C) (ℓ : ℕ) (r c : Fin 2) : ℤ :=
  if h : ℓ ≤ i then Classical.choose (hC ℓ h r c) else 0

theorem intCoeff_spec (hC : ClearsHom A i s C) {ℓ : ℕ} (h : ℓ ≤ i) (r c : Fin 2) :
    (intCoeff hC ℓ r c : ℚ) = (scaledCoeff A i s ℓ * C.map (Int.cast : ℤ → ℚ)) r c := by
  rw [intCoeff, dif_pos h]
  exact (Classical.choose_spec (hC ℓ h r c)).symm

/-- The integral matrix `M(x, y) = A(x, sy) C`. -/
def intHom (hC : ClearsHom A i s C) (x y : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  Matrix.of fun r c => ∑ ℓ ∈ Finset.range (i + 1), intCoeff hC ℓ r c * x ^ (i - ℓ) * y ^ ℓ

theorem intHom_cast (hC : ClearsHom A i s C) (x y : ℤ) :
    intMatrixCast 2 (intHom hC x y) =
      homEvalMatrix A i (x : ℚ) (s * y) * C.map (Int.cast : ℤ → ℚ) := by
  ext r c
  simp only [intMatrixCast, RingHom.mapMatrix_apply, Matrix.map_apply, intHom, Matrix.of_apply,
    Int.coe_castRingHom, Int.cast_sum, Int.cast_mul, Int.cast_pow]
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  simp only [homEvalMatrix, homEval_eq_homSum, homSum_reflect, Finset.sum_mul,
    ← Finset.sum_add_distrib, Matrix.map_apply]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  have hℓ' : ℓ ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hℓ)
  rw [intCoeff_spec hC hℓ', Matrix.mul_apply, Fin.sum_univ_two]
  simp only [scaledCoeff, Matrix.of_apply, Matrix.map_apply]
  ring

theorem intHom_det (hC : ClearsHom A i s C) (hA : ∀ x y : ℚ,
    (homEvalMatrix A i x y).det = (x ^ 2 - a * x * y - b * y ^ 2) ^ i) (x y : ℤ) :
    ((intHom hC x y).det : ℚ) =
      ((x : ℚ) ^ 2 - a * x * (s * y) - b * (s * y) ^ 2) ^ i * C.det := by
  rw [← intMatrixCast_det, intHom_cast, Matrix.det_mul, hA]
  congr 1
  exact ((Int.castRingHom ℚ).map_det C).symm

theorem intHom_modEq (hC : ClearsHom A i s C) {N : ℕ} {x y x' y' l : ℤ}
    (hx : x' ≡ l * x [ZMOD N]) (hy : y' ≡ l * y [ZMOD N]) (r c : Fin 2) :
    intHom hC x' y' r c ≡ l ^ i * intHom hC x y r c [ZMOD N] := by
  rw [← ZMod.intCast_eq_intCast_iff] at hx hy ⊢
  simp only [intHom, Matrix.of_apply, Int.cast_sum, Int.cast_mul, Int.cast_pow,
    Finset.mul_sum] at hx hy ⊢
  rw [hx, hy]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  have hℓ' : ℓ ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hℓ)
  rw [show ((l : ZMod N)) ^ i = (l : ZMod N) ^ (i - ℓ) * (l : ZMod N) ^ ℓ by
    rw [← pow_add, Nat.sub_add_cancel hℓ']]
  ring

/-- Two points congruent up to a scalar modulo the determinant give a
unimodular transport of `A(x, sy)`. -/
theorem exists_unimodular_transport (hC : ClearsHom A i s C) (hCdet : C.det ≠ 0)
    {x y x' y' l : ℤ} (hdet0 : (intHom hC x y).det ≠ 0)
    (hdet : (intHom hC x' y').det = (intHom hC x y).det)
    (hx : x' ≡ l * x [ZMOD ((intHom hC x y).det.natAbs : ℤ)])
    (hy : y' ≡ l * y [ZMOD ((intHom hC x y).det.natAbs : ℤ)]) :
    ∃ G : Matrix (Fin 2) (Fin 2) ℤ, IsUnit G ∧
      intMatrixCast 2 G * homEvalMatrix A i (x : ℚ) (s * y) =
        homEvalMatrix A i (x' : ℚ) (s * y') := by
  have hcong : ∀ r c, (intHom hC x y).det ∣ intHom hC x' y' r c - l ^ i * intHom hC x y r c := by
    intro r c
    exact Int.natAbs_dvd.mp ((intHom_modEq hC hx hy r c).symm.dvd)
  obtain ⟨G, hGX, -⟩ := intMatrix_quotient_integral _ _ (l ^ i) hdet0 hcong
  have hGdet : G.det = 1 := by
    apply mul_right_cancel₀ hdet0
    rw [← Matrix.det_mul, hGX, hdet, one_mul]
  refine ⟨G, (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [hGdet]; exact isUnit_one), ?_⟩
  have h := congrArg (intMatrixCast 2) hGX
  rw [map_mul, intHom_cast, intHom_cast, ← Matrix.mul_assoc] at h
  have hCu : IsUnit (C.map (Int.cast : ℤ → ℚ)).det := by
    have : (C.map (Int.cast : ℤ → ℚ)).det = (C.det : ℚ) := by simp [Matrix.det_fin_two]
    rw [this]
    exact isUnit_iff_ne_zero.mpr (by exact_mod_cast hCdet)
  have := congrArg (· * (C.map (Int.cast : ℤ → ℚ))⁻¹) h
  simpa only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hCu, Matrix.mul_one] using this

/-! ## The two parities -/

/-- `w_j = v_(j+1) - v_j`. -/
def wSeq (a b : ℤ) (j : ℕ) : ℤ := vSeq a b (j + 1) - vSeq a b j

theorem wSeq_modEq (a b : ℤ) (j m : ℕ) :
    wSeq a b (j + m) ≡ vSeq a b (m + 1) * wSeq a b j [ZMOD vSeq a b m] := by
  have h1 := vSeq_modEq a b (j + 1) m
  have h2 := vSeq_modEq a b j m
  rw [show j + 1 + m = j + m + 1 by ring] at h1
  unfold wSeq
  rw [mul_sub]
  exact h1.sub h2

theorem evalU_even (hab : GenAdmissible a b) {k i : ℕ}
    (B : NormalizedPadeBasis (a : ℚ) (b : ℚ) k i) (j : ℕ) :
    evalU B (2 * j) = ((b : ℚ) ^ j) ^ i •
      homEvalMatrix B.matrix i (wSeq a b j : ℚ) ((a : ℚ) / b * vSeq a b j) := by
  have hb : (b : ℚ) ≠ 0 := by exact_mod_cast hab.b_ne_zero
  have h1 : (u a b (2 * j + 1) : ℚ) = (b : ℚ) ^ j * wSeq a b j := by
    rw [(u_odd_even hab j).1, wSeq]
    push_cast
    ring
  have h0 : (u a b (2 * j) : ℚ) = (b : ℚ) ^ j * ((a : ℚ) / b * vSeq a b j) := by
    have := u_even_rat hab j
    field_simp
    linear_combination this
  rw [evalU, h1, h0, homEvalMatrix_smul]

theorem evalU_odd (hab : GenAdmissible a b) {k i : ℕ}
    (B : NormalizedPadeBasis (a : ℚ) (b : ℚ) k i) (j : ℕ) :
    evalU B (2 * j + 1) = ((a : ℚ) * b ^ j) ^ i •
      homEvalMatrix B.matrix i (vSeq a b (j + 1) : ℚ) (1 / (a : ℚ) * wSeq a b j) := by
  have ha : (a : ℚ) ≠ 0 := by exact_mod_cast hab.a_pos.ne'
  have h1 : (u a b (2 * j + 1 + 1) : ℚ) = (a * (b : ℚ) ^ j) * vSeq a b (j + 1) := by
    rw [show 2 * j + 1 + 1 = 2 * j + 2 by ring, (u_odd_even hab j).2]
    push_cast
    ring
  have h0 : (u a b (2 * j + 1) : ℚ) = (a * (b : ℚ) ^ j) * (1 / (a : ℚ) * wSeq a b j) := by
    rw [(u_odd_even hab j).1, wSeq]
    push_cast
    field_simp
  rw [evalU, h1, h0, homEvalMatrix_smul]

theorem norm_even (hab : GenAdmissible a b) (j : ℕ) :
    ((wSeq a b j : ℚ)) ^ 2 - a * wSeq a b j * ((a : ℚ) / b * vSeq a b j) -
      b * ((a : ℚ) / b * vSeq a b j) ^ 2 = 1 := by
  have hb : (b : ℚ) ≠ 0 := by exact_mod_cast hab.b_ne_zero
  have ht : (tRatio a b : ℚ) * b = (a : ℚ) ^ 2 := by exact_mod_cast hab.tRatio_mul
  have hn : ((vSeq a b (j + 1) ^ 2 - (tRatio a b + 2) * vSeq a b (j + 1) * vSeq a b j +
      vSeq a b j ^ 2 : ℤ) : ℚ) = 1 := by exact_mod_cast vSeq_norm a b j
  push_cast at hn
  unfold wSeq
  push_cast
  field_simp
  linear_combination b * hn - (vSeq a b j : ℚ) * (vSeq a b (j + 1) : ℚ) * ht -
    ((vSeq a b j : ℚ) ^ 2 - (vSeq a b j : ℚ) * vSeq a b (j + 1) + (vSeq a b j : ℚ) ^ 2 -
      (vSeq a b j : ℚ) ^ 2) * ht +
    ((vSeq a b (j + 1) : ℚ) * vSeq a b j + (vSeq a b j : ℚ) ^ 2) * ht

theorem norm_odd (hab : GenAdmissible a b) (j : ℕ) :
    ((vSeq a b (j + 1) : ℚ)) ^ 2 - a * vSeq a b (j + 1) * (1 / (a : ℚ) * wSeq a b j) -
      b * (1 / (a : ℚ) * wSeq a b j) ^ 2 = -1 / tRatio a b := by
  have ha : (a : ℚ) ≠ 0 := by exact_mod_cast hab.a_pos.ne'
  have hb : (b : ℚ) ≠ 0 := by exact_mod_cast hab.b_ne_zero
  have ht : (tRatio a b : ℚ) * b = (a : ℚ) ^ 2 := by exact_mod_cast hab.tRatio_mul
  have htz : (tRatio a b : ℚ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at ht
    exact pow_ne_zero 2 ha ht.symm
  have hn : ((vSeq a b (j + 1) ^ 2 - (tRatio a b + 2) * vSeq a b (j + 1) * vSeq a b j +
      vSeq a b j ^ 2 : ℤ) : ℚ) = 1 := by exact_mod_cast vSeq_norm a b j
  push_cast at hn
  unfold wSeq
  push_cast
  field_simp
  linear_combination (-(a : ℚ) ^ 2) * hn +
    ((vSeq a b (j + 1) : ℚ) - vSeq a b j) ^ 2 * ht -
    2 * ((vSeq a b (j + 1) : ℚ) - vSeq a b j) ^ 2 * ht

/-! ## The transport -/

/-- **Exercise `exer:main_gen`(c)**, the integrality step: if
`lcm{c(Φ_i(X, aY/b)), c(Φ_i(X, Y/a))/t^i}` divides `v_m`, then
`G U_i(n) = b^(-im) U_i(n + 2m)` for some `G ∈ GL₂(ℤ)`. -/
theorem exists_transport_exer (hab : GenAdmissible a b) {k i : ℕ}
    (B : NormalizedPadeBasis (a : ℚ) (b : ℚ) k i) {m : ℕ}
    (hm : ((exerLcm a b B.matrix i : ℕ) : ℤ) ∣ vSeq a b m) (n : ℕ) :
    ∃ G : Matrix (Fin 2) (Fin 2) ℤ, IsUnit G ∧ ∃ c : ℚ, c ≠ 0 ∧
      intMatrixCast 2 G * evalU B n = c • evalU B (n + 2 * m) := by
  have hb : (b : ℚ) ≠ 0 := by exact_mod_cast hab.b_ne_zero
  have ha : (a : ℚ) ≠ 0 := by exact_mod_cast hab.a_pos.ne'
  have hA : ∀ x y : ℚ, (homEvalMatrix B.matrix i x y).det = (x ^ 2 - a * x * y - b * y ^ 2) ^ i :=
    fun x y => B.homEval_det x y
  set l := vSeq a b (m + 1)
  rcases Nat.even_or_odd' n with ⟨j, rfl | rfl⟩
  · -- `n = 2j`: the points `(w_j, (a/b) v_j)`.
    obtain ⟨hd₁, C, hC, hCdet⟩ := clearingDet_spec B.matrix i ((a : ℚ) / b)
    have hdet (j : ℕ) : (intHom hC (wSeq a b j) (vSeq a b j)).det =
        (clearingDet B.matrix i ((a : ℚ) / b) : ℤ) := by
      have := intHom_det hC hA (wSeq a b j) (vSeq a b j)
      rw [norm_even hab j, one_pow, one_mul, hCdet] at this
      exact_mod_cast this
    have hN : (((intHom hC (wSeq a b j) (vSeq a b j)).det.natAbs : ℕ) : ℤ) ∣ vSeq a b m := by
      rw [hdet, Int.natAbs_natCast]
      exact (Int.natCast_dvd_natCast.mpr (Nat.dvd_lcm_left _ _)).trans hm
    obtain ⟨G, hG, hGe⟩ := exists_unimodular_transport hC (by rw [hCdet]; exact_mod_cast hd₁.ne')
      (x := wSeq a b j) (y := vSeq a b j) (x' := wSeq a b (j + m)) (y' := vSeq a b (j + m)) (l := l)
      (by rw [hdet]; exact_mod_cast hd₁.ne') (by rw [hdet, hdet])
      ((wSeq_modEq a b j m).of_dvd hN) ((vSeq_modEq a b j m).of_dvd hN)
    refine ⟨G, hG, (((b : ℚ) ^ m) ^ i)⁻¹, inv_ne_zero (pow_ne_zero _ (pow_ne_zero _ hb)), ?_⟩
    rw [show 2 * j + 2 * m = 2 * (j + m) by ring, evalU_even hab, evalU_even hab, Matrix.mul_smul,
      hGe, smul_smul, pow_add, mul_pow]
    congr 1
    field_simp
  · -- `n = 2j+1`: the points `(v_(j+1), w_j / a)`.
    obtain ⟨hd₂, C, hC, hCdet⟩ := clearingDet_spec B.matrix i (1 / (a : ℚ))
    set t := tRatio a b
    have ht : (t : ℚ) ≠ 0 := by
      intro h
      have := hab.tRatio_mul
      have h' : (t : ℚ) * b = (a : ℚ) ^ 2 := by exact_mod_cast this
      rw [h, zero_mul] at h'
      exact pow_ne_zero 2 ha h'.symm
    have hdet (j : ℕ) : (intHom hC (vSeq a b (j + 1)) (wSeq a b j)).det * t ^ i =
        (-1) ^ i * (clearingDet B.matrix i (1 / (a : ℚ)) : ℤ) := by
      have := intHom_det hC hA (vSeq a b (j + 1)) (wSeq a b j)
      rw [norm_odd hab j, hCdet] at this
      have h' : ((intHom hC (vSeq a b (j + 1)) (wSeq a b j)).det : ℚ) * (t : ℚ) ^ i =
          (-1) ^ i * (clearingDet B.matrix i (1 / (a : ℚ)) : ℚ) := by
        rw [this, div_pow, neg_pow, show ((tRatio a b : ℤ) : ℚ) = (t : ℚ) from rfl]
        push_cast
        field_simp
      exact_mod_cast h'
    have hdet' : (intHom hC (vSeq a b (j + m + 1)) (wSeq a b (j + m))).det =
        (intHom hC (vSeq a b (j + 1)) (wSeq a b j)).det := by
      have h1 := hdet (j + m)
      have h2 := hdet j
      have htz : (t : ℤ) ^ i ≠ 0 := pow_ne_zero _ (by exact_mod_cast ht)
      exact mul_right_cancel₀ htz (h1.trans h2.symm)
    -- `|det| = c(Φ(X, Y/a)) / |t|^i`.
    have habs : (intHom hC (vSeq a b (j + 1)) (wSeq a b j)).det.natAbs * t.natAbs ^ i =
        clearingDet B.matrix i (1 / (a : ℚ)) := by
      have := congrArg Int.natAbs (hdet j)
      rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_pow, Int.natAbs_neg,
        Int.natAbs_one, one_pow, one_mul, Int.natAbs_natCast] at this
      exact this
    have hdet0 : (intHom hC (vSeq a b (j + 1)) (wSeq a b j)).det ≠ 0 := by
      intro h0
      rw [h0, Int.natAbs_zero, zero_mul] at habs
      omega
    have hN : (((intHom hC (vSeq a b (j + 1)) (wSeq a b j)).det.natAbs : ℕ) : ℤ) ∣ vSeq a b m := by
      have htp : 0 < t.natAbs ^ i := pow_pos (Int.natAbs_pos.mpr (by exact_mod_cast ht)) _
      have : (intHom hC (vSeq a b (j + 1)) (wSeq a b j)).det.natAbs =
          clearingDet B.matrix i (1 / (a : ℚ)) / t.natAbs ^ i := by
        rw [← habs, Nat.mul_div_cancel _ htp]
      rw [this]
      exact (Int.natCast_dvd_natCast.mpr (Nat.dvd_lcm_right _ _)).trans hm
    have hv := (vSeq_modEq a b (j + 1) m).of_dvd hN
    rw [show j + 1 + m = j + m + 1 by ring] at hv
    obtain ⟨G, hG, hGe⟩ := exists_unimodular_transport hC (by rw [hCdet]; exact_mod_cast hd₂.ne')
      (x := vSeq a b (j + 1)) (y := wSeq a b j) (x' := vSeq a b (j + m + 1))
      (y' := wSeq a b (j + m)) (l := l) hdet0 hdet' hv ((wSeq_modEq a b j m).of_dvd hN)
    refine ⟨G, hG, (((b : ℚ) ^ m) ^ i)⁻¹, inv_ne_zero (pow_ne_zero _ (pow_ne_zero _ hb)), ?_⟩
    rw [show 2 * j + 1 + 2 * m = 2 * (j + m) + 1 by ring, evalU_odd hab, evalU_odd hab,
      Matrix.mul_smul, hGe, smul_smul, pow_add, mul_pow, mul_pow, mul_pow]
    congr 1
    field_simp

end TwoPoint
