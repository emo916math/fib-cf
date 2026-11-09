module

public import TwoPoint.IntegralMatrices

/-!
# The integral basis and Lemma `lem:G_integral`

Columns of `Φ_i Γ_i` are integral Padé pairs, where the columns of `Γ_i` form
a basis of the leading-coefficient lattice `Λ_{k,i}`. Evaluated homogeneously
at `(u_(n+1), u_n)`, they give integer matrices `Ũ_i(n) = U_i(n) Γ_i`. When
`Δ_{k,i} ∣ u_m`, homogeneity gives `Ũ_i(n+m) ≡ u_(m+1)^i Ũ_i(n)` modulo
`det Γ_i`, so the quotient `G_i(n,m) = U_i(n+m) U_i(n)⁻¹` lies in `GL₂(ℤ)`.
-/

@[expose] public section
noncomputable section

namespace TwoPoint

open Polynomial

/-! ## Explicit homogeneous evaluation over any commutative ring -/

/-- `∑_{j ≤ d} p_j x^j y^(d-j)`. -/
def homSum {R : Type*} [CommRing R] (p : R[X]) (d : ℕ) (x y : R) : R :=
  ∑ j ∈ Finset.range (d + 1), p.coeff j * x ^ j * y ^ (d - j)

theorem eval_homogenize_eq_homSum {R : Type*} [CommRing R] (p : R[X]) (d : ℕ) (x y : R) :
    MvPolynomial.eval ![x, y] (p.homogenize d) = homSum p d x y := by
  simp only [homogenize, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    MvPolynomial.eval_sum, homSum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [MvPolynomial.eval_monomial, Finsupp.update_eq_add_single, Finsupp.prod_add_index',
    Finsupp.prod_single_index, Finsupp.prod_single_index]
  · simp
    ring
  all_goals simp [pow_add]

theorem homEval_eq_homSum {K : Type*} [Field K] (p : K[X]) (d : ℕ) (x y : K) :
    homEval p d x y = homSum p d x y :=
  eval_homogenize_eq_homSum p d x y

theorem homSum_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (p : R[X])
    (d : ℕ) (x y : R) : homSum (p.map f) d (f x) (f y) = f (homSum p d x y) := by
  simp [homSum, map_sum, coeff_map]

theorem homSum_add {R : Type*} [CommRing R] (p q : R[X]) (d : ℕ) (x y : R) :
    homSum (p + q) d x y = homSum p d x y + homSum q d x y := by
  simp only [homSum, coeff_add, add_mul, Finset.sum_add_distrib]

theorem homSum_mul_C {R : Type*} [CommRing R] (p : R[X]) (c : R) (d : ℕ) (x y : R) :
    homSum (p * C c) d x y = homSum p d x y * c := by
  simp only [homSum, coeff_mul_C, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- Homogeneity modulo `N`. -/
theorem homSum_modEq {N : ℕ} (p : ℤ[X]) (d : ℕ) {x y x' y' c : ℤ}
    (hx : x ≡ c * x' [ZMOD N]) (hy : y ≡ c * y' [ZMOD N]) :
    homSum p d x y ≡ c ^ d * homSum p d x' y' [ZMOD N] := by
  rw [← ZMod.intCast_eq_intCast_iff] at hx hy ⊢
  simp only [homSum, Int.cast_sum, Int.cast_mul, Int.cast_pow, Finset.mul_sum] at hx hy ⊢
  rw [hx, hy]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hc : ((c : ZMod N)) ^ d = (c : ZMod N) ^ j * (c : ZMod N) ^ (d - j) := by
    rw [← pow_add, Nat.add_sub_cancel' hj']
  rw [hc, mul_pow, mul_pow]
  ring

/-! ## Recurrence congruences -/

theorem u_add_modEq (a b : ℤ) (m n : ℕ) :
    u a b (n + m) ≡ u a b (m + 1) * u a b n [ZMOD u a b m] := by
  cases n with
  | zero => simp [Int.ModEq]
  | succ n =>
    rw [show n + 1 + m = m + n + 1 by omega, u_add_succ]
    apply Int.modEq_iff_dvd.mpr
    exact ⟨-(b * u a b n), by ring⟩

/-! ## The integral basis -/

variable {a b : ℤ}

/-- Columns of `Φ_i Γ_i` are integral polynomials. -/
theorem exists_integral_basis {k i : ℕ} (hk : 0 < k) (hi : i ≤ k) (hd : delta a b k i ≠ 0)
    (B : NormalizedPadeBasis (a : ℚ) (b : ℚ) k i) :
    ∃ Γ : Matrix (Fin 2) (Fin 2) ℤ, ∃ Φ : Matrix (Fin 2) (Fin 2) ℤ[X],
      Γ.det ≠ 0 ∧ (Γ.det.natAbs : ℤ) ∣ delta a b k i ∧
      (∀ r c, (Φ r c).map (Int.castRingHom ℚ) =
        ∑ l, B.matrix r l * C ((Γ l c : ℤ) : ℚ)) := by
  obtain ⟨Γ, hΓ0, hΓidx, hΓmem⟩ := exists_padeLeadingLattice_basis a b k i hd
  have hΓdvd : (Γ.det.natAbs : ℤ) ∣ delta a b k i := by
    rw [hΓidx]
    exact Int.natCast_dvd.mpr (padeLeadingLattice_index_dvd a b k i hd)
  have hdQ : deltaOver (a : ℚ) (b : ℚ) k i ≠ 0 := by
    have hm := deltaOver_map (Int.castRingHom ℚ) a b k i
    dsimp at hm
    rw [← hm]
    exact_mod_cast (show deltaOver a b k i ≠ 0 by rw [← delta_eq_deltaOver]; exact hd)
  choose P Q hP hQ hPc hQc hrel using fun c : Fin 2 =>
    exists_integral_padePair_of_mem_lattice a b hk hi (fun r => Γ r c) (hΓmem c)
  refine ⟨Γ, Matrix.of fun r c => ![P c, Q c] r, hΓ0, hΓdvd, ?_⟩
  have hpair (c : Fin 2) : IsPadePair (a : ℚ) (b : ℚ) k i
      ((P c).map (Int.castRingHom ℚ)) ((Q c).map (Int.castRingHom ℚ)) := by
    refine ⟨(degree_map_le).trans (hP c), (degree_map_le).trans (hQ c), ?_⟩
    have := Polynomial.map_dvd (Int.castRingHom ℚ) (hrel c)
    simpa [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
      characteristicPolynomial_map] using this
  intro r c
  obtain ⟨h0, h1⟩ := B.span hi hdQ (hpair c)
  have hp : ((P c).map (Int.castRingHom ℚ)).coeff i = ((Γ 0 c : ℤ) : ℚ) := by
    rw [coeff_map, hPc c]
    rfl
  have hq : ((Q c).map (Int.castRingHom ℚ)).coeff i = ((Γ 1 c : ℤ) : ℚ) := by
    rw [coeff_map, hQc c]
    rfl
  rw [hp, hq] at h0 h1
  fin_cases r
  · simp only [Fin.sum_univ_two, Matrix.of_apply, Fin.zero_eta, Matrix.cons_val_zero]
    simpa [mul_comm] using h0
  · simp only [Fin.sum_univ_two, Matrix.of_apply, Fin.mk_one, Matrix.cons_val_one]
    simpa [mul_comm] using h1

/-- `U_i(n) = Φ_i(u_(n+1), u_n)`. -/
def evalU {k i : ℕ} (B : NormalizedPadeBasis (a : ℚ) (b : ℚ) k i) (n : ℕ) :
    Matrix (Fin 2) (Fin 2) ℚ :=
  homEvalMatrix B.matrix i (u a b (n + 1) : ℚ) (u a b n : ℚ)

theorem evalU_det {k i : ℕ} (B : NormalizedPadeBasis (a : ℚ) (b : ℚ) k i) (n : ℕ) :
    (evalU B n).det = (-(b : ℚ)) ^ (n * i) :=
  B.homEval_recurrence_det a b n

/-- **Lemma `lem:G_integral`.** If `Δ_{k,i} ∣ u_m`, then
`G_i(n,m) = U_i(n+m) U_i(n)⁻¹ ∈ GL₂(ℤ)`. -/
theorem exists_G_integral (hb₁ : b = 1 ∨ b = -1) {k i : ℕ} (hk : 0 < k) (hi : i ≤ k)
    (hd : delta a b k i ≠ 0) (B : NormalizedPadeBasis (a : ℚ) (b : ℚ) k i) {m : ℕ}
    (hm : delta a b k i ∣ u a b m) (n : ℕ) :
    ∃ G : Matrix (Fin 2) (Fin 2) ℤ, IsUnit G ∧
      intMatrixCast 2 G = evalU B (n + m) * (evalU B n)⁻¹ := by
  obtain ⟨Γ, Φ, hΓ0, hΓdvd, hΦ⟩ := exists_integral_basis hk hi hd B
  let Ut : ℕ → Matrix (Fin 2) (Fin 2) ℤ := fun n =>
    Matrix.of fun r c => homSum (Φ r c) i (u a b (n + 1)) (u a b n)
  have hcast (n : ℕ) : intMatrixCast 2 (Ut n) = evalU B n * intMatrixCast 2 Γ := by
    ext r c
    simp only [intMatrixCast, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Ut,
      evalU, Matrix.mul_apply, homEvalMatrix, Fin.sum_univ_two]
    rw [← homSum_map, hΦ r c, Fin.sum_univ_two, homSum_add, homSum_mul_C, homSum_mul_C,
      homEval_eq_homSum, homEval_eq_homSum]
    rfl
  have hb : IsUnit (-b) := by rcases hb₁ with h | h <;> simp [h]
  have hdet (n : ℕ) : (Ut n).det = (-b) ^ (n * i) * Γ.det := by
    have h := congrArg Matrix.det (hcast n)
    rw [intMatrixCast_det, Matrix.det_mul, intMatrixCast_det, evalU_det] at h
    exact_mod_cast h
  have hX : (Ut n).det ≠ 0 := by
    rw [hdet]
    exact mul_ne_zero (hb.pow _).ne_zero hΓ0
  have hcong : ∀ r s, (Ut n).det ∣ Ut (n + m) r s - u a b (m + 1) ^ i * Ut n r s := by
    intro r s
    rw [hdet]
    apply (hb.pow _).mul_left_dvd.mpr
    have hN : (Γ.det.natAbs : ℤ) ∣ u a b m := hΓdvd.trans hm
    have hx : u a b (n + m + 1) ≡ u a b (m + 1) * u a b (n + 1) [ZMOD Γ.det.natAbs] := by
      rw [show n + m + 1 = (n + 1) + m by omega]
      exact (u_add_modEq a b m (n + 1)).of_dvd hN
    have hy : u a b (n + m) ≡ u a b (m + 1) * u a b n [ZMOD Γ.det.natAbs] :=
      (u_add_modEq a b m n).of_dvd hN
    have := (homSum_modEq (Φ r s) i hx hy).symm
    rw [← Int.natAbs_dvd]
    exact (Int.modEq_iff_dvd.mp this)
  obtain ⟨G, hGu, hG⟩ := intMatrix_quotient_isUnit (Ut n) (Ut (n + m)) (u a b (m + 1) ^ i)
    ((-b) ^ (m * i)) hX (hb.pow _) (by rw [hdet, hdet]; ring) hcong
  refine ⟨G, hGu, ?_⟩
  have hΓu : IsUnit (intMatrixCast 2 Γ).det := by
    rw [intMatrixCast_det]
    exact isUnit_iff_ne_zero.mpr (by exact_mod_cast hΓ0)
  rw [hG, hcast, hcast, Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ (evalU B n)⁻¹,
    Matrix.mul_nonsing_inv _ hΓu, Matrix.one_mul]

end TwoPoint
