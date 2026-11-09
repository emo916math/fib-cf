module

public import TwoPoint.Setup

/-!
# Exercise `exer:invisible`: the determinant `Υ_{k,i}(α)`

Let `β_j` be the coefficients of
`(x - α)^(i+1) (x - ᾱ)^(i-1) = h(x)^(i-1) (x - α)^2 = β_0 x^(2i) + ⋯ + β_(2i)`, and
`Υ_{k,i}(α) = det [β_(i+s-r)]` (a `(k-i) × (k-i)` Toeplitz determinant, built as
`Δ_{k,i}` is from `h^i`). For `0 < i < k`,

  `Υ_{k,i}(α) = 0  ⟺  ξ_i = ξ_(i-1)`,

that is, the transition matrices `T_(i-1)` and `T_i` share their eigenvector for
the eigenvalue `α`. The proof works in the real Padé spaces `V_{k,j}(ℝ)` for
`j = i-1, i, i+1`, which are spanned by the columns of `Φ_j`, with
`Φ_(j+1) = Φ_j ((x - a) I + T_j)`:

* if `T_(i-1) w = T_i w = α w`, then `Φ_(i+1) w = (x - ᾱ)^2 Φ_(i-1) w`, and the Padé
  condition at level `i+1` gives the double extra contact of `Φ_(i-1) w`;
* conversely, a pair `(P, Q) = Φ_(i-1) w` of degree `< i` with this contact gives
  `(x - ᾱ)(P, Q) ∈ V_{k,i}` and `(x - ᾱ)^2 (P, Q) ∈ V_{k,i+1}`, which forces
  `T_(i-1) w = α w` and `T_i w = α w`.
-/

@[expose] public section
noncomputable section

namespace TwoPoint

open Polynomial

/-! ## The determinant -/

/-- `h(x)^(i-1) (x - α)^2 = (x - α)^(i+1) (x - ᾱ)^(i-1)` over `ℝ`. -/
def invisibleContact (a b : ℤ) (i : ℕ) : ℝ[X] :=
  characteristicPolynomial (a : ℝ) (b : ℝ) ^ (i - 1) * (X - C (alpha a b)) ^ 2

/-- `β_j`, the coefficient of `x^(2i-j)` in `invisibleContact`; zero unless `0 ≤ j ≤ 2i`. -/
def upsilonBeta (a b : ℤ) (i : ℕ) (j : ℤ) : ℝ :=
  if 0 ≤ j ∧ j ≤ 2 * (i : ℤ) then (invisibleContact a b i).coeff (2 * (i : ℤ) - j).toNat else 0

/-- `Υ_{k,i}(α)`: the `(k-i) × (k-i)` determinant with entry `β_(i+s-r)` in row `r`, column `s`. -/
def upsilon (a b : ℤ) (k i : ℕ) : ℝ :=
  Matrix.det (fun r s : Fin (k - i) => upsilonBeta a b i ((i : ℤ) + (s.val : ℤ) - (r.val : ℤ)))

theorem invisibleContact_natDegree (a b : ℤ) {i : ℕ} (hi : 1 ≤ i) :
    (invisibleContact a b i).natDegree = 2 * i := by
  have hm : (invisibleContact a b i).Monic :=
    ((characteristicPolynomial_monic _ _).pow _).mul ((monic_X_sub_C _).pow _)
  rw [invisibleContact, natDegree_mul' (by rw [((characteristicPolynomial_monic _ _).pow _).leadingCoeff,
      ((monic_X_sub_C _).pow _).leadingCoeff]; norm_num),
    natDegree_pow, characteristicPolynomial_natDegree, natDegree_pow, natDegree_X_sub_C]
  omega

theorem upsilon_eq_det_toeplitzOf (a b : ℤ) (k : ℕ) {i : ℕ} (hi : 1 ≤ i) :
    upsilon a b k i = (toeplitzOf (invisibleContact a b i) k i).det := by
  unfold upsilon
  congr 1
  ext r s
  have hdeg := invisibleContact_natDegree a b hi
  unfold upsilonBeta toeplitzOf
  by_cases hs : s.val ≤ i + r.val
  · rw [if_pos hs]
    by_cases hj : 0 ≤ (i : ℤ) + (s.val : ℤ) - (r.val : ℤ)
    · rw [if_pos ⟨hj, by omega⟩]
      congr 1
      omega
    · rw [if_neg (by omega)]
      symm
      apply coeff_eq_zero_of_natDegree_lt
      omega
  · rw [if_neg hs, if_neg (by omega)]

/-! ## Real Padé bases -/

/-- A normalized Padé basis maps to a normalized Padé basis under a field map. -/
def NormalizedPadeBasis.map {K L : Type*} [Field K] [Field L] (f : K →+* L) {a b : K}
    {a' b' : L} (ha : f a = a') (hb : f b = b') {k i : ℕ}
    (B : NormalizedPadeBasis a b k i) : NormalizedPadeBasis a' b' k i where
  matrix := B.matrix.map (Polynomial.map f)
  isPade c := by
    refine ⟨(degree_map_le).trans (B.isPade c).degree_num,
      (degree_map_le).trans (B.isPade c).degree_den, ?_⟩
    have := Polynomial.map_dvd f (B.isPade c).relation
    simpa [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
      characteristicPolynomial_map, ha, hb] using this
  coeff_matrix r c := by
    simp only [Matrix.map_apply, coeff_map, B.coeff_matrix]
    fin_cases r <;> fin_cases c <;> simp

theorem linearFactor_map {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (M : Matrix (Fin 2) (Fin 2) K) :
    (linearFactor M).map (Polynomial.map f) = linearFactor (M.map f) := by
  ext r c
  fin_cases r <;> fin_cases c <;> simp [linearFactor, Matrix.one_apply]

theorem linearFactor_mulVec_C (M : Matrix (Fin 2) (Fin 2) ℝ) (w : Fin 2 → ℝ) :
    (linearFactor M).mulVec (fun j => C (w j)) =
      (X : ℝ[X]) • (fun j => C (w j)) + fun j => C (M.mulVec w j) := by
  ext j
  fin_cases j <;>
    simp [linearFactor, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply] <;> ring

namespace Ctx

variable (C : Ctx)

/-- `Φ_j(x, 1)` over `ℝ`. -/
def PhiR (j : ℕ) (hj : j ≤ C.k) : NormalizedPadeBasis (C.a : ℝ) (C.b : ℝ) C.k j :=
  (C.S.basis j hj).map (Rat.castHom ℝ) (by simp) (by simp)

theorem PhiR_matrix (j : ℕ) (hj : j ≤ C.k) :
    (C.PhiR j hj).matrix = (C.S.basis j hj).matrix.map (Polynomial.map (Rat.castHom ℝ)) := rfl

theorem deltaR_ne_zero {j : ℕ} (hj : j ≤ C.k) : deltaOver (C.a : ℝ) (C.b : ℝ) C.k j ≠ 0 := by
  have hm := deltaOver_map (Int.castRingHom ℝ) C.a C.b C.k j
  simp only [eq_intCast] at hm
  rw [← hm]
  exact_mod_cast (show deltaOver C.a C.b C.k j ≠ 0 by rw [← delta_eq_deltaOver]; exact C.hd j hj)

/-- `Φ_(j+1) = Φ_j ((x - a) I + T_j)` over `ℝ`. -/
theorem PhiR_step {j : ℕ} (hj : j < C.k) :
    (C.PhiR (j + 1) hj).matrix =
      (C.PhiR j hj.le).matrix * linearFactor (ratToReal (C.T j) - (C.a : ℝ) • 1) := by
  have hf := (C.S.basis j hj.le).step_factorization hj.le (C.hdQ j hj.le) (C.S.basis (j + 1) hj)
  have hT : C.T j = (C.S.basis j hj.le).transitionMatrix (C.S.basis (j + 1) hj) := by
    simp [T, PadeBasisChain.transition, hj]
  rw [transitionMatrix_eq_step, ← hT] at hf
  rw [PhiR_matrix, PhiR_matrix, hf]
  have hm := Matrix.map_mul (L := (C.S.basis j hj.le).matrix)
    (M := linearFactor (C.T j - (C.a : ℚ) • 1)) (f := Polynomial.mapRingHom (Rat.castHom ℝ))
  simp only [Polynomial.coe_mapRingHom] at hm
  rw [hm, linearFactor_map]
  congr 2
  ext r c
  fin_cases r <;> fin_cases c <;> simp [ratToReal, Matrix.one_apply]

theorem PhiR_mulVec_step {j : ℕ} (hj : j < C.k) (w : Fin 2 → ℝ) :
    (C.PhiR (j + 1) hj).matrix.mulVec (fun r => Polynomial.C (w r)) =
      (C.PhiR j hj.le).matrix.mulVec ((X : ℝ[X]) • (fun r => Polynomial.C (w r)) +
        fun r => Polynomial.C ((ratToReal (C.T j) - (C.a : ℝ) • 1).mulVec w r)) := by
  rw [C.PhiR_step hj, ← Matrix.mulVec_mulVec, linearFactor_mulVec_C]

/-- On an `α`-eigenvector `w` of `T_j`, `Φ_(j+1) w = (x - ᾱ) Φ_j w`. -/
theorem PhiR_mulVec_eigen {j : ℕ} (hj : j < C.k) {w : Fin 2 → ℝ}
    (hw : (ratToReal (C.T j)).mulVec w = alpha C.a C.b • w) :
    (C.PhiR (j + 1) hj).matrix.mulVec (fun r => Polynomial.C (w r)) =
      (X - Polynomial.C (beta C.a C.b)) • (C.PhiR j hj.le).matrix.mulVec
        (fun r => Polynomial.C (w r)) := by
  rw [C.PhiR_mulVec_step hj, ← Matrix.mulVec_smul]
  congr 1
  have hM : (ratToReal (C.T j) - (C.a : ℝ) • 1).mulVec w = (-beta C.a C.b) • w := by
    rw [Matrix.sub_mulVec, hw, Matrix.smul_mulVec, Matrix.one_mulVec, ← sub_smul]
    congr 1
    simp only [beta]
    ring
  rw [hM]
  ext r
  simp [Polynomial.C_mul]
  ring

theorem PhiR_det_ne_zero (j : ℕ) (hj : j ≤ C.k) : (C.PhiR j hj).matrix.det ≠ 0 := by
  rw [(C.PhiR j hj).det]
  exact pow_ne_zero _ (characteristicPolynomial_monic _ _).ne_zero

theorem PhiR_mulVec_eq_zero (j : ℕ) (hj : j ≤ C.k) {v : Fin 2 → ℝ[X]}
    (h : (C.PhiR j hj).matrix.mulVec v = 0) : v = 0 :=
  Matrix.eq_zero_of_mulVec_eq_zero (C.PhiR_det_ne_zero j hj) h

/-- Columns combinations of `Φ_j` are Padé pairs. -/
theorem isPade_PhiR_mulVec (j : ℕ) (hj : j ≤ C.k) (w : Fin 2 → ℝ) :
    IsPadePair (C.a : ℝ) (C.b : ℝ) C.k j
      ((C.PhiR j hj).matrix.mulVec (fun r => Polynomial.C (w r)) 0)
      ((C.PhiR j hj).matrix.mulVec (fun r => Polynomial.C (w r)) 1) := by
  have h := (((C.PhiR j hj).isPade 0).const_mul (w 0)).add (((C.PhiR j hj).isPade 1).const_mul (w 1))
  convert h using 1 <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]

/-- Every real Padé pair is a combination of the columns of `Φ_j`. -/
theorem PhiR_span (j : ℕ) (hj : j ≤ C.k) {P Q : ℝ[X]}
    (h : IsPadePair (C.a : ℝ) (C.b : ℝ) C.k j P Q) :
    ![P, Q] = (C.PhiR j hj).matrix.mulVec (fun r => Polynomial.C (![P.coeff j, Q.coeff j] r)) := by
  obtain ⟨h0, h1⟩ := (C.PhiR j hj).span hj (C.deltaR_ne_zero hj) h
  funext r
  fin_cases r
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    conv_lhs => simp only [Fin.zero_eta, Matrix.cons_val_zero]; rw [h0]
    simp
    ring
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    conv_lhs => simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]; rw [h1]
    simp
    ring

end Ctx

/-! ## Auxiliary facts -/

theorem charpoly_real_factor (hab : GenAdmissible a b) :
    characteristicPolynomial (a : ℝ) (b : ℝ) =
      (X - Polynomial.C (alpha a b)) * (X - Polynomial.C (beta a b)) := by
  have h1 := alpha_add_beta a b
  have h2 := alpha_mul_beta hab
  simp only [characteristicPolynomial]
  have e1 : Polynomial.C (a : ℝ) = Polynomial.C (alpha a b) + Polynomial.C (beta a b) := by
    rw [← Polynomial.C_add, h1]
  have e2 : Polynomial.C (b : ℝ) = -(Polynomial.C (alpha a b) * Polynomial.C (beta a b)) := by
    rw [← Polynomial.C_mul, h2, Polynomial.C_neg, neg_neg]
  rw [e1, e2]
  ring

theorem coeff_X_sub_C_mul_succ (c : ℝ) {p : ℝ[X]} {n : ℕ} (hp : p.natDegree ≤ n) :
    ((X - Polynomial.C c) * p).coeff (n + 1) = p.coeff n := by
  rw [sub_mul, coeff_sub, coeff_X_mul, coeff_C_mul,
    coeff_eq_zero_of_natDegree_lt (show p.natDegree < n + 1 by omega), mul_zero, sub_zero]

/-- The eigenvector slope from any eigenvector. -/
theorem eigSlope_eq_of_mulVec (T : Matrix (Fin 2) (Fin 2) ℚ) (h10 : T 1 0 ≠ 0) {ρ : ℝ}
    {w : Fin 2 → ℝ} (hw : w ≠ 0) (h : (ratToReal T).mulVec w = ρ • w) :
    w 1 ≠ 0 ∧ eigSlope T ρ = w 0 / w 1 := by
  have h1 := congrFun h 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, ratToReal] at h1
  have h10' : (T 1 0 : ℝ) ≠ 0 := by exact_mod_cast h10
  have hw1 : w 1 ≠ 0 := by
    intro h0
    rw [h0] at h1
    simp only [mul_zero, add_zero] at h1
    have : w 0 = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h h10'
      · exact h
    apply hw
    ext j
    fin_cases j <;> simp [this, h0]
  refine ⟨hw1, ?_⟩
  rw [eigSlope, div_eq_div_iff h10' hw1]
  linarith

namespace Ctx

variable (C : Ctx)

/-- If `Φ_(j+1) w = (x - ᾱ) Φ_j w`, then `w` is an `α`-eigenvector of `T_j`. -/
theorem eigen_of_shift {j : ℕ} (hj : j < C.k) (w : Fin 2 → ℝ)
    (h : (C.PhiR (j + 1) hj).matrix.mulVec (fun r => Polynomial.C (w r)) =
      (X - Polynomial.C (beta C.a C.b)) • (C.PhiR j hj.le).matrix.mulVec
        (fun r => Polynomial.C (w r))) :
    (ratToReal (C.T j)).mulVec w = alpha C.a C.b • w := by
  rw [C.PhiR_mulVec_step hj, ← Matrix.mulVec_smul, ← sub_eq_zero, ← Matrix.mulVec_sub] at h
  have h0 := C.PhiR_mulVec_eq_zero j hj.le h
  ext r
  have hr := congrFun h0 r
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hr
  have hc : Polynomial.C ((ratToReal (C.T j) - (C.a : ℝ) • 1).mulVec w r + beta C.a C.b * w r) = 0 := by
    rw [Polynomial.C_add, Polynomial.C_mul]
    linear_combination hr
  have := Polynomial.C_eq_zero.mp hc
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at this
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
  simp only [Pi.smul_apply, smul_eq_mul]
  have hab := alpha_add_beta C.a C.b
  linear_combination this - w r * hab

theorem degree_PhiR_mulVec_lt (j : ℕ) (hj : j ≤ C.k) (w : Fin 2 → ℝ) (r : Fin 2) :
    ((C.PhiR j hj).matrix.mulVec (fun r => Polynomial.C (w r)) r).degree < (j + 1 : ℕ) := by
  have h := C.isPade_PhiR_mulVec j hj w
  have hlt : ((j : ℕ) : WithBot ℕ) < ((j + 1 : ℕ) : WithBot ℕ) := by
    exact_mod_cast Nat.lt_succ_self j
  fin_cases r
  · exact lt_of_le_of_lt h.degree_num hlt
  · exact lt_of_le_of_lt h.degree_den hlt

/-- **Exercise `exer:invisible`, algebraic part (⇐).** -/
theorem upsilon_eq_zero_of_xi_eq {i : ℕ} (hi0 : 0 < i) (hik : i < C.k)
    (h : C.xi i = C.xi (i - 1)) : upsilon C.a C.b C.k i = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [Nat.add_sub_cancel] at h
  have hj : j < C.k := by omega
  set w : Fin 2 → ℝ := ![C.xi j, 1]
  have hw1 := C.T_mulVec_xi hj
  have hw2 := C.T_mulVec_xi hik
  rw [h] at hw2
  set β := beta C.a C.b
  set V := (C.PhiR j hj.le).matrix.mulVec (fun r => Polynomial.C (w r))
  have e1 := C.PhiR_mulVec_eigen hj hw1
  have e2 := C.PhiR_mulVec_eigen hik hw2
  rw [e1, smul_smul] at e2
  -- The Padé condition at level `j + 2`.
  have hpade := (C.isPade_PhiR_mulVec (j + 2) hik w).relation
  rw [e2] at hpade
  simp only [Pi.smul_apply, smul_eq_mul] at hpade
  have hG : characteristicPolynomial (C.a : ℝ) (C.b : ℝ) ^ (j + 2) =
      ((X - Polynomial.C β) * (X - Polynomial.C β)) * invisibleContact C.a C.b (j + 1) := by
    rw [invisibleContact, Nat.add_sub_cancel, charpoly_real_factor C.hab]
    ring
  rw [hG, show X ^ C.k * ((X - Polynomial.C β) * (X - Polynomial.C β) * V 1) -
      (X - Polynomial.C β) * (X - Polynomial.C β) * V 0 =
      ((X - Polynomial.C β) * (X - Polynomial.C β)) * (X ^ C.k * V 1 - V 0) by ring] at hpade
  have hne : (X - Polynomial.C β) * (X - Polynomial.C β) ≠ 0 :=
    mul_ne_zero (X_sub_C_ne_zero β) (X_sub_C_ne_zero β)
  obtain ⟨E, hE⟩ := (mul_dvd_mul_iff_left hne).mp hpade
  -- `X^k V₁ - V₀ ≠ 0`.
  have hdeg0 := C.degree_PhiR_mulVec_lt j hj.le w 0
  have hdeg1 := C.degree_PhiR_mulVec_lt j hj.le w 1
  have hF : X ^ C.k * V 1 - V 0 ≠ 0 := by
    intro h0
    have hV1 : V 1 = 0 := by
      ext n
      have := congrArg (fun p => p.coeff (C.k + n)) h0
      simp only [coeff_sub, coeff_X_pow_mul', coeff_zero] at this
      rw [if_pos (by omega), Nat.add_sub_cancel_left,
        coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hdeg0 (by exact_mod_cast (by omega : j + 1 ≤ C.k + n))),
        sub_zero] at this
      simpa using this
    have hV0 : V 0 = 0 := by rw [hV1, mul_zero, zero_sub, neg_eq_zero] at h0; exact h0
    have hV : V = 0 := by ext r; fin_cases r <;> simp [hV0, hV1]
    have := congrFun (C.PhiR_mulVec_eq_zero j hj.le hV) 1
    simp [w] at this
  have hE0 : E ≠ 0 := by rintro rfl; rw [mul_zero] at hE; exact hF hE
  rw [upsilon_eq_det_toeplitzOf _ _ _ (by omega)]
  refine (det_toeplitzOf_eq_zero_iff_exists_pade _
    (invisibleContact_natDegree C.a C.b (by omega)).le).mpr ⟨V 0, V 1, E, hE0, hdeg0, hdeg1, ?_, ?_⟩
  · -- degree bound for `E`
    have hGn := invisibleContact_natDegree C.a C.b (i := j + 1) (by omega)
    have hGm : invisibleContact C.a C.b (j + 1) ≠ 0 := by
      intro h0; rw [h0, natDegree_zero] at hGn; omega
    have hnat : (invisibleContact C.a C.b (j + 1) * E).natDegree ≤ C.k + j := by
      rw [← hE]
      apply (natDegree_sub_le _ _).trans
      apply max_le
      · apply (natDegree_mul_le).trans
        rw [natDegree_X_pow]
        have := natDegree_le_of_degree_lt_succ (by exact_mod_cast hdeg1 : (V 1).degree < ↑(j + 1))
        omega
      · have := natDegree_le_of_degree_lt_succ (by exact_mod_cast hdeg0 : (V 0).degree < ↑(j + 1))
        omega
    rw [natDegree_mul hGm hE0, hGn] at hnat
    exact (degree_le_natDegree).trans_lt (by exact_mod_cast (by omega : E.natDegree < C.k - (j + 1)))
  · rw [hE]
    ring

/-- **Exercise `exer:invisible`, algebraic part (⇒).** -/
theorem xi_eq_of_upsilon_eq_zero {i : ℕ} (hi0 : 0 < i) (hik : i < C.k)
    (h : upsilon C.a C.b C.k i = 0) : C.xi i = C.xi (i - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hj : j < C.k := by omega
  rw [upsilon_eq_det_toeplitzOf _ _ _ (by omega)] at h
  obtain ⟨P, Q, E, hE, hP, hQ, -, hrel⟩ := (det_toeplitzOf_eq_zero_iff_exists_pade _
    (invisibleContact_natDegree C.a C.b (by omega)).le).mp h
  set β := beta C.a C.b
  set Xβ : ℝ[X] := X - Polynomial.C β
  set G := invisibleContact C.a C.b (j + 1)
  have hPn : P.natDegree ≤ j := natDegree_le_of_degree_lt_succ (by exact_mod_cast hP)
  have hQn : Q.natDegree ≤ j := natDegree_le_of_degree_lt_succ (by exact_mod_cast hQ)
  have hGh : G = characteristicPolynomial (C.a : ℝ) (C.b : ℝ) ^ j *
      (X - Polynomial.C (alpha C.a C.b)) ^ 2 := by
    simp [G, invisibleContact]
  have hfac := charpoly_real_factor C.hab
  -- Level `j`.
  have hpj : IsPadePair (C.a : ℝ) (C.b : ℝ) C.k j P Q :=
    ⟨degree_le_of_natDegree_le hPn, degree_le_of_natDegree_le hQn,
      ⟨E * (X - Polynomial.C (alpha C.a C.b)) ^ 2, by rw [hrel, hGh]; ring⟩⟩
  set w : Fin 2 → ℝ := ![P.coeff j, Q.coeff j]
  have sj := C.PhiR_span j hj.le hpj
  -- Level `j + 1`.
  have hP1 : (Xβ * P).natDegree ≤ j + 1 :=
    (natDegree_mul_le).trans (by rw [natDegree_X_sub_C]; omega)
  have hQ1 : (Xβ * Q).natDegree ≤ j + 1 :=
    (natDegree_mul_le).trans (by rw [natDegree_X_sub_C]; omega)
  have hpj1 : IsPadePair (C.a : ℝ) (C.b : ℝ) C.k (j + 1) (Xβ * P) (Xβ * Q) :=
    ⟨degree_le_of_natDegree_le hP1, degree_le_of_natDegree_le hQ1,
      ⟨E * (X - Polynomial.C (alpha C.a C.b)), by
        rw [show X ^ C.k * (Xβ * Q) - Xβ * P = Xβ * (X ^ C.k * Q - P) by ring, hrel, hGh, hfac]
        simp only [Xβ]
        ring⟩⟩
  have sj1 := C.PhiR_span (j + 1) hik.le hpj1
  have hc1 : ![(Xβ * P).coeff (j + 1), (Xβ * Q).coeff (j + 1)] = w := by
    simp only [Xβ, coeff_X_sub_C_mul_succ _ hPn, coeff_X_sub_C_mul_succ _ hQn, w]
  rw [hc1] at sj1
  have hsh1 : (C.PhiR (j + 1) hik.le).matrix.mulVec (fun r => Polynomial.C (w r)) =
      Xβ • (C.PhiR j hj.le).matrix.mulVec (fun r => Polynomial.C (w r)) := by
    rw [← sj1, ← sj]
    ext r
    fin_cases r <;> rfl
  have eig1 := C.eigen_of_shift hj w hsh1
  -- Level `j + 2`.
  have hP2 : (Xβ * (Xβ * P)).natDegree ≤ j + 2 :=
    (natDegree_mul_le).trans (by rw [natDegree_X_sub_C]; omega)
  have hQ2 : (Xβ * (Xβ * Q)).natDegree ≤ j + 2 :=
    (natDegree_mul_le).trans (by rw [natDegree_X_sub_C]; omega)
  have hik2 : j + 1 + 1 ≤ C.k := by omega
  have hpj2 : IsPadePair (C.a : ℝ) (C.b : ℝ) C.k (j + 1 + 1) (Xβ * (Xβ * P)) (Xβ * (Xβ * Q)) :=
    ⟨degree_le_of_natDegree_le hP2, degree_le_of_natDegree_le hQ2,
      ⟨E, by
        rw [show X ^ C.k * (Xβ * (Xβ * Q)) - Xβ * (Xβ * P) = Xβ * Xβ * (X ^ C.k * Q - P) by ring,
          hrel, hGh, hfac]
        simp only [Xβ]
        ring⟩⟩
  have sj2 := C.PhiR_span (j + 1 + 1) hik2 hpj2
  have hc2 : ![(Xβ * (Xβ * P)).coeff (j + 1 + 1), (Xβ * (Xβ * Q)).coeff (j + 1 + 1)] = w := by
    simp only [Xβ, coeff_X_sub_C_mul_succ _ hP1, coeff_X_sub_C_mul_succ _ hQ1,
      coeff_X_sub_C_mul_succ _ hPn, coeff_X_sub_C_mul_succ _ hQn, w]
  rw [hc2] at sj2
  have hsh2 : (C.PhiR (j + 1 + 1) hik2).matrix.mulVec (fun r => Polynomial.C (w r)) =
      Xβ • (C.PhiR (j + 1) hik.le).matrix.mulVec (fun r => Polynomial.C (w r)) := by
    rw [← sj2, ← sj1]
    ext r
    fin_cases r <;> rfl
  have eig2 := C.eigen_of_shift (j := j + 1) (by omega) w hsh2
  -- `w ≠ 0`.
  have hw : w ≠ 0 := by
    intro h0
    have hPQ : ![P, Q] = (C.PhiR j hj.le).matrix.mulVec (fun r => Polynomial.C (w r)) := sj
    rw [h0] at hPQ
    have hz : (fun r : Fin 2 => Polynomial.C ((0 : Fin 2 → ℝ) r)) = 0 := by
      funext r; simp
    rw [hz, Matrix.mulVec_zero] at hPQ
    have hP0 : P = 0 := by simpa using congrFun hPQ 0
    have hQ0 : Q = 0 := by simpa using congrFun hPQ 1
    rw [hP0, hQ0, mul_zero, sub_zero] at hrel
    have hGne : G ≠ 0 := by
      intro h0
      have := invisibleContact_natDegree C.a C.b (i := j + 1) (by omega)
      simp only [G] at h0
      rw [h0, natDegree_zero] at this
      omega
    exact hE ((mul_eq_zero.mp hrel.symm).resolve_right hGne)
  obtain ⟨-, s1⟩ := eigSlope_eq_of_mulVec _ (chain_transition_facts C.hab C.S C.hdQ hj).2 hw eig1
  obtain ⟨-, s2⟩ := eigSlope_eq_of_mulVec _ (chain_transition_facts C.hab C.S C.hdQ hik).2 hw eig2
  simp only [xi, T] at s1 s2 ⊢
  rw [s1, s2]

/-- **Exercise `exer:invisible`, algebraic part.** For `0 < i < k`,
`Υ_{k,i}(α) = 0` if and only if `T_(i-1)` and `T_i` share the `α`-eigenvector. -/
theorem upsilon_eq_zero_iff {i : ℕ} (hi0 : 0 < i) (hik : i < C.k) :
    upsilon C.a C.b C.k i = 0 ↔ C.xi i = C.xi (i - 1) :=
  ⟨C.xi_eq_of_upsilon_eq_zero hi0 hik, C.upsilon_eq_zero_of_xi_eq hi0 hik⟩

end Ctx

end TwoPoint
