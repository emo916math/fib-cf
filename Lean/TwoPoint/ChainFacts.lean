module

public import TwoPoint.Eigen

/-!
# Two facts about the chain of transition matrices

* **Nondegenerate junctions.** `ξ_(j+1) ≠ ξ'_j`. Otherwise `T_j = a - T_(j+1)`,
  so `Φ_(j+2) = h Φ_j`, and the columns of `Φ_j` would be Padé pairs of degree
  below `j + 1` with contact order `j + 1`, contradicting `Δ_{k,j+1} ≠ 0`.
* **The last transition.** The lower-left entry of `T_(k-1)` is `1/c` for a
  nonzero integer `c` (a coefficient of `h^(k-1)`), so `ξ_(k-1) - ξ'_(k-1)` is
  an integer multiple of `α - β`.
-/

@[expose] public section
noncomputable section

namespace TwoPoint

open Polynomial

variable {K : Type*} [Field K]

theorem transitionMatrix_eq_step {a b : K} {k i : ℕ} (B : NormalizedPadeBasis a b k i)
    (B' : NormalizedPadeBasis a b k (i + 1)) :
    B.stepMatrix B' = B.transitionMatrix B' - a • 1 := by
  simp [NormalizedPadeBasis.transitionMatrix]

/-- `(X - T)(X - a + T) = h` when `T² = aT + b`. -/
theorem linearFactor_neg_mul (a b : K) (T : Matrix (Fin 2) (Fin 2) K)
    (hT : T * T = a • T + b • 1) :
    linearFactor (-T) * linearFactor (T - a • 1) = (characteristicPolynomial a b) • 1 := by
  have e00 : T 0 0 * T 0 0 + T 0 1 * T 1 0 = a * T 0 0 + b := by
    have := congrFun (congrFun hT 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have e01 : T 0 0 * T 0 1 + T 0 1 * T 1 1 = a * T 0 1 := by
    have := congrFun (congrFun hT 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have e10 : T 1 0 * T 0 0 + T 1 1 * T 1 0 = a * T 1 0 := by
    have := congrFun (congrFun hT 1) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have e11 : T 1 0 * T 0 1 + T 1 1 * T 1 1 = a * T 1 1 + b := by
    have := congrFun (congrFun hT 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have c00 := congrArg C e00
  have c01 := congrArg C e01
  have c10 := congrArg C e10
  have c11 := congrArg C e11
  simp only [C_mul, C_add] at c00 c01 c10 c11
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp only [linearFactor, Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, Matrix.neg_apply, Matrix.sub_apply,
      characteristicPolynomial, Fin.zero_eta, Fin.mk_one, Matrix.one_apply_eq,
      Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), map_neg, map_sub, map_zero,
      mul_one, mul_zero, zero_add]
  · linear_combination (-1 : K[X]) * c00
  · linear_combination (-1 : K[X]) * c01
  · linear_combination (-1 : K[X]) * c10
  · linear_combination (-1 : K[X]) * c11

/-- Two real matrices agreeing on two independent vectors `(x, 1)`, `(x', 1)` coincide. -/
theorem matrix_eq_of_mulVec {A B : Matrix (Fin 2) (Fin 2) ℝ} {x x' : ℝ} (hx : x ≠ x')
    (h1 : A.mulVec ![x, 1] = B.mulVec ![x, 1]) (h2 : A.mulVec ![x', 1] = B.mulVec ![x', 1]) :
    A = B := by
  have e (v : Fin 2 → ℝ) (h : A.mulVec v = B.mulVec v) (i : Fin 2) :=
    congrFun h i
  have hsub : x - x' ≠ 0 := sub_ne_zero.mpr hx
  ext i j
  have a1 := e _ h1 i
  have a2 := e _ h2 i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at a1 a2
  have hc : A i 0 = B i 0 := by
    have : (A i 0 - B i 0) * (x - x') = 0 := by linear_combination a1 - a2
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hsub)
  fin_cases j
  · exact hc
  · simp only [Fin.mk_one]
    rw [hc] at a1
    linarith

variable {a b : ℤ}

/-- Data for the eigenvectors of a transition matrix of a chain. -/
theorem chain_transition_facts (hab : GenAdmissible a b) {k : ℕ}
    (S : PadeBasisChain (a : ℚ) (b : ℚ) k)
    (hd : ∀ i, i ≤ k → deltaOver (a : ℚ) (b : ℚ) k i ≠ 0) {i : ℕ} (hi : i < k) :
    S.transition i * S.transition i = (a : ℚ) • S.transition i + (b : ℚ) • 1 ∧
      S.transition i 1 0 ≠ 0 := by
  have hq := matrix_quadratic_of_charpoly (a : ℚ) (b : ℚ) _ (S.transition_charpoly hd hi)
  exact ⟨hq, lower_ne_zero_of_quadratic hab _ hq⟩

theorem chain_eigSlope_mulVec (hab : GenAdmissible a b) {k : ℕ}
    (S : PadeBasisChain (a : ℚ) (b : ℚ) k)
    (hd : ∀ i, i ≤ k → deltaOver (a : ℚ) (b : ℚ) k i ≠ 0) {i : ℕ} (hi : i < k)
    {ρ : ℝ} (hρ : ρ ^ 2 = a * ρ + b) :
    (ratToReal (S.transition i)).mulVec ![eigSlope (S.transition i) ρ, 1] =
      ρ • ![eigSlope (S.transition i) ρ, 1] := by
  obtain ⟨hq, h10⟩ := chain_transition_facts hab S hd hi
  obtain ⟨htr, hdet⟩ := quadratic_entries _ hq h10
  exact eigSlope_mulVec _ h10 (by exact_mod_cast htr) (by exact_mod_cast hdet) hρ

/-- **Nondegenerate junctions:** `ξ_(j+1) ≠ ξ'_j`. -/
theorem chain_xi_ne_xi'_prev (hab : GenAdmissible a b) {k : ℕ}
    (S : PadeBasisChain (a : ℚ) (b : ℚ) k)
    (hd : ∀ i, i ≤ k → deltaOver (a : ℚ) (b : ℚ) k i ≠ 0) {j : ℕ} (hj : j + 1 < k) :
    eigSlope (S.transition (j + 1)) (alpha a b) ≠ eigSlope (S.transition j) (beta a b) := by
  intro heq
  set T := S.transition (j + 1)
  set T₀ := S.transition j
  obtain ⟨hq, h10⟩ := chain_transition_facts hab S hd hj
  obtain ⟨hq₀, h10₀⟩ := chain_transition_facts hab S hd (show j < k by omega)
  have hp := eigSlope_conjPair hab T h10
  have hp₀ := eigSlope_conjPair hab T₀ h10₀
  have hswap := ConjPair.swap_of_eq hp hp₀ heq
  have hα := alpha_sq hab
  have hβ := beta_sq hab
  have hsum := alpha_add_beta a b
  -- `T₀ = a - T`.
  have hT₀ : T₀ = (a : ℚ) • 1 - T := by
    have hR : ratToReal T₀ = ratToReal ((a : ℚ) • 1 - T) := by
      apply matrix_eq_of_mulVec hp.ne
      · rw [heq, chain_eigSlope_mulVec hab S hd (show j < k by omega) hβ]
        have hT := chain_eigSlope_mulVec hab S hd hj hα
        rw [← heq]
        have : ratToReal ((a : ℚ) • 1 - T) = (a : ℝ) • 1 - ratToReal T := by
          ext i l; simp [ratToReal, Matrix.one_apply]; split_ifs <;> simp
        rw [this, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hT, ← sub_smul,
          show (a : ℝ) - alpha a b = beta a b by linarith]
      · rw [hswap, chain_eigSlope_mulVec hab S hd (show j < k by omega) hα]
        have hT := chain_eigSlope_mulVec hab S hd hj hβ
        rw [← hswap]
        have : ratToReal ((a : ℚ) • 1 - T) = (a : ℝ) • 1 - ratToReal T := by
          ext i l; simp [ratToReal, Matrix.one_apply]; split_ifs <;> simp
        rw [this, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hT, ← sub_smul,
          show (a : ℝ) - beta a b = alpha a b by linarith]
    ext i l
    have := congrFun (congrFun hR i) l
    simp [ratToReal] at this
    exact_mod_cast this
  -- `Φ_(j+2) = h Φ_j`.
  set B₀ := S.basis j (by omega)
  set B₁ := S.basis (j + 1) (by omega)
  set B₂ := S.basis (j + 2) (by omega)
  have hT₀def : T₀ = B₀.transitionMatrix B₁ := by
    simp [T₀, PadeBasisChain.transition, show j < k by omega, B₀, B₁]
  have hTdef : T = B₁.transitionMatrix B₂ := by
    simp [T, PadeBasisChain.transition, hj, B₁, B₂]
  have hf₁ := B₀.step_factorization (by omega) (hd j (by omega)) B₁
  have hf₂ := B₁.step_factorization (by omega) (hd (j + 1) (by omega)) B₂
  rw [transitionMatrix_eq_step, ← hT₀def, hT₀] at hf₁
  rw [transitionMatrix_eq_step, ← hTdef] at hf₂
  have hB₂ : B₂.matrix = (characteristicPolynomial (a : ℚ) (b : ℚ)) • B₀.matrix := by
    rw [hf₂, hf₁, Matrix.mul_assoc, show (a : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℚ) - T - (a : ℚ) • 1 = -T by abel,
      linearFactor_neg_mul _ _ T hq, Matrix.mul_smul, Matrix.mul_one]
  -- The first column of `Φ_j` would be a low-degree Padé pair.
  have hpade := B₂.isPade 0
  rw [hB₂] at hpade
  simp only [Matrix.smul_apply, smul_eq_mul] at hpade
  have hdiv : characteristicPolynomial (a : ℚ) (b : ℚ) ^ (j + 1) ∣
      X ^ k * B₀.matrix 1 0 - B₀.matrix 0 0 := by
    obtain ⟨E, hE⟩ := hpade.relation
    refine ⟨E, ?_⟩
    have hne := characteristicPolynomial_ne_zero (a : ℚ) (b : ℚ)
    apply mul_left_cancel₀ hne
    rw [pow_succ'] at hE
    linear_combination hE
  have hlow := pade_low_eq_zero (a : ℚ) (b : ℚ) (k := k) (i := j + 1) (by omega)
    (hd (j + 1) (by omega)) (B₀.matrix 0 0) (B₀.matrix 1 0)
    ((B₀.degree_entry 0 0).trans_lt (by exact_mod_cast Nat.lt_succ_self j))
    ((B₀.degree_entry 1 0).trans_lt (by exact_mod_cast Nat.lt_succ_self j)) hdiv
  have hc := B₀.coeff_matrix 0 0
  rw [hlow.1] at hc
  simp at hc

/-- **The last transition.** The lower-left entry of `T_(k-1)` is `1/c` for a
nonzero integer `c`. -/
theorem chain_last_transition {k : ℕ} (hk : 0 < k)
    (S : PadeBasisChain (a : ℚ) (b : ℚ) k)
    (hd : ∀ i, i ≤ k → deltaOver (a : ℚ) (b : ℚ) k i ≠ 0) :
    ∃ c : ℤ, c ≠ 0 ∧ S.transition (k - 1) 1 0 * c = 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  set B := S.basis j (by omega)
  set B' := S.basis (j + 1) le_rfl
  have hT : S.transition j = B.transitionMatrix B' := by
    simp [PadeBasisChain.transition, B, B']
  have hf := B.step_factorization (by omega) (hd j (by omega)) B'
  rw [transitionMatrix_eq_step, ← hT] at hf
  obtain ⟨-, hterm⟩ := B'.terminal_column hk (hd (j + 1) le_rfl)
  have h10 := congrFun (congrFun hf 1) 0
  rw [hterm] at h10
  simp only [linearFactor, Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, Matrix.sub_apply,
    Matrix.one_apply_eq, Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), mul_one,
    mul_zero, sub_zero, zero_add] at h10
  set t := S.transition j 1 0
  set Q₀ := B.matrix 1 0
  set Q₁ := B.matrix 1 1
  set P₀ := B.matrix 0 0
  have hQ₀j : Q₀.coeff j = 0 := by simpa using B.coeff_matrix 1 0
  have hQ₁j : Q₁.coeff j = 1 := by simpa using B.coeff_matrix 1 1
  have hP₀j : P₀.coeff j = 1 := by simpa using B.coeff_matrix 0 0
  have hcj := congrArg (fun p : ℚ[X] => p.coeff j) h10
  simp only [mul_add, coeff_add, coeff_mul_C, hQ₀j, hQ₁j, zero_mul, one_mul, coeff_one,
    add_zero] at hcj
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · refine ⟨1, one_ne_zero, ?_⟩
    rw [coeff_mul_X_zero] at hcj
    simp at hcj
    rw [Int.cast_one, mul_one]
    linarith
  · -- `t = -Q₀_(j-1)`.
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [coeff_mul_X] at hcj
    simp at hcj
    have ht : t = -Q₀.coeff j' := by linarith
    -- The Padé relation for the first column.
    obtain ⟨E, hE⟩ := (B.isPade 0).relation
    have hQ₀deg : Q₀.natDegree ≤ j' := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro n hn
      by_cases hnj : n = j' + 1
      · subst hnj; exact hQ₀j
      · exact coeff_eq_zero_of_degree_lt ((B.degree_entry 1 0).trans_lt
          (by exact_mod_cast (show j' + 1 < n by omega)))
    have hP₀deg : P₀.natDegree ≤ j' + 1 :=
      natDegree_le_iff_degree_le.mpr (B.degree_entry 0 0)
    set F := X ^ (j' + 1 + 1) * Q₀ - P₀
    have hFdeg : F.natDegree ≤ 2 * (j' + 1) := by
      refine (natDegree_sub_le _ _).trans (max_le ?_ (by omega))
      exact natDegree_mul_le.trans (by rw [natDegree_X_pow]; omega)
    have hE0 : E.natDegree = 0 := by
      by_cases hE0 : E = 0
      · simp [hE0]
      · have hmul : (characteristicPolynomial (a : ℚ) (b : ℚ) ^ (j' + 1) * E).natDegree =
            2 * (j' + 1) + E.natDegree := by
          rw [natDegree_mul (pow_ne_zero _ (characteristicPolynomial_ne_zero _ _)) hE0,
            natDegree_hPower]
        rw [← hE] at hmul
        omega
    rw [eq_C_of_natDegree_eq_zero hE0] at hE
    set e := E.coeff 0
    have htop := congrArg (fun p : ℚ[X] => p.coeff (2 * (j' + 1))) hE
    have hmid := congrArg (fun p : ℚ[X] => p.coeff (j' + 1)) hE
    simp only [coeff_mul_C] at htop hmid
    have hlead : (characteristicPolynomial (a : ℚ) (b : ℚ) ^ (j' + 1)).coeff (2 * (j' + 1)) = 1 := by
      rw [← natDegree_hPower (a := (a : ℚ)) (b := (b : ℚ)) (m := j' + 1)]
      exact ((characteristicPolynomial_monic _ _).pow _).coeff_natDegree
    rw [hlead, one_mul] at htop
    have hF2 : F.coeff (2 * (j' + 1)) = Q₀.coeff j' := by
      simp only [F, coeff_sub, coeff_X_pow_mul', show j' + 1 + 1 ≤ 2 * (j' + 1) by omega,
        ite_true, show 2 * (j' + 1) - (j' + 1 + 1) = j' by omega]
      rw [coeff_eq_zero_of_natDegree_lt (show P₀.natDegree < 2 * (j' + 1) by omega), sub_zero]
    have hF1 : F.coeff (j' + 1) = -1 := by
      simp only [F, coeff_sub, coeff_X_pow_mul', show ¬ (j' + 1 + 1 ≤ j' + 1) by omega,
        ite_false, hP₀j]
      ring
    rw [hF2] at htop
    rw [hF1] at hmid
    -- Integrality of the middle coefficient of `h^(j'+1)`.
    have hint : (characteristicPolynomial (a : ℚ) (b : ℚ) ^ (j' + 1)).coeff (j' + 1) =
        ((characteristicPolynomial a b ^ (j' + 1)).coeff (j' + 1) : ℚ) := by
      have hm := characteristicPolynomial_map (Int.castRingHom ℚ) a b
      simp only [eq_intCast] at hm
      rw [← hm, ← Polynomial.map_pow, coeff_map]
      simp
    set c := (characteristicPolynomial a b ^ (j' + 1)).coeff (j' + 1)
    rw [hint] at hmid
    refine ⟨c, ?_, ?_⟩
    · intro hc
      rw [hc] at hmid
      simp at hmid
    · rw [ht, htop]
      linarith

end TwoPoint
