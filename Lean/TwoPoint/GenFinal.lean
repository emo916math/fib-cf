module

public import TwoPoint.Final
public import TwoPoint.GenTransport

/-!
# Exercise `exer:main_gen`(b), (c)

The moduli `m_0 = 1` and `m_i = exerModulus a b Φ_i i` (`1 ≤ i ≤ k`) satisfy the
transport hypothesis of the patch-junction construction (`GenTransport`), so
the construction of `Final` applies.
-/

@[expose] public section
noncomputable section

namespace TwoPoint

variable {a b : ℤ}

/-- `exerLcm` is positive. -/
theorem exerLcm_pos (hab : GenAdmissible a b) {k i : ℕ}
    (B : NormalizedPadeBasis (a : ℚ) (b : ℚ) k i) : 0 < exerLcm a b B.matrix i := by
  have ha : (a : ℚ) ≠ 0 := by exact_mod_cast hab.a_pos.ne'
  obtain ⟨hd₁, -⟩ := clearingDet_spec B.matrix i ((a : ℚ) / b)
  obtain ⟨hd₂, C, hC, hCdet⟩ := clearingDet_spec B.matrix i (1 / (a : ℚ))
  set t := tRatio a b
  have ht : (t : ℚ) ≠ 0 := by
    intro h
    have h' : (t : ℚ) * b = (a : ℚ) ^ 2 := by exact_mod_cast hab.tRatio_mul
    rw [h, zero_mul] at h'
    exact pow_ne_zero 2 ha h'.symm
  have hdet : (intHom hC (vSeq a b 1) (wSeq a b 0)).det * t ^ i =
      (-1) ^ i * (clearingDet B.matrix i (1 / (a : ℚ)) : ℤ) := by
    have := intHom_det hC (fun x y => B.homEval_det x y) (vSeq a b 1) (wSeq a b 0)
    rw [norm_odd hab 0, hCdet] at this
    have h' : ((intHom hC (vSeq a b 1) (wSeq a b 0)).det : ℚ) * (t : ℚ) ^ i =
        (-1) ^ i * (clearingDet B.matrix i (1 / (a : ℚ)) : ℚ) := by
      rw [this, div_pow, neg_pow, show ((tRatio a b : ℤ) : ℚ) = (t : ℚ) from rfl]
      push_cast
      field_simp
    exact_mod_cast h'
  have habs := congrArg Int.natAbs hdet
  rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_pow, Int.natAbs_neg,
    Int.natAbs_one, one_pow, one_mul, Int.natAbs_natCast] at habs
  have htp : 0 < t.natAbs ^ i := pow_pos (Int.natAbs_pos.mpr (by exact_mod_cast ht)) _
  have h2 : clearingDet B.matrix i (1 / (a : ℚ)) / t.natAbs ^ i =
      (intHom hC (vSeq a b 1) (wSeq a b 0)).det.natAbs := by
    rw [← habs, Nat.mul_div_cancel _ htp]
  have h2pos : 0 < clearingDet B.matrix i (1 / (a : ℚ)) / t.natAbs ^ i := by
    rw [h2]
    apply Int.natAbs_pos.mpr
    intro h0
    rw [h0, Int.natAbs_zero, zero_mul] at habs
    omega
  exact Nat.lcm_pos hd₁ h2pos

/-- The least `m` of `exerModulus` exists: `exerModulus = 2 m` with `m > 0` and
`exerLcm ∣ v_m`. -/
theorem exerModulus_spec (hab : GenAdmissible a b) {k i : ℕ}
    (B : NormalizedPadeBasis (a : ℚ) (b : ℚ) k i) :
    ∃ m, 0 < m ∧ exerModulus a b B.matrix i = 2 * m ∧
      ((exerLcm a b B.matrix i : ℕ) : ℤ) ∣ vSeq a b m := by
  set L := exerLcm a b B.matrix i
  obtain ⟨m₀, hm₀, hdvd⟩ := exists_pos_dvd_vSeq a b (N := (L : ℤ))
    (by exact_mod_cast (exerLcm_pos hab B).ne')
  have hmem : m₀ ∈ {m : ℕ | 0 < m ∧ (L : ℤ) * (a * b ^ (m - 1)) ∣ u a b (2 * m)} :=
    ⟨hm₀, (dvd_u_two_mul_iff hab _ hm₀).mpr hdvd⟩
  obtain ⟨hpos, hdiv⟩ := Nat.sInf_mem ⟨m₀, hmem⟩
  exact ⟨_, hpos, rfl, (dvd_u_two_mul_iff hab _ hpos).mp hdiv⟩

/-- The construction applies to Exercise `exer:main_gen` with the moduli of part (c). -/
theorem exists_ctx_of_gen (hab : GenAdmissible a b) {k : ℕ} (hk : 1 ≤ k)
    (hdelta : ∀ i : ℕ, i ≤ k → delta a b k i ≠ 0) :
    ∃ C : Ctx, C.a = a ∧ C.b = b ∧ C.k = k ∧ C.m 0 = 1 ∧
      (∀ i : ℕ, 1 ≤ i → i ≤ k → ∀ B : NormalizedPadeBasis (a : ℚ) (b : ℚ) k i,
        C.m i = exerModulus a b B.matrix i) := by
  have hdQ : ∀ i, i ≤ k → deltaOver (a : ℚ) (b : ℚ) k i ≠ 0 := by
    intro i hi
    have hm := deltaOver_map (Int.castRingHom ℚ) a b k i
    dsimp at hm
    rw [← hm]
    exact_mod_cast (show deltaOver a b k i ≠ 0 by rw [← delta_eq_deltaOver]; exact hdelta i hi)
  obtain ⟨S⟩ := exists_padeBasisChain (a : ℚ) (b : ℚ) hk hdQ
  let m : ℕ → ℕ := fun i =>
    if i = 0 then 1 else if h : i ≤ k then exerModulus a b (S.basis i h).matrix i else 1
  have hm_gen {i : ℕ} (hi0 : i ≠ 0) (hi : i ≤ k) : m i = exerModulus a b (S.basis i hi).matrix i := by
    simp [m, hi0, hi]
  let C : Ctx :=
    { a := a, b := b, k := k, hab := hab, hk := hk, hd := hdelta, S := S, m := m
      m_pos := fun i => by
        by_cases hi0 : i = 0
        · simp [m, hi0]
        by_cases hi : i ≤ k
        · rw [hm_gen hi0 hi]
          obtain ⟨m₀, hm₀, he, -⟩ := exerModulus_spec hab (S.basis i hi)
          omega
        · simp [m, hi0, hi]
      m_zero := by simp [m]
      transport := fun i hi n t => by
        by_cases hi0 : i = 0
        · subst hi0
          refine ⟨1, isUnit_one, 1, one_ne_zero, ?_⟩
          simp only [map_one, Matrix.one_mul, one_smul, evalU, NormalizedPadeBasis.homEval_zero]
        · obtain ⟨m₀, -, he, hdvd⟩ := exerModulus_spec hab (S.basis i hi)
          obtain ⟨G, hG, c, hc, hGe⟩ := exists_transport_exer hab (S.basis i hi) (m := m₀ * t)
            (hdvd.trans (vSeq_dvd_mul a b m₀ t)) n
          refine ⟨G, hG, c, hc, ?_⟩
          rw [hGe, hm_gen hi0 hi, he]
          congr 2
          ring }
  refine ⟨C, rfl, rfl, rfl, rfl, fun i hi1 hi B => ?_⟩
  change m i = _
  rw [hm_gen (by omega) hi, NormalizedPadeBasis.unique hi (hdQ i hi) (S.basis i hi) B]

/-- **Exercise `exer:main_gen`(b), (c).** If all `Δ_{k,i} ≠ 0`, then the
patch-junction decomposition holds with `m_0 = 1` and, for `1 ≤ i ≤ k`, `m_i`
the least positive even `2m` for which
`lcm{c(Φ_i(X, aY/b)), c(Φ_i(X, Y/a))/t^i} ∣ u_(2m)/(a b^(m-1))`. -/
theorem exer_main_gen_bc (hab : GenAdmissible a b) {k : ℕ} (hk : 1 ≤ k)
    (hdelta : ∀ i : ℕ, i ≤ k → delta a b k i ≠ 0) :
    ∃ m : ℕ → ℕ, m 0 = 1 ∧
      (∀ i : ℕ, 1 ≤ i → i ≤ k → ∀ B : NormalizedPadeBasis (a : ℚ) (b : ℚ) k i,
        m i = exerModulus a b B.matrix i) ∧
      HasPatchJunctionDecompositionMod a b k m := by
  obtain ⟨C, rfl, rfl, rfl, h0, hm⟩ := exists_ctx_of_gen hab hk hdelta
  exact ⟨C.m, h0, hm, C.hasPatchJunctionDecompositionMod⟩

end TwoPoint
