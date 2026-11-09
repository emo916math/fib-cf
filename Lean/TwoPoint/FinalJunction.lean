module

public import TwoPoint.Junctions2

/-!
# The final junction

In Exercise `exer:main_gen` the modulus `m_k` may exceed `1`, and the
continued fraction may end with a nonempty junction `J_(k, n mod m_k)`.
For a residue `ν` modulo `m_k`, the integral vector
`v_ν = (H⁻_(k-1,ν))⁻¹ (u_(ν+1)^k, u_ν^k)` is pushed by a power `P^y` of the last
patch towards its attracting fixed point `σ > 1`; once the slope of `P^y v_ν`
exceeds `1`, it is the value of a positive word `J_(k,ν)`. For `ν = 0` the
special last reduction gives `y = 0` and the empty word.
-/

@[expose] public section
noncomputable section

namespace TwoPoint

open Filter Topology

/-- Powers of a hyperbolic stabilizer push every nonzero integral vector into
the cone of slopes greater than `1`: for some `y`, the vector `w = P^y v`
satisfies `0 < w₁ (w₀ - w₁)`. -/
theorem exists_pow_mulVec_cone {σ σ' : ℝ} (h : ConjPair σ σ') (hσ : 1 < σ) {P : GL2Z}
    (hP : P ∈ stab σ h.irrational) (hPl : 1 < lam σ P) (v : Fin 2 → ℤ) (hv : v ≠ 0) :
    ∃ y : ℕ, 0 < ((P ^ y : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ).mulVec v 1 *
      (((P ^ y : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ).mulVec v 0 -
        ((P ^ y : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ).mulVec v 1) := by
  set A : ℕ → Matrix (Fin 2) (Fin 2) ℝ := fun y =>
    (lam σ P ^ y)⁻¹ • intToReal ((P ^ y : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ) with hAdef
  have hA := tendsto_normalized_pow h hP hPl
  set d := (σ - σ')⁻¹
  set s := d * ((v 0 : ℝ) - σ' * v 1)
  have hd : d ≠ 0 := inv_ne_zero (sub_ne_zero.mpr h.ne)
  have hs : s ≠ 0 := by
    refine mul_ne_zero hd fun h0 => ?_
    by_cases hv1 : (v 1 : ℝ) = 0
    · apply hv
      have h1 : v 1 = 0 := by exact_mod_cast hv1
      have h0' : v 0 = 0 := by rw [hv1, mul_zero, sub_zero] at h0; exact_mod_cast h0
      ext j
      fin_cases j <;> simp [h0', h1]
    · exact h.irrational' ⟨(v 0 : ℚ) / v 1, by push_cast; field_simp; linarith⟩
  -- The two components of `A y v`.
  set f₀ : ℕ → ℝ := fun y => A y 0 0 * v 0 + A y 0 1 * v 1
  set f₁ : ℕ → ℝ := fun y => A y 1 0 * v 0 + A y 1 1 * v 1
  have hE (i j : Fin 2) := tendsto_entry hA i j
  have h₀ : Tendsto f₀ atTop (𝓝 (σ * s)) := by
    have := ((hE 0 0).mul_const (v 0 : ℝ)).add ((hE 0 1).mul_const (v 1 : ℝ))
    convert this using 2
    simp [specProj, rk1, s]
    ring
  have h₁ : Tendsto f₁ atTop (𝓝 s) := by
    have := ((hE 1 0).mul_const (v 0 : ℝ)).add ((hE 1 1).mul_const (v 1 : ℝ))
    convert this using 2
    simp [specProj, rk1, s]
    ring
  have hlim : Tendsto (fun y => f₁ y * (f₀ y - f₁ y)) atTop (𝓝 (s * (σ * s - s))) :=
    h₁.mul (h₀.sub h₁)
  have hpos : 0 < s * (σ * s - s) := by
    have : s * (σ * s - s) = s ^ 2 * (σ - 1) := by ring
    rw [this]
    exact mul_pos (by positivity) (by linarith)
  obtain ⟨y, hy⟩ := ((tendsto_order.1 hlim).1 0 hpos).exists
  refine ⟨y, ?_⟩
  set M := ((P ^ y : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ)
  have hl : 0 < lam σ P ^ y := pow_pos (by linarith) y
  have hf₀ : f₀ y = (lam σ P ^ y)⁻¹ * (M.mulVec v 0 : ℝ) := by
    simp [f₀, A, intToReal, M, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  have hf₁ : f₁ y = (lam σ P ^ y)⁻¹ * (M.mulVec v 1 : ℝ) := by
    simp [f₁, A, intToReal, M, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  rw [hf₀, hf₁] at hy
  have : (0 : ℝ) < (M.mulVec v 1 : ℝ) * ((M.mulVec v 0 : ℝ) - (M.mulVec v 1 : ℝ)) := by
    have e : (lam σ P ^ y)⁻¹ * (M.mulVec v 1 : ℝ) *
        ((lam σ P ^ y)⁻¹ * (M.mulVec v 0 : ℝ) - (lam σ P ^ y)⁻¹ * (M.mulVec v 1 : ℝ)) =
        ((lam σ P ^ y)⁻¹) ^ 2 * ((M.mulVec v 1 : ℝ) * ((M.mulVec v 0 : ℝ) - (M.mulVec v 1 : ℝ))) := by
      ring
    rw [e] at hy
    exact pos_of_mul_pos_right hy (by positivity)
  exact_mod_cast this

namespace Ctx

variable (C : Ctx)

/-- The integral vector `(H⁻_(k-1,ν))⁻¹ (u_(ν+1)^k, u_ν^k)`. -/
def vfin (ν : ℕ) : Fin 2 → ℤ :=
  (↑(C.Hm (C.k - 1) ν)⁻¹ : Matrix (Fin 2) (Fin 2) ℤ).mulVec
    ![u C.a C.b (ν + 1) ^ C.k, u C.a C.b ν ^ C.k]

theorem CFWord.matrix_nil : CFWord.matrix [] = 1 := rfl

/-- The final junction: a power `P^y` of the last patch carries `v_ν` to a
multiple of the first column of a positive word, which is empty for `ν = 0`. -/
theorem exists_final (ν : ℕ) :
    ∃ y : ℕ, ∃ w : CFWord, PositiveWord w ∧ (ν = 0 → y = 0 ∧ w = []) ∧
      ∃ c : ℚ, c ≠ 0 ∧ ∀ j, ((((C.P (C.k - 1) ν ^ y : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ).mulVec
        (C.vfin ν) j : ℤ) : ℚ) = c * (w.matrix j 0 : ℚ) := by
  have hk := C.hk
  have hi : C.k - 1 < C.k := by omega
  rcases Nat.eq_zero_or_pos ν with rfl | hν
  · obtain ⟨hK10, hK00⟩ := C.Kred_last
    refine ⟨0, [], positiveWord_nil, fun _ => ⟨rfl, rfl⟩,
      ((C.Kred (C.k - 1) 0 : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℚ), ?_, ?_⟩
    · rcases hK00 with h | h <;> simp [h]
    · intro j
      have hv : C.vfin 0 = (C.Kred (C.k - 1) 0 : Matrix (Fin 2) (Fin 2) ℤ).mulVec ![1, 0] := by
        rw [vfin, C.Hm_last, inv_inv]
        simp [zero_pow (Nat.pos_iff_ne_zero.mp hk)]
      rw [hv]
      fin_cases j <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hK10]
  · set σi := C.sig (C.k - 1) (ν % C.g (C.k - 1))
    obtain ⟨hP, hPl, -⟩ := C.P_spec hi ν
    obtain ⟨hσ, -, -⟩ := C.sig_reduced hi (ν % C.g (C.k - 1))
    have hv : C.vfin ν ≠ 0 := by
      intro h0
      have hu : 0 < u C.a C.b (ν + 1) ^ C.k := pow_pos (u_pos C.hab (by omega)) _
      have := congrArg ((C.Hm (C.k - 1) ν : Matrix (Fin 2) (Fin 2) ℤ).mulVec) h0
      rw [vfin, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, Matrix.mulVec_zero] at this
      have := congrFun this 0
      simp only [Matrix.cons_val_zero, Pi.zero_apply] at this
      omega
    obtain ⟨y, hy⟩ := exists_pow_mulVec_cone (C.sig_pair hi _) hσ hP hPl _ hv
    set W := ((C.P (C.k - 1) ν ^ y : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ).mulVec (C.vfin ν)
    have hW1 : W 1 ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hy
      exact lt_irrefl _ hy
    have hW1q : (W 1 : ℚ) ≠ 0 := by exact_mod_cast hW1
    set r : ℚ := (W 0 : ℚ) / W 1
    have hr : 1 < r := by
      have hq : (0 : ℚ) < (W 1 : ℚ) * ((W 0 : ℚ) - W 1) := by exact_mod_cast hy
      have : r - 1 = (W 1 : ℚ) * ((W 0 : ℚ) - W 1) / (W 1 : ℚ) ^ 2 := by
        simp only [r]
        field_simp
      have : 0 < r - 1 := by rw [this]; positivity
      linarith
    obtain ⟨w, hw, hwh, hwv⟩ := exists_positiveWord r hr.le
    have hw0 : w ≠ [] := by
      rintro rfl
      simp at hwh
    have hM10 := (CFWord.matrix_second_row hw hw0).1
    have hM10q : (w.matrix 1 0 : ℚ) ≠ 0 := by exact_mod_cast hM10.ne'
    rw [CFWord.cfValue_eq_matrix hw] at hwv
    refine ⟨y, w, hw, fun h => absurd h (by omega), (W 1 : ℚ) / w.matrix 1 0,
      div_ne_zero hW1q hM10q, ?_⟩
    intro j
    fin_cases j
    · change (W 0 : ℚ) = _
      have : (W 0 : ℚ) = r * W 1 := by simp only [r]; field_simp
      rw [this, ← hwv]
      field_simp
      rfl
    · change (W 1 : ℚ) = _
      field_simp
      rfl

/-- The final exponent `y_k(ν)`. -/
def yfin (ν : ℕ) : ℕ := Classical.choose (C.exists_final ν)

/-- The final junction word `J_(k,ν)`. -/
def Jfin (ν : ℕ) : CFWord := Classical.choose (Classical.choose_spec (C.exists_final ν))

theorem Jfin_spec (ν : ℕ) :
    PositiveWord (C.Jfin ν) ∧ (ν = 0 → C.yfin ν = 0 ∧ C.Jfin ν = []) ∧
      ∃ c : ℚ, c ≠ 0 ∧ ∀ j, ((((C.P (C.k - 1) ν ^ C.yfin ν : GL2Z) :
        Matrix (Fin 2) (Fin 2) ℤ).mulVec (C.vfin ν) j : ℤ) : ℚ) = c * ((C.Jfin ν).matrix j 0 : ℚ) :=
  Classical.choose_spec (Classical.choose_spec (C.exists_final ν))

end Ctx

end TwoPoint
