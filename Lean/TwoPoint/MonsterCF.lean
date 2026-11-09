module

public import TwoPoint.ContinuedFractions
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Rat.Lemmas

/-!
# A large partial quotient after a close convergent

If a rational number `x` is very close to a rational `r = p/q` in lowest
terms, then some continued fraction of `x` begins with a word for `r` followed
by a term of size about `1 / (q^2 |x - r|)`. This is the classical mechanism
behind the monster terms of Theorem 1.2(a), formalized with the matrix
conventions of Section 3.4.
-/

@[expose] public section
noncomputable section

namespace TwoPoint

/-! ## Entry bounds for word matrices -/

private theorem matrix_cons_apply (a : ℤ) (w : CFWord) :
    (CFWord.matrix (a :: w)) 0 0 = a * w.matrix 0 0 + w.matrix 1 0 ∧
    (CFWord.matrix (a :: w)) 0 1 = a * w.matrix 0 1 + w.matrix 1 1 ∧
    (CFWord.matrix (a :: w)) 1 0 = w.matrix 0 0 ∧
    (CFWord.matrix (a :: w)) 1 1 = w.matrix 0 1 := by
  simp [CFWord.matrix_cons, cfTermMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- Entries of a positive word matrix are nonnegative and its first row is
weakly decreasing; so is its second row unless the word is empty. -/
theorem CFWord.matrix_bounds {w : CFWord} (h : PositiveWord w) :
    (0 ≤ w.matrix 0 1 ∧ w.matrix 0 1 ≤ w.matrix 0 0) ∧
    (0 ≤ w.matrix 1 0 ∧ 0 ≤ w.matrix 1 1) ∧
    (w.matrix 1 1 ≤ w.matrix 1 0 ∨ w = []) := by
  induction w with
  | nil => simp
  | cons a w ih =>
    obtain ⟨ha, hw⟩ := (positiveWord_cons a w).mp h
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩ := ih hw
    obtain ⟨e00, e01, e10, e11⟩ := matrix_cons_apply a w
    rw [e00, e01, e10, e11]
    refine ⟨⟨by positivity, ?_⟩, ⟨by linarith, h1⟩, Or.inl h2⟩
    rcases h5 with h5 | rfl
    · nlinarith
    · simp
      omega

/-- The second row `(q, q')` of a nonempty positive word satisfies `0 ≤ q' ≤ q`
and `0 < q`. -/
theorem CFWord.matrix_second_row {w : CFWord} (h : PositiveWord w) (hw : w ≠ []) :
    0 < w.matrix 1 0 ∧ 0 ≤ w.matrix 1 1 ∧ w.matrix 1 1 ≤ w.matrix 1 0 := by
  obtain ⟨a, w, rfl⟩ := List.exists_cons_of_ne_nil hw
  obtain ⟨_, hw'⟩ := (positiveWord_cons a w).mp h
  obtain ⟨-, -, e10, e11⟩ := matrix_cons_apply a w
  rw [e10, e11]
  obtain ⟨⟨h1, h2⟩, -⟩ := CFWord.matrix_bounds hw'
  exact ⟨(CFWord.matrix_first_column_nonneg hw').1, h1, h2⟩

/-- Concatenation acts by the Möbius transformation of the first word. -/
theorem cfValue_append {v z : CFWord} (hv : PositiveWord v) (hz : PositiveWord z)
    (hz0 : z ≠ []) :
    cfValue (v ++ z) =
      ((v.matrix 0 0 : ℚ) * cfValue z + v.matrix 0 1) /
        ((v.matrix 1 0 : ℚ) * cfValue z + v.matrix 1 1) := by
  have hvz : PositiveWord (v ++ z) := (positiveWord_append v z).mpr ⟨hv, hz⟩
  rw [CFWord.cfValue_eq_matrix hvz, CFWord.cfValue_eq_matrix hz, CFWord.matrix_append]
  have hZ : (0 : ℚ) < z.matrix 1 0 := by exact_mod_cast (CFWord.matrix_second_row hz hz0).1
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  rw [mul_div_assoc', mul_div_assoc', div_add' _ _ _ hZ.ne', div_add' _ _ _ hZ.ne',
    div_div_div_cancel_right₀ hZ.ne']

/-! ## Existence of continued fractions -/

theorem cfValue_singleton (a : ℤ) : cfValue [a] = a := by
  rw [cfValue_eq_recursive]
  rfl

theorem cfValue_cons {a : ℤ} {z : CFWord} (hz : z ≠ []) :
    cfValue (a :: z) = a + (cfValue z)⁻¹ := by
  obtain ⟨b, z, rfl⟩ := List.exists_cons_of_ne_nil hz
  rw [cfValue_eq_recursive, cfValue_eq_recursive]
  rfl

/-- Every rational `y ≥ 1` has a positive continued fraction beginning with
`⌊y⌋`. -/
theorem exists_positiveWord (y : ℚ) (hy : 1 ≤ y) :
    ∃ z : CFWord, PositiveWord z ∧ z.head? = some ⌊y⌋ ∧ cfValue z = y := by
  induction hd : y.den using Nat.strong_induction_on generalizing y with
  | _ n ih =>
    have hfl : 1 ≤ ⌊y⌋ := Int.le_floor.mpr (by exact_mod_cast hy)
    by_cases hf : Int.fract y = 0
    · refine ⟨[⌊y⌋], (positiveWord_cons _ _).mpr ⟨by omega, positiveWord_nil⟩, rfl, ?_⟩
      rw [cfValue_singleton]
      have := Int.fract_add_floor y
      rw [hf, zero_add] at this
      exact this
    · have hf0 : 0 < Int.fract y := lt_of_le_of_ne (Int.fract_nonneg y) (Ne.symm hf)
      have hf1 : Int.fract y < 1 := Int.fract_lt_one y
      have hy' : 1 ≤ (Int.fract y)⁻¹ := (one_le_inv₀ hf0).mpr hf1.le
      have hden : ((Int.fract y)⁻¹).den < n := by
        rw [Rat.den_inv_of_ne_zero hf, ← hd]
        have hfd : (Int.fract y).den = y.den := by
          rw [Int.fract]
          exact Rat.sub_intCast_den y ⌊y⌋
        rw [← hfd]
        have hnum : ((Int.fract y).num : ℚ) < (Int.fract y).den := by
          have hpos : (0 : ℚ) < (Int.fract y).den := by exact_mod_cast (Int.fract y).den_pos
          have hn : ((Int.fract y).num : ℚ) = Int.fract y * (Int.fract y).den :=
            (Rat.mul_den_eq_num _).symm
          rw [hn]
          nlinarith
        have hnum' : (Int.fract y).num < (Int.fract y).den := by exact_mod_cast hnum
        have hnum0 : 0 < (Int.fract y).num := Rat.num_pos.mpr hf0
        omega
      obtain ⟨z, hz, hzh, hzv⟩ := ih _ hden _ hy' rfl
      have hz0 : z ≠ [] := by
        rintro rfl
        simp at hzh
      refine ⟨⌊y⌋ :: z, (positiveWord_cons _ _).mpr ⟨hfl, hz⟩, rfl, ?_⟩
      rw [cfValue_cons hz0, hzv, inv_inv]
      exact Int.floor_add_fract y

/-- Two words whose matrices have the same first column have the same value. -/
theorem cfValue_eq_of_first_column {v w : CFWord} (hv : PositiveWord v) (hw : PositiveWord w)
    (h0 : v.matrix 0 0 = w.matrix 0 0) (h1 : v.matrix 1 0 = w.matrix 1 0) :
    cfValue v = cfValue w := by
  rw [CFWord.cfValue_eq_matrix hv, CFWord.cfValue_eq_matrix hw, h0, h1]

/-- A rational number `r > 1` has positive continued fractions of both
parities, so of both determinant signs. -/
theorem exists_positiveWord_det (r : ℚ) (hr : 1 < r) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    ∃ v : CFWord, PositiveWord v ∧ v ≠ [] ∧ cfValue v = r ∧ v.matrix.det = σ := by
  obtain ⟨z, hz, hzh, hzv⟩ := exists_positiveWord r hr.le
  have hz0 : z ≠ [] := by
    rintro rfl
    simp at hzh
  by_cases hpar : z.matrix.det = σ
  · exact ⟨z, hz, hz0, hzv, hpar⟩
  -- Otherwise switch the parity of the length.
  have hflip : ∀ v : CFWord, v.length = z.length + 1 ∨ v.length + 1 = z.length →
      v.matrix.det = σ := by
    intro v hv
    rw [CFWord.matrix_det] at hpar ⊢
    rcases hv with hv | hv
    · rw [hv, pow_succ]
      rcases hσ with rfl | rfl <;>
        rcases neg_one_pow_eq_or ℤ z.length with h | h <;> simp_all
    · rw [← hv, pow_succ] at hpar
      rcases hσ with rfl | rfl <;>
        rcases neg_one_pow_eq_or ℤ v.length with h | h <;> simp_all
  obtain ⟨D, c, rfl⟩ : ∃ D c, z = D ++ [c] :=
    ⟨_, _, (List.dropLast_append_getLast hz0).symm⟩
  obtain ⟨hD, hc⟩ : PositiveWord D ∧ 0 < c := by simpa using hz
  by_cases hc2 : 2 ≤ c
  · let v := D ++ [c - 1, 1]
    have hv : PositiveWord v := by simp [v, hD]; omega
    refine ⟨v, hv, by simp [v], ?_, hflip v (Or.inl (by simp [v]))⟩
    rw [← hzv]
    apply cfValue_eq_of_first_column hv hz <;>
      simp [v, CFWord.matrix_append, cfTermMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  · have hc1 : c = 1 := by omega
    subst hc1
    rcases List.eq_nil_or_concat D with rfl | ⟨D', c', rfl⟩
    · simp [cfValue_singleton] at hzv
      rw [← hzv] at hr
      norm_num at hr
    · simp only [List.concat_eq_append] at hD hz hzv hflip ⊢
      obtain ⟨hD', hc'⟩ : PositiveWord D' ∧ 0 < c' := by simpa using hD
      let v := D' ++ [c' + 1]
      have hv : PositiveWord v := by simp [v, hD']; omega
      refine ⟨v, hv, by simp [v], ?_, hflip v (Or.inr (by simp [v]))⟩
      rw [← hzv]
      apply cfValue_eq_of_first_column hv hz <;>
        simp [v, CFWord.matrix_append, cfTermMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## The large term -/

/-- The denominator of `p/q` is `q` when `(p,q)` is the first column of a
unimodular matrix with `q > 0`. -/
theorem den_of_unimodular {p q p' q' : ℤ} (hq : 0 < q) (hdet : p * q' - p' * q = 1 ∨
    p * q' - p' * q = -1) : ((p : ℚ) / q).den = q.natAbs := by
  have hcop : IsCoprime p q := by
    rcases hdet with h | h
    · exact ⟨q', -p', by linear_combination h⟩
    · exact ⟨-q', p', by linear_combination -h⟩
  have := Rat.den_div_eq_of_coprime hq (Int.isCoprime_iff_gcd_eq_one.mp hcop)
  omega

/-- If `x ≠ r` with `r > 1`, and `Y = 1 / (den(r)^2 |x - r|) ≥ 2`, then `x` has
a continued fraction containing a term `M` with `Y - 2 ≤ M ≤ Y`. -/
theorem exists_cf_with_large_term (x r : ℚ) (hr : 1 < r) (hxr : x ≠ r)
    (hY : 2 ≤ 1 / ((r.den : ℚ) ^ 2 * |x - r|)) :
    ∃ w : CFWord, IsContinuedFraction x w ∧ ∃ M ∈ w,
      1 / ((r.den : ℚ) ^ 2 * |x - r|) - 2 ≤ M ∧ (M : ℚ) ≤ 1 / ((r.den : ℚ) ^ 2 * |x - r|) := by
  set ε := x - r with hε
  have hε0 : ε ≠ 0 := sub_ne_zero.mpr hxr
  let σ : ℤ := if 0 < ε then -1 else 1
  have hσ : σ = 1 ∨ σ = -1 := by
    by_cases h : 0 < ε <;> simp [σ, h]
  have hσε : -(σ : ℚ) / ε = 1 / |ε| := by
    by_cases h : 0 < ε
    · simp [σ, h, abs_of_pos h]
    · have h' : ε < 0 := lt_of_le_of_ne (not_lt.mp h) hε0
      simp only [σ, h, ite_false, abs_of_neg h']
      push_cast
      field_simp
  obtain ⟨v, hv, hv0, hvr, hvdet⟩ := exists_positiveWord_det r hr σ hσ
  set p := v.matrix 0 0
  set p' := v.matrix 0 1
  set q := v.matrix 1 0
  set q' := v.matrix 1 1
  obtain ⟨hq, hq'0, hq'q⟩ := CFWord.matrix_second_row hv hv0
  have hdet : p * q' - p' * q = σ := by rw [← hvdet, Matrix.det_fin_two]
  have hr' : r = (p : ℚ) / q := by rw [← hvr, CFWord.cfValue_eq_matrix hv]
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  have hden : (r.den : ℚ) = q := by
    rw [hr', den_of_unimodular hq (by rw [hdet]; exact hσ)]
    simp only [Nat.cast_natAbs, Int.cast_abs]
    exact abs_of_pos hqQ
  rw [hden] at hY ⊢
  set Y := 1 / ((q : ℚ) ^ 2 * |ε|) with hYdef
  -- The tail value `y = W⁻¹ x`.
  set y : ℚ := ((p' : ℚ) - q' * x) / (q * x - p) with hydef
  have hqx : (q : ℚ) * x - p = q * ε := by
    rw [hε, hr']
    field_simp
  have hy : y = Y - q' / q := by
    have hσ' : ((p' : ℚ) - q' * x) = -σ / q - q' * ε := by
      have hdetQ : (p : ℚ) * q' - p' * q = σ := by exact_mod_cast hdet
      rw [hε, hr']
      field_simp
      linear_combination -hdetQ
    rw [hydef, hσ', hqx, hYdef]
    have : (-(σ : ℚ) / q - q' * ε) / (q * ε) = (-(σ : ℚ) / ε) / q ^ 2 - q' / q := by
      field_simp
    rw [this, hσε]
    field_simp
  have hq'q' : (q' : ℚ) / q ≤ 1 := by
    rw [div_le_one hqQ]
    exact_mod_cast hq'q
  have hq'0' : 0 ≤ (q' : ℚ) / q := div_nonneg (by exact_mod_cast hq'0) hqQ.le
  have hy1 : 1 ≤ y := by rw [hy]; linarith
  obtain ⟨z, hz, hzh, hzv⟩ := exists_positiveWord y hy1
  have hz0 : z ≠ [] := by
    rintro rfl
    simp at hzh
  refine ⟨v ++ z, ⟨by simp [hv0], ?_, ?_⟩, ⌊y⌋, ?_, ?_, ?_⟩
  · have : PositiveWord (v ++ z) := (positiveWord_append v z).mpr ⟨hv, hz⟩
    obtain ⟨c, t, ht⟩ := List.exists_cons_of_ne_nil (by simp [hv0] : v ++ z ≠ [])
    rw [ht] at this ⊢
    exact ((positiveWord_cons c t).mp this).2
  · rw [cfValue_append hv hz hz0, hzv]
    have hqx0 : (q : ℚ) * x - p ≠ 0 := by rw [hqx]; exact mul_ne_zero hqQ.ne' hε0
    have hyq : y * ((q : ℚ) * x - p) = p' - q' * x := by
      rw [hydef]
      exact div_mul_cancel₀ _ hqx0
    have hpos : (0 : ℚ) < q * y + q' := by
      have : (0 : ℚ) ≤ q' := by exact_mod_cast hq'0
      nlinarith
    rw [div_eq_iff hpos.ne']
    linear_combination (-1 : ℚ) * hyq
  · exact List.mem_append_right v (List.mem_of_mem_head? hzh)
  · linarith [Int.lt_floor_add_one y]
  · linarith [Int.floor_le y]

end TwoPoint
