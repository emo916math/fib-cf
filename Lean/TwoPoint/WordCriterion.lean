module

public import TwoPoint.MonsterCF

/-!
# Mercat's criterion for continued-fraction words

The proposition of Section 3.4 (Mercat, Proposition 2.3): an integer matrix of
determinant `±1` with nonnegative entries and weakly decreasing rows and
columns is the matrix of a nonempty positive continued-fraction word.

The proof compares with a word for the value of the first column having the
same determinant: the first columns then agree, and the entry bounds force the
second columns to agree as well.
-/

@[expose] public section
noncomputable section

namespace TwoPoint

/-- Mercat's criterion. With `A = [[p, q], [r, s]]`, the hypotheses say
`0 ≤ s ≤ r ≤ p`, `s ≤ q ≤ p`, and `det A = ±1`. -/
theorem exists_word_of_matrix (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hdet : A.det = 1 ∨ A.det = -1)
    (hs : 0 ≤ A 1 1) (hsr : A 1 1 ≤ A 1 0) (hsq : A 1 1 ≤ A 0 1) (hqp : A 0 1 ≤ A 0 0)
    (hrp : A 1 0 ≤ A 0 0) :
    ∃ w : CFWord, PositiveWord w ∧ w ≠ [] ∧ w.matrix = A := by
  set p := A 0 0 with hpdef
  set q := A 0 1 with hqdef
  set r := A 1 0 with hrdef
  set s := A 1 1 with hsdef
  have hdA : p * s - q * r = A.det := by rw [Matrix.det_fin_two]
  have hr : 0 < r := by
    by_contra h
    have hr0 : r = 0 := by omega
    have hs0 : s = 0 := by omega
    rw [hr0, hs0] at hdA
    rcases hdet with h | h <;> rw [h] at hdA <;> simp at hdA
  have hcop : IsCoprime p r := by
    rcases hdet with h | h
    · exact ⟨s, -q, by linear_combination hdA.trans h⟩
    · exact ⟨-s, q, by linear_combination -(hdA.trans h)⟩
  rcases eq_or_lt_of_le hrp with hpr | hpr
  · -- `p = r`: then `A = [1]`.
    have hp1 : p = 1 := by
      have hd : p ∣ A.det := ⟨s - q, by rw [← hdA, hpr]; ring⟩
      have hd1 : p ∣ 1 := by
        rcases hdet with h | h <;> rw [h] at hd
        · exact hd
        · exact (dvd_neg.mp hd)
      exact Int.eq_one_of_dvd_one (a := p) (by omega) hd1
    have hr1 : r = 1 := by omega
    have hq1 : q = 1 ∧ s = 0 := by
      rw [hp1, hr1] at hdA
      rcases hdet with h | h <;> rw [h] at hdA <;> omega
    refine ⟨[1], by simp, by simp, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [CFWord.matrix, cfTermMatrix] <;> omega
  · -- `p > r`: compare with a word for `p / r` with the same determinant.
    have hx : 1 < (p : ℚ) / r := by
      rw [one_lt_div (by exact_mod_cast hr)]
      exact_mod_cast hpr
    obtain ⟨v, hv, hv0, hvx, hvdet⟩ := exists_positiveWord_det ((p : ℚ) / r) hx A.det hdet
    obtain ⟨hR, hR'0, hR'R⟩ := CFWord.matrix_second_row hv hv0
    obtain ⟨⟨hP'0, hP'P⟩, -⟩ := CFWord.matrix_bounds hv
    set W := v.matrix
    have hdW : W 0 0 * W 1 1 - W 0 1 * W 1 0 = A.det := by rw [← hvdet, Matrix.det_fin_two]
    have hcopW : IsCoprime (W 0 0) (W 1 0) := by
      rcases hdet with h | h
      · exact ⟨W 1 1, -W 0 1, by linear_combination hdW.trans h⟩
      · exact ⟨-W 1 1, W 0 1, by linear_combination -(hdW.trans h)⟩
    have hval : (W 0 0 : ℚ) / W 1 0 = (p : ℚ) / r := by
      rw [← hvx, CFWord.cfValue_eq_matrix hv]
    have hcross : W 0 0 * r = p * W 1 0 := by
      have hRQ : (W 1 0 : ℚ) ≠ 0 := by exact_mod_cast hR.ne'
      have hrQ : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
      rw [div_eq_div_iff hRQ hrQ] at hval
      exact_mod_cast hval
    have hRr : W 1 0 = r := by
      have h1 : r ∣ W 1 0 := hcop.symm.dvd_of_dvd_mul_left ⟨W 0 0, by rw [← hcross]; ring⟩
      have h2 : W 1 0 ∣ r := hcopW.symm.dvd_of_dvd_mul_left ⟨p, by rw [hcross]; ring⟩
      exact Int.dvd_antisymm hR.le hr.le h2 h1
    have hPp : W 0 0 = p := by
      rw [hRr] at hcross
      exact mul_right_cancel₀ hr.ne' hcross
    -- Second columns.
    have hmain : p * (s - W 1 1) = r * (q - W 0 1) := by
      have := hdA.trans hdW.symm
      rw [hPp, hRr] at this
      linear_combination this
    have hdvd : r ∣ s - W 1 1 := hcop.symm.dvd_of_dvd_mul_left ⟨q - W 0 1, by rw [← hmain]⟩
    obtain ⟨t, ht⟩ := hdvd
    rw [hRr] at hR'R
    have ht1 : t = 0 ∨ t = 1 ∨ t = -1 := by
      have h1 : -r ≤ r * t := by rw [← ht]; omega
      have h2 : r * t ≤ r := by rw [← ht]; omega
      have h3 : -1 ≤ t := by nlinarith
      have h4 : t ≤ 1 := by nlinarith
      omega
    rcases ht1 with rfl | rfl | rfl
    · have hq : q = W 0 1 := by
        have : r * (q - W 0 1) = 0 := by rw [← hmain]; simp [show s - W 1 1 = 0 by simpa using ht]
        rcases mul_eq_zero.mp this with h | h
        · omega
        · omega
      refine ⟨v, hv, hv0, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j
      · exact hPp
      · exact hq.symm
      · exact hRr
      · simp only [mul_zero] at ht
        show W 1 1 = s
        omega
    · -- `s = W 1 1 + r` forces `W 1 1 = 0`, and then `q ≥ p`, so `W 0 1 = 0`.
      exfalso
      have hW11 : W 1 1 = 0 := by omega
      have hsr' : s = r := by omega
      have hq : q - W 0 1 = p := by
        have : r * (q - W 0 1) = r * p := by rw [← hmain]; rw [mul_one] at ht; rw [ht]; ring
        exact mul_left_cancel₀ hr.ne' this
      have hW01 : W 0 1 = 0 := by omega
      rw [hW11, hW01] at hdW
      rcases hdet with h | h <;> rw [h] at hdW <;> simp at hdW
    · exfalso
      have hW11 : W 1 1 = r := by omega
      have hs0 : s = 0 := by omega
      have hq : q - W 0 1 = -p := by
        have : r * (q - W 0 1) = r * (-p) := by rw [← hmain]; rw [ht]; ring
        exact mul_left_cancel₀ hr.ne' this
      have hq0 : q = 0 := by omega
      rw [hs0, hq0] at hdA
      rcases hdet with h | h <;> rw [h] at hdA <;> simp at hdA

end TwoPoint
