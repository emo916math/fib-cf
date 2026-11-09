module

public import Mathlib.Algebra.ContinuedFractions.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic

@[expose] public section

noncomputable section

namespace TwoPoint

/-! ## Finite simple continued fractions

The paper allows an arbitrary integer first term, positive subsequent terms,
and a final term equal to `1`. We therefore use a representation predicate,
rather than selecting the canonical expansion of a rational number.
-/

/-- A finite word of continued-fraction terms. -/
abbrev CFWord := List ℤ

/-- Every term in this word is positive; the empty word is allowed. -/
def PositiveWord (w : CFWord) : Prop :=
  ∀ d ∈ w, 0 < d

/-- The elementary recursive evaluation, retained to verify agreement with
Mathlib's evaluation. -/
def cfValueRecursive : CFWord → ℚ
  | [] => 0
  | [a] => (a : ℚ)
  | a :: b :: tail => (a : ℚ) + (cfValueRecursive (b :: tail))⁻¹

/-- Interpret a finite word as a Mathlib generalized continued fraction.
All partial numerators are `1`; the empty word is assigned the integer `0`. -/
def CFWord.toGenContFract : CFWord → GenContFract ℚ
  | [] => GenContFract.ofInteger 0
  | a :: tail => ⟨(a : ℚ),
      Stream'.Seq.ofList (tail.map fun (b : ℤ) => (⟨1, (b : ℚ)⟩ : GenContFract.Pair ℚ))⟩

/-- Evaluate the full finite word using Mathlib's convergents.
The value on `[]` is only a total-function convention: `IsContinuedFraction`
excludes the empty word. Its positivity condition excludes zero denominators
in the noninitial tails. -/
def cfValue (w : CFWord) : ℚ :=
  w.toGenContFract.convs' w.tail.length

private theorem convs'Aux_of_word (w : CFWord) :
    GenContFract.convs'Aux
      (Stream'.Seq.ofList (w.map fun (b : ℤ) => (⟨1, (b : ℚ)⟩ : GenContFract.Pair ℚ)))
      w.length = (cfValueRecursive w)⁻¹ := by
  induction w with
  | nil => simp [GenContFract.convs'Aux, cfValueRecursive]
  | cons a tail ih =>
    simp only [List.map_cons, Stream'.Seq.ofList_cons, List.length_cons,
      GenContFract.convs'Aux, Stream'.Seq.head_cons, Stream'.Seq.tail_cons]
    rw [ih]
    cases tail <;> simp [cfValueRecursive, one_div]

/-- Mathlib's evaluation agrees with the elementary finite recursion,
including words ending in `1`. No positivity hypothesis is needed. -/
theorem cfValue_eq_recursive (w : CFWord) : cfValue w = cfValueRecursive w := by
  cases w with
  | nil => simp [cfValue, CFWord.toGenContFract, GenContFract.ofInteger,
      GenContFract.convs', GenContFract.convs'Aux, cfValueRecursive]
  | cons a tail =>
    simp only [cfValue, CFWord.toGenContFract, List.tail_cons, GenContFract.convs']
    rw [convs'Aux_of_word]
    cases tail <;> simp [cfValueRecursive]

/-- `w` is a finite simple continued fraction representing `x`.
In particular, there is no condition requiring the final term to be ≥ 2. -/
def IsContinuedFraction (x : ℚ) (w : CFWord) : Prop :=
  w ≠ [] ∧ PositiveWord w.tail ∧ cfValue w = x

/-- Concatenate `e` copies of a word. This is word repetition, not
exponentiation of its continued-fraction value. -/
def repeatWord (w : CFWord) : ℕ → CFWord
  | 0 => []
  | e + 1 => w ++ repeatWord w e

@[simp] theorem positiveWord_nil : PositiveWord [] := by simp [PositiveWord]

@[simp] theorem positiveWord_cons (a : ℤ) (w : CFWord) :
    PositiveWord (a :: w) ↔ 0 < a ∧ PositiveWord w := by
  simp [PositiveWord]

@[simp] theorem positiveWord_append (v w : CFWord) :
    PositiveWord (v ++ w) ↔ PositiveWord v ∧ PositiveWord w := by
  simp [PositiveWord, or_imp, forall_and]

theorem PositiveWord.repeatWord {w : CFWord} (h : PositiveWord w) (e : ℕ) :
    PositiveWord (repeatWord w e) := by
  induction e with
  | zero => simp [TwoPoint.repeatWord]
  | succ e ih => simpa [TwoPoint.repeatWord] using And.intro h ih

theorem mem_of_mem_repeatWord {d : ℤ} {w : CFWord} {e : ℕ}
    (hd : d ∈ repeatWord w e) : d ∈ w := by
  induction e with
  | zero => simp [repeatWord] at hd
  | succ e ih =>
    simp only [repeatWord, List.mem_append] at hd
    exact hd.elim id ih

theorem cfValueRecursive_pos {w : CFWord} (h : PositiveWord w) (hw : w ≠ []) :
    0 < cfValueRecursive w := by
  induction w with
  | nil => exact False.elim (hw rfl)
  | cons a tail ih =>
    obtain ⟨ha, ht⟩ := (positiveWord_cons a tail).mp h
    have ha' : (0 : ℚ) < a := by exact_mod_cast ha
    cases tail with
    | nil => exact ha'
    | cons b tail =>
      have hp := ih ht (by simp)
      exact add_pos ha' (inv_pos.mpr hp)

theorem cfValue_pos {w : CFWord} (h : PositiveWord w) (hw : w ≠ []) :
    0 < cfValue w := by
  rw [cfValue_eq_recursive]
  exact cfValueRecursive_pos h hw

/-- The matrix of one positive continued-fraction term, as in Section 3.4. -/
def cfTermMatrix (a : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![a, 1; 1, 0]

/-- The matrix of a word; the empty word gives the identity matrix. -/
def CFWord.matrix (w : CFWord) : Matrix (Fin 2) (Fin 2) ℤ :=
  (w.map cfTermMatrix).prod

@[simp] theorem CFWord.matrix_nil : CFWord.matrix [] = 1 := rfl

@[simp] theorem CFWord.matrix_cons (a : ℤ) (w : CFWord) :
    (CFWord.matrix (a :: w)) = cfTermMatrix a * w.matrix := by
  simp [CFWord.matrix]

theorem CFWord.matrix_append (v w : CFWord) : (v ++ w).matrix = v.matrix * w.matrix := by
  simp [CFWord.matrix, List.prod_append]

theorem CFWord.matrix_repeatWord (w : CFWord) (e : ℕ) :
    (repeatWord w e).matrix = w.matrix ^ e := by
  induction e with
  | zero => simp [repeatWord]
  | succ e ih => simp [repeatWord, matrix_append, ih, pow_succ']

theorem cfTermMatrix_det (a : ℤ) : (cfTermMatrix a).det = -1 := by
  simp [cfTermMatrix, Matrix.det_fin_two]

/-- Word matrices are unimodular, with sign determined by word length. -/
theorem CFWord.matrix_det (w : CFWord) : w.matrix.det = (-1 : ℤ) ^ w.length := by
  induction w with
  | nil => simp
  | cons a w ih => simp [Matrix.det_mul, cfTermMatrix_det, ih, pow_succ']

private theorem matrix_cons_top_left (a : ℤ) (w : CFWord) :
    (CFWord.matrix (a :: w)) 0 0 = a * w.matrix 0 0 + w.matrix 1 0 := by
  simp [CFWord.matrix_cons, cfTermMatrix, Matrix.mul_apply, Fin.sum_univ_two]

private theorem matrix_cons_bottom_left (a : ℤ) (w : CFWord) :
    (CFWord.matrix (a :: w)) 1 0 = w.matrix 0 0 := by
  simp [CFWord.matrix_cons, cfTermMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem CFWord.matrix_first_column_nonneg {w : CFWord} (h : PositiveWord w) :
    0 < w.matrix 0 0 ∧ 0 ≤ w.matrix 1 0 := by
  induction w with
  | nil => norm_num
  | cons a w ih =>
    obtain ⟨ha, hw⟩ := (positiveWord_cons a w).mp h
    obtain ⟨hp, hq⟩ := ih hw
    rw [matrix_cons_top_left, matrix_cons_bottom_left]
    exact ⟨add_pos_of_pos_of_nonneg (mul_pos ha hp) hq, le_of_lt hp⟩

/-- The numerical and matrix interpretations of a positive word agree.
This includes the empty-word convention, since division by zero in `ℚ` is zero. -/
theorem CFWord.cfValue_eq_matrix {w : CFWord} (h : PositiveWord w) :
    cfValue w = (w.matrix 0 0 : ℚ) / (w.matrix 1 0 : ℚ) := by
  rw [cfValue_eq_recursive]
  induction w with
  | nil => simp [cfValueRecursive]
  | cons a w ih =>
    obtain ⟨ha, hw⟩ := (positiveWord_cons a w).mp h
    cases w with
    | nil => simp [cfValueRecursive, matrix_cons_top_left, matrix_cons_bottom_left]
    | cons b w =>
      have hp : (((CFWord.matrix (b :: w)) 0 0 : ℤ) : ℚ) ≠ 0 := by
        exact_mod_cast ne_of_gt (CFWord.matrix_first_column_nonneg hw).1
      rw [matrix_cons_top_left a (b :: w), matrix_cons_bottom_left a (b :: w)]
      rw [cfValueRecursive, ih hw]
      push_cast
      rw [inv_div]
      field_simp

end TwoPoint
