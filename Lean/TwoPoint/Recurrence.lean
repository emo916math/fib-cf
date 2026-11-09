module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Dynamics.PeriodicPts.Lemmas

@[expose] public section

noncomputable section

namespace TwoPoint

/-! ## Recurrence and its dominant root -/

/-- The hypotheses on the recurrence in Theorem 1.2.
Thus `a ≥ 1` when `b = 1`, and `a ≥ 3` when `b = -1`. -/
def Admissible (a b : ℤ) : Prop :=
  (b = 1 ∨ b = -1) ∧ 2 - b ≤ a

/-- The recurrence `u_0 = 0`, `u_1 = 1`, `u_(n+2) = a*u_(n+1) + b*u_n`. -/
def u (a b : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => a * u a b (n + 1) + b * u a b n

/-- The larger real root of `x^2 - a*x - b`, under `GenAdmissible a b`. -/
def alpha (a b : ℤ) : ℝ :=
  ((a : ℝ) + Real.sqrt ((a : ℝ) ^ 2 + 4 * (b : ℝ))) / 2

/-- The exact rational number whose continued fraction is studied.
The theorem only uses `n ≥ 1`; casts occur before division. -/
def ratioPower (a b : ℤ) (k n : ℕ) : ℚ :=
  ((u a b (n + 1) : ℚ) / (u a b n : ℚ)) ^ k

/-- `m` is the least positive index for which `d ∣ u_m`.
Divisibility is in `ℤ`, using the determinant with its original sign.
Using this predicate in an existential conclusion also asserts existence
of the rank; existence is not an extra hypothesis on the theorem. -/
def IsRankOfApparition (a b d : ℤ) (m : ℕ) : Prop :=
  0 < m ∧ d ∣ u a b m ∧
    ∀ t : ℕ, 0 < t → d ∣ u a b t → m ≤ t

@[simp] theorem u_zero (a b : ℤ) : u a b 0 = 0 := rfl

@[simp] theorem u_one (a b : ℤ) : u a b 1 = 1 := rfl

theorem u_add_two (a b : ℤ) (n : ℕ) :
    u a b (n + 2) = a * u a b (n + 1) + b * u a b n := rfl

theorem Admissible.a_pos {a b : ℤ} (h : Admissible a b) : 0 < a := by
  rcases h with ⟨rfl | rfl, ha⟩ <;> omega

theorem Admissible.b_sq {a b : ℤ} (h : Admissible a b) : b ^ 2 = 1 := by
  rcases h.1 with rfl | rfl <;> norm_num

/-! ## The hypotheses of Exercise `exer:main_gen` -/

/-- The hypotheses of Exercise `exer:main_gen`: `a > 0`, the discriminant
`D = a^2 + 4b` is a positive non-square, and `t = a^2/b` is an integer.
All recurrence and root lemmas below are stated under these hypotheses. -/
def GenAdmissible (a b : ℤ) : Prop :=
  0 < a ∧ 0 < a ^ 2 + 4 * b ∧ ¬ IsSquare (a ^ 2 + 4 * b) ∧ b ∣ a ^ 2

theorem GenAdmissible.a_pos {a b : ℤ} (h : GenAdmissible a b) : 0 < a := h.1

theorem GenAdmissible.discriminant_not_square {a b : ℤ} (h : GenAdmissible a b) (s : ℤ) :
    s * s ≠ a ^ 2 + 4 * b := fun hs => h.2.2.1 ⟨s, hs.symm⟩

theorem GenAdmissible.b_ne_zero {a b : ℤ} (h : GenAdmissible a b) : b ≠ 0 := by
  rintro rfl
  exact h.discriminant_not_square a (by ring)

/-- The integer `t = a^2/b`. -/
def tRatio (a b : ℤ) : ℤ := a ^ 2 / b

theorem GenAdmissible.tRatio_mul {a b : ℤ} (h : GenAdmissible a b) : tRatio a b * b = a ^ 2 :=
  Int.ediv_mul_cancel h.2.2.2

/-- Under the hypotheses of Theorem 1.2, the discriminant `a^2 + 4b` is not
a perfect square. -/
theorem Admissible.discriminant_not_square {a b : ℤ} (hab : Admissible a b) (s : ℤ) :
    s * s ≠ a ^ 2 + 4 * b := by
  intro hs
  have ht : |s| * |s| = a ^ 2 + 4 * b := by rw [abs_mul_abs_self, hs]
  have h0 := abs_nonneg s
  rcases hab with ⟨rfl | rfl, ha⟩
  · have h1 : a < |s| := by nlinarith
    have h2 : a + 1 ≤ |s| := h1
    have h3 : a = 1 := by nlinarith
    subst h3
    have h4 : |s| ≤ 2 := by nlinarith
    have h5 : |s| = 2 := by omega
    rw [h5] at ht
    norm_num at ht
  · have h1 : |s| < a := by nlinarith
    have h2 : |s| + 1 ≤ a := h1
    nlinarith

/-- The hypotheses of Theorem 1.2 are the case `b = ±1` of the general ones. -/
theorem Admissible.gen {a b : ℤ} (h : Admissible a b) : GenAdmissible a b := by
  refine ⟨h.a_pos, ?_, fun ⟨s, hs⟩ => h.discriminant_not_square s hs.symm, ?_⟩
  · rcases h with ⟨rfl | rfl, ha⟩ <;> nlinarith
  · rcases h.1 with rfl | rfl <;> simp

/-- Positivity and growth of the recurrence: `a u_n ≤ 2 u_(n+1)`. -/
theorem u_nonneg_and_le_succ {a b : ℤ} (h : GenAdmissible a b) (n : ℕ) :
    0 ≤ u a b n ∧ a * u a b n ≤ 2 * u a b (n + 1) := by
  have ha := h.a_pos
  have hD := h.2.1
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨h0, h1⟩ := ih
    have hn1 : 0 ≤ u a b (n + 1) := by nlinarith
    refine ⟨hn1, ?_⟩
    rw [show n + 1 + 1 = n + 2 by omega, u_add_two]
    rcases le_or_gt 0 b with hb | hb
    · nlinarith [mul_nonneg hb h0]
    · -- `b < 0`: use `a u_n ≤ 2 u_(n+1)` and `a^2 + 4b > 0`.
      have : a * (a * u a b (n + 1) + b * u a b n) ≥ a * (a * u a b (n + 1)) +
          b * (2 * u a b (n + 1)) := by nlinarith
      nlinarith

theorem u_pos {a b : ℤ} (h : GenAdmissible a b) {n : ℕ} (hn : 0 < n) :
    0 < u a b n := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := (u_nonneg_and_le_succ h (n + 1)).2
    have := ih (by omega)
    nlinarith [h.a_pos]

/-- The quadratic norm identity used when evaluating homogeneous Padé matrices. -/
theorem u_norm (a b : ℤ) (n : ℕ) :
    u a b (n + 1) ^ 2 - a * u a b (n + 1) * u a b n - b * u a b n ^ 2 =
      (-b) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show n + 1 + 1 = n + 2 by omega, u_add_two, pow_succ (-b) n, ← ih]
    ring

/-- Addition formula without negative indices. -/
theorem u_add_succ (a b : ℤ) (m n : ℕ) :
    u a b (m + n + 1) =
      u a b (m + 1) * u a b (n + 1) + b * u a b m * u a b n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [u]; ring
  | more n ih₀ ih₁ =>
    rw [show m + (n + 2) + 1 = (m + n + 1) + 2 by omega, u_add_two]
    rw [show m + n + 1 + 1 = m + (n + 1) + 1 by omega, ih₁, ih₀]
    rw [show n + 2 + 1 = (n + 1) + 2 by omega, u_add_two]
    simp only [u_add_two]
    ring

/-- The reversible recurrence has a positive zero index modulo every nonzero
integer, as required for ranks of apparition. -/
theorem exists_pos_dvd_u {a b : ℤ} (h : b = 1 ∨ b = -1) (d : ℤ) (hd : d ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ d ∣ u a b m := by
  let : NeZero d.natAbs := ⟨Int.natAbs_ne_zero.mpr hd⟩
  let f : ZMod d.natAbs × ZMod d.natAbs → ZMod d.natAbs × ZMod d.natAbs :=
    fun p => (p.2, (a : ZMod d.natAbs) * p.2 + (b : ZMod d.natAbs) * p.1)
  have hf : Function.Injective f := by
    intro p q hpq
    have h₂ : p.2 = q.2 := congrArg Prod.fst hpq
    have h₁ := congrArg Prod.snd hpq
    dsimp [f] at h₁
    rw [h₂] at h₁
    have hb : (b : ZMod d.natAbs) * p.1 = (b : ZMod d.natAbs) * q.1 :=
      add_left_cancel h₁
    have hb' : p.1 = q.1 := by
      rcases h with rfl | rfl <;> simpa using hb
    exact Prod.ext hb' h₂
  have hi (n : ℕ) : f^[n] (0, 1) =
      ((u a b n : ZMod d.natAbs), (u a b (n + 1) : ZMod d.natAbs)) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      simp [f, u_add_two]
  obtain ⟨m, hm, hperiod⟩ := hf.mem_periodicPts (0, 1)
  refine ⟨m, hm, ?_⟩
  have hz : (u a b m : ZMod d.natAbs) = 0 := by
    simpa [hi] using congrArg Prod.fst hperiod
  have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd (u a b m) d.natAbs).mp hz
  simpa using hdvd

theorem exists_rankOfApparition {a b : ℤ} (h : Admissible a b)
    (d : ℤ) (hd : d ≠ 0) : ∃ m, IsRankOfApparition a b d m := by
  have hex := exists_pos_dvd_u (a := a) h.1 d hd
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  intro t ht hdt
  exact Nat.find_min' hex ⟨ht, hdt⟩

theorem IsRankOfApparition.unique {a b d : ℤ} {m n : ℕ}
    (hm : IsRankOfApparition a b d m) (hn : IsRankOfApparition a b d n) : m = n :=
  Nat.le_antisymm (hm.2.2 n hn.1 hn.2.1) (hn.2.2 m hm.1 hm.2.1)

theorem rankOfApparition_one (a b : ℤ) : IsRankOfApparition a b 1 1 := by
  refine ⟨by omega, by simp, ?_⟩
  intro t ht _
  omega

theorem GenAdmissible.discriminant_pos {a b : ℤ} (h : GenAdmissible a b) :
    0 < (a : ℝ) ^ 2 + 4 * (b : ℝ) := by
  exact_mod_cast h.2.1

theorem alpha_sq {a b : ℤ} (h : GenAdmissible a b) :
    alpha a b ^ 2 = (a : ℝ) * alpha a b + b := by
  have hs := Real.sq_sqrt (le_of_lt h.discriminant_pos)
  unfold alpha
  nlinarith

theorem one_lt_alpha {a b : ℤ} (h : GenAdmissible a b) : 1 < alpha a b := by
  have hs := Real.sq_sqrt (le_of_lt h.discriminant_pos)
  have hn := Real.sqrt_nonneg ((a : ℝ) ^ 2 + 4 * (b : ℝ))
  unfold alpha
  have ha := h.a_pos
  rcases (show a = 1 ∨ 2 ≤ a by omega) with rfl | ha2
  · -- `a = 1` forces `b ≥ 1`, so `D ≥ 5`.
    have hb : 1 ≤ b := by
      have := h.2.1
      have := h.b_ne_zero
      omega
    have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
    norm_num only [Int.cast_one] at hs hn ⊢
    nlinarith
  · have ha' : (2 : ℝ) ≤ a := by exact_mod_cast ha2
    have hpos := Real.sqrt_pos.mpr h.discriminant_pos
    linarith

/-- The other real root, used in the two-point approximation. -/
def beta (a b : ℤ) : ℝ := (a : ℝ) - alpha a b

theorem alpha_mul_beta {a b : ℤ} (h : GenAdmissible a b) :
    alpha a b * beta a b = -(b : ℝ) := by
  unfold beta
  nlinarith [alpha_sq h]

/-- Binet's identity in a denominator-free form. -/
theorem u_mul_root_difference {a b : ℤ} (h : GenAdmissible a b) (n : ℕ) :
    (u a b n : ℝ) * (alpha a b - beta a b) = alpha a b ^ n - beta a b ^ n := by
  have hα := alpha_sq h
  have hβ : beta a b ^ 2 = (a : ℝ) * beta a b + b := by
    unfold beta
    nlinarith
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [beta]
  | more n ih₀ ih₁ =>
    push_cast [u_add_two]
    calc
      ((a : ℝ) * (u a b (n + 1) : ℝ) + (b : ℝ) * (u a b n : ℝ)) *
          (alpha a b - beta a b) =
          (a : ℝ) * ((u a b (n + 1) : ℝ) * (alpha a b - beta a b)) +
          (b : ℝ) * ((u a b n : ℝ) * (alpha a b - beta a b)) := by ring
      _ = (a : ℝ) * (alpha a b ^ (n + 1) - beta a b ^ (n + 1)) +
          (b : ℝ) * (alpha a b ^ n - beta a b ^ n) := by rw [ih₀, ih₁]
      _ = alpha a b ^ (n + 2) - beta a b ^ (n + 2) := by
        rw [pow_add (alpha a b) n 2, pow_add (beta a b) n 2, hα, hβ,
          pow_succ, pow_succ]
        ring

/-- Equation `eq:T_powers` of the paper, without negative recurrence indices.
It applies in particular to each rational matrix satisfying its quadratic
Cayley–Hamilton identity. -/
theorem pow_eq_recurrence {R : Type*} [Ring R] (a b : ℤ) (T : R)
    (hT : T * T = a • T + b • (1 : R)) (n : ℕ) :
    T ^ (n + 1) = u a b (n + 1) • T + (b * u a b n) • (1 : R) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ T (n + 1), ih]
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, one_mul, hT, smul_add, smul_smul]
    rw [show n + 1 + 1 = n + 2 by omega, u_add_two]
    module

end TwoPoint
