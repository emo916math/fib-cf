module

public import TwoPoint.Setup

/-!
# Equivalence classes of `η`, the first point, and the last reduction

* `PairRel`: equivalence of pairs of points under one element of `GL₂(ℤ)`.
  A sequence whose class is periodic modulo `p` and modulo `q` has class
  periodic modulo `gcd p q`.
* `ξ_0 = α^k`, so `η_0(n) = α^k > 1` (this starts the continued fraction).
* The last pair `(ξ_(k-1), ξ'_(k-1))` is reduced by a map `x ↦ εx - t` fixing `∞`.
-/

@[expose] public section
noncomputable section

namespace TwoPoint

open Polynomial

/-- The pairs `(x, x')` and `(y, y')` are related by one element of `GL₂(ℤ)`. -/
def PairRel (x x' y y' : ℝ) : Prop :=
  ∃ H : GL2Z, mob (intToReal H) x = y ∧ mob (intToReal H) x' = y'

theorem PairRel.refl (x x' : ℝ) : PairRel x x' x x' :=
  ⟨1, by simp [intToReal_one, mob_one]⟩

theorem mob_inv_GL2Z (H : GL2Z) {x : ℝ} (hx : Irrational x) :
    mob (intToReal (↑H⁻¹ : Matrix (Fin 2) (Fin 2) ℤ)) (mob (intToReal H) x) = x := by
  rw [← mob_mul _ _ _ (mobDen_GL2Z_ne_zero hx H), ← intToReal_mul, Units.inv_mul,
    intToReal_one, mob_one]

theorem PairRel.symm {x x' y y' : ℝ} (hx : Irrational x) (hx' : Irrational x')
    (h : PairRel x x' y y') : PairRel y y' x x' := by
  obtain ⟨H, h1, h2⟩ := h
  exact ⟨H⁻¹, by rw [← h1, mob_inv_GL2Z H hx], by rw [← h2, mob_inv_GL2Z H hx']⟩

theorem PairRel.trans {x x' y y' z z' : ℝ} (hx : Irrational x) (hx' : Irrational x')
    (h₁ : PairRel x x' y y') (h₂ : PairRel y y' z z') : PairRel x x' z z' := by
  obtain ⟨H₁, a1, a2⟩ := h₁
  obtain ⟨H₂, b1, b2⟩ := h₂
  refine ⟨H₂ * H₁, ?_, ?_⟩
  · rw [Units.val_mul, intToReal_mul, mob_mul _ _ _ (mobDen_GL2Z_ne_zero hx H₁), a1, b1]
  · rw [Units.val_mul, intToReal_mul, mob_mul _ _ _ (mobDen_GL2Z_ne_zero hx' H₁), a2, b2]

/-- Classes periodic modulo `p` and `q` are periodic modulo `gcd p q`. -/
theorem pairRel_of_modEq {f f' : ℕ → ℝ} (hirr : ∀ n, Irrational (f n) ∧ Irrational (f' n))
    {p q : ℕ} (hp : ∀ n, PairRel (f n) (f' n) (f (n + p)) (f' (n + p)))
    (hq : ∀ n, PairRel (f n) (f' n) (f (n + q)) (f' (n + q))) {n n' : ℕ}
    (hnn : n ≡ n' [MOD Nat.gcd p q]) : PairRel (f n) (f' n) (f n') (f' n') := by
  let Per : ℕ → Prop := fun d => ∀ n, PairRel (f n) (f' n) (f (n + d)) (f' (n + d))
  have hmul (d : ℕ) (hd : Per d) (t : ℕ) : Per (d * t) := by
    induction t with
    | zero => intro n; simpa using PairRel.refl (f n) (f' n)
    | succ t ih =>
      intro n
      have := (ih n).trans (hirr n).1 (hirr n).2 (hd (n + d * t))
      rwa [show n + d * t + d = n + d * (t + 1) by ring] at this
  have hsub (d e : ℕ) (hd : Per d) (he : Per e) (hde : d ≤ e) : Per (e - d) := by
    intro n
    have h1 := he n
    have h2 := hd (n + (e - d))
    rw [show n + (e - d) + d = n + e by omega] at h2
    exact h1.trans (hirr n).1 (hirr n).2 (h2.symm (hirr _).1 (hirr _).2)
  have hgcd : ∀ m n, Per m → Per n → Per (Nat.gcd m n) := by
    intro m n
    induction m, n using Nat.gcd.induction with
    | H0 n => intro _ hn; simpa using hn
    | H1 m n hm ih =>
      intro hPm hPn
      rw [Nat.gcd_rec]
      apply ih _ hPm
      have := hsub (m * (n / m)) n (hmul m hPm _) hPn (Nat.mul_div_le n m)
      rwa [← Nat.mod_eq_sub_mul_div] at this
  have hg := hgcd p q hp hq
  rcases le_total n n' with hle | hle
  · obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' hle).mp hnn
    have := hmul _ hg t n
    rwa [← ht, Nat.add_sub_cancel' hle] at this
  · obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' hle).mp hnn.symm
    have := hmul _ hg t n'
    rw [← ht, Nat.add_sub_cancel' hle] at this
    exact this.symm (hirr n').1 (hirr n').2

namespace Ctx

variable (C : Ctx)

/-- `ξ_0 = α^k`. -/
theorem xi_zero : C.xi 0 = alpha C.a C.b ^ C.k := by
  set B₀ := C.S.basis 0 (Nat.zero_le _)
  set B₁ := C.S.basis 1 C.hk
  have hT : C.T 0 = B₀.transitionMatrix B₁ := by
    simp [T, PadeBasisChain.transition, C.hk, B₀, B₁]
  have hf := B₀.step_factorization (Nat.zero_le _) (C.hdQ 0 (Nat.zero_le _)) B₁
  rw [transitionMatrix_eq_step, ← hT, B₀.matrix_zero, Matrix.one_mul] at hf
  obtain ⟨E, hE⟩ := (B₁.isPade 0).relation
  rw [hf] at hE
  simp only [linearFactor, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply,
    Matrix.sub_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide),
    mul_one, mul_zero, sub_zero, zero_add, pow_one] at hE
  have hev := congrArg (aeval (alpha C.a C.b)) hE
  simp only [map_sub, map_mul, map_pow, aeval_X, aeval_C, map_add,
    aeval_alpha_characteristicPolynomial C.hab, zero_mul] at hev
  obtain ⟨hq, h10⟩ := chain_transition_facts C.hab C.S C.hdQ C.hk
  obtain ⟨htr, -⟩ := quadratic_entries _ hq h10
  have h10R : ((C.T 0 1 0 : ℚ) : ℝ) ≠ 0 := by exact_mod_cast h10
  have htrR : ((C.T 0 0 0 : ℚ) : ℝ) + C.T 0 1 1 = C.a := by exact_mod_cast htr
  simp only [eq_ratCast] at hev
  push_cast at hev
  rw [xi, eigSlope, div_eq_iff h10R]
  simp only [T] at hev htrR ⊢
  linear_combination -hev - htrR

theorem eta_zero (n : ℕ) : C.eta 0 n = alpha C.a C.b ^ C.k := by
  rw [eta, U_zero_left, mob_one, xi_zero]

theorem one_lt_eta_zero (n : ℕ) : 1 < C.eta 0 n := by
  rw [eta_zero]
  exact one_lt_pow₀ (one_lt_alpha C.hab) C.hk.ne'

/-- The reduction of the last pair by `x ↦ εx - t`. -/
theorem exists_last_reduction :
    ∃ K : GL2Z, (K : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 ∧
      ((K : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = 1 ∨ (K : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = -1) ∧
      1 < mob (intToReal K) (C.xi (C.k - 1)) ∧ -1 < mob (intToReal K) (C.xi' (C.k - 1)) ∧
      mob (intToReal K) (C.xi' (C.k - 1)) < 0 := by
  obtain ⟨c, hc0, htc⟩ := chain_last_transition C.hk C.S C.hdQ
  have hp := C.xi_pair (show C.k - 1 < C.k by have := C.hk; omega)
  set x := C.xi (C.k - 1)
  set x' := C.xi' (C.k - 1)
  -- `|x - x'| > 2`.
  have hdiff : x - x' = c * (alpha C.a C.b - beta C.a C.b) := by
    have h10 : ((C.T (C.k - 1) 1 0 : ℚ) : ℝ) ≠ 0 := by
      intro h
      have h0 : C.T (C.k - 1) 1 0 = 0 := by exact_mod_cast h
      simp only [T] at h0
      rw [h0, zero_mul] at htc
      exact zero_ne_one htc
    have htcR : ((C.T (C.k - 1) 1 0 : ℚ) : ℝ) * c = 1 := by exact_mod_cast htc
    simp only [x, x', xi, xi', eigSlope]
    rw [div_sub_div_same, div_eq_iff h10]
    simp only [T] at htcR ⊢
    linear_combination -(alpha C.a C.b - beta C.a C.b) * htcR
  have hgap : 2 < |x - x'| := by
    rw [hdiff, abs_mul, abs_of_pos (alpha_sub_beta_pos C.hab)]
    have : (1 : ℝ) ≤ |(c : ℝ)| := by exact_mod_cast Int.one_le_abs hc0
    nlinarith [two_lt_alpha_sub_beta C.hab]
  set ε : ℤ := if x' < x then 1 else -1
  have hε : (ε : ℝ) * (x - x') = |x - x'| := by
    by_cases h : x' < x
    · simp [ε, h, abs_of_pos (sub_pos.mpr h)]
    · have h' : x < x' := lt_of_le_of_ne (not_lt.mp h) hp.ne
      simp [ε, h, abs_of_neg (sub_neg.mpr h')]
  have hε2 : ε * ε = 1 := by by_cases h : x' < x <;> simp [ε, h]
  set t : ℤ := ⌈(ε : ℝ) * x'⌉
  let K : GL2Z := {
    val := !![ε, -t; 0, 1]
    inv := !![ε, ε * t; 0, 1]
    val_inv := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, hε2]
      linear_combination t * hε2
    inv_val := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, hε2] }
  have hmob (y : ℝ) : mob (intToReal K) y = ε * y - t := by
    simp [mob, mobDen, intToReal, K]
    ring
  have hirr : Irrational ((ε : ℝ) * x') := by
    have : (ε : ℝ) ≠ 0 := by by_cases h : x' < x <;> simp [ε, h]
    exact hp.irrational'.intCast_mul (by exact_mod_cast this)
  have ht1 : (ε : ℝ) * x' ≤ t := Int.le_ceil _
  have ht2 : (ε : ℝ) * x' ≠ t := fun h => hirr ⟨t, by rw [h]; simp⟩
  have ht3 : (t : ℝ) < ε * x' + 1 := Int.ceil_lt_add_one _
  refine ⟨K, by simp [K], ?_, ?_, ?_, ?_⟩
  · by_cases h : x' < x <;> simp [K, ε, h]
  · rw [hmob]
    have : (ε : ℝ) * x - t = (ε * x' - t) + ε * (x - x') := by ring
    rw [this, hε]
    linarith
  · rw [hmob]; linarith
  · rw [hmob]; exact sub_neg.mpr (lt_of_le_of_ne ht1 ht2)

end Ctx

end TwoPoint
