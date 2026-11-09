module

public import TwoPoint.MonsterPade
public import TwoPoint.MonsterAsymptotics
public import TwoPoint.GenTransport

/-!
# Theorem 1.2(a) and Exercise `exer:main_gen`(a): monster terms

If `Δ_{k,i}(a,b) = 0`, the exact Padé pair `P/Q` of `MonsterPade` evaluated at
`x_n = u_(n+1)/u_n` is a rational approximation to `x_n^k` with error
`E(x_n) h(x_n)^(d+1) / Q(x_n)`, where `h(x_n) = (-b)^n u_n^(-2)`. Write
`u_(n+1) = e s'`, `u_n = e t'` with `e = b^⌊(n-1)/2⌋` and `x s' + y t' = ab`
(from the even/odd description of `u` in `GenTransport`). The reduced
denominator is `D t'^d Q(x_n)` up to a bounded factor (by the homogeneous
Bézout identities). Hence
`1 / (den^2 |error|) ≍ e^(2d) u_n^2 / |b|^(n(d+1)) ≍ α^(2n) / |b|^n = |ρ|^n`,
which produces the monster term. For `b = ±1` this is `α^(2n)`.
-/

@[expose] public section
noncomputable section

namespace TwoPoint

open Polynomial Filter Topology

variable {a b : ℤ}

theorem aeval_ratCast (F : ℚ[X]) (x : ℚ) : aeval (x : ℝ) F = ((F.eval x : ℚ) : ℝ) := by
  rw [show (x : ℝ) = algebraMap ℚ ℝ x from rfl, aeval_algebraMap_apply_eq_algebraMap_eval]
  rfl

/-- The rational ratio `x_n = u_(n+1)/u_n`. -/
def uRatio (a b : ℤ) (n : ℕ) : ℚ := (u a b (n + 1) : ℚ) / u a b n

theorem ratioPower_eq_uRatio_pow (a b : ℤ) (k n : ℕ) :
    ratioPower a b k n = uRatio a b n ^ k := rfl

theorem tendsto_aeval_uRatio (hab : GenAdmissible a b) (F : ℚ[X]) :
    Tendsto (fun n => ((F.eval (uRatio a b n) : ℚ) : ℝ)) atTop (𝓝 (aeval (alpha a b) F)) := by
  have hx : Tendsto (fun n => ((uRatio a b n : ℚ) : ℝ)) atTop (𝓝 (alpha a b)) := by
    simpa [uRatio] using tendsto_u_ratio hab
  have := ((Polynomial.continuous_aeval F).tendsto (alpha a b)).comp hx
  refine this.congr ?_
  intro n
  simp [Function.comp, aeval_ratCast]

theorem eval_characteristicPolynomial_uRatio (a b : ℤ) (n : ℕ) (hn : u a b n ≠ 0) :
    (characteristicPolynomial (a : ℚ) (b : ℚ)).eval (uRatio a b n) =
      (((-b) ^ n : ℤ) : ℚ) / (u a b n : ℚ) ^ 2 := by
  have h := u_norm a b n
  have hq : (u a b n : ℚ) ≠ 0 := by exact_mod_cast hn
  have hQ : ((u a b (n + 1) : ℚ) ^ 2 - a * u a b (n + 1) * u a b n - b * u a b n ^ 2) =
      (((-b) ^ n : ℤ) : ℚ) := by exact_mod_cast h
  simp only [characteristicPolynomial, eval_sub, eval_mul, eval_pow, eval_X, eval_C, uRatio]
  rw [← hQ]
  field_simp

/-- A divisor of `c s^N` and `c t^N` divides `c κ^N` when `κ ∈ (s, t)`. -/
theorem int_dvd_of_dvd_mul_pow_of_comb {g c s t x y κ : ℤ} {N : ℕ} (hxy : x * s + y * t = κ)
    (hs : g ∣ c * s ^ N) (ht : g ∣ c * t ^ N) : g ∣ c * κ ^ N := by
  by_cases h0 : Int.gcd s t = 0
  · obtain ⟨rfl, rfl⟩ := Int.gcd_eq_zero_iff.mp h0
    simp only [mul_zero, add_zero] at hxy
    subst hxy
    exact hs
  obtain ⟨G, s₀, t₀, hG, hst, rfl, rfl⟩ := Int.exists_gcd_one' (Nat.pos_of_ne_zero h0)
  have hcop : IsCoprime s₀ t₀ := Int.isCoprime_iff_gcd_eq_one.mpr hst
  have h1 : g ∣ (c * (G : ℤ) ^ N) * s₀ ^ N := by rw [mul_assoc, ← mul_pow, mul_comm (G : ℤ)]; exact hs
  have h2 : g ∣ (c * (G : ℤ) ^ N) * t₀ ^ N := by rw [mul_assoc, ← mul_pow, mul_comm (G : ℤ)]; exact ht
  have hGκ : (G : ℤ) ∣ κ := ⟨x * s₀ + y * t₀, by rw [← hxy]; ring⟩
  exact (int_dvd_of_dvd_mul_pow hcop h1 h2).trans
    (mul_dvd_mul_left c (pow_dvd_pow_of_dvd hGκ N))

theorem wSeq_norm (a b : ℤ) (j : ℕ) :
    wSeq a b j ^ 2 - tRatio a b * wSeq a b j * vSeq a b j - tRatio a b * vSeq a b j ^ 2 = 1 := by
  unfold wSeq
  linear_combination vSeq_norm a b j

/-- The common factor `e = b^⌊(n-1)/2⌋` of `u_(n+1)` and `u_n`, and a Bézout
identity for the cofactors. -/
theorem exists_common_factor (hab : GenAdmissible a b) {n : ℕ} (hn : 1 ≤ n) :
    ∃ e s' t' x y : ℤ, u a b (n + 1) = e * s' ∧ u a b n = e * t' ∧ x * s' + y * t' = a * b ∧
      e ^ 2 ≤ |b| ^ n ∧ |b| ^ n ≤ e ^ 2 * b ^ 2 := by
  have hb1 : 1 ≤ |b| := Int.one_le_abs hab.b_ne_zero
  have hbsq : b ^ 2 = |b| ^ 2 := (sq_abs b).symm
  have hpow (m : ℕ) : (b ^ m) ^ 2 = |b| ^ (2 * m) := by
    rw [← pow_mul, mul_comm, pow_mul, hbsq, ← pow_mul]
  rcases Nat.even_or_odd' n with ⟨j, rfl | rfl⟩
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have hw := wSeq_norm a b (i + 1)
    refine ⟨b ^ i, b * wSeq a b (i + 1), a * vSeq a b (i + 1), a * wSeq a b (i + 1),
      -(tRatio a b * b * (wSeq a b (i + 1) + vSeq a b (i + 1))), ?_, ?_, ?_, ?_, ?_⟩
    · rw [(u_odd_even hab (i + 1)).1, wSeq]
      ring
    · rw [show 2 * (i + 1) = 2 * i + 2 by ring, (u_odd_even hab i).2]
      ring
    · linear_combination (a * b) * hw
    · rw [hpow]
      exact pow_le_pow_right₀ hb1 (by omega)
    · rw [hpow, hbsq, ← pow_add]
      exact le_of_eq (by ring_nf)
  · have hw := wSeq_norm a b j
    have hv := vSeq_norm a b j
    refine ⟨b ^ j, a * vSeq a b (j + 1), wSeq a b j,
      -(b * tRatio a b * vSeq a b (j + 1)), b * (a * tRatio a b * vSeq a b (j + 1) + a * wSeq a b j),
      ?_, ?_, ?_, ?_, ?_⟩
    · rw [show 2 * j + 1 + 1 = 2 * j + 2 by ring, (u_odd_even hab j).2]
      ring
    · rw [(u_odd_even hab j).1, wSeq]
    · unfold wSeq at hw ⊢
      linear_combination (a * b) * hv
    · rw [hpow]
      exact pow_le_pow_right₀ hb1 (by omega)
    · rw [hpow, hbsq, ← pow_add]
      exact pow_le_pow_right₀ hb1 (by omega)

/-- The closeness of the Padé approximation at a single index `n`, with the
common factor `e` and a bounded cancelled factor `g`. -/
theorem monster_closeness (hab : GenAdmissible a b) {k d : ℕ} {P Q E A B A' B' : ℚ[X]}
    (hM : MonsterPade (a : ℚ) (b : ℚ) k d P Q E)
    (hAB : A * P + B * Q = 1) (hA : A.natDegree ≤ d) (hB : B.natDegree ≤ d)
    (hAB' : A' * P + B' * Q = X ^ (2 * d)) (hA' : A'.natDegree ≤ d) (hB' : B'.natDegree ≤ d)
    {D D' : ℕ} (hD : 0 < D) (hD' : 0 < D')
    (hDP : ClearsDen D P) (hDQ : ClearsDen D Q)
    (hDA : ClearsDen D' A) (hDB : ClearsDen D' B) (hDA' : ClearsDen D' A') (hDB' : ClearsDen D' B')
    {n : ℕ} (hn : 1 ≤ n) (hQx : Q.eval (uRatio a b n) ≠ 0)
    {e s' t' x y : ℤ} (hs : u a b (n + 1) = e * s') (ht : u a b n = e * t')
    (hxy : x * s' + y * t' = a * b) :
    ∃ g : ℤ, g ≠ 0 ∧ |g| ≤ (D * D' : ℕ) * |a * b| ^ (2 * d) ∧
      (((P.eval (uRatio a b n) / Q.eval (uRatio a b n)).den : ℚ)) ^ 2 *
          |ratioPower a b k n - P.eval (uRatio a b n) / Q.eval (uRatio a b n)| =
        (D : ℚ) ^ 2 * |Q.eval (uRatio a b n) * E.eval (uRatio a b n)| * |(b : ℚ)| ^ (n * (d + 1)) /
          ((g : ℚ) ^ 2 * (e : ℚ) ^ (2 * d) * (u a b n : ℚ) ^ 2) := by
  have hun : u a b n ≠ 0 := (u_pos hab hn).ne'
  have he : e ≠ 0 := by rintro rfl; rw [zero_mul] at ht; exact hun ht
  have ht' : t' ≠ 0 := by rintro rfl; rw [mul_zero] at ht; exact hun ht
  have heQ : (e : ℚ) ≠ 0 := by exact_mod_cast he
  have htQ : (t' : ℚ) ≠ 0 := by exact_mod_cast ht'
  set x₀ := uRatio a b n with hxdef
  have hx : x₀ = (s' : ℚ) / t' := by
    rw [hxdef, uRatio, hs, ht]
    push_cast
    field_simp
  have hDQ0 : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  -- Integral homogeneous values at `(s', t')`.
  obtain ⟨p₁, hp₁⟩ := hDP.exists_int_hom hM.natDegree_num.le s' t' ht'
  obtain ⟨q₁, hq₁⟩ := hDQ.exists_int_hom hM.natDegree_den.le s' t' ht'
  rw [← hx] at hp₁ hq₁
  have hq₁0 : q₁ ≠ 0 := by
    have : (q₁ : ℚ) ≠ 0 := by
      rw [hq₁]; exact mul_ne_zero (mul_ne_zero hDQ0 (pow_ne_zero _ htQ)) hQx
    exact_mod_cast this
  have hr : P.eval x₀ / Q.eval x₀ = (p₁ : ℚ) / q₁ := by
    rw [hp₁, hq₁]
    field_simp
  obtain ⟨g, hgp, hgq, hgden⟩ := exists_den_mul_eq p₁ q₁ hq₁0
  rw [← hr] at hgden
  -- The gcd bound.
  have hdvd : g ∣ ((D * D' : ℕ) : ℤ) * (a * b) ^ (2 * d) := by
    obtain ⟨a₁, ha₁⟩ := hDA.exists_int_hom hA s' t' ht'
    obtain ⟨b₁, hb₁⟩ := hDB.exists_int_hom hB s' t' ht'
    obtain ⟨a₂, ha₂⟩ := hDA'.exists_int_hom hA' s' t' ht'
    obtain ⟨b₂, hb₂⟩ := hDB'.exists_int_hom hB' s' t' ht'
    rw [← hx] at ha₁ hb₁ ha₂ hb₂
    have he₁ : a₁ * p₁ + b₁ * q₁ = ((D * D' : ℕ) : ℤ) * t' ^ (2 * d) := by
      have hev := congrArg (eval x₀) hAB
      simp only [eval_add, eval_mul, eval_one] at hev
      have : (a₁ : ℚ) * p₁ + b₁ * q₁ = ((D * D' : ℕ) : ℚ) * (t' : ℚ) ^ (2 * d) := by
        rw [ha₁, hb₁, hp₁, hq₁, two_mul, pow_add]
        push_cast
        linear_combination ((D : ℚ) * D' * t' ^ d * t' ^ d) * hev
      exact_mod_cast this
    have he₂ : a₂ * p₁ + b₂ * q₁ = ((D * D' : ℕ) : ℤ) * s' ^ (2 * d) := by
      have hev := congrArg (eval x₀) hAB'
      simp only [eval_add, eval_mul, eval_pow, eval_X] at hev
      have hs' : (s' : ℚ) = x₀ * t' := by rw [hx]; field_simp
      have : (a₂ : ℚ) * p₁ + b₂ * q₁ = ((D * D' : ℕ) : ℚ) * (s' : ℚ) ^ (2 * d) := by
        rw [ha₂, hb₂, hp₁, hq₁, hs', mul_pow, two_mul, pow_add, pow_add]
        push_cast
        linear_combination ((D : ℚ) * D' * t' ^ d * t' ^ d) * hev
      exact_mod_cast this
    apply int_dvd_of_dvd_mul_pow_of_comb hxy (N := 2 * d)
    · rw [← he₂]
      exact dvd_add (dvd_mul_of_dvd_right hgp _) (dvd_mul_of_dvd_right hgq _)
    · rw [← he₁]
      exact dvd_add (dvd_mul_of_dvd_right hgp _) (dvd_mul_of_dvd_right hgq _)
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hgden
    exact hq₁0 hgden.symm
  have hab0 : a * b ≠ 0 := mul_ne_zero hab.a_pos.ne' hab.b_ne_zero
  have hgle : |g| ≤ (D * D' : ℕ) * |a * b| ^ (2 * d) := by
    have hpos : 0 < |((D * D' : ℕ) : ℤ) * (a * b) ^ (2 * d)| :=
      abs_pos.mpr (mul_ne_zero (by exact_mod_cast (Nat.mul_pos hD hD').ne') (pow_ne_zero _ hab0))
    have := Int.le_of_dvd hpos ((abs_dvd_abs _ _).mpr hdvd)
    rwa [abs_mul, abs_pow, Nat.abs_cast] at this
  refine ⟨g, hg0, hgle, ?_⟩
  -- The closeness formula.
  have hgQ : (g : ℚ) ≠ 0 := by exact_mod_cast hg0
  have hden : ((P.eval x₀ / Q.eval x₀).den : ℚ) = q₁ / g := by
    have : (((P.eval x₀ / Q.eval x₀).den : ℤ) : ℚ) * g = q₁ := by exact_mod_cast hgden
    rw [eq_div_iff hgQ]
    exact_mod_cast this
  have hrel := congrArg (eval x₀) hM.relation
  simp only [eval_sub, eval_mul, eval_pow, eval_X] at hrel
  rw [eval_characteristicPolynomial_uRatio a b n hun] at hrel
  have hε : ratioPower a b k n - P.eval x₀ / Q.eval x₀ =
      E.eval x₀ * ((((-b) ^ n : ℤ) : ℚ) / (u a b n : ℚ) ^ 2) ^ (d + 1) / Q.eval x₀ := by
    rw [ratioPower_eq_uRatio_pow, ← hxdef, ← hrel]
    field_simp
  have htt : (u a b n : ℚ) = e * t' := by rw [ht]; push_cast; ring
  have hb' : |(((-b) ^ n : ℤ) : ℚ)| = |(b : ℚ)| ^ n := by push_cast; rw [abs_pow, abs_neg]
  rw [hden, hε, hq₁, abs_div, abs_mul, abs_pow, abs_div, hb', abs_pow, abs_mul, htt]
  have hQa : |eval x₀ Q| ≠ 0 := abs_ne_zero.mpr hQx
  have h1 : ((D : ℚ) * t' ^ d * eval x₀ Q / g) ^ 2 = ((D : ℚ) * t' ^ d / g) ^ 2 * |eval x₀ Q| ^ 2 := by
    rw [sq_abs]
    ring
  rw [h1, show |(e : ℚ) * t'| ^ 2 = ((e : ℚ) * t') ^ 2 from sq_abs _, div_pow, mul_pow,
    mul_pow, div_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
  field_simp
  ring

/-- **Exercise `exer:main_gen`(a).** If some Padé–Toeplitz determinant
vanishes, then for all large `n` the continued fraction of `(u_(n+1)/u_n)^k`
has a term of exact order `|ρ|^n`, `ρ = α/ᾱ`. -/
theorem hasMonsterTermsRate_of_delta_eq_zero (hab : GenAdmissible a b) {k : ℕ} (hk : 1 ≤ k)
    (hz : ∃ i, i ≤ k ∧ delta a b k i = 0) :
    HasMonsterTermsRate a b k (fun n => rhoAbs a b ^ n) := by
  obtain ⟨i, hi, hzi⟩ := hz
  obtain ⟨d, hdk, P, Q, E, hM⟩ := exists_monsterPade hab hi hzi
  obtain ⟨hQα, hEα⟩ := hM.aeval_alpha_ne_zero hab
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    simp at hQα
  obtain ⟨A, B, hAB, hA, hB⟩ := exists_bezout_natDegree_le (M := 2 * d) hM.coprime
    hM.natDegree_num.le hM.natDegree_den hQ0 (by omega) (by omega) 1 (by simp)
  obtain ⟨A', B', hAB', hA', hB'⟩ := exists_bezout_natDegree_le (M := 2 * d) hM.coprime
    hM.natDegree_num.le hM.natDegree_den hQ0 (by omega) (by omega) (X ^ (2 * d))
    (natDegree_X_pow_le _)
  rw [show 2 * d - d = d by omega] at hA hB hA' hB'
  obtain ⟨D₁, hD₁, hD₁P⟩ := exists_clearsDen P
  obtain ⟨D₂, hD₂, hD₂Q⟩ := exists_clearsDen Q
  obtain ⟨D₃, hD₃, h₃⟩ := exists_clearsDen A
  obtain ⟨D₄, hD₄, h₄⟩ := exists_clearsDen B
  obtain ⟨D₅, hD₅, h₅⟩ := exists_clearsDen A'
  obtain ⟨D₆, hD₆, h₆⟩ := exists_clearsDen B'
  have hDP : ClearsDen (D₁ * D₂) P := hD₁P.mul_right D₂
  have hDQ : ClearsDen (D₁ * D₂) Q := hD₂Q.mul_left D₁
  have hDA : ClearsDen (D₃ * D₄ * D₅ * D₆) A := ((h₃.mul_right D₄).mul_right D₅).mul_right D₆
  have hDB : ClearsDen (D₃ * D₄ * D₅ * D₆) B := ((h₄.mul_left D₃).mul_right D₅).mul_right D₆
  have hDA' : ClearsDen (D₃ * D₄ * D₅ * D₆) A' := (h₅.mul_left (D₃ * D₄)).mul_right D₆
  have hDB' : ClearsDen (D₃ * D₄ * D₅ * D₆) B' := h₆.mul_left (D₃ * D₄ * D₅)
  set D := D₁ * D₂ with hDdef
  set D' := D₃ * D₄ * D₅ * D₆ with hD'def
  have hD : 0 < D := Nat.mul_pos hD₁ hD₂
  have hD' : 0 < D' := by positivity
  -- Limits.
  set α := alpha a b with hαdef
  set L := |aeval α Q * aeval α E| with hLdef
  have hL : 0 < L := abs_pos.mpr (mul_ne_zero hQα hEα)
  have hQE : Tendsto (fun n => |((Q.eval (uRatio a b n) : ℚ) : ℝ) *
      ((E.eval (uRatio a b n) : ℚ) : ℝ)|) atTop (𝓝 L) :=
    ((tendsto_aeval_uRatio hab Q).mul (tendsto_aeval_uRatio hab E)).abs
  have hPα : aeval α P = α ^ k * aeval α Q := by
    have h := congrArg (aeval α) hM.relation
    simp only [map_sub, map_mul, map_pow, aeval_X] at h
    rw [aeval_alpha_characteristicPolynomial hab, zero_pow (Nat.succ_ne_zero d), mul_zero] at h
    linear_combination -h
  have hr : Tendsto (fun n => (((P.eval (uRatio a b n) / Q.eval (uRatio a b n)) : ℚ) : ℝ))
      atTop (𝓝 (α ^ k)) := by
    have := (tendsto_aeval_uRatio hab P).div (tendsto_aeval_uRatio hab Q) hQα
    rw [hPα, mul_div_cancel_right₀ _ hQα] at this
    refine this.congr ?_
    intro n
    push_cast
    rfl
  have hαk : 1 < α ^ k := one_lt_pow₀ (one_lt_alpha hab) (by omega)
  obtain ⟨c₁, c₂, hc₁, hc₂, hu⟩ := eventually_u_sq_bounds hab
  -- `|ρ|^n = α^(2n) / |b|^n`.
  set β₀ : ℝ := |(b : ℝ)| with hβ₀
  have hβ₀1 : 1 ≤ β₀ := by
    rw [hβ₀]
    exact_mod_cast Int.one_le_abs hab.b_ne_zero
  have hρ (n : ℕ) : rhoAbs a b ^ n * β₀ ^ n = α ^ (2 * n) := by
    have hα0 : 0 < α := by linarith [one_lt_alpha hab]
    have hαβ : α * |beta a b| = β₀ := by
      have := congrArg abs (alpha_mul_beta hab)
      rw [abs_mul, abs_neg, abs_of_pos hα0] at this
      exact this
    have hβne : |beta a b| ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hαβ
      linarith
    rw [rhoAbs, abs_div, abs_of_pos hα0, ← hαβ, ← mul_pow, pow_mul]
    congr 1
    field_simp
  have hρpos (n : ℕ) : 0 < rhoAbs a b ^ n := by
    have := hρ n
    have : 0 < α ^ (2 * n) := pow_pos (by linarith [one_lt_alpha hab]) _
    by_contra h
    push_neg at h
    nlinarith [pow_pos (show (0 : ℝ) < β₀ by linarith) n]
  have hR : Tendsto (fun n => rhoAbs a b ^ n) atTop atTop := by
    have h1 : 1 < rhoAbs a b := by
      have := hρ 1
      rw [pow_one, pow_one, mul_one] at this
      have hab' := abs_beta_lt_alpha hab
      have hα0 : 0 < α := by linarith [one_lt_alpha hab]
      have hβ0 : beta a b ≠ 0 := by
        intro h0
        have := alpha_mul_beta hab
        rw [h0, mul_zero] at this
        exact hab.b_ne_zero (by exact_mod_cast (neg_eq_zero.mp this.symm))
      rw [rhoAbs, abs_div, abs_of_pos hα0]
      exact (one_lt_div (abs_pos.mpr hβ0)).mpr hab'
    exact tendsto_pow_atTop_atTop_of_one_lt h1
  set G : ℝ := ((D * D' : ℕ) : ℝ) * |((a * b : ℤ) : ℝ)| ^ (2 * d) with hGdef
  have hG : 1 ≤ G := by
    have h1 : (1 : ℝ) ≤ ((D * D' : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hD hD'
    have h2 : (1 : ℝ) ≤ |((a * b : ℤ) : ℝ)| ^ (2 * d) :=
      one_le_pow₀ (by exact_mod_cast Int.one_le_abs (mul_ne_zero hab.a_pos.ne' hab.b_ne_zero))
    nlinarith
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  set K₀ : ℝ := β₀ ^ (2 * d)
  have hK₀ : 1 ≤ K₀ := one_le_pow₀ hβ₀1
  refine hasMonsterTermsRate_of_estimates (fun n => rhoAbs a b ^ n) hR
    (c₁ / (2 * (D : ℝ) ^ 2 * L * K₀)) (2 * G ^ 2 * c₂ / ((D : ℝ) ^ 2 * L)) (by positivity)
    (by positivity) (fun n => P.eval (uRatio a b n) / Q.eval (uRatio a b n)) ?_
  filter_upwards [eventually_ge_atTop 1, hu, (tendsto_order.1 hQE).1 (L / 2) (by linarith),
    (tendsto_order.1 hQE).2 (2 * L) (by linarith), (tendsto_order.1 hr).1 1 hαk]
    with n hn hun hlo hhi hr1
  set x₀ := uRatio a b n with hxdef
  set F := |((Q.eval x₀ : ℚ) : ℝ) * ((E.eval x₀ : ℚ) : ℝ)| with hFdef
  have hF : 0 < F := by linarith
  have hQEx := abs_pos.mp hF
  have hQx : Q.eval x₀ ≠ 0 := by exact_mod_cast left_ne_zero_of_mul hQEx
  obtain ⟨e, s', t', x, y, hs, ht, hxy, he1, he2⟩ := exists_common_factor hab hn
  obtain ⟨g, hg0, hgle, hform⟩ := monster_closeness hab hM hAB hA hB hAB' hA' hB' hD hD'
    hDP hDQ hDA hDB hDA' hDB' hn hQx hs ht hxy
  have hun0 : (0 : ℝ) < (u a b n : ℝ) ^ 2 := by
    have := u_pos hab hn
    positivity
  have hg1 : (1 : ℝ) ≤ (g : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ g ^ 2 := by
      have := sq_abs g
      have h1 : 1 ≤ |g| := Int.one_le_abs hg0
      nlinarith
    exact_mod_cast this
  have hgG : (g : ℝ) ^ 2 ≤ G ^ 2 := by
    have h1 : (|g| : ℝ) ≤ G := by
      rw [hGdef]
      have : ((|g| : ℤ) : ℝ) ≤ (((D * D' : ℕ) * |a * b| ^ (2 * d) : ℤ) : ℝ) := by exact_mod_cast hgle
      push_cast at this ⊢
      exact this
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (by exact_mod_cast h1) 2
  -- `Z = e^(2d) / |b|^(nd) ∈ [1/K₀, 1]`.
  have he0 : e ≠ 0 := by
    rintro rfl
    have : (0 : ℤ) < u a b n := u_pos hab hn
    rw [ht, zero_mul] at this
    exact lt_irrefl _ this
  set Z : ℝ := (e : ℝ) ^ (2 * d) / β₀ ^ (n * d) with hZdef
  have hβn : 0 < β₀ ^ (n * d) := pow_pos (by linarith) _
  have he1R : (e : ℝ) ^ 2 ≤ β₀ ^ n := by
    have : ((e ^ 2 : ℤ) : ℝ) ≤ ((|b| ^ n : ℤ) : ℝ) := by exact_mod_cast he1
    push_cast at this
    exact this
  have he2R : β₀ ^ n ≤ (e : ℝ) ^ 2 * β₀ ^ 2 := by
    have : ((|b| ^ n : ℤ) : ℝ) ≤ ((e ^ 2 * b ^ 2 : ℤ) : ℝ) := by exact_mod_cast he2
    push_cast at this
    rw [hβ₀, sq_abs]
    exact this
  have hZ1 : Z ≤ 1 := by
    rw [hZdef, div_le_one hβn]
    calc (e : ℝ) ^ (2 * d) = ((e : ℝ) ^ 2) ^ d := pow_mul _ _ _
      _ ≤ (β₀ ^ n) ^ d := pow_le_pow_left₀ (sq_nonneg _) he1R d
      _ = β₀ ^ (n * d) := (pow_mul _ _ _).symm
  have hZ0 : 1 / K₀ ≤ Z := by
    rw [hZdef, div_le_div_iff₀ (by positivity) hβn, one_mul]
    calc β₀ ^ (n * d) = (β₀ ^ n) ^ d := pow_mul _ _ _
      _ ≤ ((e : ℝ) ^ 2 * β₀ ^ 2) ^ d := pow_le_pow_left₀ (by positivity) he2R d
      _ = (e : ℝ) ^ (2 * d) * K₀ := by rw [mul_pow, ← pow_mul, ← pow_mul]
  have hY : ((1 / ((((P.eval x₀ / Q.eval x₀).den : ℚ)) ^ 2 *
      |ratioPower a b k n - P.eval x₀ / Q.eval x₀|) : ℚ) : ℝ) =
      (g : ℝ) ^ 2 * Z * ((u a b n : ℝ) ^ 2 / α ^ (2 * n)) / ((D : ℝ) ^ 2 * F) *
        rhoAbs a b ^ n := by
    rw [hform]
    push_cast
    rw [one_div_div, hZdef, ← hρ n, ← hβ₀]
    have hβ0 : 0 < β₀ := by linarith
    rw [show β₀ ^ (n * (d + 1)) = β₀ ^ (n * d) * β₀ ^ n by rw [← pow_add]; ring_nf]
    have : (e : ℝ) ≠ 0 := by exact_mod_cast he0
    have hρ0 : rhoAbs a b ≠ 0 := by have := hρpos 1; rw [pow_one] at this; exact this.ne'
    have hFne : F ≠ 0 := hF.ne'
    rw [← hFdef]
    field_simp
  obtain ⟨hlo', hhi'⟩ := hun
  have hα2 : 0 < α ^ (2 * n) := pow_pos (by linarith [one_lt_alpha hab]) _
  have hW1 : c₁ ≤ (u a b n : ℝ) ^ 2 / α ^ (2 * n) := by rw [le_div_iff₀ hα2]; exact hlo'
  have hW2 : (u a b n : ℝ) ^ 2 / α ^ (2 * n) ≤ c₂ := by rw [div_le_iff₀ hα2]; exact hhi'
  have hρn := hρpos n
  refine ⟨by exact_mod_cast hr1, ?_, ?_, ?_⟩
  · intro heq
    rw [heq, sub_self, abs_zero, mul_zero] at hform
    have hpos : (0 : ℚ) < (D : ℚ) ^ 2 * |Q.eval x₀ * E.eval x₀| * |(b : ℚ)| ^ (n * (d + 1)) /
        ((g : ℚ) ^ 2 * (e : ℚ) ^ (2 * d) * (u a b n : ℚ) ^ 2) := by
      have hun' : (u a b n : ℚ) ≠ 0 := by exact_mod_cast (u_pos hab hn).ne'
      have hg' : (g : ℚ) ≠ 0 := by exact_mod_cast hg0
      have he' : (e : ℚ) ≠ 0 := by exact_mod_cast he0
      have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hab.b_ne_zero
      have hQE' : Q.eval x₀ * E.eval x₀ ≠ 0 := by exact_mod_cast hQEx
      have : (0 : ℚ) < (e : ℚ) ^ (2 * d) := by rw [pow_mul]; positivity
      positivity
    linarith
  · rw [hY]
    -- lower bound
    have hK : (0 : ℝ) < (D : ℝ) ^ 2 := by positivity
    have hZpos : 0 < Z := lt_of_lt_of_le (by positivity) hZ0
    have h1 : c₁ / (2 * (D : ℝ) ^ 2 * L * K₀) ≤ (g : ℝ) ^ 2 * Z * ((u a b n : ℝ) ^ 2 / α ^ (2 * n)) /
        ((D : ℝ) ^ 2 * F) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have e1 : (1 / K₀) * c₁ ≤ Z * ((u a b n : ℝ) ^ 2 / α ^ (2 * n)) :=
        mul_le_mul hZ0 hW1 hc₁.le hZpos.le
      have e2 : Z * ((u a b n : ℝ) ^ 2 / α ^ (2 * n)) ≤
          (g : ℝ) ^ 2 * Z * ((u a b n : ℝ) ^ 2 / α ^ (2 * n)) := by
        rw [mul_assoc]
        exact le_mul_of_one_le_left (by positivity) hg1
      have e3 : c₁ * ((D : ℝ) ^ 2 * F) ≤ c₁ * ((D : ℝ) ^ 2 * (2 * L)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hK.le) hc₁.le
      have e4 : (1 / K₀) * c₁ * (2 * (D : ℝ) ^ 2 * L * K₀) = c₁ * ((D : ℝ) ^ 2 * (2 * L)) := by
        have : K₀ ≠ 0 := by positivity
        field_simp
      calc c₁ * ((D : ℝ) ^ 2 * F) ≤ c₁ * ((D : ℝ) ^ 2 * (2 * L)) := e3
        _ = (1 / K₀) * c₁ * (2 * (D : ℝ) ^ 2 * L * K₀) := e4.symm
        _ ≤ (Z * ((u a b n : ℝ) ^ 2 / α ^ (2 * n))) * (2 * (D : ℝ) ^ 2 * L * K₀) :=
          mul_le_mul_of_nonneg_right e1 (by positivity)
        _ ≤ ((g : ℝ) ^ 2 * Z * ((u a b n : ℝ) ^ 2 / α ^ (2 * n))) * (2 * (D : ℝ) ^ 2 * L * K₀) :=
          mul_le_mul_of_nonneg_right e2 (by positivity)
    exact mul_le_mul_of_nonneg_right h1 hρn.le
  · rw [hY]
    have hK : (0 : ℝ) < (D : ℝ) ^ 2 := by positivity
    have hZpos : 0 < Z := lt_of_lt_of_le (by positivity) hZ0
    have h1 : (g : ℝ) ^ 2 * Z * ((u a b n : ℝ) ^ 2 / α ^ (2 * n)) / ((D : ℝ) ^ 2 * F) ≤
        2 * G ^ 2 * c₂ / ((D : ℝ) ^ 2 * L) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have e1 : (g : ℝ) ^ 2 * Z * ((u a b n : ℝ) ^ 2 / α ^ (2 * n)) ≤ G ^ 2 * 1 * c₂ :=
        mul_le_mul (mul_le_mul hgG hZ1 hZpos.le (by positivity)) hW2
          (div_nonneg (sq_nonneg _) hα2.le) (by positivity)
      have e2 : (D : ℝ) ^ 2 * L ≤ (D : ℝ) ^ 2 * (2 * F) :=
        mul_le_mul_of_nonneg_left (by linarith) hK.le
      calc (g : ℝ) ^ 2 * Z * ((u a b n : ℝ) ^ 2 / α ^ (2 * n)) * ((D : ℝ) ^ 2 * L)
          ≤ (G ^ 2 * 1 * c₂) * ((D : ℝ) ^ 2 * L) := mul_le_mul_of_nonneg_right e1 (by positivity)
        _ ≤ (G ^ 2 * 1 * c₂) * ((D : ℝ) ^ 2 * (2 * F)) := mul_le_mul_of_nonneg_left e2 (by positivity)
        _ = 2 * G ^ 2 * c₂ * ((D : ℝ) ^ 2 * F) := by ring
    exact mul_le_mul_of_nonneg_right h1 hρn.le

/-- For `b = ±1`, `|ρ| = α^2`. -/
theorem rhoAbs_pow_of_admissible (hab : Admissible a b) (n : ℕ) :
    rhoAbs a b ^ n = alpha a b ^ (2 * n) := by
  have hα0 : 0 < alpha a b := by linarith [one_lt_alpha hab.gen]
  have hαβ : alpha a b * |beta a b| = 1 := by
    have := congrArg abs (alpha_mul_beta hab.gen)
    rw [abs_mul, abs_neg, abs_of_pos hα0] at this
    rw [this]
    rcases hab.1 with h | h <;> simp [h]
  have hβ : |beta a b| = (alpha a b)⁻¹ := eq_inv_of_mul_eq_one_right hαβ
  rw [rhoAbs, abs_div, abs_of_pos hα0, hβ, div_inv_eq_mul, ← sq, ← pow_mul]

/-- **Theorem 1.2(a).** If some Padé–Toeplitz determinant vanishes, then for
all large `n` the continued fraction of `(u_(n+1)/u_n)^k` has a term of exact
order `α^(2n)`. -/
theorem hasMonsterTerms_of_delta_eq_zero (hab : Admissible a b) {k : ℕ} (hk : 1 ≤ k)
    (hz : ∃ i, i ≤ k ∧ delta a b k i = 0) : HasMonsterTerms a b k := by
  have h := hasMonsterTermsRate_of_delta_eq_zero hab.gen hk hz
  rw [hasMonsterTerms_iff_rate]
  simpa only [rhoAbs_pow_of_admissible hab] using h

end TwoPoint
