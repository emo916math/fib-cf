module

public import TwoPoint.MonsterCF
public import TwoPoint.GenDecomposition
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Estimates for the monster terms

Auxiliary results for Theorem 1.2(a): clearing denominators in homogeneous
evaluations, the gcd bound coming from coprime consecutive recurrence terms,
the Binet asymptotics `u_(n+1)/u_n → α` and `u_n^2 ≍ α^(2n)`, and the reduction
of `HasMonsterTerms` to two-sided estimates of `1 / (den(r)^2 |x - r|)`.
-/

@[expose] public section
noncomputable section

namespace TwoPoint

open Polynomial Filter Topology

/-! ## Clearing denominators -/

/-- `D` times every coefficient of `f` is an integer. -/
def ClearsDen (D : ℕ) (f : ℚ[X]) : Prop :=
  ∀ i, ∃ z : ℤ, (D : ℚ) * f.coeff i = z

theorem exists_clearsDen (f : ℚ[X]) : ∃ D : ℕ, 0 < D ∧ ClearsDen D f := by
  classical
  refine ⟨∏ i ∈ f.support, (f.coeff i).den,
    Finset.prod_pos (fun i _ => (f.coeff i).den_pos), ?_⟩
  intro i
  by_cases hi : i ∈ f.support
  · obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun j => (f.coeff j).den) hi
    refine ⟨m * (f.coeff i).num, ?_⟩
    rw [hm]
    push_cast
    rw [← Rat.mul_den_eq_num]
    ring
  · refine ⟨0, ?_⟩
    rw [notMem_support_iff.mp hi]
    simp

theorem ClearsDen.mul_left {D : ℕ} {f : ℚ[X]} (h : ClearsDen D f) (D' : ℕ) :
    ClearsDen (D' * D) f := by
  intro i
  obtain ⟨z, hz⟩ := h i
  exact ⟨D' * z, by push_cast; rw [mul_assoc, hz]⟩

theorem ClearsDen.mul_right {D : ℕ} {f : ℚ[X]} (h : ClearsDen D f) (D' : ℕ) :
    ClearsDen (D * D') f := by
  rw [mul_comm]
  exact h.mul_left D'

/-- The homogeneous value `D t^m f(s/t)` at integers is an integer. -/
theorem ClearsDen.exists_int_hom {D : ℕ} {f : ℚ[X]} (hf : ClearsDen D f) {m : ℕ}
    (hm : f.natDegree ≤ m) (s t : ℤ) (ht : t ≠ 0) :
    ∃ z : ℤ, (z : ℚ) = D * (t : ℚ) ^ m * f.eval ((s : ℚ) / t) := by
  choose c hc using hf
  refine ⟨∑ i ∈ Finset.range (m + 1), c i * s ^ i * t ^ (m - i), ?_⟩
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hm), Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [← hc i]
  have htq : (t : ℚ) ≠ 0 := by exact_mod_cast ht
  have hsplit : (t : ℚ) ^ m = t ^ i * t ^ (m - i) := by
    rw [← pow_add, Nat.add_sub_cancel' hi']
  rw [hsplit, div_pow]
  field_simp

/-! ## Gcd bounds -/

theorem int_dvd_of_dvd_mul_pow {g c s t : ℤ} {N : ℕ} (hst : IsCoprime s t)
    (hs : g ∣ c * s ^ N) (ht : g ∣ c * t ^ N) : g ∣ c := by
  obtain ⟨x, y, hxy⟩ := hst.pow (m := N) (n := N)
  have : c = x * (c * s ^ N) + y * (c * t ^ N) := by linear_combination (-c) * hxy
  rw [this]
  exact dvd_add (dvd_mul_of_dvd_right hs _) (dvd_mul_of_dvd_right ht _)

theorem u_isCoprime_succ (a b : ℤ) (hb : b ^ 2 = 1) (n : ℕ) :
    IsCoprime (u a b (n + 1)) (u a b n) := by
  have h := u_norm a b n
  have hu : ((-b) ^ n) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_sq, hb, one_pow]
  refine ⟨(-b) ^ n * (u a b (n + 1) - a * u a b n), (-b) ^ n * (-b * u a b n), ?_⟩
  linear_combination ((-b) ^ n) * h + hu

/-- Writing `p/q = num/den`, the cancelled common factor `g = q/den` divides
both `p` and `q`. -/
theorem exists_den_mul_eq (p q : ℤ) (hq : q ≠ 0) :
    ∃ g : ℤ, g ∣ p ∧ g ∣ q ∧ (((p : ℚ) / q).den : ℤ) * g = q := by
  set r : ℚ := (p : ℚ) / q with hrdef
  have hdvd : (r.den : ℤ) ∣ q := by
    have := Rat.den_dvd p q
    rwa [← Rat.intCast_div_eq_divInt] at this
  obtain ⟨g, hg⟩ := hdvd
  refine ⟨g, ?_, ⟨r.den, by rw [hg]; ring⟩, hg.symm⟩
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq
  have h1 : (p : ℚ) = r * q := by rw [hrdef]; field_simp
  have hgq : (q : ℚ) = r.den * g := by exact_mod_cast hg
  have h2 : (p : ℚ) = g * r.num := by
    rw [h1, hgq, ← mul_assoc, Rat.mul_den_eq_num, mul_comm]
  exact ⟨r.num, by exact_mod_cast h2⟩

/-! ## Binet asymptotics -/

variable {a b : ℤ}

/-- `|β| < α`: the root `α` is dominant. -/
theorem abs_beta_lt_alpha (hab : GenAdmissible a b) : |beta a b| < alpha a b := by
  have hs := Real.sq_sqrt (le_of_lt hab.discriminant_pos)
  have hpos := Real.sqrt_pos.mpr hab.discriminant_pos
  have ha : (0 : ℝ) < a := by exact_mod_cast hab.a_pos
  rw [abs_lt]
  unfold beta alpha
  constructor <;> linarith

theorem alpha_sub_beta_pos (hab : GenAdmissible a b) : 0 < alpha a b - beta a b := by
  have := (abs_lt.mp (abs_beta_lt_alpha hab)).2
  linarith

/-- `|β/α| < 1`. -/
theorem abs_beta_div_alpha_lt_one (hab : GenAdmissible a b) : |beta a b / alpha a b| < 1 := by
  have hα0 : (0 : ℝ) < alpha a b := by linarith [one_lt_alpha hab]
  rw [abs_div, abs_of_pos hα0, div_lt_one hα0]
  exact abs_beta_lt_alpha hab

theorem tendsto_u_ratio (hab : GenAdmissible a b) :
    Tendsto (fun n => (u a b (n + 1) : ℝ) / u a b n) atTop (𝓝 (alpha a b)) := by
  set α := alpha a b with hαdef
  set β := beta a b with hβdef
  have hα : 1 < α := one_lt_alpha hab
  set ρ := β / α with hρdef
  have hρ : |ρ| < 1 := abs_beta_div_alpha_lt_one hab
  have hp := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hρ
  have hlim : Tendsto (fun n : ℕ => (α - β * ρ ^ n) / (1 - ρ ^ n)) atTop
      (𝓝 ((α - β * 0) / (1 - 0))) :=
    (tendsto_const_nhds.sub (tendsto_const_nhds.mul hp)).div
      (tendsto_const_nhds.sub hp) (by norm_num)
  rw [mul_zero, sub_zero, sub_zero, div_one] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hδ : α - β ≠ 0 := (alpha_sub_beta_pos hab).ne'
  have hρn : ρ ^ n ≠ 1 := by
    intro h
    have h' := congrArg abs h
    rw [abs_pow, abs_one] at h'
    exact absurd h' (ne_of_lt (pow_lt_one₀ (abs_nonneg _) hρ (by omega)))
  have hαn : α ^ n ≠ 0 := pow_ne_zero _ (by linarith)
  have hβn : β ^ n = ρ ^ n * α ^ n := by rw [hρdef, div_pow, div_mul_cancel₀ _ hαn]
  have hun : (u a b n : ℝ) = (α ^ n - β ^ n) / (α - β) := by
    rw [← u_mul_root_difference hab n, mul_div_cancel_right₀ _ hδ]
  have hun1 : (u a b (n + 1) : ℝ) = (α ^ (n + 1) - β ^ (n + 1)) / (α - β) := by
    rw [← u_mul_root_difference hab (n + 1), mul_div_cancel_right₀ _ hδ]
  have h1 : 1 - ρ ^ n ≠ 0 := sub_ne_zero.mpr (Ne.symm hρn)
  rw [hun, hun1, pow_succ, pow_succ, hβn]
  field_simp

theorem eventually_u_sq_bounds (hab : GenAdmissible a b) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ n in atTop,
      c₁ * alpha a b ^ (2 * n) ≤ (u a b n : ℝ) ^ 2 ∧
      (u a b n : ℝ) ^ 2 ≤ c₂ * alpha a b ^ (2 * n) := by
  set δ := alpha a b - beta a b with hδdef
  have hδ : 0 < δ := alpha_sub_beta_pos hab
  refine ⟨1 / (4 * δ ^ 2), 4 / δ ^ 2, by positivity, by positivity, ?_⟩
  have hα0 : (0 : ℝ) < alpha a b := by linarith [one_lt_alpha hab]
  have hρ := tendsto_pow_atTop_nhds_zero_of_abs_lt_one (abs_beta_div_alpha_lt_one hab)
  filter_upwards [(tendsto_order.1 hρ.abs).2 (1 / 2) (by norm_num)] with n hn
  have hβn : |beta a b ^ n| ≤ alpha a b ^ n / 2 := by
    rw [div_pow, abs_div, abs_of_pos (pow_pos hα0 n)] at hn
    rw [le_div_iff₀ (by norm_num)]
    have := (div_lt_iff₀ (pow_pos hα0 n)).mp hn
    linarith
  have hβn' := abs_le.mp hβn
  have hαn : 0 < alpha a b ^ n := pow_pos hα0 n
  have hu := u_mul_root_difference hab n
  rw [← hδdef] at hu
  have hlo : alpha a b ^ n / (2 * δ) ≤ u a b n := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hhi : (u a b n : ℝ) ≤ 2 * alpha a b ^ n / δ := by
    rw [le_div_iff₀ hδ]
    linarith
  have hA : 0 ≤ alpha a b ^ n / (2 * δ) := by positivity
  have hsq : alpha a b ^ (2 * n) = (alpha a b ^ n) ^ 2 := by rw [mul_comm, pow_mul]
  rw [hsq]
  constructor
  · have := pow_le_pow_left₀ hA hlo 2
    calc 1 / (4 * δ ^ 2) * (alpha a b ^ n) ^ 2 = (alpha a b ^ n / (2 * δ)) ^ 2 := by
          field_simp
          ring
      _ ≤ _ := this
  · have := pow_le_pow_left₀ (le_trans hA hlo) hhi 2
    calc (u a b n : ℝ) ^ 2 ≤ (2 * alpha a b ^ n / δ) ^ 2 := this
      _ = 4 / δ ^ 2 * (alpha a b ^ n) ^ 2 := by field_simp; ring

theorem tendsto_alpha_pow_two_mul (hab : GenAdmissible a b) :
    Tendsto (fun n : ℕ => alpha a b ^ (2 * n)) atTop atTop := by
  have h1 : 1 < alpha a b ^ 2 := by nlinarith [one_lt_alpha hab]
  simpa [pow_mul] using tendsto_pow_atTop_atTop_of_one_lt h1

/-! ## Reduction to estimates -/

/-- `HasMonsterTermsRate … R` follows from close rational approximations `r_n`
whose closeness `1 / (den(r_n)^2 |x_n - r_n|)` is of exact order `R n → ∞`. -/
theorem hasMonsterTermsRate_of_estimates {k : ℕ} (R : ℕ → ℝ) (hR : Tendsto R atTop atTop)
    (c₀ C₀ : ℝ) (hc₀ : 0 < c₀) (hC₀ : 0 < C₀) (r : ℕ → ℚ)
    (hev : ∀ᶠ n in atTop, 1 < r n ∧ ratioPower a b k n ≠ r n ∧
      c₀ * R n ≤
        ((1 / (((r n).den : ℚ) ^ 2 * |ratioPower a b k n - r n|) : ℚ) : ℝ) ∧
      ((1 / (((r n).den : ℚ) ^ 2 * |ratioPower a b k n - r n|) : ℚ) : ℝ) ≤
        C₀ * R n) :
    HasMonsterTermsRate a b k R := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hev.and (hR.eventually_ge_atTop (4 / c₀)))
  refine ⟨c₀ / 2, C₀, by positivity, hC₀, max N₀ 1, le_max_right _ _, ?_⟩
  intro n hn
  obtain ⟨⟨hr1, hne, hlo, hhi⟩, hbig⟩ := hN₀ n (le_of_max_le_left hn)
  set Y : ℚ := 1 / (((r n).den : ℚ) ^ 2 * |ratioPower a b k n - r n|) with hYdef
  have h4 : 4 ≤ c₀ * R n := by
    have := mul_le_mul_of_nonneg_left hbig hc₀.le
    rwa [mul_div_cancel₀ _ hc₀.ne'] at this
  have hY2 : (2 : ℚ) ≤ Y := by
    have : (2 : ℝ) ≤ (Y : ℝ) := by linarith
    exact_mod_cast this
  obtain ⟨w, hw, M, hM, hMlo, hMhi⟩ := exists_cf_with_large_term _ _ hr1 hne hY2
  refine ⟨w, hw, M, hM, ?_, ?_⟩
  · have : ((Y - 2 : ℚ) : ℝ) ≤ ((M : ℚ) : ℝ) := by exact_mod_cast hMlo
    push_cast at this
    linarith
  · have : ((M : ℚ) : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hMhi
    push_cast at this
    linarith

end TwoPoint
