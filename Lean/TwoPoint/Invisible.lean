module

public import TwoPoint.GenFinal
public import TwoPoint.InvisibleAlgebra

/-!
# Exercise `exer:invisible`: invisible junctions

For `0 < i < k`, `Υ_{k,i}(α) = 0` exactly when `ξ_i = ξ_(i-1)` (`InvisibleAlgebra`).
In that case the points `η_(i-1)(n)` and `η_i(n)` coincide for every `n`, so
the construction (with representatives chosen per `GL₂(ℤ)`-class) gives equal
patches `P_(i-1,n) = P_(i,n)` and the half-junction `H⁺_(i,n) = H⁻_(i-1,n)`,
hence the empty junction `J_(i,n)`. Conversely:

* in the constructed decomposition, visible junctions are nonempty words, so
  an empty `J_(i,n)` forces `Υ_{k,i}(α) = 0`;
* independently of the normalization, if the half-junctions `H₁, H₂` carry one
  reduced point `σ` (the common patch) to `η_(i-1)(n)` and `η_i(n)`, and some
  renormalized junction `±P^(y₁) H₁⁻¹ H₂ P^(y₂)` with `P` in the stabilizer of
  `σ` is the empty word, then `Υ_{k,i}(α) = 0`.
-/

@[expose] public section
noncomputable section

namespace TwoPoint

namespace Ctx

variable (C : Ctx)

theorem invisible_iff {i : ℕ} (hi0 : 0 < i) (hik : i < C.k) :
    C.Invisible i ↔ upsilon C.a C.b C.k i = 0 := by
  rw [C.upsilon_eq_zero_iff hi0 hik]
  exact ⟨fun h => h.2.2, fun h => ⟨hi0, hik, h⟩⟩

/-- Equal points `η_(i-1)(n) = η_i(n)` force `ξ_(i-1) = ξ_i`. -/
theorem xi_eq_of_eta_eq {i : ℕ} (hi0 : 0 < i) (hik : i < C.k) {n : ℕ}
    (h : C.eta i n = C.eta (i - 1) n) : C.xi i = C.xi (i - 1) := by
  have hj : i - 1 < C.k := by omega
  have hs := (C.eta_succ hj n).1
  rw [show i - 1 + 1 = i by omega] at hs
  rw [hs, eta] at h
  exact mob_injective (C.U_det_ne_zero hik.le n)
    (C.mobDen_U_ne_zero hik.le n (C.xi_pair hik).irrational)
    (C.mobDen_U_ne_zero hik.le n (C.xi_pair hj).irrational) h

/-- **Exercise `exer:invisible`, converse, for any normalization.** If two
half-junctions `H₁, H₂` carry a common point `σ` (the shared patch) to
`η_(i-1)(n)` and `η_i(n)`, and a renormalized junction `s P^(y₁) H₁⁻¹ H₂ P^(y₂)`
(`s = ±1`, `P` fixing `σ`) is the empty word, then `Υ_{k,i}(α) = 0`. -/
theorem upsilon_eq_zero_of_empty_junction {i : ℕ} (hi0 : 0 < i) (hik : i < C.k) (n : ℕ)
    {σ : ℝ} (hσ : Irrational σ) {P H₁ H₂ s : GL2Z} (hP : P ∈ stab σ hσ) (hs : IsSign s)
    (y₁ y₂ : ℤ) (h₁ : mob (intToReal H₁) σ = C.eta (i - 1) n)
    (h₂ : mob (intToReal H₂) σ = C.eta i n) (hJ : s * P ^ y₁ * (H₁⁻¹ * H₂) * P ^ y₂ = 1) :
    upsilon C.a C.b C.k i = 0 := by
  rw [← C.invisible_iff hi0 hik]
  refine ⟨hi0, hik, C.xi_eq_of_eta_eq hi0 hik (n := n) ?_⟩
  -- `H₂ = H₁ Z` with `Z = s P^(-(y₁+y₂))` fixing `σ`.
  have e : H₂ = H₁ * (P ^ y₁)⁻¹ * s⁻¹ * (P ^ y₂)⁻¹ := by
    have := congrArg (fun X => H₁ * (P ^ y₁)⁻¹ * s⁻¹ * X * (P ^ y₂)⁻¹) hJ
    simp only [mul_one] at this
    rw [← this]
    group
  have hZ : H₂ = H₁ * (s * P ^ (-(y₁ + y₂))) := by
    rw [e]
    rcases hs with rfl | rfl
    · group
    · rw [show ((-1 : GL2Z))⁻¹ = -1 by simp, mul_assoc, mul_assoc]
      congr 1
      simp only [neg_one_mul, mul_neg]
      congr 1
      rw [← zpow_neg, ← zpow_neg, ← zpow_add, neg_add]
  have hPσ : mob (intToReal ((P ^ (-(y₁ + y₂)) : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ)) σ = σ :=
    mem_stab.mp ((stab σ hσ).zpow_mem hP _)
  have hZσ : mob (intToReal ((s * P ^ (-(y₁ + y₂)) : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ)) σ = σ := by
    rcases hs with rfl | rfl
    · rw [one_mul]; exact hPσ
    · rw [neg_one_mul, Units.val_neg, intToReal_neg, mob_neg]; exact hPσ
  rw [← h₂, ← h₁, hZ, Units.val_mul, intToReal_mul,
    mob_mul _ _ _ (mobDen_GL2Z_ne_zero hσ _), hZσ]

/-- The decomposition in the fixed setting, with its invisible junctions
characterized by `Υ_{k,i}(α)`. -/
theorem exists_invisible_dataMod : ∃ D : PatchJunctionData,
    D.IsDecompositionMod C.a C.b C.k C.m ∧ D.J C.k 0 = [] ∧
    ∀ i : ℕ, 0 < i → i < C.k →
      (upsilon C.a C.b C.k i = 0 ↔
        (∀ r : ℕ, D.J i r = []) ∧ ∀ n : ℕ, D.P (i - 1) (n % D.g (i - 1)) = D.P i (n % D.g i)) ∧
      ((∃ n : ℕ, D.J i (n % D.m i) = [] ∧
          D.P (i - 1) (n % D.g (i - 1)) = D.P i (n % D.g i)) → upsilon C.a C.b C.k i = 0) := by
  obtain ⟨D, hD, hJ0, hinv, hvis⟩ := C.exists_dataMod
  refine ⟨D, hD, hJ0, fun i hi0 hik => ⟨⟨fun h => hinv i ((C.invisible_iff hi0 hik).mpr h),
    fun h => (C.invisible_iff hi0 hik).mp (hvis i hi0 hik 0 (h.1 0))⟩, ?_⟩⟩
  rintro ⟨n, hJ, -⟩
  exact (C.invisible_iff hi0 hik).mp (hvis i hi0 hik _ hJ)

end Ctx

/-- **Exercise `exer:invisible`** (in the setting of Exercise `exer:main_gen`).
If all `Δ_{k,i}(a,b) ≠ 0`, the patch-junction decomposition of Exercise
`exer:main_gen`(b), (c) can be normalized so that, for every `0 < i < k`:

* if `Υ_{k,i}(α) = 0`, then `J_(i,n)` is the empty word and `P_(i-1,n) = P_(i,n)`
  for all `n` (and conversely);
* if `J_(i,n) = ∅` and `P_(i-1,n) = P_(i,n)` for some `n`, then `Υ_{k,i}(α) = 0`.

See also `Ctx.upsilon_eq_zero_of_empty_junction` for the converse under any
renormalization of the half-junctions. -/
theorem exer_invisible (a b : ℤ) (k : ℕ) (hab : GenAdmissible a b) (hk : 1 ≤ k)
    (hdelta : ∀ i : ℕ, i ≤ k → delta a b k i ≠ 0) :
    ∃ m : ℕ → ℕ, m 0 = 1 ∧
      (∀ i : ℕ, 1 ≤ i → i ≤ k → ∀ B : NormalizedPadeBasis (a : ℚ) (b : ℚ) k i,
        m i = exerModulus a b B.matrix i) ∧
      ∃ D : PatchJunctionData, D.IsDecompositionMod a b k m ∧
        ∀ i : ℕ, 0 < i → i < k →
          (upsilon a b k i = 0 ↔
            (∀ r : ℕ, D.J i r = []) ∧
              ∀ n : ℕ, D.P (i - 1) (n % D.g (i - 1)) = D.P i (n % D.g i)) ∧
          ((∃ n : ℕ, D.J i (n % D.m i) = [] ∧
              D.P (i - 1) (n % D.g (i - 1)) = D.P i (n % D.g i)) → upsilon a b k i = 0) := by
  obtain ⟨C, rfl, rfl, rfl, h0, hm⟩ := exists_ctx_of_gen hab hk hdelta
  obtain ⟨D, hD, -, hinv⟩ := C.exists_invisible_dataMod
  exact ⟨C.m, h0, hm, D, hD, hinv⟩

/-- **Exercise `exer:invisible`** for the decomposition of Theorem 1.2(b)
(`b = ±1`, moduli the ranks of apparition of `Δ_{k,i}`). For instance
`Υ_{4,3}(α) = 0` when `a^2 = b`, giving the invisible junction of `(F_(n+1)/F_n)^4`. -/
theorem theorem_1_2_invisible (a b : ℤ) (k : ℕ) (hab : Admissible a b) (hk : 1 ≤ k)
    (hdelta : ∀ i : ℕ, i ≤ k → delta a b k i ≠ 0) :
    ∃ D : PatchJunctionData, D.IsDecomposition a b k ∧
      ∀ i : ℕ, 0 < i → i < k →
        (upsilon a b k i = 0 ↔
          (∀ r : ℕ, D.J i r = []) ∧
            ∀ n : ℕ, D.P (i - 1) (n % D.g (i - 1)) = D.P i (n % D.g i)) ∧
        ((∃ n : ℕ, D.J i (n % D.m i) = [] ∧
            D.P (i - 1) (n % D.g (i - 1)) = D.P i (n % D.g i)) → upsilon a b k i = 0) := by
  obtain ⟨C, rfl, rfl, rfl, hm⟩ := exists_ctx_of_admissible hab hk hdelta
  obtain ⟨D, hD, hJ0, hinv⟩ := C.exists_invisible_dataMod
  exact ⟨D, C.isDecomposition_of_ranks hm hD hJ0, hinv⟩

end TwoPoint
