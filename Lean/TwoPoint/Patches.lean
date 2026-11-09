module

public import TwoPoint.Setup2

/-!
# Ranks, reduced representatives, half-junctions, and middle matrices

For `i < k` and a residue `ρ` modulo `g_i = gcd(m_i, m_(i+1))`, the pair
`(η_i(ρ), η'_i(ρ))` is reduced to `(σ, σ')`. Half-junctions `H⁺`, `H⁻` map
`σ` to `η_i(ν)` for residues `ν` modulo `m_i`, `m_(i+1)` respectively. The
middle matrix `X_i(n) = H⁺⁻¹ U_i(ν⁺) T_i^n U_(i+1)(ν⁻)⁻¹ H⁻` is integral, fixes
`σ`, and its eigenvalue at `σ` is `c · α^n` with `c` depending only on residues.
-/

@[expose] public section
noncomputable section

namespace TwoPoint

theorem u_dvd_u_mul (a b : ℤ) (m t : ℕ) : u a b m ∣ u a b (m * t) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h := u_add_modEq a b m (m * t)
    rw [show m * (t + 1) = m * t + m by ring]
    exact (Int.ModEq.dvd h.symm).elim fun c hc => by
      have : u a b (m * t + m) = u a b (m + 1) * u a b (m * t) + u a b m * c := by linarith
      rw [this]
      exact dvd_add (dvd_mul_of_dvd_right ih _) (dvd_mul_right _ _)

namespace Ctx

variable (C : Ctx)

/-! ## Moduli -/

/-- `g_i = gcd(m_i, m_(i+1))`. -/
def g (i : ℕ) : ℕ := Nat.gcd (C.m i) (C.m (i + 1))

/-- `L_i = lcm(m_i, m_(i+1))`. -/
def L (i : ℕ) : ℕ := Nat.lcm (C.m i) (C.m (i + 1))

theorem g_pos (i : ℕ) : 0 < C.g i := Nat.gcd_pos_of_pos_left _ (C.m_pos i)

theorem L_pos (i : ℕ) : 0 < C.L i := Nat.lcm_pos (C.m_pos i) (C.m_pos (i + 1))

/-! ## The classes of `η` modulo `g_i` -/

theorem eta_irr {i : ℕ} (hi : i < C.k) (n : ℕ) :
    Irrational (C.eta i n) ∧ Irrational (C.eta' i n) :=
  ⟨(C.eta_pair hi n).irrational, (C.eta_pair hi n).irrational'⟩

theorem eta_rel {i : ℕ} (hi : i < C.k) {n n' : ℕ} (h : n ≡ n' [MOD C.g i]) :
    PairRel (C.eta i n) (C.eta' i n) (C.eta i n') (C.eta' i n') := by
  apply pairRel_of_modEq (C.eta_irr hi) _ _ h
  · intro n
    obtain ⟨G, h1, h2⟩ := C.eta_transport hi 1 n
    rw [mul_one] at h1 h2
    exact ⟨G, h1, h2⟩
  · intro n
    obtain ⟨G, h1, h2⟩ := C.eta_transport' hi 1 n
    rw [mul_one] at h1 h2
    exact ⟨G, h1, h2⟩

/-! ## Reduced representatives

The reduced representative of the class of `(η_i(ρ), η'_i(ρ))` is chosen as a
function of the `GL₂(ℤ)`-orbit of the pair, so that equal classes (for
instance at an invisible junction) receive equal representatives. The orbit of
the last pair `(ξ_(k-1), ξ'_(k-1))` is represented by the special reduction
`x ↦ εx - t`, which fixes `∞`. -/

/-- The `GL₂(ℤ)`-orbit of a pair of points. -/
def orbitPair (x x' : ℝ) : Set (ℝ × ℝ) := {p | PairRel x x' p.1 p.2}

/-- `p` is a reduced pair: `p.1 > 1` and `-1 < p.2 < 0`. -/
def IsReducedPair (p : ℝ × ℝ) : Prop := 1 < p.1 ∧ -1 < p.2 ∧ p.2 < 0

theorem orbitPair_eq {x x' y y' : ℝ} (hx : Irrational x) (hx' : Irrational x')
    (h : PairRel x x' y y') : orbitPair x x' = orbitPair y y' := by
  obtain ⟨H, h1, h2⟩ := h
  have hy : Irrational y := h1 ▸ irrational_mob (IsRatMat.intToReal _) H.det_real_ne_zero hx
  have hy' : Irrational y' := h2 ▸ irrational_mob (IsRatMat.intToReal _) H.det_real_ne_zero hx'
  ext p
  constructor
  · intro hp
    exact (PairRel.symm hx hx' ⟨H, h1, h2⟩).trans hy hy' hp
  · intro hp
    exact PairRel.trans hx hx' ⟨H, h1, h2⟩ hp

/-- The special reduced pair representing the class of `(ξ_(k-1), ξ'_(k-1))`. -/
def lastPair : ℝ × ℝ :=
  (mob (intToReal ((Classical.choose C.exists_last_reduction : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ))
      (C.xi (C.k - 1)),
    mob (intToReal ((Classical.choose C.exists_last_reduction : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ))
      (C.xi' (C.k - 1)))

open scoped Classical in
/-- The chosen reduced pair of an orbit. -/
def classRep (S : Set (ℝ × ℝ)) : ℝ × ℝ :=
  if S = orbitPair (C.xi (C.k - 1)) (C.xi' (C.k - 1)) then C.lastPair
  else if h : ∃ p ∈ S, IsReducedPair p then Classical.choose h else (0, 0)

theorem lastPair_reduced : IsReducedPair C.lastPair := by
  obtain ⟨-, -, h1, h2, h3⟩ := Classical.choose_spec C.exists_last_reduction
  exact ⟨h1, h2, h3⟩

theorem lastPair_mem : C.lastPair ∈ orbitPair (C.xi (C.k - 1)) (C.xi' (C.k - 1)) :=
  ⟨Classical.choose C.exists_last_reduction, rfl, rfl⟩

theorem classRep_spec {S : Set (ℝ × ℝ)} (h : ∃ p ∈ S, IsReducedPair p) :
    C.classRep S ∈ S ∧ IsReducedPair (C.classRep S) := by
  unfold classRep
  split_ifs with hS
  · subst hS
    exact ⟨C.lastPair_mem, C.lastPair_reduced⟩
  · exact Classical.choose_spec h

theorem exists_reduced_mem {i : ℕ} (hi : i < C.k) (ρ : ℕ) :
    ∃ p ∈ orbitPair (C.eta i ρ) (C.eta' i ρ), IsReducedPair p := by
  obtain ⟨K, h1, h2, h3⟩ := exists_reduction (C.eta_pair hi ρ)
  exact ⟨(mob (intToReal K) (C.eta i ρ), mob (intToReal K) (C.eta' i ρ)), ⟨K, rfl, rfl⟩,
    h1, h2, h3⟩

theorem exists_canonical_reduction {i : ℕ} (hi : i < C.k) (ρ : ℕ) :
    ∃ K : GL2Z, mob (intToReal K) (C.eta i ρ) =
        (C.classRep (orbitPair (C.eta i ρ) (C.eta' i ρ))).1 ∧
      mob (intToReal K) (C.eta' i ρ) = (C.classRep (orbitPair (C.eta i ρ) (C.eta' i ρ))).2 :=
  (C.classRep_spec (C.exists_reduced_mem hi ρ)).1

/-- The reducing matrix for `(η_i(ρ), η'_i(ρ))`; for `i = k-1`, `ρ = 0` it is
the special map `x ↦ εx - t` fixing `∞`. -/
def Kred (i ρ : ℕ) : GL2Z :=
  if i + 1 = C.k ∧ ρ = 0 then Classical.choose C.exists_last_reduction
  else if hi : i < C.k then Classical.choose (C.exists_canonical_reduction hi ρ) else 1

theorem Kred_last_eq : C.Kred (C.k - 1) 0 = Classical.choose C.exists_last_reduction := by
  unfold Kred
  rw [if_pos ⟨by have := C.hk; omega, rfl⟩]

theorem Kred_generic {i ρ : ℕ} (hi : i < C.k) (h : ¬(i + 1 = C.k ∧ ρ = 0)) :
    C.Kred i ρ = Classical.choose (C.exists_canonical_reduction hi ρ) := by
  unfold Kred
  rw [if_neg h, dif_pos hi]

/-- The reduced representative `σ_(i,ρ)`. -/
def sig (i ρ : ℕ) : ℝ := mob (intToReal (C.Kred i ρ)) (C.eta i ρ)

/-- Its conjugate `σ'_(i,ρ)`. -/
def sig' (i ρ : ℕ) : ℝ := mob (intToReal (C.Kred i ρ)) (C.eta' i ρ)

theorem eta_last : C.eta (C.k - 1) 0 = C.xi (C.k - 1) ∧ C.eta' (C.k - 1) 0 = C.xi' (C.k - 1) := by
  simp [eta, eta', U_zero_right, mob_one]

/-- The representative is the chosen reduced pair of the orbit. -/
theorem sig_eq_classRep {i : ℕ} (hi : i < C.k) (ρ : ℕ) :
    (C.sig i ρ, C.sig' i ρ) = C.classRep (orbitPair (C.eta i ρ) (C.eta' i ρ)) := by
  by_cases hl : i + 1 = C.k ∧ ρ = 0
  · obtain ⟨hl1, rfl⟩ := hl
    have hi' : i = C.k - 1 := by omega
    subst hi'
    rw [sig, sig', Kred_last_eq, C.eta_last.1, C.eta_last.2]
    unfold classRep
    rw [if_pos rfl]
    rfl
  · rw [sig, sig', Kred_generic C hi hl]
    obtain ⟨h1, h2⟩ := Classical.choose_spec (C.exists_canonical_reduction hi ρ)
    rw [h1, h2]

theorem sig_reduced {i : ℕ} (hi : i < C.k) (ρ : ℕ) :
    1 < C.sig i ρ ∧ -1 < C.sig' i ρ ∧ C.sig' i ρ < 0 := by
  have h := (C.classRep_spec (C.exists_reduced_mem hi ρ)).2
  rw [← C.sig_eq_classRep hi ρ] at h
  exact h

/-- Related points have equal representatives. -/
theorem sig_eq_of_pairRel {i i' : ℕ} (hi : i < C.k) (hi' : i' < C.k) (ρ ρ' : ℕ)
    (h : PairRel (C.eta i ρ) (C.eta' i ρ) (C.eta i' ρ') (C.eta' i' ρ')) :
    C.sig i ρ = C.sig i' ρ' ∧ C.sig' i ρ = C.sig' i' ρ' := by
  have he := orbitPair_eq (C.eta_pair hi ρ).irrational (C.eta_pair hi ρ).irrational' h
  have h1 := C.sig_eq_classRep hi ρ
  have h2 := C.sig_eq_classRep hi' ρ'
  rw [he, ← h2] at h1
  exact ⟨congrArg Prod.fst h1, congrArg Prod.snd h1⟩

theorem sig_pair {i : ℕ} (hi : i < C.k) (ρ : ℕ) : ConjPair (C.sig i ρ) (C.sig' i ρ) :=
  (C.eta_pair hi ρ).mob_GL2Z _

theorem Kred_last :
    ((C.Kred (C.k - 1) 0 : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 ∧
      (((C.Kred (C.k - 1) 0 : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = 1 ∨
        ((C.Kred (C.k - 1) 0 : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = -1) := by
  obtain ⟨h1, h2, -⟩ := Classical.choose_spec C.exists_last_reduction
  rw [Kred_last_eq]
  exact ⟨h1, h2⟩

/-! ## Half-junctions -/

theorem exists_half {i : ℕ} (hi : i < C.k) (ν : ℕ) :
    ∃ H : GL2Z, mob (intToReal H) (C.sig i (ν % C.g i)) = C.eta i ν ∧
      mob (intToReal H) (C.sig' i (ν % C.g i)) = C.eta' i ν := by
  obtain ⟨E, h1, h2⟩ := C.eta_rel hi (Nat.mod_modEq ν (C.g i))
  have hirr := C.eta_irr hi (ν % C.g i)
  refine ⟨E * (C.Kred i (ν % C.g i))⁻¹, ?_, ?_⟩
  · rw [Units.val_mul, intToReal_mul, mob_mul _ _ _ (mobDen_GL2Z_ne_zero
      (C.sig_pair hi _).irrational _), sig, mob_inv_GL2Z _ hirr.1, h1]
  · rw [Units.val_mul, intToReal_mul, mob_mul _ _ _ (mobDen_GL2Z_ne_zero
      (C.sig_pair hi _).irrational' _), sig', mob_inv_GL2Z _ hirr.2, h2]

/-! ## Invisible junctions -/

/-- An invisible junction at `i`: `0 < i < k` and `ξ_i = ξ_(i-1)`. -/
def Invisible (i : ℕ) : Prop := 0 < i ∧ i < C.k ∧ C.xi i = C.xi (i - 1)

theorem xi'_eq_of_xi_eq {i j : ℕ} (hi : i < C.k) (hj : j < C.k) (h : C.xi i = C.xi j) :
    C.xi' i = C.xi' j := by
  have ht := (chain_transition_facts C.hab C.S C.hdQ hi).2
  have hs := (chain_transition_facts C.hab C.S C.hdQ hj).2
  have ht' : ((C.T i 1 0 : ℚ) : ℝ) ≠ 0 := by exact_mod_cast ht
  have hs' : ((C.T j 1 0 : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hs
  simp only [xi, xi', eigSlope, T] at h ht' hs' ⊢
  rw [div_eq_div_iff ht' hs'] at h
  have hlin : (((C.S.transition j 1 0 - C.S.transition i 1 0 : ℚ) : ℝ)) * alpha C.a C.b +
      ((C.S.transition j 1 1 * C.S.transition i 1 0 - C.S.transition i 1 1 * C.S.transition j 1 0 :
        ℚ) : ℝ) = 0 := by
    push_cast
    linear_combination h
  obtain ⟨h1, h2⟩ := eq_zero_of_rat_lin (irrational_alpha C.hab) hlin
  have e1 : C.S.transition j 1 0 = C.S.transition i 1 0 := by linarith
  have e2 : C.S.transition i 1 1 = C.S.transition j 1 1 := by
    rw [e1] at h2
    have := mul_right_cancel₀ (show C.S.transition i 1 0 ≠ 0 from ht)
      (show C.S.transition i 1 1 * C.S.transition i 1 0 = C.S.transition j 1 1 * C.S.transition i 1 0
        by linarith)
    exact this
  rw [e1, e2]

theorem eta_eq_of_invisible {i : ℕ} (h : C.Invisible i) (ν : ℕ) :
    C.eta i ν = C.eta (i - 1) ν ∧ C.eta' i ν = C.eta' (i - 1) ν := by
  obtain ⟨hi0, hik, hξ⟩ := h
  have hj : i - 1 < C.k := by omega
  have hs := C.eta_succ hj ν
  rw [show i - 1 + 1 = i by omega] at hs
  have hξ' := C.xi'_eq_of_xi_eq hik hj hξ
  rw [hs.1, hs.2, eta, eta', hξ, hξ']
  exact ⟨rfl, rfl⟩

theorem sig_eq_of_invisible {i : ℕ} (h : C.Invisible i) (ν : ℕ) :
    C.sig i (ν % C.g i) = C.sig (i - 1) (ν % C.g (i - 1)) ∧
      C.sig' i (ν % C.g i) = C.sig' (i - 1) (ν % C.g (i - 1)) := by
  obtain ⟨hi0, hik, -⟩ := id h
  have hj : i - 1 < C.k := by omega
  apply C.sig_eq_of_pairRel hik hj
  have r1 := C.eta_rel hik (Nat.mod_modEq ν (C.g i))
  have r2 := C.eta_rel hj (Nat.mod_modEq ν (C.g (i - 1)))
  have hirr := C.eta_irr hik (ν % C.g i)
  have hirr' := C.eta_irr hj (ν % C.g (i - 1))
  rw [← (C.eta_eq_of_invisible h ν).1, ← (C.eta_eq_of_invisible h ν).2] at r2
  exact r1.trans hirr.1 hirr.2 (r2.symm hirr'.1 hirr'.2)

/-- `H⁻_(i,ν)` for `ν` modulo `m_(i+1)`; the last one is the inverse of the
special reduction. -/
def Hm (i ν : ℕ) : GL2Z :=
  if i + 1 = C.k ∧ ν = 0 then (C.Kred i 0)⁻¹
  else if hi : i < C.k then Classical.choose (C.exists_half hi ν) else 1

open scoped Classical in
/-- `H⁺_(i,ν)` for `ν` modulo `m_i`; by convention `H⁺_(k,ν) = H⁻_(k-1,ν)`, and at an
invisible junction `H⁺_(i,ν) = H⁻_(i-1,ν)`. -/
def Hp (i ν : ℕ) : GL2Z :=
  if i = C.k then C.Hm (C.k - 1) ν
  else if C.Invisible i then C.Hm (i - 1) ν
  else if hi : i < C.k then Classical.choose (C.exists_half hi ν) else 1

theorem Hm_special {i : ℕ} (hl : i + 1 = C.k) : C.Hm i 0 = (C.Kred i 0)⁻¹ := by
  unfold Hm
  rw [if_pos ⟨hl, rfl⟩]

theorem Hm_generic {i ν : ℕ} (hi : i < C.k) (h : ¬(i + 1 = C.k ∧ ν = 0)) :
    C.Hm i ν = Classical.choose (C.exists_half hi ν) := by
  unfold Hm
  rw [if_neg h, dif_pos hi]

theorem Hm_spec {i : ℕ} (hi : i < C.k) (ν : ℕ) :
    mob (intToReal (C.Hm i ν)) (C.sig i (ν % C.g i)) = C.eta i ν ∧
      mob (intToReal (C.Hm i ν)) (C.sig' i (ν % C.g i)) = C.eta' i ν := by
  by_cases hl : i + 1 = C.k ∧ ν = 0
  · obtain ⟨hl1, rfl⟩ := hl
    rw [Hm_special C hl1, Nat.zero_mod, sig, sig']
    have hirr := C.eta_irr hi 0
    exact ⟨mob_inv_GL2Z _ hirr.1, mob_inv_GL2Z _ hirr.2⟩
  · rw [Hm_generic C hi hl]
    exact Classical.choose_spec (C.exists_half hi ν)

theorem Hp_invisible {i : ℕ} (h : C.Invisible i) (ν : ℕ) : C.Hp i ν = C.Hm (i - 1) ν := by
  unfold Hp
  rw [if_neg h.2.1.ne, if_pos h]

theorem Hp_spec {i : ℕ} (hi : i < C.k) (ν : ℕ) :
    mob (intToReal (C.Hp i ν)) (C.sig i (ν % C.g i)) = C.eta i ν ∧
      mob (intToReal (C.Hp i ν)) (C.sig' i (ν % C.g i)) = C.eta' i ν := by
  by_cases hv : C.Invisible i
  · have hj : i - 1 < C.k := by omega
    rw [C.Hp_invisible hv, (C.sig_eq_of_invisible hv ν).1, (C.sig_eq_of_invisible hv ν).2,
      (C.Hm_spec hj ν).1, (C.Hm_spec hj ν).2, (C.eta_eq_of_invisible hv ν).1,
      (C.eta_eq_of_invisible hv ν).2]
    exact ⟨rfl, rfl⟩
  have : C.Hp i ν = Classical.choose (C.exists_half hi ν) := by
    unfold Hp
    rw [if_neg hi.ne, if_neg hv, dif_pos hi]
  rw [this]
  exact Classical.choose_spec (C.exists_half hi ν)

theorem Hp_k (ν : ℕ) : C.Hp C.k ν = C.Hm (C.k - 1) ν := by
  unfold Hp
  rw [if_pos rfl]

theorem Hm_last : C.Hm (C.k - 1) 0 = (C.Kred (C.k - 1) 0)⁻¹ :=
  C.Hm_special (by have := C.hk; omega)

/-! ## Middle matrices -/

/-- Inverse of `intToReal` on `GL₂(ℤ)`. -/
theorem intToReal_inv_mul (H : GL2Z) :
    intToReal (↑H⁻¹ : Matrix (Fin 2) (Fin 2) ℤ) * intToReal H = 1 := by
  rw [← intToReal_mul, Units.inv_mul, intToReal_one]

theorem intToReal_mul_inv (H : GL2Z) :
    intToReal H * intToReal (↑H⁻¹ : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
  rw [← intToReal_mul, Units.mul_inv, intToReal_one]

theorem exists_X {i : ℕ} (hi : i < C.k) (n : ℕ) :
    ∃ X : GL2Z, ∃ c : ℝ, c ≠ 0 ∧ intToReal (C.Hp i (n % C.m i)) * intToReal X *
        intToReal (↑(C.Hm i (n % C.m (i + 1)))⁻¹ : Matrix (Fin 2) (Fin 2) ℤ) *
        C.U (i + 1) (n % C.m (i + 1)) =
      c • (C.U i (n % C.m i) * ratToReal (C.T i) ^ n) := by
  set ν₁ := n % C.m i
  set ν₂ := n % C.m (i + 1)
  obtain ⟨G₁, c₁, hc₁, hG₁⟩ := C.exists_G hi.le (n / C.m i) ν₁
  obtain ⟨G₂, c₂, hc₂, hG₂⟩ := C.exists_G (Nat.succ_le_of_lt hi) (n / C.m (i + 1)) ν₂
  rw [show ν₁ + C.m i * (n / C.m i) = n from Nat.mod_add_div n _] at hG₁
  rw [show ν₂ + C.m (i + 1) * (n / C.m (i + 1)) = n from Nat.mod_add_div n _] at hG₂
  refine ⟨(C.Hp i ν₁)⁻¹ * G₁⁻¹ * G₂ * C.Hm i ν₂, c₂ / c₁, div_ne_zero hc₂ hc₁, ?_⟩
  have hgrp : C.Hp i ν₁ * ((C.Hp i ν₁)⁻¹ * G₁⁻¹ * G₂ * C.Hm i ν₂) * (C.Hm i ν₂)⁻¹ = G₁⁻¹ * G₂ := by
    group
  have hU : C.U i n = c₁⁻¹ • (intToReal G₁ * C.U i ν₁) := by
    rw [hG₁, smul_smul, inv_mul_cancel₀ hc₁, one_smul]
  calc intToReal (C.Hp i ν₁) * intToReal ((C.Hp i ν₁)⁻¹ * G₁⁻¹ * G₂ * C.Hm i ν₂ : GL2Z) *
        intToReal (↑(C.Hm i ν₂)⁻¹ : Matrix (Fin 2) (Fin 2) ℤ) * C.U (i + 1) ν₂
      = intToReal (↑(G₁⁻¹ * G₂ : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ) * C.U (i + 1) ν₂ := by
        rw [← hgrp]
        simp only [Units.val_mul, intToReal_mul]
    _ = intToReal (↑G₁⁻¹ : Matrix (Fin 2) (Fin 2) ℤ) * (intToReal G₂ * C.U (i + 1) ν₂) := by
        rw [Units.val_mul, intToReal_mul, Matrix.mul_assoc]
    _ = (c₂ / c₁) • (intToReal (↑G₁⁻¹ : Matrix (Fin 2) (Fin 2) ℤ) * (intToReal G₁ * C.U i ν₁) *
          ratToReal (C.T i) ^ n) := by
        rw [hG₂, U_succ, hU]
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
        rw [div_eq_mul_inv]
    _ = (c₂ / c₁) • (C.U i ν₁ * ratToReal (C.T i) ^ n) := by
        rw [← Matrix.mul_assoc, intToReal_inv_mul, Matrix.one_mul]

/-- The middle matrix `X_i(n)` and its scalar. -/
def X (i n : ℕ) : GL2Z :=
  if hi : i < C.k then Classical.choose (C.exists_X hi n) else 1

/-- The scalar in the defining identity of `X_i(n)`. -/
def Xc (i n : ℕ) : ℝ :=
  if hi : i < C.k then Classical.choose (Classical.choose_spec (C.exists_X hi n)) else 1

theorem X_spec {i : ℕ} (hi : i < C.k) (n : ℕ) :
    C.Xc i n ≠ 0 ∧ intToReal (C.Hp i (n % C.m i)) * intToReal (C.X i n) *
        intToReal (↑(C.Hm i (n % C.m (i + 1)))⁻¹ : Matrix (Fin 2) (Fin 2) ℤ) *
        C.U (i + 1) (n % C.m (i + 1)) =
      C.Xc i n • (C.U i (n % C.m i) * ratToReal (C.T i) ^ n) := by
  have h1 : C.X i n = Classical.choose (C.exists_X hi n) := by
    unfold X
    rw [dif_pos hi]
  have h2 : C.Xc i n = Classical.choose (Classical.choose_spec (C.exists_X hi n)) := by
    unfold Xc
    rw [dif_pos hi]
  rw [h1, h2]
  exact Classical.choose_spec (Classical.choose_spec (C.exists_X hi n))

/-- `H⁻¹ (H x, 1) = (1 / den) (x, 1)`. -/
theorem inv_mulVec_mob (H : GL2Z) {x : ℝ} (hx : Irrational x) :
    (intToReal (↑H⁻¹ : Matrix (Fin 2) (Fin 2) ℤ)).mulVec ![mob (intToReal H) x, 1] =
      (mobDen (intToReal H) x)⁻¹ • ![x, 1] := by
  have hd := mobDen_GL2Z_ne_zero hx H
  have h := mulVec_eq_mobDen_smul (intToReal H) x hd
  have h2 := congrArg (intToReal (↑H⁻¹ : Matrix (Fin 2) (Fin 2) ℤ)).mulVec h
  rw [Matrix.mulVec_mulVec, intToReal_inv_mul, Matrix.one_mulVec, Matrix.mulVec_smul] at h2
  rw [h2, smul_smul, inv_mul_cancel₀ hd, one_smul]

/-- `X_i(n)` fixes `σ` with eigenvalue `c · s · α^n`, where `c` depends only on
the residues of `n` modulo `m_i` and `m_(i+1)` and `s` is the scalar `Xc`. -/
theorem X_mulVec {i : ℕ} (hi : i < C.k) (n : ℕ) :
    (intToReal (C.X i n)).mulVec ![C.sig i (n % C.g i), 1] =
      ((mobDen (intToReal (C.Hm i (n % C.m (i + 1)))) (C.sig i (n % C.g i)) /
          mobDen (C.U (i + 1) (n % C.m (i + 1))) (C.xi i)) *
        (mobDen (C.U i (n % C.m i)) (C.xi i) /
          mobDen (intToReal (C.Hp i (n % C.m i))) (C.sig i (n % C.g i))) *
        C.Xc i n * alpha C.a C.b ^ n) • ![C.sig i (n % C.g i), 1] := by
  set ν₁ := n % C.m i
  set ν₂ := n % C.m (i + 1)
  set s := C.sig i (n % C.g i)
  have hs := (C.sig_pair hi (n % C.g i)).irrational
  have hξ := (C.xi_pair hi).irrational
  have hmod1 : ν₁ % C.g i = n % C.g i := Nat.mod_mod_of_dvd n (Nat.gcd_dvd_left _ _)
  have hmod2 : ν₂ % C.g i = n % C.g i := Nat.mod_mod_of_dvd n (Nat.gcd_dvd_right _ _)
  have hHm := C.Hm_spec hi ν₂
  have hHp := C.Hp_spec hi ν₁
  rw [hmod2] at hHm
  rw [hmod1] at hHp
  set d₁ := mobDen (intToReal (C.Hm i ν₂)) s
  set d₂ := mobDen (C.U (i + 1) ν₂) (C.xi i)
  set d₃ := mobDen (C.U i ν₁) (C.xi i)
  set d₅ := mobDen (intToReal (C.Hp i ν₁)) s
  have hd₁ : d₁ ≠ 0 := mobDen_GL2Z_ne_zero hs _
  have hd₂ : d₂ ≠ 0 := C.mobDen_U_ne_zero (Nat.succ_le_of_lt hi) _ hξ
  have hd₅ : d₅ ≠ 0 := mobDen_GL2Z_ne_zero hs _
  -- `Hm⁻¹ U_(i+1)(ν₂) (ξ, 1) = (d₂ / d₁) (σ, 1)`.
  have e1 : (intToReal (↑(C.Hm i ν₂)⁻¹ : Matrix (Fin 2) (Fin 2) ℤ) * C.U (i + 1) ν₂).mulVec
      ![C.xi i, 1] = (d₂ / d₁) • ![s, 1] := by
    rw [← Matrix.mulVec_mulVec, mulVec_eq_mobDen_smul _ _ hd₂, ← (C.eta_succ hi ν₂).1,
      Matrix.mulVec_smul, ← hHm.1, inv_mulVec_mob _ hs, smul_smul, div_eq_mul_inv]
  -- `Hp⁻¹ U_i(ν₁) T^n (ξ, 1) = α^n (d₃ / d₅) (σ, 1)`.
  have e2 : (intToReal (↑(C.Hp i ν₁)⁻¹ : Matrix (Fin 2) (Fin 2) ℤ) *
      (C.U i ν₁ * ratToReal (C.T i) ^ n)).mulVec ![C.xi i, 1] =
      (alpha C.a C.b ^ n * (d₃ / d₅)) • ![s, 1] := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      pow_mulVec_of_eigen (C.T_mulVec_xi hi) n, Matrix.mulVec_smul, Matrix.mulVec_smul,
      mulVec_eq_mobDen_smul _ _ (C.mobDen_U_ne_zero hi.le _ hξ), Matrix.mulVec_smul]
    change _ • _ • (intToReal (↑(C.Hp i ν₁)⁻¹ : Matrix (Fin 2) (Fin 2) ℤ)).mulVec
      ![C.eta i ν₁, 1] = _
    rw [← hHp.1, inv_mulVec_mob _ hs, smul_smul, smul_smul, div_eq_mul_inv]
    ring_nf
    rfl
  -- Combine with `X_spec`.
  obtain ⟨-, hX⟩ := C.X_spec hi n
  have hX' : intToReal (C.X i n) * (intToReal (↑(C.Hm i ν₂)⁻¹ : Matrix (Fin 2) (Fin 2) ℤ) *
      C.U (i + 1) ν₂) = C.Xc i n • (intToReal (↑(C.Hp i ν₁)⁻¹ : Matrix (Fin 2) (Fin 2) ℤ) *
      (C.U i ν₁ * ratToReal (C.T i) ^ n)) := by
    rw [← Matrix.mul_smul, ← hX, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, intToReal_inv_mul, Matrix.one_mul, Matrix.mul_assoc]
  have h3 := congrArg (fun A => A.mulVec ![C.xi i, 1]) hX'
  rw [← Matrix.mulVec_mulVec, e1, Matrix.smul_mulVec, e2, Matrix.mulVec_smul, smul_smul] at h3
  have hne : d₂ / d₁ ≠ 0 := div_ne_zero hd₂ hd₁
  have h4 := congrArg (fun v => (d₂ / d₁)⁻¹ • v) h3
  simp only [smul_smul, inv_mul_cancel₀ hne, one_smul] at h4
  rw [h4]
  congr 1
  field_simp

end Ctx

end TwoPoint
