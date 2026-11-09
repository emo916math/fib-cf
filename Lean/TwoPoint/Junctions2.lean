module

public import TwoPoint.Patches2

/-!
# Junction words

For `0 < i < k` and a residue `ν` modulo `m_i`, the raw junction
`(H⁻_(i-1,ν))⁻¹ H⁺_(i,ν)` sits between the patches `P_(i-1,ν)` and `P_(i,ν)`.
Its nondegeneracy reduces to `ξ_i ≠ ξ'_(i-1)`, so by the junction lemma
`±P_(i-1)^y (H⁻)⁻¹ H⁺ P_i^y` is a word for some `y`. The first junction
`±H⁺_(0,0) P_0^y` is a word because `η_0 = α^k > 1`.
-/

@[expose] public section
noncomputable section

namespace TwoPoint

theorem mob_injective {A : Matrix (Fin 2) (Fin 2) ℝ} (hdet : A.det ≠ 0) {x y : ℝ}
    (hx : mobDen A x ≠ 0) (hy : mobDen A y ≠ 0) (h : mob A x = mob A y) : x = y := by
  rw [mob, mob, div_eq_div_iff hx hy] at h
  have : (A 0 0 * A 1 1 - A 0 1 * A 1 0) * (x - y) = 0 := by
    simp only [mobDen] at h
    linear_combination h
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd (by rw [Matrix.det_fin_two]; exact h0) hdet
  · linarith

/-- A sign in `GL₂(ℤ)`. -/
def IsSign (s : GL2Z) : Prop := s = 1 ∨ s = -1

theorem IsSign.comm {s : GL2Z} (hs : IsSign s) (g : GL2Z) : s * g = g * s := by
  rcases hs with rfl | rfl <;> simp

theorem IsSign.mul_self {s : GL2Z} (hs : IsSign s) : s * s = 1 := by
  rcases hs with rfl | rfl <;> simp

theorem IsSign.mul {s t : GL2Z} (hs : IsSign s) (ht : IsSign t) : IsSign (s * t) := by
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> simp [IsSign]

theorem IsSign.one : IsSign 1 := Or.inl rfl

namespace Ctx

variable (C : Ctx)

/-- The raw junction group element with patch powers attached. -/
def Jraw (i ν : ℕ) (y : ℕ) : GL2Z :=
  if i = 0 then C.Hp 0 ν * C.P 0 ν ^ y
  else C.P (i - 1) ν ^ y * ((C.Hm (i - 1) ν)⁻¹ * C.Hp i ν) * C.P i ν ^ y

theorem exists_junction {i : ℕ} (hi : i < C.k) (ν : ℕ) :
    ∃ y : ℕ, ∃ s : GL2Z, IsSign s ∧ ∃ w : CFWord, PositiveWord w ∧ w ≠ [] ∧
      w.matrix = ((s * C.Jraw i ν y : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ) := by
  have hwrap : ∀ (M : GL2Z) (w : CFWord),
      (w.matrix = (M : Matrix (Fin 2) (Fin 2) ℤ) ∨ w.matrix = -(M : Matrix (Fin 2) (Fin 2) ℤ)) →
      ∃ s : GL2Z, IsSign s ∧ w.matrix = ((s * M : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ) := by
    intro M w h
    rcases h with h | h
    · exact ⟨1, Or.inl rfl, by simpa using h⟩
    · exact ⟨-1, Or.inr rfl, by simpa using h⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · -- The first junction.
    obtain ⟨hP, hPl, -⟩ := C.P_spec hi ν
    obtain ⟨-, h2, h3⟩ := C.sig_reduced hi (ν % C.g 0)
    have hJ : 1 < mob (intToReal (C.Hp 0 ν)) (C.sig 0 (ν % C.g 0)) := by
      rw [(C.Hp_spec hi ν).1]
      exact C.one_lt_eta_zero ν
    obtain ⟨y, w, hw, hw0, hwm⟩ := exists_left_junction_word (C.sig_pair hi _) h2 h3 hP hPl _ hJ
    obtain ⟨s, hs, hsw⟩ := hwrap _ w hwm
    exact ⟨y, s, hs, w, hw, hw0, by rw [hsw]; simp [Jraw]⟩
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hj : j < C.k := by omega
    obtain ⟨hP, hPl, -⟩ := C.P_spec hj ν
    obtain ⟨hQ, hQl, -⟩ := C.P_spec hi ν
    obtain ⟨h1, -, -⟩ := C.sig_reduced hj (ν % C.g j)
    obtain ⟨-, h2, h3⟩ := C.sig_reduced hi (ν % C.g (j + 1))
    -- `ν mod g_j` and `ν mod m_(j+1)` determine the same class.
    have hHm := C.Hm_spec hj ν
    have hHp := C.Hp_spec hi ν
    have hJ : mob (intToReal (((C.Hm j ν)⁻¹ * C.Hp (j + 1) ν : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ))
        (C.sig (j + 1) (ν % C.g (j + 1))) ≠ C.sig' j (ν % C.g j) := by
      intro heq
      have hs := (C.sig_pair hi (ν % C.g (j + 1))).irrational
      rw [Units.val_mul, intToReal_mul, mob_mul _ _ _ (mobDen_GL2Z_ne_zero hs _), hHp.1] at heq
      have hs' := (C.sig_pair hj (ν % C.g j)).irrational'
      have hsig' : C.sig' j (ν % C.g j) =
          mob (intToReal ↑(C.Hm j ν)⁻¹) (C.eta' j ν) := by
        rw [← hHm.2, mob_inv_GL2Z _ hs']
      rw [hsig'] at heq
      have he1 := mob_injective (GL2Z.det_real_ne_zero _)
        (mobDen_GL2Z_ne_zero (C.eta_irr hi ν).1 _) (mobDen_GL2Z_ne_zero (C.eta_irr hj ν).2 _) heq
      rw [(C.eta_succ hj ν).2, eta] at he1
      have hξ := (C.xi_pair hi).irrational
      have hξ' := (C.xi_pair hj).irrational'
      have he2 := mob_injective (C.U_det_ne_zero (Nat.succ_le_of_lt hj) ν)
        (C.mobDen_U_ne_zero (Nat.succ_le_of_lt hj) ν hξ)
        (C.mobDen_U_ne_zero (Nat.succ_le_of_lt hj) ν hξ') he1
      exact chain_xi_ne_xi'_prev C.hab C.S C.hdQ hi he2
    obtain ⟨y, w, hw, hw0, hwm⟩ := exists_junction_word (C.sig_pair hj _) (C.sig_pair hi _)
      h1 h2 h3 hP hQ hPl hQl _ hJ
    obtain ⟨s, hs, hsw⟩ := hwrap _ w hwm
    refine ⟨y, s, hs, w, hw, hw0, ?_⟩
    rw [hsw]
    simp only [Jraw, Nat.add_sub_cancel, Nat.succ_ne_zero, ite_false]

open scoped Classical in
/-- The junction exponent `y_(i,ν)` (zero at an invisible junction). -/
def y (i ν : ℕ) : ℕ :=
  if C.Invisible i then 0 else if hi : i < C.k then Classical.choose (C.exists_junction hi ν) else 0

open scoped Classical in
/-- The junction sign. -/
def jsign (i ν : ℕ) : GL2Z :=
  if C.Invisible i then 1
  else if hi : i < C.k then Classical.choose (Classical.choose_spec (C.exists_junction hi ν)) else 1

open scoped Classical in
/-- The junction word `J_(i,ν)`, empty at an invisible junction. -/
def Jword (i ν : ℕ) : CFWord :=
  if C.Invisible i then []
  else if hi : i < C.k then
    Classical.choose (Classical.choose_spec (Classical.choose_spec (C.exists_junction hi ν))).2
  else []

theorem Jword_invisible {i : ℕ} (h : C.Invisible i) (ν : ℕ) : C.Jword i ν = [] := by
  unfold Jword
  rw [if_pos h]

theorem Jword_spec {i : ℕ} (hi : i < C.k) (ν : ℕ) :
    IsSign (C.jsign i ν) ∧ PositiveWord (C.Jword i ν) ∧ (i = 0 → C.Jword i ν ≠ []) ∧
      (C.Jword i ν).matrix = ((C.jsign i ν * C.Jraw i ν (C.y i ν) : GL2Z) :
        Matrix (Fin 2) (Fin 2) ℤ) := by
  by_cases hv : C.Invisible i
  · have hy : C.y i ν = 0 := by unfold y; rw [if_pos hv]
    have hs : C.jsign i ν = 1 := by unfold jsign; rw [if_pos hv]
    rw [C.Jword_invisible hv, hy, hs]
    refine ⟨IsSign.one, positiveWord_nil, fun h0 => absurd h0 (by have := hv.1; omega), ?_⟩
    have hi0 : i ≠ 0 := by have := hv.1; omega
    simp only [Jraw, if_neg hi0, pow_zero, mul_one, one_mul, C.Hp_invisible hv, inv_mul_cancel,
      Units.val_one]
    rfl
  have h1 : C.y i ν = Classical.choose (C.exists_junction hi ν) := by
    unfold y; rw [if_neg hv, dif_pos hi]
  have h2 : C.jsign i ν = Classical.choose (Classical.choose_spec (C.exists_junction hi ν)) := by
    unfold jsign; rw [if_neg hv, dif_pos hi]
  have h3 : C.Jword i ν = Classical.choose
      (Classical.choose_spec (Classical.choose_spec (C.exists_junction hi ν))).2 := by
    unfold Jword; rw [if_neg hv, dif_pos hi]
  rw [h1, h2, h3]
  obtain ⟨hs, hw⟩ := Classical.choose_spec (Classical.choose_spec (C.exists_junction hi ν))
  obtain ⟨hw1, hw2, hw3⟩ := Classical.choose_spec hw
  exact ⟨hs, hw1, fun _ => hw2, hw3⟩

/-- Visible junctions are nonempty words. -/
theorem Jword_ne_nil {i : ℕ} (hi : i < C.k) (hv : ¬ C.Invisible i) (ν : ℕ) : C.Jword i ν ≠ [] := by
  have h3 : C.Jword i ν = Classical.choose
      (Classical.choose_spec (Classical.choose_spec (C.exists_junction hi ν))).2 := by
    unfold Jword; rw [if_neg hv, dif_pos hi]
  rw [h3]
  obtain ⟨-, hw⟩ := Classical.choose_spec (Classical.choose_spec (C.exists_junction hi ν))
  exact (Classical.choose_spec hw).2.1

end Ctx

end TwoPoint
