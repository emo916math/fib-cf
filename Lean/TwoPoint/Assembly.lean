module

public import TwoPoint.FinalJunction

/-!
# Assembling the continued fraction

For fixed `n`, write `ν_i = n mod m_i`, `H⁺_i = H⁺_(i,ν_i)`, `H⁻_i = H⁻_(i,ν_(i+1))`,
`X_i = X_i(n)` and `C_i = (H⁻_i)⁻¹ H⁺_(i+1)`. Telescoping the identities
`H⁺_i X_i (H⁻_i)⁻¹ U_(i+1)(ν_(i+1)) = s_i U_i(ν_i) T_i^n` (with scalars `s_i`) gives

  `c U_k(n) = H⁺_0 ∏_(i<k) (X_i C_i) · (H⁻_(k-1))⁻¹ U_k(ν_k)`.

Substituting `X_i = ±P_i^(e_i)` and the junction identities, the product
`H⁺_0 ∏ X_i C_i` equals `±∏_(i<k) J_i P_i^(e'_i) · P_(k-1)^(y_k)` with
`e'_i = e_i - y_i - y_(i+1)`, where `y_k` is the exponent of the final junction.
-/

@[expose] public section
noncomputable section

namespace TwoPoint

/-- Equality up to sign in `GL₂(ℤ)`. -/
def PMeq (x y : GL2Z) : Prop := x = y ∨ x = -y

theorem PMeq.refl (x : GL2Z) : PMeq x x := Or.inl rfl

theorem PMeq.of_eq {x y : GL2Z} (h : x = y) : PMeq x y := Or.inl h

theorem PMeq.mul {x x' y y' : GL2Z} (hx : PMeq x x') (hy : PMeq y y') :
    PMeq (x * y) (x' * y') := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [PMeq]

theorem PMeq.trans {x y z : GL2Z} (h₁ : PMeq x y) (h₂ : PMeq y z) : PMeq x z := by
  rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;> simp [PMeq]

theorem PMeq.of_sign {s x y : GL2Z} (hs : IsSign s) (h : x = s * y) : PMeq x y := by
  rcases hs with rfl | rfl <;> simp [PMeq, h]

theorem sign_sign {s : GL2Z} (hs : IsSign s) (x : GL2Z) : s * (s * x) = x := by
  rw [← mul_assoc, hs.mul_self, one_mul]

theorem list_prod_range_succ {M : Type*} [Monoid M] (f : ℕ → M) (i : ℕ) :
    ((List.range (i + 1)).map f).prod = ((List.range i).map f).prod * f i := by
  rw [List.range_succ, List.map_append, List.prod_append]
  simp

namespace Ctx

variable (C : Ctx)

/-! ## Telescoping -/

/-- `H⁺_i` at `n`. -/
def Hpn (n i : ℕ) : GL2Z := C.Hp i (n % C.m i)

/-- `H⁻_i` at `n`. -/
def Hmn (n i : ℕ) : GL2Z := C.Hm i (n % C.m (i + 1))

/-- `C_i = (H⁻_i)⁻¹ H⁺_(i+1)` at `n`. -/
def Cn (n i : ℕ) : GL2Z := (C.Hmn n i)⁻¹ * C.Hpn n (i + 1)

/-- `∏_(j<i) X_j C_j` at `n`. -/
def prodXC (n i : ℕ) : GL2Z := ((List.range i).map fun j => C.X j n * C.Cn n j).prod

theorem telescope (n : ℕ) {i : ℕ} (hi : i ≤ C.k) :
    ∃ c : ℝ, c ≠ 0 ∧
      intToReal (C.Hpn n 0 * C.prodXC n i * (C.Hpn n i)⁻¹ : GL2Z) * C.U i (n % C.m i) =
        c • C.U i n := by
  induction i with
  | zero =>
    refine ⟨1, one_ne_zero, ?_⟩
    simp only [prodXC, List.range_zero, List.map_nil, List.prod_nil, mul_one, mul_inv_cancel,
      Units.val_one, intToReal_one, U_zero_left, one_smul]
  | succ i ih =>
    have hi' : i < C.k := hi
    obtain ⟨c, hc, ih⟩ := ih (Nat.le_of_succ_le hi)
    obtain ⟨hXc, hX⟩ := C.X_spec hi' n
    have hgrp : C.Hpn n 0 * C.prodXC n (i + 1) * (C.Hpn n (i + 1))⁻¹ =
        C.Hpn n 0 * C.prodXC n i * (C.Hpn n i)⁻¹ * (C.Hpn n i * C.X i n * (C.Hmn n i)⁻¹) := by
      simp only [prodXC, list_prod_range_succ, Cn]
      group
    refine ⟨C.Xc i n * c, mul_ne_zero hXc hc, ?_⟩
    calc intToReal (C.Hpn n 0 * C.prodXC n (i + 1) * (C.Hpn n (i + 1))⁻¹ : GL2Z) *
          C.U (i + 1) (n % C.m (i + 1))
        = intToReal (C.Hpn n 0 * C.prodXC n i * (C.Hpn n i)⁻¹ : GL2Z) *
            (intToReal (C.Hp i (n % C.m i)) * intToReal (C.X i n) *
              intToReal (↑(C.Hm i (n % C.m (i + 1)))⁻¹ : Matrix (Fin 2) (Fin 2) ℤ) *
              C.U (i + 1) (n % C.m (i + 1))) := by
          rw [hgrp, Units.val_mul, intToReal_mul]
          simp only [Hpn, Hmn, Units.val_mul, intToReal_mul, Matrix.mul_assoc]
      _ = C.Xc i n • (intToReal (C.Hpn n 0 * C.prodXC n i * (C.Hpn n i)⁻¹ : GL2Z) *
            C.U i (n % C.m i) * ratToReal (C.T i) ^ n) := by
          rw [hX, Matrix.mul_smul, Matrix.mul_assoc]
      _ = (C.Xc i n * c) • C.U (i + 1) n := by
          rw [ih, U_succ, Matrix.smul_mul, smul_smul]

/-- The telescoped identity at `i = k`, with the final half-junction. -/
theorem U_k_eq (n : ℕ) : ∃ c : ℝ, c ≠ 0 ∧
    intToReal (C.Hpn n 0 * C.prodXC n C.k : GL2Z) *
      intToReal (↑(C.Hm (C.k - 1) (n % C.m C.k))⁻¹ : Matrix (Fin 2) (Fin 2) ℤ) *
      C.U C.k (n % C.m C.k) = c • C.U C.k n := by
  obtain ⟨c, hc, h⟩ := C.telescope n le_rfl
  refine ⟨c, hc, ?_⟩
  rw [← h]
  simp only [Hpn, Hp_k, Units.val_mul, intToReal_mul]

/-! ## Regrouping -/

/-- `y_i` at `n`; `y_k` is the exponent of the final junction. -/
def yn (n i : ℕ) : ℤ :=
  if i < C.k then (C.y i (n % C.m i) : ℤ) else if i = C.k then (C.yfin (n % C.m C.k) : ℤ) else 0

/-- `y_i` at `n` depends only on `n mod m_i`. -/
theorem yn_congr {n n' i : ℕ} (h : n % C.m i = n' % C.m i) : C.yn n i = C.yn n' i := by
  unfold yn
  split_ifs with h₁ h₂
  · rw [h]
  · subst h₂
    rw [h]
  · rfl

/-- The effective exponent `e'_i = e_i - y_i - y_(i+1)`. -/
def e' (n i : ℕ) : ℤ := C.e i n - C.yn n i - C.yn n (i + 1)

/-- The junction group element `J_i` at `n`. -/
def Jn (n i : ℕ) : GL2Z := C.jsign i (n % C.m i) * C.Jraw i (n % C.m i) (C.y i (n % C.m i))

theorem P_eq_of_dvd {i n ν : ℕ} (hν : ν = n % C.m (i + 1)) (h : C.g i ∣ C.m (i + 1)) :
    C.P i ν = C.P i n := by
  rw [← C.P_mod i ν, ← C.P_mod i n, hν, Nat.mod_mod_of_dvd n h]

theorem P_eq_of_dvd' {i n ν : ℕ} (hν : ν = n % C.m i) : C.P i ν = C.P i n := by
  rw [← C.P_mod i ν, ← C.P_mod i n, hν,
    Nat.mod_mod_of_dvd n (show C.g i ∣ C.m i from Nat.gcd_dvd_left _ _)]

theorem Hpn_zero (n : ℕ) :
    PMeq (C.Hpn n 0) (C.Jn n 0 * C.P 0 n ^ (-(C.yn n 0))) := by
  have hk := C.hk
  have hs := (C.Jword_spec hk (n % C.m 0)).1
  have hP : C.P 0 (n % C.m 0) = C.P 0 n := C.P_eq_of_dvd' rfl
  apply PMeq.of_sign hs
  simp only [Jn, Jraw, yn, if_pos hk, hP, Hpn, ↓reduceIte]
  rw [mul_assoc (C.jsign 0 (n % C.m 0)), sign_sign hs]
  group

theorem Cn_interior (n : ℕ) {j : ℕ} (hj : j + 1 < C.k) :
    PMeq (C.Cn n j)
      (C.P j n ^ (-(C.yn n (j + 1))) * C.Jn n (j + 1) * C.P (j + 1) n ^ (-(C.yn n (j + 1)))) := by
  have hs := (C.Jword_spec hj (n % C.m (j + 1))).1
  have hP1 : C.P j (n % C.m (j + 1)) = C.P j n :=
    C.P_eq_of_dvd rfl (Nat.gcd_dvd_right _ _)
  have hP2 : C.P (j + 1) (n % C.m (j + 1)) = C.P (j + 1) n := C.P_eq_of_dvd' rfl
  apply PMeq.of_sign hs
  simp only [Jn, Jraw, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, yn, if_pos hj, hP1, hP2,
    Cn, Hmn, Hpn]
  set s := C.jsign (j + 1) (n % C.m (j + 1))
  have hcomm : ∀ a b : GL2Z, a * (s * b) = s * (a * b) := fun a b => by
    rw [← mul_assoc, ← hs.comm a, mul_assoc]
  rw [hcomm, mul_assoc s, sign_sign hs]
  group

theorem Cn_last (n : ℕ) : C.Cn n (C.k - 1) = 1 := by
  have hk := C.hk
  simp only [Cn, Hmn, Hpn, show C.k - 1 + 1 = C.k by omega, Hp_k]
  exact inv_mul_cancel _

theorem X_pm (n : ℕ) {j : ℕ} (hj : j < C.k) : PMeq (C.X j n) (C.P j n ^ C.e j n) := by
  rcases C.e_spec hj n with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- `∏_(j<i) J_j P_j^(e'_j)`. -/
def prodJP (n i : ℕ) : GL2Z := ((List.range i).map fun j => C.Jn n j * C.P j n ^ C.e' n j).prod

theorem regroup_aux (n : ℕ) {i : ℕ} (hi : i < C.k) :
    PMeq (C.Hpn n 0 * C.prodXC n i)
      (C.prodJP n i * C.Jn n i * C.P i n ^ (-(C.yn n i))) := by
  induction i with
  | zero =>
    simpa [prodXC, prodJP] using C.Hpn_zero n
  | succ i ih =>
    have ih' := ih (by omega)
    have hX := C.X_pm n (show i < C.k by omega)
    have hC := C.Cn_interior n (j := i) hi
    have hstep : C.Hpn n 0 * C.prodXC n (i + 1) = C.Hpn n 0 * C.prodXC n i * (C.X i n * C.Cn n i) := by
      simp only [prodXC, list_prod_range_succ, mul_assoc]
    rw [hstep]
    refine (ih'.mul (hX.mul hC)).trans (PMeq.of_eq ?_)
    simp only [prodJP, list_prod_range_succ, e']
    rw [zpow_sub, zpow_sub]
    group

theorem regroup (n : ℕ) :
    PMeq (C.Hpn n 0 * C.prodXC n C.k) (C.prodJP n C.k * C.P (C.k - 1) n ^ C.yn n C.k) := by
  have hk := C.hk
  obtain ⟨j, hj⟩ : ∃ j, C.k = j + 1 := ⟨C.k - 1, by omega⟩
  have hjk : j < C.k := by omega
  have h := C.regroup_aux n hjk
  have hX := C.X_pm n hjk
  have hstep : C.Hpn n 0 * C.prodXC n C.k = C.Hpn n 0 * C.prodXC n j * (C.X j n * C.Cn n j) := by
    rw [hj]
    simp only [prodXC, list_prod_range_succ, mul_assoc]
  rw [hstep]
  have hC : C.Cn n j = 1 := by rw [show j = C.k - 1 by omega]; exact C.Cn_last n
  rw [hC, mul_one]
  refine (h.mul hX).trans (PMeq.of_eq ?_)
  have hj' : C.k - 1 = j := by omega
  rw [hj', hj]
  simp only [prodJP, list_prod_range_succ, e']
  rw [zpow_sub, zpow_sub]
  group

end Ctx

end TwoPoint
