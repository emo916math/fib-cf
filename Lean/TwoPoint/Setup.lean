module

public import TwoPoint.ChainFacts
public import TwoPoint.IntegralBasis

/-!
# Setting for the patch-junction decomposition

We fix `(a, b)` satisfying the hypotheses of Exercise `exer:main_gen`, `k ≥ 1`
with all `Δ_{k,i} ≠ 0`, a chain of normalized Padé bases with transition
matrices `T_i`, and moduli `m_i` (with `m_0 = 1`) along which the evaluations
`U_i` are transported by `GL₂(ℤ)` up to a scalar. Then

* `U i n = T_0^n ⋯ T_(i-1)^n` (the homogeneous evaluation `Φ_i(u_(n+1), u_n)`);
* `ξ_i`, `ξ'_i` are the eigenvector slopes of `T_i` for `α`, `β`;
* `η i n = U_i(n) · ξ_i` and its conjugate `η' i n`.

Integral transports `G` (Lemma `lem:G_integral`, or Exercise `exer:main_gen`(c)
when `|b| > 1`) move `(η i n, η' i n)` to `(η i (n+m), η' i (n+m))` whenever
`m` is a multiple of `m_i` or of `m_(i+1)`.
-/

@[expose] public section
noncomputable section

namespace TwoPoint

open Polynomial

/-- The fixed data of Theorem 1.2(b) and Exercise `exer:main_gen`(b). -/
structure Ctx where
  a : ℤ
  b : ℤ
  k : ℕ
  hab : GenAdmissible a b
  hk : 0 < k
  hd : ∀ i, i ≤ k → delta a b k i ≠ 0
  S : PadeBasisChain (a : ℚ) (b : ℚ) k
  /-- The moduli `m_i`. -/
  m : ℕ → ℕ
  m_pos : ∀ i, 0 < m i
  m_zero : m 0 = 1
  /-- `U_i(n + m_i t)` is a scalar multiple of `G U_i(n)` with `G ∈ GL₂(ℤ)`. -/
  transport : ∀ i (hi : i ≤ k) (n t : ℕ), ∃ G : Matrix (Fin 2) (Fin 2) ℤ, IsUnit G ∧
    ∃ c : ℚ, c ≠ 0 ∧
      intMatrixCast 2 G * evalU (S.basis i hi) n = c • evalU (S.basis i hi) (n + m i * t)

namespace Ctx

variable (C : Ctx)

theorem hdQ : ∀ i, i ≤ C.k → deltaOver (C.a : ℚ) (C.b : ℚ) C.k i ≠ 0 := by
  intro i hi
  have hm := deltaOver_map (Int.castRingHom ℚ) C.a C.b C.k i
  dsimp at hm
  rw [← hm]
  exact_mod_cast (show deltaOver C.a C.b C.k i ≠ 0 by rw [← delta_eq_deltaOver]; exact C.hd i hi)

/-- The transition matrices. -/
def T (j : ℕ) : Matrix (Fin 2) (Fin 2) ℚ := C.S.transition j

/-- `T_0^n ⋯ T_(i-1)^n` over `ℚ`. -/
def Uq (i n : ℕ) : Matrix (Fin 2) (Fin 2) ℚ := ((List.range i).map fun j => C.T j ^ n).prod

/-- `T_0^n ⋯ T_(i-1)^n` over `ℝ`. -/
def U (i n : ℕ) : Matrix (Fin 2) (Fin 2) ℝ := ratToReal (C.Uq i n)

theorem ratToReal_one : ratToReal (1 : Matrix (Fin 2) (Fin 2) ℚ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ratToReal]

theorem U_succ (i n : ℕ) : C.U (i + 1) n = C.U i n * ratToReal (C.T i) ^ n := by
  simp [U, Uq, List.range_succ, List.prod_append, ratToReal_mul, ratToReal_pow]

theorem U_zero_left (n : ℕ) : C.U 0 n = 1 := by simp [U, Uq, ratToReal_one]

theorem U_zero_right (i : ℕ) : C.U i 0 = 1 := by
  simp [U, Uq, ratToReal_one]

theorem Uq_eq_evalU {i : ℕ} (hi : i ≤ C.k) (n : ℕ) :
    C.Uq i n = evalU (C.S.basis i hi) n :=
  (C.S.homEval_eq_prod C.a C.b C.hdQ n i hi).symm

theorem U_det_ne_zero {i : ℕ} (hi : i ≤ C.k) (n : ℕ) : (C.U i n).det ≠ 0 := by
  rw [U, ratToReal_det, C.Uq_eq_evalU hi, evalU_det]
  have hb : (C.b : ℚ) ≠ 0 := by exact_mod_cast C.hab.b_ne_zero
  exact_mod_cast pow_ne_zero _ (neg_ne_zero.mpr hb)

theorem isRatMat_U (i n : ℕ) : IsRatMat (C.U i n) := IsRatMat.ratToReal _

theorem ratToReal_smul (c : ℚ) (A : Matrix (Fin 2) (Fin 2) ℚ) :
    ratToReal (c • A) = (c : ℝ) • ratToReal A := by
  ext i j
  simp [ratToReal]

/-- Lemma `lem:G_integral`, as an integral transport of `U` up to a scalar. -/
theorem exists_G {i : ℕ} (hi : i ≤ C.k) (t n : ℕ) :
    ∃ G : GL2Z, ∃ c : ℝ, c ≠ 0 ∧ intToReal G * C.U i n = c • C.U i (n + C.m i * t) := by
  obtain ⟨G, hGu, c, hc, hG⟩ := C.transport i hi n t
  refine ⟨hGu.unit, c, by exact_mod_cast hc, ?_⟩
  have hcast : intToReal (hGu.unit : Matrix (Fin 2) (Fin 2) ℤ) = ratToReal (intMatrixCast 2 G) := by
    ext r c
    simp [intToReal, ratToReal, intMatrixCast]
  rw [hcast, U, U, ← ratToReal_mul, C.Uq_eq_evalU hi, C.Uq_eq_evalU hi, hG, ratToReal_smul]

/-! ## Eigenvectors and the points `η` -/

/-- The slope `ξ_j` of the `α`-eigenvector of `T_j`. -/
def xi (j : ℕ) : ℝ := eigSlope (C.T j) (alpha C.a C.b)

/-- The slope `ξ'_j` of the `β`-eigenvector of `T_j`. -/
def xi' (j : ℕ) : ℝ := eigSlope (C.T j) (beta C.a C.b)

theorem xi_pair {j : ℕ} (hj : j < C.k) : ConjPair (C.xi j) (C.xi' j) :=
  eigSlope_conjPair C.hab _ (chain_transition_facts C.hab C.S C.hdQ hj).2

theorem T_mulVec_xi {j : ℕ} (hj : j < C.k) :
    (ratToReal (C.T j)).mulVec ![C.xi j, 1] = alpha C.a C.b • ![C.xi j, 1] :=
  chain_eigSlope_mulVec C.hab C.S C.hdQ hj (alpha_sq C.hab)

theorem T_mulVec_xi' {j : ℕ} (hj : j < C.k) :
    (ratToReal (C.T j)).mulVec ![C.xi' j, 1] = beta C.a C.b • ![C.xi' j, 1] :=
  chain_eigSlope_mulVec C.hab C.S C.hdQ hj (beta_sq C.hab)

theorem pow_mulVec_of_eigen {A : Matrix (Fin 2) (Fin 2) ℝ} {v : Fin 2 → ℝ} {c : ℝ}
    (h : A.mulVec v = c • v) (n : ℕ) : (A ^ n).mulVec v = c ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ, mul_comm]

theorem beta_ne_zero : beta C.a C.b ≠ 0 := by
  intro h
  have := alpha_mul_beta C.hab
  rw [h, mul_zero] at this
  exact C.hab.b_ne_zero (by exact_mod_cast (neg_eq_zero.mp this.symm))

theorem alpha_ne_zero : alpha C.a C.b ≠ 0 := by
  have := one_lt_alpha C.hab
  linarith

theorem mob_T_pow_xi {j : ℕ} (hj : j < C.k) (n : ℕ) :
    mob (ratToReal (C.T j) ^ n) (C.xi j) = C.xi j ∧
      mobDen (ratToReal (C.T j) ^ n) (C.xi j) = alpha C.a C.b ^ n :=
  mob_of_mulVec (pow_ne_zero _ C.alpha_ne_zero) (pow_mulVec_of_eigen (C.T_mulVec_xi hj) n)

theorem mob_T_pow_xi' {j : ℕ} (hj : j < C.k) (n : ℕ) :
    mob (ratToReal (C.T j) ^ n) (C.xi' j) = C.xi' j ∧
      mobDen (ratToReal (C.T j) ^ n) (C.xi' j) = beta C.a C.b ^ n :=
  mob_of_mulVec (pow_ne_zero _ C.beta_ne_zero) (pow_mulVec_of_eigen (C.T_mulVec_xi' hj) n)

/-- `η_i(n) = U_i(n) · ξ_i`. -/
def eta (i n : ℕ) : ℝ := mob (C.U i n) (C.xi i)

/-- `η'_i(n) = U_i(n) · ξ'_i`. -/
def eta' (i n : ℕ) : ℝ := mob (C.U i n) (C.xi' i)

theorem mobDen_U_ne_zero {i : ℕ} (hi : i ≤ C.k) (n : ℕ) {x : ℝ} (hx : Irrational x) :
    mobDen (C.U i n) x ≠ 0 :=
  mobDen_ne_zero_of_irrational (C.isRatMat_U i n) (C.U_det_ne_zero hi n) hx

theorem eta_pair {i : ℕ} (hi : i < C.k) (n : ℕ) : ConjPair (C.eta i n) (C.eta' i n) :=
  (C.xi_pair hi).mob (C.isRatMat_U i n) (C.U_det_ne_zero hi.le n)

theorem eta_succ {i : ℕ} (hi : i < C.k) (n : ℕ) :
    C.eta i n = mob (C.U (i + 1) n) (C.xi i) ∧ C.eta' i n = mob (C.U (i + 1) n) (C.xi' i) := by
  have hT := C.mob_T_pow_xi hi n
  have hT' := C.mob_T_pow_xi' hi n
  constructor
  · rw [eta, U_succ, mob_mul _ _ _ (by rw [hT.2]; exact pow_ne_zero _ C.alpha_ne_zero), hT.1]
  · rw [eta', U_succ, mob_mul _ _ _ (by rw [hT'.2]; exact pow_ne_zero _ C.beta_ne_zero), hT'.1]

theorem mobDen_smul (c : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) (x : ℝ) :
    mobDen (c • A) x = c * mobDen A x := by
  simp [mobDen]
  ring

theorem mob_smul {c : ℝ} (hc : c ≠ 0) (A : Matrix (Fin 2) (Fin 2) ℝ) (x : ℝ) :
    mob (c • A) x = mob A x := by
  simp only [mob, mobDen_smul, Matrix.smul_apply, smul_eq_mul]
  rw [show c * A 0 0 * x + c * A 0 1 = c * (A 0 0 * x + A 0 1) by ring, mul_div_mul_left _ _ hc]

/-- Transport along `G_i`. -/
theorem eta_transport {i : ℕ} (hi : i < C.k) (t n : ℕ) :
    ∃ G : GL2Z, mob (intToReal G) (C.eta i n) = C.eta i (n + C.m i * t) ∧
      mob (intToReal G) (C.eta' i n) = C.eta' i (n + C.m i * t) := by
  obtain ⟨G, c, hc, hG⟩ := C.exists_G hi.le t n
  have hp := C.xi_pair hi
  refine ⟨G, ?_, ?_⟩
  · rw [eta, eta, ← mob_mul _ _ _ (C.mobDen_U_ne_zero hi.le n hp.irrational), hG, mob_smul hc]
  · rw [eta', eta', ← mob_mul _ _ _ (C.mobDen_U_ne_zero hi.le n hp.irrational'), hG, mob_smul hc]

/-- Transport along `G_(i+1)`. -/
theorem eta_transport' {i : ℕ} (hi : i < C.k) (t n : ℕ) :
    ∃ G : GL2Z, mob (intToReal G) (C.eta i n) = C.eta i (n + C.m (i + 1) * t) ∧
      mob (intToReal G) (C.eta' i n) = C.eta' i (n + C.m (i + 1) * t) := by
  obtain ⟨G, c, hc, hG⟩ := C.exists_G (Nat.succ_le_of_lt hi) t n
  have hp := C.xi_pair hi
  refine ⟨G, ?_, ?_⟩
  · rw [(C.eta_succ hi n).1, (C.eta_succ hi (n + C.m (i + 1) * t)).1,
      ← mob_mul _ _ _ (C.mobDen_U_ne_zero (Nat.succ_le_of_lt hi) n hp.irrational), hG, mob_smul hc]
  · rw [(C.eta_succ hi n).2, (C.eta_succ hi (n + C.m (i + 1) * t)).2,
      ← mob_mul _ _ _ (C.mobDen_U_ne_zero (Nat.succ_le_of_lt hi) n hp.irrational'), hG, mob_smul hc]

end Ctx

end TwoPoint
