module

public import TwoPoint.IntegralLattice

/-!
# Integral quotients of congruent matrices

These are the adjugate calculations used in Lemma `lem:G_integral`.
Congruence modulo the determinant clears the denominator of the inverse.
-/

@[expose] public section
noncomputable section

namespace TwoPoint

/-- Entrywise inclusion of integer matrices into rational matrices. -/
def intMatrixCast (n : ℕ) : Matrix (Fin n) (Fin n) ℤ →+* Matrix (Fin n) (Fin n) ℚ :=
  (Int.castRingHom ℚ).mapMatrix

theorem intMatrixCast_det {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    (intMatrixCast n A).det = (A.det : ℚ) :=
  ((Int.castRingHom ℚ).map_det A).symm

/-- An explicit integer quotient when the numerator matrix differs from a
scalar multiple of the denominator by its determinant times an integer matrix. -/
theorem intMatrix_quotient_of_decomposition {n : ℕ} (X Y A : Matrix (Fin n) (Fin n) ℤ)
    (c : ℤ) (hX : X.det ≠ 0) (hY : Y = c • X + X.det • A) :
    intMatrixCast n (c • 1 + A * X.adjugate) = intMatrixCast n Y * (intMatrixCast n X)⁻¹ := by
  let G := c • (1 : Matrix (Fin n) (Fin n) ℤ) + A * X.adjugate
  have hGX : G * X = Y := by
    rw [hY]
    dsimp only [G]
    rw [add_mul, Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul,
      Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]
  have hcast : intMatrixCast n G * intMatrixCast n X = intMatrixCast n Y := by
    rw [← map_mul, hGX]
  have hx : IsUnit (intMatrixCast n X).det := by
    rw [intMatrixCast_det]
    exact isUnit_iff_ne_zero.mpr (by exact_mod_cast hX)
  have heq := congrArg (fun Z => Z * (intMatrixCast n X)⁻¹) hcast
  simpa only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hx, Matrix.mul_one] using heq

/-- The same integrality criterion stated as entrywise divisibility. -/
theorem intMatrix_quotient_integral {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℤ)
    (c : ℤ) (hX : X.det ≠ 0)
    (hcong : ∀ r s, X.det ∣ Y r s - c * X r s) :
    ∃ G : Matrix (Fin n) (Fin n) ℤ,
      G * X = Y ∧ intMatrixCast n G = intMatrixCast n Y * (intMatrixCast n X)⁻¹ := by
  choose f hf using hcong
  let A : Matrix (Fin n) (Fin n) ℤ := Matrix.of f
  have hA : ∀ r s, Y r s - c * X r s = X.det * A r s := hf
  have hY : Y = c • X + X.det • A := by
    apply Matrix.ext
    intro r s
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    linear_combination hA r s
  refine ⟨c • 1 + A * X.adjugate, ?_, intMatrix_quotient_of_decomposition X Y A c hX hY⟩
  rw [hY]
  rw [add_mul, Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul,
    Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]

/-- If the determinants differ by a unit, the integral quotient is unimodular. -/
theorem intMatrix_quotient_isUnit {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℤ)
    (c ε : ℤ) (hX : X.det ≠ 0) (hε : IsUnit ε) (hdet : Y.det = ε * X.det)
    (hcong : ∀ r s, X.det ∣ Y r s - c * X r s) :
    ∃ G : Matrix (Fin n) (Fin n) ℤ, IsUnit G ∧
      intMatrixCast n G = intMatrixCast n Y * (intMatrixCast n X)⁻¹ := by
  obtain ⟨G, hGX, hG⟩ := intMatrix_quotient_integral X Y c hX hcong
  have hd : G.det = ε := by
    apply mul_right_cancel₀ hX
    rw [← Matrix.det_mul, hGX, hdet]
  exact ⟨G, (Matrix.isUnit_iff_isUnit_det _).mpr (hd ▸ hε), hG⟩

end TwoPoint
