module

public import TwoPoint.MatrixProduct
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.IndexNSmul

/-!
# The integer lattice underlying the Padé basis

The leading-coefficient lattice is the inverse image of the Toeplitz column
lattice under the inhomogeneous right-hand-side map. The index calculation
uses Mathlib's determinant formula for quotients of free integer modules.
-/

@[expose] public section
noncomputable section

namespace TwoPoint

open Polynomial

theorem intMatrix_toLin_injective {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : A.det ≠ 0) : Function.Injective (Matrix.toLin' A) := by
  intro x y hxy
  have hz : A.mulVec (x - y) = 0 := by
    change (Matrix.toLin' A) (x - y) = 0
    rw [map_sub, hxy, sub_self]
  have hsub : x - y = 0 := by
    by_contra hne
    exact hA (Matrix.exists_mulVec_eq_zero_iff.mp ⟨x - y, hne, hz⟩)
  exact sub_eq_zero.mp hsub

/-- The index of the column lattice of an integer matrix is the absolute
value of its determinant. -/
theorem intMatrix_range_index {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : A.det ≠ 0) : (LinearMap.range (Matrix.toLin' A)).toAddSubgroup.index = A.det.natAbs := by
  let f := Matrix.toLin' A
  let e := LinearEquiv.ofInjective f (intMatrix_toLin_injective A hA)
  have hh := Submodule.natAbs_det_equiv (LinearMap.range f) e
  have heq : (LinearMap.range f).subtype ∘ₗ
      AddMonoidHom.toIntLinearMap (e : (Fin n → ℤ) →+ LinearMap.range f) = f := by
    ext x r
    rfl
  rw [heq, LinearMap.det_toLin'] at hh
  exact hh.symm

/-- Pulling a column lattice back along an integer linear map can only
decrease its index by a divisor. -/
theorem intMatrix_preimage_index_dvd {m n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : A.det ≠ 0) (f : (Fin m → ℤ) →ₗ[ℤ] (Fin n → ℤ)) :
    ((LinearMap.range (Matrix.toLin' A)).toAddSubgroup.comap f.toAddMonoidHom).index ∣
      A.det.natAbs := by
  rw [AddSubgroup.index_comap, ← intMatrix_range_index A hA]
  exact AddSubgroup.relIndex_dvd_index_of_normal _ _

/-- Right-hand side of the coefficient system for prescribed leading
coefficients `p = v 0`, `q = v 1`. -/
def padeLeadingRhs (a b : ℤ) (k i : ℕ) :
    (Fin 2 → ℤ) →ₗ[ℤ] (Fin (k - i) → ℤ) where
  toFun v r := -(v 0 * (if r.val = 0 then 1 else 0) +
    v 1 * (X ^ (k - i) * characteristicPolynomial a b ^ i).coeff (i + r.val))
  map_add' v w := by
    ext r
    simp only [Pi.add_apply]
    ring
  map_smul' c v := by
    ext r
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The lattice defined by solvability of the integral Toeplitz system. -/
def padeLeadingLattice (a b : ℤ) (k i : ℕ) : AddSubgroup (Fin 2 → ℤ) :=
  (LinearMap.range (Matrix.toLin' (padeToeplitz a b k i))).toAddSubgroup.comap
    (padeLeadingRhs a b k i).toAddMonoidHom

theorem mem_padeLeadingLattice_iff (a b : ℤ) (k i : ℕ) (v : Fin 2 → ℤ) :
    v ∈ padeLeadingLattice a b k i ↔
      ∃ e : Fin (k - i) → ℤ, (padeToeplitz a b k i).mulVec e = padeLeadingRhs a b k i v :=
  Iff.rfl

/-- The index divisibility in Lemma `lem:Delta_dvd`, for the lattice defined
by the inhomogeneous Toeplitz equations. -/
theorem padeLeadingLattice_index_dvd (a b : ℤ) (k i : ℕ) (hd : delta a b k i ≠ 0) :
    (padeLeadingLattice a b k i).index ∣ (delta a b k i).natAbs := by
  rw [delta_eq_deltaOver] at hd ⊢
  exact intMatrix_preimage_index_dvd (padeToeplitz a b k i) hd (padeLeadingRhs a b k i)

theorem padeLeadingLattice_index_pos (a b : ℤ) (k i : ℕ) (hd : delta a b k i ≠ 0) :
    0 < (padeLeadingLattice a b k i).index :=
  Nat.pos_of_dvd_of_pos (padeLeadingLattice_index_dvd a b k i hd) (Int.natAbs_pos.mpr hd)

/-- An integral solution of the Toeplitz system constructs an integral Padé
pair with the prescribed leading coefficients. -/
theorem exists_integral_padePair_of_mem_lattice (a b : ℤ) {k i : ℕ}
    (hk : 0 < k) (hi : i ≤ k) (v : Fin 2 → ℤ)
    (hv : v ∈ padeLeadingLattice a b k i) :
    ∃ P Q : Polynomial ℤ,
      P.degree ≤ i ∧ Q.degree ≤ i ∧ P.coeff i = v 0 ∧ Q.coeff i = v 1 ∧
      characteristicPolynomial a b ^ i ∣ X ^ k * Q - P := by
  obtain ⟨e, he⟩ := (mem_padeLeadingLattice_iff a b k i v).mp hv
  let H := characteristicPolynomial a b ^ i
  let E₀ := ofFn (k - i) e
  let E := E₀ + C (v 1) * X ^ (k - i)
  let G := E * H + C (v 0) * X ^ i
  have hE₀ : E₀.natDegree ≤ k - i :=
    natDegree_le_iff_degree_le.mpr (ofFn_degree_lt e).le
  have hqdeg : (C (v 1) * (X : Polynomial ℤ) ^ (k - i)).natDegree ≤ k - i :=
    (natDegree_C_mul_le _ _).trans (natDegree_X_pow_le _)
  have hE : E.natDegree ≤ k - i :=
    (natDegree_add_le _ _).trans (max_le hE₀ hqdeg)
  have hpdeg : (C (v 0) * (X : Polynomial ℤ) ^ i).natDegree ≤ i :=
    (natDegree_C_mul_le _ _).trans (natDegree_X_pow_le _)
  have hH : H.natDegree ≤ 2 * i := hPower_natDegree_le a b i
  have hG : G.natDegree ≤ k + i := by
    have hmul := natDegree_mul_le (p := E) (q := H)
    have hadd := natDegree_add_le (E * H) (C (v 0) * X ^ i)
    change (E * H + C (v 0) * X ^ i).natDegree ≤ k + i
    omega
  have hEcoeff : E.coeff (k - i) = v 1 := by
    simp [E, E₀, coeff_add, ofFn_coeff_eq_zero_of_ge e le_rfl]
  have hGcoeff : G.coeff (k + i) = v 1 := by
    have hidx : k + i = (k - i) + 2 * i := by omega
    change (E * H + C (v 0) * X ^ i).coeff (k + i) = v 1
    rw [coeff_add]
    have hpzero : (C (v 0) * (X : Polynomial ℤ) ^ i).coeff (k + i) = 0 :=
      coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hpzero, add_zero, hidx, coeff_mul_add_eq_of_natDegree_le hE hH, hEcoeff]
    simp only [H, hPower_coeff_top, mul_one]
  have hgap : ∀ r : Fin (k - i), G.coeff (i + r.val) = 0 := by
    intro r
    have hGeq : G = E₀ * H +
        (C (v 1) * (X ^ (k - i) * H) + C (v 0) * X ^ i) := by
      dsimp [G, E]
      ring
    rw [hGeq, coeff_add]
    change (ofFn (k - i) e * characteristicPolynomial a b ^ i).coeff (i + r.val) + _ = 0
    rw [← padeToeplitz_mulVec_eq_coeff, congrFun he r]
    simp [padeLeadingRhs, coeff_add, coeff_X_pow, H]
    ring
  obtain ⟨L, Q, hL, hQ, hQc, hsplit⟩ := split_polynomial_at_gap G hi hG hgap
  refine ⟨C (v 0) * X ^ i - L, Q, ?_, hQ, ?_, hQc.trans hGcoeff, ?_⟩
  · exact (degree_sub_le _ _).trans
      (max_le (natDegree_le_iff_degree_le.mp hpdeg) hL.le)
  · rw [coeff_sub, coeff_C_mul, coeff_X_pow_self, mul_one,
      coeff_eq_zero_of_degree_lt hL, sub_zero]
  · refine ⟨E, ?_⟩
    dsimp only [G] at hsplit
    linear_combination hsplit

/-- A two-column integral basis matrix for the solvability lattice, with
determinant of the exact index (up to sign). -/
theorem exists_padeLeadingLattice_basis (a b : ℤ) (k i : ℕ) (hd : delta a b k i ≠ 0) :
    ∃ Γ : Matrix (Fin 2) (Fin 2) ℤ,
      Γ.det ≠ 0 ∧ Γ.det.natAbs = (padeLeadingLattice a b k i).index ∧
      ∀ c, (fun r => Γ r c) ∈ padeLeadingLattice a b k i := by
  let L := padeLeadingLattice a b k i
  let : L.FiniteIndex := ⟨Nat.ne_of_gt (padeLeadingLattice_index_pos a b k i hd)⟩
  have : Module.Finite ℤ L :=
    inferInstanceAs (Module.Finite ℤ (AddSubgroup.toIntSubmodule L))
  have : Module.Free ℤ L :=
    inferInstanceAs (Module.Free ℤ (AddSubgroup.toIntSubmodule L))
  have hrank : Module.finrank ℤ L = 2 := by
    rw [AddSubgroup.finrank_eq_of_finiteIndex]
    simp
  let β := Module.finBasisOfFinrankEq ℤ L hrank
  let Γ : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of fun r c => (β c).val r
  have hdet : Γ.det.natAbs = L.index := by
    have hh := AddSubgroup.index_eq_natAbs_det (Pi.basisFun ℤ (Fin 2)) L β
    rw [Pi.basisFun_det_apply] at hh
    have heq : Matrix.of (fun c => (β c).val) = Γ.transpose := rfl
    rw [heq, Matrix.det_transpose] at hh
    exact hh.symm
  refine ⟨Γ, ?_, hdet, fun c => (β c).property⟩
  intro hz
  have := padeLeadingLattice_index_pos a b k i hd
  rw [hz, Int.natAbs_zero] at hdet
  exact Nat.ne_of_gt this hdet.symm

end TwoPoint
