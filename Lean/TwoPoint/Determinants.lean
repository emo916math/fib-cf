module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Tactic

@[expose] public section

noncomputable section

namespace TwoPoint

/-! ## The explicit Padé–Toeplitz polynomials -/

/-- The characteristic polynomial `h(x) = x^2 - a*x - b`. -/
def characteristicPolynomial {R : Type*} [CommRing R] (a b : R) : Polynomial R :=
  Polynomial.X ^ 2 - Polynomial.C a * Polynomial.X - Polynomial.C b

/-- The coefficient `c_j` in `h(x)^i = Σ_j c_j x^(2*i-j)`.
The index is an integer: coefficients outside `0 ≤ j ≤ 2*i` are zero. -/
def hPowerCoeff {R : Type*} [CommRing R] (a b : R) (i : ℕ) (j : ℤ) : R :=
  if 0 ≤ j ∧ j ≤ 2 * (i : ℤ) then
    (characteristicPolynomial a b ^ i).coeff (2 * (i : ℤ) - j).toNat
  else 0

/-- The `(k-i) × (k-i)` matrix `C_{k,i}` of Lemma 2.1.
Rows and columns start at zero; entry `(r,s)` is `c_(i+s-r)`. -/
def padeToeplitz {R : Type*} [CommRing R] (a b : R) (k i : ℕ) :
    Matrix (Fin (k - i)) (Fin (k - i)) R :=
  fun r s => hPowerCoeff a b i ((i : ℤ) + (s.val : ℤ) - (r.val : ℤ))

/-- The Padé–Toeplitz determinant, over any commutative coefficient ring. -/
def deltaOver {R : Type*} [CommRing R] (a b : R) (k i : ℕ) : R :=
  (padeToeplitz a b k i).det

/-- The explicit polynomial `Δ_{k,i} ∈ ℤ[a,b]`.
The variables numbered `0` and `1` represent `a` and `b`, respectively. -/
def deltaPolynomial (k i : ℕ) : MvPolynomial (Fin 2) ℤ :=
  deltaOver (MvPolynomial.X (0 : Fin 2)) (MvPolynomial.X (1 : Fin 2)) k i

/-- Evaluation of the determinant polynomial at integer parameters `(a,b)`. -/
def delta (a b : ℤ) (k i : ℕ) : ℤ :=
  MvPolynomial.eval (fun t : Fin 2 => if t.val = 0 then a else b)
    (deltaPolynomial k i)

theorem padeToeplitz_zero {R : Type*} [CommRing R] (a b : R) (k : ℕ) :
    padeToeplitz a b k 0 = 1 := by
  ext r s
  by_cases hrs : r = s
  · subst s
    simp [padeToeplitz, hPowerCoeff]
  · have hnot : ¬ (0 ≤ (s.val : ℤ) - (r.val : ℤ) ∧
        (s.val : ℤ) - (r.val : ℤ) ≤ 0) := by
      intro h
      apply hrs
      apply Fin.ext
      exact Int.ofNat.inj (sub_eq_zero.mp (le_antisymm h.2 h.1)).symm
    simp only [padeToeplitz, hPowerCoeff, Nat.cast_zero, mul_zero, zero_add,
      ite_eq_right hnot, Matrix.one_apply, ite_eq_right hrs]

theorem deltaPolynomial_zero (k : ℕ) : deltaPolynomial k 0 = 1 := by
  simp [deltaPolynomial, deltaOver, padeToeplitz_zero]

theorem deltaPolynomial_self (k : ℕ) : deltaPolynomial k k = 1 := by
  have : IsEmpty (Fin (k - k)) := by
    rw [Nat.sub_self]
    infer_instance
  exact Matrix.det_isEmpty

/-- The evaluated boundary identity `Δ_{k,0}(a,b) = 1`. -/
theorem delta_zero (a b : ℤ) (k : ℕ) : delta a b k 0 = 1 := by
  simp [delta, deltaPolynomial_zero]

/-- The evaluated boundary identity `Δ_{k,k}(a,b) = 1`. -/
theorem delta_self (a b : ℤ) (k : ℕ) : delta a b k k = 1 := by
  simp [delta, deltaPolynomial_self]

/-- Formation of the characteristic polynomial commutes with changing rings. -/
theorem characteristicPolynomial_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a b : R) :
    (characteristicPolynomial a b).map f = characteristicPolynomial (f a) (f b) := by
  simp [characteristicPolynomial]

theorem hPowerCoeff_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a b : R) (i : ℕ) (j : ℤ) :
    f (hPowerCoeff a b i j) = hPowerCoeff (f a) (f b) i j := by
  unfold hPowerCoeff
  split_ifs
  · rw [← Polynomial.coeff_map, Polynomial.map_pow, characteristicPolynomial_map]
  · exact f.map_zero

theorem deltaOver_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a b : R) (k i : ℕ) :
    f (deltaOver a b k i) = deltaOver (f a) (f b) k i := by
  unfold deltaOver
  rw [f.map_det]
  congr 1
  ext r s
  exact hPowerCoeff_map f a b i _

/-- Evaluating the universal determinant is the same as taking the determinant
of the evaluated coefficient matrix. -/
theorem delta_eq_deltaOver (a b : ℤ) (k i : ℕ) :
    delta a b k i = deltaOver a b k i := by
  unfold delta deltaPolynomial
  rw [deltaOver_map]
  simp

/-- The singularity criterion over the integers. This is the linear-algebra
step in Lemma 2.1; the coefficient interpretation gives the Padé relation. -/
theorem delta_eq_zero_iff_exists_kernel (a b : ℤ) (k i : ℕ) :
    delta a b k i = 0 ↔
      ∃ e : Fin (k - i) → ℤ, e ≠ 0 ∧ (padeToeplitz a b k i).mulVec e = 0 := by
  rw [delta_eq_deltaOver]
  exact Matrix.exists_mulVec_eq_zero_iff.symm

/-- The same criterion over the rational coefficient field used for Padé spaces. -/
theorem delta_eq_zero_iff_exists_rat_kernel (a b : ℤ) (k i : ℕ) :
    delta a b k i = 0 ↔
      ∃ e : Fin (k - i) → ℚ, e ≠ 0 ∧
        (padeToeplitz (a : ℚ) (b : ℚ) k i).mulVec e = 0 := by
  rw [Matrix.exists_mulVec_eq_zero_iff, delta_eq_deltaOver]
  change deltaOver a b k i = 0 ↔ deltaOver (a : ℚ) (b : ℚ) k i = 0
  have hm := deltaOver_map (Int.castRingHom ℚ) a b k i
  dsimp at hm
  rw [← hm]
  exact Int.cast_eq_zero.symm

/-- A vanishing determinant is necessarily at an interior index. -/
theorem delta_zero_index_bounds {a b : ℤ} {k i : ℕ} (hi : i ≤ k)
    (hzero : delta a b k i = 0) : 0 < i ∧ i < k := by
  have hi0 : i ≠ 0 := by
    intro h
    subst i
    simp [delta_zero] at hzero
  have hik : i ≠ k := by
    intro h
    subst i
    simp [delta_self] at hzero
  omega

end TwoPoint
