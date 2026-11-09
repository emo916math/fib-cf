module

public import TwoPoint.PadeBasis
public import TwoPoint.Recurrence

/-!
# The moduli of Exercise `exer:main_gen`(c)

For a matrix `A` of rational polynomials of degree at most `i` (a
dehomogenized `Φ_i(x, 1)`), the homogeneous matrix `A(X, sY)` has the
coefficient `s^ℓ · [x^(i-ℓ)] A` at `X^(i-ℓ) Y^ℓ`. The integer `c(A(X, sY))`
is the least positive determinant of an integer matrix `C` for which
`A(X, sY) C` has integer coefficients. (The paper also describes `c` as the
least common denominator of the `2 × 2` minors of the coefficient matrix and
says the two descriptions are equivalent; we use the determinant description.)

With `t = a^2/b`, the modulus `m_i` is the least positive even integer `2m` for
which `lcm{c(Φ_i(X, aY/b)), c(Φ_i(X, Y/a))/t^i}` divides `u_(2m)/(a b^(m-1))`.
The divisibility is written without division, as
`lcm{…} · a b^(m-1) ∣ u_(2m)`; the quotient `u_(2m)/(a b^(m-1))` is an integer
(see `GenTransport`).
-/

@[expose] public section

noncomputable section

namespace TwoPoint

open Polynomial

/-- The coefficient matrix of `X^(i-ℓ) Y^ℓ` in `A(X, sY)`, where `A = A(x, 1)`
has entries of degree at most `i`. -/
def scaledCoeff (A : Matrix (Fin 2) (Fin 2) ℚ[X]) (i : ℕ) (s : ℚ) (ℓ : ℕ) :
    Matrix (Fin 2) (Fin 2) ℚ :=
  Matrix.of fun r c => s ^ ℓ * (A r c).coeff (i - ℓ)

/-- `A(X, sY) C` has integer coefficients. -/
def ClearsHom (A : Matrix (Fin 2) (Fin 2) ℚ[X]) (i : ℕ) (s : ℚ)
    (C : Matrix (Fin 2) (Fin 2) ℤ) : Prop :=
  ∀ ℓ, ℓ ≤ i → ∀ r c, ∃ z : ℤ, (scaledCoeff A i s ℓ * C.map (Int.cast : ℤ → ℚ)) r c = z

/-- `c(A(X, sY))`: the least positive determinant of an integer matrix `C` with
`A(X, sY) C` integral. -/
def clearingDet (A : Matrix (Fin 2) (Fin 2) ℚ[X]) (i : ℕ) (s : ℚ) : ℕ :=
  sInf {d : ℕ | 0 < d ∧ ∃ C : Matrix (Fin 2) (Fin 2) ℤ, ClearsHom A i s C ∧ C.det = d}

/-- `lcm{c(A(X, aY/b)), c(A(X, Y/a))/t^i}` with `t = a^2/b`. -/
def exerLcm (a b : ℤ) (A : Matrix (Fin 2) (Fin 2) ℚ[X]) (i : ℕ) : ℕ :=
  Nat.lcm (clearingDet A i ((a : ℚ) / b))
    (clearingDet A i (1 / (a : ℚ)) / (tRatio a b).natAbs ^ i)

/-- The modulus of Exercise `exer:main_gen`(c) for `A = Φ_i(x, 1)`: the least
positive even `2m` with `exerLcm ∣ u_(2m)/(a b^(m-1))`. -/
def exerModulus (a b : ℤ) (A : Matrix (Fin 2) (Fin 2) ℚ[X]) (i : ℕ) : ℕ :=
  2 * sInf {m : ℕ | 0 < m ∧ ((exerLcm a b A i : ℕ) : ℤ) * (a * b ^ (m - 1)) ∣ u a b (2 * m)}

/-- A scalar multiple of the identity clears all denominators, so `c` is the
least element of a nonempty set. -/
theorem exists_clearsHom (A : Matrix (Fin 2) (Fin 2) ℚ[X]) (i : ℕ) (s : ℚ) :
    ∃ d : ℕ, 0 < d ∧ ∃ C : Matrix (Fin 2) (Fin 2) ℤ, ClearsHom A i s C ∧ C.det = d := by
  set D : ℕ := ∏ ℓ ∈ Finset.range (i + 1), ∏ r : Fin 2, ∏ c : Fin 2,
    (scaledCoeff A i s ℓ r c).den
  have hD : 0 < D := Finset.prod_pos fun ℓ _ => Finset.prod_pos fun r _ =>
    Finset.prod_pos fun c _ => (scaledCoeff A i s ℓ r c).den_pos
  refine ⟨D ^ 2, by positivity, !![(D : ℤ), 0; 0, (D : ℤ)], ?_, ?_⟩
  · intro ℓ hℓ r c
    have h1 : (scaledCoeff A i s ℓ r c).den ∣ ∏ c : Fin 2, (scaledCoeff A i s ℓ r c).den :=
      Finset.dvd_prod_of_mem (fun c => (scaledCoeff A i s ℓ r c).den) (Finset.mem_univ c)
    have h2 : ∏ c : Fin 2, (scaledCoeff A i s ℓ r c).den ∣
        ∏ r : Fin 2, ∏ c : Fin 2, (scaledCoeff A i s ℓ r c).den :=
      Finset.dvd_prod_of_mem (fun r => ∏ c : Fin 2, (scaledCoeff A i s ℓ r c).den)
        (Finset.mem_univ r)
    have h3 : ∏ r : Fin 2, ∏ c : Fin 2, (scaledCoeff A i s ℓ r c).den ∣ D :=
      Finset.dvd_prod_of_mem (fun ℓ => ∏ r : Fin 2, ∏ c : Fin 2, (scaledCoeff A i s ℓ r c).den)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hℓ))
    obtain ⟨e, he⟩ := h1.trans (h2.trans h3)
    refine ⟨(scaledCoeff A i s ℓ r c).num * e, ?_⟩
    have hent : (scaledCoeff A i s ℓ * (!![(D : ℤ), 0; 0, (D : ℤ)]).map (Int.cast : ℤ → ℚ)) r c =
        scaledCoeff A i s ℓ r c * D := by
      fin_cases c <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [hent, he]
    push_cast
    rw [← Rat.mul_den_eq_num]
    ring
  · simp [Matrix.det_fin_two]
    ring

theorem clearingDet_spec (A : Matrix (Fin 2) (Fin 2) ℚ[X]) (i : ℕ) (s : ℚ) :
    0 < clearingDet A i s ∧ ∃ C : Matrix (Fin 2) (Fin 2) ℤ,
      ClearsHom A i s C ∧ C.det = clearingDet A i s := by
  obtain ⟨d, hd⟩ := exists_clearsHom A i s
  exact Nat.sInf_mem (s := {d : ℕ | 0 < d ∧ ∃ C : Matrix (Fin 2) (Fin 2) ℤ,
    ClearsHom A i s C ∧ C.det = d}) ⟨d, hd⟩

end TwoPoint
