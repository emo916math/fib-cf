module

public import TwoPoint.Decomposition

/-!
# The conclusion of Exercise `exer:main_gen`(b)

Exercise `exer:main_gen`(b) differs from Theorem 1.2(b) in two ways: the
moduli `m_i` are no longer ranks of apparition of `Δ_{k,i}` (they are given
by part (c)), and the word may end with a nonempty final junction
`J_(k, n mod m_k)`. The patch-junction data is the same `PatchJunctionData`;
only the assembled word and the conditions change.
-/

@[expose] public section

noncomputable section

namespace TwoPoint

/-- The word of Exercise `exer:main_gen`(b):

`J_(0,n mod m_0) P_(0,n mod g_0)^(e_0(n)) ⋯
 J_(k-1,n mod m_(k-1)) P_(k-1,n mod g_(k-1))^(e_(k-1)(n)) J_(k,n mod m_k)`. -/
def PatchJunctionData.wordFinal (D : PatchJunctionData) (k n : ℕ) : CFWord :=
  D.word k n ++ D.J k (n % D.m k)

/-- The conclusion of Exercise `exer:main_gen`(b), with the moduli `m_i`
(`i ≤ k`) prescribed by the function `m`.

* The moduli are the prescribed positive integers.
* Patch words are nonempty positive words, indexed modulo `g_i = gcd(m_i, m_(i+1))`.
* Junction words `J_i` for `i ≤ k`, including the final one, are positive
  words, possibly empty, indexed modulo `m_i`.
* Exponents are eventually affine with positive slope on residues modulo
  `lcm(m_i, m_(i+1))`.
* The concatenation represents `(u_(n+1)/u_n)^k` for all large `n`.
* One bound works for every term of all these expansions.
-/
def HasPatchJunctionDecompositionMod (a b : ℤ) (k : ℕ) (m : ℕ → ℕ) : Prop :=
  ∃ D : PatchJunctionData,
    (∀ i : ℕ, i ≤ k → D.m i = m i ∧ 0 < D.m i) ∧
    (∀ i : ℕ, i < k → ∀ r : ℕ, r < D.g i →
      D.P i r ≠ [] ∧ PositiveWord (D.P i r)) ∧
    (∀ i : ℕ, i ≤ k → ∀ r : ℕ, r < D.m i →
      PositiveWord (D.J i r)) ∧
    ∃ N : ℕ, 1 ≤ N ∧
      (∀ i : ℕ, i < k →
        GrowsAffinelyOnResidues (D.e i) (D.exponentModulus i) N) ∧
      (∀ n : ℕ, N ≤ n →
        IsContinuedFraction (ratioPower a b k n) (D.wordFinal k n)) ∧
      ∃ B : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ d : ℤ, d ∈ D.wordFinal k n → |d| ≤ (B : ℤ)

/-- Part (a) with a prescribed growth rate `R n`: for all large `n` the
continued fraction of `(u_(n+1)/u_n)^k` has a term between `c R n` and `C R n`.
`HasMonsterTerms a b k` is the case `R n = α^(2n)`. -/
def HasMonsterTermsRate (a b : ℤ) (k : ℕ) (R : ℕ → ℝ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∃ N : ℕ, 1 ≤ N ∧
      ∀ n : ℕ, N ≤ n →
        ∃ w : CFWord, IsContinuedFraction (ratioPower a b k n) w ∧
          ∃ M : ℤ, M ∈ w ∧ c * R n ≤ (M : ℝ) ∧ (M : ℝ) ≤ C * R n

theorem hasMonsterTerms_iff_rate (a b : ℤ) (k : ℕ) :
    HasMonsterTerms a b k ↔ HasMonsterTermsRate a b k (fun n => alpha a b ^ (2 * n)) := Iff.rfl

/-- `|ρ|`, the absolute value of the root ratio `ρ = α/ᾱ`. -/
def rhoAbs (a b : ℤ) : ℝ := |alpha a b / beta a b|

/-- The conditions of `HasPatchJunctionDecompositionMod` on fixed data `D`. -/
def PatchJunctionData.IsDecompositionMod (D : PatchJunctionData) (a b : ℤ) (k : ℕ)
    (m : ℕ → ℕ) : Prop :=
  (∀ i : ℕ, i ≤ k → D.m i = m i ∧ 0 < D.m i) ∧
    (∀ i : ℕ, i < k → ∀ r : ℕ, r < D.g i →
      D.P i r ≠ [] ∧ PositiveWord (D.P i r)) ∧
    (∀ i : ℕ, i ≤ k → ∀ r : ℕ, r < D.m i →
      PositiveWord (D.J i r)) ∧
    ∃ N : ℕ, 1 ≤ N ∧
      (∀ i : ℕ, i < k →
        GrowsAffinelyOnResidues (D.e i) (D.exponentModulus i) N) ∧
      (∀ n : ℕ, N ≤ n →
        IsContinuedFraction (ratioPower a b k n) (D.wordFinal k n)) ∧
      ∃ B : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ d : ℤ, d ∈ D.wordFinal k n → |d| ≤ (B : ℤ)

theorem hasPatchJunctionDecompositionMod_iff (a b : ℤ) (k : ℕ) (m : ℕ → ℕ) :
    HasPatchJunctionDecompositionMod a b k m ↔ ∃ D : PatchJunctionData, D.IsDecompositionMod a b k m :=
  Iff.rfl

/-- The conditions of `HasPatchJunctionDecomposition` (Theorem 1.2(b)) on fixed data `D`. -/
def PatchJunctionData.IsDecomposition (D : PatchJunctionData) (a b : ℤ) (k : ℕ) : Prop :=
  (∀ i : ℕ, i ≤ k → IsRankOfApparition a b (delta a b k i) (D.m i)) ∧
    (∀ i : ℕ, i < k → ∀ r : ℕ, r < D.g i →
      D.P i r ≠ [] ∧ PositiveWord (D.P i r)) ∧
    (∀ i : ℕ, i < k → ∀ r : ℕ, r < D.m i →
      PositiveWord (D.J i r)) ∧
    ∃ N : ℕ, 1 ≤ N ∧
      (∀ i : ℕ, i < k →
        GrowsAffinelyOnResidues (D.e i) (D.exponentModulus i) N) ∧
      (∀ n : ℕ, N ≤ n →
        IsContinuedFraction (ratioPower a b k n) (D.word k n)) ∧
      ∃ B : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ d : ℤ, d ∈ D.word k n → |d| ≤ (B : ℤ)

theorem hasPatchJunctionDecomposition_iff (a b : ℤ) (k : ℕ) :
    HasPatchJunctionDecomposition a b k ↔ ∃ D : PatchJunctionData, D.IsDecomposition a b k :=
  Iff.rfl

/-- Boundedness of the words with a final junction, from the finite families. -/
theorem PatchJunctionData.exists_uniform_bound_final (D : PatchJunctionData) (k : ℕ)
    (hm : ∀ i, i ≤ k → 0 < D.m i) :
    ∃ B : ℕ, ∀ n : ℕ, ∀ d : ℤ, d ∈ D.wordFinal k n → |d| ≤ (B : ℤ) := by
  obtain ⟨B₁, hB₁⟩ := D.exists_uniform_bound k hm
  set F : CFWord := (List.range (D.m k)).flatMap (D.J k)
  refine ⟨B₁ + (F.map Int.natAbs).sum, ?_⟩
  intro n d hd
  rcases List.mem_append.mp hd with h | h
  · have := hB₁ n d h
    rw [Nat.cast_add]
    have : (0 : ℤ) ≤ ((F.map Int.natAbs).sum : ℕ) := Nat.cast_nonneg _
    omega
  · have hF : d ∈ F := List.mem_flatMap.mpr
      ⟨n % D.m k, List.mem_range.mpr (Nat.mod_lt _ (hm k le_rfl)), h⟩
    have hmem : d.natAbs ∈ F.map Int.natAbs := List.mem_map.mpr ⟨d, hF, rfl⟩
    have hle := List.le_sum_of_mem hmem
    have hcast : (d.natAbs : ℤ) ≤ ((F.map Int.natAbs).sum : ℤ) := by exact_mod_cast hle
    rw [Int.natCast_natAbs] at hcast
    rw [Nat.cast_add]
    have := abs_nonneg d
    omega

end TwoPoint
