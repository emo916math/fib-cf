module

public import TwoPoint.Recurrence
public import TwoPoint.Determinants
public import TwoPoint.ContinuedFractions

@[expose] public section

noncomputable section

namespace TwoPoint

/-! ## Ranks, periods, and the concatenated word -/

/-- The word families and repetition counts in part (b).

For exponent `k`, only `m i` with `i ≤ k` and `P i`, `J i`, `e i` with
`i < k` are used. Natural-number indexing keeps `m i` and `m (i+1)` legible.
The second arguments of `P` and `J` are residue indices. The assembled word
below explicitly reduces these indices modulo `g_i` and `m_i`.
-/
structure PatchJunctionData where
  m : ℕ → ℕ
  P : ℕ → ℕ → CFWord
  J : ℕ → ℕ → CFWord
  e : ℕ → ℕ → ℕ

/-- `g_i = gcd(m_i, m_(i+1))`, the modulus for the patch word. -/
def PatchJunctionData.g (D : PatchJunctionData) (i : ℕ) : ℕ :=
  Nat.gcd (D.m i) (D.m (i + 1))

/-- `lcm(m_i, m_(i+1))`, the modulus for the affine exponent formulas. -/
def PatchJunctionData.exponentModulus (D : PatchJunctionData) (i : ℕ) : ℕ :=
  Nat.lcm (D.m i) (D.m (i + 1))

/-- The complete word, in order:

`J_(0,n mod m_0) P_(0,n mod g_0)^(e_0(n)) ...
 J_(k-1,n mod m_(k-1)) P_(k-1,n mod g_(k-1))^(e_(k-1)(n))`.

There are exactly `k` patch blocks and no final `J_k`. Since the ranks of
`delta a b k 0 = 1` and `delta a b k k = 1` are both `1`, the first junction
and the first and last patch words are independent of `n`. This definition
also handles `k = 1` as a single patch, with no separate endpoint choices.
-/
def PatchJunctionData.word (D : PatchJunctionData) (k n : ℕ) : CFWord :=
  ((List.range k).map fun i =>
    D.J i (n % D.m i) ++ repeatWord (D.P i (n % D.g i)) (D.e i n)).flatten

/-- On each residue class modulo `L`, `e(n)` eventually agrees with an
affine function `A*n + B` with rational coefficients and positive slope.

Here "linear" includes the constant term, as it does in the paper. The
condition is only imposed for `n ≥ N`: small indices may give negative
values of the affine expression even though repetition counts are natural.

The explicit condition `0 < A` records the *growing* patches described in
the abstract and proved in §3 by `alpha^n = c' * lambda^(e(n))`, with
`alpha > 1` and `lambda > 1`. The sentence in Theorem 1.2(b) says "linear"
without separately writing this inequality. No formula for `A`, equality
of slopes in different residues, or minimality of the modulus is imposed.
-/
def GrowsAffinelyOnResidues (e : ℕ → ℕ) (L N : ℕ) : Prop :=
  ∀ r : ℕ, r < L →
    ∃ A B : ℚ, 0 < A ∧
      ∀ n : ℕ, N ≤ n → n % L = r →
        (e n : ℚ) = A * (n : ℚ) + B

/-! ## The two conclusions of Theorem 1.2 -/

/-- Part (a): constants `c,C > 0` and a threshold `N ≥ 1` work for every
`n ≥ N`. The expansion and its selected monster term may vary with `n`.
No uniqueness or fixed position of the monster term is asserted. -/
def HasMonsterTerms (a b : ℤ) (k : ℕ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∃ N : ℕ, 1 ≤ N ∧
      ∀ n : ℕ, N ≤ n →
        ∃ w : CFWord, IsContinuedFraction (ratioPower a b k n) w ∧
          ∃ M : ℤ, M ∈ w ∧
            c * alpha a b ^ (2 * n) ≤ (M : ℝ) ∧
            (M : ℝ) ≤ C * alpha a b ^ (2 * n)

/-- Part (b), with all witnesses independent of `n` except as explicitly
specified by their arguments.

* Every `m_i` is the least positive index of divisibility by `delta a b k i`.
* Patch words are nonempty positive words, indexed modulo `g_i`.
* Junction words are positive words, possibly empty, indexed modulo `m_i`.
* Exponents are eventually affine on residues modulo `lcm(m_i,m_(i+1))`.
* The concatenation represents the required rational number for all large `n`.
* One bound works for every term of all these expansions.

The boundedness clause is included explicitly to match the last sentence
of the theorem, though it follows from the finite families of words.
Patch words need not be primitive periods; Theorem 1.2 does not require this.
-/
def HasPatchJunctionDecomposition (a b : ℤ) (k : ℕ) : Prop :=
  ∃ D : PatchJunctionData,
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

/-- A finite list containing every term that can occur in a patch or junction
at one of the residue indices used in the decomposition. -/
def PatchJunctionData.alphabet (D : PatchJunctionData) (k : ℕ) : CFWord :=
  (List.range k).flatMap fun i =>
    (List.range (D.m i)).flatMap (D.J i) ++ (List.range (D.g i)).flatMap (D.P i)

theorem PatchJunctionData.mem_alphabet_of_mem_word (D : PatchJunctionData) (k n : ℕ)
    (hm : ∀ i, i ≤ k → 0 < D.m i) {d : ℤ} (hd : d ∈ D.word k n) :
    d ∈ D.alphabet k := by
  simp only [word, List.mem_flatten, List.mem_map] at hd
  obtain ⟨w, ⟨i, hi, rfl⟩, hd⟩ := hd
  have hik : i < k := List.mem_range.mp hi
  have hmi := hm i (Nat.le_of_lt hik)
  have hgi : 0 < D.g i := Nat.gcd_pos_of_pos_left _ hmi
  simp only [alphabet, List.mem_flatMap, List.mem_append, List.mem_range]
  refine ⟨i, hik, ?_⟩
  rcases List.mem_append.mp hd with hJ | hP
  · exact Or.inl ⟨n % D.m i, Nat.mod_lt _ hmi, hJ⟩
  · exact Or.inr ⟨n % D.g i, Nat.mod_lt _ hgi, mem_of_mem_repeatWord hP⟩

/-- Boundedness follows from the finite residue-indexed families, independently
of how fast the repetition counts grow. -/
theorem PatchJunctionData.exists_uniform_bound (D : PatchJunctionData) (k : ℕ)
    (hm : ∀ i, i ≤ k → 0 < D.m i) :
    ∃ B : ℕ, ∀ n : ℕ, ∀ d : ℤ, d ∈ D.word k n → |d| ≤ (B : ℤ) := by
  refine ⟨((D.alphabet k).map Int.natAbs).sum, ?_⟩
  intro n d hd
  have hmem : d.natAbs ∈ (D.alphabet k).map Int.natAbs :=
    List.mem_map.mpr ⟨d, D.mem_alphabet_of_mem_word k n hm hd, rfl⟩
  have hle := List.le_sum_of_mem hmem
  have hcast : (d.natAbs : ℤ) ≤ (((D.alphabet k).map Int.natAbs).sum : ℤ) := by
    exact_mod_cast hle
  simpa only [Int.natCast_natAbs] using hcast

/-- The final assembly step: once the periodic families, affine exponents,
and representation are constructed, the boundedness clause is automatic. -/
theorem hasPatchJunctionDecomposition_of_data (a b : ℤ) (k : ℕ)
    (D : PatchJunctionData)
    (hm : ∀ i, i ≤ k → IsRankOfApparition a b (delta a b k i) (D.m i))
    (hP : ∀ i, i < k → ∀ r, r < D.g i → D.P i r ≠ [] ∧ PositiveWord (D.P i r))
    (hJ : ∀ i, i < k → ∀ r, r < D.m i → PositiveWord (D.J i r))
    (N : ℕ) (hN : 1 ≤ N)
    (he : ∀ i, i < k → GrowsAffinelyOnResidues (D.e i) (D.exponentModulus i) N)
    (hw : ∀ n, N ≤ n → IsContinuedFraction (ratioPower a b k n) (D.word k n)) :
    HasPatchJunctionDecomposition a b k := by
  obtain ⟨B, hB⟩ := D.exists_uniform_bound k (fun i hi => (hm i hi).1)
  exact ⟨D, hm, hP, hJ, N, hN, he, hw, B, fun n _ d hd => hB n d hd⟩

/-- The first and final ranks are one because the boundary determinants are one. -/
theorem PatchJunctionData.boundary_ranks (D : PatchJunctionData) (a b : ℤ) (k : ℕ)
    (hm : ∀ i, i ≤ k → IsRankOfApparition a b (delta a b k i) (D.m i)) :
    D.m 0 = 1 ∧ D.m k = 1 := by
  have hzero := hm 0 (Nat.zero_le k)
  have hself := hm k le_rfl
  rw [delta_zero] at hzero
  rw [delta_self] at hself
  exact ⟨hzero.unique (rankOfApparition_one a b), hself.unique (rankOfApparition_one a b)⟩

end TwoPoint
