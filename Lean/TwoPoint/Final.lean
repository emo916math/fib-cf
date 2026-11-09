module

public import TwoPoint.Assembly
public import TwoPoint.GenDecomposition

/-!
# Theorem 1.2(b) and Exercise `exer:main_gen`(b): the patch-junction decomposition

The words are the patch generators `P_(i,ρ)`, the junction words `J_(i,ν)`
and the final junction `J_(k,ν)`; the repetition counts are the effective
exponents `e'_i(n)`. For large `n` all `e'_i(n) ≥ 0`, the concatenated word has
matrix `±∏ J_i P_i^(e'_i) · J_k`, and comparing first columns with
`U_k(n) = T_0^n ⋯ T_(k-1)^n` shows that it is a continued fraction for
`(u_(n+1)/u_n)^k`. When `m_k = 1` the final junction is empty
(Theorem 1.2(b)).
-/

@[expose] public section
noncomputable section

namespace TwoPoint

theorem CFWord.matrix_flatten (l : List CFWord) :
    CFWord.matrix l.flatten = (l.map CFWord.matrix).prod := by
  induction l with
  | nil => rfl
  | cons w l ih =>
    rw [List.flatten_cons, CFWord.matrix_append, ih]
    simp

theorem positiveWord_flatten {l : List CFWord} (h : ∀ w ∈ l, PositiveWord w) :
    PositiveWord l.flatten := by
  intro d hd
  obtain ⟨w, hw, hdw⟩ := List.mem_flatten.mp hd
  exact h w hw d hdw

namespace Ctx

variable (C : Ctx)

open scoped Classical in
/-- A nonempty positive word with matrix `M`, chosen as a function of `M`. -/
def wordOf (M : GL2Z) : CFWord :=
  if h : ∃ w : CFWord, PositiveWord w ∧ w ≠ [] ∧ w.matrix = (M : Matrix (Fin 2) (Fin 2) ℤ) then
    Classical.choose h
  else []

/-- The patch word for `P_(i,ρ)`. -/
def Pword (i ρ : ℕ) : CFWord := wordOf (C.P i ρ)

theorem Pword_spec {i : ℕ} (hi : i < C.k) (ρ : ℕ) :
    PositiveWord (C.Pword i ρ) ∧ C.Pword i ρ ≠ [] ∧
      (C.Pword i ρ).matrix = (C.P i ρ : Matrix (Fin 2) (Fin 2) ℤ) := by
  have : C.Pword i ρ = Classical.choose (C.exists_patch_word hi ρ) := by
    unfold Pword wordOf; rw [dif_pos (C.exists_patch_word hi ρ)]
  rw [this]
  exact Classical.choose_spec (C.exists_patch_word hi ρ)

/-- The decomposition data. -/
def data : PatchJunctionData where
  m := C.m
  P := C.Pword
  J := fun i ν => if i < C.k then C.Jword i ν else if i = C.k then C.Jfin ν else []
  e := fun i n => (C.e' n i).toNat

theorem data_g (i : ℕ) : C.data.g i = C.g i := rfl

theorem data_word (n : ℕ) :
    C.data.word C.k n = ((List.range C.k).map fun i =>
      C.Jword i (n % C.m i) ++ repeatWord (C.Pword i (n % C.g i)) (C.e' n i).toNat).flatten := by
  unfold PatchJunctionData.word
  congr 1
  apply List.map_congr_left
  intro i hi
  simp [data, List.mem_range.mp hi]
  rfl

theorem data_J_k (ν : ℕ) : C.data.J C.k ν = C.Jfin ν := by simp [data]

theorem data_wordFinal (n : ℕ) :
    C.data.wordFinal C.k n = C.data.word C.k n ++ C.Jfin (n % C.m C.k) := by
  rw [PatchJunctionData.wordFinal, data_J_k]
  rfl

theorem data_word_positive (n : ℕ) : PositiveWord (C.data.word C.k n) := by
  rw [data_word]
  apply positiveWord_flatten
  intro w hw
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
  have hik := List.mem_range.mp hi
  exact (positiveWord_append _ _).mpr ⟨(C.Jword_spec hik _).2.1,
    (C.Pword_spec hik _).1.repeatWord _⟩

theorem data_word_ne_nil (n : ℕ) : C.data.word C.k n ≠ [] := by
  rw [data_word]
  intro h
  have hk := C.hk
  have hmem : C.Jword 0 (n % C.m 0) ++ repeatWord (C.Pword 0 (n % C.g 0)) (C.e' n 0).toNat ∈
      (List.range C.k).map fun i =>
        C.Jword i (n % C.m i) ++ repeatWord (C.Pword i (n % C.g i)) (C.e' n i).toNat :=
    List.mem_map.mpr ⟨0, List.mem_range.mpr hk, rfl⟩
  have := List.flatten_eq_nil_iff.mp h _ hmem
  exact (C.Jword_spec hk _).2.2.1 rfl (List.append_eq_nil_iff.mp this).1

/-- With nonnegative exponents, the word matrix is `∏ J_i P_i^(e'_i)`. -/
theorem data_word_matrix (n : ℕ) (he : ∀ i, i < C.k → 0 ≤ C.e' n i) :
    (C.data.word C.k n).matrix = (C.prodJP n C.k : Matrix (Fin 2) (Fin 2) ℤ) := by
  rw [data_word, CFWord.matrix_flatten, prodJP, ← Units.coeHom_apply, map_list_prod,
    List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hik := List.mem_range.mp hi
  simp only [Function.comp_apply, Units.coeHom_apply, Units.val_mul, CFWord.matrix_append,
    CFWord.matrix_repeatWord]
  rw [(C.Jword_spec hik _).2.2.2, (C.Pword_spec hik _).2.2, C.P_mod]
  congr 1
  rw [← Int.toNat_of_nonneg (he i hik), zpow_natCast, Units.val_pow_eq_pow_val]
  rfl

theorem intToReal_mulVec_cast (M : Matrix (Fin 2) (Fin 2) ℤ) (v : Fin 2 → ℤ) :
    (intToReal M).mulVec (fun j => (v j : ℝ)) = fun j => ((M.mulVec v) j : ℝ) := by
  ext j
  simp [intToReal, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The first column of `U_k(n)` is `(u_(n+1)^k, u_n^k)`. -/
theorem U_k_mulVec (n : ℕ) :
    (C.U C.k n).mulVec ![1, 0] = fun j => ((![u C.a C.b (n + 1) ^ C.k, u C.a C.b n ^ C.k] j : ℤ) : ℝ) := by
  obtain ⟨h0, h1⟩ := C.S.prod_first_column C.a C.b C.hk C.hdQ n
  ext j
  fin_cases j
  · simp [U, Uq, T, ratToReal, Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0]
  · simp [U, Uq, T, ratToReal, Matrix.mulVec, dotProduct, Fin.sum_univ_two, h1]

theorem ratio_eq (n : ℕ) (hn : 1 ≤ n) (he : ∀ i, i < C.k → 0 ≤ C.e' n i) :
    IsContinuedFraction (ratioPower C.a C.b C.k n) (C.data.wordFinal C.k n) := by
  set ν := n % C.m C.k
  obtain ⟨hJf, -, c', hc', hJc⟩ := C.Jfin_spec ν
  have hpos : PositiveWord (C.data.wordFinal C.k n) := by
    rw [data_wordFinal]
    exact (positiveWord_append _ _).mpr ⟨C.data_word_positive n, hJf⟩
  have hne : C.data.wordFinal C.k n ≠ [] := by
    rw [data_wordFinal]
    exact fun h => C.data_word_ne_nil n (List.append_eq_nil_iff.mp h).1
  refine ⟨hne, ?_, ?_⟩
  · obtain ⟨c, t, ht⟩ := List.exists_cons_of_ne_nil hne
    rw [ht] at hpos ⊢
    exact ((positiveWord_cons c t).mp hpos).2
  rw [CFWord.cfValue_eq_matrix hpos]
  set M := (C.data.wordFinal C.k n).matrix
  have hM : M = (C.prodJP n C.k : Matrix (Fin 2) (Fin 2) ℤ) * (C.Jfin ν).matrix := by
    simp only [M, data_wordFinal, CFWord.matrix_append, C.data_word_matrix n he]
    rfl
  -- The first column of `U_k(n)` is a nonzero multiple of that of `M`.
  have hk := C.hk
  have hP : C.P (C.k - 1) n = C.P (C.k - 1) ν := by
    have h1 : C.k - 1 + 1 = C.k := by omega
    exact (C.P_eq_of_dvd (i := C.k - 1) (n := n) (ν := ν) (by rw [h1])
      (Nat.gcd_dvd_right _ _)).symm
  have hy : C.yn n C.k = (C.yfin ν : ℤ) := by simp [yn, ν]
  obtain ⟨c, hc, hU⟩ := C.U_k_eq n
  have hcol : ∃ d : ℝ, d ≠ 0 ∧ ∀ j, ((![u C.a C.b (n + 1) ^ C.k, u C.a C.b n ^ C.k] j : ℤ) : ℝ) =
      d * (M j 0 : ℝ) := by
    have hV := congrArg (fun A => A.mulVec ![(1 : ℝ), 0]) hU
    simp only [Matrix.smul_mulVec, C.U_k_mulVec n] at hV
    rw [← Matrix.mulVec_mulVec, C.U_k_mulVec ν, ← Matrix.mulVec_mulVec, intToReal_mulVec_cast] at hV
    change _ = c • fun j => ((![u C.a C.b (n + 1) ^ C.k, u C.a C.b n ^ C.k] j : ℤ) : ℝ) at hV
    -- Replace the prefix by `±prodJP · P^y`.
    obtain ⟨σ, hσ, hpre⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
        intToReal (C.Hpn n 0 * C.prodXC n C.k : GL2Z) = σ • (intToReal (C.prodJP n C.k) *
          intToReal ((C.P (C.k - 1) ν ^ C.yfin ν : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ)) := by
      rcases C.regroup n with h | h
      · refine ⟨1, Or.inl rfl, ?_⟩
        rw [h, hy, hP, one_smul, Units.val_mul, intToReal_mul, zpow_natCast]
      · refine ⟨-1, Or.inr rfl, ?_⟩
        rw [h, hy, hP, Units.val_neg, intToReal_neg, Units.val_mul, intToReal_mul, zpow_natCast,
          neg_one_smul]
    rw [hpre, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, intToReal_mulVec_cast] at hV
    change σ • (intToReal (C.prodJP n C.k)).mulVec (fun j => ((((C.P (C.k - 1) ν ^ C.yfin ν :
      GL2Z) : Matrix (Fin 2) (Fin 2) ℤ).mulVec (C.vfin ν) j : ℤ) : ℝ)) = _ at hV
    have hJc' : (fun j => ((((C.P (C.k - 1) ν ^ C.yfin ν : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ).mulVec
        (C.vfin ν) j : ℤ) : ℝ)) = (c' : ℝ) • fun j => (((C.Jfin ν).matrix.mulVec ![1, 0] j : ℤ) : ℝ) := by
      ext j
      simp only [Pi.smul_apply, smul_eq_mul]
      have h := congrArg (Rat.cast : ℚ → ℝ) (hJc j)
      rw [Rat.cast_mul, Rat.cast_intCast, Rat.cast_intCast] at h
      rw [h]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [hJc', Matrix.mulVec_smul, intToReal_mulVec_cast, Matrix.mulVec_mulVec, ← hM] at hV
    refine ⟨σ * c' / c, div_ne_zero (mul_ne_zero (by rcases hσ with rfl | rfl <;> norm_num)
      (by exact_mod_cast hc')) hc, fun j => ?_⟩
    have := congrFun hV j
    simp only [Pi.smul_apply, smul_eq_mul] at this
    have hMj : ((M.mulVec ![1, 0] j : ℤ) : ℝ) = (M j 0 : ℝ) := by
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [hMj] at this
    field_simp
    linarith
  obtain ⟨d, hd, hcol⟩ := hcol
  have e0 := hcol 0
  have e1 := hcol 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e0 e1
  push_cast at e0 e1
  have hun : (u C.a C.b n : ℝ) ≠ 0 := by exact_mod_cast (u_pos C.hab hn).ne'
  have hM10 : (M 1 0 : ℝ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at e1
    exact pow_ne_zero _ hun e1
  rw [ratioPower]
  apply Rat.cast_injective (α := ℝ)
  push_cast
  rw [div_pow, e0, e1]
  field_simp

/-! ## Exponents -/

theorem mod_add_mul_L {i d : ℕ} (hd : d ∣ C.L i) (r j : ℕ) : (r + j * C.L i) % d = r % d := by
  obtain ⟨c, hc⟩ := hd
  rw [hc, show j * (d * c) = d * (j * c) by ring, Nat.add_mul_mod_self_left]

theorem e'_affine {i : ℕ} (hi : i < C.k) (r j : ℕ) :
    C.e' (r + j * C.L i) i = C.e' r i + j * (C.e i (r + C.L i) - C.e i r) := by
  have h1 := C.mod_add_mul_L (i := i) (Nat.dvd_lcm_left (C.m i) (C.m (i + 1))) r j
  have h2 := C.mod_add_mul_L (i := i) (Nat.dvd_lcm_right (C.m i) (C.m (i + 1))) r j
  rw [e', e', C.yn_congr h1, C.yn_congr h2, C.e_affine hi r j]
  ring

/-- A threshold after which all effective exponents are nonnegative. -/
def Nbig : ℕ :=
  1 + ∑ i ∈ Finset.range C.k, ∑ r ∈ Finset.range (C.L i), (r + (-(C.e' r i)).toNat * C.L i)

theorem e'_nonneg {n : ℕ} (hn : C.Nbig ≤ n) {i : ℕ} (hi : i < C.k) : 0 ≤ C.e' n i := by
  set L := C.L i
  have hL := C.L_pos i
  set r := n % L
  set j := n / L
  have hn' : n = r + j * L := by rw [Nat.mul_comm]; exact (Nat.mod_add_div n L).symm
  have hr : r < L := Nat.mod_lt _ hL
  set T := (-(C.e' r i)).toNat
  have hterm : r + T * L ≤ ∑ i ∈ Finset.range C.k, ∑ r ∈ Finset.range (C.L i),
      (r + (-(C.e' r i)).toNat * C.L i) := by
    have h1 : r + T * L ≤ ∑ r ∈ Finset.range (C.L i), (r + (-(C.e' r i)).toNat * C.L i) :=
      Finset.single_le_sum (f := fun r => r + (-(C.e' r i)).toNat * C.L i)
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hr)
    exact h1.trans (Finset.single_le_sum (f := fun i => ∑ r ∈ Finset.range (C.L i),
      (r + (-(C.e' r i)).toNat * C.L i)) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hi))
  have hjT : T ≤ j := by
    by_contra h
    have : j * L ≤ T * L := Nat.mul_le_mul_right _ (by omega)
    have : C.Nbig ≤ r + j * L := hn'.symm ▸ hn
    unfold Nbig at this
    omega
  rw [hn', C.e'_affine hi r j]
  have hδ := C.e_shift_pos hi r
  have hT : -(C.e' r i) ≤ T := Int.self_le_toNat _
  have hjT' : (T : ℤ) ≤ j := by exact_mod_cast hjT
  nlinarith

theorem data_affine {i : ℕ} (hi : i < C.k) :
    GrowsAffinelyOnResidues (C.data.e i) (C.data.exponentModulus i) C.Nbig := by
  intro r hr
  have hLdef : C.data.exponentModulus i = C.L i := rfl
  rw [hLdef] at hr ⊢
  have hL : (0 : ℚ) < C.L i := by exact_mod_cast C.L_pos i
  have hδ : (0 : ℚ) < ((C.e i (r + C.L i) - C.e i r : ℤ) : ℚ) := by
    exact_mod_cast C.e_shift_pos hi r
  refine ⟨((C.e i (r + C.L i) - C.e i r : ℤ) : ℚ) / C.L i,
    (C.e' r i : ℚ) - ((C.e i (r + C.L i) - C.e i r : ℤ) : ℚ) / C.L i * r, div_pos hδ hL, ?_⟩
  intro n hn hnr
  have hn' : n = r + n / C.L i * C.L i := by
    rw [← hnr, Nat.mul_comm]; exact (Nat.mod_add_div n (C.L i)).symm
  have hnn := C.e'_nonneg hn hi
  obtain ⟨j, rfl⟩ : ∃ j, n = r + j * C.L i := ⟨n / C.L i, hn'⟩
  change ((C.e' (r + j * C.L i) i).toNat : ℚ) = _
  rw [show ((C.e' (r + j * C.L i) i).toNat : ℚ) = ((C.e' (r + j * C.L i) i : ℤ) : ℚ) by
    exact_mod_cast Int.toNat_of_nonneg hnn, C.e'_affine hi r j]
  push_cast
  field_simp
  ring

/-- The patch-junction decomposition in the fixed setting, with the extra
information that the final junction at residue `0` is empty. -/
theorem exists_data : ∃ D : PatchJunctionData,
    D.m = C.m ∧ D.J C.k 0 = [] ∧
    (∀ i : ℕ, C.Invisible i → (∀ r : ℕ, D.J i r = []) ∧
      ∀ n : ℕ, D.P (i - 1) (n % D.g (i - 1)) = D.P i (n % D.g i)) ∧
    (∀ i : ℕ, 0 < i → i < C.k → ∀ r : ℕ, D.J i r = [] → C.Invisible i) ∧
    (∀ i : ℕ, i < C.k → ∀ r : ℕ, r < D.g i → D.P i r ≠ [] ∧ PositiveWord (D.P i r)) ∧
    (∀ i : ℕ, i ≤ C.k → ∀ r : ℕ, r < D.m i → PositiveWord (D.J i r)) ∧
    ∃ N : ℕ, 1 ≤ N ∧
      (∀ i : ℕ, i < C.k → GrowsAffinelyOnResidues (D.e i) (D.exponentModulus i) N) ∧
      (∀ n : ℕ, N ≤ n → IsContinuedFraction (ratioPower C.a C.b C.k n) (D.wordFinal C.k n)) := by
  refine ⟨C.data, rfl, by rw [data_J_k]; exact ((C.Jfin_spec 0).2.1 rfl).2,
    fun i hv => ⟨fun r => by simp [data, hv.2.1, C.Jword_invisible hv], fun n => ?_⟩,
    fun i _ hik r hJ => by
      by_contra hv
      exact C.Jword_ne_nil hik hv r (by simpa [data, hik] using hJ),
    fun i hi r _ => ⟨(C.Pword_spec hi r).2.1, (C.Pword_spec hi r).1⟩, ?_, C.Nbig,
    by unfold Nbig; omega, fun i hi => C.data_affine hi, ?_⟩
  · have hj : i - 1 < C.k := by have := hv.2.1; omega
    change C.Pword (i - 1) (n % C.g (i - 1)) = C.Pword i (n % C.g i)
    unfold Pword
    rw [C.P_mod, C.P_mod, C.P_eq_of_sig_eq hj hv.2.1 n n (C.sig_eq_of_invisible hv n).1.symm]
  · intro i hi r _
    rcases lt_or_eq_of_le hi with hi | rfl
    · simpa [data, hi] using (C.Jword_spec hi r).2.1
    · rw [data_J_k]
      exact (C.Jfin_spec r).1
  · intro n hn
    exact C.ratio_eq n (le_trans (by unfold Nbig; omega) hn) (fun i hi => C.e'_nonneg hn hi)

/-- The decomposition in the fixed setting, with the facts about the final and
the invisible junctions. -/
theorem exists_dataMod : ∃ D : PatchJunctionData, D.IsDecompositionMod C.a C.b C.k C.m ∧
    D.J C.k 0 = [] ∧
    (∀ i : ℕ, C.Invisible i → (∀ r : ℕ, D.J i r = []) ∧
      ∀ n : ℕ, D.P (i - 1) (n % D.g (i - 1)) = D.P i (n % D.g i)) ∧
    (∀ i : ℕ, 0 < i → i < C.k → ∀ r : ℕ, D.J i r = [] → C.Invisible i) := by
  obtain ⟨D, hDm, hJ0, hinv, hvis, hP, hJ, N, hN, he, hw⟩ := C.exists_data
  have hm : ∀ i, i ≤ C.k → 0 < D.m i := fun i _ => hDm ▸ C.m_pos i
  obtain ⟨B, hB⟩ := D.exists_uniform_bound_final C.k hm
  exact ⟨D, ⟨fun i hi => ⟨hDm ▸ rfl, hm i hi⟩, hP, hJ, N, hN, he, hw, B,
    fun n _ d hd => hB n d hd⟩, hJ0, hinv, hvis⟩

/-- Exercise `exer:main_gen`(b) in the fixed setting, with moduli `C.m`. -/
theorem hasPatchJunctionDecompositionMod : HasPatchJunctionDecompositionMod C.a C.b C.k C.m := by
  obtain ⟨D, hD, -⟩ := C.exists_dataMod
  exact ⟨D, hD⟩

/-- With the ranks of apparition as moduli, `m_k = 1` and the final junction is
empty, so the decomposition is that of Theorem 1.2(b). -/
theorem isDecomposition_of_ranks
    (hm : ∀ i, i ≤ C.k → IsRankOfApparition C.a C.b (delta C.a C.b C.k i) (C.m i))
    {D : PatchJunctionData} (hD : D.IsDecompositionMod C.a C.b C.k C.m) (hJ0 : D.J C.k 0 = []) :
    D.IsDecomposition C.a C.b C.k := by
  obtain ⟨hDm, hP, hJ, N, hN, he, hw, B, hB⟩ := hD
  have hmk : D.m C.k = 1 := by
    rw [(hDm C.k le_rfl).1]
    have := hm C.k le_rfl
    rw [delta_self] at this
    exact this.unique (rankOfApparition_one _ _)
  have hword (n : ℕ) : D.wordFinal C.k n = D.word C.k n := by
    rw [PatchJunctionData.wordFinal, hmk, Nat.mod_one, hJ0, List.append_nil]
  refine ⟨fun i hi => (hDm i hi).1 ▸ hm i hi, hP, fun i hi r hr => hJ i hi.le r hr, N, hN, he,
    fun n hn => hword n ▸ hw n hn, B, fun n hn d hd => hB n hn d (by rw [hword]; exact hd)⟩

end Ctx

/-- The construction applies to Theorem 1.2, with the ranks of apparition of
`Δ_{k,i}` as moduli. -/
theorem exists_ctx_of_admissible {a b : ℤ} (hab : Admissible a b) {k : ℕ}
    (hk : 1 ≤ k) (hdelta : ∀ i : ℕ, i ≤ k → delta a b k i ≠ 0) :
    ∃ C : Ctx, C.a = a ∧ C.b = b ∧ C.k = k ∧
      ∀ i, i ≤ k → IsRankOfApparition a b (delta a b k i) (C.m i) := by
  have hdQ : ∀ i, i ≤ k → deltaOver (a : ℚ) (b : ℚ) k i ≠ 0 := by
    intro i hi
    have hm := deltaOver_map (Int.castRingHom ℚ) a b k i
    dsimp at hm
    rw [← hm]
    exact_mod_cast (show deltaOver a b k i ≠ 0 by rw [← delta_eq_deltaOver]; exact hdelta i hi)
  obtain ⟨S⟩ := exists_padeBasisChain (a : ℚ) (b : ℚ) hk hdQ
  -- The ranks of apparition `m_i` of `Δ_{k,i}`.
  have hex (i : ℕ) : ∃ m, i ≤ k → IsRankOfApparition a b (delta a b k i) m := by
    by_cases hi : i ≤ k
    · obtain ⟨m, hm⟩ := exists_rankOfApparition hab _ (hdelta i hi)
      exact ⟨m, fun _ => hm⟩
    · exact ⟨1, fun h => absurd h hi⟩
  choose m hm using hex
  have hrank1 {i : ℕ} (hi : i ≤ k) (h1 : delta a b k i = 1) : m i = 1 := by
    have := hm i hi
    rw [h1] at this
    exact this.unique (rankOfApparition_one a b)
  let m' : ℕ → ℕ := fun i => if i ≤ k then m i else 1
  have hm' {i : ℕ} (hi : i ≤ k) : m' i = m i := by simp [m', hi]
  let C : Ctx :=
    { a := a, b := b, k := k, hab := hab.gen, hk := hk, hd := hdelta, S := S, m := m'
      m_pos := fun i => by
        by_cases hi : i ≤ k
        · rw [hm' hi]; exact (hm i hi).1
        · simp [m', hi]
      m_zero := by rw [hm' (Nat.zero_le _)]; exact hrank1 (Nat.zero_le _) (delta_zero a b k)
      transport := fun i hi n t => by
        obtain ⟨G, hGu, hG⟩ := exists_G_integral hab.1 hk hi (hdelta i hi) (S.basis i hi)
          (m := m' i * t) (by rw [hm' hi]; exact (hm i hi).2.1.trans (u_dvd_u_mul _ _ _ _)) n
        refine ⟨G, hGu, 1, one_ne_zero, ?_⟩
        have hdet : IsUnit (evalU (S.basis i hi) n).det := by
          rw [evalU_det]
          have hb : (b : ℚ) ≠ 0 := by rcases hab.1 with h | h <;> simp [h]
          exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ (neg_ne_zero.mpr hb))
        rw [hG, one_smul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one] }
  exact ⟨C, rfl, rfl, rfl, fun i hi => by
    change IsRankOfApparition a b (delta a b k i) (m' i)
    rw [hm' hi]
    exact hm i hi⟩

/-- **Theorem 1.2(b).** -/
theorem hasPatchJunctionDecomposition_of_delta_ne_zero {a b : ℤ} (hab : Admissible a b) {k : ℕ}
    (hk : 1 ≤ k) (hdelta : ∀ i : ℕ, i ≤ k → delta a b k i ≠ 0) :
    HasPatchJunctionDecomposition a b k := by
  obtain ⟨C, rfl, rfl, rfl, hm⟩ := exists_ctx_of_admissible hab hk hdelta
  obtain ⟨D, hD, hJ0, -⟩ := C.exists_dataMod
  exact ⟨D, C.isDecomposition_of_ranks hm hD hJ0⟩

end TwoPoint
