module

public import TwoPoint.Pade
public import Mathlib.Algebra.Polynomial.Div

/-!
# Normalized two-point Padé bases

The construction follows Lemma `lem:Phi` in
`ODorney_TwoPoint_Fibonacci(4).tex`. The arguments work over any field, so that
the rational basis can later be used over the real quadratic extension.
-/

@[expose] public section

noncomputable section

namespace TwoPoint

open Polynomial
open scoped BigOperators

variable {K : Type*} [Field K]

theorem characteristicPolynomial_coeff_two {R : Type*} [CommRing R] [IsDomain R] (a b : R) :
    (characteristicPolynomial a b).coeff 2 = 1 := by
  simp [characteristicPolynomial]

theorem characteristicPolynomial_monic {R : Type*} [CommRing R] [IsDomain R] (a b : R) :
    (characteristicPolynomial a b).Monic :=
  monic_of_degree_le 2
    (natDegree_le_iff_degree_le.mp (characteristicPolynomial_natDegree_le a b))
    (characteristicPolynomial_coeff_two a b)

theorem characteristicPolynomial_natDegree {R : Type*} [CommRing R] [IsDomain R] (a b : R) :
    (characteristicPolynomial a b).natDegree = 2 :=
  natDegree_eq_of_le_of_coeff_ne_zero (characteristicPolynomial_natDegree_le a b)
    (by rw [characteristicPolynomial_coeff_two]; exact one_ne_zero)

theorem hPower_natDegree {R : Type*} [CommRing R] [IsDomain R] (a b : R) (i : ℕ) :
    (characteristicPolynomial a b ^ i).natDegree = 2 * i := by
  rw [natDegree_pow, characteristicPolynomial_natDegree, Nat.mul_comm]

theorem hPower_coeff_top {R : Type*} [CommRing R] [IsDomain R] (a b : R) (i : ℕ) :
    (characteristicPolynomial a b ^ i).coeff (2 * i) = 1 := by
  rw [← hPower_natDegree a b i, coeff_natDegree]
  exact ((characteristicPolynomial_monic a b).pow i).leadingCoeff

/-- Split a polynomial around a zero coefficient block. -/
theorem split_polynomial_at_gap {R : Type*} [CommRing R] (G : Polynomial R) {k i : ℕ} (hi : i ≤ k)
    (hdeg : G.natDegree ≤ k + i)
    (hgap : ∀ r : Fin (k - i), G.coeff (i + r.val) = 0) :
    ∃ L Q : Polynomial R, L.degree < i ∧ Q.degree ≤ i ∧
      Q.coeff i = G.coeff (k + i) ∧ X ^ k * Q + L = G := by
  classical
  let L := ofFn i (toFn i G)
  let Q := ofFn (i + 1) (fun s : Fin (i + 1) => G.coeff (k + s.val))
  refine ⟨L, Q, ofFn_degree_lt _, ?_, ?_, ?_⟩
  · apply natDegree_le_iff_degree_le.mp
    dsimp only [Q]
    have := ofFn_natDegree_lt (by omega : 1 ≤ i + 1)
      (fun s : Fin (i + 1) => G.coeff (k + s.val))
    omega
  · simp [Q]
  · ext n
    rw [coeff_add, coeff_X_pow_mul']
    by_cases hn : n < k
    · rw [ite_eq_right (by omega), zero_add]
      by_cases hni : n < i
      · simp [L, ofFn_coeff_eq_val_of_lt _ hni, toFn]
      · rw [ofFn_coeff_eq_zero_of_ge _ (by omega : i ≤ n)]
        symm
        have := hgap ⟨n - i, by omega⟩
        simpa only [show i + (n - i) = n by omega] using this
    · rw [ite_eq_left (by omega),
        ofFn_coeff_eq_zero_of_ge _ (by omega : i ≤ n), add_zero]
      by_cases hni : n - k < i + 1
      · simp only [Q, ofFn_coeff_eq_val_of_lt _ hni,
          show k + (n - k) = n by omega]
      · rw [ofFn_coeff_eq_zero_of_ge _ (by omega : i + 1 ≤ n - k)]
        exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

/-- A numerator and denominator of degree at most `i` satisfying the
two-point Padé congruence of order `i`. -/
structure IsPadePair (a b : K) (k i : ℕ) (P Q : Polynomial K) : Prop where
  degree_num : P.degree ≤ i
  degree_den : Q.degree ≤ i
  relation : characteristicPolynomial a b ^ i ∣ X ^ k * Q - P

/-- Nonsingularity rules out a Padé pair whose two degrees are below `i`. -/
theorem pade_low_eq_zero (a b : K) {k i : ℕ} (hi : i ≤ k)
    (hdelta : deltaOver a b k i ≠ 0) (P Q : Polynomial K)
    (hP : P.degree < i) (hQ : Q.degree < i)
    (hdiv : characteristicPolynomial a b ^ i ∣ X ^ k * Q - P) :
    P = 0 ∧ Q = 0 := by
  classical
  obtain ⟨E, he⟩ := hdiv
  have he' : X ^ k * Q - P = E * characteristicPolynomial a b ^ i := by
    simpa only [mul_comm] using he
  have hPcoeff := (degree_lt_iff_coeff_zero P i).mp hP
  have hQcoeff := (degree_lt_iff_coeff_zero Q i).mp hQ
  have hEzero : E = 0 := by
    by_contra hE
    have hprod : E * characteristicPolynomial a b ^ i ≠ 0 :=
      mul_ne_zero hE (pow_ne_zero _ (characteristicPolynomial_monic a b).ne_zero)
    have hdeg : (E * characteristicPolynomial a b ^ i).degree < (k + i : ℕ) := by
      rw [← he', degree_lt_iff_coeff_zero]
      intro n hn
      rw [coeff_sub, coeff_X_pow_mul', ite_eq_left (by omega),
        hQcoeff _ (by omega), hPcoeff _ (by omega), sub_self]
    have hnat := (natDegree_lt_iff_degree_lt hprod).mpr hdeg
    rw [natDegree_mul hE (pow_ne_zero _ (characteristicPolynomial_monic a b).ne_zero),
      hPower_natDegree] at hnat
    have hEnat : E.natDegree < k - i := by omega
    let e := toFn (k - i) E
    have hrec : ofFn (k - i) e = E := ofFn_comp_toFn_eq_id_of_natDegree_lt hEnat
    have he0 : e ≠ 0 := by
      intro hz
      apply hE
      rw [← hrec, hz, map_zero]
    have hker : (padeToeplitz a b k i).mulVec e = 0 := by
      ext r
      rw [padeToeplitz_mulVec_eq_coeff, hrec, ← he', coeff_sub,
        coeff_X_pow_mul', ite_eq_right (by omega), hPcoeff _ (by omega), sub_self]
      rfl
    exact hdelta (Matrix.exists_mulVec_eq_zero_iff.mp ⟨e, he0, hker⟩)
  have hPQ : X ^ k * Q = P := sub_eq_zero.mp (by rw [he', hEzero, zero_mul])
  have hQzero : Q = 0 := by
    ext n
    have hp := hPcoeff (n + k) (by omega)
    have := congrArg (fun F : Polynomial K => F.coeff (n + k)) hPQ
    simpa only [coeff_X_pow_mul, hp, coeff_zero] using this
  exact ⟨by simpa [hQzero] using hPQ.symm, hQzero⟩

private theorem degree_sub_lt_of_coeff_eq (P Q : Polynomial K) (i : ℕ)
    (hP : P.degree ≤ i) (hQ : Q.degree ≤ i) (hc : P.coeff i = Q.coeff i) :
    (P - Q).degree < i := by
  rw [degree_lt_iff_coeff_zero]
  intro n hn
  rw [coeff_sub]
  rcases eq_or_lt_of_le hn with rfl | hlt
  · exact sub_eq_zero.mpr hc
  · have hPn : P.coeff n = 0 := coeff_eq_zero_of_degree_lt (hP.trans_lt (by exact_mod_cast hlt))
    have hQn : Q.coeff n = 0 := coeff_eq_zero_of_degree_lt (hQ.trans_lt (by exact_mod_cast hlt))
    rw [hPn, hQn, sub_self]

/-- Leading coefficients determine a Padé pair uniquely. -/
theorem IsPadePair.eq_of_coeff_eq {a b : K} {k i : ℕ} (hi : i ≤ k)
    (hdelta : deltaOver a b k i ≠ 0) {P Q P' Q' : Polynomial K}
    (h : IsPadePair a b k i P Q) (h' : IsPadePair a b k i P' Q')
    (hp : P.coeff i = P'.coeff i) (hq : Q.coeff i = Q'.coeff i) : P = P' ∧ Q = Q' := by
  have hdiv : characteristicPolynomial a b ^ i ∣ X ^ k * (Q - Q') - (P - P') := by
    convert dvd_sub h.relation h'.relation using 1; ring
  obtain ⟨hP, hQ⟩ := pade_low_eq_zero a b hi hdelta (P - P') (Q - Q')
    (degree_sub_lt_of_coeff_eq _ _ _ h.degree_num h'.degree_num hp)
    (degree_sub_lt_of_coeff_eq _ _ _ h.degree_den h'.degree_den hq) hdiv
  exact ⟨sub_eq_zero.mp hP, sub_eq_zero.mp hQ⟩

/-- Solve the inhomogeneous Toeplitz system with prescribed leading
coefficients. This is the existence assertion of Lemma `lem:Phi`. -/
theorem exists_padePair_of_coeff (a b : K) {k i : ℕ} (hk : 0 < k) (hi : i ≤ k)
    (hdelta : deltaOver a b k i ≠ 0) (p q : K) :
    ∃ P Q : Polynomial K, IsPadePair a b k i P Q ∧ P.coeff i = p ∧ Q.coeff i = q := by
  classical
  let H := characteristicPolynomial a b ^ i
  let B := C q * X ^ (k - i) * H + C p * X ^ i
  have hunit : IsUnit (padeToeplitz a b k i) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdelta)
  obtain ⟨e, he⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hunit
    (fun r : Fin (k - i) => -B.coeff (i + r.val))
  let E₀ := ofFn (k - i) e
  let E := E₀ + C q * X ^ (k - i)
  let G := E * H + C p * X ^ i
  have hE₀ : E₀.natDegree ≤ k - i :=
    natDegree_le_iff_degree_le.mpr (ofFn_degree_lt e).le
  have hqdeg : (C q * X ^ (k - i)).natDegree ≤ k - i :=
    (natDegree_C_mul_le _ _).trans (natDegree_X_pow_le _)
  have hE : E.natDegree ≤ k - i :=
    (natDegree_add_le _ _).trans (max_le hE₀ hqdeg)
  have hpdeg : (C p * (X : Polynomial K) ^ i).natDegree ≤ i :=
    (natDegree_C_mul_le _ _).trans (natDegree_X_pow_le _)
  have hH : H.natDegree ≤ 2 * i := hPower_natDegree_le a b i
  have hG : G.natDegree ≤ k + i := by
    have hmul := natDegree_mul_le (p := E) (q := H)
    have hadd := natDegree_add_le (E * H) (C p * X ^ i)
    change (E * H + C p * X ^ i).natDegree ≤ k + i
    omega
  have hEcoeff : E.coeff (k - i) = q := by
    simp [E, E₀, coeff_add, ofFn_coeff_eq_zero_of_ge e le_rfl]
  have hGcoeff : G.coeff (k + i) = q := by
    have hidx : k + i = (k - i) + 2 * i := by omega
    change (E * H + C p * X ^ i).coeff (k + i) = q
    rw [coeff_add]
    have hpzero : (C p * (X : Polynomial K) ^ i).coeff (k + i) = 0 :=
      coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hpzero, add_zero, hidx, coeff_mul_add_eq_of_natDegree_le hE hH, hEcoeff]
    simp only [H, hPower_coeff_top, mul_one]
  have hgap : ∀ r : Fin (k - i), G.coeff (i + r.val) = 0 := by
    intro r
    have hGeq : G = E₀ * H + B := by dsimp [G, E, B]; ring
    rw [hGeq, coeff_add]
    change (ofFn (k - i) e * characteristicPolynomial a b ^ i).coeff (i + r.val) +
      B.coeff (i + r.val) = 0
    rw [← padeToeplitz_mulVec_eq_coeff, congrFun he r, neg_add_cancel]
  obtain ⟨L, Q, hL, hQ, hQc, hsplit⟩ := split_polynomial_at_gap G hi hG hgap
  refine ⟨C p * X ^ i - L, Q, ⟨?_, hQ, ?_⟩, ?_, hQc.trans hGcoeff⟩
  · exact (degree_sub_le _ _).trans
      (max_le (natDegree_le_iff_degree_le.mp hpdeg) hL.le)
  · refine ⟨E, ?_⟩
    dsimp only [G] at hsplit
    linear_combination hsplit
  · rw [coeff_sub, coeff_C_mul, coeff_X_pow_self, mul_one,
      coeff_eq_zero_of_degree_lt hL, sub_zero]

/-- Existence and uniqueness of a normalized Padé pair for any prescribed
leading-coefficient vector. -/
theorem existsUnique_padePair_of_coeff (a b : K) {k i : ℕ} (hk : 0 < k) (hi : i ≤ k)
    (hdelta : deltaOver a b k i ≠ 0) (p q : K) :
    ∃! v : Polynomial K × Polynomial K,
      IsPadePair a b k i v.1 v.2 ∧ v.1.coeff i = p ∧ v.2.coeff i = q := by
  obtain ⟨P, Q, h, hp, hq⟩ := exists_padePair_of_coeff a b hk hi hdelta p q
  refine ⟨(P, Q), ⟨h, hp, hq⟩, ?_⟩
  rintro ⟨P', Q'⟩ ⟨h', hp', hq'⟩
  obtain ⟨hP, hQ⟩ := h'.eq_of_coeff_eq hi hdelta h (hp'.trans hp.symm) (hq'.trans hq.symm)
  exact Prod.ext hP hQ

theorem IsPadePair.add {a b : K} {k i : ℕ} {P Q P' Q' : Polynomial K}
    (h : IsPadePair a b k i P Q) (h' : IsPadePair a b k i P' Q') :
    IsPadePair a b k i (P + P') (Q + Q') where
  degree_num := (degree_add_le _ _).trans (max_le h.degree_num h'.degree_num)
  degree_den := (degree_add_le _ _).trans (max_le h.degree_den h'.degree_den)
  relation := by convert dvd_add h.relation h'.relation using 1; ring

theorem IsPadePair.const_mul {a b : K} {k i : ℕ} {P Q : Polynomial K}
    (h : IsPadePair a b k i P Q) (c : K) :
    IsPadePair a b k i (C c * P) (C c * Q) where
  degree_num := natDegree_le_iff_degree_le.mp
    ((natDegree_C_mul_le _ _).trans (natDegree_le_iff_degree_le.mpr h.degree_num))
  degree_den := natDegree_le_iff_degree_le.mp
    ((natDegree_C_mul_le _ _).trans (natDegree_le_iff_degree_le.mpr h.degree_den))
  relation := by convert dvd_mul_of_dvd_right h.relation (C c) using 1; ring

/-- The dehomogenized normalized matrix in Lemma `lem:Phi`. -/
structure NormalizedPadeBasis (a b : K) (k i : ℕ) where
  matrix : Matrix (Fin 2) (Fin 2) (Polynomial K)
  isPade : ∀ c, IsPadePair a b k i (matrix 0 c) (matrix 1 c)
  coeff_matrix : ∀ r c, (matrix r c).coeff i = (1 : Matrix (Fin 2) (Fin 2) K) r c

theorem exists_normalizedPadeBasis (a b : K) {k i : ℕ} (hk : 0 < k) (hi : i ≤ k)
    (hdelta : deltaOver a b k i ≠ 0) : Nonempty (NormalizedPadeBasis a b k i) := by
  obtain ⟨P₀, Q₀, h₀, hp₀, hq₀⟩ := exists_padePair_of_coeff a b hk hi hdelta 1 0
  obtain ⟨P₁, Q₁, h₁, hp₁, hq₁⟩ := exists_padePair_of_coeff a b hk hi hdelta 0 1
  refine ⟨⟨!![P₀, P₁; Q₀, Q₁], ?_, ?_⟩⟩
  · intro c
    fin_cases c
    · exact h₀
    · exact h₁
  · intro r c
    fin_cases r <;> fin_cases c <;> simp [hp₀, hq₀, hp₁, hq₁]

theorem NormalizedPadeBasis.degree_entry {a b : K} {k i : ℕ}
    (B : NormalizedPadeBasis a b k i) (r c : Fin 2) : (B.matrix r c).degree ≤ i := by
  fin_cases r
  · exact (B.isPade c).degree_num
  · exact (B.isPade c).degree_den

theorem NormalizedPadeBasis.unique {a b : K} {k i : ℕ} (hi : i ≤ k)
    (hdelta : deltaOver a b k i ≠ 0) (B B' : NormalizedPadeBasis a b k i) :
    B.matrix = B'.matrix := by
  apply Matrix.ext
  intro r c
  have hh := (B.isPade c).eq_of_coeff_eq hi hdelta (B'.isPade c)
    ((B.coeff_matrix 0 c).trans (B'.coeff_matrix 0 c).symm)
    ((B.coeff_matrix 1 c).trans (B'.coeff_matrix 1 c).symm)
  fin_cases r
  · exact hh.1
  · exact hh.2

/-- Every Padé pair is the linear combination of the normalized columns with
its own leading coefficients as coordinates. -/
theorem NormalizedPadeBasis.span {a b : K} {k i : ℕ} (hi : i ≤ k)
    (hdelta : deltaOver a b k i ≠ 0) (B : NormalizedPadeBasis a b k i)
    {P Q : Polynomial K} (h : IsPadePair a b k i P Q) :
    P = C (P.coeff i) * B.matrix 0 0 + C (Q.coeff i) * B.matrix 0 1 ∧
    Q = C (P.coeff i) * B.matrix 1 0 + C (Q.coeff i) * B.matrix 1 1 := by
  apply h.eq_of_coeff_eq hi hdelta
    (((B.isPade 0).const_mul (P.coeff i)).add ((B.isPade 1).const_mul (Q.coeff i)))
  · simp [coeff_add, coeff_C_mul, B.coeff_matrix]
  · simp [coeff_add, coeff_C_mul, B.coeff_matrix]

/-- The determinant divisibility follows directly from the two Padé relations. -/
theorem NormalizedPadeBasis.hPower_dvd_det {a b : K} {k i : ℕ}
    (B : NormalizedPadeBasis a b k i) : characteristicPolynomial a b ^ i ∣ B.matrix.det := by
  rw [Matrix.det_fin_two]
  convert dvd_sub (dvd_mul_of_dvd_right (B.isPade 1).relation (B.matrix 1 0))
    (dvd_mul_of_dvd_right (B.isPade 0).relation (B.matrix 1 1)) using 1
  ring

/-- The determinant identity in Lemma `lem:Phi`. -/
theorem NormalizedPadeBasis.det {a b : K} {k i : ℕ}
    (B : NormalizedPadeBasis a b k i) : B.matrix.det = characteristicPolynomial a b ^ i := by
  have hdeg (r c : Fin 2) : (B.matrix r c).natDegree ≤ i :=
    natDegree_le_iff_degree_le.mpr (B.degree_entry r c)
  have hd : B.matrix.det.natDegree ≤ 2 * i := by
    rw [Matrix.det_fin_two]
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · have := natDegree_mul_le (p := B.matrix 0 0) (q := B.matrix 1 1)
      have := hdeg 0 0
      have := hdeg 1 1
      omega
    · have := natDegree_mul_le (p := B.matrix 0 1) (q := B.matrix 1 0)
      have := hdeg 0 1
      have := hdeg 1 0
      omega
  have hc : B.matrix.det.coeff (2 * i) = 1 := by
    rw [Matrix.det_fin_two, coeff_sub, show 2 * i = i + i by omega,
      coeff_mul_add_eq_of_natDegree_le (hdeg 0 0) (hdeg 1 1),
      coeff_mul_add_eq_of_natDegree_le (hdeg 0 1) (hdeg 1 0)]
    simp [B.coeff_matrix]
  apply eq_of_monic_of_dvd_of_natDegree_le
    ((characteristicPolynomial_monic a b).pow i)
    (monic_of_natDegree_le_of_coeff_eq_one (2 * i) hd hc) B.hPower_dvd_det
  rwa [hPower_natDegree]

end TwoPoint
