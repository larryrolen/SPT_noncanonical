/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.HeckeProductPairings
public import SptClassification.QSeries.PrincipalFormsPairing
public import SptClassification.QSeries.ConditionalCoefficient
public import SptClassification.QSeries.HeckeMinusHalfIntegral
public import SptClassification.QSeries.HeckeShadowWords
public import SptClassification.QSeries.InverseEtaPoleSupport
public import SptClassification.ModularForms.WeightTwoConstantTermHeckeTranslation

/-!
# Analytic constant terms of the Hecke products

The rational Fourier rows of the two Hecke products have separate pole shifts.
The coefficient at the sum of those shifts is the finite pairing used in
[rolenManuscript, §3, equations (ct1) and (ct2)].
-/

public section

namespace SptClassification.QSeries

/-- Fourier indices appearing in the Cauchy coefficient after clearing poles
of orders `M` and `N`. The second factor has initial index `-m²`. -/
def shiftedPairingIndices (m M N : ℕ) : Finset ℤ :=
  (Finset.antidiagonal (M + N)).image
    (fun ij : ℕ × ℕ => 24 * (ij.2 : ℤ) - (m : ℤ) ^ 2)

/-- Reindex the Cauchy coefficient by the actual Fourier index of the second
factor. This statement allows a finite pairing to contain extra zero terms. -/
theorem shiftedCauchy_coeff_eq_finiteConstantTerm
    (m d M N : ℕ) (hshift : 24 * (M + N) = d + m ^ 2)
    (I : Finset ℤ) (F H : ℤ → ℚ)
    (hOutside : ∀ r : ℤ, r ∈ shiftedPairingIndices m M N → r ∉ I →
      F r * H (-r) = 0)
    (hExtra : ∀ r : ℤ, r ∈ I → r ∉ shiftedPairingIndices m M N →
      F r * H (-r) = 0) :
    ((PowerSeries.mk fun j : ℕ => H (24 * (j : ℤ) - d)) *
      (PowerSeries.mk fun j : ℕ => F (24 * (j : ℤ) - (m : ℤ) ^ 2))).coeff
        (M + N) = finiteConstantTerm I F H := by
  classical
  let J := shiftedPairingIndices m M N
  have hinj : Set.InjOn
      (fun ij : ℕ × ℕ => 24 * (ij.2 : ℤ) - (m : ℤ) ^ 2)
      (Finset.antidiagonal (M + N) : Set (ℕ × ℕ)) := by
    intro x hx y hy hxy
    have hxsum : x.1 + x.2 = M + N := Finset.mem_antidiagonal.mp hx
    have hysum : y.1 + y.2 = M + N := Finset.mem_antidiagonal.mp hy
    have hxy' : 24 * (x.2 : ℤ) = 24 * (y.2 : ℤ) := by
      linear_combination hxy
    have hsecInt : (x.2 : ℤ) = (y.2 : ℤ) := by omega
    have hsecond : x.2 = y.2 := by exact_mod_cast hsecInt
    have hfirst : x.1 = y.1 := by omega
    exact Prod.ext hfirst hsecond
  have hCauchy :
      ((PowerSeries.mk fun j : ℕ => H (24 * (j : ℤ) - d)) *
        (PowerSeries.mk fun j : ℕ => F (24 * (j : ℤ) - (m : ℤ) ^ 2))).coeff
          (M + N) = ∑ r ∈ J, F r * H (-r) := by
    rw [PowerSeries.coeff_mul]
    rw [show J = (Finset.antidiagonal (M + N)).image
      (fun ij : ℕ × ℕ => 24 * (ij.2 : ℤ) - (m : ℤ) ^ 2) from rfl,
      Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro ij hij
    have hijsum : ij.1 + ij.2 = M + N := Finset.mem_antidiagonal.mp hij
    simp only [PowerSeries.coeff_mk]
    have hindex : 24 * (ij.1 : ℤ) - d =
        -(24 * (ij.2 : ℤ) - (m : ℤ) ^ 2) := by
      have hs : (24 : ℤ) * ((M : ℤ) + N) = (d : ℤ) + (m : ℤ) ^ 2 := by
        exact_mod_cast hshift
      have hijsumInt : (ij.1 : ℤ) + (ij.2 : ℤ) = (M : ℤ) + N := by
        exact_mod_cast hijsum
      omega
    rw [hindex]
    ring
  rw [hCauchy]
  rw [finiteConstantTerm_apply]
  calc
    ∑ r ∈ J, F r * H (-r) = ∑ r ∈ J ∪ I, F r * H (-r) := by
      apply Finset.sum_subset (Finset.subset_union_left)
      intro r hr hrJ
      have hrI : r ∈ I := (Finset.mem_union.mp hr).resolve_left hrJ
      exact hExtra r hrI hrJ
    _ = ∑ r ∈ I, F r * H (-r) := by
      symm
      apply Finset.sum_subset (Finset.subset_union_right)
      intro r hr hrI
      have hrJ : r ∈ J := (Finset.mem_union.mp hr).resolve_right hrI
      exact hOutside r hrJ hrI

/-- Each possible constant-term index occurs in the Cauchy coefficient after
clearing both poles. The square-index congruence is used for *every* divisor
of the Hecke index, including those arising from repeated prime factors. -/
theorem constantTermIndices_subset_shiftedPairingIndices
    (m d : ℕ) (hm : 0 < m) (hcop : m.Coprime 6)
    (hd : d % 24 = 23) :
    constantTermIndices m d ⊆
      shiftedPairingIndices m (principalIndex d) ((m * m) / 24) := by
  intro r hr
  have hdm : 24 * principalIndex d = d + 1 := principalIndex_mul d hd
  have hsq : (m * m) % 24 = 1 :=
    squareIndex_mod_twentyFour_of_coprime_six m hcop
  have hmdecomp : 24 * ((m * m) / 24) + 1 = m * m := by omega
  rw [constantTermIndices_eq] at hr
  rcases Finset.mem_insert.mp hr with heq | hr
  · subst r
    apply Finset.mem_image.mpr
    refine ⟨(0, principalIndex d + (m * m) / 24), ?_, ?_⟩
    · exact Finset.mem_antidiagonal.mpr (by omega)
    · dsimp
      have hsqInt : (m : ℤ) ^ 2 = (m * m : ℕ) := by push_cast; ring
      rw [hsqInt]
      omega
  · obtain ⟨t, ht, heq⟩ := mem_negativeDivisorSquareIndices.mp hr
    have htdiv : t ∣ m := (Nat.mem_divisors.mp ht).1
    have htpos : 0 < t := Nat.pos_of_dvd_of_pos htdiv hm
    have htCop : t.Coprime 6 := Nat.Coprime.of_dvd_left htdiv hcop
    have htsq : (t * t) % 24 = 1 :=
      squareIndex_mod_twentyFour_of_coprime_six t htCop
    have htdecomp : 24 * ((t * t) / 24) + 1 = t * t := by omega
    have htle : t ≤ m := Nat.le_of_dvd hm htdiv
    have hsqle : t * t ≤ m * m := Nat.mul_le_mul htle htle
    have hTle : (t * t) / 24 ≤ (m * m) / 24 := by omega
    apply Finset.mem_image.mpr
    refine ⟨(principalIndex d + (t * t) / 24,
      (m * m) / 24 - (t * t) / 24), ?_, ?_⟩
    · exact Finset.mem_antidiagonal.mpr (by omega)
    · dsimp
      have hmsqInt : (m : ℤ) ^ 2 = (m * m : ℕ) := by push_cast; ring
      have htsqInt : (t : ℤ) ^ 2 = (t * t : ℕ) := by push_cast; ring
      rw [hmsqInt]
      have hrInt : (r : ℤ) = - (t * t : ℕ) := by
        rw [← htsqInt]
        exact heq
      omega

/-- Analytic Hecke and shadow-cancellation input. The forms have the inverse
eta multiplier and weights `3/2` and `-1/2`, respectively. Their complete
convergent rows are the actual Hecke words, including repeated prime factors.
The normalized minus-half row is reduced locally at primes away from `n` by
`principalK_finiteConstantTerm_mod_of_rat_zero`; no global reduction of
rational coefficients is assumed. [rolenManuscript, §3; rolen2026canonical, Lemma 2.4] -/
structure PartitionHeckeForms where
  form : ∀ n : ℕ, 0 < n → n.Coprime 6 →
    EtaInverseWeaklyHolomorphicForm 0
  hasSum : ∀ (n : ℕ) (hn : 0 < n) (hc : n.Coprime 6)
      (τ : UpperHalfPlane),
    HasSum (fun j : ℕ =>
      ((heckeMinusHalfWord n.primeFactorsList
          (fun r => (partitionFourier r : ℚ))
          (24 * (j : ℤ) - (n : ℤ) ^ 2) : ℂ) *
        Function.Periodic.qParam 1 τ ^ j))
      (Function.Periodic.qParam 1 τ ^ ((n * n) / 24) *
        Function.Periodic.qParam 24 τ * form n hn hc τ)

/-- The earlier combined analytic interface, retained for existing conditional
clients. The partition component is exposed separately by `partitionForms`. -/
structure AnalyticHeckePairingInputs where
  differenceForm : ∀ n : ℕ, 0 < n → n.Coprime 6 →
    EtaInverseWeaklyHolomorphicForm 2
  partitionForm : ∀ n : ℕ, 0 < n → n.Coprime 6 →
    EtaInverseWeaklyHolomorphicForm 0
  difference_hasSum : ∀ (n : ℕ) (hn : 0 < n) (hc : n.Coprime 6)
      (τ : UpperHalfPlane),
    HasSum (fun j : ℕ =>
      (((heckeThreeHalfWord n.primeFactorsList
          (fun r => (fFourier r : ℚ))
          (24 * (j : ℤ) - (n : ℤ) ^ 2) -
        (heckeShadowEigenvalue n : ℚ) *
          (fFourier (24 * (j : ℤ) - (n : ℤ) ^ 2) : ℚ)) : ℂ) *
        Function.Periodic.qParam 1 τ ^ j))
      (Function.Periodic.qParam 1 τ ^ ((n * n) / 24) *
        Function.Periodic.qParam 24 τ * differenceForm n hn hc τ)
  partition_hasSum : ∀ (n : ℕ) (hn : 0 < n) (hc : n.Coprime 6)
      (τ : UpperHalfPlane),
    HasSum (fun j : ℕ =>
      ((heckeMinusHalfWord n.primeFactorsList
          (fun r => (partitionFourier r : ℚ))
          (24 * (j : ℤ) - (n : ℤ) ^ 2) : ℂ) *
        Function.Periodic.qParam 1 τ ^ j))
      (Function.Periodic.qParam 1 τ ^ ((n * n) / 24) *
        Function.Periodic.qParam 24 τ * partitionForm n hn hc τ)

/-- Extract the weight `-1/2` part of the combined analytic interface. -/
def AnalyticHeckePairingInputs.partitionForms
    (inputs : AnalyticHeckePairingInputs) : PartitionHeckeForms where
  form := inputs.partitionForm
  hasSum := inputs.partition_hasSum

/-- At Hecke index one the shadow-cancelled row vanishes and is represented
by the zero weak form. This is the identity word, without an analytic Hecke
input [rolenManuscript, §3]. -/
theorem analyticHecke_one_difference_hasSum (τ : UpperHalfPlane) :
    HasSum (fun j : ℕ =>
      (((heckeThreeHalfWord (1 : ℕ).primeFactorsList
          (fun r => (fFourier r : ℚ))
          (24 * (j : ℤ) - (1 : ℤ) ^ 2) -
        (heckeShadowEigenvalue 1 : ℚ) *
          (fFourier (24 * (j : ℤ) - (1 : ℤ) ^ 2) : ℚ)) : ℂ) *
        Function.Periodic.qParam 1 τ ^ j))
      (Function.Periodic.qParam 1 τ ^ ((1 * 1) / 24) *
        Function.Periodic.qParam 24 τ *
          EtaInverseWeaklyHolomorphicForm.zero 2 τ) := by
  simpa [Nat.primeFactorsList_one, heckeThreeHalfWord_nil,
    heckeShadowEigenvalue_one, EtaInverseWeaklyHolomorphicForm.zero_apply] using
    (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)

/-- At Hecke index one the partition row is the actual convergent Fourier
row of inverse eta [rolenManuscript, §3]. -/
theorem analyticHecke_one_partition_hasSum (τ : UpperHalfPlane) :
    HasSum (fun j : ℕ =>
      ((heckeMinusHalfWord (1 : ℕ).primeFactorsList
          (fun r => (partitionFourier r : ℚ))
          (24 * (j : ℤ) - (1 : ℤ) ^ 2) : ℂ) *
        Function.Periodic.qParam 1 τ ^ j))
      (Function.Periodic.qParam 1 τ ^ ((1 * 1) / 24) *
        Function.Periodic.qParam 24 τ * inverseEtaWeakForm τ) := by
  simpa [Nat.primeFactorsList_one, heckeMinusHalfWord_nil,
    partitionFourier_at, QSeries.partitionSeries_coeff]
    using inverseEtaWeakForm_hasSum τ

/-- A weak form together with its complete Fourier row after a Hecke word.
The pole shift is kept as an index, so a further prime step changes `m` to
`m * p` without assuming a formula for the whole word. -/
structure InverseEtaFourierForm (m : ℕ) (A : ℤ → ℚ) where
  residue_support : ∀ r : ℤ, A r ≠ 0 → r % 24 = 23
  form : EtaInverseWeaklyHolomorphicForm 0
  support : SquarePoleSupported m A
  hasSum : ∀ τ : UpperHalfPlane,
    HasSum (fun j : ℕ =>
      ((A (24 * (j : ℤ) - (m : ℤ) ^ 2) : ℂ) *
        Function.Periodic.qParam 1 τ ^ j))
      (Function.Periodic.qParam 1 τ ^ ((m * m) / 24) *
        Function.Periodic.qParam 24 τ * form τ)

/-- The precise remaining analytic Hecke step: on a realized weight `-1/2`
inverse-eta Fourier row, a single prime operator produces a realized row
with the three coefficient terms of [rolenManuscript, §3, Hecke formula].
The manuscript states that coefficient action but does not construct its
analytic weak form; this field is an explicit prerequisite, not a claimed
consequence of the cited shadow identities. -/
structure PrimeInverseEtaHeckeLaw where
  step : ∀ (m p : ℕ), 0 < m → m.Coprime 6 → p.Prime → 5 ≤ p →
    ∀ (A : ℤ → ℚ), InverseEtaFourierForm m A →
      InverseEtaFourierForm (m * p) (heckeMinusHalf p A)

/-- The untransformed inverse eta function supplies the initial realized
Fourier row. [rolenManuscript, §3, `P = η⁻¹`] -/
noncomputable def inverseEtaFourierForm :
    InverseEtaFourierForm 1 (fun r => (partitionFourier r : ℚ)) where
  residue_support := by
    intro r hr
    have h : partitionFourier r ≠ 0 := by exact_mod_cast hr
    exact (partitionFourier_support r h).2
  form := inverseEtaWeakForm
  support := squarePoleSupported_partitionFourier
  hasSum := by
    intro τ
    simpa only [Nat.primeFactorsList_one, heckeMinusHalfWord_nil,
      Int.natCast_one] using
      analyticHecke_one_partition_hasSum τ

/-- Iterate only the one-prime analytic law. The final index `n` controls
coprimality of every intermediate index, even for repeated prime factors. -/
private def PrimeInverseEtaHeckeLaw.wordForm
    (law : PrimeInverseEtaHeckeLaw) (n : ℕ)
    (hn : 0 < n) (hc : n.Coprime 6)
    (ps : List ℕ) (hps : ∀ p ∈ ps, p.Prime ∧ 5 ≤ p)
    (m : ℕ) (hmn : m * ps.prod = n) (A : ℤ → ℚ)
    (initial : InverseEtaFourierForm m A) :
    InverseEtaFourierForm n (heckeMinusHalfWord ps A) := by
  induction ps generalizing m A with
  | nil =>
    have hmeq : m = n := by simpa using hmn
    subst m
    simpa only [heckeMinusHalfWord_nil] using initial
  | cons p ps ih =>
    have hmdiv : m ∣ n := by
      refine ⟨p * ps.prod, ?_⟩
      simpa only [List.prod_cons] using hmn.symm
    have hm : 0 < m := Nat.pos_of_dvd_of_pos hmdiv hn
    have hmc : m.Coprime 6 := Nat.Coprime.of_dvd_left hmdiv hc
    have hp : p.Prime ∧ 5 ≤ p := hps p (by simp)
    have htail : ∀ q ∈ ps, q.Prime ∧ 5 ≤ q :=
      fun q hq => hps q (by simp [hq])
    have hnext : (m * p) * ps.prod = n := by
      calc
        (m * p) * ps.prod = m * (p * ps.prod) := by ring
        _ = n := by simpa only [List.prod_cons] using hmn
    simpa only [heckeMinusHalfWord_cons] using
      ih htail (m * p) hnext (heckeMinusHalf p A)
        (law.step m p hm hmc hp.1 hp.2 A initial)

/-- A single-prime analytic Hecke law supplies the full partition Hecke forms
for every positive index coprime to six. The finite-word construction includes
repeated prime factors; no all-index analytic family is presumed. -/
noncomputable def PartitionHeckeForms.ofPrimeLaw (law : PrimeInverseEtaHeckeLaw) :
    PartitionHeckeForms where
  form n hn hc :=
    (law.wordForm n hn hc n.primeFactorsList
      (primeFactorsList_prime_five n hn hc) 1
      (by simpa using Nat.prod_primeFactorsList (Nat.ne_of_gt hn))
      (fun r => (partitionFourier r : ℚ)) inverseEtaFourierForm).form
  hasSum n hn hc :=
    (law.wordForm n hn hc n.primeFactorsList
      (primeFactorsList_prime_five n hn hc) 1
      (by simpa using Nat.prod_primeFactorsList (Nat.ne_of_gt hn))
      (fun r => (partitionFourier r : ℚ)) inverseEtaFourierForm).hasSum

/-- At Hecke index one, the `K_d P` finite pairing vanishes directly from the
actual weight-two product. Its complete Fourier row is the integral Cauchy
product with the partition series [rolenManuscript, §3, eq. (ct2)]. -/
theorem principalK_partition_finiteConstantTerm_one_zero
    (d : ℕ) (hd : d % 24 = 23) :
    finiteConstantTerm (constantTermIndices 1 d)
      (fun r => (partitionFourier r : ℚ))
      (fun r => (principalKFourier d r : ℚ)) = 0 := by
  let K : ℤ → ℚ := fun r => (principalKFourier d r : ℚ)
  let P : ℤ → ℚ := fun r => (partitionFourier r : ℚ)
  have hshift : 24 * (principalIndex d + 0) = d + (1 : ℕ) ^ 2 := by
    simpa using principalIndex_mul d hd
  have hsub : constantTermIndices 1 d ⊆
      shiftedPairingIndices 1 (principalIndex d) 0 := by
    simpa using constantTermIndices_subset_shiftedPairingIndices 1 d
      (by decide) (by decide) hd
  have hout : ∀ r : ℤ, r ∈ shiftedPairingIndices 1 (principalIndex d) 0 →
      r ∉ constantTermIndices 1 d → P r * K (-r) = 0 := by
    intro r _ hr
    have h := principalK_hecke_product_zero_outside [] (by simp) d hd r hr
    simpa only [List.prod_nil, Nat.cast_one, one_pow, one_mul,
      heckeMinusHalfWord_nil, P, K]
      using h
  have hextra : ∀ r : ℤ, r ∈ constantTermIndices 1 d →
      r ∉ shiftedPairingIndices 1 (principalIndex d) 0 →
      P r * K (-r) = 0 := by
    intro r hr hnot
    exact False.elim (hnot (hsub hr))
  have hfinite := shiftedCauchy_coeff_eq_finiteConstantTerm 1 d
    (principalIndex d) 0 hshift (constantTermIndices 1 d) P K hout hextra
  have hseries :
      ((PowerSeries.mk fun j : ℕ => K (24 * (j : ℤ) - d)) *
        (PowerSeries.mk fun j : ℕ => P (24 * (j : ℤ) - 1))).coeff
          (principalIndex d) =
        ((principalKInverseEtaSeries d).coeff (principalIndex d) : ℚ) := by
    simp only [PowerSeries.coeff_mul, PowerSeries.coeff_mk,
      principalKInverseEtaSeries_coeff,
      Int.cast_sum, Int.cast_mul, Int.cast_natCast, K, P,
      partitionFourier_at]
  have hzero :
      ((PowerSeries.mk fun j : ℕ => K (24 * (j : ℤ) - d)) *
        (PowerSeries.mk fun j : ℕ => P (24 * (j : ℤ) - 1))).coeff
          (principalIndex d) = 0 := by
    rw [hseries]
    exact_mod_cast principalKInverseEtaSeries_constantCoeff_eq_zero d hd
  simpa only [Nat.add_zero, P, K] using hfinite.symm.trans hzero

/-- The second manuscript constant-term identity at the identity Hecke word.
The divisor sum has its stated `c_t/t²` normalization even at this base case
[rolenManuscript, §3, eq. (ct2)]. -/
theorem principalK_partition_coefficient_one (d : ℕ) (hd : d % 24 = 23) :
    (partitionFourier d : ℚ) =
      -∑ t ∈ (1 : ℕ).divisors,
        ((heckePrincipalCoefficient [] t : ℚ) / (t : ℚ) ^ 2) *
          (principalKFourier d ((t : ℤ) ^ 2) : ℚ) := by
  have hct : finiteConstantTerm (constantTermIndices ([] : List ℕ).prod d)
      (fun r => (([] : List ℕ).prod : ℚ) ^ 2 *
        heckeMinusHalfWord [] (fun s => (partitionFourier s : ℚ)) r)
      (fun r => (principalKFourier d r : ℚ)) = 0 := by
    simpa only [List.prod_nil, Nat.cast_one, one_pow, one_mul,
      heckeMinusHalfWord_nil] using
      principalK_partition_finiteConstantTerm_one_zero d hd
  have h := heckeMinusHalf_coefficient_of_constantTerm_zero [] (by simp)
    (by omega : 0 < d) (fun r => (principalKFourier d r : ℚ))
    (principalKFourier_rat_neg_d d hd) hct
  simpa only [List.prod_nil, Nat.cast_one, one_pow, one_mul,
    heckeMinusHalfWord_nil] using h

private theorem constantTermIndices_one_subset (n d : ℕ) (hn : 0 < n) :
    constantTermIndices 1 d ⊆ constantTermIndices n d := by
  intro r hr
  rw [constantTermIndices_eq] at hr ⊢
  rcases Finset.mem_insert.mp hr with heq | hr
  · exact Finset.mem_insert.mpr (Or.inl heq)
  · obtain ⟨t, ht, hrt⟩ := mem_negativeDivisorSquareIndices.mp hr
    have ht1 : t = 1 := Nat.eq_one_of_dvd_one (Nat.mem_divisors.mp ht).1
    subst t
    apply Finset.mem_insert.mpr (Or.inr ?_)
    apply mem_negativeDivisorSquareIndices.mpr
    refine ⟨1, Nat.mem_divisors.mpr ⟨one_dvd n, by omega⟩, hrt⟩

private theorem f_pairing_zero_outside (n d : ℕ) (hn : 0 < n)
    (hd : d % 24 = 23) (r : ℤ)
    (hr : r ∉ constantTermIndices n d) :
    (fFourier r : ℚ) *
      (principalHFourier d (fFourier d) (-r) : ℚ) = 0 := by
  have hr1 : r ∉ constantTermIndices 1 d := by
    exact fun h => hr (constantTermIndices_one_subset n d hn h)
  simpa only [heckeThreeHalfWord_nil] using
    principalH_hecke_product_zero_outside [] (by simp) d hd r hr1

private theorem hecke_pairing_shift (n d : ℕ) (hc : n.Coprime 6)
    (hd : d % 24 = 23) :
    24 * (principalIndex d + (n * n) / 24) = d + n ^ 2 := by
  have hd' := principalIndex_mul d hd
  have hn' := squareIndex_mod_twentyFour_of_coprime_six n hc
  have hn'' : 24 * ((n * n) / 24) + 1 = n * n := by omega
  simp only [pow_two]
  omega

/-- The shadow-cancelled H product has zero rational constant term because
its two actual eta factors have complementary weights. -/
theorem analyticHecke_difference_finiteConstantTerm_zero
    (inputs : AnalyticHeckePairingInputs) (d n : ℕ)
    (hd : d % 24 = 23) (hn : 0 < n) (hc : n.Coprime 6) :
    finiteConstantTerm (constantTermIndices n.primeFactorsList.prod d)
      (fun r => heckeThreeHalfWord n.primeFactorsList
        (fun s => (fFourier s : ℚ)) r -
        (heckeShadowEigenvalue n : ℚ) * (fFourier r : ℚ))
      (fun r => (principalHFourier d (fFourier d) r : ℚ)) = 0 := by
  let H : ℤ → ℚ := fun r => (principalHFourier d (fFourier d) r : ℚ)
  let F : ℤ → ℚ := fun r => heckeThreeHalfWord n.primeFactorsList
      (fun s => (fFourier s : ℚ)) r -
      (heckeShadowEigenvalue n : ℚ) * (fFourier r : ℚ)
  let A : PowerSeries ℚ := PowerSeries.mk fun j => H (24 * (j : ℤ) - d)
  let B : PowerSeries ℚ := PowerSeries.mk fun j => F (24 * (j : ℤ) - (n : ℤ) ^ 2)
  have hprod : n.primeFactorsList.prod = n :=
    Nat.prod_primeFactorsList (Nat.ne_of_gt hn)
  have hprimes : ∀ q ∈ n.primeFactorsList, q.Prime :=
    fun q hq => Nat.prime_of_mem_primeFactorsList hq
  have hcoeff : (A * B).coeff (principalIndex d + (n * n) / 24) = 0 := by
    apply etaWeightTwoProduct_rationalSeries_constantCoeff_eq_zero
      (principalHForm d) (inputs.differenceForm n hn hc) (by decide)
    · intro τ
      simpa only [A, H, PowerSeries.coeff_mk, Rat.cast_intCast] using
        principalHForm_hasSum d hd τ
    · intro τ
      simpa only [B, F, PowerSeries.coeff_mk, Rat.cast_sub, Rat.cast_mul,
        Rat.cast_intCast] using
        inputs.difference_hasSum n hn hc τ
  have hsub : constantTermIndices n.primeFactorsList.prod d ⊆
      shiftedPairingIndices n (principalIndex d) ((n * n) / 24) := by
    rw [hprod]
    exact constantTermIndices_subset_shiftedPairingIndices n d hn hc hd
  have hout : ∀ r : ℤ,
      r ∈ shiftedPairingIndices n (principalIndex d) ((n * n) / 24) →
      r ∉ constantTermIndices n.primeFactorsList.prod d → F r * H (-r) = 0 := by
    intro r _ hr
    have hh := principalH_hecke_product_zero_outside
      n.primeFactorsList hprimes d hd r hr
    have hf := f_pairing_zero_outside n d hn hd r (by simpa only [hprod] using hr)
    dsimp [F, H]
    rw [sub_mul, mul_assoc, hh, hf]
    ring
  have hextra : ∀ r : ℤ, r ∈ constantTermIndices n.primeFactorsList.prod d →
      r ∉ shiftedPairingIndices n (principalIndex d) ((n * n) / 24) →
      F r * H (-r) = 0 := by
    intro r hr hnot
    exact False.elim (hnot (hsub hr))
  have hfinite := shiftedCauchy_coeff_eq_finiteConstantTerm n d
    (principalIndex d) ((n * n) / 24) (hecke_pairing_shift n d hc hd)
    (constantTermIndices n.primeFactorsList.prod d) F H hout hextra
  exact hfinite.symm.trans hcoeff

/-- The actual `K_d` product with the minus-half Hecke word has zero rational
constant term. The integral normalization `n²` is applied after using the
weight-two theorem on the unscaled analytic form. -/
theorem PartitionHeckeForms.finiteConstantTerm_zero
    (inputs : PartitionHeckeForms) (d n : ℕ)
    (hd : d % 24 = 23) (hn : 0 < n) (hc : n.Coprime 6) :
    finiteConstantTerm (constantTermIndices n.primeFactorsList.prod d)
      (fun r => (n.primeFactorsList.prod : ℚ) ^ 2 *
        heckeMinusHalfWord n.primeFactorsList
          (fun s => (partitionFourier s : ℚ)) r)
      (fun r => (principalKFourier d r : ℚ)) = 0 := by
  let K : ℤ → ℚ := fun r => (principalKFourier d r : ℚ)
  let P : ℤ → ℚ := fun r => heckeMinusHalfWord n.primeFactorsList
    (fun s => (partitionFourier s : ℚ)) r
  let A : PowerSeries ℚ := PowerSeries.mk fun j => K (24 * (j : ℤ) - d)
  let B : PowerSeries ℚ := PowerSeries.mk fun j => P (24 * (j : ℤ) - (n : ℤ) ^ 2)
  have hprod : n.primeFactorsList.prod = n :=
    Nat.prod_primeFactorsList (Nat.ne_of_gt hn)
  have hprimes : ∀ q ∈ n.primeFactorsList, q.Prime :=
    fun q hq => Nat.prime_of_mem_primeFactorsList hq
  have hcoeff : (A * B).coeff (principalIndex d + (n * n) / 24) = 0 := by
    apply etaWeightTwoProduct_rationalSeries_constantCoeff_eq_zero
      (principalKForm d) (inputs.form n hn hc) (by decide)
    · intro τ
      simpa only [A, K, PowerSeries.coeff_mk, Rat.cast_intCast] using
        principalKForm_hasSum d hd τ
    · intro τ
      simpa only [B, P, PowerSeries.coeff_mk] using
        inputs.hasSum n hn hc τ
  have hsub : constantTermIndices n.primeFactorsList.prod d ⊆
      shiftedPairingIndices n (principalIndex d) ((n * n) / 24) := by
    rw [hprod]
    exact constantTermIndices_subset_shiftedPairingIndices n d hn hc hd
  have hnq : (n : ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast Nat.ne_of_gt hn)
  have hout : ∀ r : ℤ,
      r ∈ shiftedPairingIndices n (principalIndex d) ((n * n) / 24) →
      r ∉ constantTermIndices n.primeFactorsList.prod d → P r * K (-r) = 0 := by
    intro r _ hr
    have hscaled := principalK_hecke_product_zero_outside
      n.primeFactorsList hprimes d hd r hr
    have hzero : (n : ℚ) ^ 2 * (P r * K (-r)) = 0 := by
      simpa only [hprod, P, K, mul_assoc] using hscaled
    exact (mul_eq_zero.mp hzero).resolve_left hnq
  have hextra : ∀ r : ℤ, r ∈ constantTermIndices n.primeFactorsList.prod d →
      r ∉ shiftedPairingIndices n (principalIndex d) ((n * n) / 24) →
      P r * K (-r) = 0 := by
    intro r hr hnot
    exact False.elim (hnot (hsub hr))
  have hraw := (shiftedCauchy_coeff_eq_finiteConstantTerm n d
    (principalIndex d) ((n * n) / 24) (hecke_pairing_shift n d hc hd)
    (constantTermIndices n.primeFactorsList.prod d) P K hout hextra).symm.trans hcoeff
  rw [finiteConstantTerm_apply]
  calc
    ∑ r ∈ constantTermIndices n.primeFactorsList.prod d,
        ((n.primeFactorsList.prod : ℚ) ^ 2 * P r) * K (-r) =
      (n : ℚ) ^ 2 * finiteConstantTerm
        (constantTermIndices n.primeFactorsList.prod d) P K := by
          rw [hprod]
          simp only [finiteConstantTerm_apply, Finset.mul_sum, mul_assoc]
    _ = 0 := by rw [hraw]; ring

/-- Compatibility with the original combined conditional interface. -/
theorem analyticHecke_partition_finiteConstantTerm_zero
    (inputs : AnalyticHeckePairingInputs) (d n : ℕ)
    (hd : d % 24 = 23) (hn : 0 < n) (hc : n.Coprime 6) :
    finiteConstantTerm (constantTermIndices n.primeFactorsList.prod d)
      (fun r => (n.primeFactorsList.prod : ℚ) ^ 2 *
        heckeMinusHalfWord n.primeFactorsList
          (fun s => (partitionFourier s : ℚ)) r)
      (fun r => (principalKFourier d r : ℚ)) = 0 :=
  inputs.partitionForms.finiteConstantTerm_zero d n hd hn hc

private theorem finiteConstantTerm_sub_smul (I : Finset ℤ)
    (A B H : ℤ → ℚ) (c : ℚ) :
    finiteConstantTerm I (fun r => A r - c * B r) H =
      finiteConstantTerm I A H - c * finiteConstantTerm I B H := by
  simp only [finiteConstantTerm_apply, sub_mul, Finset.sum_sub_distrib,
    Finset.mul_sum, mul_assoc]

/-- The finite constant-term pairing is additive in its first Fourier row. -/
theorem finiteConstantTerm_add_left (I : Finset ℤ) (A B H : ℤ → ℚ) :
    finiteConstantTerm I (A + B) H =
      finiteConstantTerm I A H + finiteConstantTerm I B H := by
  simp only [finiteConstantTerm_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- Rational scaling commutes with the finite constant-term pairing. -/
theorem finiteConstantTerm_smul_left (I : Finset ℤ) (c : ℚ)
    (A H : ℤ → ℚ) :
    finiteConstantTerm I (c • A) H = c * finiteConstantTerm I A H := by
  simp only [finiteConstantTerm_apply, Pi.smul_apply, smul_eq_mul, mul_assoc,
    Finset.mul_sum]

/-- Vanishing on each correction row whose index divides `n` extends to
their entire rational span. This is the finite-pairing step needed after
the repeated-prime shadow induction; the generator vanishings remain
separate analytic statements. -/
theorem finiteConstantTerm_zero_of_mem_shadowDivisorSpan
    (G : ℕ → ℤ → ℚ) (n : ℕ) (I : Finset ℤ) (H A : ℤ → ℚ)
    (hG : ∀ t, t ∣ n → finiteConstantTerm I (G t) H = 0)
    (hA : A ∈ shadowDivisorSpan G n) :
    finiteConstantTerm I A H = 0 := by
  rw [shadowDivisorSpan_eq] at hA
  induction hA using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, rfl⟩ := hx
    exact hG t ht
  | zero =>
    simp only [finiteConstantTerm_apply, Pi.zero_apply, zero_mul, Finset.sum_const_zero]
  | add x y hx hy ihx ihy =>
    rw [finiteConstantTerm_add_left, ihx, ihy, add_zero]
  | smul c x hx ih =>
    rw [finiteConstantTerm_smul_left, ih, mul_zero]

/-- The untransformed `H_d f` cancellation persists on the larger divisor
support used by every Hecke word. -/
theorem principalH_f_finiteConstantTerm_zero_on_hecke_indices
    (d n : ℕ) (hd : d % 24 = 23) (hn : 0 < n) :
    finiteConstantTerm (constantTermIndices n d)
      (fun r => (fFourier r : ℚ))
      (fun r => (principalHFourier d (fFourier d) r : ℚ)) = 0 := by
  have hsub := constantTermIndices_one_subset n d hn
  have heq : finiteConstantTerm (constantTermIndices 1 d)
      (fun r => (fFourier r : ℚ))
      (fun r => (principalHFourier d (fFourier d) r : ℚ)) =
    finiteConstantTerm (constantTermIndices n d)
      (fun r => (fFourier r : ℚ))
      (fun r => (principalHFourier d (fFourier d) r : ℚ)) := by
    simp only [finiteConstantTerm_apply]
    apply Finset.sum_subset hsub
    intro r hr hr1
    exact f_pairing_zero_outside 1 d (by omega) hd r hr1
  exact heq.symm.trans (principalH_f_finiteConstantTerm_zero d hd)

/-- The individual integral shadow-correction forms of
[rolen2026canonical, Proposition 2.2 and Remark 2.3, PDF p. 3]. Each valid
`G_t` has inverse eta multiplier and weight `3/2`; its coefficients are
indexed by the numerator of the exponent over `24`. The two prescribed
negative coefficients and the residue class support are recorded separately
from its analytic Fourier expansion. -/
structure IndividualShadowForms where
  coeff : ℕ → ℤ → ℤ
  form : ∀ t : ℕ, 1 < t → t.Coprime 6 → EtaInverseWeaklyHolomorphicForm 2
  /-- The inverse eta multiplier under translation forces Fourier indices
  into the residue class `-1 mod 24`. This also makes the total coefficient
  row agree with the indexed expansion of the cited form. -/
  residue_support : ∀ (t : ℕ), 1 < t → t.Coprime 6 →
    ∀ r : ℤ, r % 24 ≠ 23 → coeff t r = 0
  hasSum : ∀ (t : ℕ) (ht : 1 < t) (hc : t.Coprime 6)
      (τ : UpperHalfPlane),
    HasSum (fun j : ℕ =>
      ((coeff t (24 * (j : ℤ) - (t : ℤ) ^ 2) : ℂ) *
        Function.Periodic.qParam 1 τ ^ j))
      (Function.Periodic.qParam 1 τ ^ ((t * t) / 24) *
        Function.Periodic.qParam 24 τ * form t ht hc τ)
  negative_support : ∀ (t : ℕ), 1 < t → t.Coprime 6 →
    ∀ r : ℤ, r < 0 → coeff t r ≠ 0 →
      r = - (t : ℤ) ^ 2 ∨ r = -1
  leading : ∀ (t : ℕ), 1 < t → t.Coprime 6 →
    coeff t (- (t : ℤ) ^ 2) = 1
  next_pole : ∀ (t : ℕ), 1 < t → t.Coprime 6 →
    coeff t (-1) = -characterTwelve (t : ℤ)

/-- Every nonzero shadow coefficient belongs to the inverse-eta residue class. -/
theorem IndividualShadowForms.support (forms : IndividualShadowForms)
    (t : ℕ) (ht : 1 < t) (hc : t.Coprime 6) (r : ℤ)
    (hr : forms.coeff t r ≠ 0) : r % 24 = 23 := by
  by_contra h
  exact hr (forms.residue_support t ht hc r h)

/-- The inverse-eta residue class excludes the index zero. -/
theorem IndividualShadowForms.zero_index (forms : IndividualShadowForms)
    (t : ℕ) (ht : 1 < t) (hc : t.Coprime 6) : forms.coeff t 0 = 0 := by
  exact forms.residue_support t ht hc 0 (by decide)

/-- Extend the Fourier rows of the individual `G_t` by zero outside the
indices covered by [rolen2026canonical, Proposition 2.2 and Remark 2.3]. -/
def IndividualShadowForms.rationalRow (forms : IndividualShadowForms)
    (t : ℕ) : ℤ → ℚ :=
  if 1 < t ∧ t.Coprime 6 then
    fun r => (forms.coeff t r : ℚ)
  else 0

@[simp] theorem IndividualShadowForms.rationalRow_valid
    (forms : IndividualShadowForms) (t : ℕ)
    (ht : 1 < t) (hc : t.Coprime 6) (r : ℤ) :
    forms.rationalRow t r = (forms.coeff t r : ℚ) := by
  rw [rationalRow]
  simp only [if_pos (And.intro ht hc)]

@[simp] theorem IndividualShadowForms.rationalRow_invalid
    (forms : IndividualShadowForms) (t : ℕ)
    (ht : ¬ (1 < t ∧ t.Coprime 6)) :
    forms.rationalRow t = 0 := by
  simp [rationalRow, ht]

/-- The individually constructed integral forms `G_t`, with `G₁ = 0`, in
[rolen2026canonical, Proposition 2.2 and Remark 2.3, PDF p. 3]. This leaf
records their actual Fourier realizations and prescribed principal parts;
the subsequent Hecke identities are separate. -/
theorem rolen_individualShadowForms : Nonempty IndividualShadowForms := by
  sorry

/-- The single-prime relation for the mock row `f` in
[rolen2026canonical, Lemma 2.4, equation (2.6), PDF p. 3]. The Hecke
normalization is the three-term weight `3/2` action on indices `r/24`. -/
theorem rolen_f_prime_shadow (forms : IndividualShadowForms)
    (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    heckeThreeHalf p (fun r => (fFourier r : ℚ)) -
      (((characterTwelve (p : ℤ) * (1 + (p : ℤ)) : ℤ) : ℚ) •
        (fun r => (fFourier r : ℚ))) =
      (p : ℚ) • forms.rationalRow p := by
  sorry

/-- The single-prime relation for each integral `G_m` in
[rolen2026canonical, Lemma 2.4, equation (2.7), PDF p. 3]. The diagonal
coefficient is written exactly as the displayed `χ₁₂(p)(m²/p)`. The
conventions are `G_(m/p) = 0` when `p ∤ m` and `G₁ = 0`. -/
theorem rolen_G_prime_shadow_source
    (forms : IndividualShadowForms) (p m : ℕ) [Fact p.Prime]
    (hp5 : 5 ≤ p) (hm : 1 < m) (hmc : m.Coprime 6) :
    heckeThreeHalf p (forms.rationalRow m) =
      (p : ℚ) • forms.rationalRow (m * p) +
        ((characterTwelve (p : ℤ) : ℚ) *
          (legendreSym p ((m : ℤ) ^ 2) : ℚ)) • forms.rationalRow m +
        (if p ∣ m then forms.rationalRow (m / p) else 0) -
        ((p : ℚ) * (characterTwelve (m : ℤ) : ℚ)) •
          forms.rationalRow p := by
  sorry

/-- Translate the source's Legendre-symbol notation to the coefficient
operator used for the iterated Hecke words. -/
theorem rolen_G_prime_shadow
    (forms : IndividualShadowForms) (p m : ℕ) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hm : 1 < m) (hmc : m.Coprime 6) :
    heckeThreeHalf p (forms.rationalRow m) =
      (p : ℚ) • forms.rationalRow (m * p) +
        etaHeckeDiagonal p (-((m : ℤ) ^ 2)) • forms.rationalRow m +
        (if p ∣ m then forms.rationalRow (m / p) else 0) -
        ((p : ℚ) * (characterTwelve (m : ℤ) : ℚ)) •
          forms.rationalRow p := by
  letI : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := Nat.Prime.odd_of_ne_two hp (by omega)
  simpa only [etaHeckeDiagonal_negative_square p m hodd] using
    (rolen_G_prime_shadow_source forms p m hp5 hm hmc)

/-- Assemble the separately cited one-prime identities. The zero extension
outside Rolen's allowed indices follows from the definition of the rows. -/
def rolenPrimeShadowRelations (forms : IndividualShadowForms) : PrimeShadowRelations
    (fun r => (fFourier r : ℚ)) forms.rationalRow where
  zero_outside := by
    intro m hm
    exact forms.rationalRow_invalid m hm
  f_prime := rolen_f_prime_shadow forms
  G_prime := fun p hp hp5 m hm hmc =>
    rolen_G_prime_shadow forms p m hp hp5 hm hmc

/-- The two permitted negative coefficients of `G_t` lie at or above its
leading pole. This is the support fact needed when a divisor row is shifted
to the pole index of a larger Hecke word. -/
theorem IndividualShadowForms.coeff_below_pole_eq_zero
    (forms : IndividualShadowForms) (t : ℕ) (ht : 1 < t)
    (hc : t.Coprime 6) (r : ℤ) (hr : r < -(t : ℤ) ^ 2) :
    forms.coeff t r = 0 := by
  by_contra hne
  rcases forms.negative_support t ht hc r (by nlinarith) hne with h | h
  · omega
  · have ht' : 1 < (t : ℤ) := by exact_mod_cast ht
    nlinarith

/-- Every rational divisor correction row is represented by an actual
weight `3/2` weak form at the common pole shift `n²/24`. The construction
uses only Rolen's individual `G_t` forms; the repeated-prime word enters
later through membership in the divisor span. -/
theorem IndividualShadowForms.realize_divisorSpan
    (forms : IndividualShadowForms) (n : ℕ) (hn : 0 < n)
    (hc : n.Coprime 6) (A : ℤ → ℚ)
    (hA : A ∈ shadowDivisorSpan forms.rationalRow n) :
    ∃ g : EtaInverseWeaklyHolomorphicForm 2,
      ∀ τ : UpperHalfPlane,
        HasSum (fun j : ℕ =>
          ((A (24 * (j : ℤ) - (n : ℤ) ^ 2) : ℂ) *
            Function.Periodic.qParam 1 τ ^ j))
          (Function.Periodic.qParam 1 τ ^ ((n * n) / 24) *
            Function.Periodic.qParam 24 τ * g τ) := by
  rw [shadowDivisorSpan_eq] at hA
  induction hA using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, htdiv, rfl⟩ := hx
    by_cases hv : 1 < t ∧ t.Coprime 6
    · let N := (n * n) / 24
      let T := (t * t) / 24
      let s := N - T
      have htle : t ≤ n := Nat.le_of_dvd hn htdiv
      have hTle : T ≤ N := Nat.div_le_div_right (Nat.mul_le_mul htle htle)
      have hnmod := squareIndex_mod_twentyFour_of_coprime_six n hc
      have htmod := squareIndex_mod_twentyFour_of_coprime_six t hv.2
      have hN : 24 * N + 1 = n * n := by dsimp [N]; omega
      have hT : 24 * T + 1 = t * t := by dsimp [T]; omega
      have hs : 24 * s + t * t = n * n := by dsimp [s]; omega
      refine ⟨forms.form t hv.1 hv.2, ?_⟩
      intro τ
      let q := Function.Periodic.qParam 1 τ
      let a : ℕ → ℂ := fun j =>
        (forms.coeff t (24 * (j : ℤ) - (t : ℤ) ^ 2) : ℂ)
      have hbase : HasSum (fun j : ℕ => a j * q ^ j)
          (q ^ T * Function.Periodic.qParam 24 τ *
            forms.form t hv.1 hv.2 τ) := by
        simpa only [a, q, T] using forms.hasSum t hv.1 hv.2 τ
      have hshift := hasSum_shifted_powers s a q
        (q ^ T * Function.Periodic.qParam 24 τ *
          forms.form t hv.1 hv.2 τ) hbase
      have hrow (j : ℕ) :
          (forms.rationalRow t (24 * (j : ℤ) - (n : ℤ) ^ 2) : ℂ) =
            if s ≤ j then a (j - s) else 0 := by
        by_cases hj : s ≤ j
        · rw [if_pos hj, forms.rationalRow_valid t hv.1 hv.2]
          have hindex : 24 * ((j - s : ℕ) : ℤ) - (t : ℤ) ^ 2 =
              24 * (j : ℤ) - (n : ℤ) ^ 2 := by
            have hsInt : (24 : ℤ) * (s : ℤ) + (t : ℤ) ^ 2 = (n : ℤ) ^ 2 := by
              exact_mod_cast (by simpa only [pow_two] using hs)
            omega
          simp only [a, hindex]
          norm_cast
        · rw [if_neg hj, forms.rationalRow_valid t hv.1 hv.2]
          have hbelow : 24 * (j : ℤ) - (n : ℤ) ^ 2 < -(t : ℤ) ^ 2 := by
            have hsInt : (24 : ℤ) * (s : ℤ) + (t : ℤ) ^ 2 = (n : ℤ) ^ 2 := by
              exact_mod_cast (by simpa only [pow_two] using hs)
            have hjlt : j < s := Nat.lt_of_not_ge hj
            omega
          simp [forms.coeff_below_pole_eq_zero t hv.1 hv.2 _ hbelow]
      convert hshift using 1
      · funext j
        by_cases hj : s ≤ j
        · simpa only [hrow j, if_pos hj, q]
        · simpa only [hrow j, if_neg hj, zero_mul]
      · have hsum : s + T = N := Nat.sub_add_cancel hTle
        change q ^ N * Function.Periodic.qParam 24 τ *
            forms.form t hv.1 hv.2 τ =
          q ^ s * (q ^ T * Function.Periodic.qParam 24 τ *
            forms.form t hv.1 hv.2 τ)
        rw [← hsum, pow_add]
        ring
    · refine ⟨EtaInverseWeaklyHolomorphicForm.zero 2, ?_⟩
      intro τ
      simpa only [forms.rationalRow_invalid t hv,
        Pi.zero_apply, Rat.cast_zero, zero_mul,
        EtaInverseWeaklyHolomorphicForm.zero_apply,
        mul_zero] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
  | zero =>
    refine ⟨EtaInverseWeaklyHolomorphicForm.zero 2, ?_⟩
    intro τ
    simpa only [Pi.zero_apply, Rat.cast_zero, zero_mul,
      EtaInverseWeaklyHolomorphicForm.zero_apply,
      mul_zero] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
  | add x y hx hy ihx ihy =>
    obtain ⟨fx, hfx⟩ := ihx
    obtain ⟨fy, hfy⟩ := ihy
    refine ⟨EtaInverseWeaklyHolomorphicForm.add fx fy, ?_⟩
    intro τ
    have h := (hfx τ).add (hfy τ)
    simpa only [Pi.add_apply, Rat.cast_add,
      EtaInverseWeaklyHolomorphicForm.add_apply, add_mul, mul_add]
      using h
  | smul c x hx ih =>
    obtain ⟨fx, hfx⟩ := ih
    refine ⟨EtaInverseWeaklyHolomorphicForm.smulRat c fx, ?_⟩
    intro τ
    have h := (hfx τ).mul_left (c : ℂ)
    simp only [Pi.smul_apply, smul_eq_mul, Rat.cast_mul,
      EtaInverseWeaklyHolomorphicForm.smulRat_apply] at h ⊢
    convert h using 1
    · funext j
      ring
    · ring

/-- The correction to a finite Hecke word is a genuine weight `3/2` weak
form. The only admitted inputs are Rolen's individual forms and the cited
single-prime relations; iteration through repeated factors is proved by
`PrimeShadowRelations.word_mem_divisor_primeFactors`. -/
noncomputable def IndividualShadowForms.heckeDifferenceForm
    (forms : IndividualShadowForms)
    (relations : PrimeShadowRelations
      (fun r => (fFourier r : ℚ)) forms.rationalRow)
    (n : ℕ) (hn : 0 < n) (hc : n.Coprime 6) :
    EtaInverseWeaklyHolomorphicForm 2 :=
  Classical.choose (forms.realize_divisorSpan n hn hc
    (heckeThreeHalfWord n.primeFactorsList (fun r => (fFourier r : ℚ)) -
      (heckeShadowEigenvalue n : ℚ) • (fun r => (fFourier r : ℚ)))
    (relations.word_mem_divisor_primeFactors n hn hc))

/-- The analytic Fourier row of the actual Hecke difference. -/
theorem IndividualShadowForms.heckeDifference_hasSum
    (forms : IndividualShadowForms)
    (relations : PrimeShadowRelations
      (fun r => (fFourier r : ℚ)) forms.rationalRow)
    (n : ℕ) (hn : 0 < n) (hc : n.Coprime 6)
    (τ : UpperHalfPlane) :
    HasSum (fun j : ℕ =>
      (((heckeThreeHalfWord n.primeFactorsList
          (fun r => (fFourier r : ℚ))
          (24 * (j : ℤ) - (n : ℤ) ^ 2) -
        (heckeShadowEigenvalue n : ℚ) *
          (fFourier (24 * (j : ℤ) - (n : ℤ) ^ 2) : ℚ)) : ℂ) *
        Function.Periodic.qParam 1 τ ^ j))
      (Function.Periodic.qParam 1 τ ^ ((n * n) / 24) *
        Function.Periodic.qParam 24 τ *
          forms.heckeDifferenceForm relations n hn hc τ) := by
  have h := Classical.choose_spec (forms.realize_divisorSpan n hn hc
    (heckeThreeHalfWord n.primeFactorsList (fun r => (fFourier r : ℚ)) -
      (heckeShadowEigenvalue n : ℚ) • (fun r => (fFourier r : ℚ)))
    (relations.word_mem_divisor_primeFactors n hn hc)) τ
  simpa only [heckeDifferenceForm, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, Rat.cast_sub, Rat.cast_mul, Rat.cast_intCast] using h

/-- The legacy combined analytic interface follows from independent source
forms and the manuscript's repeated-prime shadow induction. -/
noncomputable def AnalyticHeckePairingInputs.ofShadowForms
    (forms : IndividualShadowForms)
    (relations : PrimeShadowRelations
      (fun r => (fFourier r : ℚ)) forms.rationalRow)
    (partitionForms : PartitionHeckeForms) : AnalyticHeckePairingInputs where
  differenceForm := forms.heckeDifferenceForm relations
  partitionForm := partitionForms.form
  difference_hasSum := forms.heckeDifference_hasSum relations
  partition_hasSum := partitionForms.hasSum

/-- The weak form representing the shadow-cancelled Hecke word. Rolen's
individual forms and single-prime relations are the only cited inputs;
the iteration includes repeated prime factors of `n`.
[rolen2026canonical, Proposition 2.2 and Lemma 2.4;
rolenManuscript, §3] -/
noncomputable def heckeShadowDifferenceForm
    (n : ℕ) (hn : 0 < n) (hc : n.Coprime 6) :
    EtaInverseWeaklyHolomorphicForm 2 :=
  let forms : IndividualShadowForms := Classical.choice rolen_individualShadowForms
  forms.heckeDifferenceForm (rolenPrimeShadowRelations forms) n hn hc

/-- The full convergent Fourier row of the manuscript's shadow-cancelled
Hecke word, including repeated factors. This is the analytic assertion
used in the first constant-term pairing [rolenManuscript, §3]. -/
theorem heckeShadowDifferenceForm_hasSum
    (n : ℕ) (hn : 0 < n) (hc : n.Coprime 6)
    (τ : UpperHalfPlane) :
    HasSum (fun j : ℕ =>
      (((heckeThreeHalfWord n.primeFactorsList
          (fun r => (fFourier r : ℚ))
          (24 * (j : ℤ) - (n : ℤ) ^ 2) -
        (heckeShadowEigenvalue n : ℚ) *
          (fFourier (24 * (j : ℤ) - (n : ℤ) ^ 2) : ℚ)) : ℂ) *
        Function.Periodic.qParam 1 τ ^ j))
      (Function.Periodic.qParam 1 τ ^ ((n * n) / 24) *
        Function.Periodic.qParam 24 τ *
          heckeShadowDifferenceForm n hn hc τ) := by
  let forms : IndividualShadowForms := Classical.choice rolen_individualShadowForms
  exact forms.heckeDifference_hasSum (rolenPrimeShadowRelations forms)
    n hn hc τ

/-- Only the two negative terms of an individual `G_t` can pair with a
positive coefficient of `H_d`. -/
theorem IndividualShadowForms.product_zero_outside
    (forms : IndividualShadowForms) (t d : ℕ)
    (ht : 1 < t) (hc : t.Coprime 6) (hd : d % 24 = 23)
    (r : ℤ) (hr : r ∉ constantTermIndices t d) :
    (forms.coeff t r : ℚ) *
      (principalHFourier d (fFourier d) (-r) : ℚ) = 0 := by
  apply coefficientProduct_zero_outside (by omega : 0 < t)
    (fun s => (forms.coeff t s : ℚ))
    (fun s => (principalHFourier d (fFourier d) s : ℚ))
  · intro s hs hne
    have hnz : forms.coeff t s ≠ 0 := by exact_mod_cast hne
    rcases forms.negative_support t ht hc s hs hnz with h | h
    · exact ⟨t, by omega, dvd_refl t, h⟩
    · exact ⟨1, by decide, one_dvd t, by simpa using h⟩
  · intro s hs hne
    by_contra hnot
    have hzero := principalHFourier_negative d hd (fFourier d) s hs
    rw [if_neg hnot] at hzero
    exact hne (by exact_mod_cast hzero)
  · simp [forms.zero_index t ht hc]
  · exact hr

/-- The weight-two product of `H_d` and one actual `G_t` has vanishing
constant term. This derives its finite pairing from Proposition 2.2's
individual analytic form, with no pairing premise. -/
theorem IndividualShadowForms.finiteConstantTerm_zero
    (forms : IndividualShadowForms) (t d : ℕ)
    (ht : 1 < t) (hc : t.Coprime 6) (hd : d % 24 = 23) :
    finiteConstantTerm (constantTermIndices t d)
      (fun r => (forms.coeff t r : ℚ))
      (fun r => (principalHFourier d (fFourier d) r : ℚ)) = 0 := by
  let H : ℤ → ℚ := fun r => (principalHFourier d (fFourier d) r : ℚ)
  let G : ℤ → ℚ := fun r => (forms.coeff t r : ℚ)
  let A : PowerSeries ℚ := PowerSeries.mk fun j => H (24 * (j : ℤ) - d)
  let B : PowerSeries ℚ := PowerSeries.mk fun j => G (24 * (j : ℤ) - (t : ℤ) ^ 2)
  have hcoeff : (A * B).coeff (principalIndex d + (t * t) / 24) = 0 := by
    apply etaWeightTwoProduct_rationalSeries_constantCoeff_eq_zero
      (principalHForm d) (forms.form t ht hc) (by decide)
    · intro τ
      simpa only [A, H, PowerSeries.coeff_mk, Rat.cast_intCast] using
        principalHForm_hasSum d hd τ
    · intro τ
      simpa only [B, G, PowerSeries.coeff_mk, Rat.cast_intCast] using
        forms.hasSum t ht hc τ
  have hsub : constantTermIndices t d ⊆
      shiftedPairingIndices t (principalIndex d) ((t * t) / 24) :=
    constantTermIndices_subset_shiftedPairingIndices t d (by omega) hc hd
  have hout : ∀ r : ℤ,
      r ∈ shiftedPairingIndices t (principalIndex d) ((t * t) / 24) →
      r ∉ constantTermIndices t d → G r * H (-r) = 0 := by
    intro r _ hr
    exact forms.product_zero_outside t d ht hc hd r hr
  have hextra : ∀ r : ℤ, r ∈ constantTermIndices t d →
      r ∉ shiftedPairingIndices t (principalIndex d) ((t * t) / 24) →
      G r * H (-r) = 0 := by
    intro r hr hnot
    exact False.elim (hnot (hsub hr))
  exact (shiftedCauchy_coeff_eq_finiteConstantTerm t d
    (principalIndex d) ((t * t) / 24) (hecke_pairing_shift t d hc hd)
    (constantTermIndices t d) G H hout hextra).symm.trans hcoeff

/-- A divisor's constant-term indices are contained in the indices of the
whole Hecke word. -/
theorem constantTermIndices_mono_of_dvd (t n d : ℕ)
    (ht : t ∣ n) (hn : 0 < n) :
    constantTermIndices t d ⊆ constantTermIndices n d := by
  intro r hr
  rw [constantTermIndices_eq] at hr ⊢
  rcases Finset.mem_insert.mp hr with heq | hr
  · exact Finset.mem_insert.mpr (Or.inl heq)
  · obtain ⟨u, hu, hru⟩ := mem_negativeDivisorSquareIndices.mp hr
    have huDiv : u ∣ n := (Nat.mem_divisors.mp hu).1.trans ht
    apply Finset.mem_insert_of_mem
    exact mem_negativeDivisorSquareIndices.mpr
      ⟨u, Nat.mem_divisors.mpr ⟨huDiv, by omega⟩, hru⟩

/-- The individual `G_t H_d` pairing is unchanged when the finite index
set is enlarged from `t` to any multiple `n`. -/
theorem IndividualShadowForms.finiteConstantTerm_zero_of_dvd
    (forms : IndividualShadowForms) (t n d : ℕ)
    (ht : 1 < t) (hc : t.Coprime 6) (htn : t ∣ n)
    (hn : 0 < n) (hd : d % 24 = 23) :
    finiteConstantTerm (constantTermIndices n d)
      (fun r => (forms.coeff t r : ℚ))
      (fun r => (principalHFourier d (fFourier d) r : ℚ)) = 0 := by
  have hsub := constantTermIndices_mono_of_dvd t n d htn hn
  have heq : finiteConstantTerm (constantTermIndices t d)
      (fun r => (forms.coeff t r : ℚ))
      (fun r => (principalHFourier d (fFourier d) r : ℚ)) =
      finiteConstantTerm (constantTermIndices n d)
        (fun r => (forms.coeff t r : ℚ))
        (fun r => (principalHFourier d (fFourier d) r : ℚ)) := by
    simp only [finiteConstantTerm_apply]
    apply Finset.sum_subset hsub
    intro r hr hrOld
    exact forms.product_zero_outside t d ht hc hd r hrOld
  exact heq.symm.trans (forms.finiteConstantTerm_zero t d ht hc hd)

/-- Every divisor correction pairs to zero with `H_d`, including the zero
extension at indices for which `G_t` is not defined. -/
theorem IndividualShadowForms.rationalRow_finiteConstantTerm_zero_of_dvd
    (forms : IndividualShadowForms) (t n d : ℕ)
    (htn : t ∣ n) (hn : 0 < n) (hd : d % 24 = 23) :
    finiteConstantTerm (constantTermIndices n d) (forms.rationalRow t)
      (fun r => (principalHFourier d (fFourier d) r : ℚ)) = 0 := by
  by_cases hvalid : 1 < t ∧ t.Coprime 6
  · have hrow : forms.rationalRow t = fun r => (forms.coeff t r : ℚ) := by
      funext r
      exact forms.rationalRow_valid t hvalid.1 hvalid.2 r
    rw [hrow]
    exact forms.finiteConstantTerm_zero_of_dvd t n d hvalid.1 hvalid.2
      htn hn hd
  · rw [forms.rationalRow_invalid t hvalid]
    simp only [finiteConstantTerm_apply, Pi.zero_apply, zero_mul,
      Finset.sum_const_zero]

/-- The first manuscript constant-term pairing follows from the individual
forms of [rolen2026canonical, Proposition 2.2], their one-prime relations in
Lemma 2.4, and the repeated-prime divisor induction proved here. No full
analytic Hecke-pairing bundle is assumed. [rolenManuscript, §3, (ct1)] -/
theorem IndividualShadowForms.hecke_h_finiteConstantTerm_zero
    (forms : IndividualShadowForms)
    (relations : PrimeShadowRelations
      (fun r => (fFourier r : ℚ)) forms.rationalRow)
    (n d : ℕ) (hn : 0 < n) (hc : n.Coprime 6)
    (hd : d % 24 = 23) :
    finiteConstantTerm (constantTermIndices n d)
      (heckeThreeHalfWord n.primeFactorsList
        (fun r => (fFourier r : ℚ)))
      (fun r => (principalHFourier d (fFourier d) r : ℚ)) = 0 := by
  let F : ℤ → ℚ := fun r => (fFourier r : ℚ)
  let H : ℤ → ℚ := fun r => (principalHFourier d (fFourier d) r : ℚ)
  let c : ℚ := (heckeShadowEigenvalue n : ℚ)
  have hword : heckeThreeHalfWord n.primeFactorsList F - c • F ∈
      shadowDivisorSpan forms.rationalRow n :=
    relations.word_mem_divisor_primeFactors n hn hc
  have hdiff : finiteConstantTerm (constantTermIndices n d)
      (heckeThreeHalfWord n.primeFactorsList F - c • F) H = 0 :=
    finiteConstantTerm_zero_of_mem_shadowDivisorSpan forms.rationalRow n
      (constantTermIndices n d) H _
      (fun t ht => forms.rationalRow_finiteConstantTerm_zero_of_dvd
        t n d ht hn hd) hword
  have hf : finiteConstantTerm (constantTermIndices n d) F H = 0 :=
    principalH_f_finiteConstantTerm_zero_on_hecke_indices d n hd hn
  change finiteConstantTerm (constantTermIndices n d)
    (fun r => heckeThreeHalfWord n.primeFactorsList F r - c * F r) H = 0
      at hdiff
  rw [finiteConstantTerm_sub_smul, hf, mul_zero, sub_zero] at hdiff
  exact hdiff

/-- The first manuscript constant-term identity follows from the individual
`G_t H_d` pairings and the one-prime shadow laws. The induction over the full
Hecke word, including repeated primes, is supplied by
`PrimeShadowRelations.word_mem_divisor` [rolenManuscript, §3, eq. (ct1);
rolen2026canonical, Lemma 2.4]. -/
theorem primeShadow_h_finiteConstantTerm_zero
    (G : ℕ → ℤ → ℚ)
    (relations : PrimeShadowRelations (fun r => (fFourier r : ℚ)) G)
    (ps : List ℕ) (hps : ∀ q ∈ ps, q.Prime ∧ 5 ≤ q)
    (hn : 0 < ps.prod) (d : ℕ) (hd : d % 24 = 23)
    (hG : ∀ t, t ∣ ps.prod →
      finiteConstantTerm (constantTermIndices ps.prod d) (G t)
        (fun r => (principalHFourier d (fFourier d) r : ℚ)) = 0) :
    finiteConstantTerm (constantTermIndices ps.prod d)
      (heckeThreeHalfWord ps (fun r => (fFourier r : ℚ)))
      (fun r => (principalHFourier d (fFourier d) r : ℚ)) = 0 := by
  let H : ℤ → ℚ := fun r => (principalHFourier d (fFourier d) r : ℚ)
  let F : ℤ → ℚ := fun r => (fFourier r : ℚ)
  let c : ℚ := (ps.map fun (q : ℕ) =>
    ((characterTwelve (q : ℤ) * (1 + (q : ℤ)) : ℤ) : ℚ)).prod
  have hword : heckeThreeHalfWord ps F - c • F ∈
      shadowDivisorSpan G ps.prod :=
    by simpa only [F, c] using relations.word_mem_divisor ps hps
  have hdiff : finiteConstantTerm (constantTermIndices ps.prod d)
      (heckeThreeHalfWord ps F - c • F) H = 0 :=
    finiteConstantTerm_zero_of_mem_shadowDivisorSpan G ps.prod
      (constantTermIndices ps.prod d) H _ hG hword
  have hf : finiteConstantTerm (constantTermIndices ps.prod d) F H = 0 :=
    principalH_f_finiteConstantTerm_zero_on_hecke_indices d ps.prod hd hn
  change finiteConstantTerm (constantTermIndices ps.prod d)
    (fun r => heckeThreeHalfWord ps F r - c * F r) H = 0 at hdiff
  rw [finiteConstantTerm_sub_smul, hf, mul_zero, sub_zero] at hdiff
  exact hdiff

/-- Adding back the exact shadow eigenvalue recovers the first manuscript
pairing for the full Hecke row. -/
theorem analyticHecke_h_finiteConstantTerm_zero
    (inputs : AnalyticHeckePairingInputs) (d n : ℕ)
    (hd : d % 24 = 23) (hn : 0 < n) (hc : n.Coprime 6) :
    finiteConstantTerm (constantTermIndices n.primeFactorsList.prod d)
      (heckeThreeHalfWord n.primeFactorsList
        (fun r => (fFourier r : ℚ)))
      (fun r => (principalHFourier d (fFourier d) r : ℚ)) = 0 := by
  have hdiff := analyticHecke_difference_finiteConstantTerm_zero
    inputs d n hd hn hc
  rw [finiteConstantTerm_sub_smul] at hdiff
  have hprod : n.primeFactorsList.prod = n :=
    Nat.prod_primeFactorsList (Nat.ne_of_gt hn)
  have hf := principalH_f_finiteConstantTerm_zero_on_hecke_indices d n hd hn
  rw [hprod] at hdiff
  rw [hf, mul_zero, sub_zero] at hdiff
  simpa only [hprod] using hdiff

/-- The actual analytic Hecke products supply both finite pairing inputs of
the conditional coefficient theorem. Coprimality with `6 * p` makes every
prime in the repeated-factor Hecke word a unit modulo `p`; the rational
minus-half row is reduced only through its integral normalization.
[rolenManuscript, §3, equations (ct1) and (ct2)] -/
theorem AnalyticHeckePairingInputs.toConstantTermInputs
    (inputs : AnalyticHeckePairingInputs) (p : ℕ) [Fact p.Prime]
    (_hp : 5 ≤ p) : ConstantTermInputs p := by
  constructor
  ·
    intro d n hd hn hcop
    have hc6 : n.Coprime 6 :=
      Nat.Coprime.of_dvd_right (⟨p, by omega⟩ : 6 ∣ 6 * p) hcop
    exact principalH_finiteConstantTerm_mod_of_rat_zero p
      n.primeFactorsList d
      (analyticHecke_h_finiteConstantTerm_zero inputs d n hd hn hc6)
  ·
    intro d n hd hn hcop
    have hc6 : n.Coprime 6 :=
      Nat.Coprime.of_dvd_right (⟨p, by omega⟩ : 6 ∣ 6 * p) hcop
    have hcp : n.Coprime p :=
      Nat.Coprime.of_dvd_right (⟨6, by omega⟩ : p ∣ 6 * p) hcop
    have hnUnit : (n : ZMod p) ≠ 0 := by
      intro hnZero
      have hpn : ¬ p ∣ n :=
        ((Fact.out : p.Prime).coprime_iff_not_dvd).mp hcp.symm
      exact hpn ((ZMod.natCast_eq_zero_iff n p).mp hnZero)
    have hprimes : ∀ q ∈ n.primeFactorsList, q.Prime :=
      fun q hq => Nat.prime_of_mem_primeFactorsList hq
    have hunits : ∀ q ∈ n.primeFactorsList, (q : ZMod p) ≠ 0 := by
      intro q hq
      simpa only [Int.cast_natCast] using
        primeFactorsList_unit_of_dvd p n n hnUnit (dvd_refl n) hn q hq
    exact principalK_finiteConstantTerm_mod_of_rat_zero p
      n.primeFactorsList hprimes hunits d
      (analyticHecke_partition_finiteConstantTerm_zero inputs d n hd hn hc6)

/-- The two exact constant-term identities of [rolenManuscript, §3,
equations (ct1) and (ct2)]. The first uses the individual shadow forms and
their one-prime laws [rolen2026canonical, Proposition 2.2 and Lemma 2.4];
the second uses the realized inverse-eta Hecke row. The argument applies to
all positive Hecke indices coprime to six, including repeated primes. -/
theorem constant_term_pairings_of_shadowForms
    (forms : IndividualShadowForms)
    (relations : PrimeShadowRelations
      (fun r => (fFourier r : ℚ)) forms.rationalRow)
    (partitionForms : PartitionHeckeForms)
    (d n : ℕ) (hd : d % 24 = 23) (hn : 0 < n) (hc : n.Coprime 6) :
    heckeThreeHalfWord n.primeFactorsList (fun r => (fFourier r : ℚ)) d =
        -∑ t ∈ n.divisors,
          (heckePrincipalCoefficient n.primeFactorsList t : ℚ) *
            (principalHFourier d (fFourier d) ((t : ℤ) ^ 2) : ℚ) ∧
      (n : ℚ) ^ 2 *
        heckeMinusHalfWord n.primeFactorsList
          (fun r => (partitionFourier r : ℚ)) d =
          -∑ t ∈ n.divisors,
            ((heckePrincipalCoefficient n.primeFactorsList t : ℚ) /
              (t : ℚ) ^ 2) *
              (principalKFourier d ((t : ℤ) ^ 2) : ℚ) := by
  have hprod : n.primeFactorsList.prod = n :=
    Nat.prod_primeFactorsList (Nat.ne_of_gt hn)
  have hprimes : ∀ q ∈ n.primeFactorsList, q.Prime :=
    fun q hq => Nat.prime_of_mem_primeFactorsList hq
  have hH := forms.hecke_h_finiteConstantTerm_zero relations n d hn hc hd
  have hK := partitionForms.finiteConstantTerm_zero d n hd hn hc
  simpa only [hprod] using
    principalForms_hecke_coefficients_of_constantTerms_zero
      n.primeFactorsList hprimes d hd (by simpa only [hprod] using hH) hK

/-- A single-prime analytic inverse-eta law supplies the partition rows in
both manuscript constant-term identities. Its iteration over the factor
list is proved in `PartitionHeckeForms.ofPrimeLaw`. -/
theorem constant_term_pairings_of_primeInverseEtaLaw
    (forms : IndividualShadowForms)
    (relations : PrimeShadowRelations
      (fun r => (fFourier r : ℚ)) forms.rationalRow)
    (law : PrimeInverseEtaHeckeLaw)
    (d n : ℕ) (hd : d % 24 = 23) (hn : 0 < n) (hc : n.Coprime 6) :
    heckeThreeHalfWord n.primeFactorsList (fun r => (fFourier r : ℚ)) d =
        -∑ t ∈ n.divisors,
          (heckePrincipalCoefficient n.primeFactorsList t : ℚ) *
            (principalHFourier d (fFourier d) ((t : ℤ) ^ 2) : ℚ) ∧
      (n : ℚ) ^ 2 *
        heckeMinusHalfWord n.primeFactorsList
          (fun r => (partitionFourier r : ℚ)) d =
          -∑ t ∈ n.divisors,
            ((heckePrincipalCoefficient n.primeFactorsList t : ℚ) /
              (t : ℚ) ^ 2) *
              (principalKFourier d ((t : ℤ) ^ 2) : ℚ) := by
  exact constant_term_pairings_of_shadowForms forms relations
    (PartitionHeckeForms.ofPrimeLaw law) d n hd hn hc

/-- The two manuscript product pairings follow from the individual integral
shadow forms, their cited single-prime relations, and the analytic inverse-eta
Hecke forms. The repeated-prime shadow deduction and weight-two product
pairings are proved above; the three inputs remain separate.
[rolen2026canonical, Proposition 2.2 and Lemma 2.4;
rolenManuscript, §3, equations (ct1) and (ct2)] -/
theorem constantTermInputs_of_shadowForms
    (p : ℕ) [Fact p.Prime] (forms : IndividualShadowForms)
    (relations : PrimeShadowRelations
      (fun r => (fFourier r : ℚ)) forms.rationalRow)
    (partitionForms : PartitionHeckeForms) : ConstantTermInputs p := by
  constructor
  · intro d n hd hn hcop
    have hc6 : n.Coprime 6 :=
      Nat.Coprime.of_dvd_right (⟨p, by omega⟩ : 6 ∣ 6 * p) hcop
    have hprod : n.primeFactorsList.prod = n :=
      Nat.prod_primeFactorsList (Nat.ne_of_gt hn)
    have hpair := forms.hecke_h_finiteConstantTerm_zero relations n d hn hc6 hd
    exact principalH_finiteConstantTerm_mod_of_rat_zero p
      n.primeFactorsList d (by simpa only [hprod] using hpair)
  · intro d n hd hn hcop
    have hc6 : n.Coprime 6 :=
      Nat.Coprime.of_dvd_right (⟨p, by omega⟩ : 6 ∣ 6 * p) hcop
    have hcp : n.Coprime p :=
      Nat.Coprime.of_dvd_right (⟨6, by omega⟩ : p ∣ 6 * p) hcop
    have hnUnit : (n : ZMod p) ≠ 0 := by
      intro hnZero
      have hpn : ¬ p ∣ n :=
        ((Fact.out : p.Prime).coprime_iff_not_dvd).mp hcp.symm
      exact hpn ((ZMod.natCast_eq_zero_iff n p).mp hnZero)
    have hprimes : ∀ q ∈ n.primeFactorsList, q.Prime :=
      fun q hq => Nat.prime_of_mem_primeFactorsList hq
    have hunits : ∀ q ∈ n.primeFactorsList, (q : ZMod p) ≠ 0 := by
      intro q hq
      simpa only [Int.cast_natCast] using
        primeFactorsList_unit_of_dvd p n n hnUnit (dvd_refl n) hn q hq
    exact principalK_finiteConstantTerm_mod_of_rat_zero p
      n.primeFactorsList hprimes hunits d
      (partitionForms.finiteConstantTerm_zero d n hd hn hc6)

/-- The conditional square-index coefficient theorem with the exact
individual analytic inputs. In particular, `d` need not be squarefree and
the Hecke word retains repeated factors of `m`.
[rolenManuscript, §3, Lemma 3.1] -/
theorem square_coefficient_relation_of_shadowForms
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (sign : ℤ)
    (hsign : sign = 1 ∨ sign = -1) (d : ℕ) (hdPos : 0 < d)
    (hd : d % 24 = 23)
    (hr : legendreSym p (-(d : ℤ)) = sign)
    (hspt : ∀ j : ℕ, legendreSym p (1 - 24 * (j : ℤ)) = sign →
      ((spt j : ℤ) : ZMod p) = 0)
    (forms : IndividualShadowForms)
    (relations : PrimeShadowRelations
      (fun r => (fFourier r : ℚ)) forms.rationalRow)
    (partitionForms : PartitionHeckeForms) (m : ℕ) (hmPos : 0 < m)
    (hmCop : m.Coprime (6 * p)) :
    (p : ℤ) ∣ (m : ℤ) ^ 2 *
      principalHFourier d (fFourier d) ((m : ℤ) ^ 2) +
      (d : ℤ) * principalKFourier d ((m : ℤ) ^ 2) := by
  exact conditional_square_coefficient_relation p hp sign hsign d hdPos hd
    hr hspt (constantTermInputs_of_shadowForms p forms relations partitionForms)
    m hmPos hmCop

/-- The square-coefficient relation with analytic Hecke and shadow laws as
its only constant-term input. The two weight-two product constant terms are
proved above, rather than included among the analytic hypotheses.
[rolenManuscript, §3, Lemma 3.1] -/
theorem square_coefficient_relation_of_analyticHecke
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (sign : ℤ)
    (hsign : sign = 1 ∨ sign = -1) (d : ℕ) (hdPos : 0 < d)
    (hd : d % 24 = 23)
    (hr : legendreSym p (-(d : ℤ)) = sign)
    (hspt : ∀ j : ℕ, legendreSym p (1 - 24 * (j : ℤ)) = sign →
      ((spt j : ℤ) : ZMod p) = 0)
    (inputs : AnalyticHeckePairingInputs) (m : ℕ) (hmPos : 0 < m)
    (hmCop : m.Coprime (6 * p)) :
    (p : ℤ) ∣ (m : ℤ) ^ 2 *
      principalHFourier d (fFourier d) ((m : ℤ) ^ 2) +
      (d : ℤ) * principalKFourier d ((m : ℤ) ^ 2) := by
  exact conditional_square_coefficient_relation p hp sign hsign d hdPos hd
    hr hspt (inputs.toConstantTermInputs p hp) m hmPos hmCop

/-- The manuscript's square-index conclusion using only the unresolved
single-prime analytic realization for inverse eta. The individual `G_t` forms
and their single-prime shadow identities are the separate cited inputs above;
all repeated-prime and constant-term deductions are proved here.
[rolenManuscript, §3, Lemma 3.1; rolen2026canonical, Proposition 2.2 and
Lemma 2.4] -/
theorem square_coefficient_relation_of_primeInverseEtaLaw
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (sign : ℤ)
    (hsign : sign = 1 ∨ sign = -1) (d : ℕ) (hdPos : 0 < d)
    (hd : d % 24 = 23)
    (hr : legendreSym p (-(d : ℤ)) = sign)
    (hspt : ∀ j : ℕ, legendreSym p (1 - 24 * (j : ℤ)) = sign →
      ((spt j : ℤ) : ZMod p) = 0)
    (law : PrimeInverseEtaHeckeLaw) (m : ℕ) (hmPos : 0 < m)
    (hmCop : m.Coprime (6 * p)) :
    (p : ℤ) ∣ (m : ℤ) ^ 2 *
      principalHFourier d (fFourier d) ((m : ℤ) ^ 2) +
      (d : ℤ) * principalKFourier d ((m : ℤ) ^ 2) := by
  let forms : IndividualShadowForms := Classical.choice rolen_individualShadowForms
  exact square_coefficient_relation_of_shadowForms p hp sign hsign d hdPos hd
    hr hspt forms (rolenPrimeShadowRelations forms)
    (PartitionHeckeForms.ofPrimeLaw law) m hmPos hmCop

end SptClassification.QSeries
