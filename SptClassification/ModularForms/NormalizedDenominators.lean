/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.PrimeLocalNormalizedProduct
import Mathlib.Data.Finset.NatAntidiagonal

/-!
# A common denominator for the normalized approximation

The Fourier row in [rolenManuscript, §2, (2.5)] is built from integer rows
and finitely many prime-local rational constants. Its common denominator
is therefore prime to the reduction prime. This supplies the uniformity
needed to localize the integral q-expansion principle.
-/

public section

namespace SptClassification

/-- One denominator prime to `p` clears the entire rational family. -/
def HasPrimeLocalCommonDenominator (p : ℕ) {ι : Type*} (a : ι → ℚ) : Prop :=
  ∃ D : ℤ, ¬(p : ℤ) ∣ D ∧ ∀ i, ∃ z : ℤ, (D : ℚ) * a i = z

namespace HasPrimeLocalCommonDenominator

variable {p : ℕ} [Fact p.Prime] {ι κ : Type*}

theorem iff_exists {a : ι → ℚ} : HasPrimeLocalCommonDenominator p a ↔
    ∃ D : ℤ, ¬(p : ℤ) ∣ D ∧ ∀ i, ∃ z : ℤ, (D : ℚ) * a i = z := by
  rfl

theorem intCast (a : ι → ℤ) :
    HasPrimeLocalCommonDenominator p (fun i => (a i : ℚ)) := by
  refine ⟨1, ?_, fun i => ⟨a i, by simp⟩⟩
  intro h
  have : p ∣ 1 := by exact_mod_cast h
  exact (Fact.out : p.Prime).not_dvd_one this

theorem of_reduces {q : ℚ} {z : ZMod p} (hq : RationalReduces p q z) :
    HasPrimeLocalCommonDenominator p (fun _ : ι => q) := by
  obtain ⟨n, D, hD, rfl⟩ := hq.exists_denominator
  have hD0 : (D : ℚ) ≠ 0 := by
    exact_mod_cast (show D ≠ 0 from fun h => hD (h ▸ dvd_zero _))
  exact ⟨D, hD, fun _ => ⟨n, by field_simp⟩⟩

private theorem not_dvd_product {D E : ℤ}
    (hD : ¬(p : ℤ) ∣ D) (hE : ¬(p : ℤ) ∣ E) : ¬(p : ℤ) ∣ D * E := by
  have hp : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using
    (Fact.out : p.Prime))
  exact fun h => (hp.dvd_mul.mp h).elim hD hE

theorem add {a b : ι → ℚ} (ha : HasPrimeLocalCommonDenominator p a)
    (hb : HasPrimeLocalCommonDenominator p b) :
    HasPrimeLocalCommonDenominator p (fun i => a i + b i) := by
  obtain ⟨D, hD, ha⟩ := ha
  obtain ⟨E, hE, hb⟩ := hb
  refine ⟨D * E, not_dvd_product hD hE, ?_⟩
  intro i
  obtain ⟨n, hn⟩ := ha i
  obtain ⟨m, hm⟩ := hb i
  refine ⟨E * n + D * m, ?_⟩
  push_cast
  rw [show (D : ℚ) * E * (a i + b i) = E * ((D : ℚ) * a i) +
    D * ((E : ℚ) * b i) by ring, hn, hm]

theorem neg {a : ι → ℚ} (ha : HasPrimeLocalCommonDenominator p a) :
    HasPrimeLocalCommonDenominator p (fun i => -a i) := by
  obtain ⟨D, hD, ha⟩ := ha
  refine ⟨D, hD, ?_⟩
  intro i
  obtain ⟨n, hn⟩ := ha i
  exact ⟨-n, by simpa using congrArg Neg.neg hn⟩

theorem sub {a b : ι → ℚ} (ha : HasPrimeLocalCommonDenominator p a)
    (hb : HasPrimeLocalCommonDenominator p b) :
    HasPrimeLocalCommonDenominator p (fun i => a i - b i) := by
  simpa only [sub_eq_add_neg] using ha.add hb.neg

theorem mul {a b : ι → ℚ} (ha : HasPrimeLocalCommonDenominator p a)
    (hb : HasPrimeLocalCommonDenominator p b) :
    HasPrimeLocalCommonDenominator p (fun i => a i * b i) := by
  obtain ⟨D, hD, ha⟩ := ha
  obtain ⟨E, hE, hb⟩ := hb
  refine ⟨D * E, not_dvd_product hD hE, ?_⟩
  intro i
  obtain ⟨n, hn⟩ := ha i
  obtain ⟨m, hm⟩ := hb i
  refine ⟨n * m, ?_⟩
  push_cast
  rw [show (D : ℚ) * E * (a i * b i) =
    ((D : ℚ) * a i) * ((E : ℚ) * b i) by ring, hn, hm]

theorem comp {a : ι → ℚ} (ha : HasPrimeLocalCommonDenominator p a) (f : κ → ι) :
    HasPrimeLocalCommonDenominator p (a ∘ f) := by
  obtain ⟨D, hD, ha⟩ := ha
  exact ⟨D, hD, fun i => ha (f i)⟩

/-- Selecting a set of coefficients preserves the same common denominator. -/
theorem restrict {a : ι → ℚ} (ha : HasPrimeLocalCommonDenominator p a)
    (P : ι → Prop) [DecidablePred P] :
    HasPrimeLocalCommonDenominator p (fun i => if P i then a i else 0) := by
  obtain ⟨D, hD, ha⟩ := ha
  refine ⟨D, hD, fun i => ?_⟩
  by_cases hi : P i
  · simpa only [if_pos hi] using ha i
  · exact ⟨0, by simp [hi]⟩

/-- If every coefficient reduces to zero, dividing the row by `p` retains
its common denominator prime to `p`. The cleared integer numerators, rather
than the denominator, absorb the division. -/
theorem div_prime_of_zero {a : ι → ℚ}
    (ha : HasPrimeLocalCommonDenominator p a)
    (hzero : ∀ i, RationalReduces p (a i) 0) :
    HasPrimeLocalCommonDenominator p (fun i => a i / p) := by
  obtain ⟨D, hD, ha⟩ := ha
  refine ⟨D, hD, fun i => ?_⟩
  obtain ⟨z, hz⟩ := ha i
  have hred := (RationalReduces.intCast p D).mul (hzero i)
  rw [hz] at hred
  have hzmod : (z : ZMod p) = 0 := by
    simpa using (hred.unique (RationalReduces.intCast p z)).symm
  obtain ⟨w, hw⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd z p).mp hzmod
  refine ⟨w, ?_⟩
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [← mul_div_assoc, hz, hw]
  push_cast
  field_simp

theorem sum {a : ι → κ → ℚ} (s : ι → Finset κ)
    (ha : HasPrimeLocalCommonDenominator p (fun ik : ι × κ => a ik.1 ik.2)) :
    HasPrimeLocalCommonDenominator p (fun i => ∑ k ∈ s i, a i k) := by
  classical
  obtain ⟨D, hD, ha⟩ := ha
  choose z hz using ha
  refine ⟨D, hD, fun i => ⟨∑ k ∈ s i, z (i, k), ?_⟩⟩
  simp only [Finset.mul_sum, Int.cast_sum]
  exact Finset.sum_congr rfl (fun k _ => hz (i, k))

theorem nonnegativeRow (A : PowerSeries ℚ)
    (ha : HasPrimeLocalCommonDenominator p (fun n => A.coeff n)) :
    HasPrimeLocalCommonDenominator p (nonnegativeRationalRow A) := by
  obtain ⟨D, hD, ha⟩ := ha
  refine ⟨D, hD, ?_⟩
  intro r
  by_cases hr : r < 0
  · exact ⟨0, by rw [nonnegativeRationalRow_zero_below A r hr]; simp⟩
  · have heq : (r.toNat : ℤ) = r := Int.toNat_of_nonneg (by omega)
    rw [← heq, nonnegativeRationalRow_natCast]
    exact ha r.toNat

theorem laurentProduct {a b : ℤ → ℚ}
    (ha : HasPrimeLocalCommonDenominator p a)
    (hb : HasPrimeLocalCommonDenominator p b) (M N : ℕ) :
    HasPrimeLocalCommonDenominator p (rationalLaurentProductRow a b M N) := by
  have hterm := (ha.comp (fun ij : ℕ × ℕ => (ij.1 : ℤ) - M)).mul
    (hb.comp (fun ij : ℕ × ℕ => (ij.2 : ℤ) - N))
  have hsum := HasPrimeLocalCommonDenominator.sum
    (a := fun (_ : ℤ) (ij : ℕ × ℕ) =>
      a ((ij.1 : ℤ) - M) * b ((ij.2 : ℤ) - N))
    (fun r : ℤ => Finset.HasAntidiagonal.antidiagonal (r + (M + N : ℕ)).toNat)
    (hterm.comp (fun ij : ℤ × (ℕ × ℕ) => ij.2))
  obtain ⟨D, hD, hsum⟩ := hsum
  refine ⟨D, hD, ?_⟩
  intro r
  by_cases hr : r < -((M + N : ℕ) : ℤ)
  · exact ⟨0, by rw [rationalLaurentProductRow_zero_below a b M N r hr]; simp⟩
  · rw [rationalLaurentProductRow_eq_sum a b M N r hr]
    exact hsum r

end HasPrimeLocalCommonDenominator

/-- The first positive Eisenstein coefficient controls all denominators. -/
theorem normalizedEisenstein_commonDenominator
    {p : ℕ} [Fact p.Prime] (k : ℕ) (z : ZMod p)
    (h : RationalReduces p (normalizedEisensteinRationalCoefficient k 1) z) :
    HasPrimeLocalCommonDenominator p (normalizedEisensteinRationalCoefficient k) := by
  obtain ⟨D, hD, hcoeff⟩ :=
    (HasPrimeLocalCommonDenominator.of_reduces (ι := Unit) h)
  obtain ⟨c, hc⟩ := hcoeff ()
  refine ⟨D, hD, ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    exact ⟨D, by simp⟩
  · refine ⟨c * (ArithmeticFunction.sigma (k - 1) n : ℤ), ?_⟩
    rw [normalizedEisensteinRationalCoefficient_eq_first_mul k n hn, ← mul_assoc, hc]
    push_cast
    rfl

/-- The full manuscript representative has a single denominator prime to `p`. -/
theorem normalizedRepresentative_commonDenominator
    {p Q : ℕ} [Fact p.Prime] [Fact Q.Prime] (hp : 5 ≤ p) :
    HasPrimeLocalCommonDenominator p (normalizedRepresentativeRationalRow p Q) := by
  have hminus := HasPrimeLocalCommonDenominator.nonnegativeRow
    (normalizedEisensteinRationalSeries (p - 1))
    (by simpa only [normalizedEisensteinRationalSeries_coeff] using
      (normalizedEisenstein_commonDenominator (p - 1) _
        (normalizedEisenstein_minus_reduces hp 1)))
  have hplus := HasPrimeLocalCommonDenominator.nonnegativeRow
    (normalizedEisensteinRationalSeries (p + 1))
    (by simpa only [normalizedEisensteinRationalSeries_coeff] using
      (normalizedEisenstein_commonDenominator (p + 1) _
        (normalizedEisenstein_plus_reduces hp 1)))
  have htwo : HasPrimeLocalCommonDenominator p
      (nonnegativeRationalRow eisensteinTwoRationalSeries) := by
    apply HasPrimeLocalCommonDenominator.nonnegativeRow
    simpa only [eisensteinTwoRationalSeries_coeff, eisensteinTwoCoefficient_eq_intCast] using
      (HasPrimeLocalCommonDenominator.intCast eisensteinTwoIntegerCoefficient (p := p))
  have hP : HasPrimeLocalCommonDenominator p (twistedPartitionRationalRow Q) := by
    convert HasPrimeLocalCommonDenominator.intCast
      (fun r => if legendreSym Q (-r) = -1 then QSeries.partitionFourier r else 0)
      (p := p) using 1
    funext r
    simp only [twistedPartitionRationalRow_eq, negativeSquareSelector_eq]
    split_ifs <;> simp
  have hS : HasPrimeLocalCommonDenominator p (twistedSmallestPartsRationalRow Q) := by
    convert HasPrimeLocalCommonDenominator.intCast
      (fun r => if legendreSym Q (-r) = -1 then QSeries.sptFourier r else 0)
      (p := p) using 1
    funext r
    simp only [twistedSmallestPartsRationalRow_eq, negativeSquareSelector_eq]
    split_ifs <;> simp
  have hc := HasPrimeLocalCommonDenominator.of_reduces (ι := ℤ) (one_div_288_reduces hp)
  have hinner : HasPrimeLocalCommonDenominator p (normalizedInnerRationalRow Q) := by
    convert hS.sub ((htwo.laurentProduct hP 0 1).mul hc) using 1
    funext r
    simp only [normalizedInnerRationalRow_eq, div_eq_mul_inv, one_mul]
  convert (hminus.laurentProduct hinner 0 1).add
    ((hplus.laurentProduct hP 0 1).mul hc) using 1
  funext r
  simp only [normalizedRepresentativeRationalRow_eq, div_eq_mul_inv, one_mul]

/-- This denominator belongs to the actual analytic form, by Fourier uniqueness. -/
theorem SptModularApproximation.commonDenominator
    {p Q : ℕ} {hp : 5 ≤ p} [Fact p.Prime] [Fact Q.Prime]
    (A : SptModularApproximation p Q hp) :
    HasPrimeLocalCommonDenominator p A.form.coeff := by
  have heq : A.form.coeff = normalizedRepresentativeRationalRow p Q := by
    funext r
    exact A.form_coeff_eq_normalizedRepresentative_all r
  rw [heq]
  exact normalizedRepresentative_commonDenominator hp

/-- The divided source progression in the manuscript's slash argument has
a uniform prime-local denominator, even when `p` divides the modulus `M`. -/
theorem SptModularApproximation.dividedProjection_commonDenominator
    {p Q : ℕ} {hp : 5 ≤ p} [Fact p.Prime] [Fact Q.Prime]
    (A : SptModularApproximation p Q hp) (M : ℕ) (u : ℤ)
    (hzero : ∀ r : ℤ, (r : ZMod M) = (u : ZMod M) → A.form.coeffMod r = 0) :
    HasPrimeLocalCommonDenominator p
      (fun r : ℤ => (if (r : ZMod M) = (u : ZMod M) then A.form.coeff r else 0) / p) := by
  apply (A.commonDenominator.restrict
    (fun r : ℤ => (r : ZMod M) = (u : ZMod M))).div_prime_of_zero
  intro r
  by_cases hr : (r : ZMod M) = (u : ZMod M)
  · rw [if_pos hr]
    obtain ⟨num, den, hd, hq, hz⟩ := A.form.pIntegral r
    have hred : RationalReduces p (A.form.coeff r) (A.form.coeffMod r) := by
      rw [hq]
      exact RationalReduces.ofFraction p num den hd _ hz
    rwa [hzero r hr] at hred
  · simpa only [if_neg hr, Int.cast_zero] using RationalReduces.intCast p 0

end SptClassification
