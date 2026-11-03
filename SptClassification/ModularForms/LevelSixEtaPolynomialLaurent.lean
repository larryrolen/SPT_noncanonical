/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.LevelSixHolomorphicBasis
public import SptClassification.ModularForms.LevelSixTateInjectivity
import all SptClassification.ModularForms.LevelSixTateInjectivity
import all SptClassification.ModularForms.LevelSixHolomorphicBasis
import all SptClassification.ModularForms.LevelSixEtaFrame
import all SptClassification.ModularForms.LevelSixTateComparison
import all SptClassification.ModularForms.LevelSixSerreExpansion
import Mathlib.Tactic.Ring

/-!
# Eta polynomials over coefficient rings and their Laurent expansions

The reversed basis is `t^(k-i) b^k = q^i U^(k-i) V^k`. The weight bound
is retained before coefficient reduction, even if the polynomial degree drops.
This supplies the polynomial numerator comparison in [rolenManuscript, §4].
-/

public noncomputable section

namespace SptClassification.LevelSixEtaPolynomialLaurent

open LevelSixHolomorphicBasis LevelSixEtaFrame LevelSixSerreExpansion
  LevelSixTateComparison LevelSixTateInjectivity

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The finite holomorphic eta row over any coefficient ring. Its interpretation
as `P(t)b^k` requires `P.natDegree ≤ k`. -/
def polynomialSeries (k : ℕ) (P : Polynomial R) : PowerSeries R :=
  ∑ i ∈ Finset.range (k + 1),
    PowerSeries.C (P.coeff (k - i)) *
      PowerSeries.map (Int.castRingHom R) (basisSeries k i)

/-- Specialization preserves the chosen weight and reversed indices. -/
theorem map_polynomialSeries (f : R →+* S) (k : ℕ) (P : Polynomial R) :
    PowerSeries.map f (polynomialSeries k P) = polynomialSeries k (P.map f) := by
  simp only [polynomialSeries, map_sum, map_mul, PowerSeries.map_C,
    Polynomial.coeff_map]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ext n
  simp

/-- Compatibility with the original complex eta basis, with no new analytic premise. -/
theorem polynomialSeries_complex (k : ℕ) (P : Polynomial ℂ) :
    polynomialSeries k P = LevelSixHolomorphicBasis.polynomialSeries k P := by
  rfl

variable (K : Type*) [Field K]

/-- An individual reversed basis row has its expected Laurent expansion. -/
theorem tateBase_basisSeries (k i : ℕ) (hi : i ≤ k) :
    tateBase K (PowerSeries.map (Int.castRingHom K) (basisSeries k i)) =
      etaParameter K ^ (k - i) * tateBase K (cuspForm K) ^ k := by
  have hunit : PowerSeries.map (Int.castRingHom K) levelSixFormalEulerUnit =
      etaUnit K := by rfl
  simp only [basisSeries, basisUnit, map_mul, map_pow, PowerSeries.map_X, hunit]
  rw [← q_mul_etaParameter]
  change q K ^ i * ((q K * etaParameter K) ^ (k - i) *
    tateBase K (PowerSeries.map (Int.castRingHom K) cuspFormUnit) ^ k) = _
  rw [cuspForm, map_mul]
  change _ = etaParameter K ^ (k - i) *
    (q K * tateBase K (PowerSeries.map (Int.castRingHom K) cuspFormUnit)) ^ k
  rw [mul_pow, mul_pow]
  have hp : q K ^ i * q K ^ (k - i) = q K ^ k := by
    rw [← pow_add, Nat.add_sub_of_le hi]
  calc
    _ = (q K ^ i * q K ^ (k - i)) * etaParameter K ^ (k - i) *
        tateBase K (PowerSeries.map (Int.castRingHom K) cuspFormUnit) ^ k := by ring
    _ = _ := by rw [hp]; ring

/-- A degree-bounded eta polynomial embeds into the actual Laurent coordinate.
Neither `t` itself nor arbitrary rational functions are sent to power series. -/
theorem tateBase_polynomialSeries (k : ℕ) (P : Polynomial K)
    (hdeg : P.natDegree ≤ k) :
    tateBase K (polynomialSeries k P) =
      polynomialExpansion K P * tateBase K (cuspForm K) ^ k := by
  simp only [polynomialSeries, map_sum, map_mul]
  have hb : (∑ i ∈ Finset.range (k + 1),
      tateBase K (PowerSeries.C (P.coeff (k - i))) *
        tateBase K (PowerSeries.map (Int.castRingHom K) (basisSeries k i))) =
      ∑ i ∈ Finset.range (k + 1), constants K (P.coeff (k - i)) *
        (etaParameter K ^ (k - i) * tateBase K (cuspForm K) ^ k) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [tateBase_basisSeries K k i (by simpa using Finset.mem_range.mp hi)]
    rfl
  rw [hb]
  change (∑ i ∈ Finset.range (k + 1), constants K (P.coeff (k - i)) *
    (etaParameter K ^ (k - i) * tateBase K (cuspForm K) ^ k)) = _
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  congr 1
  change _ = P.eval₂ (constants K) (etaParameter K)
  rw [Polynomial.eval₂_eq_sum_range' _ (Nat.lt_succ_of_le hdeg)]
  simpa using (Finset.sum_range_reflect
    (fun i => constants K (P.coeff i) * etaParameter K ^ i) (k + 1))

/-- Reduction into any field keeps the degree bound from the original ring. -/
theorem tateBase_map_polynomialSeries (f : R →+* K) (k : ℕ)
    (P : Polynomial R) (hdeg : P.natDegree ≤ k) :
    tateBase K (PowerSeries.map f (polynomialSeries k P)) =
      polynomialExpansion K (P.map f) * tateBase K (cuspForm K) ^ k := by
  rw [map_polynomialSeries]
  exact tateBase_polynomialSeries K k (P.map f)
    (le_trans Polynomial.natDegree_map_le hdeg)

/-- Reduction followed by a residue-field extension uses the original weight
bound; no preservation of the leading coefficient is required. -/
theorem tateBase_map_map_polynomialSeries (f : R →+* S) (g : S →+* K)
    (k : ℕ) (P : Polynomial R) (hdeg : P.natDegree ≤ k) :
    tateBase K (PowerSeries.map g (PowerSeries.map f (polynomialSeries k P))) =
      polynomialExpansion K (P.map (g.comp f)) * tateBase K (cuspForm K) ^ k := by
  have hm (F : PowerSeries R) : PowerSeries.map g (PowerSeries.map f F) =
      PowerSeries.map (g.comp f) F := by
    ext n
    simp
  rw [hm]
  exact tateBase_map_polynomialSeries K (g.comp f) k P hdeg

/-- Equality after an injective coefficient map determines the integral row. -/
theorem eq_polynomialSeries_of_map (f : R →+* S) (hf : Function.Injective f)
    (k : ℕ) (P : Polynomial R) (F : PowerSeries R)
    (hF : PowerSeries.map f F = polynomialSeries k (P.map f)) :
    F = polynomialSeries k P := by
  rw [← map_polynomialSeries] at hF
  ext n
  apply hf
  simpa using congrArg (PowerSeries.coeff n) hF

/-- A local complex coefficient ring recovers its exact eta row from the
actual Fourier expansion. The only analytic input is the previously named
Euler-product comparison [maier2009, Tables 8 and 11]. -/
theorem series_eq_of_qExpansion (R : Subring ℂ) (k : ℕ)
    (P : Polynomial R) (hdeg : P.natDegree ≤ k)
    (F : UpperHalfPlane → ℂ)
    (hF : ∀ z, F z = (P.map R.subtype).eval (levelSixEtaQuotient z) * b z ^ k)
    (row : PowerSeries R)
    (hrow : PowerSeries.map R.subtype row = UpperHalfPlane.qExpansion 1 F) :
    row = polynomialSeries k P := by
  apply eq_polynomialSeries_of_map R.subtype R.subtype_injective k P row
  rw [hrow, funext hF, polynomial_qExpansion_literature k (P.map R.subtype)
    (le_trans Polynomial.natDegree_map_le hdeg)]
  exact (polynomialSeries_complex k (P.map R.subtype)).symm

/-- The same local row can then be reduced to any coefficient field and
embedded into the true Laurent coordinate. -/
theorem tateBase_row_of_qExpansion (R : Subring ℂ) (f : R →+* K) (k : ℕ)
    (P : Polynomial R) (hdeg : P.natDegree ≤ k)
    (F : UpperHalfPlane → ℂ)
    (hF : ∀ z, F z = (P.map R.subtype).eval (levelSixEtaQuotient z) * b z ^ k)
    (row : PowerSeries R)
    (hrow : PowerSeries.map R.subtype row = UpperHalfPlane.qExpansion 1 F) :
    tateBase K (PowerSeries.map f row) =
      polynomialExpansion K (P.map f) * tateBase K (cuspForm K) ^ k := by
  rw [series_eq_of_qExpansion R k P hdeg F hF row hrow]
  exact tateBase_map_polynomialSeries K f k P hdeg

/-- The general all-cusp eta basis and an independently supplied integral
Fourier row give a typed polynomial and an exact equality over the local ring.
This theorem constructs no particular CM lift and assumes no good reduction. -/
theorem holomorphic_basis_with_series (R : Subring ℂ) (k : ℕ) (hk : Even k)
    (F : ModularForm ((CongruenceSubgroup.Gamma0 6).map
      (Matrix.SpecialLinearGroup.mapGL ℝ)) (k : ℤ))
    (row : PowerSeries R)
    (hrow : PowerSeries.map R.subtype row =
      UpperHalfPlane.qExpansion 1 (fun z => F z)) :
    ∃ P : Polynomial R, P.natDegree ≤ k ∧
      (∀ z : UpperHalfPlane,
        F z = (P.map R.subtype).eval (levelSixEtaQuotient z) * b z ^ k) ∧
      row = polynomialSeries k P := by
  have hc : ∀ n, PowerSeries.coeff n
      (UpperHalfPlane.qExpansion 1 (fun z => F z)) ∈ R := by
    intro n
    rw [← hrow, PowerSeries.coeff_map]
    exact (PowerSeries.coeff n row).property
  obtain ⟨P, hdeg, hF⟩ := holomorphic_basis_over_subring R k hk F hc
  exact ⟨P, hdeg, hF, series_eq_of_qExpansion R k P hdeg (fun z => F z) hF row hrow⟩

/-- A ready-to-specialize numerator identity for an actual holomorphic form.
The witness degree is bounded over the original ring, before reduction. -/
theorem holomorphic_basis_with_laurent (R : Subring ℂ) (f : R →+* K)
    (k : ℕ) (hk : Even k)
    (F : ModularForm ((CongruenceSubgroup.Gamma0 6).map
      (Matrix.SpecialLinearGroup.mapGL ℝ)) (k : ℤ))
    (row : PowerSeries R)
    (hrow : PowerSeries.map R.subtype row =
      UpperHalfPlane.qExpansion 1 (fun z => F z)) :
    ∃ P : Polynomial R, P.natDegree ≤ k ∧ row = polynomialSeries k P ∧
      tateBase K (PowerSeries.map f row) =
        polynomialExpansion K (P.map f) * tateBase K (cuspForm K) ^ k := by
  obtain ⟨P, hdeg, _, hP⟩ := holomorphic_basis_with_series R k hk F row hrow
  refine ⟨P, hdeg, hP, ?_⟩
  rw [hP]
  exact tateBase_map_polynomialSeries K f k P hdeg

end SptClassification.LevelSixEtaPolynomialLaurent

