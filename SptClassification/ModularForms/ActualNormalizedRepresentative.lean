/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.ScaledGeneratingDerivative
public import SptClassification.ModularForms.NormalizedAutomorphy

/-!
# The actual holomorphic normalized representative

This specializes the analytic construction in [rolenManuscript, §2, (2.5)]
to the partition-defined smallest-parts function. Holomorphy is proved here;
the half-integral transformation and cusp laws remain separate.
-/

public section

namespace SptClassification

open UpperHalfPlane
open scoped Manifold

/-- The derivative terms cancel before any modular transformation is used.
The only remaining correction is the actual `E₂ P_Q / 288` term. -/
theorem sptTwistedAnalyticData_mock_sub_serre (Q : ℕ) [Fact Q.Prime]
    (τ : UpperHalfPlane) :
    (sptTwistedAnalyticData Q).twistedM τ -
        (sptTwistedAnalyticData Q).serreDerivativeP τ / 12 =
      fourierFilter (negativeSquareResidueSelector Q) scaledSptFunction τ -
        EisensteinSeries.E2 τ *
          fourierFilter (negativeSquareResidueSelector Q) scaledPartitionFunction τ / 288 := by
  have hmock : sptMockHolomorphicPart = scaledSptFunction +
      (fun z => (12 : ℂ)⁻¹ *
        Derivative.normalizedDerivOfComplex scaledPartitionFunction z) := by
    funext z
    rw [sptMockHolomorphicPart_apply]
    simp only [Pi.add_apply, div_eq_mul_inv, mul_comm]
  rw [sptTwistedAnalyticData_twistedM_eq, sptTwistedAnalyticData_serreDerivativeP_eq,
    hmock, fourierFilter_add, fourierFilter_const_mul, serreDerivative_negative_half,
    normalizedDeriv_fourierFilter _ _ mdifferentiable_scaledPartitionFunction]
  simp only [Pi.add_apply]
  ring

/-- An exact analytic form of the manuscript's Eisenstein correction, now using
only the two original generating functions and their finite filters. -/
theorem sptTwistedAnalyticData_normalizedRepresentative_eq
    (p Q : ℕ) [Fact Q.Prime] (hp : 5 ≤ p) (τ : UpperHalfPlane) :
    (sptTwistedAnalyticData Q).normalizedRepresentative p hp τ =
      ModularForm.E (k := p - 1) (by omega) τ *
        fourierFilter (negativeSquareResidueSelector Q) scaledSptFunction τ +
      (ModularForm.E (k := p + 1) (by omega) τ -
        ModularForm.E (k := p - 1) (by omega) τ * EisensteinSeries.E2 τ) *
          fourierFilter (negativeSquareResidueSelector Q) scaledPartitionFunction τ / 288 := by
  rw [SptTwistedAnalyticData.normalizedRepresentative_apply,
    sptTwistedAnalyticData_mock_sub_serre, sptTwistedAnalyticData_twistedP_eq]
  ring

/-- The normalized representative built from the actual generating functions is
holomorphic, without any completion, transformation or cusp hypotheses. -/
theorem sptTwistedAnalyticData_normalizedRepresentative_holomorphic
    (p Q : ℕ) [Fact Q.Prime] (hp : 5 ≤ p) :
    MDiff ((sptTwistedAnalyticData Q).normalizedRepresentative p hp) := by
  exact (sptTwistedAnalyticData Q).normalizedRepresentative_holomorphic hp
    (sptTwistedAnalyticData_twistedM_holomorphic Q)
    (sptTwistedAnalyticData_serreDerivativeP_holomorphic Q)
    (sptTwistedAnalyticData_twistedP_holomorphic Q)

end SptClassification
