/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.ScaledGeneratingDerivative
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# The analytic completion of the smallest-parts generating function

We use [ahlgrenAndersen2016, §3, (3.1)–(3.2), PDF p. 9] directly at
`24τ`. The vertical ray is parametrized by `w = -24 conjugate(τ) + it`;
the factor `i` in the integrand is `dw/dt`. Complex powers use the principal
branch, and the coefficient is `sqrt(3i)/(2π)`.
-/

public section

namespace SptClassification

open UpperHalfPlane MeasureTheory

/-- The nonholomorphic Eichler integral in the Ahlgren–Andersen normalization,
rescaled to integral Fourier indices. -/
noncomputable def sptNonholomorphicCorrection (τ : UpperHalfPlane) : ℂ :=
  Complex.sqrt (3 * Complex.I) / (2 * Real.pi) *
    ∫ t : ℝ in Set.Ici 0,
      ModularForm.eta (-24 * star (τ : ℂ) + Complex.I * t) /
        (24 * (τ : ℂ) + (-24 * star (τ : ℂ) + Complex.I * t)) ^ (3 / 2 : ℂ) *
          Complex.I

/-- The actual completed function, not an abstract form with a prescribed
holomorphic part. Its holomorphic part has already been identified with
the partition-defined smallest-parts series. -/
noncomputable def sptCompletion (τ : UpperHalfPlane) : ℂ :=
  sptMockHolomorphicPart τ + sptNonholomorphicCorrection τ

theorem sptCompletion_eq :
    sptCompletion = sptMockHolomorphicPart + sptNonholomorphicCorrection := (rfl)

/-- The negative-square support of the eta Eichler integral. This is the
Fourier-expansion consequence of the integral in
[ahlgrenAndersen2016, §3, (3.1), PDF p. 9], equivalently
[ahlgrenBringmannLovejoy2011, §3, (3.1), PDF p. 7], and the unary-theta
expansion of `eta(24τ)`. The amplitudes may depend on height, as required
for the incomplete-gamma terms. This named analytic literature premise
does not assert modularity or any congruence propagation. -/
theorem etaEichlerIntegral_negativeSquare_expansion :
    ∃ amplitude : ℤ → ℝ → ℂ, ∀ τ : UpperHalfPlane,
      HasSum (fun t => amplitude t τ.im *
        Function.Periodic.qParam 1 τ ^ (-(t ^ 2))) (sptNonholomorphicCorrection τ) := by
  sorry

/-- The manuscript's actual finite twist removes the nonholomorphic
correction, using its negative-square support. -/
theorem fourierFilter_sptCompletion (Q : ℕ) [Fact Q.Prime] :
    fourierFilter (negativeSquareResidueSelector Q) sptCompletion =
      (sptTwistedAnalyticData Q).twistedM := by
  obtain ⟨amplitude, hsum⟩ := etaEichlerIntegral_negativeSquare_expansion
  rw [sptTwistedAnalyticData_twistedM_eq]
  exact fourierFilter_completion_of_height_expansion Q sptCompletion
    sptMockHolomorphicPart sptNonholomorphicCorrection sptCompletion_eq amplitude hsum

end SptClassification
