/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.MarkedEtaIdentification

/-!
# Classical analytic inputs for the marked lattice coefficients

These are named literature premises, with visible admissions. The periods are
`(1, τ)`, the marking is `1/6`, and the affine normalization is `y = wp'/2`.
They concern the classical Weierstrass functions, independently of CM, eta
coordinates, or reduction at a prime.

[whittakerWatson1920, §§20.2–20.22, pp. 433–437; §§21.3, 21.41–21.43,
pp. 469–473] supplies the defining series, theta products, their local uniform
convergence, and the sigma/theta correspondence. With its half-periods
`ω₁ = 1/2`, `ω₂ = τ/2` and nome `q = exp(π i τ)`, the trigonometric degeneration is
`g₂ → 4π⁴/3`, `wp(z) → π²/sin(πz)² - π²/3`, and
`wp'(z) → -2π³ cos(πz)/sin(πz)³`.
The statements below specialize these classical consequences at `z = 1/6`.
The limits hold as `Im τ → ∞` without restricting `Re τ`.
-/

public section

namespace SptClassification.ComplexUniformization

open UpperHalfPlane Filter

/-- Holomorphy of the normalized weight-four lattice invariant; the defining
Eisenstein series is locally normally convergent on H
[whittakerWatson1920, §§20.2–20.22, pp. 433–437]. -/
theorem analyticOnNhd_markedShortA_literature :
    AnalyticOnNhd ℂ markedShortA upperHalfPlaneSet := by
  sorry

/-- Holomorphy in the period ratio of `wp(1/6)`; the fixed marking never meets
the lattice on H. This is the theta-product consequence of
[whittakerWatson1920, §§21.3, 21.41–21.43, pp. 469–473]. -/
theorem analyticOnNhd_markedShortX_literature :
    AnalyticOnNhd ℂ markedShortX upperHalfPlaneSet := by
  sorry

/-- Holomorphy in the period ratio of `wp'(1/6)/2`, using the differentiated
theta products [whittakerWatson1920, §§21.41–21.43, pp. 471–473]. -/
theorem analyticOnNhd_markedShortY_literature :
    AnalyticOnNhd ℂ markedShortY upperHalfPlaneSet := by
  sorry

/-- The trigonometric degeneration of `-g₂/4` for periods `(1, τ)`.
The invariant is the Laurent coefficient in §20.22; its constant term follows
from the theta products in §§21.41–21.43 of [whittakerWatson1920]. -/
theorem tendsto_markedShortA_literature :
    Tendsto (fun z : UpperHalfPlane => markedShortA z) atImInfty
      (nhds (-(Real.pi : ℂ) ^ 4 / 3)) := by
  sorry

/-- Specialization of `wp(z) → π² csc²(πz) - π²/3` at `z = 1/6`.
See [whittakerWatson1920, §§21.41–21.43, pp. 471–473]; the nome convention
is `q = exp(π i τ)` and the first full period is one. -/
theorem tendsto_markedShortX_literature :
    Tendsto (fun z : UpperHalfPlane => markedShortX z) atImInfty
      (nhds (11 * (Real.pi : ℂ) ^ 2 / 3)) := by
  sorry

/-- Specialization of the derivative degeneration, divided by two, at `1/6`.
The square root is positive real, so the sign of the marked generator is fixed.
See [whittakerWatson1920, §§21.41–21.43, pp. 471–473]. -/
theorem tendsto_markedShortY_literature :
    Tendsto (fun z : UpperHalfPlane => markedShortY z) atImInfty
      (nhds (-4 * (Real.sqrt 3 : ℂ) * (Real.pi : ℂ) ^ 3)) := by
  sorry

end SptClassification.ComplexUniformization
