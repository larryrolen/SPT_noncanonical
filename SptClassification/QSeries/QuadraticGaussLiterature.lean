/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.QuadraticCuspGauss

/-!
# The signed quadratic Gauss sum

The positive additive phase is the one in `ZMod.stdAddChar`. Its sign is
needed in the inverse-eta Hecke calculation and does not follow from the
Gauss-square identity [berndtEvansWilliams1998, Chapter 1, evaluation of the
quadratic Gauss sum].
-/

public section

namespace SptClassification.QSeries

/-- The classical signed quadratic Gauss evaluation for an odd prime, with
the integral quadratic character cast to `ℂ`, the positive standard additive
character, and the positive real square root. The exact primary-source
theorem locator remains unverified.
[berndtEvansWilliams1998, Chapter 1, evaluation of the quadratic Gauss sum] -/
theorem quadraticGaussSum_positivePhase (p : ℕ) [Fact p.Prime]
    (hpOdd : p ≠ 2) :
    gaussSum (quadraticComplexChar p) ZMod.stdAddChar =
      (if p % 4 = 1 then (1 : ℂ) else Complex.I) * (Real.sqrt p : ℂ) := by
  sorry

end SptClassification.QSeries
