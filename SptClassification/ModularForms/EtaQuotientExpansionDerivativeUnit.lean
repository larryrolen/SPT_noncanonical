/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.EtaQuotientExpansionDerivative
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# The formal eta-coordinate derivative is a cusp unit

The normalized derivative `q Θt = q U'(q) - U(q)` has constant coefficient
`-1` in its integral expansion. Hence it remains a formal unit after base
change to any commutative ring. This is a local cusp statement toward the
integral coordinate of [rolen2026canonical], Section 4.
-/

public section

namespace SptClassification

open PowerSeries

/-- The normalized derivative retains its unit constant term after any
commutative-ring base change. -/
theorem levelSixEtaDerivativeSeries_map_constantCoeff
    (R : Type*) [CommRing R] :
    constantCoeff (levelSixEtaDerivativeSeries.map (Int.castRingHom R)) = -1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply,
    levelSixEtaDerivativeSeries_constantCoeff]
  simp

/-- The normalized derivative has a formal inverse over every commutative
coefficient ring, including rings of positive characteristic. -/
theorem levelSixEtaDerivativeSeries_map_mul_invOfUnit
    (R : Type*) [CommRing R] :
    levelSixEtaDerivativeSeries.map (Int.castRingHom R) *
      (levelSixEtaDerivativeSeries.map (Int.castRingHom R)).invOfUnit (-1) = 1 := by
  exact PowerSeries.mul_invOfUnit _ _
    (levelSixEtaDerivativeSeries_map_constantCoeff R)

end SptClassification
