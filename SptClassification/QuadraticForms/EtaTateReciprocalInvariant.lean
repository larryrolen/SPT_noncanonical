/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.UpperHalfPlaneMarkedCurve

/-!
# The actual marked and eta families have equal reciprocal invariants

The unmarked covering identity and the pointed Tate coordinate construction
supply this equality at every point, including the zero j-invariant fibers.
Selecting the marked branch still requires the independent cusp limits.
-/

public section

namespace SptClassification.ComplexUniformization

open LevelSixWeierstrass

/-- Maier's cleared invariant relation gives equality of reciprocal invariants;
no nonzero hypothesis on j or c₄ is needed. -/
theorem eta_reciprocalInvariant (z : UpperHalfPlane) :
    tateReciprocalInvariant (tateParameter (levelSixEtaQuotient z)) =
      (curve (upperHalfPlanePeriods z)).Δ / (curve (upperHalfPlanePeriods z)).c₄ ^ 3 := by
  let L := upperHalfPlanePeriods z
  letI := curve_isElliptic L
  have h := levelSixEta_invariant_relation L z
    (upperHalfPlanePeriods_omega_one z) (upperHalfPlanePeriods_omega_two z)
  rw [tateParameter_reciprocalInvariant _ (eta_add_eight_ne_zero z)]
  rw [RationalPointMap.reciprocalInvariant_eq_inv_j (curve L)]
  rw [← h, div_eq_mul_inv, mul_inv_rev, ← mul_assoc,
    mul_inv_cancel₀ (eta_discriminant_ne_zero z), one_mul]

/-- The actual short Tate coordinate and eta coordinate have equal reciprocal
invariants throughout the upper half-plane. The marking comes from `1/6`. -/
theorem shortTateParameter_reciprocalInvariant_eta (z : UpperHalfPlane) :
    tateReciprocalInvariant
      (shortTateParameter (-(upperHalfPlanePeriods z).g₂ / 4)
        ((upperHalfPlanePeriods z).weierstrassP (1 / 6))
        ((upperHalfPlanePeriods z).derivWeierstrassP (1 / 6) / 2)) =
      tateReciprocalInvariant (tateParameter (levelSixEtaQuotient z)) := by
  rw [← (upperHalfPlanePair_tateCoordinate_eq z).2,
    LevelSixPair.tateCoordinate_reciprocalInvariant, eta_reciprocalInvariant]
  rfl

end SptClassification.ComplexUniformization
