/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.EtaQuotientCuspsEulerGerms

/-!
# Local zero and pole of the level-six eta quotient

At the infinity cusp, the reciprocal of the eta quotient is the local nome
divided by a holomorphic unit. At the Fricke cusp zero, the eta quotient is
`72` times the same germ. Their nonzero first derivatives give the simple
pole and simple zero needed for the cusp divisor calculation in
[rolen2026canonical], Section 4.
-/

public section

namespace SptClassification

/-- The reciprocal-coordinate germ at infinity has a simple zero with
normalized derivative one. -/
theorem hasDerivAt_levelSixInfinityReciprocalGerm :
    HasDerivAt (fun q : ℂ => q / levelSixEulerUnit q) 1 0 := by
  have hunit : HasDerivAt levelSixEulerUnit
      (deriv levelSixEulerUnit 0) 0 :=
    (differentiableAt_levelSixEulerUnit (by simp)).hasDerivAt
  have h := (hasDerivAt_id (0 : ℂ)).mul
    (hunit.inv (by simp [levelSixEulerUnit_zero]))
  convert h using 1
  · funext q
    simp [div_eq_mul_inv]
  · simp [levelSixEulerUnit_zero]

/-- The Fricke-coordinate germ at zero has a simple zero with exact leading
coefficient `72`. -/
theorem hasDerivAt_levelSixZeroGerm :
    HasDerivAt (fun q : ℂ => 72 * q / levelSixEulerUnit q) 72 0 := by
  convert hasDerivAt_levelSixInfinityReciprocalGerm.const_mul (72 : ℂ) using 1
  · funext q
    ring
  · ring

/-- The actual reciprocal eta quotient agrees with the simple-zero germ at
the infinity cusp. -/
theorem levelSixEtaQuotient_inv_eq_infinityGerm (z : UpperHalfPlane) :
    (levelSixEtaQuotient (z : ℂ))⁻¹ =
      Function.Periodic.qParam 1 z /
        levelSixEulerUnit (Function.Periodic.qParam 1 z) := by
  have hq : Function.Periodic.qParam 1 z ≠ 0 := by
    unfold Function.Periodic.qParam
    exact Complex.exp_ne_zero _
  have ht := levelSixEtaQuotient_ne_zero z
  rw [← qParam_mul_levelSixEtaQuotient]
  field_simp [hq, ht]

/-- Along the upper half-plane, the Fricke transform agrees exactly with its
zero-cusp germ in the ordinary nome. -/
theorem levelSixEtaQuotient_fricke_eq_zeroGerm (z : UpperHalfPlane) :
    levelSixEtaQuotient (-1 / (6 * (z : ℂ))) =
      72 * Function.Periodic.qParam 1 z /
        levelSixEulerUnit (Function.Periodic.qParam 1 z) := by
  have hq : Function.Periodic.qParam 1 z ≠ 0 := by
    unfold Function.Periodic.qParam
    exact Complex.exp_ne_zero _
  have h := levelSixEtaQuotient_fricke_six_div_qParam z
  apply (div_eq_iff hq).mp at h
  calc
    levelSixEtaQuotient (-1 / (6 * (z : ℂ))) =
        (72 / levelSixEulerUnit (Function.Periodic.qParam 1 z)) *
          Function.Periodic.qParam 1 z := h
    _ = _ := by ring

end SptClassification
