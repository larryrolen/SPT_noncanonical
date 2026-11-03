/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.LevelSixTateCoordinates
public import SptClassification.QuadraticForms.CMIntegralModel

/-!
# Integral Tate parameters and specialization

The denominator of the Tate parameter is a unit on an actual integral CM
fiber. Thus the parameter exists before taking a complex or residue fiber,
and both fiber maps recover the same rational coordinate formula.
-/

public section

namespace SptClassification.LevelSixWeierstrass

variable {R : Type*} [CommRing R]

/-- The Tate coordinate in the base ring, using its invertible denominator. -/
noncomputable def integralTateParameter (t : R) (h : IsUnit (9 * (t + 8))) : R :=
  -t * ↑h.unit⁻¹

/-- The integral coordinate satisfies its denominator-cleared relation. -/
theorem integralTateParameter_mul (t : R) (h : IsUnit (9 * (t + 8))) :
    integralTateParameter t h * (9 * (t + 8)) = -t := by
  change -t * ↑h.unit⁻¹ * (9 * (t + 8)) = -t
  calc
    -t * ↑h.unit⁻¹ * (9 * (t + 8)) = -t * (↑h.unit⁻¹ * ↑h.unit) := by
      rw [h.unit_spec, mul_assoc]
    _ = -t := by simp

/-- Scaling from the integral Tate equation to the original integral model. -/
noncomputable def integralTateChange (t : R) (h : IsUnit (9 * (t + 8))) :
    WeierstrassCurve.VariableChange R :=
  ⟨h.unit⁻¹, 0, 0, 0⟩

/-- The admissible coordinate change is defined over the integral base itself,
not only over its complex or residue fields. It fixes the affine origin. -/
theorem integralTateChange_curve (t : R) (h : IsUnit (9 * (t + 8))) :
    integralTateChange t h • tateCurve (integralTateParameter t h) = curve t := by
  let c := integralTateParameter t h
  let u : R := 9 * (t + 8)
  have hc : c * u = -t := integralTateParameter_mul t h
  have h1 : u * (1 - c) = (curve t).a₁ := by
    rw [curve_a₁]
    calc
      u * (1 - c) = u - c * u := by ring
      _ = _ := by rw [hc]; dsimp [u]; ring
  have h2 : u ^ 2 * (-c * (c + 1)) = (curve t).a₂ := by
    rw [curve_a₂]
    calc
      u ^ 2 * (-c * (c + 1)) = -(c * u) * (c * u + u) := by ring
      _ = _ := by rw [hc]; dsimp [u]; ring
  have h3 : u ^ 3 * (-c * (c + 1)) = (curve t).a₃ := by
    calc
      u ^ 3 * (-c * (c + 1)) = u * (u ^ 2 * (-c * (c + 1))) := by ring
      _ = _ := by rw [h2, curve_a₂, curve_a₃]; dsimp [u]; ring
  ext
  · simpa [WeierstrassCurve.variableChange_a₁, integralTateChange,
      tateCurve_a₁, h.unit_spec, c, u] using h1
  · simpa [WeierstrassCurve.variableChange_a₂, integralTateChange,
      tateCurve_a₂, h.unit_spec, c, u] using h2
  · simpa [WeierstrassCurve.variableChange_a₃, integralTateChange,
      tateCurve_a₃, h.unit_spec, c, u] using h3
  · simp [WeierstrassCurve.variableChange_a₄, integralTateChange, tateCurve_a₄, curve_a₄]
  · simp [WeierstrassCurve.variableChange_a₆, integralTateChange, tateCurve_a₆, curve_a₆]

/-- Any field fiber recovers the usual Tate parameter. This includes the
fixed residue map and requires no choice of a new prime or complex lift. -/
theorem map_integralTateParameter {K : Type*} [Field K] (f : R →+* K)
    (t : R) (h : IsUnit (9 * (t + 8))) :
    f (integralTateParameter t h) = tateParameter (f t) := by
  rw [tateParameter_eq]
  have hn : 9 * (f t + 8) ≠ 0 := by
    simpa only [map_mul, map_add, map_ofNat] using (h.map f).ne_zero
  apply (eq_div_iff hn).mpr
  have he := congrArg f (integralTateParameter_mul t h)
  simpa only [map_mul, map_add, map_ofNat, map_neg] using he

/-- Six invertible and a good fiber make the Tate denominator invertible. -/
theorem isUnit_tate_denominator (t : R) (h6 : IsUnit (6 : R))
    (hΔ : IsUnit (curve t).Δ) : IsUnit (9 * (t + 8)) := by
  have h3 : IsUnit (3 : R) := by
    have he : (6 : R) = 2 * 3 := by norm_num
    rw [he] at h6
    exact ((Commute.all _ _).isUnit_mul_iff.mp h6).2
  have h9 : IsUnit (9 : R) := by
    have he : (9 : R) = 3 ^ 2 := by norm_num
    rw [he]
    exact h3.pow 2
  exact h9.mul (isUnit_cusp_factors t hΔ).2.1

end SptClassification.LevelSixWeierstrass

namespace SptClassification.LevelSixForm

variable {D : ℤ} {r : ZMod 12} [Fact (D < 0)] (Q : LevelSixForm D r)

/-- The denominator of the actual CM eta fiber is a unit in the common
integral closure. -/
theorem integralEta_isUnit_tate_denominator (hodd : Q.b % 2 = 1)
    (t : CMIntegralValues.Ring)
    (ht : CMIntegralValues.complexEmbedding t = levelSixEtaQuotient Q.cmPoint) :
    IsUnit (9 * (t + 8)) := by
  letI := Q.integralEta_isElliptic hodd t ht
  exact LevelSixWeierstrass.isUnit_tate_denominator t CMIntegralValues.isUnit_six
    WeierstrassCurve.IsElliptic.isUnit

/-- The Tate parameter of an actual integral eta fiber. This does not yet
identify its marked complex curve with the original CM torus. -/
noncomputable def integralEtaTateParameter (hodd : Q.b % 2 = 1)
    (t : CMIntegralValues.Ring)
    (ht : CMIntegralValues.complexEmbedding t = levelSixEtaQuotient Q.cmPoint) :
    CMIntegralValues.Ring :=
  LevelSixWeierstrass.integralTateParameter t
    (Q.integralEta_isUnit_tate_denominator hodd t ht)

/-- Complex and residue fibers use a single integral Tate parameter. -/
theorem map_integralEtaTateParameter (hodd : Q.b % 2 = 1)
    (t : CMIntegralValues.Ring)
    (ht : CMIntegralValues.complexEmbedding t = levelSixEtaQuotient Q.cmPoint)
    {K : Type*} [Field K] (f : CMIntegralValues.Ring →+* K) :
    f (Q.integralEtaTateParameter hodd t ht) =
      LevelSixWeierstrass.tateParameter (f t) :=
  LevelSixWeierstrass.map_integralTateParameter f t _

end SptClassification.LevelSixForm
