/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.CMIntegralEtaReduction
public import SptClassification.QuadraticForms.LevelSixIntegralModel

/-!
# The good integral model at an actual CM eta value

The explicit family is elliptic over the common integral closure of
`ℤ[1/6]` in `ℂ`. This constructs its good model, but does not identify its
marked complex fiber with the original CM torus or specialize the CM action.
-/

public section

namespace SptClassification

namespace CMIntegralValues

/-- Six remains invertible in the common integral closure. -/
theorem isUnit_six : IsUnit (6 : Ring) := by
  have h : IsUnit (6 : Localization.Away (6 : ℤ)) := by
    simpa using IsLocalization.map_units (Localization.Away (6 : ℤ))
      (⟨6, ⟨1, by simp⟩⟩ : Submonoid.powers (6 : ℤ))
  have h' := h.map (algebraMap (Localization.Away (6 : ℤ)) Ring)
  simpa only [map_ofNat] using h'

end CMIntegralValues

namespace LevelSixForm

variable {D : ℤ} {r : ZMod 12} [Fact (D < 0)] (Q : LevelSixForm D r)

/-- The actual integral eta value defines a good model over the entire common
integral ring, uniformly for ordinary and supersingular residue primes. -/
theorem integralEta_isElliptic (hodd : Q.b % 2 = 1)
    (t : CMIntegralValues.Ring)
    (ht : CMIntegralValues.complexEmbedding t = levelSixEtaQuotient Q.cmPoint) :
    (LevelSixWeierstrass.curve t).IsElliptic :=
  LevelSixWeierstrass.integral_isElliptic_of_j_relation t (Q.integralInvariant hodd)
    CMIntegralValues.isUnit_six (Q.integralEta_invariant_relation hodd t ht)

/-- The cusp factors of an actual integral CM eta value are invertible. -/
theorem integralEta_isUnit_cusp_factors (hodd : Q.b % 2 = 1)
    (t : CMIntegralValues.Ring)
    (ht : CMIntegralValues.complexEmbedding t = levelSixEtaQuotient Q.cmPoint) :
    IsUnit t ∧ IsUnit (t + 8) ∧ IsUnit (t + 9) := by
  letI := Q.integralEta_isElliptic hodd t ht
  exact LevelSixWeierstrass.isUnit_cusp_factors t WeierstrassCurve.IsElliptic.isUnit

end LevelSixForm
end SptClassification
