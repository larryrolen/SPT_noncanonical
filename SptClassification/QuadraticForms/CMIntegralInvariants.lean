/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.CMSingularModuli
public import SptClassification.QuadraticForms.CMIntegralValues
public import SptClassification.QuadraticForms.LevelSixWeierstrass

/-!
# Singular invariants in the common reduction ring

The actual lattice j-invariant belongs to the same integral closure as the
oriented eta values. An identity in the complex fiber therefore descends to
that ring and survives its fixed residue map. In the explicit level-six
family, the finite j-identity excludes all singular fibers away from six.
The identification of the parameter with the eta value, and of the marking
with the original CM subgroup, remain separate mathematical requirements.
-/

public section

namespace SptClassification
namespace LevelSixForm

variable {D : ℤ} {r : ZMod 12} [Fact (D < 0)] (Q : LevelSixForm D r)

/-- The singular modulus is integral over the coefficient ring used for
the class polynomials, by base extension of its integrality over `ℤ`. -/
theorem complexCurve_j_isIntegral_away_six (hodd : Q.b % 2 = 1) :
    letI := Q.complexCurve_isElliptic
    IsIntegral (Localization.Away (6 : ℤ)) Q.complexCurve.j := by
  letI := Q.complexCurve_isElliptic
  exact IsIntegral.map_of_comp_eq (Int.castRingHom (Localization.Away (6 : ℤ)))
    (RingHom.id ℂ) (by ext n; simp) (Q.complexCurve_j_isIntegral hodd)

/-- The actual complex j-value, lifted into the common integral ring. -/
noncomputable def integralInvariant (hodd : Q.b % 2 = 1) : CMIntegralValues.Ring :=
  letI := Q.complexCurve_isElliptic
  ⟨Q.complexCurve.j, Q.complexCurve_j_isIntegral_away_six hodd⟩

theorem complexEmbedding_integralInvariant (hodd : Q.b % 2 = 1) :
    letI := Q.complexCurve_isElliptic
    CMIntegralValues.complexEmbedding (Q.integralInvariant hodd) =
      Q.complexCurve.j := by
  simp only [CMIntegralValues.complexEmbedding_apply, integralInvariant]

/-- A complex invariant identity for an integral parameter holds already
in the common integral ring. No independent integral j-lift is assumed. -/
theorem integralInvariant_relation (hodd : Q.b % 2 = 1)
    (t : CMIntegralValues.Ring)
    (hj : letI := Q.complexCurve_isElliptic
      Q.complexCurve.j *
          (LevelSixWeierstrass.curve (CMIntegralValues.complexEmbedding t)).Δ =
        (LevelSixWeierstrass.curve (CMIntegralValues.complexEmbedding t)).c₄ ^ 3) :
    Q.integralInvariant hodd * (LevelSixWeierstrass.curve t).Δ =
      (LevelSixWeierstrass.curve t).c₄ ^ 3 := by
  apply CMIntegralValues.complexEmbedding_injective
  simpa only [map_mul, map_pow, LevelSixWeierstrass.curve_discriminant,
    LevelSixWeierstrass.curve_c₄, map_add, map_ofNat,
    Q.complexEmbedding_integralInvariant] using hj

/-- The actual integral singular modulus supplies the finite j-value needed
by the algebraic nonsingularity criterion at any residue characteristic
away from six. The sole remaining coordinate hypothesis is stated in `ℂ`. -/
theorem integralParameter_reduction_isElliptic (hodd : Q.b % 2 = 1)
    (t : CMIntegralValues.Ring) {K : Type*} [Field K]
    (red : CMIntegralValues.Ring →+* K) (h6 : (6 : K) ≠ 0)
    (hj : letI := Q.complexCurve_isElliptic
      Q.complexCurve.j *
          (LevelSixWeierstrass.curve (CMIntegralValues.complexEmbedding t)).Δ =
        (LevelSixWeierstrass.curve (CMIntegralValues.complexEmbedding t)).c₄ ^ 3) :
    (LevelSixWeierstrass.curve (red t)).IsElliptic :=
  LevelSixWeierstrass.reduction_isElliptic red t (Q.integralInvariant hodd) h6
    (Q.integralInvariant_relation hodd t hj)

end LevelSixForm
end SptClassification
