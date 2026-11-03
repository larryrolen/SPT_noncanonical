/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.CMIntegralInvariants
public import SptClassification.QuadraticForms.LevelSixEtaInvariant

/-!
# Nonsingular reduction at the actual integral eta value

The covering identity removes the independent complex invariant hypothesis
from the integral reduction criterion. The result applies at every prime
away from six. It does not yet specialize the original marked CM action.
-/

public section

namespace SptClassification.LevelSixForm

variable {D : ℤ} {r : ZMod 12} [Fact (D < 0)] (Q : LevelSixForm D r)

/-- The actual eta parameter and singular modulus obey the invariant relation
in their common integral closure. -/
theorem integralEta_invariant_relation (hodd : Q.b % 2 = 1)
    (t : CMIntegralValues.Ring)
    (ht : CMIntegralValues.complexEmbedding t = levelSixEtaQuotient Q.cmPoint) :
    Q.integralInvariant hodd * (LevelSixWeierstrass.curve t).Δ =
      (LevelSixWeierstrass.curve t).c₄ ^ 3 := by
  apply Q.integralInvariant_relation hodd t
  rw [ht]
  exact Q.complexCurve_eta_invariant_relation

/-- Every reduction of the actual integral eta value away from six defines
a nonsingular explicit level-six curve, for either CM splitting type. -/
theorem integralEta_reduction_isElliptic (hodd : Q.b % 2 = 1)
    (t : CMIntegralValues.Ring)
    (ht : CMIntegralValues.complexEmbedding t = levelSixEtaQuotient Q.cmPoint)
    {K : Type*} [Field K] (red : CMIntegralValues.Ring →+* K) (h6 : (6 : K) ≠ 0) :
    (LevelSixWeierstrass.curve (red t)).IsElliptic :=
  LevelSixWeierstrass.reduction_isElliptic red t (Q.integralInvariant hodd) h6
    (Q.integralEta_invariant_relation hodd t ht)

end SptClassification.LevelSixForm
