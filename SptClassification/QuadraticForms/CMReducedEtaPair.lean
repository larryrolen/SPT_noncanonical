/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.CMIntegralEtaReduction
public import SptClassification.QuadraticForms.LevelSixFamilyCoordinate

/-!
# The reduced marked pair at an actual integral CM eta value

The actual integral value supplies a nonsingular fiber and its point of exact
order six. Its geometric coordinate is the residue of that value. Identifying
this pair with an equivariant specialization of the original CM action remains
separate.
-/

public section

namespace SptClassification.LevelSixForm

variable {D : ℤ} {r : ZMod 12} [Fact (D < 0)] (Q : LevelSixForm D r)
variable (hodd : Q.b % 2 = 1) (t : CMIntegralValues.Ring)
variable (ht : CMIntegralValues.complexEmbedding t = levelSixEtaQuotient Q.cmPoint)
variable {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K]
variable (red : CMIntegralValues.Ring →+* K) (h6 : (6 : K) ≠ 0)

/-- The actual marked fiber at the reduction of an integral CM eta value. -/
noncomputable def reducedEtaPair : LevelSixPair K :=
  letI := Q.integralEta_reduction_isElliptic hodd t ht red h6
  LevelSixWeierstrass.pair (red t) (by
    exact isUnit_iff_ne_zero.mp WeierstrassCurve.IsElliptic.isUnit)

/-- Its geometric coordinate is precisely the chosen residue value. -/
theorem reducedEtaPair_coordinate :
    LevelSixPair.moduliCoordinate h6
      (Q.reducedEtaPair hodd t ht red h6).moduliClass = red t := by
  unfold reducedEtaPair
  exact LevelSixWeierstrass.pair_moduliCoordinate _ h6 _

/-- Equal reduced eta values give the same geometric cyclic-six class.
No CM action on this common pair is asserted here. -/
theorem reducedEtaPair_moduliClass_eq
    {D' : ℤ} {r' : ZMod 12} [Fact (D' < 0)] (Q' : LevelSixForm D' r')
    (hodd' : Q'.b % 2 = 1) (t' : CMIntegralValues.Ring)
    (ht' : CMIntegralValues.complexEmbedding t' = levelSixEtaQuotient Q'.cmPoint)
    (heq : red t = red t') :
    (Q.reducedEtaPair hodd t ht red h6).moduliClass =
      (Q'.reducedEtaPair hodd' t' ht' red h6).moduliClass := by
  apply LevelSixPair.moduliCoordinate_injective h6
  rw [Q.reducedEtaPair_coordinate, Q'.reducedEtaPair_coordinate, heq]

end SptClassification.LevelSixForm
