/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.MarkedEtaIdentification
public import SptClassification.QuadraticForms.CMShortTateCoordinate
public import SptClassification.QuadraticForms.LevelSixFamilyCoordinate

/-!
# The actual CM pair on the eta model

The coefficient holomorphy and cusp limits identify the marked lattice cubic
with the explicit eta family by a rational equivalence carrying the chosen
six-torsion generator. These analytic inputs remain explicit hypotheses.
Descent and specialization of the rational CM action are separate steps.
-/

public section

namespace SptClassification.LevelSixForm

open ComplexUniformization LevelSixWeierstrass UpperHalfPlane Filter

variable {D : ℤ} {s : ZMod 12} [Fact (D < 0)] (Q : LevelSixForm D s)

/-- The CM period pair is the normalized upper-half-plane period pair. -/
theorem periodPair_eq_upperHalfPlanePeriods :
    Q.periodPair = upperHalfPlanePeriods Q.cmPoint := by
  have hext (L M : PeriodPair) (h₁ : L.ω₁ = M.ω₁) (h₂ : L.ω₂ = M.ω₂) : L = M := by
    cases L
    cases M
    simp_all
  apply hext
  · rw [Q.periodPair_omega_one, upperHalfPlanePeriods_omega_one]
  · rw [Q.periodPair_omega_two, upperHalfPlanePeriods_omega_two]

variable
    (ha : AnalyticOnNhd ℂ markedShortA upperHalfPlaneSet)
    (hx : AnalyticOnNhd ℂ markedShortX upperHalfPlaneSet)
    (hy : AnalyticOnNhd ℂ markedShortY upperHalfPlaneSet)
    (k r : ℂ) (hk : k ≠ 0) (hr : r ^ 2 = 3)
    (hlimA : Tendsto (fun z : UpperHalfPlane => markedShortA z) atImInfty
      (nhds (-k ^ 4 / 3)))
    (hlimX : Tendsto (fun z : UpperHalfPlane => markedShortX z) atImInfty
      (nhds (11 * k ^ 2 / 3)))
    (hlimY : Tendsto (fun z : UpperHalfPlane => markedShortY z) atImInfty
      (nhds (-4 * r * k ^ 3)))

include ha hx hy hk hr hlimA hlimX hlimY

/-- The actual CM marking has the eta Tate parameter, using only coefficient
analysis as input to the proved branch and continuation argument. -/
theorem complexPair_tateCoordinate_eq_eta_of_analytic_data :
    LevelSixPair.tateCoordinate (by norm_num) Q.complexPair =
      tateParameter (levelSixEtaQuotient Q.cmPoint) := by
  rw [Q.complexPair_tateCoordinate_eq.2, Q.periodPair_eq_upperHalfPlanePeriods]
  rw [← (upperHalfPlanePair_tateCoordinate_eq Q.cmPoint).2]
  exact upperHalfPlanePair_tateCoordinate_eq_eta_of_analytic_data
    ha hx hy k r hk hr hlimA hlimX hlimY Q.cmPoint

/-- The marked CM curve is isomorphic to the explicit eta fiber; the
isomorphism class includes the cyclic-six subgroup. -/
theorem complexPair_isomorphic_eta_of_analytic_data :
    Q.complexPair.Isomorphic
      (pair (levelSixEtaQuotient Q.cmPoint) (eta_discriminant_ne_zero Q.cmPoint)) := by
  apply LevelSixPair.isomorphic_of_tateCoordinate_eq (by norm_num)
  rw [pair_tateCoordinate]
  exact Q.complexPair_tateCoordinate_eq_eta_of_analytic_data
    ha hx hy k r hk hr hlimA hlimX hlimY

/-- The equivalence can be chosen to preserve the specific generator, so
conjugating the CM action preserves its eigenvalue on six-torsion. -/
theorem exists_pointed_eta_equiv_of_analytic_data :
    ∃ e : RationalPointMap.CurveEquiv Q.complexPair.curve
      (pair (levelSixEtaQuotient Q.cmPoint)
        (eta_discriminant_ne_zero Q.cmPoint)).curve,
      e.toAddEquiv Q.complexPair.point =
        (pair (levelSixEtaQuotient Q.cmPoint)
          (eta_discriminant_ne_zero Q.cmPoint)).point := by
  exact (LevelSixPair.isomorphic_iff_pointed _ _).mp
    (Q.complexPair_isomorphic_eta_of_analytic_data ha hx hy k r hk hr hlimA hlimX hlimY)

/-- The eta equation carries the entire rational CM action, with its original
quadratic relation, orientation scalar and nonintegrality. The same pointed
equivalence transports all three properties. This is still over the complex
numbers; it does not assert descent or reduction of the endomorphism. -/
theorem exists_eta_CM_action_of_analytic_data (hodd : Q.b % 2 = 1)
    (n : ℕ) (hn : 4 * (n : ℤ) = 1 - D) :
    ∃ a : RationalPointMap.endomorphismRing
        (LevelSixWeierstrass.curve (levelSixEtaQuotient Q.cmPoint)),
      a * a - a + (n : RationalPointMap.endomorphismRing
        (LevelSixWeierstrass.curve (levelSixEtaQuotient Q.cmPoint))) = 0 ∧
      RationalPointMap.pointAction _ a
        (sixPoint (levelSixEtaQuotient Q.cmPoint) (eta_discriminant_ne_zero Q.cmPoint)) =
        ((Q.b + 1) / 2 : ℤ) •
          sixPoint (levelSixEtaQuotient Q.cmPoint) (eta_discriminant_ne_zero Q.cmPoint) ∧
      ∀ m : ℤ, a ≠ m := by
  obtain ⟨e, he⟩ := Q.exists_pointed_eta_equiv_of_analytic_data
    ha hx hy k r hk hr hlimA hlimX hlimY
  let B := pair (levelSixEtaQuotient Q.cmPoint) (eta_discriminant_ne_zero Q.cmPoint)
  have hE : (LevelSixWeierstrass.curve (levelSixEtaQuotient Q.cmPoint)).IsElliptic :=
    B.elliptic
  let e' : RationalPointMap.CurveEquiv Q.complexCurve
      (LevelSixWeierstrass.curve (levelSixEtaQuotient Q.cmPoint)) := e
  have he' : e'.toAddEquiv Q.curveSixPoint = B.point := he
  let f : RationalPointMap.endomorphismRing Q.complexCurve →+*
      RationalPointMap.endomorphismRing
        (LevelSixWeierstrass.curve (levelSixEtaQuotient Q.cmPoint)) :=
    e'.conjugate Q.complexCurve_isElliptic hE
  refine ⟨f (Q.rationalGenerator hodd), ?_, ?_, ?_⟩
  · have h := congrArg f (Q.rationalGenerator_quadratic hodd n hn)
    simpa only [map_add, map_sub, map_mul, map_natCast, map_zero] using h
  · have h := e'.conjugate_action Q.complexCurve_isElliptic hE
      (Q.rationalGenerator hodd) Q.curveSixPoint
    rw [Q.rationalGenerator_sixPoint, map_zsmul] at h
    rw [he'] at h
    exact h
  · intro m hm
    apply Q.rationalGenerator_ne_intCast hodd m
    apply e'.conjugate_injective Q.complexCurve_isElliptic hE
    simpa only [map_intCast, f] using hm

end SptClassification.LevelSixForm
