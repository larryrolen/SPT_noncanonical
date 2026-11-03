/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.EtaTateReciprocalInvariant

/-!
# Identification of the actual marked family from its analytic coefficients

The only inputs here are holomorphy and cusp limits of the three classical
Weierstrass coefficients. Regularity of the marked coordinate, equality of
invariants, selection of the cusp branch and analytic continuation are proved.
The analytic inputs remain explicit hypotheses, not literature admissions.
-/

public section

namespace SptClassification.ComplexUniformization

open UpperHalfPlane Filter LevelSixWeierstrass

/-- The short coefficient of the normalized lattice, extended off the upper
half-plane through `ofComplex` solely to express complex differentiability. -/
noncomputable def markedShortA (z : ℂ) : ℂ :=
  -(upperHalfPlanePeriods (ofComplex z)).g₂ / 4

/-- The actual x-coordinate of the distinguished lattice point `1/6`. -/
noncomputable def markedShortX (z : ℂ) : ℂ :=
  (upperHalfPlanePeriods (ofComplex z)).weierstrassP (1 / 6)

/-- The actual y-coordinate, with the normalization `y = wp'/2`. -/
noncomputable def markedShortY (z : ℂ) : ℂ :=
  (upperHalfPlanePeriods (ofComplex z)).derivWeierstrassP (1 / 6) / 2

theorem markedShortA_coe (z : UpperHalfPlane) :
    markedShortA z = -(upperHalfPlanePeriods z).g₂ / 4 := by
  simp only [markedShortA, ofComplex_apply]

theorem markedShortX_coe (z : UpperHalfPlane) :
    markedShortX z = (upperHalfPlanePeriods z).weierstrassP (1 / 6) := by
  simp only [markedShortX, ofComplex_apply]

theorem markedShortY_coe (z : UpperHalfPlane) :
    markedShortY z = (upperHalfPlanePeriods z).derivWeierstrassP (1 / 6) / 2 := by
  simp only [markedShortY, ofComplex_apply]

/-- Exact order six rules out every zero of the actual y-coordinate on H. -/
theorem markedShortY_ne_zero (z : UpperHalfPlane) : markedShortY z ≠ 0 := by
  rw [markedShortY_coe]
  exact (upperHalfPlanePair_tateCoordinate_eq z).1

/-- Holomorphy of the three actual coefficients implies holomorphy of the
marked parameter; no additional nonvanishing hypothesis is needed. -/
theorem analyticOnNhd_markedShortParameter
    (ha : AnalyticOnNhd ℂ markedShortA upperHalfPlaneSet)
    (hx : AnalyticOnNhd ℂ markedShortX upperHalfPlaneSet)
    (hy : AnalyticOnNhd ℂ markedShortY upperHalfPlaneSet) :
    AnalyticOnNhd ℂ
      (fun z => shortTateParameter (markedShortA z) (markedShortX z) (markedShortY z))
      upperHalfPlaneSet := by
  intro z hz
  have hy0 : markedShortY z ≠ 0 := markedShortY_ne_zero ⟨z, hz⟩
  have hs : AnalyticAt ℂ (fun w =>
      (3 * markedShortX w ^ 2 + markedShortA w) / (2 * markedShortY w)) z := ((analyticAt_const.mul ((hx z hz).pow 2)).add (ha z hz)).div
    (analyticAt_const.mul (hy z hz)) (mul_ne_zero (by norm_num) hy0)
  simp only [shortTateParameter_eq]
  exact analyticAt_const.sub
    ((hs.mul ((analyticAt_const.mul (hx z hz)).sub (hs.pow 2))).div (hy z hz) hy0)

/-- The actual marked Tate coordinate equals the eta coordinate once the
classical coefficient holomorphy and three normalized cusp limits are supplied.
Neither invariant matching nor the marked identity is an input. -/
theorem upperHalfPlanePair_tateCoordinate_eq_eta_of_analytic_data
    (ha : AnalyticOnNhd ℂ markedShortA upperHalfPlaneSet)
    (hx : AnalyticOnNhd ℂ markedShortX upperHalfPlaneSet)
    (hy : AnalyticOnNhd ℂ markedShortY upperHalfPlaneSet)
    (k r : ℂ) (hk : k ≠ 0) (hr : r ^ 2 = 3)
    (hlimA : Tendsto (fun z : UpperHalfPlane => markedShortA z) atImInfty
      (nhds (-k ^ 4 / 3)))
    (hlimX : Tendsto (fun z : UpperHalfPlane => markedShortX z) atImInfty
      (nhds (11 * k ^ 2 / 3)))
    (hlimY : Tendsto (fun z : UpperHalfPlane => markedShortY z) atImInfty
      (nhds (-4 * r * k ^ 3))) (z : UpperHalfPlane) :
    LevelSixPair.tateCoordinate (by norm_num) (upperHalfPlanePair z) =
      tateParameter (levelSixEtaQuotient z) := by
  have heq : ∀ᶠ w : UpperHalfPlane in atImInfty,
      tateReciprocalInvariant
        (shortTateParameter (markedShortA w) (markedShortX w) (markedShortY w)) =
      tateReciprocalInvariant (tateParameter (levelSixEtaQuotient w)) := by
    exact Filter.Eventually.of_forall fun w => by
      simpa only [markedShortA_coe, markedShortX_coe, markedShortY_coe] using
        shortTateParameter_reciprocalInvariant_eta w
  have h := shortTateParameter_eq_eta_of_cusp_data markedShortA markedShortX markedShortY
    k r hk hr hlimA hlimX hlimY (analyticOnNhd_markedShortParameter ha hx hy)
    analyticOnNhd_tateParameter_eta heq z
  rw [(upperHalfPlanePair_tateCoordinate_eq z).2]
  simpa only [markedShortA_coe, markedShortX_coe, markedShortY_coe] using h

end SptClassification.ComplexUniformization
