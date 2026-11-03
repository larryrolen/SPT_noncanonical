/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.LevelSixTateSections
public import SptClassification.QuadraticForms.LevelSixFamilyCoordinate

/-!
# Realization of sections on marked level-six curves

The existing pointed Tate normal form gives an actual coordinate change from
the integral family to any marked elliptic curve. Applying it to a marked
Tate curve constructs the framed expansion used by the Hasse section model.
A choice of cyclic-six structure is retained; no particular cusp or analytic
eta expansion is silently selected.
-/

public noncomputable section

namespace SptClassification.LevelSixSectionRealization

open LevelSixWeierstrass LevelSixModularSections LevelSixHasseGeometry
  LevelSixTateSections WeierstrassHasse

variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]

/-- Every actual cyclic-six pair is represented by the integral family with
its own moduli coordinate, and an admissible change of invariant frame. -/
theorem exists_framed_model (A : LevelSixPair F) (h6 : (6 : F) ≠ 0) :
    ∃ (t : F) (C : WeierstrassCurve.VariableChange F),
      t = LevelSixPair.moduliCoordinate h6 A.moduliClass ∧
      IsInterior t ∧ C • curve t = A.curve := by
  obtain ⟨t, hΔ, e, he⟩ := exists_integral_model A h6
  have ht : IsInterior t := by
    have h := (discriminant_eq_zero_iff t h6).not.mp hΔ
    simpa [isInterior_iff, not_or] using h
  have hEt : (curve t).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  obtain ⟨C, hC, _⟩ := RationalPointMap.exists_variableChange_of_curveEquiv
    A.curve (curve t) A.elliptic hEt e
  have hpair : A.Isomorphic (pair t hΔ) :=
    (LevelSixPair.isomorphic_iff_pointed A (pair t hΔ)).mpr ⟨e, he⟩
  have hclass := (LevelSixPair.moduliClass_eq_iff A (pair t hΔ)).mpr hpair
  refine ⟨t, C, ?_, ht, hC⟩
  rw [hclass, pair_moduliCoordinate t h6 hΔ]

/-- The Hasse coefficient of any cyclic-six pair is evaluation of the same
homogeneous section, in its actual invariant differential frame. -/
theorem exists_framed_hasse_evaluation (p : ℕ) [Fact p.Prime] [CharP F p]
    (hp : 3 < p) (h6 : (6 : F) ≠ 0) (A : LevelSixPair F) :
    ∃ w : F, w ≠ 0 ∧
      framedEval (RingHom.id F) (LevelSixPair.moduliCoordinate h6 A.moduliClass) w
        (hasseSection p) = hasse p A.curve := by
  obtain ⟨t, C, ht, _, hC⟩ := exists_framed_model A h6
  refine ⟨↑C.u⁻¹, Units.ne_zero _, ?_⟩
  rw [← ht, framedEval_hasseSection, mul_comm,
    ← hasse_variableChange_literature p hp, hC]

/-- A marked Tate curve gives an actual realization of the level-six section
ring. This constructs the curve/frame comparison; it assumes neither a Hasse
value nor a Fourier identity for an unknown section. The map `base` and the
cyclic-six marking specify the chosen expansion. -/
theorem exists_tateRealization_of_marked
    {K : Type*} [Field K] (base : PowerSeries K →+* F)
    (A : LevelSixPair F) (h6 : (6 : F) ≠ 0)
    (hA : A.curve = (LevelSixTateSections.tateCurve K).map base) :
    ∃ T : TateRealization (K := K) (S := F),
      T.base = base ∧ T.parameter = LevelSixPair.moduliCoordinate h6 A.moduliClass := by
  obtain ⟨t, C, ht, _, hC⟩ := exists_framed_model A h6
  exact ⟨⟨base, t, C, hC.trans hA⟩, rfl, ht⟩

/-- The realization constructed from a marked Tate curve gives the normalized
Hasse expansion in the same graded section model. -/
theorem exists_normalized_tate_expansion_of_marked
    {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] [CharP F p]
    (hp : 3 < p) (base : PowerSeries K →+* F)
    (A : LevelSixPair F) (h6 : (6 : F) ≠ 0)
    (hA : A.curve = (LevelSixTateSections.tateCurve K).map base) :
    ∃ T : TateRealization (K := K) (S := F),
      T.base = base ∧ T.parameter = LevelSixPair.moduliCoordinate h6 A.moduliClass ∧
      T.expansion (hasseSection p) = 1 := by
  obtain ⟨T, hbase, ht⟩ := exists_tateRealization_of_marked base A h6 hA
  exact ⟨T, hbase, ht, T.expansion_hasse p hp⟩

end SptClassification.LevelSixSectionRealization
