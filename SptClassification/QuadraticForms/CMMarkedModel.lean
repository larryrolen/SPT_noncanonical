/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.CMAlgebraicModel
public import SptClassification.QuadraticForms.CMNonintegerAction
public import SptClassification.QuadraticForms.LevelSixPointedIsomorphism
public import SptClassification.QuadraticForms.VariableChangeIsomorphism

/-!
# Transport of the marked CM curve to its prescribed-j model

The model has coefficients in the actual subfield `ℚ(j)`. We transport the
original point and rational CM action to its complex base change through the
same rational isomorphism. All order, orientation and quadratic identities
are preserved. Algebraicity of the transported point and endomorphism, and
good-reduction specialization, remain separate from this construction.
-/

public section

namespace SptClassification

namespace WeierstrassDescent

/-- The complex base change of the prescribed-j model. -/
@[expose] noncomputable def complexModel (E : WeierstrassCurve ℂ) [E.IsElliptic] :
    WeierstrassCurve ℂ := (model E).map (invariantField E).subtype

instance complexModel_isElliptic (E : WeierstrassCurve ℂ) [E.IsElliptic] :
    (complexModel E).IsElliptic := by
  unfold complexModel
  infer_instance

/-- The admissible coordinate change yields a rational equivalence of the
actual complex point groups. Its existence uses the named coordinate-change
literature interface, in addition to mathlib's equal-j classification. -/
theorem exists_modelEquiv (E : WeierstrassCurve ℂ) [E.IsElliptic] :
    Nonempty (RationalPointMap.CurveEquiv E (complexModel E)) := by
  obtain ⟨C, hC⟩ := model_variableChange E
  obtain ⟨e, _⟩ := RationalPointMap.exists_curveEquiv_of_variableChange
    E (complexModel E) inferInstance C hC
  exact ⟨e⟩

/-- A fixed rational identification with the complex model. -/
noncomputable def modelEquiv (E : WeierstrassCurve ℂ) [E.IsElliptic] :
    RationalPointMap.CurveEquiv E (complexModel E) :=
  Classical.choice (exists_modelEquiv E)

end WeierstrassDescent

namespace LevelSixForm

variable {D : ℤ} {r : ZMod 12} [Fact (D < 0)] (Q : LevelSixForm D r)

/-- The prescribed-j model of the lattice cubic, after complex base change. -/
@[expose] noncomputable def modelCurve : WeierstrassCurve ℂ :=
  letI := Q.complexCurve_isElliptic
  WeierstrassDescent.complexModel Q.complexCurve

theorem modelCurve_isElliptic : Q.modelCurve.IsElliptic := by
  letI := Q.complexCurve_isElliptic
  unfold modelCurve
  infer_instance

/-- One rational isomorphism transports both the marking and CM action. -/
noncomputable def modelCurveEquiv :
    RationalPointMap.CurveEquiv Q.complexCurve Q.modelCurve :=
  letI := Q.complexCurve_isElliptic
  WeierstrassDescent.modelEquiv Q.complexCurve

/-- The transported complex point, not yet a point over a number field. -/
noncomputable def modelSixPoint : Q.modelCurve.toAffine.Point :=
  Q.modelCurveEquiv.toAddEquiv Q.curveSixPoint

theorem modelSixPoint_nsmul_eq_zero (n : ℕ) :
    n • Q.modelSixPoint = 0 ↔ 6 ∣ n := by
  unfold modelSixPoint
  rw [← map_nsmul, ← map_zero Q.modelCurveEquiv.toAddEquiv,
    Q.modelCurveEquiv.toAddEquiv.injective.eq_iff]
  exact Q.curveSixPoint_nsmul_eq_zero n

theorem modelSixPoint_order : addOrderOf Q.modelSixPoint = 6 := by
  apply Nat.dvd_antisymm
  · exact addOrderOf_dvd_of_nsmul_eq_zero
      ((Q.modelSixPoint_nsmul_eq_zero 6).mpr (dvd_refl 6))
  · exact (Q.modelSixPoint_nsmul_eq_zero _).mp (addOrderOf_nsmul_eq_zero _)

/-- The distinguished point on the original lattice cubic has order six. -/
theorem curveSixPoint_order : addOrderOf Q.curveSixPoint = 6 := by
  have h := Q.modelSixPoint_order
  unfold modelSixPoint at h
  rwa [Q.modelCurveEquiv.toAddEquiv.addOrderOf_eq] at h

/-- The original complex cyclic-six pair, with its specified generator.
The structure is exposed so its dependent point type is the lattice cubic. -/
@[expose] noncomputable def complexPair : LevelSixPair ℂ :=
  ⟨Q.complexCurve, Q.complexCurve_isElliptic, Q.curveSixPoint, Q.curveSixPoint_order⟩

theorem complexPair_curve : Q.complexPair.curve = Q.complexCurve := (rfl)

theorem complexPair_point : Q.complexPair.point = Q.curveSixPoint := (rfl)

/-- The actual geometric marked pair on the prescribed-j equation. -/
noncomputable def modelPair : LevelSixPair ℂ :=
  ⟨Q.modelCurve, Q.modelCurve_isElliptic, Q.modelSixPoint, Q.modelSixPoint_order⟩

/-- The change of equation preserves the actual cyclic-six moduli class,
not only the unmarked j-invariant. -/
theorem complexPair_moduliClass_eq_modelPair :
    Q.complexPair.moduliClass = Q.modelPair.moduliClass := by
  apply (LevelSixPair.moduliClass_eq_iff_pointed _ _).mpr
  exact ⟨Q.modelCurveEquiv, rfl⟩

/-- A CM generator transported as an entire rational endomorphism. -/
noncomputable def modelGenerator (hodd : Q.b % 2 = 1) :
    RationalPointMap.endomorphismRing Q.modelCurve :=
  Q.modelCurveEquiv.conjugate Q.complexCurve_isElliptic Q.modelCurve_isElliptic
    (Q.rationalGenerator hodd)

/-- The chosen isomorphism intertwines the two CM actions everywhere. -/
theorem modelGenerator_action (hodd : Q.b % 2 = 1)
    (x : Q.complexCurve.toAffine.Point) :
    RationalPointMap.pointAction Q.modelCurve (Q.modelGenerator hodd)
        (Q.modelCurveEquiv.toAddEquiv x) =
      Q.modelCurveEquiv.toAddEquiv
        (RationalPointMap.pointAction Q.complexCurve (Q.rationalGenerator hodd) x) := by
  exact Q.modelCurveEquiv.conjugate_action
    Q.complexCurve_isElliptic Q.modelCurve_isElliptic (Q.rationalGenerator hodd) x

/-- The orientation scalar survives the change of equation. -/
theorem modelGenerator_sixPoint (hodd : Q.b % 2 = 1) :
    RationalPointMap.pointAction Q.modelCurve (Q.modelGenerator hodd) Q.modelSixPoint =
      ((Q.b + 1) / 2 : ℤ) • Q.modelSixPoint := by
  unfold modelSixPoint
  rw [Q.modelGenerator_action, Q.rationalGenerator_sixPoint, map_zsmul]

theorem modelGenerator_quadratic (hodd : Q.b % 2 = 1) (n : ℕ)
    (hn : 4 * (n : ℤ) = 1 - D) :
    Q.modelGenerator hodd * Q.modelGenerator hodd - Q.modelGenerator hodd +
      (n : RationalPointMap.endomorphismRing Q.modelCurve) = 0 := by
  have h := congrArg
    (Q.modelCurveEquiv.conjugate Q.complexCurve_isElliptic Q.modelCurve_isElliptic)
    (Q.rationalGenerator_quadratic hodd n hn)
  simpa only [map_add, map_sub, map_mul, map_natCast, map_zero, modelGenerator] using h

/-- The transported action still supplies genuine complex multiplication. -/
theorem modelGenerator_ne_intCast (hodd : Q.b % 2 = 1) (m : ℤ) :
    Q.modelGenerator hodd ≠ m := by
  intro h
  apply Q.rationalGenerator_ne_intCast hodd m
  apply Q.modelCurveEquiv.conjugate_injective
    Q.complexCurve_isElliptic Q.modelCurve_isElliptic
  simpa only [map_intCast, modelGenerator] using h

end LevelSixForm
end SptClassification
