/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.LevelSixTateModel

/-!
# An injective coordinate on geometric cyclic-six classes

Tate normalization and pointed uniqueness define a coordinate on actual
elliptic curves with cyclic-six structure. The fractional linear change gives
the integral-family normalization. Its identification with the analytic eta
quotient, and compatibility with reduction, are separate statements.
-/

public section

namespace SptClassification.LevelSixPair

open LevelSixWeierstrass

variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]

/-- The uniquely determined parameter of a marked Tate model. -/
noncomputable def tateCoordinate (h6 : (6 : F) ≠ 0) (A : LevelSixPair F) : F :=
  (A.exists_tate_model h6).choose

/-- The chosen parameter comes with an actual pointed rational equivalence. -/
theorem tateCoordinate_spec (h6 : (6 : F) ≠ 0) (A : LevelSixPair F) :
    ∃ (_ : (tateCurve (tateCoordinate h6 A)).Δ ≠ 0)
      (hO : (tateCurve (tateCoordinate h6 A)).toAffine.Nonsingular 0 0)
      (e : RationalPointMap.CurveEquiv A.curve (tateCurve (tateCoordinate h6 A))),
      e.toAddEquiv A.point = .some 0 0 hO :=
  (A.exists_tate_model h6).choose_spec

/-- Pointed normalizations of isomorphic cyclic-six pairs have equal parameters. -/
theorem tateCoordinate_eq_of_isomorphic (h6 : (6 : F) ≠ 0)
    (A B : LevelSixPair F) (h : A.Isomorphic B) :
    tateCoordinate h6 A = tateCoordinate h6 B := by
  obtain ⟨e, he⟩ := (isomorphic_iff_pointed A B).mp h
  obtain ⟨hc, hO, f, hf⟩ := tateCoordinate_spec h6 A
  obtain ⟨hd, hO', g, hg⟩ := tateCoordinate_spec h6 B
  have hEc : (tateCurve (tateCoordinate h6 A)).IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr hc⟩
  have hEd : (tateCurve (tateCoordinate h6 B)).IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr hd⟩
  let k := (f.symm.trans e hEc A.elliptic B.elliptic).trans g hEc B.elliptic hEd
  apply tateParameter_eq_of_pointed_equiv _ _ hc hd hO hO' k
  have hf' : f.toAddEquiv.symm (.some 0 0 hO) = A.point :=
    f.toAddEquiv.symm_apply_eq.mpr hf.symm
  simp only [k, RationalPointMap.CurveEquiv.trans_apply,
    RationalPointMap.CurveEquiv.symm_toAddEquiv, hf', he, hg]

/-- Equal Tate parameters yield an actual pointed equivalence of representatives. -/
theorem isomorphic_of_tateCoordinate_eq (h6 : (6 : F) ≠ 0)
    (A B : LevelSixPair F) (h : tateCoordinate h6 A = tateCoordinate h6 B) :
    A.Isomorphic B := by
  have hspec := tateCoordinate_spec h6 A
  rw [h] at hspec
  obtain ⟨hc, hO, f, hf⟩ := hspec
  obtain ⟨hd, hO', g, hg⟩ := tateCoordinate_spec h6 B
  have hE : (tateCurve (tateCoordinate h6 B)).IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr hd⟩
  apply (isomorphic_iff_pointed A B).mpr
  refine ⟨f.trans g.symm A.elliptic hE B.elliptic, ?_⟩
  rw [RationalPointMap.CurveEquiv.trans_apply, hf,
    RationalPointMap.CurveEquiv.symm_toAddEquiv]
  apply g.toAddEquiv.injective
  simpa only [g.toAddEquiv.apply_symm_apply] using hg.symm

/-- The Tate parameter is independent of the representative and generator. -/
noncomputable def moduliTateCoordinate (h6 : (6 : F) ≠ 0) : Moduli F → F :=
  Moduli.lift (tateCoordinate h6) (tateCoordinate_eq_of_isomorphic h6)

theorem moduliTateCoordinate_mk (h6 : (6 : F) ≠ 0) (A : LevelSixPair F) :
    moduliTateCoordinate h6 A.moduliClass = tateCoordinate h6 A :=
  Moduli.lift_mk _ _ A

/-- The Tate coordinate separates geometric cyclic-six classes. -/
theorem moduliTateCoordinate_injective (h6 : (6 : F) ≠ 0) :
    Function.Injective (moduliTateCoordinate h6) := by
  intro a b
  refine Moduli.inductionOn₂ (P := fun a b =>
    moduliTateCoordinate h6 a = moduliTateCoordinate h6 b → a = b) a b ?_
  intro A B h
  apply (moduliClass_eq_iff A B).mpr
  exact isomorphic_of_tateCoordinate_eq h6 A B
    ((moduliTateCoordinate_mk h6 A).symm.trans (h.trans (moduliTateCoordinate_mk h6 B)))

/-- Coordinate with the normalization of the integral level-six family. -/
noncomputable def moduliCoordinate (h6 : (6 : F) ≠ 0) (a : Moduli F) : F :=
  integralParameter (moduliTateCoordinate h6 a)

theorem moduliCoordinate_eq (h6 : (6 : F) ≠ 0) (a : Moduli F) :
    moduliCoordinate h6 a = integralParameter (moduliTateCoordinate h6 a) := (rfl)

/-- The integral normalization recovers the Tate coordinate on every class. -/
theorem tateParameter_moduliCoordinate (h6 : (6 : F) ≠ 0) (a : Moduli F) :
    tateParameter (moduliCoordinate h6 a) = moduliTateCoordinate h6 a := by
  refine Moduli.inductionOn (P := fun a =>
    tateParameter (moduliCoordinate h6 a) = moduliTateCoordinate h6 a) a ?_
  intro A
  obtain ⟨hc, _⟩ := tateCoordinate_spec h6 A
  change tateParameter (integralParameter (moduliTateCoordinate h6 A.moduliClass)) = _
  rw [moduliTateCoordinate_mk]
  exact (integralParameter_regular _ h6 hc).2

/-- An injective coordinate on actual marked geometric pairs, in every
characteristic away from two and three, including ordinary fibers. -/
theorem moduliCoordinate_injective (h6 : (6 : F) ≠ 0) :
    Function.Injective (moduliCoordinate h6) := by
  intro a b h
  apply moduliTateCoordinate_injective h6
  rw [← tateParameter_moduliCoordinate h6 a, ← tateParameter_moduliCoordinate h6 b, h]

/-- Recover the parameter from any specified pointed Tate model. -/
theorem tateCoordinate_eq_of_model (h6 : (6 : F) ≠ 0) (A : LevelSixPair F)
    (c : F) (hc : (tateCurve c).Δ ≠ 0)
    (hO : (tateCurve c).toAffine.Nonsingular 0 0)
    (e : RationalPointMap.CurveEquiv A.curve (tateCurve c))
    (he : e.toAddEquiv A.point = .some 0 0 hO) :
    tateCoordinate h6 A = c := by
  obtain ⟨hd, hO', f, hf⟩ := tateCoordinate_spec h6 A
  have hEd : (tateCurve (tateCoordinate h6 A)).IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr hd⟩
  have hEc : (tateCurve c).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hc⟩
  apply tateParameter_eq_of_pointed_equiv _ _ hd hc hO' hO
    (f.symm.trans e hEd A.elliptic hEc)
  have hf' : f.toAddEquiv.symm (.some 0 0 hO') = A.point :=
    f.toAddEquiv.symm_apply_eq.mpr hf.symm
  simp only [RationalPointMap.CurveEquiv.trans_apply,
    RationalPointMap.CurveEquiv.symm_toAddEquiv, hf', he]

end SptClassification.LevelSixPair
