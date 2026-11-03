/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.LevelSixModuli

/-!
# Pointed representatives of cyclic level-six pairs

The only generators of a cyclic group of order six are a point and its
negative. Negation is a rational elliptic isomorphism, so the geometric
equivalence relation for cyclic subgroups also admits pointed representatives.
This connects the manuscript's cyclic level structure with pointed normal
forms; it asserts neither the normal form nor its eta normalization.
-/

public section

namespace SptClassification

/-- The two generators of an order-six cyclic subgroup. -/
theorem eq_or_eq_neg_of_mem_zmultiples_order_six
    {G : Type*} [AddGroup G] {P Q : G}
    (hP : addOrderOf P = 6) (hQ : addOrderOf Q = 6)
    (hmem : Q ∈ AddSubgroup.zmultiples P) : Q = P ∨ Q = -P := by
  obtain ⟨k, rfl⟩ := hmem
  have period (n : ℤ) (hn : (n * k) % 6 = 0) : n % 6 = 0 := by
    have h : n • (k • P) = (0 : ℤ) • (k • P) := by
      rw [smul_smul, zero_zsmul]
      have h' : (n * k) • P = (0 : ℤ) • P := by
        apply zsmul_eq_zsmul_iff_modEq.mpr
        rw [hP]
        change (n * k) % 6 = 0 % 6
        exact hn
      simpa only [zero_zsmul] using h'
    have h' := zsmul_eq_zsmul_iff_modEq.mp h
    rw [hQ] at h'
    exact h'
  have hk : k % 6 = 1 ∨ k % 6 = 5 := by
    have h2 := period 2
    have h3 := period 3
    have h1 := period 1
    omega
  rcases hk with hk | hk
  · left
    conv_rhs => rw [← one_zsmul P]
    apply zsmul_eq_zsmul_iff_modEq.mpr
    rw [hP]
    exact hk
  · right
    conv_rhs => rw [← neg_one_zsmul P]
    apply zsmul_eq_zsmul_iff_modEq.mpr
    rw [hP]
    exact hk

namespace RationalPointMap.CurveEquiv

variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]

/-- Negation as a rational origin-preserving isomorphism of an elliptic curve. -/
noncomputable def neg (W : WeierstrassCurve F) (hW : W.IsElliptic) :
    CurveEquiv W W where
  toAddEquiv := AddEquiv.neg _
  rational := by
    have h : (AddEquiv.neg W.toAffine.Point).toAddMonoidHom =
        pointAction W (-1) := by
      rw [map_neg, map_one]
      ext x
      rfl
    rw [h]
    exact endomorphismRing_isRational W hW (-1)
  inverse_rational := by
    have h : (AddEquiv.neg W.toAffine.Point).symm.toAddMonoidHom =
        pointAction W (-1) := by
      rw [map_neg, map_one]
      ext x
      rfl
    rw [h]
    exact endomorphismRing_isRational W hW (-1)

end RationalPointMap.CurveEquiv

namespace LevelSixPair

variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]

/-- A rational equivalence of cyclic-six pairs can always be chosen to carry
the selected generator exactly. This is particular to level six. -/
theorem isomorphic_iff_pointed (A B : LevelSixPair F) :
    A.Isomorphic B ↔ ∃ e : RationalPointMap.CurveEquiv A.curve B.curve,
      e.toAddEquiv A.point = B.point := by
  rw [isomorphic_iff]
  constructor
  · rintro ⟨e, he⟩
    have hmem : e.toAddEquiv A.point ∈ AddSubgroup.zmultiples B.point := by
      rw [← B.subgroup_eq]
      change e.toAddEquiv A.point ∈ (B.subgroup : Set B.curve.toAffine.Point)
      rw [← he]
      refine ⟨A.point, ?_, rfl⟩
      rw [A.subgroup_eq]
      exact ⟨1, one_zsmul _⟩
    have hord : addOrderOf (e.toAddEquiv A.point) = 6 := by
      rw [e.toAddEquiv.addOrderOf_eq, A.order_six]
    rcases eq_or_eq_neg_of_mem_zmultiples_order_six B.order_six hord hmem with h | h
    · exact ⟨e, h⟩
    · refine ⟨e.trans (RationalPointMap.CurveEquiv.neg B.curve B.elliptic)
        A.elliptic B.elliptic B.elliptic, ?_⟩
      rw [RationalPointMap.CurveEquiv.trans_apply]
      change -e.toAddEquiv A.point = B.point
      rw [h, neg_neg]
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    rw [A.subgroup_eq, B.subgroup_eq]
    ext y
    constructor
    · rintro ⟨x, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, by rw [map_zsmul, he]⟩
    · rintro ⟨n, rfl⟩
      exact ⟨n • A.point, ⟨n, rfl⟩, by rw [map_zsmul, he]⟩

/-- Equality of geometric cyclic-six classes is also equality up to a
rational pointed isomorphism. -/
theorem moduliClass_eq_iff_pointed (A B : LevelSixPair F) :
    A.moduliClass = B.moduliClass ↔
      ∃ e : RationalPointMap.CurveEquiv A.curve B.curve,
        e.toAddEquiv A.point = B.point := by
  rw [moduliClass_eq_iff, isomorphic_iff_pointed]

end LevelSixPair
end SptClassification
