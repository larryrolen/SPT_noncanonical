/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.CMRationalAction
public import SptClassification.QuadraticForms.CyclicCMTransport

/-!
# CM orientation after compatible specialization

The complex actions here are the constructed rational endomorphisms, and the
maps on torsion have only the actual cyclic level-six subgroups as domains.
The ring specialization maps, torsion compatibility and common image remain
separate hypotheses. No existence of a common reduced pair is admitted.
-/

public section

namespace SptClassification.LevelSixForm

variable {D : ℤ} {r s : ZMod 12} [Fact (D < 0)] (Q : LevelSixForm D r)

/-- The distinguished generator as a member of its actual cyclic subgroup. -/
noncomputable def levelPoint : Q.curveLevelSix :=
  ⟨Q.curveSixPoint, by
    rw [Q.curveLevelSix_eq]
    exact ⟨1, one_zsmul _⟩⟩

theorem levelPoint_val : (Q.levelPoint : Q.complexCurve.toAffine.Point) =
    Q.curveSixPoint := (rfl)

/-- Restriction of the actual CM map to the cyclic level subgroup. -/
noncomputable def levelGenerator (hodd : Q.b % 2 = 1) :
    Q.curveLevelSix →+ Q.curveLevelSix where
  toFun x := ⟨Q.curveGenerator hodd x, Q.curveGenerator_preserves_levelSix hodd x x.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add (Q.curveGenerator hodd)
    (x : Q.complexCurve.toAffine.Point) (y : Q.complexCurve.toAffine.Point))

/-- The restriction acts by the same scalar at every point of the subgroup. -/
theorem levelGenerator_scalar (hodd : Q.b % 2 = 1) (x : Q.curveLevelSix) :
    Q.levelGenerator hodd x = ((Q.b + 1) / 2 : ℤ) • x := by
  apply Subtype.ext
  exact scalar_action_on_zmultiples (Q.curveGenerator hodd) Q.curveSixPoint
    ((Q.b + 1) / 2) (Q.curveGenerator_sixPoint hodd) x
    (by simpa only [Q.curveLevelSix_eq] using x.property)

/-- Any injective specialization of the cyclic subgroup preserves the order
of its generator. No map on all complex points is needed. -/
theorem specialized_levelPoint_order
    {G : Type*} [AddCommGroup G] (e : Q.curveLevelSix →+ G)
    (he : Function.Injective e) : addOrderOf (e Q.levelPoint) = 6 := by
  have hzero (n : ℕ) : n • e Q.levelPoint = 0 ↔ 6 ∣ n := by
    rw [← map_nsmul, map_eq_zero_iff e he]
    have hsub : n • Q.levelPoint = 0 ↔ n • Q.curveSixPoint = 0 := by
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
    rw [hsub, Q.curveSixPoint_nsmul_eq_zero]
  apply Nat.dvd_antisymm
  · exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr ((hzero 6).mpr (dvd_refl 6))
  · exact (hzero _).mp (addOrderOf_nsmul_eq_zero _)

omit [Fact (D < 0)] in
/-- The integral action scalar reduces modulo six using only the original
orientation modulo twelve. -/
theorem generatorScalar_emod_six (m : ℤ) (hr : r = (m : ZMod 12)) :
    ((Q.b + 1) / 2) % 6 = ((m + 1) / 2) % 6 := by
  have hdiv : 12 ∣ Q.b - m :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (Q.b - m) 12).mp (by
      simpa only [Int.cast_sub] using sub_eq_zero.mpr (Q.b_residue.trans hr))
  obtain ⟨k, hk⟩ := hdiv
  omega

omit [Fact (D < 0)] in
/-- The first two product orientations give the required integral residues. -/
theorem generatorScalar_first_pair (hr : r = 1 ∨ r = 11) :
    ((Q.b + 1) / 2) % 6 = 0 ∨ ((Q.b + 1) / 2) % 6 = 1 := by
  rcases hr with hr | hr
  · exact Or.inr (Q.generatorScalar_emod_six 1 hr)
  · exact Or.inl (Q.generatorScalar_emod_six 11 hr)

omit [Fact (D < 0)] in
/-- The other two product orientations give residues three and four. -/
theorem generatorScalar_second_pair (hr : r = 5 ∨ r = 7) :
    ((Q.b + 1) / 2) % 6 = 3 ∨ ((Q.b + 1) / 2) % 6 = 4 := by
  rcases hr with hr | hr
  · exact Or.inl (Q.generatorScalar_emod_six 5 hr)
  · exact Or.inr (Q.generatorScalar_emod_six 7 hr)

/-- Compatible ring specialization and a common cyclic image preserve the
orientation contradiction. The target is the rational endomorphism ring of
an actual elliptic curve over an algebraically closed field. -/
theorem rational_specializations_not_commute
    (R : LevelSixForm D s) (hQ : Q.b % 2 = 1) (hR : R.b % 2 = 1)
    (n : ℕ) (hn : 4 * (n : ℤ) = 1 - D)
    {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
    (W : WeierstrassCurve F) (hW : W.IsElliptic)
    (σQ : RationalPointMap.endomorphismRing Q.complexCurve →+*
      RationalPointMap.endomorphismRing W)
    (σR : RationalPointMap.endomorphismRing R.complexCurve →+*
      RationalPointMap.endomorphismRing W)
    (eQ : Q.curveLevelSix →+ W.toAffine.Point)
    (eR : R.curveLevelSix →+ W.toAffine.Point)
    (heQ : Function.Injective eQ) (hpair : Set.range eQ = Set.range eR)
    (hequivQ : ∀ x, RationalPointMap.pointAction W (σQ (Q.rationalGenerator hQ)) (eQ x) =
      eQ (Q.levelGenerator hQ x))
    (hequivR : ∀ x, RationalPointMap.pointAction W (σR (R.rationalGenerator hR)) (eR x) =
      eR (R.levelGenerator hR x))
    (hr : r = 1 ∨ r = 11) (hs : s = 5 ∨ s = 7) :
    σQ (Q.rationalGenerator hQ) * σR (R.rationalGenerator hR) ≠
      σR (R.rationalGenerator hR) * σQ (Q.rationalGenerator hQ) := by
  let := RationalPointMap.endomorphismRing_noZeroDivisors W hW
  have ha := congrArg σQ (Q.rationalGenerator_quadratic hQ n hn)
  have hb := congrArg σR (R.rationalGenerator_quadratic hR n hn)
  simp only [map_add, map_sub, map_mul, map_natCast, map_zero] at ha hb
  have hscalarQ : RationalPointMap.pointAction W (σQ (Q.rationalGenerator hQ))
      (eQ Q.levelPoint) = ((Q.b + 1) / 2 : ℤ) • eQ Q.levelPoint := by
    rw [hequivQ, Q.levelGenerator_scalar, map_zsmul]
  have hmem : eQ Q.levelPoint ∈ Set.range eR := by
    rw [← hpair]
    exact ⟨Q.levelPoint, rfl⟩
  obtain ⟨x, hx⟩ := hmem
  have hscalarR : RationalPointMap.pointAction W (σR (R.rationalGenerator hR))
      (eQ Q.levelPoint) = ((R.b + 1) / 2 : ℤ) • eQ Q.levelPoint := by
    rw [← hx, hequivR, R.levelGenerator_scalar, map_zsmul]
  exact oriented_point_actions_not_commute (RationalPointMap.pointAction W)
    _ _ (n : RationalPointMap.endomorphismRing W) (eQ Q.levelPoint)
    (Q.specialized_levelPoint_order eQ heQ) ha hb
    ((Q.b + 1) / 2) ((R.b + 1) / 2) hscalarQ hscalarR
    (Q.generatorScalar_first_pair hr) (R.generatorScalar_second_pair hs)

end SptClassification.LevelSixForm
