/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.CMOrdinaryReduction
public import SptClassification.QuadraticForms.SupersingularKernelBound

/-!
# Numerical separation of specialized CM pairs

The degree in the supersingular estimate is recovered from the specialized
quadratic relation. No degree-preservation hypothesis on specialization is
needed. Existence of compatible marked specializations is a separate input.
-/

public section

namespace SptClassification.LevelSixForm

variable {D : ℤ} {r s : ZMod 12} [Fact (D < 0)] (Q : LevelSixForm D r)

/-- Incompatible orientations force the supersingular bound on the actual
geometric kernels, including when the prime is split in the CM field. -/
theorem kernel_bound_of_rational_specializations
    (R : LevelSixForm D s) (hQ : Q.b % 2 = 1) (hR : R.b % 2 = 1)
    (n : ℕ) (hn : 4 * (n : ℤ) = 1 - D)
    {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
    (p : ℕ) [Fact p.Prime] [CharP F p] (hp : 3 < p)
    (hnpos : 0 < n) (hpn : ¬p ∣ n)
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
    6 * p ≤ 4 * n * n := by
  let f := σQ (Q.rationalGenerator hQ)
  let g := σR (R.rationalGenerator hR)
  have hf : f * f - f + (n : RationalPointMap.endomorphismRing W) = 0 := by
    simpa only [map_add, map_sub, map_mul, map_natCast, map_zero] using
      congrArg σQ (Q.rationalGenerator_quadratic hQ n hn)
  have hg : g * g - g + (n : RationalPointMap.endomorphismRing W) = 0 := by
    simpa only [map_add, map_sub, map_mul, map_natCast, map_zero] using
      congrArg σR (R.rationalGenerator_quadratic hR n hn)
  have hne := Q.rational_specializations_not_commute R hQ hR n hn W hW
    σQ σR eQ eR heQ hpair hequivQ hequivR hr hs
  have hss := RationalPointMap.prime_torsion_eq_zero_of_not_commute p W hW f g hne
  have hscalarQ : RationalPointMap.pointAction W f (eQ Q.levelPoint) =
      ((Q.b + 1) / 2 : ℤ) • eQ Q.levelPoint := by
    rw [hequivQ, Q.levelGenerator_scalar, map_zsmul]
  have hmem : eQ Q.levelPoint ∈ Set.range eR := by
    rw [← hpair]
    exact ⟨Q.levelPoint, rfl⟩
  obtain ⟨x, hx⟩ := hmem
  have hscalarR : RationalPointMap.pointAction W g (eQ Q.levelPoint) =
      ((R.b + 1) / 2 : ℤ) • eQ Q.levelPoint := by
    rw [← hx, hequivR, R.levelGenerator_scalar, map_zsmul]
  have hpres {a : RationalPointMap.endomorphismRing W} {m : ℤ}
      (ha : RationalPointMap.pointAction W a (eQ Q.levelPoint) =
        m • eQ Q.levelPoint) :
      ∀ y ∈ AddSubgroup.zmultiples (eQ Q.levelPoint),
        RationalPointMap.pointAction W a y ∈ AddSubgroup.zmultiples (eQ Q.levelPoint) := by
    rintro y ⟨k, rfl⟩
    rw [map_zsmul, ha]
    exact ⟨k * m, mul_zsmul _ _ _⟩
  have hbound := RationalPointMap.supersingular_kernel_bound p hp W hW hss
    (eQ Q.levelPoint) (Q.specialized_levelPoint_order eQ heQ) f g
    (RationalPointMap.hasPrimeToCharFactor_of_quadratic p W f n hnpos hpn hf)
    (RationalPointMap.hasPrimeToCharFactor_of_quadratic p W g n hnpos hpn hg)
    (hpres hscalarQ) (hpres hscalarR) hne
  rw [RationalPointMap.kernelCard_eq_of_quadratic p W hW f n hnpos hpn hf,
    RationalPointMap.kernelCard_eq_of_quadratic p W hW g n hnpos hpn hg] at hbound
  exact hbound

/-- The manuscript strict bound rules out compatible CM actions on isomorphic
marked reductions. The original discriminant and orientations are retained;
this does not assert that an eta common root constructs these reductions. -/
theorem not_rational_pair_specializations_of_bound
    {D : ℤ} {r s : ZMod 12} [Fact (D < 0)]
    (Q : LevelSixForm D r) (R : LevelSixForm D s)
    (hQ : Q.b % 2 = 1) (hR : R.b % 2 = 1)
    (n : ℕ) (hn : 4 * (n : ℤ) = 1 - D)
    {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
    (p : ℕ) [Fact p.Prime] [CharP F p] (hp : 3 < p)
    (hbound : (1 - D) ^ 2 < 24 * (p : ℤ))
    (W₁ W₂ : WeierstrassCurve F) (hW₁ : W₁.IsElliptic) (hW₂ : W₂.IsElliptic)
    (σQ : RationalPointMap.endomorphismRing Q.complexCurve →+*
      RationalPointMap.endomorphismRing W₁)
    (σR : RationalPointMap.endomorphismRing R.complexCurve →+*
      RationalPointMap.endomorphismRing W₂)
    (eQ : Q.curveLevelSix →+ W₁.toAffine.Point)
    (eR : R.curveLevelSix →+ W₂.toAffine.Point)
    (heQ : Function.Injective eQ)
    (φ : RationalPointMap.CurveEquiv W₂ W₁)
    (hpair : Set.range eQ = φ.toAddEquiv '' Set.range eR)
    (hequivQ : ∀ x, RationalPointMap.pointAction W₁ (σQ (Q.rationalGenerator hQ))
      (eQ x) = eQ (Q.levelGenerator hQ x))
    (hequivR : ∀ x, RationalPointMap.pointAction W₂ (σR (R.rationalGenerator hR))
      (eR x) = eR (R.levelGenerator hR x))
    (hr : r = 1 ∨ r = 11) (hs : s = 5 ∨ s = 7) : False := by
  have hD : D < 0 := Fact.out
  have hnpos : 0 < n := by omega
  have hboundNat : 16 * n * n < 24 * p := by
    have h : (16 : ℤ) * n * n < 24 * p := by nlinarith [hbound]
    exact_mod_cast h
  have hnp : n < p := by
    by_contra h
    have hpn : p ≤ n := by omega
    have hsquare := Nat.mul_self_le_mul_self hpn
    nlinarith
  have hpn : ¬p ∣ n := Nat.not_dvd_of_pos_of_lt hnpos hnp
  have hcommon : Set.range eQ = Set.range (φ.toAddEquiv.toAddMonoidHom.comp eR) := by
    simpa only [AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom,
      Set.range_comp] using hpair
  have htransport : ∀ x, RationalPointMap.pointAction W₁
      (((φ.conjugate hW₂ hW₁).comp σR) (R.rationalGenerator hR))
      ((φ.toAddEquiv.toAddMonoidHom.comp eR) x) =
        (φ.toAddEquiv.toAddMonoidHom.comp eR) (R.levelGenerator hR x) := by
    intro x
    change RationalPointMap.pointAction W₁
      (φ.conjugate hW₂ hW₁ (σR (R.rationalGenerator hR))) (φ.toAddEquiv (eR x)) = _
    rw [φ.conjugate_action, hequivR]
    rfl
  have h := Q.kernel_bound_of_rational_specializations R hQ hR n hn p hp hnpos hpn
    W₁ hW₁ σQ ((φ.conjugate hW₂ hW₁).comp σR) eQ
    (φ.toAddEquiv.toAddMonoidHom.comp eR) heQ hcommon hequivQ htransport hr hs
  nlinarith

end SptClassification.LevelSixForm
