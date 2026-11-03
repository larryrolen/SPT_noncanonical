/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.CMModuliSeparation
public import SptClassification.QuadraticForms.CMIntegralValues

/-!
# Polynomial separation from individual CM specializations

The common-root argument of [rolenManuscript, Lemma `lem:separation`]
is deduced from individual specializations of the actual CM pairs and an
injective coordinate on their geometric moduli. Existence of these data and
compatibility with the integral eta values remain explicit hypotheses; this
module does not admit either geometric construction as a literature theorem.
-/

public section

namespace SptClassification

namespace LevelSixForm

variable {D : ℤ} {r : ZMod 12} [Fact (D < 0)]

/-- An individual specialization of the rational CM action and its cyclic
subgroup, retaining equivariance for the actual quadratic generator. -/
structure Specialization (Q : LevelSixForm D r) (hodd : Q.b % 2 = 1)
    (F : Type*) [Field F] [DecidableEq F] where
  curve : WeierstrassCurve F
  elliptic : curve.IsElliptic
  endomorphisms : RationalPointMap.endomorphismRing Q.complexCurve →+*
    RationalPointMap.endomorphismRing curve
  cyclic : Q.curveLevelSix →+ curve.toAffine.Point
  injective : Function.Injective cyclic
  equivariant : ∀ x, RationalPointMap.pointAction curve
    (endomorphisms (Q.rationalGenerator hodd)) (cyclic x) =
      cyclic (Q.levelGenerator hodd x)

/-- The geometric cyclic-six class of an individual specialization. -/
noncomputable def Specialization.moduliClass
    {Q : LevelSixForm D r} {hodd : Q.b % 2 = 1}
    {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
    (S : Q.Specialization hodd F) :
    LevelSixPair.Moduli F :=
  (Q.specializedPair S.curve S.elliptic S.cyclic S.injective).moduliClass

end LevelSixForm

namespace CMIntegralValues

/-- Opposite-oriented integral eta values have different reductions when
their individual CM specializations have a compatible injective coordinate.
This compares actual primitive classes, rather than arbitrary polynomial roots. -/
theorem reduced_values_ne_of_specializations
    (d p : ℕ) [Fact (-(d : ℤ) < 0)] [Fact p.Prime]
    [DecidableEq (AlgebraicClosure (ZMod p))]
    (hp6 : ¬p ∣ 6) (hp : 3 < p)
    (n : ℕ) (hn : 4 * (n : ℤ) = 1 + (d : ℤ))
    (hbound : (1 + (d : ℤ)) ^ 2 < 24 * (p : ℤ))
    (models : IntegralCMClassPolynomials d)
    (coordinate : LevelSixPair.Moduli (AlgebraicClosure (ZMod p)) →
      AlgebraicClosure (ZMod p)) (hinj : Function.Injective coordinate)
    (specialize : ∀ {r : ZMod 12} (Q : LevelSixForm (-(d : ℤ)) r)
      (hodd : Q.b % 2 = 1), Q.Specialization hodd (AlgebraicClosure (ZMod p)))
    (compatible : ∀ {r : ZMod 12} (Q : LevelSixForm (-(d : ℤ)) r)
      (hodd : Q.b % 2 = 1) (v : Ring),
      complexEmbedding v = levelSixEtaQuotient Q.cmPoint →
      coordinate (specialize Q hodd).moduliClass = reduction p hp6 v)
    {r s : ZMod 12} (C : PrimitiveCMClass (-(d : ℤ)) r)
    (E : PrimitiveCMClass (-(d : ℤ)) s)
    (hr : r = 1 ∨ r = 11) (hs : s = 5 ∨ s = 7) :
    reduction p hp6 (first models C hr) ≠ reduction p hp6 (second models E hs) := by
  obtain ⟨Q, hQ⟩ := Quotient.exists_rep C.val
  obtain ⟨R, hR⟩ := Quotient.exists_rep E.val
  have hoddQ := Q.middle_coefficient_odd_of_product_orientation
    (hr.elim (fun h => Or.inl h) (fun h => Or.inr (Or.inr (Or.inr h))))
  have hoddR := R.middle_coefficient_odd_of_product_orientation
    (hs.elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr (Or.inl h))))
  have hvQ : complexEmbedding (first models C hr) = levelSixEtaQuotient Q.cmPoint := by
    rw [complexEmbedding_first, ← hQ, CMClass.etaValue_mk]
  have hvR : complexEmbedding (second models E hs) = levelSixEtaQuotient R.cmPoint := by
    rw [complexEmbedding_second, ← hR, CMClass.etaValue_mk]
  intro heq
  have hclasses := hinj ((compatible Q hoddQ _ hvQ).trans
    (heq.trans (compatible R hoddR _ hvR).symm))
  exact Q.specialized_moduli_ne_of_bound R hoddQ hoddR n (by simpa using hn)
    p hp (by simpa using hbound)
    (specialize Q hoddQ).curve (specialize R hoddR).curve
    (specialize Q hoddQ).elliptic (specialize R hoddR).elliptic
    (specialize Q hoddQ).endomorphisms (specialize R hoddR).endomorphisms
    (specialize Q hoddQ).cyclic (specialize R hoddR).cyclic
    (specialize Q hoddQ).injective (specialize R hoddR).injective
    (specialize Q hoddQ).equivariant (specialize R hoddR).equivariant hr hs hclasses

/-- The manuscript polynomial deduction from individual compatible CM
specializations. The geometric inputs are independent of any common root;
ordinary split primes require no additional hypothesis. -/
theorem isCoprime_of_specializations
    (d p : ℕ) [Fact (-(d : ℤ) < 0)] [Fact p.Prime]
    [DecidableEq (AlgebraicClosure (ZMod p))]
    (hp6 : ¬p ∣ 6) (hp : 3 < p) (hmod : d % 24 = 23)
    (hbound : (d + 1) ^ 2 < 24 * p)
    (models : IntegralCMClassPolynomials d)
    (coordinate : LevelSixPair.Moduli (AlgebraicClosure (ZMod p)) →
      AlgebraicClosure (ZMod p)) (hinj : Function.Injective coordinate)
    (specialize : ∀ {r : ZMod 12} (Q : LevelSixForm (-(d : ℤ)) r)
      (hodd : Q.b % 2 = 1), Q.Specialization hodd (AlgebraicClosure (ZMod p)))
    (compatible : ∀ {r : ZMod 12} (Q : LevelSixForm (-(d : ℤ)) r)
      (hodd : Q.b % 2 = 1) (v : Ring),
      complexEmbedding v = levelSixEtaQuotient Q.cmPoint →
      coordinate (specialize Q hodd).moduliClass = reduction p hp6 v) :
    IsCoprime (models.modelA.map (cmCoefficientReduction p hp6))
      (models.modelB.map (cmCoefficientReduction p hp6)) := by
  have hn : 4 * (((d + 1) / 4 : ℕ) : ℤ) = 1 + (d : ℤ) := by omega
  have hb : (1 + (d : ℤ)) ^ 2 < 24 * (p : ℤ) := by
    exact_mod_cast (show (1 + d) ^ 2 < 24 * p by simpa [Nat.add_comm] using hbound)
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
    (ZMod p) (AlgebraicClosure (ZMod p)) _ _).2
  intro x
  by_contra h
  push Not at h
  obtain ⟨ha, hb'⟩ := h
  obtain ⟨hA, hB⟩ := common_root_classes d p hp6 models x ha hb'
  have hne {r s : ZMod 12} (C : PrimitiveCMClass (-(d : ℤ)) r)
      (E : PrimitiveCMClass (-(d : ℤ)) s) :=
    reduced_values_ne_of_specializations d p hp6 hp ((d + 1) / 4) hn hb
      models coordinate hinj specialize compatible C E
  rcases hA with ⟨C, hC⟩ | ⟨C, hC⟩ <;>
    rcases hB with ⟨E, hE⟩ | ⟨E, hE⟩
  · exact hne C E (Or.inl rfl) (Or.inl rfl) (hC.trans hE.symm)
  · exact hne C E (Or.inl rfl) (Or.inr rfl) (hC.trans hE.symm)
  · exact hne C E (Or.inr rfl) (Or.inl rfl) (hC.trans hE.symm)
  · exact hne C E (Or.inr rfl) (Or.inr rfl) (hC.trans hE.symm)

end CMIntegralValues
end SptClassification
