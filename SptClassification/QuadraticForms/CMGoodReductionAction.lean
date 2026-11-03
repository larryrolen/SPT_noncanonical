/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.AlgebraicGoodReduction
public import SptClassification.QuadraticForms.CMMarkedEtaLiterature
public import SptClassification.QuadraticForms.CMIntegralEtaReduction

/-! # The oriented CM action on the actual reduced eta fiber -/

public section

namespace SptClassification

namespace LevelSixWeierstrass

/-- The integral eta equation commutes with every coefficient ring map. -/
theorem map_curve {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (t : A) : (curve t).map f = curve (f t) := by
  ext <;> simp only [WeierstrassCurve.map, curve_a₁, curve_a₂, curve_a₃,
    curve_a₄, curve_a₆, map_add, map_mul, map_ofNat, map_zero]

end LevelSixWeierstrass

namespace LevelSixForm

open LevelSixWeierstrass RationalPointMap

variable {D : ℤ} {r : ZMod 12} [Fact (D < 0)] (Q : LevelSixForm D r)

/-- The constructed complex action specializes to the actual integral eta
fiber. The quadratic relation is preserved by the endomorphism ring map;
the integral origin section preserves the orientation scalar. This deduction
works for ordinary and supersingular primes and uses only the named general
good-reduction and classical analytic literature inputs. -/
theorem exists_reduced_eta_CM_action (hodd : Q.b % 2 = 1)
    (n : ℕ) (hn : 4 * (n : ℤ) = 1 - D)
    (t : CMIntegralValues.Ring)
    (ht : CMIntegralValues.complexEmbedding t = levelSixEtaQuotient Q.cmPoint)
    {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
    (p : ℕ) [Fact p.Prime] [CharP F p] (hp : 3 < p)
    (red : CMIntegralValues.Ring →+* F) (h6 : (6 : F) ≠ 0)
    (hΔ : (curve (red t)).Δ ≠ 0) :
    ∃ a : endomorphismRing (curve (red t)),
      a * a - a + (n : endomorphismRing (curve (red t))) = 0 ∧
      pointAction _ a (sixPoint (red t) hΔ) =
        ((Q.b + 1) / 2 : ℤ) • sixPoint (red t) hΔ := by
  obtain ⟨a, ha, hP, _⟩ := Q.exists_eta_CM_action hodd n hn
  have hE : (curve (levelSixEtaQuotient Q.cmPoint)).IsElliptic :=
    (pair _ (eta_discriminant_ne_zero Q.cmPoint)).elliptic
  obtain ⟨σ, hσ⟩ := goodReduction_endomorphisms_sections_literature p hp red
    (curve t) (curve (levelSixEtaQuotient Q.cmPoint)) (curve (red t))
    (by rw [map_curve, ht]) (map_curve red t) hE
    (Q.integralEta_reduction_isElliptic hodd t ht red h6)
  refine ⟨σ a, ?_, ?_⟩
  · simpa only [map_add, map_sub, map_mul, map_natCast, map_zero] using congrArg σ ha
  · have hc : (curve (levelSixEtaQuotient Q.cmPoint)).toAffine.Nonsingular
        (CMIntegralValues.complexEmbedding 0) (CMIntegralValues.complexEmbedding 0) := by
      simpa only [map_zero] using origin_nonsingular _ (eta_discriminant_ne_zero Q.cmPoint)
    have hr : (curve (red t)).toAffine.Nonsingular (red 0) (red 0) := by
      simpa only [map_zero] using origin_nonsingular (red t) hΔ
    have h := hσ 0 0 hc hr a ((Q.b + 1) / 2)
    simpa only [map_zero, sixPoint_eq] using h (by simpa only [map_zero, sixPoint_eq] using hP)

end LevelSixForm
end SptClassification
