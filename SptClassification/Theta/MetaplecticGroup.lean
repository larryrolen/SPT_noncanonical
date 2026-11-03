/- Assembled by AxiomProver. -/

module

public import SptClassification.Theta.MetaplecticPairs

/-!
# The group of algebraic metaplectic pairs

The pointwise square-root condition already gives inverses for matrix–factor
pairs. This is an algebraic group of pairs; the generated standard lifts form
a more restrictive collection. The analytic Weil representation of the latter
still requires operator descent. See [rolenManuscript, lines 339–343].
-/

public section

namespace SptClassification
namespace Theta

/-- The inverse pair uses the inverse matrix and the reciprocal of the
original factor at its inverse image. -/
noncomputable def MetaplecticPair.inverse (g : MetaplecticPair) :
    MetaplecticPair where
  matrix := g.matrix⁻¹
  factor z := (g.factor (g.matrix⁻¹ • z))⁻¹
  factor_ne_zero z := inv_ne_zero (g.factor_ne_zero _)
  factor_sq z := by
    have hnonzero : metaplecticDenominator g.matrix
        (g.matrix⁻¹ • z) ≠ 0 := by
      rw [← g.factor_sq]
      exact pow_ne_zero _ (g.factor_ne_zero _)
    have hden := metaplecticDenominator_mul g.matrix⁻¹ g.matrix
      (g.matrix⁻¹ • z) hnonzero
    have hprod : metaplecticDenominator g.matrix⁻¹ z *
        metaplecticDenominator g.matrix (g.matrix⁻¹ • z) = 1 := by
      have haction : g.matrix • (g.matrix⁻¹ • z) = z := by
        rw [← mul_smul, mul_inv_cancel, one_smul]
      simpa only [haction, inv_mul_cancel, metaplecticDenominator_one] using hden.symm
    rw [inv_pow, g.factor_sq]
    apply (mul_right_cancel₀ hnonzero)
    rw [inv_mul_cancel₀ hnonzero]
    exact hprod.symm

/-- A pair composed with its inverse is the neutral pair. -/
theorem MetaplecticPair.comp_inverse (g : MetaplecticPair) :
    g.comp g.inverse = identity := by
  apply MetaplecticPair.ext
  · simp only [MetaplecticPair.comp_matrix, MetaplecticPair.identity_matrix,
      MetaplecticPair.inverse, mul_inv_cancel]
  · funext z
    simp only [MetaplecticPair.comp_factor, MetaplecticPair.identity_factor,
      MetaplecticPair.inverse]
    exact mul_inv_cancel₀ (g.factor_ne_zero _)

/-- The inverse pair composed with a pair is the neutral pair. -/
theorem MetaplecticPair.inverse_comp (g : MetaplecticPair) :
    g.inverse.comp g = identity := by
  apply MetaplecticPair.ext
  · simp only [MetaplecticPair.comp_matrix, MetaplecticPair.identity_matrix,
      MetaplecticPair.inverse, inv_mul_cancel]
  · funext z
    simp only [MetaplecticPair.comp_factor, MetaplecticPair.identity_factor,
      MetaplecticPair.inverse]
    have hact : g.matrix⁻¹ • (g.matrix • z) = z := by
      rw [← mul_smul, inv_mul_cancel, one_smul]
    rw [hact]
    exact inv_mul_cancel₀ (g.factor_ne_zero z)

/-- Algebraic metaplectic matrix–factor pairs form a group. -/
noncomputable instance instGroupMetaplecticPair : Group MetaplecticPair where
  inv := MetaplecticPair.inverse
  inv_mul_cancel := MetaplecticPair.inverse_comp

end Theta
end SptClassification
