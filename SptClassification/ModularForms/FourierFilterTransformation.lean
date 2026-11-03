/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.FiniteFourierFilter

/-!
# Equivariance of finite Fourier filters

A residue multiplier invariant under a unit dilation has an invariant
translation kernel. Reindexing then transfers a transformation law through
the filter. No holomorphy or restriction on the weight is needed.
-/

public section

namespace SptClassification

open UpperHalfPlane

/-- Multiplication by a unit permutes the residue classes. -/
def unitResidueMulEquiv {N : ℕ} (u : (ZMod N)ˣ) : ZMod N ≃ ZMod N where
  toFun x := (u : ZMod N) * x
  invFun x := ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * x
  left_inv x := by simp [← mul_assoc]
  right_inv x := by simp [← mul_assoc]

theorem unitResidueMulEquiv_apply {N : ℕ} (u : (ZMod N)ˣ) (x : ZMod N) :
    unitResidueMulEquiv u x = (u : ZMod N) * x := (rfl)

/-- Unit dilation preserves the Fourier kernel when it preserves the selector. -/
theorem fourierFilterKernel_mul_unit {N : ℕ} [NeZero N]
    (c : ZMod N → ℂ) (u : (ZMod N)ˣ)
    (hc : ∀ x, c ((u : ZMod N) * x) = c x) (j : ZMod N) :
    fourierFilterKernel c ((u : ZMod N) * j) = fourierFilterKernel c j := by
  simp only [fourierFilterKernel_eq]
  congr 1
  have h := ZMod.dft_comp_unitMul c u ((u : ZMod N) * j)
  simpa only [hc, ← mul_assoc, Units.inv_mul, one_mul] using h

/-- Reindexing the rational translates transfers any scalar automorphy law. -/
theorem fourierFilter_map_of_translate {N : ℕ} [NeZero N]
    (c : ZMod N → ℂ) (F : UpperHalfPlane → ℂ)
    (u : (ZMod N)ˣ) (hc : ∀ x, c ((u : ZMod N) * x) = c x)
    (τ τ' : UpperHalfPlane) (a : ℂ)
    (hF : ∀ j : ZMod N, F (fourierTranslate j τ') =
      a * F (fourierTranslate ((u : ZMod N) * j) τ)) :
    fourierFilter c F τ' = a * fourierFilter c F τ := by
  simp only [fourierFilter_apply, hF]
  calc
    _ = a * ∑ j : ZMod N, fourierFilterKernel c ((u : ZMod N) * j) *
        F (fourierTranslate ((u : ZMod N) * j) τ) := by
      simp only [fourierFilterKernel_mul_unit c u hc, Finset.mul_sum, mul_left_comm]
    _ = _ := by
      congr 1
      exact Equiv.sum_comp (unitResidueMulEquiv u)
        (fun j : ZMod N => fourierFilterKernel c j * F (fourierTranslate j τ))

/-- The negative-square selector is invariant under nonzero squares. -/
theorem negativeSquareResidueSelector_mul_square (Q : ℕ) [Fact Q.Prime]
    (u : (ZMod Q)ˣ) (x : ZMod Q) :
    negativeSquareResidueSelector Q ((u : ZMod Q) ^ 2 * x) =
      negativeSquareResidueSelector Q x := by
  have hu : (((u : ZMod Q).val : ℤ) : ZMod Q) ≠ 0 := by
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using u.ne_zero
  have h := congrArg (fun y : ℚ => (y : ℂ))
    (negativeSquareSelector_mul_square Q hu (x.val : ℤ))
  simpa only [← negativeSquareResidueSelector_intCast, Int.cast_mul, Int.cast_pow,
    Int.cast_natCast, ZMod.natCast_zmod_val] using h

end SptClassification
