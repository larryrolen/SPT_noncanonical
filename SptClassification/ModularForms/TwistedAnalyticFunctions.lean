/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.FiniteFourierFilter
public import SptClassification.ModularForms.ConditionalPropagation
public import Mathlib.NumberTheory.ModularForms.Derivative

/-!
# Analytic operators in the quadratic twist construction

The finite translation filter acts on actual holomorphic functions and commutes
with the normalized derivative. Mathlib's analytic `E₂` and Serre derivative
have exactly the normalization in [rolenManuscript, §2, (2.5)].
-/

public section

namespace SptClassification

open UpperHalfPlane
open scoped Manifold Topology

/-- The actual weight-two Eisenstein function sums the manuscript's rational row. -/
theorem hasSum_eisensteinTwoCoefficient (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ => (eisensteinTwoCoefficient n : ℂ) *
      Function.Periodic.qParam 1 τ ^ n) (EisensteinSeries.E2 τ) := by
  convert EisensteinSeries.hasSum_qExpansion_E2 (z := τ) using 1
  ext n
  by_cases hn : n = 0 <;> simp [hn, eisensteinTwoCoefficient_apply, ArithmeticFunction.sigma_apply,
    Function.Periodic.qParam, smul_eq_mul]

/-- The weight `-1/2` Serre correction has positive sign and denominator 24. -/
theorem serreDerivative_negative_half (P : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    Derivative.serreDerivative (-(1 / 2 : ℂ)) P τ =
      Derivative.normalizedDerivOfComplex P τ + EisensteinSeries.E2 τ * P τ / 24 := by
  rw [Derivative.serreDerivative_apply]
  ring

/-- Differentiation of a rational translate introduces no scale factor. -/
theorem hasDerivAt_fourierTranslate {N : ℕ} [NeZero N]
    (F : UpperHalfPlane → ℂ) (hF : MDiff F) (j : ZMod N) (τ : UpperHalfPlane) :
    HasDerivAt ((fun z => F (fourierTranslate j z)) ∘ ofComplex)
      (deriv (F ∘ ofComplex) (fourierTranslate j τ)) (τ : ℂ) := by
  have h := (mdifferentiableAt_iff.mp (hF (fourierTranslate j τ))).hasDerivAt
  rw [fourierTranslate_coe] at h
  have ht := h.comp (τ : ℂ) ((hasDerivAt_id (τ : ℂ)).add_const
    ((j.val : ℝ) / N : ℂ))
  simp only [mul_one] at ht
  rw [fourierTranslate_coe]
  apply ht.congr_of_eventuallyEq
  rw [← isOpenEmbedding_coe.map_nhds_eq, Filter.eventuallyEq_map]
  apply Filter.Eventually.of_forall
  intro z
  simp only [Function.comp_apply, ofComplex_apply]
  congr 1
  simpa only [fourierTranslate_coe, id_eq] using (ofComplex_apply (fourierTranslate j z)).symm

/-- Rational translation preserves holomorphy. -/
theorem mdifferentiable_fourierTranslate {N : ℕ} [NeZero N]
    (F : UpperHalfPlane → ℂ) (hF : MDiff F) (j : ZMod N) :
    MDiff (fun z => F (fourierTranslate j z)) := by
  intro τ
  exact mdifferentiableAt_iff.mpr (hasDerivAt_fourierTranslate F hF j τ).differentiableAt

/-- A finite residue filter preserves holomorphy. -/
theorem mdifferentiable_fourierFilter {N : ℕ} [NeZero N]
    (c : ZMod N → ℂ) (F : UpperHalfPlane → ℂ) (hF : MDiff F) :
    MDiff (fourierFilter c F) := by
  have hsum := MDifferentiable.sum (t := Finset.univ)
    (fun (j : ZMod N) _ =>
      (mdifferentiable_const (c := fourierFilterKernel c j)).mul
        (mdifferentiable_fourierTranslate F hF j))
  have he : (∑ j : ZMod N, (fun _ : UpperHalfPlane => fourierFilterKernel c j) *
      (fun z => F (fourierTranslate j z))) = fourierFilter c F := by
    funext τ
    simp only [Finset.sum_apply, Pi.mul_apply, fourierFilter_apply]
  rw [he] at hsum
  exact hsum

/-- The normalized derivative commutes with the finite translation filter. -/
theorem normalizedDeriv_fourierFilter {N : ℕ} [NeZero N]
    (c : ZMod N → ℂ) (F : UpperHalfPlane → ℂ) (hF : MDiff F) :
    Derivative.normalizedDerivOfComplex (fourierFilter c F) =
      fourierFilter c (Derivative.normalizedDerivOfComplex F) := by
  funext τ
  have h := HasDerivAt.sum (u := Finset.univ) (fun j _ =>
    (hasDerivAt_fourierTranslate F hF j τ).const_mul (fourierFilterKernel c j))
  have hd : deriv (fourierFilter c F ∘ ofComplex) τ =
      ∑ j : ZMod N, fourierFilterKernel c j *
        deriv (F ∘ ofComplex) (fourierTranslate j τ) := by
        have he : (∑ j : ZMod N, fun z : ℂ =>
            fourierFilterKernel c j * F (fourierTranslate j (ofComplex z))) =
            fourierFilter c F ∘ ofComplex := by
          funext z
          simp only [Finset.sum_apply, Function.comp_apply, fourierFilter_apply]
        simp only [Function.comp_apply] at h
        rw [he] at h
        exact h.deriv
  simp only [Derivative.normalizedDerivOfComplex, hd, fourierFilter_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Filtering an integral-index rational Fourier row gives exactly the manuscript
selector, with no integrality or nonvanishing restriction on the index. -/
theorem negativeSquareFilter_hasSum (Q : ℕ) [Fact Q.Prime]
    (F : UpperHalfPlane → ℂ) (a : ℤ → ℚ)
    (hF : ∀ τ : UpperHalfPlane, HasSum (fun r : ℤ => (a r : ℂ) *
      Function.Periodic.qParam 1 τ ^ r) (F τ)) (τ : UpperHalfPlane) :
    HasSum (fun r : ℤ => ((negativeSquareSelector Q r * a r : ℚ) : ℂ) *
      Function.Periodic.qParam 1 τ ^ r)
      (fourierFilter (negativeSquareResidueSelector Q) F τ) := by
  simpa only [negativeSquareResidueSelector_intCast, Rat.cast_mul] using
    fourierFilter_qExpansion (negativeSquareResidueSelector Q) F
      (fun r => (a r : ℂ)) hF τ

/-- Construct the analytic constituents using the actual finite filter and Serre
operator. Only the untwisted Fourier expansions are supplied; all selected rows,
the derivative commutation and the Serre correction are deductions. No modular
transformation or cusp property is asserted here. -/
noncomputable def twistedAnalyticDataOfFourierExpansions (Q : ℕ) [Fact Q.Prime]
    (P M : UpperHalfPlane → ℂ) (hP : MDiff P)
    (hpart : ∀ τ : UpperHalfPlane, HasSum (fun r : ℤ => (QSeries.partitionFourier r : ℂ) *
      Function.Periodic.qParam 1 τ ^ r) (P τ))
    (hderiv : ∀ τ : UpperHalfPlane, HasSum (fun r : ℤ =>
      ((r * QSeries.partitionFourier r : ℚ) : ℂ) *
        Function.Periodic.qParam 1 τ ^ r) (Derivative.normalizedDerivOfComplex P τ))
    (hmock : ∀ τ : UpperHalfPlane, HasSum (fun r : ℤ =>
      (((QSeries.sptFourier r : ℚ) + r * QSeries.partitionFourier r / 12 : ℚ) : ℂ) *
        Function.Periodic.qParam 1 τ ^ r) (M τ)) : SptTwistedAnalyticData Q where
  eisensteinTwo := EisensteinSeries.E2
  eisensteinTwo_expansion := hasSum_eisensteinTwoCoefficient
  twistedM := fourierFilter (negativeSquareResidueSelector Q) M
  twistedP := fourierFilter (negativeSquareResidueSelector Q) P
  thetaTwistedP := Derivative.normalizedDerivOfComplex
    (fourierFilter (negativeSquareResidueSelector Q) P)
  serreDerivativeP := Derivative.serreDerivative (-(1 / 2 : ℂ))
    (fourierFilter (negativeSquareResidueSelector Q) P)
  twistedP_expansion := by
    intro τ
    exact negativeSquareFilter_hasSum Q P (fun r => (QSeries.partitionFourier r : ℚ))
      (by simpa only [Rat.cast_intCast] using hpart) τ
  twistedM_expansion := negativeSquareFilter_hasSum Q M _ hmock
  thetaTwistedP_expansion := by
    intro τ
    rw [normalizedDeriv_fourierFilter _ P hP]
    convert negativeSquareFilter_hasSum Q (Derivative.normalizedDerivOfComplex P)
      (fun r => r * QSeries.partitionFourier r) hderiv τ using 1
    ext r
    congr 2
    ring
  serreDerivativeP_eq := serreDerivative_negative_half _

section

variable (Q : ℕ) [Fact Q.Prime]
    (P M : UpperHalfPlane → ℂ) (hP : MDiff P)
    (hpart : ∀ τ : UpperHalfPlane, HasSum (fun r : ℤ => (QSeries.partitionFourier r : ℂ) *
      Function.Periodic.qParam 1 τ ^ r) (P τ))
    (hderiv : ∀ τ : UpperHalfPlane, HasSum (fun r : ℤ =>
      ((r * QSeries.partitionFourier r : ℚ) : ℂ) *
        Function.Periodic.qParam 1 τ ^ r) (Derivative.normalizedDerivOfComplex P τ))
    (hmock : ∀ τ : UpperHalfPlane, HasSum (fun r : ℤ =>
      (((QSeries.sptFourier r : ℚ) + r * QSeries.partitionFourier r / 12 : ℚ) : ℂ) *
        Function.Periodic.qParam 1 τ ^ r) (M τ))

/-- The constructed `twistedM` is the specified analytic operator. -/
theorem twistedAnalyticDataOfFourierExpansions_twistedM :
    (twistedAnalyticDataOfFourierExpansions Q P M hP hpart hderiv hmock).twistedM =
      fourierFilter (negativeSquareResidueSelector Q) M := (rfl)

/-- The constructed `twistedP` is the specified analytic operator. -/
theorem twistedAnalyticDataOfFourierExpansions_twistedP :
    (twistedAnalyticDataOfFourierExpansions Q P M hP hpart hderiv hmock).twistedP =
      fourierFilter (negativeSquareResidueSelector Q) P := (rfl)

/-- The constructed `serreDerivativeP` is the specified analytic operator. -/
theorem twistedAnalyticDataOfFourierExpansions_serreDerivativeP :
    (twistedAnalyticDataOfFourierExpansions Q P M hP hpart hderiv hmock).serreDerivativeP =
      Derivative.serreDerivative (-(1 / 2 : ℂ))
      (fourierFilter (negativeSquareResidueSelector Q) P) := (rfl)

end

end SptClassification
