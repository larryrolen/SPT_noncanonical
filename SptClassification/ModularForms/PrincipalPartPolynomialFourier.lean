/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.PrincipalPartFourier
public import SptClassification.ModularForms.PrincipalPartFourierDerivative
public import SptClassification.QSeries.PrincipalPartPolynomialEvaluation

/-!
# Full Fourier series of the integral eta polynomial families

The finite polynomial evaluation theorem identifies all coefficients of the
analytic families in [rolenManuscript, §3]. The derivative family has one
additional pole in the nome, accounting for the shift in the K construction.
-/

public section

namespace SptClassification

open UpperHalfPlane

/-- The full eta-polynomial row sums to the analytic polynomial, after clearing its pole. -/
theorem hasSum_etaJPolynomial_rows (P : Polynomial ℤ) (M : ℕ)
    (hM : P.natDegree ≤ M) (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ =>
      (QSeries.polynomialRows (QSeries.etaJRow QSeries.etaIntegralCore
        QSeries.modularJIntegralCore) P ((M : ℤ) - (n : ℤ)) : ℂ) *
        Function.Periodic.qParam 1 τ ^ n)
      (Function.Periodic.qParam 1 τ ^ M * (Function.Periodic.qParam 24 τ)⁻¹ *
        etaJPolynomial P τ) := by
  have hq : Function.Periodic.qParam 1 (τ : ℂ) ≠ 0 := Complex.exp_ne_zero _
  have ht : Function.Periodic.qParam 24 (τ : ℂ) ≠ 0 := Complex.exp_ne_zero _
  have hU := (principalPart_fourier_comparison τ).1.of_norm.hasSum
  have hJ := hasSum_modularJIntegralCore τ
  have hs := QSeries.hasSum_polynomialRows_etaJRow _ _ P M hM _ _ _ hq hU hJ
  convert hs using 1
  rw [etaJPolynomial_eq, eta_eq_qParam_mul_tsum_integralCore]
  simp only [Polynomial.eval_map, mul_div_cancel_left₀ _ hq]
  field_simp

/-- Absolute convergence of the full eta-polynomial coefficient sequence. -/
theorem summable_norm_etaJPolynomial_rows (P : Polynomial ℤ) (M : ℕ)
    (hM : P.natDegree ≤ M) (τ : UpperHalfPlane) :
    Summable (fun n : ℕ =>
      ‖(QSeries.polynomialRows (QSeries.etaJRow QSeries.etaIntegralCore
        QSeries.modularJIntegralCore) P ((M : ℤ) - (n : ℤ)) : ℂ) *
        Function.Periodic.qParam 1 τ ^ n‖) :=
  (hasSum_etaJPolynomial_rows P M hM τ).summable.norm

/-- The derivative-polynomial row carries one additional power of the nome. -/
theorem hasSum_etaThetaJPolynomial_rows (P : Polynomial ℤ) (M : ℕ)
    (hM : P.natDegree ≤ M) (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ =>
      (QSeries.polynomialRows (QSeries.etaThetaJRow QSeries.etaIntegralCore
        QSeries.modularJIntegralCore) P ((M : ℤ) - (n : ℤ)) : ℂ) *
        Function.Periodic.qParam 1 τ ^ n)
      (Function.Periodic.qParam 1 τ ^ (M + 1) * (Function.Periodic.qParam 24 τ)⁻¹ *
        etaThetaJPolynomial P τ) := by
  have hq : Function.Periodic.qParam 1 (τ : ℂ) ≠ 0 := Complex.exp_ne_zero _
  have ht : Function.Periodic.qParam 24 (τ : ℂ) ≠ 0 := Complex.exp_ne_zero _
  have hU := (principalPart_fourier_comparison τ).1.of_norm.hasSum
  have hD := hasSum_negative_j_derivative_core τ
  have hUD := QSeries.hasSum_coefficientTerm_mul _ _ _ _ _
    hU.summable.norm hD.summable.norm hU hD
  have hJ := hasSum_modularJIntegralCore τ
  have hs := QSeries.hasSum_polynomialRows_etaJRow _ _ P M hM _ _ _ hq hUD hJ
  rw [QSeries.etaThetaJRow_eq_etaJRow]
  convert hs using 1
  rw [etaThetaJPolynomial_eq, eta_eq_qParam_mul_tsum_integralCore]
  simp only [Polynomial.eval_map, mul_div_cancel_left₀ _ hq, pow_succ]
  field_simp

/-- Absolute convergence of the derivative-polynomial coefficient sequence. -/
theorem summable_norm_etaThetaJPolynomial_rows (P : Polynomial ℤ) (M : ℕ)
    (hM : P.natDegree ≤ M) (τ : UpperHalfPlane) :
    Summable (fun n : ℕ =>
      ‖(QSeries.polynomialRows (QSeries.etaThetaJRow QSeries.etaIntegralCore
        QSeries.modularJIntegralCore) P ((M : ℤ) - (n : ℤ)) : ℂ) *
        Function.Periodic.qParam 1 τ ^ n‖) :=
  (hasSum_etaThetaJPolynomial_rows P M hM τ).summable.norm

end SptClassification
