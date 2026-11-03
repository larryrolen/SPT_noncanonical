/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.PrincipalPartPolynomialDegree
public import SptClassification.ModularForms.PrincipalPartPolynomialFourier

/-!
# Fourier series of the prescribed principal forms

The actual integral polynomials realize the complete formal H and K rows from
[rolenManuscript, §3, equations (H) and (K)]. The derivative contributes the
extra pole that turns the K polynomial degree `principalIndex d - 1` into the
same leading Fourier exponent as H.
-/

public section

namespace SptClassification

open UpperHalfPlane

/-- The entire prescribed H row sums to its actual analytic eta polynomial. -/
theorem hasSum_integralHPrincipalPart (d : ℕ) (a : ℤ) (τ : UpperHalfPlane) :
    HasSum (fun m : ℕ =>
      (QSeries.integralHPrincipalPart d a ((QSeries.principalIndex d : ℤ) - (m : ℤ)) : ℂ) *
        Function.Periodic.qParam 1 τ ^ m)
      (Function.Periodic.qParam 1 τ ^ QSeries.principalIndex d *
        (Function.Periodic.qParam 24 τ)⁻¹ *
        etaJPolynomial (QSeries.integralHPolynomial d a) τ) := by
  simpa only [QSeries.polynomialRows_integralHPolynomial] using
    hasSum_etaJPolynomial_rows (QSeries.integralHPolynomial d a)
      (QSeries.principalIndex d) (QSeries.natDegree_integralHPolynomial_le d a) τ

/-- Absolute convergence of the complete prescribed H coefficient sequence. -/
theorem summable_norm_integralHPrincipalPart (d : ℕ) (a : ℤ) (τ : UpperHalfPlane) :
    Summable (fun m : ℕ =>
      ‖(QSeries.integralHPrincipalPart d a ((QSeries.principalIndex d : ℤ) - (m : ℤ)) : ℂ) *
        Function.Periodic.qParam 1 τ ^ m‖) :=
  (hasSum_integralHPrincipalPart d a τ).summable.norm

/-- The entire prescribed K row has the same cleared pole exponent as H. -/
theorem hasSum_integralKPrincipalPart (d : ℕ) (hd : d % 24 = 23) (τ : UpperHalfPlane) :
    HasSum (fun m : ℕ =>
      (QSeries.integralKPrincipalPart d (((QSeries.principalIndex d - 1 : ℕ) : ℤ) -
        (m : ℤ)) : ℂ) * Function.Periodic.qParam 1 τ ^ m)
      (Function.Periodic.qParam 1 τ ^ QSeries.principalIndex d *
        (Function.Periodic.qParam 24 τ)⁻¹ *
        etaThetaJPolynomial (QSeries.integralKPolynomial d) τ) := by
  have hshift : QSeries.principalIndex d - 1 + 1 = QSeries.principalIndex d := by
    have := QSeries.principalIndex_pos d hd
    omega
  simpa only [QSeries.polynomialRows_integralKPolynomial, hshift] using
    hasSum_etaThetaJPolynomial_rows (QSeries.integralKPolynomial d)
      (QSeries.principalIndex d - 1) (QSeries.natDegree_integralKPolynomial_le d) τ

/-- Absolute convergence of the complete prescribed K coefficient sequence. -/
theorem summable_norm_integralKPrincipalPart (d : ℕ) (hd : d % 24 = 23)
    (τ : UpperHalfPlane) :
    Summable (fun m : ℕ =>
      ‖(QSeries.integralKPrincipalPart d (((QSeries.principalIndex d - 1 : ℕ) : ℤ) -
        (m : ℤ)) : ℂ) * Function.Periodic.qParam 1 τ ^ m‖) :=
  (hasSum_integralKPrincipalPart d hd τ).summable.norm

end SptClassification
