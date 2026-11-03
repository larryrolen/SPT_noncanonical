/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.PrincipalWeakForms
public import SptClassification.ModularForms.PrincipalFormsFourier
public import SptClassification.QSeries.PrincipalFormsCoefficients
public import SptClassification.QSeries.FourierCoefficients

/-!
# The prescribed integral weakly holomorphic principal forms

The forms `principalHForm` and `principalKForm` realize equations (H) and (K)
of [rolenManuscript, §3]. Their integer coefficients are indexed by the
exponent of `exp(2πiτ/24)`. Clearing the common pole gives a convergent ordinary
power series, and the coefficient at exponent one in H is the negative of
the actual coefficient `fFourier d`.
-/

public section

namespace SptClassification

open UpperHalfPlane

/-- The prescribed weight-one-half form, with the actual coefficient of f. -/
noncomputable def principalHForm (d : ℕ) : EtaWeaklyHolomorphicForm 0 :=
  etaJWeakForm (QSeries.integralHPolynomial d (QSeries.fFourier d))

/-- The prescribed weight-five-halves form. -/
noncomputable def principalKForm (d : ℕ) : EtaWeaklyHolomorphicForm 2 :=
  etaThetaJWeakForm (QSeries.integralKPolynomial d)

/-- The full integral H coefficients sum to the actual weak form after pole clearing. -/
theorem principalHForm_hasSum (d : ℕ) (hd : d % 24 = 23) (τ : UpperHalfPlane) :
    HasSum (fun m : ℕ =>
      (QSeries.principalHFourier d (QSeries.fFourier d) (24 * (m : ℤ) - d) : ℂ) *
        Function.Periodic.qParam 1 τ ^ m)
      (Function.Periodic.qParam 1 τ ^ QSeries.principalIndex d *
        (Function.Periodic.qParam 24 τ)⁻¹ * principalHForm d τ) := by
  have hn := QSeries.principalIndex_mul d hd
  have hrow (m : ℕ) : 24 * (m : ℤ) - d =
      1 - 24 * ((QSeries.principalIndex d : ℤ) - m) := by omega
  simpa only [hrow, QSeries.principalHFourier_row, principalHForm, etaJWeakForm_apply]
    using hasSum_integralHPrincipalPart d (QSeries.fFourier d) τ

/-- The full integral K coefficients sum to the actual weak form after pole clearing. -/
theorem principalKForm_hasSum (d : ℕ) (hd : d % 24 = 23) (τ : UpperHalfPlane) :
    HasSum (fun m : ℕ =>
      (QSeries.principalKFourier d (24 * (m : ℤ) - d) : ℂ) *
        Function.Periodic.qParam 1 τ ^ m)
      (Function.Periodic.qParam 1 τ ^ QSeries.principalIndex d *
        (Function.Periodic.qParam 24 τ)⁻¹ * principalKForm d τ) := by
  have hn := QSeries.principalIndex_mul d hd
  have hnpos := QSeries.principalIndex_pos d hd
  have hrow (m : ℕ) : 24 * (m : ℤ) - d =
      1 - 24 * ((((QSeries.principalIndex d - 1 : ℕ) : ℤ) - m) + 1) := by omega
  simpa only [hrow, QSeries.principalKFourier_row, principalKForm, etaThetaJWeakForm_apply]
    using hasSum_integralKPrincipalPart d hd τ

/-- The normalized H coefficient at exponent one is `-a(d)`. -/
theorem principalHForm_coefficient_one (d : ℕ) (hd : d % 24 = 23) :
    QSeries.principalHFourier d (QSeries.fFourier d) 1 = -QSeries.fFourier d :=
  QSeries.principalHFourier_one d hd _

/-- Both actual forms have just the prescribed leading negative Fourier coefficient. -/
theorem principalForms_negative_coefficients (d : ℕ) (hd : d % 24 = 23)
    (r : ℤ) (hr : r < 0) :
    QSeries.principalHFourier d (QSeries.fFourier d) r =
        (if r = -(d : ℤ) then 1 else 0) ∧
      QSeries.principalKFourier d r = (if r = -(d : ℤ) then 1 else 0) :=
  ⟨QSeries.principalHFourier_negative d hd _ r hr,
    QSeries.principalKFourier_negative d hd r hr⟩

/-- The two prescribed integral weakly holomorphic forms exist, with their full
Fourier series and the exact principal parts of equations (H) and (K). -/
theorem exists_principal_forms (d : ℕ) (hd : d % 24 = 23) :
    ∃ (H : EtaWeaklyHolomorphicForm 0) (K : EtaWeaklyHolomorphicForm 2),
      (∀ τ : UpperHalfPlane,
        HasSum (fun m : ℕ =>
          (QSeries.principalHFourier d (QSeries.fFourier d) (24 * (m : ℤ) - d) : ℂ) *
            Function.Periodic.qParam 1 τ ^ m)
          (Function.Periodic.qParam 1 τ ^ QSeries.principalIndex d *
            (Function.Periodic.qParam 24 τ)⁻¹ * H τ)) ∧
      (∀ τ : UpperHalfPlane,
        HasSum (fun m : ℕ =>
          (QSeries.principalKFourier d (24 * (m : ℤ) - d) : ℂ) *
            Function.Periodic.qParam 1 τ ^ m)
          (Function.Periodic.qParam 1 τ ^ QSeries.principalIndex d *
            (Function.Periodic.qParam 24 τ)⁻¹ * K τ)) ∧
      QSeries.principalHFourier d (QSeries.fFourier d) 1 = -QSeries.fFourier d ∧
      (∀ r : ℤ, r < 0 →
        QSeries.principalHFourier d (QSeries.fFourier d) r =
          (if r = -(d : ℤ) then 1 else 0) ∧
        QSeries.principalKFourier d r = (if r = -(d : ℤ) then 1 else 0)) :=
  ⟨principalHForm d, principalKForm d, principalHForm_hasSum d hd,
    principalKForm_hasSum d hd, principalHForm_coefficient_one d hd,
    principalForms_negative_coefficients d hd⟩

end SptClassification
