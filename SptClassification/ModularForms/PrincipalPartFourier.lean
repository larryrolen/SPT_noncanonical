/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.PrincipalPartFourierJ
public import SptClassification.QSeries.EtaIntegralCore

/-!
# The analytic-to-integral Fourier comparison for eta and j

The integral formal series used for principal-part elimination evaluate to the
actual analytic functions, with the specified exponential branch for eta.
These are the Fourier normalizations in [rolenManuscript, §3].
-/

public section

namespace SptClassification

open UpperHalfPlane

/-- The actual eta function is the specified exponential times its integral core sum. -/
theorem eta_eq_qParam_mul_tsum_integralCore (τ : UpperHalfPlane) :
    ModularForm.eta τ = Function.Periodic.qParam 24 τ *
      ∑' n, (QSeries.etaIntegralCore.coeff n : ℂ) * Function.Periodic.qParam 1 τ ^ n := by
  rw [(QSeries.hasSum_etaIntegralCore
    (Function.Periodic.norm_qParam_lt_one (by norm_num) τ.im_pos)).tsum_eq]
  simpa using eta_nat_mul_eq_euler 1 (τ : ℂ)

/-- The analytic invariant is the inverse nome times its integral core sum. -/
theorem levelOneJ_eq_qParam_inv_mul_tsum_integralCore (τ : UpperHalfPlane) :
    levelOneJ τ = (Function.Periodic.qParam 1 τ)⁻¹ *
      ∑' n, (QSeries.modularJIntegralCore.coeff n : ℂ) * Function.Periodic.qParam 1 τ ^ n := by
  rw [(hasSum_modularJIntegralCore τ).tsum_eq]
  have hq : Function.Periodic.qParam 1 (τ : ℂ) ≠ 0 := Complex.exp_ne_zero _
  simp [hq]

/-- The two integral core series converge absolutely and recover the actual eta
and modular invariant with the prescribed exponential normalizations. -/
theorem principalPart_fourier_comparison (τ : UpperHalfPlane) :
    let q := Function.Periodic.qParam 1 (τ : ℂ)
    Summable (fun n => ‖(QSeries.etaIntegralCore.coeff n : ℂ) * q ^ n‖) ∧
    Summable (fun n => ‖(QSeries.modularJIntegralCore.coeff n : ℂ) * q ^ n‖) ∧
    ModularForm.eta τ = Function.Periodic.qParam 24 τ *
      ∑' n, (QSeries.etaIntegralCore.coeff n : ℂ) * q ^ n ∧
    levelOneJ τ = q⁻¹ * ∑' n, (QSeries.modularJIntegralCore.coeff n : ℂ) * q ^ n := by
  exact ⟨QSeries.summable_norm_etaIntegralCore
      (Function.Periodic.norm_qParam_lt_one (by norm_num) τ.im_pos),
    summable_norm_modularJIntegralCore τ, eta_eq_qParam_mul_tsum_integralCore τ,
    levelOneJ_eq_qParam_inv_mul_tsum_integralCore τ⟩

end SptClassification
