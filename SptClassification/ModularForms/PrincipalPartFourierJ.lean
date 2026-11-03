/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.PrincipalPartEisenstein
public import SptClassification.ModularForms.PrincipalPartCusp
public import SptClassification.QSeries.PrincipalPartIntegral
public import SptClassification.QSeries.PartitionEulerProduct
public import SptClassification.QSeries.ConvergentPowers

/-!
# The convergent integral Fourier core of the modular invariant

The actual partition and normalized Eisenstein series evaluate the integral
formal core `J = E₄³ P²⁴`. The discriminant identity then identifies its sum
with `q j`, with the eta exponential branch fixed as in [rolenManuscript, §3].
-/

public section

namespace SptClassification

open UpperHalfPlane

/-- The integral core of `j` sums to its Eisenstein and Euler-product expression. -/
theorem hasSum_modularJIntegralCore_euler (τ : UpperHalfPlane) :
    HasSum (fun n => (QSeries.modularJIntegralCore.coeff n : ℂ) *
      Function.Periodic.qParam 1 τ ^ n)
      (ModularForm.E₄ τ ^ 3 * (etaEulerProduct (Function.Periodic.qParam 1 τ))⁻¹ ^ 24) := by
  rw [QSeries.modularJIntegralCore_eq]
  have hq := Function.Periodic.norm_qParam_lt_one (by norm_num : (0 : ℝ) < 1) τ.im_pos
  have hE : HasSum (fun n => (QSeries.eisensteinFourSeries.coeff n : ℂ) *
      Function.Periodic.qParam 1 τ ^ n) (ModularForm.E₄ τ) := by
    simpa only [QSeries.eisensteinFourSeries_coeff] using hasSum_eisensteinFourCoefficient τ
  have hP : HasSum (fun n => (QSeries.partitionSeries.coeff n : ℂ) *
      Function.Periodic.qParam 1 τ ^ n)
      (etaEulerProduct (Function.Periodic.qParam 1 τ))⁻¹ := by
    simpa using QSeries.hasSum_partitionCount_inverseEuler hq
  have hE3 := QSeries.hasSum_coefficientTerm_pow _ _ _ 3 hE
  have hP24 := QSeries.hasSum_coefficientTerm_pow _ _ _ 24 hP
  exact QSeries.hasSum_coefficientTerm_mul _ _ _ _ _
    hE3.summable.norm hP24.summable.norm hE3 hP24

/-- The discriminant factors as the nome times the twenty-fourth Euler-product power. -/
theorem discriminant_eq_qParam_mul_euler (τ : UpperHalfPlane) :
    CuspForm.discriminant τ = Function.Periodic.qParam 1 τ *
      etaEulerProduct (Function.Periodic.qParam 1 τ) ^ 24 := by
  change ModularForm.eta τ ^ 24 = _
  have hη : ModularForm.eta τ = Function.Periodic.qParam 24 τ *
      etaEulerProduct (Function.Periodic.qParam 1 τ) := by
    simpa using eta_nat_mul_eq_euler 1 (τ : ℂ)
  rw [hη, mul_pow, qParam_twentyFour_pow]

/-- The actual integral formal `j` core has sum `q j(τ)` at every upper-half-plane point. -/
theorem hasSum_modularJIntegralCore (τ : UpperHalfPlane) :
    HasSum (fun n => (QSeries.modularJIntegralCore.coeff n : ℂ) *
      Function.Periodic.qParam 1 τ ^ n)
      (Function.Periodic.qParam 1 τ * levelOneJ τ) := by
  have hq : Function.Periodic.qParam 1 (τ : ℂ) ≠ 0 := Complex.exp_ne_zero _
  have he : etaEulerProduct (Function.Periodic.qParam 1 τ) ≠ 0 :=
    etaEulerProduct_ne_zero (Function.Periodic.norm_qParam_lt_one (by norm_num) τ.im_pos)
  convert hasSum_modularJIntegralCore_euler τ using 1
  rw [levelOneJ_eq, discriminant_eq_qParam_mul_euler]
  field_simp

/-- The integral `j` core converges absolutely at every upper-half-plane nome. -/
theorem summable_norm_modularJIntegralCore (τ : UpperHalfPlane) :
    Summable (fun n => ‖(QSeries.modularJIntegralCore.coeff n : ℂ) *
      Function.Periodic.qParam 1 τ ^ n‖) :=
  (hasSum_modularJIntegralCore τ).summable.norm

end SptClassification
