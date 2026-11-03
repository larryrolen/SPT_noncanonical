/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.ComplexPowerSeries
public import SptClassification.QSeries.PrincipalPartIntegral
public import SptClassification.QSeries.PartitionEulerProduct
public import Mathlib.Analysis.Complex.TaylorSeries

/-!
# The analytic sum of the integral eta core

The Euler product is holomorphic on the unit disc. Its Taylor series is the
formal inverse of the actual partition generating series, and hence agrees with
the integral core used in the principal-part construction [rolenManuscript, §3].
-/

public section

namespace SptClassification.QSeries

/-- The Taylor series at zero of the actual analytic Euler product. -/
noncomputable def etaTaylorSeries : PowerSeries ℂ :=
  PowerSeries.mk (fun n => (n.factorial : ℂ)⁻¹ * iteratedDeriv n etaEulerProduct 0)

/-- Coefficients of the Taylor series of the analytic Euler product. -/
theorem etaTaylorSeries_coeff (n : ℕ) :
    etaTaylorSeries.coeff n =
      (n.factorial : ℂ)⁻¹ * iteratedDeriv n etaEulerProduct 0 := by
  simp [etaTaylorSeries]

/-- Holomorphy on the whole unit disc gives convergence of the Euler-product Taylor series there. -/
theorem hasSum_etaTaylorSeries {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n => etaTaylorSeries.coeff n * q ^ n) (etaEulerProduct q) := by
  have hf : DifferentiableOn ℂ etaEulerProduct (Metric.ball 0 1) :=
    differentiableOn_etaEulerProduct
  have h := Complex.hasSum_taylorSeries_on_ball hf (z := q) (by simpa using hq)
  simpa [etaTaylorSeries, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using h

/-- The complex partition series times the Taylor series of the Euler product is one. -/
theorem partitionSeries_map_mul_etaTaylorSeries :
    partitionSeries.map (Int.castRingHom ℂ) * etaTaylorSeries = 1 := by
  apply PowerSeries.ext
  have h := coefficients_eq_of_hasSum
    (c := fun n => (partitionSeries.map (Int.castRingHom ℂ) * etaTaylorSeries).coeff n)
    (d := fun n => (1 : PowerSeries ℂ).coeff n) (f := fun _ => 1)
    (fun q hq => ?_) (fun q _ => hasSum_complexPowerSeries_one q)
  · exact congrFun h
  · have hP : HasSum (fun n => (partitionSeries.map (Int.castRingHom ℂ)).coeff n * q ^ n)
        (etaEulerProduct q)⁻¹ := by
      simpa using hasSum_partitionCount_inverseEuler hq
    simpa [etaEulerProduct_ne_zero hq] using
      hasSum_complexPowerSeries_mul _ _ _ _ _ hP (hasSum_etaTaylorSeries hq)

/-- The complex image of the integral eta core is exactly the analytic Taylor series. -/
theorem etaIntegralCore_map_eq_taylorSeries :
    etaIntegralCore.map (Int.castRingHom ℂ) = etaTaylorSeries := by
  have hP : partitionSeries.map (Int.castRingHom ℂ) *
      etaIntegralCore.map (Int.castRingHom ℂ) = 1 := by
    simpa using congrArg (PowerSeries.map (Int.castRingHom ℂ)) partitionSeries_mul_etaIntegralCore
  calc
    etaIntegralCore.map (Int.castRingHom ℂ) =
        etaIntegralCore.map (Int.castRingHom ℂ) *
          (partitionSeries.map (Int.castRingHom ℂ) * etaTaylorSeries) := by
      rw [partitionSeries_map_mul_etaTaylorSeries, mul_one]
    _ = etaTaylorSeries := by
      rw [← mul_assoc, mul_comm (etaIntegralCore.map _), hP, one_mul]

/-- The actual integral eta core sums to the analytic Euler product on the full unit disc. -/
theorem hasSum_etaIntegralCore {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n => (etaIntegralCore.coeff n : ℂ) * q ^ n) (etaEulerProduct q) := by
  have h := hasSum_etaTaylorSeries hq
  rw [← etaIntegralCore_map_eq_taylorSeries] at h
  simpa using h

/-- The integral eta core converges absolutely throughout the unit disc. -/
theorem summable_norm_etaIntegralCore {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun n => ‖(etaIntegralCore.coeff n : ℂ) * q ^ n‖) :=
  (hasSum_etaIntegralCore hq).summable.norm

end SptClassification.QSeries
