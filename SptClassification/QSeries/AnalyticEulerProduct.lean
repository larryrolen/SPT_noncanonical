/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.EtaQuotientExpansion
public import Mathlib.Topology.Algebra.InfiniteSum.Group
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# The analytic inverse Euler product

The complex Euler product is nonzero on the open unit disc. Its inverse is
analytic there and is the limit of the finite geometric products. These facts
supply the analytic bounds for the partition generating-function comparison in
the principal-part construction [rolenManuscript, §3]. Identification with the
actual partition coefficient series is a separate assertion.
-/

public section

namespace SptClassification

open scoped Topology

/-- The inverse Euler product is the convergent product of the geometric factors. -/
theorem hasProd_inverseEulerFactors {q : ℂ} (hq : ‖q‖ < 1) :
    HasProd (fun n : ℕ => (1 - q ^ (n + 1))⁻¹) (etaEulerProduct q)⁻¹ := by
  have hne : (∏' n : ℕ, (1 - q ^ (n + 1))) ≠ 0 := by
    simpa only [etaEulerProduct_eq] using etaEulerProduct_ne_zero hq
  simpa only [etaEulerProduct_eq] using
    (ModularForm.multipliable_one_sub_pow hq).hasProd.inv₀ hne

/-- Finite geometric products tend to the analytic inverse Euler product. -/
theorem tendsto_inverseEulerProducts {q : ℂ} (hq : ‖q‖ < 1) :
    Filter.Tendsto (fun N : ℕ => ∏ n ∈ Finset.range N, (1 - q ^ (n + 1))⁻¹)
      Filter.atTop (𝓝 (etaEulerProduct q)⁻¹) :=
  (hasProd_inverseEulerFactors hq).tendsto_prod_nat

/-- The inverse Euler product is analytic at every point of the unit disc. -/
theorem analyticAt_inverseEtaEulerProduct {q : ℂ} (hq : ‖q‖ < 1) :
    AnalyticAt ℂ (fun z => (etaEulerProduct z)⁻¹) q := by
  have hD : DifferentiableOn ℂ etaEulerProduct (Metric.ball 0 1) :=
    differentiableOn_etaEulerProduct
  have hE : AnalyticAt ℂ etaEulerProduct q :=
    hD.analyticAt
      (Metric.isOpen_ball.mem_nhds (by simpa using hq))
  exact hE.inv (etaEulerProduct_ne_zero hq)

end SptClassification
