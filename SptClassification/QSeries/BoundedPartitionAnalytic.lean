/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.BoundedPartitionProduct
public import SptClassification.QSeries.AnalyticGeometric
public import SptClassification.QSeries.ConvergentProducts

/-!
# Convergent generating functions for bounded partitions

The actual counts of partitions with bounded parts have an absolutely convergent
generating series on the unit disc. Finite geometric multiplication identifies
its sum with the finite inverse Euler product, without evaluating an infinite
formal product. This is the finite approximation used in [rolenManuscript, §3].
-/

public section

namespace SptClassification.QSeries

/-- The formal bounded-partition series converges absolutely on the unit disc. -/
theorem summable_norm_boundedPartitionSeries (N : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun n => ‖((boundedPartitionSeries N).coeff n : ℂ) * q ^ n‖) := by
  induction N with
  | zero =>
    simpa +contextual [boundedPartitionSeries_zero, PowerSeries.coeff_one, apply_ite] using
      (hasSum_ite_eq (0 : ℕ) (1 : ℝ)).summable
  | succ N ih =>
    rw [boundedPartitionSeries_succ]
    exact summable_norm_coefficientTerm_mul _ _ _ ih
      (summable_norm_geometricCoefficient (Nat.succ_pos N) hq)

/-- The bounded formal series evaluates to the finite inverse Euler product. -/
theorem hasSum_boundedPartitionSeries (N : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n => ((boundedPartitionSeries N).coeff n : ℂ) * q ^ n)
      (∏ i ∈ Finset.range N, (1 - q ^ (i + 1))⁻¹) := by
  induction N with
  | zero =>
    simpa +contextual [boundedPartitionSeries_zero, PowerSeries.coeff_one] using
      hasSum_ite_eq (0 : ℕ) (1 : ℂ)
  | succ N ih =>
    rw [boundedPartitionSeries_succ, Finset.prod_range_succ]
    exact hasSum_coefficientTerm_mul _ _ _ _ _
      (summable_norm_boundedPartitionSeries N hq)
      (summable_norm_geometricCoefficient (Nat.succ_pos N) hq) ih
      (hasSum_geometricCoefficient (Nat.succ_pos N) hq)

/-- The actual bounded-partition coefficient series is absolutely summable. -/
theorem summable_norm_boundedPartitionCount (N : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun n => ‖(boundedPartitionCount N n : ℂ) * q ^ n‖) := by
  simpa only [coeff_boundedPartitionSeries, Int.cast_natCast] using
    summable_norm_boundedPartitionSeries N hq

/-- Actual bounded-partition counts sum to the finite inverse Euler product,
including the empty product at cutoff zero. -/
theorem hasSum_boundedPartitionCount (N : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n => (boundedPartitionCount N n : ℂ) * q ^ n)
      (∏ i ∈ Finset.range N, (1 - q ^ (i + 1))⁻¹) := by
  simpa only [coeff_boundedPartitionSeries, Int.cast_natCast] using
    hasSum_boundedPartitionSeries N hq

end SptClassification.QSeries
