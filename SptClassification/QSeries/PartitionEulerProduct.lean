/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.BoundedPartitionAnalytic
public import SptClassification.QSeries.AnalyticEulerProduct
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The convergent partition Euler product

Finite bounded-partition products bound every real partial sum of the partition
series. This proves absolute convergence on the unit disc. Dominated convergence
then identifies the analytic sum with the inverse Euler product. The argument
supplies the partition component of the eta/j Fourier bridge in
[rolenManuscript, §3], without a partition-growth asymptotic.
-/

public section

namespace SptClassification.QSeries

open Filter
open scoped Topology

/-- Real partition partial sums are bounded by the inverse analytic Euler
product. The argument includes `r = 0`. -/
theorem partition_partialSum_le_inverseEuler {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (L : ℕ) :
    ∑ n ∈ Finset.range L, (partitionCount n : ℝ) * r ^ n ≤
      ((etaEulerProduct (r : ℂ))⁻¹).re := by
  have hq : ‖(r : ℂ)‖ < 1 := by simpa [abs_of_nonneg hr] using hr1
  apply ge_of_tendsto ((Complex.continuous_re.tendsto _).comp
    (tendsto_inverseEulerProducts hq))
  filter_upwards [eventually_ge_atTop L] with N hN
  have hs := Complex.hasSum_re (hasSum_boundedPartitionCount N hq)
  have hs' : HasSum (fun n => (boundedPartitionCount N n : ℝ) * r ^ n)
      (∏ i ∈ Finset.range N, (1 - (r : ℂ) ^ (i + 1))⁻¹).re := by
    simpa [← Complex.ofReal_pow] using hs
  calc
    ∑ n ∈ Finset.range L, (partitionCount n : ℝ) * r ^ n =
        ∑ n ∈ Finset.range L, (boundedPartitionCount N n : ℝ) * r ^ n := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnN : n ≤ N := (Nat.le_of_lt (Finset.mem_range.mp hn)).trans hN
      rw [boundedPartitionCount_eq hnN]
    _ ≤ _ := sum_le_hasSum _ (fun n _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr n)) hs'

/-- Nonnegative real partition series converge everywhere below one. -/
theorem summable_partitionCount_real {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n => (partitionCount n : ℝ) * r ^ n) :=
  summable_of_sum_range_le (fun n => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr n))
    (partition_partialSum_le_inverseEuler hr hr1)

/-- The actual partition generating series is absolutely convergent on the
complex unit disc. -/
theorem summable_norm_partitionCount {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun n => ‖(partitionCount n : ℂ) * q ^ n‖) := by
  simpa [norm_mul, norm_pow] using summable_partitionCount_real (norm_nonneg q) hq

/-- Bounded-partition analytic sums approach the ordinary partition sum. -/
theorem tendsto_boundedPartition_tsum {q : ℂ} (hq : ‖q‖ < 1) :
    Tendsto (fun N => ∑' n, (boundedPartitionCount N n : ℂ) * q ^ n) atTop
      (𝓝 (∑' n, (partitionCount n : ℂ) * q ^ n)) := by
  apply tendsto_tsum_of_dominated_convergence (summable_norm_partitionCount hq)
  · intro n
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop n] with N hN
    simp [boundedPartitionCount_eq hN]
  · apply Eventually.of_forall
    intro N n
    simp only [norm_mul, norm_pow, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast boundedPartitionCount_le N n)
      (pow_nonneg (norm_nonneg q) n)

/-- The actual partition coefficients sum to the inverse analytic Euler
product throughout the unit disc. -/
theorem hasSum_partitionCount_inverseEuler {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n => (partitionCount n : ℂ) * q ^ n) (etaEulerProduct q)⁻¹ := by
  have ht := tendsto_boundedPartition_tsum hq
  simp only [(hasSum_boundedPartitionCount _ hq).tsum_eq] at ht
  have he := tendsto_nhds_unique ht (tendsto_inverseEulerProducts hq)
  exact he ▸ (summable_norm_partitionCount hq).of_norm.hasSum

end SptClassification.QSeries
