/- Assembled by AxiomProver. -/

module

public import SptClassification.Partitions.CoefficientTable

/-!
# Recovering smallest-parts coefficients from the restricted partition table

The smallest part and its positive multiplicity give a finite sum over restricted
partition coefficients. Substitution of the checked degree-87 table yields an
efficient evaluator for the manuscript's finite coefficient range.
-/

public section

namespace SptClassification.QSeries

open PowerSeries
open scoped PowerSeries.WithPiTopology

/-- Coefficients obtained by fixing a least part and its multiplicity. -/
theorem coeff_minimumSeries_eq_tail_sum {m : ℕ} (hm : 0 < m) (n : ℕ) :
    (minimumSeries m).coeff n =
      ∑ j ∈ Finset.range n, ((j + 1 : ℕ) : ℤ) *
        if m * (j + 1) ≤ n then
          (restrictedPartitionSeries (m + 1)).coeff (n - m * (j + 1)) else 0 := by
  have hs : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℤ) •
      (X : PowerSeries ℤ) ^ (m * (j + 1))) :=
    Nat.Partition.summable_genFun_term' (fun _ c => (c : ℤ)) hm.ne'
  have hsum := hs.hasSum.mul_right (restrictedPartitionSeries (m + 1))
  change HasSum _ (weightedGeometricSeries m * restrictedPartitionSeries (m + 1)) at hsum
  have hlimit : weightedGeometricSeries m * restrictedPartitionSeries (m + 1) =
      minimumSeries m := (minimumSeries_eq_weightedGeometric_mul_restricted hm).symm
  rw [hlimit] at hsum
  have hc := (WithPiTopology.hasSum_iff_hasSum_coeff ℤ).mp hsum n
  let F : ℕ → ℤ := fun j =>
    (((((j + 1 : ℕ) : ℤ) • (X : PowerSeries ℤ) ^ (m * (j + 1))) *
      restrictedPartitionSeries (m + 1)).coeff n)
  change HasSum F ((minimumSeries m).coeff n) at hc
  have hzero : ∀ j ∉ Finset.range n, F j = 0 := by
    intro j hj
    have hnj : n ≤ j := by simpa only [Finset.mem_range, not_lt] using hj
    have hdegree : ¬m * (j + 1) ≤ n := by nlinarith
    dsimp only [F]
    rw [smul_mul_assoc, map_zsmul]
    simp only [zsmul_eq_mul, Int.cast_id, PowerSeries.coeff_X_pow_mul',
      ite_eq_right hdegree, mul_zero]
  calc
    (minimumSeries m).coeff n = ∑' j : ℕ, F j := hc.tsum_eq.symm
    _ = ∑ j ∈ Finset.range n, F j := tsum_eq_sum hzero
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [F]
      rw [smul_mul_assoc, map_zsmul]
      simp only [zsmul_eq_mul, Int.cast_id, PowerSeries.coeff_X_pow_mul']

/-- The finite smallest-part/multiplicity formula for the genuine statistic. -/
theorem spt_eq_sum_restricted_coefficients (n : ℕ) :
    (spt n : ℤ) =
      ∑ m ∈ Finset.Icc 1 n, ∑ j ∈ Finset.range n, ((j + 1 : ℕ) : ℤ) *
        if m * (j + 1) ≤ n then
          (restrictedPartitionSeries (m + 1)).coeff (n - m * (j + 1)) else 0 := by
  rw [← coeff_sptSeries n, ← sum_coeff_minimumSeries n]
  apply Finset.sum_congr rfl
  intro m hm
  exact coeff_minimumSeries_eq_tail_sum (Finset.mem_Icc.mp hm).1 n

/-- The smallest-parts value read from the checked degree-87 restricted table. -/
def sptTableCandidate (n : ℕ) : ℤ :=
  ∑ m ∈ Finset.Icc 1 n, ∑ j ∈ Finset.range n, ((j + 1 : ℕ) : ℤ) *
    if m * (j + 1) ≤ n then partitionTailCandidate 87 (m + 1) (n - m * (j + 1)) else 0

/-- The bounded table evaluator equals the actual smallest-parts function. -/
theorem spt_eq_tableCandidate {n : ℕ} (hn : n ≤ 87) : (spt n : ℤ) = sptTableCandidate n := by
  rw [spt_eq_sum_restricted_coefficients, sptTableCandidate]
  apply Finset.sum_congr rfl
  intro m hm
  have hm' := Finset.mem_Icc.mp hm
  apply Finset.sum_congr rfl
  intro j _
  split_ifs
  · rw [partitionTailCertificate_correct (by omega) (by omega) (by omega)]
  · rfl

/-- The coefficient values through index 87 used in the finite congruence calculation. -/
@[expose] def sptCoefficientValues : List ℕ :=
  [0, 1, 3, 5, 10, 14, 26, 35,
   57, 80, 119, 161, 238, 315, 440, 589,
   801, 1048, 1407, 1820, 2399, 3087, 3998, 5092,
   6545, 8263, 10486, 13165, 16562, 20630, 25773, 31897,
   39546, 48692, 59960, 73423, 89937, 109553, 133439, 161840,
   196168, 236843, 285816, 343667, 412950, 494702, 592063, 706671,
   842749, 1002435, 1191282, 1412543, 1673196, 1977864, 2335760, 2753091,
   3241818, 3810641, 4474756, 5246120, 6144561, 7185780, 8395439, 9794939,
   11416820, 13289625, 15455445, 17951601, 20832168, 24146510, 27963340, 32347380,
   37386792, 43165216, 49795175, 57385734, 66079291, 76016857, 87379833, 100348950,
   115154394, 132028382, 151261320, 173150428, 198063060, 226376867, 258555197, 295078787]

theorem sptCoefficientValues_length : sptCoefficientValues.length = 88 := by
  decide +kernel

/-- The complete bounded coefficient list is verified by kernel reduction. -/
theorem sptTableCandidate_values : ∀ n : Fin 88,
    sptTableCandidate n.val = ((sptCoefficientValues[n.val]?).getD 0 : ℤ) := by
  decide +kernel

/-- Every entry of the finite coefficient list is the genuine smallest-parts value. -/
theorem spt_eq_coefficientValues {n : ℕ} (hn : n ≤ 87) :
    spt n = (sptCoefficientValues[n]?).getD 0 := by
  have h := (spt_eq_tableCandidate hn).trans (sptTableCandidate_values ⟨n, by omega⟩)
  exact_mod_cast h

end SptClassification.QSeries
