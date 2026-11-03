/- Assembled by AxiomProver. -/

module

public import SptClassification.Partitions.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Coefficient growth of the partition and smallest-parts series

The classical Hardy–Ramanujan asymptotic for the partition function gives the
coarse coefficient estimate below. The passage from partitions to the actual
smallest-parts statistic uses its defining finite sum, not a second literature
input. The analytic use of these estimates is in `ScaledGeneratingGrowth`.
-/

public section

namespace SptClassification

/-- Coarse consequence of Hardy and Ramanujan's partition asymptotic
`p(n) ∼ exp (π * sqrt (2*n/3)) / (4*n*sqrt 3)` as `n → ∞`:
"Asymptotic formulae in combinatory analysis" (1918), Introduction, displayed
leading asymptotic for `p(n)` [hardyRamanujan1918]. This is the sole literature
admission in this module. Its constants are existential because only their
positivity matters for the manuscript's cusp-growth argument. -/
theorem hardyRamanujan_partitionCount_growth :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧
      ∀ n : ℕ, (partitionCount n : ℝ) ≤ C * Real.exp (B * Real.sqrt n) := by
  sorry

/-- A polynomial factor can be absorbed into a slightly faster square-root
exponential. -/
theorem natCast_le_exp_two_sqrt (n : ℕ) :
    (n : ℝ) ≤ Real.exp (2 * Real.sqrt n) := by
  have hs : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt (n : ℝ)) ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg _)
  have he : 1 + Real.sqrt (n : ℝ) ≤ Real.exp (Real.sqrt n) := by
    simpa [add_comm] using Real.add_one_le_exp (Real.sqrt (n : ℝ))
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (1 : ℝ) + Real.sqrt n) he 2
  have hleft : (n : ℝ) ≤ (1 + Real.sqrt n) ^ 2 := by nlinarith
  calc
    (n : ℝ) ≤ (1 + Real.sqrt n) ^ 2 := hleft
    _ ≤ Real.exp (Real.sqrt n) ^ 2 := hpow
    _ = Real.exp (2 * Real.sqrt n) := by rw [← Real.exp_nat_mul]; ring

/-- Both actual coefficient sequences have the same square-root exponential
growth type. This follows from the classical partition estimate and the proved
inequality `spt(n) ≤ n p(n)`. -/
theorem exists_partition_spt_coefficient_growth :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧
      (∀ n : ℕ, (partitionCount n : ℝ) ≤ C * Real.exp (B * Real.sqrt n)) ∧
      (∀ n : ℕ, (spt n : ℝ) ≤ C * Real.exp (B * Real.sqrt n)) := by
  obtain ⟨C, B, hC, hB, hp⟩ := hardyRamanujan_partitionCount_growth
  refine ⟨C, B + 2, hC, by positivity, ?_, ?_⟩
  · intro n
    have hs : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
    calc
      (partitionCount n : ℝ) ≤ C * Real.exp (B * Real.sqrt n) := hp n
      _ ≤ C * Real.exp ((B + 2) * Real.sqrt n) := by
        apply mul_le_mul_of_nonneg_left _ hC.le
        apply Real.exp_le_exp.mpr
        nlinarith
  · intro n
    have hs : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
    have hnp : (spt n : ℝ) ≤ (n : ℝ) * partitionCount n := by
      exact_mod_cast spt_le_mul_partitionCount n
    calc
      (spt n : ℝ) ≤ (n : ℝ) * partitionCount n := hnp
      _ ≤ Real.exp (2 * Real.sqrt n) * (C * Real.exp (B * Real.sqrt n)) := by
        gcongr
        · exact natCast_le_exp_two_sqrt n
        · exact hp n
      _ = C * Real.exp ((B + 2) * Real.sqrt n) := by
        rw [mul_left_comm, ← Real.exp_add]
        congr 1
        ring

end SptClassification
