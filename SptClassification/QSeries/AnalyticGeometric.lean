/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.Geometric
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Complex.Basic

/-!
# Analytic evaluation of the formal geometric factors

For a positive part size, the formal geometric series has coefficient one at
its multiples and zero elsewhere. Its coefficient series converges absolutely
on the unit disc to the ordinary geometric factor. This supplies a factor in
the finite partition product used in [rolenManuscript, §3].
-/

public section

namespace SptClassification.QSeries

open PowerSeries
open scoped PowerSeries.WithPiTopology

/-- Geometric coefficients select exactly the multiples of the part size. -/
theorem coeff_geometricSeries {m : ℕ} (hm : 0 < m) (n : ℕ) :
    (geometricSeries m).coeff n = if m ∣ n then 1 else 0 := by
  rw [geometricSeries_eq_tsum, (summable_geometricSeries hm).map_tsum _
    (WithPiTopology.continuous_coeff _ _)]
  simp only [← pow_mul, coeff_X_pow]
  by_cases hd : m ∣ n
  · rw [ite_eq_left hd]
    obtain ⟨k, rfl⟩ := hd
    rw [tsum_eq_single k]
    · simp
    · intro r hr
      have h : m * k ≠ m * r := by
        intro he
        apply hr
        nlinarith
      simp [h]
  · rw [ite_eq_right hd]
    have h : ∀ r : ℕ, n ≠ m * r := fun r he => hd ⟨r, he⟩
    simp [h]

/-- Each geometric factor has an absolutely convergent coefficient series on
the open unit disc. -/
theorem summable_norm_geometricCoefficient {m : ℕ} (hm : 0 < m)
    {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun n => ‖((geometricSeries m).coeff n : ℂ) * q ^ n‖) := by
  apply (summable_geometric_of_lt_one (norm_nonneg q) hq).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro n
  by_cases hd : m ∣ n <;> simp [coeff_geometricSeries hm, hd, norm_pow]

/-- The analytic sum of the formal geometric coefficients is the expected
inverse factor, including at `q = 0`. -/
theorem hasSum_geometricCoefficient {m : ℕ} (hm : 0 < m)
    {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n => ((geometricSeries m).coeff n : ℂ) * q ^ n) (1 - q ^ m)⁻¹ := by
  have hi : Function.Injective (fun r : ℕ => m * r) := by
    intro a b hab
    nlinarith
  have hz : ∀ n, n ∉ Set.range (fun r : ℕ => m * r) →
      ((geometricSeries m).coeff n : ℂ) * q ^ n = 0 := by
    intro n hn
    have hd : ¬ m ∣ n := by
      rintro ⟨r, hr⟩
      exact hn ⟨r, hr.symm⟩
    simp [coeff_geometricSeries hm, hd]
  apply (hi.hasSum_iff hz).mp
  have hqm : ‖q ^ m‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq hm.ne'
  simpa [Function.comp_def, coeff_geometricSeries hm, pow_mul] using
    hasSum_geometric_of_norm_lt_one hqm

end SptClassification.QSeries
