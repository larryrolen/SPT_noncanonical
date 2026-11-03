/- Assembled by AxiomProver. -/

module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

/-!
# Convergent products of integral coefficient series

Absolute convergence permits multiplication of the analytic sums, with precisely
the coefficients of the formal product. We use this finite Cauchy-product step
for the partition Euler product in [rolenManuscript, §3].
-/

public section

namespace SptClassification.QSeries

/-- Multiplication by a power of the nome shifts a convergent Fourier row,
with zero coefficients before the new pole-clearing index. -/
theorem hasSum_shifted_powers (s : ℕ) (a : ℕ → ℂ) (z L : ℂ)
    (hs : HasSum (fun k : ℕ => a k * z ^ k) L) :
    HasSum (fun j : ℕ =>
      if s ≤ j then a (j - s) * z ^ j else 0) (z ^ s * L) := by
  let g : ℕ → ℂ := fun j =>
    if s ≤ j then a (j - s) * z ^ j else 0
  have hinj : Function.Injective (fun k : ℕ => s + k) := by
    intro x y hxy
    exact Nat.add_left_cancel hxy
  have hout : ∀ j, j ∉ Set.range (fun k : ℕ => s + k) → g j = 0 := by
    intro j hj
    have hlt : ¬ s ≤ j := by
      intro hle
      apply hj
      exact ⟨j - s, Nat.add_sub_of_le hle⟩
    simp [g, hlt]
  apply (hinj.hasSum_iff hout).mp
  have hterm (k : ℕ) :
      g (s + k) = z ^ s * (a k * z ^ k) := by
    have hle : s ≤ s + k := Nat.le_add_right s k
    have hsub : s + k - s = k := by omega
    simp only [g, if_pos hle, hsub, pow_add]
    ring
  simpa only [Function.comp_def, hterm] using hs.mul_left (z ^ s)

/-- Evaluated coefficients of a product are the Cauchy convolution of the
evaluated coefficients of its factors. -/
theorem coefficientTerm_mul (F G : PowerSeries ℤ) (q : ℂ) (n : ℕ) :
    ((F * G).coeff n : ℂ) * q ^ n =
      ∑ p ∈ Finset.antidiagonal n,
        ((F.coeff p.1 : ℂ) * q ^ p.1) * ((G.coeff p.2 : ℂ) * q ^ p.2) := by
  rw [PowerSeries.coeff_mul]
  simp only [Int.cast_sum, Int.cast_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.mem_antidiagonal.mp hp, pow_add]
  ring

/-- Absolute convergence is preserved by the formal product. -/
theorem summable_norm_coefficientTerm_mul (F G : PowerSeries ℤ) (q : ℂ)
    (hF : Summable (fun n => ‖(F.coeff n : ℂ) * q ^ n‖))
    (hG : Summable (fun n => ‖(G.coeff n : ℂ) * q ^ n‖)) :
    Summable (fun n => ‖((F * G).coeff n : ℂ) * q ^ n‖) := by
  simpa only [coefficientTerm_mul] using
    summable_norm_sum_mul_antidiagonal_of_summable_norm hF hG

/-- The analytic sum of a formal product is the product of the analytic sums
when both coefficient series converge absolutely. -/
theorem hasSum_coefficientTerm_mul (F G : PowerSeries ℤ) (q a b : ℂ)
    (hF : Summable (fun n => ‖(F.coeff n : ℂ) * q ^ n‖))
    (hG : Summable (fun n => ‖(G.coeff n : ℂ) * q ^ n‖))
    (ha : HasSum (fun n => (F.coeff n : ℂ) * q ^ n) a)
    (hb : HasSum (fun n => (G.coeff n : ℂ) * q ^ n) b) :
    HasSum (fun n => ((F * G).coeff n : ℂ) * q ^ n) (a * b) := by
  have h := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hF hG
  rw [ha.tsum_eq, hb.tsum_eq] at h
  simpa only [coefficientTerm_mul, ← h] using
    (summable_norm_coefficientTerm_mul F G q hF hG).of_norm.hasSum

end SptClassification.QSeries
