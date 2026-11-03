/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.LevelSixEtaQuotient
public import Mathlib.Tactic.Ring

/-!
# Translation of eta and the level-six quotient

The defining exponential product gives the integer translation multiplier of
eta. The exponents of the level-six quotient make the total multiplier one.
-/

public section

namespace SptClassification

theorem qParam_add_eq_mul (h : ℝ) (z w : ℂ) :
    Function.Periodic.qParam h (z + w) =
      Function.Periodic.qParam h z * Function.Periodic.qParam h w := by
  simp [Function.Periodic.qParam, mul_add, add_div, Complex.exp_add]

theorem qParam_one_int (n : ℤ) : Function.Periodic.qParam 1 n = 1 := by
  simpa [Function.Periodic.qParam, mul_comm] using Complex.exp_int_mul_two_pi_mul_I n

/-- The integer translation multiplier of the actual Dedekind eta product. -/
theorem eta_add_int (z : ℂ) (n : ℤ) :
    ModularForm.eta (z + n) =
      Complex.exp (Real.pi * Complex.I * n / 12) * ModularForm.eta z := by
  have hq : Function.Periodic.qParam 1 (z + n) = Function.Periodic.qParam 1 z := by
    rw [qParam_add_eq_mul, qParam_one_int, mul_one]
  have he : Function.Periodic.qParam 24 n =
      Complex.exp (Real.pi * Complex.I * n / 12) := by
    unfold Function.Periodic.qParam
    congr 1
    norm_num
    ring
  simp only [ModularForm.eta, ModularForm.eta_q, hq, qParam_add_eq_mul, he]
  ring

/-- The exact eta quotient has period one. -/
theorem levelSixEtaQuotient_add_one (z : ℂ) :
    levelSixEtaQuotient (z + 1) = levelSixEtaQuotient z := by
  have h1 := eta_add_int z 1
  have h2 := eta_add_int (2 * z) 2
  have h3 := eta_add_int (3 * z) 3
  have h6 := eta_add_int (6 * z) 6
  norm_num only [Int.cast_one, Int.cast_ofNat, mul_one] at h1 h2 h3 h6
  have hphase :
      (Complex.exp (Real.pi * Complex.I / 12) ^ 5 *
          Complex.exp (Real.pi * Complex.I * 3 / 12)) /
        (Complex.exp (Real.pi * Complex.I * 2 / 12) *
          Complex.exp (Real.pi * Complex.I * 6 / 12) ^ 5) = 1 := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
      ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_sub]
    norm_num only [Nat.cast_ofNat]
    have he : (5 : ℂ) * (Real.pi * Complex.I / 12) + Real.pi * Complex.I * 3 / 12 -
        (Real.pi * Complex.I * 2 / 12 + 5 * (Real.pi * Complex.I * 6 / 12)) =
        -(2 * Real.pi * Complex.I) := by ring
    rw [he, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]
  rw [levelSixEtaQuotient_eq, levelSixEtaQuotient_eq]
  rw [show 2 * (z + 1) = 2 * z + 2 by ring,
    show 3 * (z + 1) = 3 * z + 3 by ring,
    show 6 * (z + 1) = 6 * z + 6 by ring, h1, h2, h3, h6]
  calc
    _ = ((Complex.exp (Real.pi * Complex.I / 12) ^ 5 *
          Complex.exp (Real.pi * Complex.I * 3 / 12)) /
        (Complex.exp (Real.pi * Complex.I * 2 / 12) *
          Complex.exp (Real.pi * Complex.I * 6 / 12) ^ 5)) *
        (ModularForm.eta z ^ 5 * ModularForm.eta (3 * z) /
          (ModularForm.eta (2 * z) * ModularForm.eta (6 * z) ^ 5)) := by
      simp only [mul_pow, div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by rw [hphase, one_mul]

end SptClassification
