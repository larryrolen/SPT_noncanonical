/- Assembled by AxiomProver. -/

module

public import Mathlib.Analysis.RCLike.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-! # Principal square roots in the upper half-plane -/

public section

namespace SptClassification

/-- Squaring the principal complex square root recovers its argument. -/
theorem complex_sqrt_sq (z : ℂ) : z.sqrt ^ 2 = z := by
  rw [Complex.sqrt, ← Complex.cpow_nat_mul]
  norm_num

theorem complex_sqrt_re_nonneg (z : ℂ) : 0 ≤ z.sqrt.re := by
  rw [Complex.sqrt, Complex.cpow_inv_two_re]
  exact Real.sqrt_nonneg _

/-- A number in the upper half-plane has its principal square root in the first quadrant. -/
theorem complex_sqrt_re_im_pos {z : ℂ} (hz : 0 < z.im) :
    0 < z.sqrt.re ∧ 0 < z.sqrt.im := by
  have hnonneg := complex_sqrt_re_nonneg z
  have hsq := congrArg Complex.im (complex_sqrt_sq z)
  simp only [pow_two, Complex.mul_im] at hsq
  have hre : 0 < z.sqrt.re := by
    by_contra h
    have heq : z.sqrt.re = 0 := le_antisymm (le_of_not_gt h) hnonneg
    rw [heq] at hsq
    simp only [zero_mul, mul_zero, add_zero] at hsq
    linarith
  have hmul : 0 < z.sqrt.re * z.sqrt.im := by nlinarith
  exact ⟨hre, pos_of_mul_pos_right hmul hre.le⟩

/-- The square root with positive real part is the principal root. -/
theorem eq_complex_sqrt_of_sq_eq {w z : ℂ} (hsq : w ^ 2 = z) (hw : 0 < w.re) :
    w = z.sqrt := by
  have hfactor : (w - z.sqrt) * (w + z.sqrt) = 0 := by
    linear_combination hsq - complex_sqrt_sq z
  rcases mul_eq_zero.mp hfactor with h | h
  · exact sub_eq_zero.mp h
  · have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.zero_re] at hre
    linarith [complex_sqrt_re_nonneg z]

/-- A positive natural square scales the principal root of an upper-half-plane
argument by that natural number. -/
theorem complex_sqrt_nat_square_mul (n : ℕ) (hn : 0 < n) {z : ℂ}
    (hz : 0 < z.im) :
    (((n * n : ℕ) : ℂ) * z).sqrt = (n : ℂ) * z.sqrt := by
  symm
  apply eq_complex_sqrt_of_sq_eq
  · rw [mul_pow, complex_sqrt_sq]
    push_cast
    ring
  · rw [Complex.mul_re]
    simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
    exact mul_pos (Nat.cast_pos.mpr hn) (complex_sqrt_re_im_pos hz).1

/-- A positive natural dilation scales the principal root on the upper
half-plane by its positive real square root. -/
theorem complex_sqrt_nat_mul (n : ℕ) (hn : 0 < n) {z : ℂ}
    (hz : 0 < z.im) :
    ((n : ℂ) * z).sqrt = ((Real.sqrt n : ℝ) : ℂ) * z.sqrt := by
  symm
  apply eq_complex_sqrt_of_sq_eq
  · rw [mul_pow, complex_sqrt_sq]
    simp only [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    norm_cast
  · rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_pos (Real.sqrt_pos.2 (Nat.cast_pos.mpr hn))
      (complex_sqrt_re_im_pos hz).1

/-- The two inversion square roots combine with their exact principal-branch sign. -/
theorem complex_sqrt_inversion_product {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    -Complex.I * w.sqrt * z.sqrt = (-w * z).sqrt := by
  apply eq_complex_sqrt_of_sq_eq
  · simp only [mul_pow, neg_sq, Complex.I_sq, complex_sqrt_sq]
    ring
  · obtain ⟨hzr, hzi⟩ := complex_sqrt_re_im_pos hz
    obtain ⟨hwr, hwi⟩ := complex_sqrt_re_im_pos hw
    simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re,
      Complex.I_re, Complex.I_im, zero_mul, neg_mul, one_mul, zero_sub, zero_add]
    nlinarith [mul_pos hwr hzi, mul_pos hwi hzr]

/-- The two principal roots at an upper-half-plane point and its inversion
have product `i`; this fixes the branch sign in eta calculations. -/
theorem complex_sqrt_neg_inv_mul {z : ℂ} (hz : 0 < z.im) :
    (-1 / z).sqrt * z.sqrt = Complex.I := by
  have hz0 : z ≠ 0 := by
    intro h
    simp only [h, Complex.zero_im] at hz
    exact (lt_irrefl 0 hz).elim
  have hw : 0 < (-1 / z).im := by
    simp only [neg_div, one_div, Complex.neg_im, Complex.inv_im, neg_neg]
    exact div_pos hz (Complex.normSq_pos.mpr hz0)
  have hprod : -(-1 / z) * z = 1 := by
    field_simp [hz0]
  have hroot := complex_sqrt_inversion_product hz hw
  rw [hprod, Complex.sqrt_one] at hroot
  calc
    (-1 / z).sqrt * z.sqrt =
        (Complex.I * -Complex.I) * ((-1 / z).sqrt * z.sqrt) := by
          simp [Complex.I_sq]
    _ = Complex.I * (-Complex.I * (-1 / z).sqrt * z.sqrt) := by ring
    _ = Complex.I := by rw [hroot]; ring

/-- A lower-half-plane argument has its principal root in the fourth quadrant. -/
theorem complex_sqrt_re_pos_im_neg {z : ℂ} (hz : z.im < 0) :
    0 < z.sqrt.re ∧ z.sqrt.im < 0 := by
  have hnonneg := complex_sqrt_re_nonneg z
  have hsq := congrArg Complex.im (complex_sqrt_sq z)
  simp only [pow_two, Complex.mul_im] at hsq
  have hre : 0 < z.sqrt.re := by
    by_contra h
    have heq : z.sqrt.re = 0 := le_antisymm (le_of_not_gt h) hnonneg
    rw [heq] at hsq
    simp only [zero_mul, mul_zero, add_zero] at hsq
    linarith
  have him : z.sqrt.im < 0 := by
    by_contra h
    have hm := mul_nonneg hre.le (le_of_not_gt h)
    nlinarith
  exact ⟨hre, him⟩

/-- Principal roots multiply without a sign correction for arguments in opposite
open half-planes. -/
theorem complex_sqrt_mul_opposite {z w : ℂ} (hz : z.im < 0) (hw : 0 < w.im) :
    z.sqrt * w.sqrt = (z * w).sqrt := by
  apply eq_complex_sqrt_of_sq_eq
  · rw [mul_pow, complex_sqrt_sq, complex_sqrt_sq]
  · obtain ⟨hzr, hzi⟩ := complex_sqrt_re_pos_im_neg hz
    obtain ⟨hwr, hwi⟩ := complex_sqrt_re_im_pos hw
    rw [Complex.mul_re]
    nlinarith [mul_pos hzr hwr, mul_neg_of_neg_of_pos hzi hwi]

end SptClassification
