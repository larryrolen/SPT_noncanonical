/- Assembled by AxiomProver. -/

module

public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
public import SptClassification.Arithmetic.QuadraticTwist

/-!
# Finite translation filters

Fourier inversion realizes a residue selector as a finite linear combination
of rational translates. The same operator acts on Fourier terms with arbitrary
imaginary-part dependence, so it also removes the negative-square shadow in
[rolenManuscript, §2]. No modular transformation law is assumed here.
-/

public section

namespace SptClassification

open UpperHalfPlane

/-- Translation by the standard representative of `j/N`. -/
noncomputable def fourierTranslate {N : ℕ} [NeZero N] (j : ZMod N)
    (τ : UpperHalfPlane) : UpperHalfPlane :=
  ⟨(τ : ℂ) + (j.val : ℝ) / N, by simpa using τ.im_pos⟩

@[simp] theorem fourierTranslate_coe {N : ℕ} [NeZero N] (j : ZMod N)
    (τ : UpperHalfPlane) :
    (fourierTranslate j τ : ℂ) = (τ : ℂ) + (j.val : ℝ) / N := (rfl)

@[simp] theorem fourierTranslate_im {N : ℕ} [NeZero N] (j : ZMod N)
    (τ : UpperHalfPlane) : (fourierTranslate j τ).im = τ.im := by
  simp [fourierTranslate]

/-- The normalized discrete Fourier transform of a residue multiplier. -/
noncomputable def fourierFilterKernel {N : ℕ} [NeZero N]
    (c : ZMod N → ℂ) (j : ZMod N) : ℂ :=
  (N : ℂ)⁻¹ * ZMod.dft c j

theorem fourierFilterKernel_eq {N : ℕ} [NeZero N]
    (c : ZMod N → ℂ) (j : ZMod N) :
    fourierFilterKernel c j = (N : ℂ)⁻¹ * ZMod.dft c j := (rfl)

/-- The finite translation operator with the prescribed residue multiplier. -/
noncomputable def fourierFilter {N : ℕ} [NeZero N] (c : ZMod N → ℂ)
    (F : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) : ℂ :=
  ∑ j : ZMod N, fourierFilterKernel c j * F (fourierTranslate j τ)

theorem fourierFilter_apply {N : ℕ} [NeZero N] (c : ZMod N → ℂ)
    (F : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    fourierFilter c F τ =
      ∑ j : ZMod N, fourierFilterKernel c j * F (fourierTranslate j τ) := (rfl)

/-- A uniform bound depending only on height survives the finite filter.
The constant is the sum of the absolute kernel coefficients; in particular
the exponential rate of any height bound is unchanged. -/
theorem norm_fourierFilter_le_of_height_bound
    {N : ℕ} [NeZero N] (c : ZMod N → ℂ)
    (F : UpperHalfPlane → ℂ) (B : ℝ → ℝ)
    (hF : ∀ τ : UpperHalfPlane, ‖F τ‖ ≤ B τ.im) (τ : UpperHalfPlane) :
    ‖fourierFilter c F τ‖ ≤
      (∑ j : ZMod N, ‖fourierFilterKernel c j‖) * B τ.im := by
  rw [fourierFilter_apply, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  simpa only [fourierTranslate_im] using hF (fourierTranslate j τ)

/-- The finite translation operator respects addition. -/
theorem fourierFilter_add {N : ℕ} [NeZero N] (c : ZMod N → ℂ)
    (F G : UpperHalfPlane → ℂ) :
    fourierFilter c (F + G) = fourierFilter c F + fourierFilter c G := by
  funext τ
  simp only [fourierFilter, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- The finite translation operator commutes with constant scaling. -/
theorem fourierFilter_const_mul {N : ℕ} [NeZero N] (c : ZMod N → ℂ)
    (z : ℂ) (F : UpperHalfPlane → ℂ) :
    fourierFilter c (fun τ => z * F τ) = fun τ => z * fourierFilter c F τ := by
  funext τ
  simp only [fourierFilter, Finset.mul_sum, mul_left_comm]

/-- Fourier inversion determines the multiplier on every Fourier mode. -/
theorem fourierFilterKernel_sum {N : ℕ} [NeZero N]
    (c : ZMod N → ℂ) (n : ZMod N) :
    (∑ j : ZMod N, fourierFilterKernel c j * ZMod.stdAddChar (j * n)) = c n := by
  have h := congrFun (ZMod.dft.symm_apply_apply c) n
  rw [ZMod.invDFT_apply] at h
  simpa only [fourierFilterKernel, smul_eq_mul, Finset.mul_sum,
    mul_left_comm, mul_comm, mul_assoc] using h

/-- A rational translate changes the q-parameter by the standard additive
character; the imaginary part is unchanged. -/
theorem qParam_fourierTranslate {N : ℕ} [NeZero N] (j : ZMod N)
    (τ : UpperHalfPlane) :
    Function.Periodic.qParam 1 (fourierTranslate j τ) =
      ZMod.stdAddChar j * Function.Periodic.qParam 1 τ := by
  have hj : ZMod.stdAddChar j =
      Complex.exp (2 * Real.pi * Complex.I * j.val / N) := by
    simpa using (ZMod.stdAddChar_coe (N := N) (j.val : ℤ))
  rw [hj]
  simp only [Function.Periodic.qParam, fourierTranslate_coe, Complex.ofReal_one,
    div_one, Complex.ofReal_div, Complex.ofReal_natCast]
  rw [← Complex.exp_add]
  congr 1
  ring

/-- The same phase formula holds for negative Fourier indices. -/
theorem qParam_fourierTranslate_zpow {N : ℕ} [NeZero N] (j : ZMod N)
    (τ : UpperHalfPlane) (n : ℤ) :
    Function.Periodic.qParam 1 (fourierTranslate j τ) ^ n =
      ZMod.stdAddChar (j * (n : ZMod N)) * Function.Periodic.qParam 1 τ ^ n := by
  rw [qParam_fourierTranslate, mul_zpow, ← AddChar.map_zsmul_eq_zpow]
  simp only [zsmul_eq_mul, mul_comm]

/-- Filtering a convergent Fourier expansion commutes with summation. The
terms may depend nonholomorphically on the imaginary part. -/
theorem fourierFilter_hasSum {N : ℕ} [NeZero N] {ι : Type*}
    (c : ZMod N → ℂ) (F : UpperHalfPlane → ℂ)
    (term : ι → UpperHalfPlane → ℂ) (freq : ι → ℤ)
    (hF : ∀ τ, HasSum (fun i => term i τ) (F τ))
    (hterm : ∀ i j τ, term i (fourierTranslate (N := N) j τ) =
      ZMod.stdAddChar (j * (freq i : ZMod N)) * term i τ)
    (τ : UpperHalfPlane) :
    HasSum (fun i => c (freq i) * term i τ) (fourierFilter c F τ) := by
  have h := hasSum_sum (s := Finset.univ) (fun j _ =>
    (hF (fourierTranslate j τ)).mul_left (fourierFilterKernel c j))
  apply h.congr
  intro i
  simp only [hterm, ← mul_assoc, ← Finset.sum_mul, fourierFilterKernel_sum]

/-- Fourier coefficients of the finite translation operator. -/
theorem fourierFilter_qExpansion {N : ℕ} [NeZero N]
    (c : ZMod N → ℂ) (F : UpperHalfPlane → ℂ) (a : ℤ → ℂ)
    (hF : ∀ (τ : UpperHalfPlane), HasSum (fun n => a n * Function.Periodic.qParam 1 τ ^ n) (F τ))
    (τ : UpperHalfPlane) :
    HasSum (fun (n : ℤ) => (c (n : ZMod N) * a n) * Function.Periodic.qParam 1 τ ^ n)
      (fourierFilter c F τ) := by
  simpa only [mul_assoc, id_eq] using fourierFilter_hasSum c F
    (fun n τ => a n * Function.Periodic.qParam 1 τ ^ n) id hF
    (fun n j τ => by simp only [qParam_fourierTranslate_zpow, id_eq]; ring) τ

/-- The residue selector used to remove the smallest-parts shadow. -/
noncomputable def negativeSquareResidueSelector (Q : ℕ) [Fact Q.Prime]
    (u : ZMod Q) : ℂ := (negativeSquareSelector Q u.val : ℚ)

@[simp] theorem negativeSquareResidueSelector_intCast (Q : ℕ) [Fact Q.Prime]
    (n : ℤ) : negativeSquareResidueSelector Q (n : ZMod Q) =
      (negativeSquareSelector Q n : ℚ) := by
  simp only [negativeSquareResidueSelector, negativeSquareSelector_eq, legendreSym,
    Int.cast_neg, Int.cast_natCast, ZMod.natCast_zmod_val]

/-- A convergent shadow supported on negative squares is killed by the actual
finite translation operator, including terms whose frequency is zero modulo Q. -/
theorem fourierFilter_negativeSquare_shadow (Q : ℕ) [Fact Q.Prime]
    (F : UpperHalfPlane → ℂ) (term : ℤ → UpperHalfPlane → ℂ)
    (hF : ∀ τ, HasSum (fun t => term t τ) (F τ))
    (hterm : ∀ t j τ, term t (fourierTranslate (N := Q) j τ) =
      ZMod.stdAddChar (j * (-(t ^ 2) : ZMod Q)) * term t τ) :
    fourierFilter (negativeSquareResidueSelector Q) F = 0 := by
  funext τ
  have h := fourierFilter_hasSum (negativeSquareResidueSelector Q) F term
    (fun t => -(t ^ 2)) hF (by simpa using hterm) τ
  have hz : HasSum (fun _ : ℤ => (0 : ℂ))
      (fourierFilter (negativeSquareResidueSelector Q) F τ) := by
    simpa only [negativeSquareResidueSelector_intCast, negativeSquareSelector_neg_sq,
      Rat.cast_zero, zero_mul] using h
  exact hz.unique hasSum_zero

/-- A completion and its holomorphic part have the same filtered function
when their difference is a convergent negative-square shadow. -/
theorem fourierFilter_completion (Q : ℕ) [Fact Q.Prime]
    (M H R : UpperHalfPlane → ℂ) (hM : M = H + R)
    (term : ℤ → UpperHalfPlane → ℂ)
    (hR : ∀ τ, HasSum (fun t => term t τ) (R τ))
    (hterm : ∀ t j τ, term t (fourierTranslate (N := Q) j τ) =
      ZMod.stdAddChar (j * (-(t ^ 2) : ZMod Q)) * term t τ) :
    fourierFilter (negativeSquareResidueSelector Q) M =
      fourierFilter (negativeSquareResidueSelector Q) H := by
  rw [hM, fourierFilter_add, fourierFilter_negativeSquare_shadow Q R term hR hterm,
    add_zero]

/-- Negative-square Fourier terms have the required translation law even
when their amplitudes are arbitrary functions of the height. This applies
to the incomplete-gamma terms in a harmonic Maass completion. -/
theorem negativeSquareTerm_fourierTranslate {N : ℕ} [NeZero N]
    (amplitude : ℤ → ℝ → ℂ) (t : ℤ) (j : ZMod N) (τ : UpperHalfPlane) :
    amplitude t (fourierTranslate j τ).im *
        Function.Periodic.qParam 1 (fourierTranslate j τ) ^ (-(t ^ 2)) =
      ZMod.stdAddChar (j * (-(t ^ 2) : ZMod N)) *
        (amplitude t τ.im * Function.Periodic.qParam 1 τ ^ (-(t ^ 2))) := by
  rw [fourierTranslate_im, qParam_fourierTranslate_zpow]
  simp only [Int.cast_neg, Int.cast_pow]
  ring

/-- The negative-square completion correction is removed without requiring
holomorphy of its amplitude functions. -/
theorem fourierFilter_completion_of_height_expansion (Q : ℕ) [Fact Q.Prime]
    (M H R : UpperHalfPlane → ℂ) (hM : M = H + R)
    (amplitude : ℤ → ℝ → ℂ)
    (hR : ∀ (τ : UpperHalfPlane), HasSum (fun t => amplitude t τ.im *
      Function.Periodic.qParam 1 τ ^ (-(t ^ 2))) (R τ)) :
    fourierFilter (negativeSquareResidueSelector Q) M =
      fourierFilter (negativeSquareResidueSelector Q) H := by
  exact fourierFilter_completion Q M H R hM _ hR
    (negativeSquareTerm_fourierTranslate amplitude)

end SptClassification
