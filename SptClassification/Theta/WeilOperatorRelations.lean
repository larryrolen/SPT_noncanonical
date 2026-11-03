/- Assembled by AxiomProver. -/

module

public import SptClassification.Theta.EtaWeilGeneratorWords
public import Mathlib.Analysis.Fourier.ZMod

/-!
# Relations for the finite Weil inversion operator

The Fourier kernel for the signature-one lattice uses the negative
discriminant pairing. Mathlib's `ZMod.dft` has the same convention. Its
inversion formula gives the square of the standard finite Weil `S` operator
on every coefficient vector, not only the distinguished input line.
See [rolenManuscript, lines 339–343].
-/

public section

namespace SptClassification
namespace Theta

/-- The positive twelfth root gives Mathlib's standard additive character. -/
theorem exp_pos_pi_div_six_pow (r : ZMod 12) :
    Complex.exp ((Real.pi / 6) * Complex.I) ^ r.val =
      ZMod.stdAddChar r := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The finite Weil Fourier numerator is the unnormalized negative-kernel
discrete Fourier transform. -/
theorem fourierNumerator_exp_eq_dft (f : ZMod 12 → ℂ) :
    fourierNumerator ℂ (Complex.exp ((Real.pi / 6) * Complex.I)) f =
      ZMod.dft f := by
  funext s
  rw [fourierNumerator, ZMod.dft_apply]
  apply Finset.sum_congr rfl
  intro r _
  rw [exp_pos_pi_div_six_pow]
  simp only [smul_eq_mul]
  ring

/-- The signature-one phase squares to `-i`. -/
theorem finiteWeilInversionPhase_sq :
    Complex.exp (-(Real.pi / 4) * Complex.I) ^ 2 = -Complex.I := by
  rw [← eta_inversion_phase, inv_pow, complex_sqrt_sq]
  simp

/-- The square of finite Weil inversion is `-i` times reflection on the
whole discriminant-group coefficient space. -/
theorem finiteWeilS_sq (f : ZMod 12 → ℂ) :
    finiteWeilS (finiteWeilS f) =
      fun r => -Complex.I * f (-r) := by
  let c : ℂ := Complex.exp (-(Real.pi / 4) * Complex.I) / (Real.sqrt 12 : ℂ)
  have hsqrt : (Real.sqrt 12 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 12)))
  have hsqrt_sq : (Real.sqrt 12 : ℂ) ^ 2 = 12 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 12)
  have hc : c * c * (12 : ℂ) = -Complex.I := by
    dsimp [c]
    rw [← pow_two, div_pow, finiteWeilInversionPhase_sq, hsqrt_sq]
    field_simp
  have hS (g : ZMod 12 → ℂ) :
      finiteWeilS g = fun r => c * (ZMod.dft g) r := by
    funext r
    simp only [finiteWeilS, fourierNumerator_exp_eq_dft]
    rfl
  calc
    finiteWeilS (finiteWeilS f) =
        finiteWeilS (fun r => c * (ZMod.dft f) r) := by rw [hS f]
    _ = fun r => c * finiteWeilS (ZMod.dft f) r :=
      finiteWeilS_smul c (ZMod.dft f)
    _ = fun r => -Complex.I * f (-r) := by
      funext r
      rw [hS, ZMod.dft_dft]
      simp only [smul_eq_mul]
      calc
        c * (c * ((12 : ℂ) * f (-r))) =
            (c * c * (12 : ℂ)) * f (-r) := by ring
        _ = -Complex.I * f (-r) := by rw [hc]

/-- Four standard finite Weil inversions act by the negative identity. -/
theorem finiteWeilS_fourth (f : ZMod 12 → ℂ) :
    finiteWeilS (finiteWeilS (finiteWeilS (finiteWeilS f))) =
      fun r => -f r := by
  funext r
  rw [congrFun (finiteWeilS_sq (finiteWeilS (finiteWeilS f))) r]
  rw [congrFun (finiteWeilS_sq f) (-r)]
  simp only [neg_neg]
  calc
    -Complex.I * (-Complex.I * f r) = Complex.I ^ 2 * f r := by ring
    _ = -f r := by rw [Complex.I_sq]; ring

/-- The standard finite Weil inversion lift has order eight on every
discriminant-group coefficient vector. -/
theorem finiteWeilS_eighth (f : ZMod 12 → ℂ) :
    finiteWeilS (finiteWeilS (finiteWeilS (finiteWeilS
      (finiteWeilS (finiteWeilS (finiteWeilS (finiteWeilS f))))))) = f := by
  funext r
  rw [congrFun (finiteWeilS_fourth
    (finiteWeilS (finiteWeilS (finiteWeilS (finiteWeilS f))))) r]
  rw [congrFun (finiteWeilS_fourth f) r]
  ring

end Theta
end SptClassification
