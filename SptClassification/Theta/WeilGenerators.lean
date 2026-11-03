/- Assembled by AxiomProver. -/

module

public import SptClassification.Theta.WeilFourier

/-!
# The two finite Weil generator formulas

The formulas for the standard lifts of `T` and `S` use the quadratic value
`r²/24`, the discriminant pairing `rs/12`, and the signature-one phase.
Their action on the input vector of [rolenManuscript, lines 339–342] is
computed here. A group action and the eta multiplier law remain separate.
-/

public section

namespace SptClassification
namespace Theta

/-- The diagonal formula for the standard metaplectic lift of `T`. -/
@[expose]
noncomputable def finiteWeilT (f : ZMod 12 → ℂ) (r : ZMod 12) : ℂ :=
  Complex.exp (Real.pi * Complex.I * (discriminantQuadratic r).val / 12) * f r

/-- The Fourier formula for the standard metaplectic lift of `S`, with
signature phase `exp(-πi/4)`. -/
@[expose]
noncomputable def finiteWeilS (f : ZMod 12 → ℂ) (s : ZMod 12) : ℂ :=
  Complex.exp (-(Real.pi / 4) * Complex.I) / (Real.sqrt 12 : ℂ) *
    fourierNumerator ℂ (Complex.exp ((Real.pi / 6) * Complex.I)) f s

/-- The finite `T` formula has eta's translation eigenvalue on the input. -/
theorem finiteWeilT_weilInputVector :
    finiteWeilT (weilInputVectorAs ℂ) =
      fun r => Complex.exp (Real.pi * Complex.I / 12) * weilInputVectorAs ℂ r := by
  funext r
  by_cases hr : weilInputVector r = 0
  · simp [finiteWeilT, weilInputVectorAs, hr]
  · rw [finiteWeilT, weilInputVector_quadratic_support hr]
    have hval : (1 : ZMod 24).val = 1 := by decide
    simp only [hval, Nat.cast_one, mul_one]

/-- The finite `S` formula has eta's inversion eigenvalue on the input. -/
theorem finiteWeilS_weilInputVector :
    finiteWeilS (weilInputVectorAs ℂ) =
      fun s => Complex.exp (-(Real.pi / 4) * Complex.I) * weilInputVectorAs ℂ s := by
  funext s
  simp only [finiteWeilS, congrFun (fourierNumerator_weilInputVector ℂ
    (Complex.exp ((Real.pi / 6) * Complex.I))) s,
    gaussNumerator_exp_pos_pi_div_six]
  have hsqrt : (Real.sqrt 12 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 12)))
  field_simp

end Theta
end SptClassification
