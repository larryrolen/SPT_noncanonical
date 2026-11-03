/- Assembled by AxiomProver. -/

module

public import SptClassification.Theta.WeilQuadraticGauss

/-!
# The cubic relation for the finite Weil generators

Completing the quadratic square gives the operator relation on the whole
discriminant-group coefficient space. The scalar is fixed using the
distinguished input vector, whose two generator eigenvalues were calculated
from the manuscript normalization. See [rolenManuscript, lines 339–343].
-/

public section

namespace SptClassification
namespace Theta

private theorem stdAddChar_negative_kernel (r s t : ZMod 12) :
    (ZMod.stdAddChar (-(s * t)) : ℂ) *
        ZMod.stdAddChar (-(t * r)) =
      ZMod.stdAddChar (-(t * (r + s))) := by
  rw [← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- The diagonal Fourier conjugation identity before evaluating its Gauss
scalar. All three diagonal phases are needed for the standard `S T` word. -/
theorem weilQuadratic_dft_identity (f : ZMod 12 → ℂ) (r : ZMod 12) :
    weilQuadraticPhase r *
        ZMod.dft (fun t => weilQuadraticPhase t *
          ZMod.dft (fun s => weilQuadraticPhase s * f s) t) r =
      weilQuadraticGauss * ZMod.dft f r := by
  have hchar (s t : ZMod 12) := stdAddChar_negative_kernel r s t
  calc
    weilQuadraticPhase r *
        ZMod.dft (fun t => weilQuadraticPhase t *
          ZMod.dft (fun s => weilQuadraticPhase s * f s) t) r =
      ∑ t : ZMod 12, ∑ s : ZMod 12,
        (weilQuadraticPhase r * weilQuadraticPhase s *
          (weilQuadraticPhase t * ZMod.stdAddChar (-(t * (r + s))))) * f s := by
            simp only [ZMod.dft_apply, smul_eq_mul, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro t _
            apply Finset.sum_congr rfl
            intro s _
            rw [← hchar s t]
            ring
    _ = ∑ s : ZMod 12, ∑ t : ZMod 12,
          (weilQuadraticPhase r * weilQuadraticPhase s *
            (weilQuadraticPhase t * ZMod.stdAddChar (-(t * (r + s))))) * f s :=
      Finset.sum_comm
    _ = ∑ s : ZMod 12,
          (weilQuadraticPhase r * weilQuadraticPhase s *
            (∑ t : ZMod 12,
              weilQuadraticPhase t * ZMod.stdAddChar (-(t * (r + s))))) * f s := by
            apply Finset.sum_congr rfl
            intro s _
            simp only [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ s : ZMod 12,
          (weilQuadraticGauss * ZMod.stdAddChar (-(r * s))) * f s := by
            apply Finset.sum_congr rfl
            intro s _
            rw [weilQuadraticGauss_kernel]
    _ = weilQuadraticGauss * ZMod.dft f r := by
      simp only [ZMod.dft_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      have h : -(r * s) = -(s * r) := by ring
      rw [h]
      ring

/-- The unnormalized finite Fourier transform commutes with complex scalars. -/
theorem dft_smul (a : ℂ) (f : ZMod 12 → ℂ) :
    ZMod.dft (fun r => a * f r) = fun r => a * ZMod.dft f r := by
  funext r
  simp only [ZMod.dft_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

private theorem quadraticPhase_input :
    (fun r => weilQuadraticPhase r * weilInputVectorAs ℂ r) =
      fun r => Complex.exp (Real.pi * Complex.I / 12) * weilInputVectorAs ℂ r := by
  funext r
  have h := congrFun finiteWeilT_weilInputVector r
  simpa only [finiteWeilT, ← weilQuadraticPhase_eq] using h

private theorem dft_input :
    ZMod.dft (weilInputVectorAs ℂ) =
      fun r => (Real.sqrt 12 : ℂ) * weilInputVectorAs ℂ r := by
  funext r
  calc
    ZMod.dft (weilInputVectorAs ℂ) r =
        fourierNumerator ℂ (Complex.exp ((Real.pi / 6) * Complex.I))
          (weilInputVectorAs ℂ) r :=
      (congrFun (fourierNumerator_exp_eq_dft (weilInputVectorAs ℂ)) r).symm
    _ = weilInputVectorAs ℂ r *
        gaussNumerator ℂ (Complex.exp ((Real.pi / 6) * Complex.I)) :=
      congrFun (fourierNumerator_weilInputVector ℂ
        (Complex.exp ((Real.pi / 6) * Complex.I))) r
    _ = (Real.sqrt 12 : ℂ) * weilInputVectorAs ℂ r := by
      rw [gaussNumerator_exp_pos_pi_div_six]
      ring

/-- Evaluation on the nonzero input eigenvector determines the Gauss scalar
without a second trigonometric Gauss-sum calculation. -/
theorem weilQuadraticGauss_eq :
    weilQuadraticGauss =
      (Real.sqrt 12 : ℂ) * Complex.exp ((Real.pi / 4) * Complex.I) := by
  let v : ZMod 12 → ℂ := weilInputVectorAs ℂ
  let z : ℂ := Complex.exp (Real.pi * Complex.I / 12)
  let b : ℂ := Real.sqrt 12
  have hD : (fun r => weilQuadraticPhase r * v r) = fun r => z * v r :=
    quadraticPhase_input
  have hF : ZMod.dft v = fun r => b * v r := dft_input
  have hDF : ZMod.dft (fun r => weilQuadraticPhase r * v r) =
      fun r => z * b * v r := by
    rw [hD, dft_smul]
    funext r
    rw [congrFun hF r]
    ring
  have hDFD : (fun r => weilQuadraticPhase r *
        ZMod.dft (fun s => weilQuadraticPhase s * v s) r) =
      fun r => z ^ 2 * b * v r := by
    funext r
    rw [congrFun hDF r]
    have hv := congrFun hD r
    calc
      weilQuadraticPhase r * (z * b * v r) =
          (z * b) * (weilQuadraticPhase r * v r) := by ring
      _ = z ^ 2 * b * v r := by rw [hv]; ring
  have hFDFD : ZMod.dft (fun r => weilQuadraticPhase r *
        ZMod.dft (fun s => weilQuadraticPhase s * v s) r) =
      fun r => z ^ 2 * b ^ 2 * v r := by
    rw [hDFD, dft_smul]
    funext r
    rw [congrFun hF r]
    ring
  have hv1 : v 1 = 1 := by
    change ((weilInputVector (1 : ZMod 12) : ℤ) : ℂ) = 1
    have h : weilInputVector (1 : ZMod 12) = 1 := by decide +kernel
    norm_num [h]
  have hscalar : z ^ 3 * b ^ 2 = weilQuadraticGauss * b := by
    have h := weilQuadratic_dft_identity v 1
    rw [congrFun hFDFD 1, congrFun hF 1, hv1] at h
    have hd1 := congrFun hD 1
    rw [hv1, mul_one] at hd1
    rw [hd1] at h
    simpa only [mul_one] using (show z ^ 3 * b ^ 2 = weilQuadraticGauss * b by
      calc
        z ^ 3 * b ^ 2 = z * (z ^ 2 * b ^ 2) := by ring
        _ = weilQuadraticGauss * b := by simpa only [mul_one] using h)
  have hb : b ≠ 0 := by
    dsimp [b]
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 12)))
  have hgauss : weilQuadraticGauss = z ^ 3 * b := by
    have h := congrArg (fun x : ℂ => x * b⁻¹) hscalar
    calc
      weilQuadraticGauss = (weilQuadraticGauss * b) * b⁻¹ := by field_simp [hb]
      _ = (z ^ 3 * b ^ 2) * b⁻¹ := h.symm
      _ = z ^ 3 * b := by field_simp [hb]
  have hz : z ^ 3 = Complex.exp ((Real.pi / 4) * Complex.I) := by
    dsimp [z]
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  rw [hgauss, hz]
  dsimp [b]
  ring

/-- The signature-one Fourier normalizing factor cancels the quadratic Gauss
sum with the manuscript's phase convention. -/
theorem weilQuadraticGauss_normalized :
    (Complex.exp (-(Real.pi / 4) * Complex.I) / (Real.sqrt 12 : ℂ)) *
      weilQuadraticGauss = 1 := by
  rw [weilQuadraticGauss_eq]
  have hb : (Real.sqrt 12 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 12)))
  have hexp : Complex.exp (-(Real.pi / 4) * Complex.I) *
      Complex.exp ((Real.pi / 4) * Complex.I) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 1
    congr 1
    ring
  calc
    (Complex.exp (-(Real.pi / 4) * Complex.I) / (Real.sqrt 12 : ℂ)) *
        ((Real.sqrt 12 : ℂ) * Complex.exp ((Real.pi / 4) * Complex.I)) =
      Complex.exp (-(Real.pi / 4) * Complex.I) *
        Complex.exp ((Real.pi / 4) * Complex.I) := by field_simp [hb]
    _ = 1 := hexp

/-- Fourier transform after the quadratic diagonal, before the signature
phase and square-root normalization. -/
noncomputable def weilSTNumerator (f : ZMod 12 → ℂ) : ZMod 12 → ℂ :=
  ZMod.dft (fun r => weilQuadraticPhase r * f r)

theorem weilSTNumerator_smul (a : ℂ) (f : ZMod 12 → ℂ) :
    weilSTNumerator (fun r => a * f r) =
      fun r => a * weilSTNumerator f r := by
  simp only [weilSTNumerator]
  have h : (fun r => weilQuadraticPhase r * (a * f r)) =
      fun r => a * (weilQuadraticPhase r * f r) := by
    funext r
    ring
  rw [h, dft_smul]

/-- Three unnormalized `F D` words reduce to the Gauss scalar times `F²`. -/
theorem weilSTNumerator_cube (f : ZMod 12 → ℂ) :
    weilSTNumerator (weilSTNumerator (weilSTNumerator f)) =
      fun r => weilQuadraticGauss * ZMod.dft (ZMod.dft f) r := by
  change ZMod.dft (fun r => weilQuadraticPhase r *
    ZMod.dft (fun t => weilQuadraticPhase t *
      ZMod.dft (fun s => weilQuadraticPhase s * f s) t) r) = _
  have h : (fun r => weilQuadraticPhase r *
      ZMod.dft (fun t => weilQuadraticPhase t *
        ZMod.dft (fun s => weilQuadraticPhase s * f s) t) r) =
      fun r => weilQuadraticGauss * ZMod.dft f r := by
    funext r
    exact weilQuadratic_dft_identity f r
  rw [h, dft_smul]

/-- The standard finite Weil `S` formula is the normalized Fourier transform. -/
theorem finiteWeilS_eq_dft (f : ZMod 12 → ℂ) :
    finiteWeilS f = fun r =>
      (Complex.exp (-(Real.pi / 4) * Complex.I) / (Real.sqrt 12 : ℂ)) *
        ZMod.dft f r := by
  funext r
  simp only [finiteWeilS, fourierNumerator_exp_eq_dft]

/-- The standard finite Weil `T` formula is the quadratic diagonal. -/
theorem finiteWeilT_eq_phase (f : ZMod 12 → ℂ) :
    finiteWeilT f = fun r => weilQuadraticPhase r * f r := by
  funext r
  rw [finiteWeilT, weilQuadraticPhase_eq]

/-- The normalized standard `S T` word is a scalar multiple of its Fourier
numerator. -/
theorem finiteWeilST_eq (f : ZMod 12 → ℂ) :
    finiteWeilS (finiteWeilT f) = fun r =>
      (Complex.exp (-(Real.pi / 4) * Complex.I) / (Real.sqrt 12 : ℂ)) *
        weilSTNumerator f r := by
  rw [finiteWeilS_eq_dft, finiteWeilT_eq_phase]
  rfl

/-- The two standard lifts satisfy `(S T)³ = S²` as operators on every
coefficient vector of the twelve-element discriminant group. -/
theorem finiteWeilST_cube (f : ZMod 12 → ℂ) :
    finiteWeilS (finiteWeilT
      (finiteWeilS (finiteWeilT (finiteWeilS (finiteWeilT f))))) =
      finiteWeilS (finiteWeilS f) := by
  let c : ℂ :=
    Complex.exp (-(Real.pi / 4) * Complex.I) / (Real.sqrt 12 : ℂ)
  have hST (g : ZMod 12 → ℂ) :
      finiteWeilS (finiteWeilT g) = fun r => c * weilSTNumerator g r :=
    finiteWeilST_eq g
  have hS (g : ZMod 12 → ℂ) :
      finiteWeilS g = fun r => c * ZMod.dft g r := finiteWeilS_eq_dft g
  have hcube :
      finiteWeilS (finiteWeilT
        (finiteWeilS (finiteWeilT (finiteWeilS (finiteWeilT f))))) =
        fun r => c ^ 3 *
          weilSTNumerator (weilSTNumerator (weilSTNumerator f)) r := by
    funext r
    simp only [hST, weilSTNumerator_smul]
    ring
  have hS2 : finiteWeilS (finiteWeilS f) =
      fun r => c ^ 2 * ZMod.dft (ZMod.dft f) r := by
    calc
      finiteWeilS (finiteWeilS f) =
          fun r => c * ZMod.dft (finiteWeilS f) r := hS _
      _ = fun r => c * ZMod.dft (fun s => c * ZMod.dft f s) r := by rw [hS f]
      _ = fun r => c ^ 2 * ZMod.dft (ZMod.dft f) r := by
        rw [dft_smul]
        funext r
        ring
  have hcG : c * weilQuadraticGauss = 1 := weilQuadraticGauss_normalized
  calc
    finiteWeilS (finiteWeilT
      (finiteWeilS (finiteWeilT (finiteWeilS (finiteWeilT f))))) =
        fun r => c ^ 3 *
          weilSTNumerator (weilSTNumerator (weilSTNumerator f)) r := hcube
    _ = fun r => c ^ 3 *
        (weilQuadraticGauss * ZMod.dft (ZMod.dft f) r) := by
          rw [weilSTNumerator_cube]
    _ = fun r => c ^ 2 * ZMod.dft (ZMod.dft f) r := by
      funext r
      calc
        c ^ 3 * (weilQuadraticGauss * ZMod.dft (ZMod.dft f) r) =
            c ^ 2 * (c * weilQuadraticGauss) * ZMod.dft (ZMod.dft f) r := by
              ring
        _ = c ^ 2 * ZMod.dft (ZMod.dft f) r := by rw [hcG]; ring
    _ = finiteWeilS (finiteWeilS f) := hS2.symm

end Theta
end SptClassification
