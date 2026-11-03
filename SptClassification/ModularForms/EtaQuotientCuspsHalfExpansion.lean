/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.EtaQuotientCusps

/-!
# Expansion of the level-six eta quotient at the cusp one-half

The substitution `z ↦ z/(2z+1)` approaches the cusp `1/2` as `z` approaches
infinity. Its four eta factors reduce to eta values at `z`, `2z`,
`(z-1)/3`, and `(2z+1)/3`. This is the analytic input for the remaining
cusp divisor calculation of the coordinate in [rolen2026canonical], Section 4.
-/

public section

namespace SptClassification

/-- The matrix `[1,0;2,1]` transports infinity to the cusp one-half. -/
noncomputable def cuspHalfApproach (z : UpperHalfPlane) : ℂ :=
  (z : ℂ) / (2 * z + 1)

@[simp] theorem cuspHalfApproach_eq (z : UpperHalfPlane) :
    cuspHalfApproach z = (z : ℂ) / (2 * z + 1) := (rfl)

/-- The first eta factor under the cusp-one-half substitution. -/
theorem eta_cuspHalfApproach (z : UpperHalfPlane) :
    ModularForm.eta (cuspHalfApproach z) =
      Complex.exp (-Real.pi * Complex.I * 2 / 12) *
        (2 * (z : ℂ) + 1).sqrt * ModularForm.eta z := by
  simpa [cuspHalfApproach] using eta_lower_unipotent z 2

/-- The eta factor at twice the cusp-one-half substitution. -/
theorem eta_twice_cuspHalfApproach (z : UpperHalfPlane) :
    ModularForm.eta (2 * cuspHalfApproach z) =
      Complex.exp (Real.pi * Complex.I / 12) *
        Complex.I.sqrt⁻¹ * (2 * (z : ℂ) + 1).sqrt *
        ModularForm.eta (2 * (z : ℂ) + 1) := by
  have hpos : 0 < (2 * (z : ℂ) + 1).im := by
    simpa using mul_pos (by norm_num : (0 : ℝ) < 2) z.im_pos
  have hden : (2 : ℂ) * z + 1 ≠ 0 := by
    intro h
    rw [h] at hpos
    simp at hpos
  have htrans := eta_add_int (-1 / (2 * (z : ℂ) + 1)) 1
  norm_num only [Int.cast_one] at htrans
  have hinv := eta_neg_inv hpos
  have harg : 2 * cuspHalfApproach z = -1 / (2 * (z : ℂ) + 1) + 1 := by
    unfold cuspHalfApproach
    field_simp [hden]
    ring
  rw [harg]
  have hcomm : (1 : ℂ) + 2 * (z : ℂ) = 2 * z + 1 := by ring
  calc
    ModularForm.eta (-1 / (2 * (z : ℂ) + 1) + 1) =
        Complex.exp (Real.pi * Complex.I / 12) *
          (Complex.I.sqrt⁻¹ * (2 * (z : ℂ) + 1).sqrt *
            ModularForm.eta (2 * (z : ℂ) + 1)) := by
      rw [htrans, hinv]
      norm_num only [Int.cast_one, mul_one]
    _ = _ := by ring

/-- The eta factor at three times the cusp-one-half substitution. -/
theorem eta_thrice_cuspHalfApproach (z : UpperHalfPlane) :
    ModularForm.eta (3 * cuspHalfApproach z) =
      Complex.exp (Real.pi * Complex.I / 12) *
        (Complex.exp (-Real.pi * Complex.I * 2 / 12) *
          (((2 * (z : ℂ) + 1) / 3).sqrt *
            ModularForm.eta (((z : ℂ) - 1) / 3))) := by
  let v : UpperHalfPlane := ⟨((z : ℂ) - 1) / 3, by
    have hz := z.im_pos
    simp only [Complex.div_im, Complex.sub_im, Complex.one_im]
    norm_num at *
    exact hz⟩
  have hv : (v : ℂ) = ((z : ℂ) - 1) / 3 := rfl
  have hfactor : (2 : ℂ) * v + 1 = (2 * (z : ℂ) + 1) / 3 := by
    rw [hv]
    ring
  have hdenZ : (2 : ℂ) * z + 1 ≠ 0 := by
    intro h
    have hp : 0 < ((2 : ℂ) * z + 1).im := by
      simpa using mul_pos (by norm_num : (0 : ℝ) < 2) z.im_pos
    rw [h] at hp
    simp at hp
  have hdenZ' : (1 : ℂ) + (z : ℂ) * 2 ≠ 0 := by
    convert hdenZ using 1; ring
  have harg : 3 * cuspHalfApproach z = (v : ℂ) / (2 * v + 1) + 1 := by
    unfold cuspHalfApproach
    rw [hv]
    field_simp [hdenZ']
    have hc : ((1 : ℂ) + (z : ℂ) * 2) * ((1 : ℂ) + (z : ℂ) * 2)⁻¹ = 1 :=
      mul_inv_cancel₀ hdenZ'
    linear_combination hc
  rw [harg]
  have htrans := eta_add_int ((v : ℂ) / (2 * v + 1)) 1
  rw [show ModularForm.eta ((v : ℂ) / (2 * v + 1) + 1) =
    Complex.exp (Real.pi * Complex.I / 12) *
      ModularForm.eta ((v : ℂ) / (2 * v + 1)) by simpa using htrans]
  have hηv : ModularForm.eta ((v : ℂ) / (2 * v + 1)) =
      Complex.exp (-Real.pi * Complex.I * 2 / 12) *
        (2 * (v : ℂ) + 1).sqrt * ModularForm.eta v := by
    simpa using eta_lower_unipotent v 2
  rw [hηv, hfactor, hv]
  ring

/-- The eta factor at six times the cusp-one-half substitution. -/
theorem eta_six_cuspHalfApproach (z : UpperHalfPlane) :
    ModularForm.eta (6 * cuspHalfApproach z) =
      Complex.exp (Real.pi * Complex.I * 3 / 12) *
        (Complex.I.sqrt⁻¹ * (((2 * (z : ℂ) + 1) / 3).sqrt *
          ModularForm.eta ((2 * (z : ℂ) + 1) / 3))) := by
  let v : UpperHalfPlane := ⟨(2 * (z : ℂ) + 1) / 3, by
    have hz := z.im_pos
    simp only [Complex.div_im, Complex.add_im, Complex.mul_im,
      Complex.one_im]
    norm_num at *
    exact hz⟩
  have hv : (v : ℂ) = (2 * (z : ℂ) + 1) / 3 := rfl
  have harg : 6 * cuspHalfApproach z = -1 / (v : ℂ) + 3 := by
    unfold cuspHalfApproach
    rw [hv]
    have hden : (2 : ℂ) * z + 1 ≠ 0 := by
      intro h
      have hp : 0 < ((2 : ℂ) * z + 1).im := by
        simpa using mul_pos (by norm_num : (0 : ℝ) < 2) z.im_pos
      rw [h] at hp
      simp at hp
    have hden' : (1 : ℂ) + (z : ℂ) * 2 ≠ 0 := by
      convert hden using 1; ring
    field_simp [hden']
    have hc : ((1 : ℂ) + (z : ℂ) * 2) * ((1 : ℂ) + (z : ℂ) * 2)⁻¹ = 1 :=
      mul_inv_cancel₀ hden'
    linear_combination 3 * hc
  rw [harg]
  have htrans := eta_add_int (-1 / (v : ℂ)) 3
  rw [show ModularForm.eta (-1 / (v : ℂ) + 3) =
    Complex.exp (Real.pi * Complex.I * 3 / 12) *
      ModularForm.eta (-1 / (v : ℂ)) by simpa using htrans]
  rw [eta_neg_inv v.im_pos, hv]
  ring

private theorem cuspHalf_sqrt_ratio (u : ℂ) (hu : u ≠ 0) :
    u.sqrt ^ 5 * (u / 3).sqrt /
      (u.sqrt * (u / 3).sqrt ^ 5) = 9 := by
  have hs : u.sqrt ≠ 0 := by
    intro he
    have h := complex_sqrt_sq u
    rw [he] at h
    simp at h
    exact hu h.symm
  have hr : (u / 3).sqrt ≠ 0 := by
    intro he
    have h := complex_sqrt_sq (u / 3)
    rw [he] at h
    simp at h
    exact hu (by simpa using h.symm)
  calc
    _ = (u.sqrt ^ 2) ^ 2 / ((u / 3).sqrt ^ 2) ^ 2 := by
      field_simp [hs, hr]
    _ = u ^ 2 / (u / 3) ^ 2 := by rw [complex_sqrt_sq, complex_sqrt_sq]
    _ = 9 := by field_simp [hu]; ring

private theorem cuspHalf_exp_half_turn :
    Complex.exp (-Real.pi * Complex.I / 2) = -Complex.I := by
  have h : -Real.pi * Complex.I / 2 =
      ((-Real.pi / 2 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h, Complex.exp_mul_I]
  have harg : ((-Real.pi / 2 : ℝ) : ℂ) = -(↑Real.pi / 2 : ℂ) := by push_cast; ring
  rw [harg, Complex.cos_neg, Complex.sin_neg]
  norm_num

private theorem cuspHalf_phase :
    ((Complex.exp (-Real.pi * Complex.I / 6) ^ 5 *
        (Complex.exp (Real.pi * Complex.I / 12) *
          Complex.exp (-Real.pi * Complex.I / 6))) /
      (Complex.exp (Real.pi * Complex.I / 12) * Complex.I.sqrt⁻¹ *
        (Complex.exp (Real.pi * Complex.I / 4) * Complex.I.sqrt⁻¹) ^ 5)) *
      Complex.exp (-Real.pi * Complex.I / 4) = -1 := by
  let a : ℂ := Real.pi * Complex.I
  let r : ℂ := Complex.I.sqrt
  have hr : r ≠ 0 := by
    intro he
    have hs := complex_sqrt_sq Complex.I
    change r ^ 2 = Complex.I at hs
    rw [he] at hs
    exact Complex.I_ne_zero (by simpa using hs.symm)
  have hr6 : r ^ 6 = -Complex.I := by
    calc
      r ^ 6 = (r ^ 2) ^ 3 := by ring
      _ = Complex.I ^ 3 := by rw [show r ^ 2 = Complex.I from complex_sqrt_sq _]
      _ = -Complex.I := by simp [pow_succ]
  have hexp : Complex.exp (-a / 6) ^ 6 /
      Complex.exp (a / 4) ^ 5 * Complex.exp (-a / 4) =
      Complex.exp (-a / 2) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
      ← Complex.exp_sub, ← Complex.exp_add]
    calc
      _ = Complex.exp (-a / 2 - 2 * Real.pi * Complex.I) := by
        congr 1
        dsimp [a]
        ring
      _ = _ := by rw [Complex.exp_sub, Complex.exp_two_pi_mul_I, div_one]
  have hneg : -Real.pi * Complex.I = -a := by dsimp [a]; ring
  rw [hneg]
  change ((Complex.exp (-a / 6) ^ 5 *
      (Complex.exp (a / 12) * Complex.exp (-a / 6))) /
    (Complex.exp (a / 12) * r⁻¹ *
      (Complex.exp (a / 4) * r⁻¹) ^ 5)) *
      Complex.exp (-a / 4) = -1
  have halg : ((Complex.exp (-a / 6) ^ 5 *
        (Complex.exp (a / 12) * Complex.exp (-a / 6))) /
      (Complex.exp (a / 12) * r⁻¹ *
        (Complex.exp (a / 4) * r⁻¹) ^ 5)) *
      Complex.exp (-a / 4) =
      (Complex.exp (-a / 6) ^ 6 /
        Complex.exp (a / 4) ^ 5 * Complex.exp (-a / 4)) * r ^ 6 := by
    field_simp [hr, Complex.exp_ne_zero]
  rw [halg, hexp, hr6]
  rw [show -a / 2 = -Real.pi * Complex.I / 2 by dsimp [a]; ring,
    cuspHalf_exp_half_turn]
  simp

/-- The eta exponential factors have no varying exponential at the cusp
one-half; their remaining phase is a fixed eighth root of unity. -/
private theorem cuspHalf_eta_prefactor (z : ℂ) :
    Function.Periodic.qParam 24 z ^ 5 *
      Function.Periodic.qParam 24 ((z - 1) / 3) /
      (Function.Periodic.qParam 24 (2 * z + 1) *
        Function.Periodic.qParam 24 ((2 * z + 1) / 3) ^ 5) =
      Complex.exp (-Real.pi * Complex.I / 4) := by
  unfold Function.Periodic.qParam
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
    ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_sub]
  congr 1
  norm_num
  ring

/-- The four transformation factors reduce the cusp-one-half quotient to
ordinary eta values at four arguments with the same imaginary direction. -/
private theorem levelSixEtaQuotient_cuspHalf_eta (z : UpperHalfPlane) :
    levelSixEtaQuotient (cuspHalfApproach z) =
      9 *
        ((Complex.exp (-Real.pi * Complex.I / 6) ^ 5 *
            (Complex.exp (Real.pi * Complex.I / 12) *
              Complex.exp (-Real.pi * Complex.I / 6))) /
          (Complex.exp (Real.pi * Complex.I / 12) * Complex.I.sqrt⁻¹ *
            (Complex.exp (Real.pi * Complex.I / 4) * Complex.I.sqrt⁻¹) ^ 5)) *
        (ModularForm.eta z ^ 5 *
          ModularForm.eta (((z : ℂ) - 1) / 3) /
          (ModularForm.eta (2 * (z : ℂ) + 1) *
            ModularForm.eta ((2 * (z : ℂ) + 1) / 3) ^ 5)) := by
  let u : ℂ := 2 * (z : ℂ) + 1
  have huPos : 0 < u.im := by
    simpa [u] using mul_pos (by norm_num : (0 : ℝ) < 2) z.im_pos
  have hu : u ≠ 0 := by
    intro he
    rw [he] at huPos
    simp at huPos
  have hvPos : 0 < (u / 3).im := by
    have h : (u / 3).im = u.im / 3 := by
      simp
    rw [h]
    exact div_pos huPos (by norm_num)
  have hηu : ModularForm.eta u ≠ 0 := ModularForm.eta_ne_zero huPos
  have hηv : ModularForm.eta (u / 3) ≠ 0 := ModularForm.eta_ne_zero hvPos
  have hs : u.sqrt ≠ 0 := by
    intro he
    have h := complex_sqrt_sq u
    rw [he] at h
    exact hu (by simpa using h.symm)
  have hr : (u / 3).sqrt ≠ 0 := by
    intro he
    have h := complex_sqrt_sq (u / 3)
    rw [he] at h
    exact hu (by simpa using h.symm)
  have hκ : Complex.I.sqrt⁻¹ ≠ 0 := by
    apply inv_ne_zero
    intro he
    have h := complex_sqrt_sq Complex.I
    rw [he] at h
    exact Complex.I_ne_zero (by simpa using h.symm)
  have hsqrt := cuspHalf_sqrt_ratio u hu
  have ha : -Real.pi * Complex.I * 2 / 12 = -Real.pi * Complex.I / 6 := by ring
  have hd : Real.pi * Complex.I * 3 / 12 = Real.pi * Complex.I / 4 := by ring
  rw [levelSixEtaQuotient_eq]
  rw [eta_cuspHalfApproach, eta_twice_cuspHalfApproach,
    eta_thrice_cuspHalfApproach, eta_six_cuspHalfApproach, ha, hd]
  change _ = 9 * _ *
    (ModularForm.eta z ^ 5 * ModularForm.eta (((z : ℂ) - 1) / 3) /
      (ModularForm.eta u * ModularForm.eta (u / 3) ^ 5))
  have hcalc :
      ((Complex.exp (-Real.pi * Complex.I / 6) * u.sqrt * ModularForm.eta z) ^ 5 *
          (Complex.exp (Real.pi * Complex.I / 12) *
            (Complex.exp (-Real.pi * Complex.I / 6) *
              ((u / 3).sqrt * ModularForm.eta (((z : ℂ) - 1) / 3))))) /
        ((Complex.exp (Real.pi * Complex.I / 12) *
            Complex.I.sqrt⁻¹ * u.sqrt * ModularForm.eta u) *
          (Complex.exp (Real.pi * Complex.I / 4) *
            (Complex.I.sqrt⁻¹ * ((u / 3).sqrt * ModularForm.eta (u / 3)))) ^ 5) =
        ((Complex.exp (-Real.pi * Complex.I / 6) ^ 5 *
            (Complex.exp (Real.pi * Complex.I / 12) *
              Complex.exp (-Real.pi * Complex.I / 6))) /
          (Complex.exp (Real.pi * Complex.I / 12) * Complex.I.sqrt⁻¹ *
            (Complex.exp (Real.pi * Complex.I / 4) * Complex.I.sqrt⁻¹) ^ 5)) *
        (u.sqrt ^ 5 * (u / 3).sqrt /
          (u.sqrt * (u / 3).sqrt ^ 5)) *
        (ModularForm.eta z ^ 5 * ModularForm.eta (((z : ℂ) - 1) / 3) /
          (ModularForm.eta u * ModularForm.eta (u / 3) ^ 5)) := by
    simp only [mul_pow, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hcalc, hsqrt]
  ring

/-- The Euler product quotient at the cusp one-half after removing all eta
exponential factors. Each of its four arguments tends to zero as the cusp is
approached from the upper half-plane. -/
noncomputable def cuspHalfEulerQuotient (z : ℂ) : ℂ :=
  etaEulerProduct (Function.Periodic.qParam 1 z) ^ 5 *
    etaEulerProduct (Function.Periodic.qParam 1 ((z - 1) / 3)) /
    (etaEulerProduct (Function.Periodic.qParam 1 (2 * z + 1)) *
      etaEulerProduct (Function.Periodic.qParam 1 ((2 * z + 1) / 3)) ^ 5)

/-- The cusp-one-half expansion has constant coefficient `-9`. The remaining
Euler quotient is holomorphic at its four nome origins and equals one there.
This is the analytic cusp input for [rolen2026canonical], Section 4. -/
theorem levelSixEtaQuotient_cuspHalf_eq_euler (z : UpperHalfPlane) :
    levelSixEtaQuotient (cuspHalfApproach z) =
      -9 * cuspHalfEulerQuotient z := by
  let p : ℂ :=
    (Complex.exp (-Real.pi * Complex.I / 6) ^ 5 *
      (Complex.exp (Real.pi * Complex.I / 12) *
        Complex.exp (-Real.pi * Complex.I / 6))) /
      (Complex.exp (Real.pi * Complex.I / 12) * Complex.I.sqrt⁻¹ *
        (Complex.exp (Real.pi * Complex.I / 4) * Complex.I.sqrt⁻¹) ^ 5)
  have hp : p * Complex.exp (-Real.pi * Complex.I / 4) = -1 :=
    cuspHalf_phase
  have hη (w : ℂ) : ModularForm.eta w =
      Function.Periodic.qParam 24 w *
        etaEulerProduct (Function.Periodic.qParam 1 w) := by
    simpa using eta_nat_mul_eq_euler 1 w
  rw [levelSixEtaQuotient_cuspHalf_eta]
  change 9 * p * _ = -9 * cuspHalfEulerQuotient z
  rw [hη (z : ℂ), hη (((z : ℂ) - 1) / 3),
    hη (2 * (z : ℂ) + 1), hη ((2 * (z : ℂ) + 1) / 3)]
  have hfactor :
      ((Function.Periodic.qParam 24 (z : ℂ) *
          etaEulerProduct (Function.Periodic.qParam 1 (z : ℂ))) ^ 5 *
          (Function.Periodic.qParam 24 (((z : ℂ) - 1) / 3) *
            etaEulerProduct (Function.Periodic.qParam 1 (((z : ℂ) - 1) / 3)))) /
        ((Function.Periodic.qParam 24 (2 * (z : ℂ) + 1) *
            etaEulerProduct (Function.Periodic.qParam 1 (2 * (z : ℂ) + 1))) *
          (Function.Periodic.qParam 24 ((2 * (z : ℂ) + 1) / 3) *
            etaEulerProduct (Function.Periodic.qParam 1 ((2 * (z : ℂ) + 1) / 3))) ^ 5) =
      Complex.exp (-Real.pi * Complex.I / 4) * cuspHalfEulerQuotient z := by
    rw [← cuspHalf_eta_prefactor (z : ℂ)]
    unfold cuspHalfEulerQuotient
    simp only [mul_pow, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hfactor]
  calc
    9 * p * (Complex.exp (-Real.pi * Complex.I / 4) * cuspHalfEulerQuotient z) =
        9 * (p * Complex.exp (-Real.pi * Complex.I / 4)) *
          cuspHalfEulerQuotient z := by ring
    _ = _ := by rw [hp]; ring

/-- Addition in the upper-half-plane variable multiplies the ordinary nome. -/
theorem qParam_one_add_complex (w c : ℂ) :
    Function.Periodic.qParam 1 (w + c) =
      Function.Periodic.qParam 1 w * Function.Periodic.qParam 1 c := by
  unfold Function.Periodic.qParam
  rw [← Complex.exp_add]
  congr 1
  ring

/-- A single nome parametrizes the Euler quotient at the width-three cusp
one-half. Its constant term is one. -/
noncomputable def cuspHalfEulerUnit (q : ℂ) : ℂ :=
  etaEulerProduct (q ^ 3) ^ 5 *
    etaEulerProduct (q * Function.Periodic.qParam 1 (-1 / 3)) /
    (etaEulerProduct (q ^ 6 * Function.Periodic.qParam 1 1) *
      etaEulerProduct (q ^ 2 * Function.Periodic.qParam 1 (1 / 3)) ^ 5)

/-- The Euler expression defining the cusp-one-half unit. -/
theorem cuspHalfEulerUnit_eq (q : ℂ) :
    cuspHalfEulerUnit q =
      etaEulerProduct (q ^ 3) ^ 5 *
        etaEulerProduct (q * Function.Periodic.qParam 1 (-1 / 3)) /
        (etaEulerProduct (q ^ 6 * Function.Periodic.qParam 1 1) *
          etaEulerProduct (q ^ 2 * Function.Periodic.qParam 1 (1 / 3)) ^ 5) := (rfl)

/-- The four nomes in the cusp-one-half quotient are powers of the local
width-three nome, with fixed unit phases. -/
theorem cuspHalfEulerQuotient_three (w : ℂ) :
    cuspHalfEulerQuotient (3 * w) =
      cuspHalfEulerUnit (Function.Periodic.qParam 1 w) := by
  let q : ℂ := Function.Periodic.qParam 1 w
  have h3 : Function.Periodic.qParam 1 (3 * w) = q ^ 3 := by
    simpa [q] using qParam_nat_mul 3 w
  have hshift : (3 * w - 1) / 3 = w + (-1 / 3 : ℂ) := by ring
  have h1 : Function.Periodic.qParam 1 ((3 * w - 1) / 3) =
      q * Function.Periodic.qParam 1 (-1 / 3) := by
    rw [hshift, qParam_one_add_complex]
  have h6 : Function.Periodic.qParam 1 (2 * (3 * w) + 1) =
      q ^ 6 * Function.Periodic.qParam 1 1 := by
    have h6core : Function.Periodic.qParam 1 (6 * w) = q ^ 6 := by
      simpa [q] using qParam_nat_mul 6 w
    calc
      _ = Function.Periodic.qParam 1 (6 * w + 1) := by congr 1; ring
      _ = Function.Periodic.qParam 1 (6 * w) *
          Function.Periodic.qParam 1 1 := qParam_one_add_complex _ _
      _ = _ := by rw [h6core]
  have hshift2 : (2 * (3 * w) + 1) / 3 = 2 * w + 1 / 3 := by ring
  have h2 : Function.Periodic.qParam 1 ((2 * (3 * w) + 1) / 3) =
      q ^ 2 * Function.Periodic.qParam 1 (1 / 3) := by
    have h2core : Function.Periodic.qParam 1 (2 * w) = q ^ 2 := by
      simpa [q] using qParam_nat_mul 2 w
    rw [hshift2, qParam_one_add_complex, h2core]
  unfold cuspHalfEulerQuotient cuspHalfEulerUnit
  rw [h3, h1, h6, h2]

@[simp] theorem cuspHalfEulerUnit_zero : cuspHalfEulerUnit 0 = 1 := by
  simp [cuspHalfEulerUnit]

/-- The local Euler quotient is holomorphic at the cusp-one-half nome. -/
theorem differentiableAt_cuspHalfEulerUnit_zero :
    DifferentiableAt ℂ cuspHalfEulerUnit 0 := by
  have h3 : DifferentiableAt ℂ
      (fun q : ℂ => etaEulerProduct (q ^ 3)) 0 := by
    have hi : DifferentiableAt ℂ (fun q : ℂ => q ^ 3) 0 := by fun_prop
    apply DifferentiableAt.comp (g := etaEulerProduct)
      (f := fun q : ℂ => q ^ 3)
      (x := (0 : ℂ))
    · exact differentiableAt_etaEulerProduct (by simp)
    · exact hi
  have h1 : DifferentiableAt ℂ
      (fun q : ℂ => etaEulerProduct
        (q * Function.Periodic.qParam 1 (-1 / 3))) 0 := by
    have hi : DifferentiableAt ℂ
        (fun q : ℂ => q * Function.Periodic.qParam 1 (-1 / 3)) 0 := by fun_prop
    exact (differentiableAt_etaEulerProduct
      (by simp : ‖(0 : ℂ) * Function.Periodic.qParam 1 (-1 / 3)‖ < 1)).comp
      (0 : ℂ) hi
  have h6 : DifferentiableAt ℂ
      (fun q : ℂ => etaEulerProduct
        (q ^ 6 * Function.Periodic.qParam 1 1)) 0 := by
    have hi : DifferentiableAt ℂ
        (fun q : ℂ => q ^ 6 * Function.Periodic.qParam 1 1) 0 := by fun_prop
    exact (differentiableAt_etaEulerProduct
      (by simp : ‖(0 : ℂ) ^ 6 * Function.Periodic.qParam 1 1‖ < 1)).comp
      (0 : ℂ) hi
  have h2 : DifferentiableAt ℂ
      (fun q : ℂ => etaEulerProduct
        (q ^ 2 * Function.Periodic.qParam 1 (1 / 3))) 0 := by
    have hi : DifferentiableAt ℂ
        (fun q : ℂ => q ^ 2 * Function.Periodic.qParam 1 (1 / 3)) 0 := by fun_prop
    exact (differentiableAt_etaEulerProduct
      (by simp : ‖(0 : ℂ) ^ 2 * Function.Periodic.qParam 1 (1 / 3)‖ < 1)).comp
      (0 : ℂ) hi
  unfold cuspHalfEulerUnit
  apply ((h3.pow 5).mul h1).div ((h6.mul (h2.pow 5)))
  simp

/-- Scaling by three gives the local width-three parameter at cusp one-half. -/
noncomputable def cuspHalfTriplePoint (w : UpperHalfPlane) : UpperHalfPlane :=
  ⟨3 * (w : ℂ), by
    simpa using mul_pos (by norm_num : (0 : ℝ) < 3) w.im_pos⟩

@[simp] theorem cuspHalfTriplePoint_coe (w : UpperHalfPlane) :
    (cuspHalfTriplePoint w : ℂ) = 3 * (w : ℂ) := (rfl)

/-- In the width-three nome, the eta quotient has a holomorphic germ with
exact cusp value `-9`. -/
theorem levelSixEtaQuotient_cuspHalf_widthThree (w : UpperHalfPlane) :
    levelSixEtaQuotient (cuspHalfApproach (cuspHalfTriplePoint w)) =
      -9 * cuspHalfEulerUnit (Function.Periodic.qParam 1 w) := by
  rw [levelSixEtaQuotient_cuspHalf_eq_euler]
  change -9 * cuspHalfEulerQuotient (3 * (w : ℂ)) = _
  rw [cuspHalfEulerQuotient_three]

/-- Every approach along which the width-three nome tends to zero gives the
same cusp value `-9`. -/
theorem tendsto_levelSixEtaQuotient_cuspHalf
    {α : Type*} {l : Filter α} (w : α → UpperHalfPlane)
    (hw : Filter.Tendsto
      (fun a => Function.Periodic.qParam 1 (w a : ℂ)) l (nhds 0)) :
    Filter.Tendsto
      (fun a => levelSixEtaQuotient
        (cuspHalfApproach (cuspHalfTriplePoint (w a)))) l (nhds (-9)) := by
  have hunit := differentiableAt_cuspHalfEulerUnit_zero.continuousAt.tendsto.comp hw
  have hprod := (tendsto_const_nhds.mul hunit :
    Filter.Tendsto
      (fun a => (-9 : ℂ) *
        cuspHalfEulerUnit (Function.Periodic.qParam 1 (w a : ℂ)))
      l (nhds ((-9 : ℂ) * cuspHalfEulerUnit 0)))
  simpa only [levelSixEtaQuotient_cuspHalf_widthThree,
    cuspHalfEulerUnit_zero, mul_one] using hprod

end SptClassification
