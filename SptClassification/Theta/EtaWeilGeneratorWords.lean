/- Assembled by AxiomProver. -/

module

public import SptClassification.Theta.WeilGenerators
public import SptClassification.ModularForms.EtaUnipotent

/-!
# Eta and the finite Weil input on generator words

For a word in the standard inversion and integer translations, the actual eta
function and the distinguished finite Weil vector acquire the same scalar.
The eta formula retains the ordered product of square-root factors. This is
the generator calculation behind [rolenManuscript, lines 339–343]; descending
it to the metaplectic group and constructing the full Weil representation are
separate mathematical tasks.
-/

public section

namespace SptClassification
namespace Theta

/-- The two kinds of standard generators, with all integral translations. -/
inductive EtaWeilStep where
  | inversion
  | translation (n : ℤ)
  deriving DecidableEq

/-- The action of one generator on the upper half-plane. -/
noncomputable def EtaWeilStep.act : EtaWeilStep → UpperHalfPlane → UpperHalfPlane
  | .inversion, z => ModularGroup.S • z
  | .translation n, z => (n : ℝ) +ᵥ z

@[simp] theorem EtaWeilStep.act_inversion (z : UpperHalfPlane) :
    EtaWeilStep.inversion.act z = ModularGroup.S • z := (rfl)

@[simp] theorem EtaWeilStep.act_translation (n : ℤ) (z : UpperHalfPlane) :
    (EtaWeilStep.translation n).act z = (n : ℝ) +ᵥ z := (rfl)

/-- The square-root factor for one chosen standard lift. -/
noncomputable def EtaWeilStep.factor : EtaWeilStep → UpperHalfPlane → ℂ
  | .inversion, z => (z : ℂ).sqrt
  | .translation _, _ => 1

@[simp] theorem EtaWeilStep.factor_inversion (z : UpperHalfPlane) :
    EtaWeilStep.inversion.factor z = (z : ℂ).sqrt := (rfl)

@[simp] theorem EtaWeilStep.factor_translation (n : ℤ) (z : UpperHalfPlane) :
    (EtaWeilStep.translation n).factor z = 1 := (rfl)

theorem EtaWeilStep.factor_ne_zero (g : EtaWeilStep) (z : UpperHalfPlane) :
    g.factor z ≠ 0 := by
  cases g with
  | inversion =>
      change (z : ℂ).sqrt ≠ 0
      intro h
      have hs := complex_sqrt_sq (z : ℂ)
      rw [h] at hs
      exact z.ne_zero (by simpa using hs.symm)
  | translation n => simp [EtaWeilStep.factor]

/-- The eta eigenvalue attached to one chosen standard lift. -/
noncomputable def EtaWeilStep.phase : EtaWeilStep → ℂ
  | .inversion => Complex.I.sqrt⁻¹
  | .translation n => Complex.exp (Real.pi * Complex.I * n / 12)

@[simp] theorem EtaWeilStep.phase_inversion :
    EtaWeilStep.inversion.phase = Complex.I.sqrt⁻¹ := (rfl)

@[simp] theorem EtaWeilStep.phase_translation (n : ℤ) :
    (EtaWeilStep.translation n).phase =
      Complex.exp (Real.pi * Complex.I * n / 12) := (rfl)

/-- Integral powers of the finite Weil translation formula. -/
noncomputable def finiteWeilTranslation (n : ℤ) (f : ZMod 12 → ℂ)
    (r : ZMod 12) : ℂ :=
  Complex.exp (Real.pi * Complex.I * n * (discriminantQuadratic r).val / 12) * f r

@[simp] theorem finiteWeilTranslation_apply (n : ℤ) (f : ZMod 12 → ℂ)
    (r : ZMod 12) :
    finiteWeilTranslation n f r =
      Complex.exp (Real.pi * Complex.I * n * (discriminantQuadratic r).val / 12) * f r :=
  (rfl)

theorem finiteWeilTranslation_weilInputVector (n : ℤ) :
    finiteWeilTranslation n (weilInputVectorAs ℂ) =
      fun r => Complex.exp (Real.pi * Complex.I * n / 12) *
        weilInputVectorAs ℂ r := by
  funext r
  by_cases hr : weilInputVector r = 0
  · simp [finiteWeilTranslation, weilInputVectorAs, hr]
  · rw [finiteWeilTranslation, weilInputVector_quadratic_support hr]
    have hval : (1 : ZMod 24).val = 1 := by decide
    simp only [hval, Nat.cast_one, mul_one]

/-- The finite action associated with each generator formula. -/
noncomputable def EtaWeilStep.finiteAction (g : EtaWeilStep)
    (f : ZMod 12 → ℂ) : ZMod 12 → ℂ :=
  match g with
  | .inversion => finiteWeilS f
  | .translation n => finiteWeilTranslation n f

@[simp] theorem EtaWeilStep.finiteAction_inversion (f : ZMod 12 → ℂ) :
    EtaWeilStep.inversion.finiteAction f = finiteWeilS f := (rfl)

@[simp] theorem EtaWeilStep.finiteAction_translation (n : ℤ) (f : ZMod 12 → ℂ) :
    (EtaWeilStep.translation n).finiteAction f = finiteWeilTranslation n f := (rfl)

theorem finiteWeilS_smul (a : ℂ) (f : ZMod 12 → ℂ) :
    finiteWeilS (fun r => a * f r) = fun s => a * finiteWeilS f s := by
  funext s
  have hsum :
      (∑ r : ZMod 12, (a * f r) *
        Complex.exp ((Real.pi / 6) * Complex.I) ^ (-(r * s)).val) =
      a * ∑ r : ZMod 12, f r *
        Complex.exp ((Real.pi / 6) * Complex.I) ^ (-(r * s)).val := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  simp only [finiteWeilS, fourierNumerator, hsum]
  ring

theorem finiteWeilTranslation_smul (n : ℤ) (a : ℂ) (f : ZMod 12 → ℂ) :
    finiteWeilTranslation n (fun r => a * f r) =
      fun r => a * finiteWeilTranslation n f r := by
  funext r
  simp only [finiteWeilTranslation]
  ring

theorem EtaWeilStep.finiteAction_smul (g : EtaWeilStep) (a : ℂ)
    (f : ZMod 12 → ℂ) :
    g.finiteAction (fun r => a * f r) =
      fun r => a * g.finiteAction f r := by
  cases g with
  | inversion => exact finiteWeilS_smul a f
  | translation n => exact finiteWeilTranslation_smul n a f

/-- Eta's inversion scalar agrees with the signature-one Weil S phase. -/
theorem eta_inversion_phase :
    Complex.I.sqrt⁻¹ = Complex.exp (-(Real.pi / 4) * Complex.I) := by
  have hsqrt : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)))
  have hplus : (1 + Complex.I : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
  have hsqrt_sq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hreal : Real.sqrt (1 / 2) = Real.sqrt 2 / 2 := by
    have hhalf := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have htwo := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hhalf_nonneg := Real.sqrt_nonneg (1 / 2)
    have htwo_nonneg := Real.sqrt_nonneg 2
    nlinarith
  have hexp : Complex.exp (-(Real.pi / 4) * Complex.I) =
      (Real.sqrt 2 : ℂ) / 2 * (1 - Complex.I) := by
    rw [Complex.exp_mul_I]
    have harg : (Real.pi : ℂ) / 4 = ((Real.pi / 4 : ℝ) : ℂ) := by norm_num
    rw [harg, Complex.cos_neg, Complex.sin_neg]
    norm_cast
    rw [Real.cos_pi_div_four, Real.sin_pi_div_four]
    push_cast
    ring
  rw [Complex.sqrt_I, hexp]
  field_simp [hsqrt, hplus]
  rw [hreal]
  push_cast
  calc
    2 = ((Real.sqrt 2 : ℂ) ^ 2 / 2) * (1 - Complex.I ^ 2) := by
      rw [hsqrt_sq, Complex.I_sq]
      ring
    _ = _ := by ring

theorem EtaWeilStep.finiteAction_input (g : EtaWeilStep) :
    g.finiteAction (weilInputVectorAs ℂ) =
      fun r => g.phase * weilInputVectorAs ℂ r := by
  cases g with
  | inversion =>
      simp only [EtaWeilStep.finiteAction, EtaWeilStep.phase]
      rw [eta_inversion_phase]
      exact finiteWeilS_weilInputVector
  | translation n =>
      exact finiteWeilTranslation_weilInputVector n

/-- Eta's actual transformation under each generator. -/
theorem EtaWeilStep.eta_action (g : EtaWeilStep) (z : UpperHalfPlane) :
    ModularForm.eta (g.act z : ℂ) =
      g.phase * g.factor z * ModularForm.eta z := by
  cases g with
  | inversion =>
      rw [EtaWeilStep.act, UpperHalfPlane.modular_S_smul]
      rw [EtaWeilStep.phase, EtaWeilStep.factor]
      have harg : (-(z : ℂ))⁻¹ = -1 / (z : ℂ) := by
        field_simp [z.ne_zero]
      change ModularForm.eta ((-(z : ℂ))⁻¹) =
        Complex.I.sqrt⁻¹ * (z : ℂ).sqrt * ModularForm.eta (z : ℂ)
      rw [harg]
      exact eta_neg_inv z.im_pos
  | translation n =>
      simpa only [EtaWeilStep.act, EtaWeilStep.phase, EtaWeilStep.factor,
        UpperHalfPlane.coe_vadd, Complex.ofReal_intCast, one_mul, mul_one,
        add_comm] using eta_add_int (z : ℂ) n

/-- Apply the rightmost generator first. -/
noncomputable def etaWeilWordAction : List EtaWeilStep → UpperHalfPlane → UpperHalfPlane
  | [], z => z
  | g :: w, z => g.act (etaWeilWordAction w z)

@[simp] theorem etaWeilWordAction_nil (z : UpperHalfPlane) :
    etaWeilWordAction [] z = z := (rfl)

@[simp] theorem etaWeilWordAction_cons (g : EtaWeilStep) (w : List EtaWeilStep)
    (z : UpperHalfPlane) :
    etaWeilWordAction (g :: w) z = g.act (etaWeilWordAction w z) := (rfl)

/-- The ordered product of eta and Weil eigenvalues. -/
noncomputable def etaWeilWordPhase : List EtaWeilStep → ℂ
  | [] => 1
  | g :: w => g.phase * etaWeilWordPhase w

@[simp] theorem etaWeilWordPhase_nil : etaWeilWordPhase [] = 1 := (rfl)

@[simp] theorem etaWeilWordPhase_cons (g : EtaWeilStep) (w : List EtaWeilStep) :
    etaWeilWordPhase (g :: w) = g.phase * etaWeilWordPhase w := (rfl)

/-- The ordered product of automorphy square roots. -/
noncomputable def etaWeilWordFactor : List EtaWeilStep → UpperHalfPlane → ℂ
  | [], _ => 1
  | g :: w, z => g.factor (etaWeilWordAction w z) * etaWeilWordFactor w z

@[simp] theorem etaWeilWordFactor_nil (z : UpperHalfPlane) :
    etaWeilWordFactor [] z = 1 := (rfl)

@[simp] theorem etaWeilWordFactor_cons (g : EtaWeilStep) (w : List EtaWeilStep)
    (z : UpperHalfPlane) :
    etaWeilWordFactor (g :: w) z =
      g.factor (etaWeilWordAction w z) * etaWeilWordFactor w z := (rfl)

theorem etaWeilWordFactor_ne_zero (w : List EtaWeilStep)
    (z : UpperHalfPlane) : etaWeilWordFactor w z ≠ 0 := by
  induction w generalizing z with
  | nil => simp [etaWeilWordFactor]
  | cons g w ih =>
      change g.factor (etaWeilWordAction w z) * etaWeilWordFactor w z ≠ 0
      exact mul_ne_zero (g.factor_ne_zero _) (ih z)

/-- Composition of the two finite generator formulas, rightmost first. -/
noncomputable def etaWeilWordFiniteAction : List EtaWeilStep →
    (ZMod 12 → ℂ) → (ZMod 12 → ℂ)
  | [], f => f
  | g :: w, f => g.finiteAction (etaWeilWordFiniteAction w f)

@[simp] theorem etaWeilWordFiniteAction_nil (f : ZMod 12 → ℂ) :
    etaWeilWordFiniteAction [] f = f := (rfl)

@[simp] theorem etaWeilWordFiniteAction_cons (g : EtaWeilStep) (w : List EtaWeilStep)
    (f : ZMod 12 → ℂ) :
    etaWeilWordFiniteAction (g :: w) f =
      g.finiteAction (etaWeilWordFiniteAction w f) := (rfl)

/-- Every generator word has the same finite eigenvalue and eta scalar. -/
theorem etaWeilWordFiniteAction_input (w : List EtaWeilStep) :
    etaWeilWordFiniteAction w (weilInputVectorAs ℂ) =
      fun r => etaWeilWordPhase w * weilInputVectorAs ℂ r := by
  induction w with
  | nil => simp [etaWeilWordFiniteAction, etaWeilWordPhase]
  | cons g w ih =>
      simp only [etaWeilWordFiniteAction, etaWeilWordPhase, ih]
      rw [g.finiteAction_smul, g.finiteAction_input]
      funext r
      ring

/-- The actual eta product transforms along every standard generator word
with exactly the scalar of the finite Weil input. -/
theorem eta_action_generator_word (w : List EtaWeilStep)
    (z : UpperHalfPlane) :
    ModularForm.eta (etaWeilWordAction w z : ℂ) =
      etaWeilWordPhase w * etaWeilWordFactor w z * ModularForm.eta z := by
  induction w generalizing z with
  | nil => simp [etaWeilWordAction, etaWeilWordPhase, etaWeilWordFactor]
  | cons g w ih =>
      change ModularForm.eta (g.act (etaWeilWordAction w z) : ℂ) = _
      rw [g.eta_action, ih]
      simp only [etaWeilWordPhase, etaWeilWordFactor]
      ring

/-- The eigenvalue attached to a generator word is determined by its actual
upper-half-plane action and ordered square-root factor at one point. This is
the local descent test needed to define a metaplectic action on the input line. -/
theorem etaWeilWordPhase_eq_of_action_factor_eq
    (w w' : List EtaWeilStep) (z : UpperHalfPlane)
    (hact : etaWeilWordAction w z = etaWeilWordAction w' z)
    (hfactor : etaWeilWordFactor w z = etaWeilWordFactor w' z) :
    etaWeilWordPhase w = etaWeilWordPhase w' := by
  have hprod : etaWeilWordPhase w * etaWeilWordFactor w z * ModularForm.eta z =
      etaWeilWordPhase w' * etaWeilWordFactor w' z * ModularForm.eta z := by
    calc
      _ = ModularForm.eta (etaWeilWordAction w z : ℂ) :=
        (eta_action_generator_word w z).symm
      _ = ModularForm.eta (etaWeilWordAction w' z : ℂ) := by rw [hact]
      _ = _ := eta_action_generator_word w' z
  rw [hfactor] at hprod
  have hn : etaWeilWordFactor w' z * ModularForm.eta z ≠ 0 :=
    mul_ne_zero (etaWeilWordFactor_ne_zero w' z)
      (ModularForm.eta_ne_zero z.im_pos)
  apply (mul_right_cancel₀ hn)
  simpa only [mul_assoc] using hprod

end Theta
end SptClassification
