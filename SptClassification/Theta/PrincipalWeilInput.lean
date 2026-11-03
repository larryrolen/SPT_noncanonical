/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.PrincipalForms
public import SptClassification.Theta.MetaplecticWords

/-!
# The principal weight-five-halves Weil input

The actual analytic input is `K_d (e₁ - e₅ - e₇ + e₁₁)`. Its finite Weil
transformation, integral Fourier coefficients and sole negative exponent are
the input calculations in [rolenManuscript, §3, lines 339–343]. These
calculations precede the meromorphic lifting theorem [borcherds1998, Theorem 14.3].
-/

public section

namespace SptClassification
namespace Theta

open UpperHalfPlane
open scoped MatrixGroups Manifold

/-- Scalar multiplication commutes with every finite Weil generator word. -/
theorem etaWeilWordFiniteAction_smul (w : List EtaWeilStep) (a : ℂ)
    (f : ZMod 12 → ℂ) :
    etaWeilWordFiniteAction w (fun r => a * f r) =
      fun r => a * etaWeilWordFiniteAction w f r := by
  induction w with
  | nil => simp only [etaWeilWordFiniteAction_nil]
  | cons g w ih =>
      simp only [etaWeilWordFiniteAction_cons, ih, g.finiteAction_smul]

/-- An eta weak form has the exact half-integral weight on standard lifts. -/
theorem etaWeakForm_map_word {k : ℕ} (f : EtaWeaklyHolomorphicForm k)
    (w : List EtaWeilStep) (τ : UpperHalfPlane) :
    f (etaWeilWordAction w τ) =
      etaWeilWordPhase w * etaWeilWordFactor w τ ^ (2 * k + 1) * f τ := by
  let γ := etaWeilWordMatrix w
  have hη : etaAutomorphyFactor (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ =
      etaWeilWordPhase w * etaWeilWordFactor w τ := by
    apply mul_right_cancel₀ (ModularForm.eta_ne_zero τ.im_pos)
    rw [etaAutomorphyFactor_mul_eta]
    change ModularForm.eta (γ • τ : UpperHalfPlane) = _
    rw [etaWeilWordMatrix_smul, eta_action_generator_word]
  have hden : denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ =
      etaWeilWordFactor w τ ^ 2 :=
    (metaplecticDenominator_eq_denom γ τ).symm.trans
      (etaWeilWordFactor_sq w τ).symm
  have h := f.map_action (Matrix.SpecialLinearGroup.mapGL ℝ γ) ⟨γ, rfl⟩ τ
  change f (γ • τ) = _ at h
  rw [etaWeilWordMatrix_smul, hη, hden] at h
  rw [h, pow_add, pow_one, pow_mul]
  ring

/-- The actual vector-valued analytic function used in the meromorphic lift. -/
noncomputable def principalWeilInput (d : ℕ) (τ : UpperHalfPlane) : ZMod 12 → ℂ :=
  fun r => principalKForm d τ * weilInputVectorAs ℂ r

/-- The component formula for the actual input. -/
theorem principalWeilInput_apply (d : ℕ) (τ : UpperHalfPlane) (r : ZMod 12) :
    principalWeilInput d τ r = principalKForm d τ * weilInputVectorAs ℂ r := (rfl)

/-- The integral coefficient at exponent `n/24` in component `r`. -/
noncomputable def principalWeilCoefficient (d : ℕ) (n : ℤ) (r : ZMod 12) : ℤ :=
  QSeries.principalKFourier d n * weilInputVector r

/-- The input transforms with weight `5/2` and the computed finite Weil action. -/
theorem principalWeilInput_map_word (d : ℕ) (w : List EtaWeilStep)
    (τ : UpperHalfPlane) :
    principalWeilInput d (etaWeilWordAction w τ) =
      fun r => etaWeilWordFactor w τ ^ 5 *
        etaWeilWordFiniteAction w (principalWeilInput d τ) r := by
  change (fun r => principalKForm d (etaWeilWordAction w τ) * weilInputVectorAs ℂ r) = _
  rw [etaWeakForm_map_word]
  have hinput : principalWeilInput d τ =
      fun r => principalKForm d τ * weilInputVectorAs ℂ r := (rfl)
  rw [hinput, etaWeilWordFiniteAction_smul, etaWeilWordFiniteAction_input]
  funext r
  norm_num
  ring

/-- Each component is holomorphic on the upper half-plane. -/
theorem principalWeilInput_holomorphic (d : ℕ) (r : ZMod 12) :
    MDiff (fun τ => principalWeilInput d τ r) :=
  (principalKForm d).holomorphic.mul mdifferentiable_const

/-- The components are meromorphic in the period-24 cusp coordinate. -/
theorem principalWeilInput_meromorphic_cusp (d : ℕ) (r : ZMod 12) :
    ∃ G : ℂ → ℂ, MeromorphicAt G 0 ∧
      ∀ τ : UpperHalfPlane,
        G (Function.Periodic.qParam 24 τ) = principalWeilInput d τ r := by
  obtain ⟨G, hG, hτ⟩ := (principalKForm d).has_meromorphic_cusp
  refine ⟨fun q => G q * weilInputVectorAs ℂ r,
    hG.mul (MeromorphicAt.const _ _), ?_⟩
  intro τ
  simp only [hτ, principalWeilInput]

/-- Pole clearing gives the convergent Fourier series of every component. -/
theorem principalWeilInput_hasSum (d : ℕ) (hd : d % 24 = 23)
    (τ : UpperHalfPlane) (r : ZMod 12) :
    HasSum (fun m : ℕ =>
      (principalWeilCoefficient d (24 * (m : ℤ) - d) r : ℂ) *
        Function.Periodic.qParam 1 τ ^ m)
      (Function.Periodic.qParam 1 τ ^ QSeries.principalIndex d *
        (Function.Periodic.qParam 24 τ)⁻¹ * principalWeilInput d τ r) := by
  simpa only [principalWeilCoefficient, principalWeilInput, weilInputVectorAs,
    Int.cast_mul, mul_assoc, mul_left_comm, mul_comm] using
    (principalKForm_hasSum d hd τ).mul_right (weilInputVectorAs ℂ r)

/-- The negative Fourier part is exactly `q^(-d/24) v`. -/
theorem principalWeilCoefficient_negative (d : ℕ) (hd : d % 24 = 23)
    (n : ℤ) (hn : n < 0) (r : ZMod 12) :
    principalWeilCoefficient d n r =
      if n = -(d : ℤ) then weilInputVector r else 0 := by
  rw [principalWeilCoefficient, QSeries.principalKFourier_negative d hd n hn]
  split <;> simp

/-- The constant term vanishes in every discriminant component. -/
theorem principalWeilCoefficient_zero (d : ℕ) (r : ZMod 12) :
    principalWeilCoefficient d 0 r = 0 := by
  rw [principalWeilCoefficient,
    (QSeries.principalFourier_zero_of_mod_ne d 0 0 (by norm_num)).2, zero_mul]

/-- Nonzero coefficients have the required quadratic class and exponent. -/
theorem principalWeilCoefficient_support (d : ℕ) (n : ℤ) (r : ZMod 12)
    (h : principalWeilCoefficient d n r ≠ 0) :
    n % 24 = 1 ∧ discriminantQuadratic r = 1 := by
  have hv : weilInputVector r ≠ 0 := by
    intro hr
    exact h (by simp [principalWeilCoefficient, hr])
  refine ⟨?_, weilInputVector_quadratic_support hv⟩
  by_contra hn
  exact h (by rw [principalWeilCoefficient,
    (QSeries.principalFourier_zero_of_mod_ne d 0 n hn).2, zero_mul])

end Theta
end SptClassification
