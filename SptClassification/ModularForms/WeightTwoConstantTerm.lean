/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.MeromorphicCusp

/-!
# Constant terms of weakly holomorphic weight-two forms

The cusp Laurent coefficient is recovered after clearing its pole and then
vanishes by the horizontal period integral [rolenManuscript, §3].
-/

public section

namespace SptClassification

open UpperHalfPlane
open scoped Manifold

/-- The constant Laurent coefficient of a meromorphic period-one cusp function,
expressed as its horizontal Fourier integral at height one. The comparison with
the Taylor coefficient after any analytic pole clearing is proved below. -/
noncomputable def meromorphicCuspConstantTerm (f : ℂ → ℂ) : ℂ :=
  ∫ x : ℝ in (0 : ℝ)..1, f ((x : ℂ) + Complex.I)

private theorem qParam_add_one (z : ℂ) :
    Function.Periodic.qParam 1 (z + 1) = Function.Periodic.qParam 1 z := by
  simp [Function.Periodic.qParam, add_mul, mul_add, Complex.exp_add,
    mul_comm, mul_left_comm]
  convert Complex.exp_two_pi_mul_I using 1
  ring_nf

/-- Clearing a period-one cusp pole preserves period one on the upper half-plane. -/
theorem poleClearing_periodic {f : ℂ → ℂ}
    (hT : ∀ z : ℂ, 0 < z.im → f (z + 1) = f z) (M : ℕ) :
    Function.Periodic
      ((fun τ : UpperHalfPlane => Function.Periodic.qParam 1 τ ^ M * f τ) ∘ ofComplex)
      1 := by
  intro z
  by_cases hz : 0 < z.im
  · have hz1 : 0 < (z + 1).im := by simpa using hz
    have hzc : ((ofComplex z : UpperHalfPlane) : ℂ) = z := by
      let τ : UpperHalfPlane := ⟨z, hz⟩
      change ((ofComplex (τ : ℂ) : UpperHalfPlane) : ℂ) = z
      rw [ofComplex_apply]
    have hz1c : ((ofComplex (z + 1) : UpperHalfPlane) : ℂ) = z + 1 := by
      let τ : UpperHalfPlane := ⟨z + 1, hz1⟩
      change ((ofComplex (τ : ℂ) : UpperHalfPlane) : ℂ) = z + 1
      rw [ofComplex_apply]
    simp only [Function.comp_apply, hzc, hz1c, qParam_add_one, hT z hz]
  · have hz1 : ¬ 0 < (z + 1).im := by simpa using hz
    simp only [Function.comp_apply]
    have hnot : ¬ ∃ a : UpperHalfPlane, a ∈ Set.univ ∧ (a : ℂ) = z := by
      rintro ⟨a, _, ha⟩
      apply hz
      rw [← ha]
      exact a.im_pos
    have hnot1 : ¬ ∃ a : UpperHalfPlane, a ∈ Set.univ ∧ (a : ℂ) = z + 1 := by
      rintro ⟨a, _, ha⟩
      apply hz1
      rw [← ha]
      exact a.im_pos
    have heq : (ofComplex (z + 1) : UpperHalfPlane) = ofComplex z := by
      simp [UpperHalfPlane.ofComplex,
        Topology.IsOpenEmbedding.toOpenPartialHomeomorph, Function.invFunOn]
      simp only [dite_eq_right hnot1, dite_eq_right hnot]
    rw [heq]

/-- The coefficient that becomes the constant Laurent coefficient after
clearing a meromorphic cusp pole vanishes for a level-one weight-two form. -/
theorem weightTwo_constantTerm_afterClearing_eq_zero {f G : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet)
    (hT : ∀ z : ℂ, 0 < z.im → f (z + 1) = f z)
    (hS : ∀ z : ℂ, 0 < z.im → f (-1 / z) = z ^ 2 * f z)
    (hEq : ∀ τ : UpperHalfPlane, G (Function.Periodic.qParam 1 τ) = f τ)
    (M : ℕ) (hM : AnalyticAt ℂ (fun q : ℂ => q ^ M * G q) 0) :
    (qExpansion 1 (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam 1 τ ^ M * f τ)).coeff M = 0 := by
  apply weightTwo_poleCleared_coefficient_eq_zero hf hT hS M (by intro τ; rfl)
    (poleClearing_periodic hT M) (mdifferentiable_poleClearing hf M)
  simpa only [hEq] using isBoundedAtImInfty_of_analytic_qParam hM

/-- If a pole clearing is bounded at the cusp, its Fourier coefficient at the
clearing exponent is the intrinsic constant Laurent coefficient. This form of
the comparison also applies when boundedness comes from a convergent series
[rolenManuscript, §3]. -/
theorem meromorphicCuspConstantTerm_eq_qExpansion_coeff_of_bounded {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet)
    (hT : ∀ z : ℂ, 0 < z.im → f (z + 1) = f z)
    (M : ℕ)
    (hB : IsBoundedAtImInfty (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam 1 τ ^ M * f τ)) :
    meromorphicCuspConstantTerm f =
      (qExpansion 1 (fun τ : UpperHalfPlane =>
        Function.Periodic.qParam 1 τ ^ M * f τ)).coeff M := by
  rw [qExpansion_coeff_eq_intervalIntegral (by norm_num : (0 : ℝ) < 1)
    (poleClearing_periodic hT M) (mdifferentiable_poleClearing hf M)
    hB M (by norm_num : (0 : ℝ) < 1)]
  simp only [Complex.ofReal_one, div_one, one_mul]
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp [meromorphicCuspConstantTerm]
  have hq : Function.Periodic.qParam 1 ((x : ℂ) + Complex.I) ≠ 0 :=
    Complex.exp_ne_zero _
  field_simp [hq]

/-- The coefficient at the pole-clearing index is the intrinsic constant
Laurent coefficient, independently of modular weight or the chosen exponent.
The `qExpansion` is the Taylor series of the analytic cusp function
[rolenManuscript, §3]. -/
theorem meromorphicCuspConstantTerm_eq_qExpansion_coeff {f G : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet)
    (hT : ∀ z : ℂ, 0 < z.im → f (z + 1) = f z)
    (hEq : ∀ τ : UpperHalfPlane, G (Function.Periodic.qParam 1 τ) = f τ)
    (M : ℕ) (hM : AnalyticAt ℂ (fun q : ℂ => q ^ M * G q) 0) :
    meromorphicCuspConstantTerm f =
      (qExpansion 1 (fun τ : UpperHalfPlane =>
        Function.Periodic.qParam 1 τ ^ M * f τ)).coeff M := by
  exact meromorphicCuspConstantTerm_eq_qExpansion_coeff_of_bounded hf hT M
    (by simpa only [hEq] using isBoundedAtImInfty_of_analytic_qParam hM)

/-- Every meromorphic level-one weight-two form has a pole-clearing exponent
whose Taylor coefficient at that exponent is zero. -/
theorem weightTwo_exists_zero_constantTerm {f G : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet)
    (hT : ∀ z : ℂ, 0 < z.im → f (z + 1) = f z)
    (hS : ∀ z : ℂ, 0 < z.im → f (-1 / z) = z ^ 2 * f z)
    (hG : MeromorphicAt G 0)
    (hEq : ∀ τ : UpperHalfPlane, G (Function.Periodic.qParam 1 τ) = f τ) :
    ∃ M : ℕ, AnalyticAt ℂ (fun q : ℂ => q ^ M * G q) 0 ∧
      (qExpansion 1 (fun τ : UpperHalfPlane =>
        Function.Periodic.qParam 1 τ ^ M * f τ)).coeff M = 0 := by
  obtain ⟨M, hM⟩ := MeromorphicAt.exists_analytic_poleClearing hG
  exact ⟨M, hM, weightTwo_constantTerm_afterClearing_eq_zero hf hT hS hEq M hM⟩

/-- The coefficient at the pole-clearing index is independent of the chosen
analytic clearing exponent for a weight-two form. -/
theorem weightTwo_constantTerm_independent {f G : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet)
    (hT : ∀ z : ℂ, 0 < z.im → f (z + 1) = f z)
    (hEq : ∀ τ : UpperHalfPlane, G (Function.Periodic.qParam 1 τ) = f τ)
    (M N : ℕ)
    (hM : AnalyticAt ℂ (fun q : ℂ => q ^ M * G q) 0)
    (hN : AnalyticAt ℂ (fun q : ℂ => q ^ N * G q) 0) :
    (qExpansion 1 (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam 1 τ ^ M * f τ)).coeff M =
    (qExpansion 1 (fun τ : UpperHalfPlane =>
        Function.Periodic.qParam 1 τ ^ N * f τ)).coeff N := by
  rw [← meromorphicCuspConstantTerm_eq_qExpansion_coeff hf hT hEq M hM,
    ← meromorphicCuspConstantTerm_eq_qExpansion_coeff hf hT hEq N hN]

/-- The intrinsic constant Laurent coefficient vanishes for every level-one
weakly holomorphic weight-two form [rolenManuscript, §3]. -/
theorem weightTwo_meromorphic_constantTerm_eq_zero {f G : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet)
    (hT : ∀ z : ℂ, 0 < z.im → f (z + 1) = f z)
    (hS : ∀ z : ℂ, 0 < z.im → f (-1 / z) = z ^ 2 * f z)
    (hG : MeromorphicAt G 0)
    (hEq : ∀ τ : UpperHalfPlane, G (Function.Periodic.qParam 1 τ) = f τ) :
    meromorphicCuspConstantTerm f = 0 := by
  obtain ⟨M, hM⟩ := MeromorphicAt.exists_analytic_poleClearing hG
  rw [meromorphicCuspConstantTerm_eq_qExpansion_coeff hf hT hEq M hM]
  exact weightTwo_constantTerm_afterClearing_eq_zero hf hT hS hEq M hM

end SptClassification
