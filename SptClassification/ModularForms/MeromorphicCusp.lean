/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.WeightTwoFourierCoefficient
public import Mathlib.Analysis.Meromorphic.Basic

/-!
# Clearing a meromorphic cusp pole

A meromorphic cusp representative has an arbitrary value at the origin. The
definition of `MeromorphicAt` nevertheless supplies a power that makes the
*actual product* analytic there. This exponent may be larger than the pole
order, and is sufficient for the weight-two coefficient argument
[rolenManuscript, §3].
-/

public section

namespace SptClassification

open UpperHalfPlane Filter
open scoped Manifold

/-- The nome of any real width is holomorphic on the upper half-plane. -/
theorem mdifferentiable_qParam (h : ℝ) :
    MDiff (fun τ : UpperHalfPlane => Function.Periodic.qParam h τ) := by
  intro τ
  apply mdifferentiableAt_iff.mpr
  apply (Function.Periodic.differentiable_qParam (h := h) (τ : ℂ)).congr_of_eventuallyEq
  filter_upwards [eventuallyEq_coe_comp_ofComplex τ.im_pos] with z hz
  exact congrArg (Function.Periodic.qParam h) hz

/-- Translating by the width leaves the nome unchanged. -/
theorem qParam_vadd {h : ℝ} (hh : h ≠ 0) (τ : UpperHalfPlane) :
    Function.Periodic.qParam h (h +ᵥ τ) = Function.Periodic.qParam h τ := by
  unfold Function.Periodic.qParam
  rw [coe_vadd]
  have he : 2 * (Real.pi : ℂ) * Complex.I * ((h : ℂ) + τ) / h =
      2 * (Real.pi : ℂ) * Complex.I * τ / h + 2 * (Real.pi : ℂ) * Complex.I := by
    field_simp [Complex.ofReal_ne_zero.mpr hh]
    <;> ring
  rw [he, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- The period-one nome is holomorphic on the upper half-plane. -/
theorem mdifferentiable_qParam_one :
    MDiff (fun τ : UpperHalfPlane => Function.Periodic.qParam 1 τ) := by
  intro τ
  apply mdifferentiableAt_iff.mpr
  have hd : DifferentiableAt ℂ (Function.Periodic.qParam 1) (τ : ℂ) := by
    unfold Function.Periodic.qParam
    fun_prop
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventuallyEq_coe_comp_ofComplex τ.im_pos] with z hz
  exact congrArg (Function.Periodic.qParam 1) hz

private theorem mdifferentiableOn_upperHalfPlane {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet) :
    MDiff (fun τ : UpperHalfPlane => f τ) := by
  intro τ
  apply mdifferentiableAt_iff.mpr
  have hd : DifferentiableAt ℂ f (τ : ℂ) :=
    (hf τ τ.im_pos).differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventuallyEq_coe_comp_ofComplex τ.im_pos] with z hz
  exact congrArg f hz

/-- Multiplying a holomorphic upper-half-plane function by a nome power preserves
holomorphy. -/
theorem mdifferentiable_poleClearing {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet) (M : ℕ) :
    MDiff (fun τ : UpperHalfPlane => Function.Periodic.qParam 1 τ ^ M * f τ) := by
  exact (mdifferentiable_qParam_one.pow M).mul (mdifferentiableOn_upperHalfPlane hf)

/-- A finite nonnegative power clears a meromorphic cusp germ at zero. -/
theorem MeromorphicAt.exists_analytic_poleClearing {G : ℂ → ℂ}
    (hG : MeromorphicAt G 0) :
    ∃ M : ℕ, AnalyticAt ℂ (fun q : ℂ => q ^ M * G q) 0 := by
  obtain ⟨M, hM⟩ := hG
  refine ⟨M, ?_⟩
  simpa only [sub_zero, smul_eq_mul] using hM

/-- An analytic cusp germ is bounded when evaluated at the nome near infinity. -/
theorem isBoundedAtImInfty_of_analytic_qParam {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g 0) :
    IsBoundedAtImInfty (fun τ : UpperHalfPlane =>
      g (Function.Periodic.qParam 1 τ)) := by
  have hq : Tendsto (fun τ : UpperHalfPlane => Function.Periodic.qParam 1 τ)
      atImInfty (nhds 0) := qParam_tendsto_atImInfty (by norm_num)
  have hlim : Tendsto (fun τ : UpperHalfPlane =>
      g (Function.Periodic.qParam 1 τ)) atImInfty (nhds (g 0)) :=
    hg.continuousAt.tendsto.comp hq
  obtain ⟨C, hC⟩ := hlim.norm.isBoundedUnder_le
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp hC
  exact isBoundedAtImInfty_iff.mpr ⟨C, A, hA⟩

/-- The limit of a high-cusp analytic representative is its value at zero. -/
theorem tendsto_atImInfty_of_analytic_qParam_germ
    {f : UpperHalfPlane → ℂ} {g : ℂ → ℂ} {h r : ℝ}
    (hh : 0 < h) (hr : 0 < r) (hg : AnalyticAt ℂ g 0) (Y : ℝ)
    (heq : ∀ z : UpperHalfPlane, Y < z.im →
      ‖Function.Periodic.qParam h z‖ < r →
      g (Function.Periodic.qParam h z) = f z) :
    Tendsto f atImInfty (nhds (g 0)) := by
  have hq := qParam_tendsto_atImInfty hh
  have hsmall : ∀ᶠ z : UpperHalfPlane in atImInfty,
      ‖Function.Periodic.qParam h z‖ < r := by
    have hs : ∀ᶠ z : UpperHalfPlane in atImInfty,
        Function.Periodic.qParam h z ∈ Metric.ball (0 : ℂ) r :=
      hq (Metric.ball_mem_nhds (0 : ℂ) hr)
    simpa only [Metric.mem_ball, dist_zero_right] using hs
  have hhigh : ∀ᶠ z : UpperHalfPlane in atImInfty, Y < z.im := by
    apply (atImInfty_mem _).mpr
    exact ⟨Y + 1, fun z hz => by dsimp at hz ⊢; linarith⟩
  apply (hg.continuousAt.tendsto.comp hq).congr'
  filter_upwards [hhigh, hsmall] with z hz hnorm
  exact heq z hz hnorm

/-- An analytic germ agreeing only sufficiently high in a cusp still gives
the bound required for a modular form. The width may be any positive real. -/
theorem isBoundedAtImInfty_of_analytic_qParam_germ
    {f : UpperHalfPlane → ℂ} {g : ℂ → ℂ} {h r : ℝ}
    (hh : 0 < h) (hr : 0 < r) (hg : AnalyticAt ℂ g 0) (Y : ℝ)
    (heq : ∀ z : UpperHalfPlane, Y < z.im →
      ‖Function.Periodic.qParam h z‖ < r →
      g (Function.Periodic.qParam h z) = f z) :
    IsBoundedAtImInfty f := by
  have hlim := tendsto_atImInfty_of_analytic_qParam_germ hh hr hg Y heq
  obtain ⟨C, hC⟩ := hlim.norm.isBoundedUnder_le
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp hC
  exact isBoundedAtImInfty_iff.mpr ⟨C, A, hA⟩

/-- Pole clearing yields a bounded upper-half-plane function at the cusp. -/
theorem MeromorphicAt.exists_bounded_poleClearing {G : ℂ → ℂ}
    (hG : MeromorphicAt G 0) :
    ∃ M : ℕ, AnalyticAt ℂ (fun q : ℂ => q ^ M * G q) 0 ∧
      IsBoundedAtImInfty (fun τ : UpperHalfPlane =>
        Function.Periodic.qParam 1 τ ^ M * G (Function.Periodic.qParam 1 τ)) := by
  obtain ⟨M, hM⟩ := MeromorphicAt.exists_analytic_poleClearing hG
  exact ⟨M, hM, isBoundedAtImInfty_of_analytic_qParam hM⟩

/-- A meromorphic representative bounds the pole-cleared actual cusp function. -/
theorem MeromorphicAt.exists_bounded_poleClearing_of_eq
    {G : ℂ → ℂ} {f : UpperHalfPlane → ℂ}
    (hG : MeromorphicAt G 0)
    (hEq : ∀ τ : UpperHalfPlane, G (Function.Periodic.qParam 1 τ) = f τ) :
    ∃ M : ℕ, IsBoundedAtImInfty (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam 1 τ ^ M * f τ) := by
  obtain ⟨M, _, hM⟩ := MeromorphicAt.exists_bounded_poleClearing hG
  refine ⟨M, ?_⟩
  simpa only [hEq] using hM

/-- Conversely, a bounded holomorphic periodic function after pole clearing
supplies a meromorphic representative of the original function. This uses
Mathlib's removable-singularity theorem for the bounded cusp function. -/
theorem exists_meromorphic_cusp_of_bounded_poleClearing
    {f : UpperHalfPlane → ℂ} {h : ℝ} (hh : 0 < h) (M : ℕ)
    (hper : Function.Periodic
      ((fun τ : UpperHalfPlane => Function.Periodic.qParam h τ ^ M * f τ) ∘
        ofComplex) h)
    (hhol : MDiff (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam h τ ^ M * f τ))
    (hbdd : IsBoundedAtImInfty (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam h τ ^ M * f τ)) :
    ∃ G : ℂ → ℂ, MeromorphicAt G 0 ∧ ∀ τ : UpperHalfPlane,
      G (Function.Periodic.qParam h τ) = f τ := by
  let g : UpperHalfPlane → ℂ := fun τ => Function.Periodic.qParam h τ ^ M * f τ
  have hg : AnalyticAt ℂ (cuspFunction h g) 0 :=
    analyticAt_cuspFunction_zero hh hper hhol hbdd
  refine ⟨fun q => cuspFunction h g q / q ^ M,
    hg.meromorphicAt.div (analyticAt_id.pow M).meromorphicAt, ?_⟩
  intro τ
  dsimp only [g]
  rw [UpperHalfPlane.eq_cuspFunction τ hh.ne' hper]
  exact mul_div_cancel_left₀ (f τ)
    (pow_ne_zero M (Complex.exp_ne_zero _))

/-- A nome power bounds a function of at most exponential growth. The
inequality on the power is explicit, so the same estimate works at any
positive cusp width. -/
theorem isBoundedAtImInfty_poleClearing_of_exp_bound
    {f : UpperHalfPlane → ℂ} {h C A Y : ℝ} (_hh : 0 < h)
    (hC : 0 ≤ C) (M : ℕ) (hM : A ≤ 2 * Real.pi * M / h)
    (hf : ∀ τ : UpperHalfPlane, Y ≤ τ.im → ‖f τ‖ ≤ C * Real.exp (A * τ.im)) :
    IsBoundedAtImInfty (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam h τ ^ M * f τ) := by
  apply isBoundedAtImInfty_iff.mpr
  refine ⟨C, Y, ?_⟩
  intro τ hτ
  calc
    ‖Function.Periodic.qParam h τ ^ M * f τ‖ =
        Real.exp ((M : ℝ) * (-2 * Real.pi * τ.im / h)) * ‖f τ‖ := by
      rw [norm_mul, norm_pow, Function.Periodic.norm_qParam, Real.exp_nat_mul]
      rfl
    _ ≤ Real.exp ((M : ℝ) * (-2 * Real.pi * τ.im / h)) *
        (C * Real.exp (A * τ.im)) :=
      mul_le_mul_of_nonneg_left (hf τ hτ) (Real.exp_nonneg _)
    _ = C * Real.exp ((A - 2 * Real.pi * M / h) * τ.im) := by
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    _ ≤ C * 1 := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hM) τ.im_pos.le
    _ = C := mul_one C

/-- A holomorphic periodic function of eventual exponential growth has a
meromorphic q representative. No assertion about modularity is required. -/
theorem exists_meromorphic_cusp_of_exp_bound
    {f : UpperHalfPlane → ℂ} {h C A Y : ℝ} (hh : 0 < h)
    (hper : Function.Periodic (f ∘ ofComplex) (h : ℂ))
    (hhol : MDiff f) (hC : 0 ≤ C)
    (hf : ∀ τ : UpperHalfPlane, Y ≤ τ.im → ‖f τ‖ ≤ C * Real.exp (A * τ.im)) :
    ∃ G : ℂ → ℂ, MeromorphicAt G 0 ∧ ∀ τ : UpperHalfPlane,
      G (Function.Periodic.qParam h τ) = f τ := by
  obtain ⟨M, hM⟩ := exists_nat_ge (A * h / (2 * Real.pi))
  have hMA : A ≤ 2 * Real.pi * M / h := by
    apply (le_div_iff₀ hh).mpr
    have := (div_le_iff₀ Real.two_pi_pos).mp hM
    nlinarith
  apply exists_meromorphic_cusp_of_bounded_poleClearing hh M
  · apply UpperHalfPlane.periodic_comp_ofComplex
    intro τ
    have hp : f (h +ᵥ τ) = f τ := by
      have he : (τ : ℂ) + h = ((h +ᵥ τ : UpperHalfPlane) : ℂ) := by
        rw [coe_vadd, add_comm]
      simpa only [Function.comp_def, he, ofComplex_apply] using hper (τ : ℂ)
    rw [qParam_vadd hh.ne', hp]
  · exact ((mdifferentiable_qParam h).pow M).mul hhol
  · exact isBoundedAtImInfty_poleClearing_of_exp_bound hh hC M hMA hf

/-- Periodicity extends an exponential estimate on one strip to every real
part. The strip may start at any real number. -/
theorem exp_bound_of_periodic_strip
    {f : UpperHalfPlane → ℂ} {h a C A Y : ℝ} (hh : 0 < h)
    (hper : Function.Periodic (f ∘ ofComplex) (h : ℂ))
    (hf : ∀ τ : UpperHalfPlane, a ≤ τ.re → τ.re < a + h → Y ≤ τ.im →
      ‖f τ‖ ≤ C * Real.exp (A * τ.im)) :
    ∀ τ : UpperHalfPlane, Y ≤ τ.im → ‖f τ‖ ≤ C * Real.exp (A * τ.im) := by
  intro τ hτ
  let n : ℤ := ⌊(τ.re - a) / h⌋
  let σ : UpperHalfPlane := (-(n : ℝ) * h) +ᵥ τ
  have hn₁ := Int.floor_le ((τ.re - a) / h)
  have hn₂ := Int.lt_floor_add_one ((τ.re - a) / h)
  have hs₁ : a ≤ σ.re := by
    dsimp [σ]
    have := (le_div_iff₀ hh).mp hn₁
    dsimp [n]
    linarith
  have hs₂ : σ.re < a + h := by
    dsimp [σ]
    have := (div_lt_iff₀ hh).mp hn₂
    dsimp [n]
    nlinarith
  have he : f σ = f τ := by
    have hp := hper.sub_int_mul_eq (x := (τ : ℂ)) n
    have hs : (τ : ℂ) - (n : ℂ) * (h : ℂ) = (σ : ℂ) := by
      simp [σ, coe_vadd, sub_eq_add_neg, add_comm]
    simpa only [Function.comp_def, hs, ofComplex_apply] using hp
  simpa only [he, σ, vadd_im] using hf σ hs₁ hs₂ (by simpa [σ] using hτ)

/-- The meromorphic cusp criterion with growth assumed only on a fundamental
strip, uniformly above some height. -/
theorem exists_meromorphic_cusp_of_strip_exp_bound
    {f : UpperHalfPlane → ℂ} {h a C A Y : ℝ} (hh : 0 < h)
    (hper : Function.Periodic (f ∘ ofComplex) (h : ℂ))
    (hhol : MDiff f) (hC : 0 ≤ C)
    (hf : ∀ τ : UpperHalfPlane, a ≤ τ.re → τ.re < a + h → Y ≤ τ.im →
      ‖f τ‖ ≤ C * Real.exp (A * τ.im)) :
    ∃ G : ℂ → ℂ, MeromorphicAt G 0 ∧ ∀ τ : UpperHalfPlane,
      G (Function.Periodic.qParam h τ) = f τ :=
  exists_meromorphic_cusp_of_exp_bound hh hper hhol hC
    (exp_bound_of_periodic_strip hh hper hf)

end SptClassification
