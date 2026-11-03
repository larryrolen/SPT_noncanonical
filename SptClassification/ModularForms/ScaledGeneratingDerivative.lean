/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.ScaledGeneratingSeries

/-!
# Differentiation of the rescaled generating functions

The normalized derivative multiplies the coefficient at `24n-1` by `24n-1`.
This constructs the holomorphic part `M` in [rolenManuscript, §2].
-/

public section

namespace SptClassification

open UpperHalfPlane
open scoped Topology Manifold

/-- A convergent power series is differentiable throughout its disc. -/
theorem differentiableAt_core_of_hasSum {c : ℕ → ℂ} {f : ℂ → ℂ}
    (hc : ∀ q : ℂ, ‖q‖ < 1 → HasSum (fun n => c n * q ^ n) (f q))
    {q : ℂ} (hq : ‖q‖ < 1) : DifferentiableAt ℂ f q := by
  have hp := QSeries.hasFPowerSeriesOnBall_of_hasSum hc
  have hb : q ∈ Metric.eball (0 : ℂ) 1 := by
    simpa only [← ENNReal.coe_one, Metric.eball_coe, NNReal.coe_one,
      mem_ball_zero_iff] using hq
  exact (hp.analyticAt_of_mem hb).differentiableAt

/-- The nome has derivative `2πiq`. -/
theorem hasDerivAt_qParam_one (z : ℂ) :
    HasDerivAt (Function.Periodic.qParam 1)
      (Function.Periodic.qParam 1 z * (2 * Real.pi * Complex.I)) z := by
  change HasDerivAt (fun w => Function.Periodic.qParam 1 w) _ z
  simpa [Function.Periodic.qParam] using
    ((hasDerivAt_id z).const_mul (2 * Real.pi * Complex.I)).cexp

/-- Chain and product rules for the actual rescaling on the upper half-plane. -/
theorem hasDerivAt_scaledFourierFunction {c : ℕ → ℂ} {f : ℂ → ℂ}
    (hc : ∀ q : ℂ, ‖q‖ < 1 → HasSum (fun n => c n * q ^ n) (f q))
    (τ : UpperHalfPlane) :
    let q := Function.Periodic.qParam 1 τ
    HasDerivAt (scaledFourierFunction f ∘ ofComplex)
      ((q⁻¹ * (24 * q ^ 24 * deriv f (q ^ 24) - f (q ^ 24))) *
        (2 * Real.pi * Complex.I)) (τ : ℂ) := by
  let q := Function.Periodic.qParam 1 (τ : ℂ)
  have hq0 : q ≠ 0 := Complex.exp_ne_zero _
  have hq : ‖q ^ 24‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _)
      (Function.Periodic.norm_qParam_lt_one one_pos τ.im_pos) (by norm_num)
  have h := ((hasDerivAt_qParam_one τ).inv hq0).mul
    ((differentiableAt_core_of_hasSum hc hq).hasDerivAt.comp (τ : ℂ)
      ((hasDerivAt_qParam_one τ).pow 24))
  have he : (scaledFourierFunction f ∘ ofComplex) =ᶠ[𝓝 (τ : ℂ)]
      (fun z : ℂ => (Function.Periodic.qParam 1 z)⁻¹ *
        f (Function.Periodic.qParam 1 z ^ 24)) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
    simp only [Function.comp_apply, scaledFourierFunction_apply, ofComplex_apply_of_im_pos hz]
  convert h.congr_of_eventuallyEq he using 1 <;> dsimp only [q]
  simp only [Pi.inv_apply, Function.comp_apply, Pi.pow_apply]
  field_simp [show Function.Periodic.qParam 1 (τ : ℂ) ≠ 0 from hq0]
  <;> ring

/-- Rescaling a convergent power series gives a holomorphic function. -/
theorem mdifferentiable_scaledFourierFunction {c : ℕ → ℂ} {f : ℂ → ℂ}
    (hc : ∀ q : ℂ, ‖q‖ < 1 → HasSum (fun n => c n * q ^ n) (f q)) :
    MDiff (scaledFourierFunction f) := by
  intro τ
  exact mdifferentiableAt_iff.mpr (hasDerivAt_scaledFourierFunction hc τ).differentiableAt

/-- The normalized derivative removes the analytic factor `2πi`. -/
theorem normalizedDeriv_scaledFourierFunction {c : ℕ → ℂ} {f : ℂ → ℂ}
    (hc : ∀ q : ℂ, ‖q‖ < 1 → HasSum (fun n => c n * q ^ n) (f q))
    (τ : UpperHalfPlane) :
    let q := Function.Periodic.qParam 1 τ
    Derivative.normalizedDerivOfComplex (scaledFourierFunction f) τ =
      q⁻¹ * (24 * q ^ 24 * deriv f (q ^ 24) - f (q ^ 24)) := by
  have hC : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  rw [Derivative.normalizedDerivOfComplex, (hasDerivAt_scaledFourierFunction hc τ).deriv]
  field_simp

/-- Differentiation multiplies the coefficient by its integral Fourier index. -/
theorem normalizedDeriv_scaledFourierFunction_hasSum {c : ℕ → ℂ} {f : ℂ → ℂ}
    (hc : ∀ q : ℂ, ‖q‖ < 1 → HasSum (fun n => c n * q ^ n) (f q))
    (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ => (24 * (n : ℂ) - 1) * c n *
      Function.Periodic.qParam 1 τ ^ (24 * (n : ℤ) - 1))
      (Derivative.normalizedDerivOfComplex (scaledFourierFunction f) τ) := by
  have hcore : ∀ q : ℂ, ‖q‖ < 1 →
      HasSum (fun n : ℕ => ((24 * (n : ℂ) - 1) * c n) * q ^ n)
        (24 * q * deriv f q - f q) := by
    intro q hq
    convert ((QSeries.hasSum_eulerDerivative_of_hasSum hc hq).mul_left 24).sub
      (hc q hq) using 1
    · funext n
      ring
    · ring
  simpa only [normalizedDeriv_scaledFourierFunction hc τ, scaledFourierFunction_apply] using
    scaledFourierFunction_hasSum (fun n => (24 * (n : ℂ) - 1) * c n)
      (fun q => 24 * q * deriv f q - f q) hcore τ

/-- The partition generating function is holomorphic on the upper half-plane. -/
theorem mdifferentiable_scaledPartitionFunction : MDiff scaledPartitionFunction := by
  rw [scaledPartitionFunction_eq]
  exact mdifferentiable_scaledFourierFunction
    (fun q hq => QSeries.hasSum_partitionCount_inverseEuler hq)

/-- The smallest-parts generating function is holomorphic on the upper half-plane. -/
theorem mdifferentiable_scaledSptFunction : MDiff scaledSptFunction := by
  rw [scaledSptFunction_eq]
  exact mdifferentiable_scaledFourierFunction (fun q hq => hasSum_sptAnalyticCore hq)

/-- The complete integral-index expansion of `ΘP`. -/
theorem normalizedDeriv_scaledPartitionFunction_hasSum (τ : UpperHalfPlane) :
    HasSum (fun r : ℤ => ((r * QSeries.partitionFourier r : ℚ) : ℂ) *
      Function.Periodic.qParam 1 τ ^ r)
      (Derivative.normalizedDerivOfComplex scaledPartitionFunction τ) := by
  apply hasSum_integral_of_twentyFour
  · intro r hr
    have hz : QSeries.partitionFourier r = 0 := by
      by_contra h
      obtain ⟨hlo, hmod⟩ := QSeries.partitionFourier_support r h
      apply hr
      exact ⟨((r + 1) / 24).toNat, by dsimp only; omega⟩
    simp [hz]
  · rw [scaledPartitionFunction_eq]
    convert normalizedDeriv_scaledFourierFunction_hasSum
      (fun q hq => QSeries.hasSum_partitionCount_inverseEuler hq) τ using 1
    funext n
    rw [QSeries.partitionFourier_at]
    push_cast
    rfl

/-- The holomorphic part of the completed weight `3/2` form, with the
normalization in [rolenManuscript, §2] and [ahlgrenBringmannLovejoy2011, §3]. -/
noncomputable def sptMockHolomorphicPart (τ : UpperHalfPlane) : ℂ :=
  scaledSptFunction τ + Derivative.normalizedDerivOfComplex scaledPartitionFunction τ / 12

theorem sptMockHolomorphicPart_apply (τ : UpperHalfPlane) :
    sptMockHolomorphicPart τ = scaledSptFunction τ +
      Derivative.normalizedDerivOfComplex scaledPartitionFunction τ / 12 := (rfl)

/-- The mock holomorphic part has the manuscript's exact rational Fourier row. -/
theorem sptMockHolomorphicPart_hasSum (τ : UpperHalfPlane) :
    HasSum (fun r : ℤ =>
      (((QSeries.sptFourier r : ℚ) + r * QSeries.partitionFourier r / 12 : ℚ) : ℂ) *
        Function.Periodic.qParam 1 τ ^ r) (sptMockHolomorphicPart τ) := by
  rw [sptMockHolomorphicPart_apply]
  convert (scaledSptFunction_hasSum τ).add
    ((normalizedDeriv_scaledPartitionFunction_hasSum τ).div_const 12) using 1
  ext r
  push_cast
  ring

/-- Holomorphy of the actual mock holomorphic part follows from ordinary
holomorphy of the partition and smallest-parts generating functions. -/
theorem mdifferentiable_sptMockHolomorphicPart : MDiff sptMockHolomorphicPart := by
  have he : sptMockHolomorphicPart = fun τ => scaledSptFunction τ +
      Derivative.normalizedDerivOfComplex scaledPartitionFunction τ * (12 : ℂ)⁻¹ := by
    funext τ
    rw [sptMockHolomorphicPart_apply, div_eq_mul_inv]
  rw [he]
  exact mdifferentiable_scaledSptFunction.add
    ((Derivative.normalizedDerivOfComplex_mdifferentiable
      mdifferentiable_scaledPartitionFunction).mul mdifferentiable_const)

/-- Actual twisted analytic constituents, constructed without supplying Fourier
expansions as hypotheses. Modular transformation and cusp laws remain separate. -/
noncomputable def sptTwistedAnalyticData (Q : ℕ) [Fact Q.Prime] : SptTwistedAnalyticData Q :=
  twistedAnalyticDataOfFourierExpansions Q scaledPartitionFunction sptMockHolomorphicPart
    mdifferentiable_scaledPartitionFunction scaledPartitionFunction_hasSum
    normalizedDeriv_scaledPartitionFunction_hasSum sptMockHolomorphicPart_hasSum

/-- The actual `twistedM` retains the finite-filter normalization. -/
theorem sptTwistedAnalyticData_twistedM_eq (Q : ℕ) [Fact Q.Prime] :
    (sptTwistedAnalyticData Q).twistedM =
      fourierFilter (negativeSquareResidueSelector Q) sptMockHolomorphicPart := by
  rw [sptTwistedAnalyticData, twistedAnalyticDataOfFourierExpansions_twistedM]

/-- The actual `twistedP` retains the finite-filter normalization. -/
theorem sptTwistedAnalyticData_twistedP_eq (Q : ℕ) [Fact Q.Prime] :
    (sptTwistedAnalyticData Q).twistedP =
      fourierFilter (negativeSquareResidueSelector Q) scaledPartitionFunction := by
  rw [sptTwistedAnalyticData, twistedAnalyticDataOfFourierExpansions_twistedP]

/-- The actual `serreDerivativeP` retains the finite-filter normalization. -/
theorem sptTwistedAnalyticData_serreDerivativeP_eq (Q : ℕ) [Fact Q.Prime] :
    (sptTwistedAnalyticData Q).serreDerivativeP =
      Derivative.serreDerivative (-(1 / 2 : ℂ))
      (fourierFilter (negativeSquareResidueSelector Q) scaledPartitionFunction) := by
  rw [sptTwistedAnalyticData, twistedAnalyticDataOfFourierExpansions_serreDerivativeP]

/-- The actual filtered mock part is holomorphic. This uses convergence of the
holomorphic part and finite translation, independently of modularity. -/
theorem sptTwistedAnalyticData_twistedM_holomorphic (Q : ℕ) [Fact Q.Prime] :
    MDiff (sptTwistedAnalyticData Q).twistedM := by
  rw [sptTwistedAnalyticData, twistedAnalyticDataOfFourierExpansions_twistedM]
  exact mdifferentiable_fourierFilter _ _ mdifferentiable_sptMockHolomorphicPart

/-- The actual filtered inverse eta function is holomorphic. -/
theorem sptTwistedAnalyticData_twistedP_holomorphic (Q : ℕ) [Fact Q.Prime] :
    MDiff (sptTwistedAnalyticData Q).twistedP := by
  rw [sptTwistedAnalyticData, twistedAnalyticDataOfFourierExpansions_twistedP]
  exact mdifferentiable_fourierFilter _ _ mdifferentiable_scaledPartitionFunction

/-- The actual Serre derivative is holomorphic, with the negative half-weight
normalization fixed by its definition. -/
theorem sptTwistedAnalyticData_serreDerivativeP_holomorphic (Q : ℕ) [Fact Q.Prime] :
    MDiff (sptTwistedAnalyticData Q).serreDerivativeP := by
  rw [sptTwistedAnalyticData, twistedAnalyticDataOfFourierExpansions_serreDerivativeP]
  exact Derivative.serreDerivative_mdifferentiable _
    (mdifferentiable_fourierFilter _ _ mdifferentiable_scaledPartitionFunction)

end SptClassification
