/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.WeightTwoConstantTermHeckeCusp

/-!
# Descent of a meromorphic cusp germ along a finer nome

A period-24 holomorphic function may initially be represented by a germ in
the finer period-`24n` nome. If that germ is meromorphic, clearing a pole
gives a bounded period-24 function at infinity. The usual cusp extension
then supplies a meromorphic germ in the original nome
[rolenManuscript, §3].
-/

public section

namespace SptClassification

open UpperHalfPlane Filter
open scoped Manifold

/-- Raising the finer period-`24n` nome to the `n`th power gives the
period-24 nome. -/
theorem qParam_twentyFour_mul_pow (n : ℕ) (hn : 0 < n) (z : ℂ) :
    Function.Periodic.qParam (24 * n) z ^ n =
      Function.Periodic.qParam 24 z := by
  unfold Function.Periodic.qParam
  rw [← Complex.exp_nat_mul]
  congr 1
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  norm_num
  field_simp

/-- The period-24 nome is unchanged by translation through 24. -/
private theorem qParam_twentyFour_add (z : ℂ) :
    Function.Periodic.qParam 24 (z + 24) = Function.Periodic.qParam 24 z := by
  unfold Function.Periodic.qParam
  have harg : 2 * Real.pi * Complex.I * (z + 24) / 24 =
      2 * Real.pi * Complex.I * z / 24 + 2 * Real.pi * Complex.I := by ring
  norm_num at harg ⊢
  rw [harg, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- Pole clearing in the period-24 nome preserves the actual period 24 on
the upper half-plane. -/
theorem poleClearing_twentyFour_periodic {f : ℂ → ℂ}
    (hT : ∀ z : ℂ, 0 < z.im → f (z + 24) = f z) (M : ℕ) :
    Function.Periodic
      ((fun τ : UpperHalfPlane => Function.Periodic.qParam 24 τ ^ M * f τ) ∘
        ofComplex) 24 := by
  intro z
  by_cases hz : 0 < z.im
  · have hz24 : 0 < (z + 24).im := by simpa using hz
    have hzc : ((ofComplex z : UpperHalfPlane) : ℂ) = z := by
      let τ : UpperHalfPlane := ⟨z, hz⟩
      change ((ofComplex (τ : ℂ) : UpperHalfPlane) : ℂ) = z
      rw [ofComplex_apply]
    have hz24c : ((ofComplex (z + 24) : UpperHalfPlane) : ℂ) = z + 24 := by
      let τ : UpperHalfPlane := ⟨z + 24, hz24⟩
      change ((ofComplex (τ : ℂ) : UpperHalfPlane) : ℂ) = z + 24
      rw [ofComplex_apply]
    simp only [Function.comp_apply, hzc, hz24c, qParam_twentyFour_add, hT z hz]
  · have hz24 : ¬ 0 < (z + 24).im := by simpa using hz
    simp only [Function.comp_apply]
    have hnot : ¬ ∃ a : UpperHalfPlane, a ∈ Set.univ ∧ (a : ℂ) = z := by
      rintro ⟨a, _, ha⟩
      apply hz
      rw [← ha]
      exact a.im_pos
    have hnot24 : ¬ ∃ a : UpperHalfPlane, a ∈ Set.univ ∧ (a : ℂ) = z + 24 := by
      rintro ⟨a, _, ha⟩
      apply hz24
      rw [← ha]
      exact a.im_pos
    have heq : (ofComplex (z + 24) : UpperHalfPlane) = ofComplex z := by
      simp [UpperHalfPlane.ofComplex,
        Topology.IsOpenEmbedding.toOpenPartialHomeomorph, Function.invFunOn]
      simp only [dif_neg hnot24, dif_neg hnot]
    rw [heq]

private theorem qParam_twentyFour_mdifferentiable :
    MDiff (fun τ : UpperHalfPlane => Function.Periodic.qParam 24 τ) := by
  intro τ
  apply mdifferentiableAt_iff.mpr
  have hd : DifferentiableAt ℂ (Function.Periodic.qParam 24) (τ : ℂ) := by
    unfold Function.Periodic.qParam
    fun_prop
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventuallyEq_coe_comp_ofComplex τ.im_pos] with z hz
  exact congrArg (Function.Periodic.qParam 24) hz

private theorem mdifferentiable_twentyFour_poleClearing {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet) (M : ℕ) :
    MDiff (fun τ : UpperHalfPlane => Function.Periodic.qParam 24 τ ^ M * f τ) := by
  have hf' : MDiff (fun τ : UpperHalfPlane => f τ) := by
    intro τ
    apply mdifferentiableAt_iff.mpr
    have hd : DifferentiableAt ℂ f (τ : ℂ) :=
      (hf τ τ.im_pos).differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)
    apply hd.congr_of_eventuallyEq
    filter_upwards [eventuallyEq_coe_comp_ofComplex τ.im_pos] with z hz
    exact congrArg f hz
  exact (qParam_twentyFour_mdifferentiable.pow M).mul hf'

private theorem isBoundedAtImInfty_of_analytic_qParam24n {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g 0) (n : ℕ) (hn : 0 < n) :
    IsBoundedAtImInfty (fun τ : UpperHalfPlane =>
      g (Function.Periodic.qParam (24 * n) τ)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hq : Tendsto (fun τ : UpperHalfPlane => Function.Periodic.qParam (24 * n) τ)
      atImInfty (nhds 0) := qParam_tendsto_atImInfty (by positivity)
  have hlim : Tendsto (fun τ : UpperHalfPlane =>
      g (Function.Periodic.qParam (24 * n) τ)) atImInfty (nhds (g 0)) :=
    hg.continuousAt.tendsto.comp hq
  obtain ⟨C, hC⟩ := hlim.norm.isBoundedUnder_le
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp hC
  exact isBoundedAtImInfty_iff.mpr ⟨C, A, hA⟩

/-- A holomorphic period-24 function represented by a meromorphic germ in
the finer period-`24n` nome has a meromorphic germ in the original period-24
nome. The arbitrary value of the finer germ at zero is never used to infer
continuity there [rolenManuscript, §3]. -/
theorem meromorphicCusp_twentyFour_mul_descends {f G : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet)
    (hT : ∀ z : ℂ, 0 < z.im → f (z + 24) = f z)
    (hG : MeromorphicAt G 0)
    (n : ℕ) (hn : 0 < n)
    (hEq : ∀ τ : UpperHalfPlane,
      G (Function.Periodic.qParam (24 * n) τ) = f τ) :
    ∃ J : ℂ → ℂ, MeromorphicAt J 0 ∧
      ∀ τ : UpperHalfPlane, J (Function.Periodic.qParam 24 τ) = f τ := by
  obtain ⟨N, hN⟩ := MeromorphicAt.exists_analytic_poleClearing hG
  let F : UpperHalfPlane → ℂ := fun τ => Function.Periodic.qParam 24 τ ^ N * f τ
  have hidx : n * N = (n - 1) * N + N := by
    calc
      n * N = ((n - 1) + 1) * N := by rw [Nat.sub_add_cancel hn]
      _ = (n - 1) * N + N := by ring
  have hA : AnalyticAt ℂ (fun t : ℂ => t ^ (n * N) * G t) 0 := by
    have hpow : AnalyticAt ℂ (fun t : ℂ => t ^ ((n - 1) * N)) 0 :=
      analyticAt_id.pow _
    have he : (fun t : ℂ => t ^ (n * N) * G t) =
        (fun t : ℂ => t ^ ((n - 1) * N) * (t ^ N * G t)) := by
      funext t
      rw [hidx, pow_add, mul_assoc]
    rw [he]
    exact hpow.mul hN
  have hBound : IsBoundedAtImInfty F := by
    have hB := isBoundedAtImInfty_of_analytic_qParam24n hA n hn
    have he (τ : UpperHalfPlane) :
        Function.Periodic.qParam (24 * n) τ ^ (n * N) *
          G (Function.Periodic.qParam (24 * n) τ) = F τ := by
      rw [hEq τ, pow_mul, qParam_twentyFour_mul_pow n hn]
    simpa only [he] using hB
  have hper : Function.Periodic (F ∘ ofComplex) ((24 : ℝ) : ℂ) := by
    simpa using poleClearing_twentyFour_periodic hT N
  have han : AnalyticAt ℂ (cuspFunction 24 F) 0 :=
    analyticAt_cuspFunction_zero (by norm_num) hper
      (mdifferentiable_twentyFour_poleClearing hf N) hBound
  let J : ℂ → ℂ := fun q => cuspFunction 24 F q / q ^ N
  have hJ : MeromorphicAt J 0 := by
    exact han.meromorphicAt.div (analyticAt_id.pow N).meromorphicAt
  refine ⟨J, hJ, ?_⟩
  intro τ
  have hc : cuspFunction 24 F (Function.Periodic.qParam 24 τ) = F τ := by
    change Function.Periodic.cuspFunction 24 (F ∘ ofComplex)
      (Function.Periodic.qParam 24 (τ : ℂ)) = F τ
    rw [Function.Periodic.eq_cuspFunction (by norm_num) hper]
    simp only [Function.comp_apply, ofComplex_apply]
  simp only [J, hc, F]
  exact mul_div_cancel_left₀ (f τ) (pow_ne_zero N (Complex.exp_ne_zero _))

/-- The finite translated average of a holomorphic upper-half-plane function
is holomorphic. Its defining complex function agrees with the actual affine
upper-half-plane sum throughout the upper half-plane. -/
private theorem differentiableOn_cuspAffineAverage {f : UpperHalfPlane → ℂ}
    (hf : MDiff f) (n : ℕ) (hn : 0 < n) :
    DifferentiableOn ℂ
      (fun z : ℂ => ∑ j ∈ Finset.range n,
        f (ofComplex ((z + 24 * j) / n))) upperHalfPlaneSet := by
  classical
  have hf' : DifferentiableOn ℂ (f ∘ ofComplex) upperHalfPlaneSet :=
    UpperHalfPlane.mdifferentiable_iff.mp hf
  intro z hz
  have hterm (j : ℕ) : DifferentiableAt ℂ
      (fun w : ℂ => f (ofComplex ((w + 24 * j) / n))) z := by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hzj : 0 < ((z + 24 * j) / n).im := by
      simpa using div_pos hz hn'
    have hfj : DifferentiableAt ℂ (f ∘ ofComplex) ((z + 24 * j) / n) :=
      (hf' _ hzj).differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds hzj)
    have ha : DifferentiableAt ℂ (fun w : ℂ => (w + 24 * j) / n) z := by
      fun_prop
    change DifferentiableAt ℂ
      ((f ∘ ofComplex) ∘ (fun w : ℂ => (w + 24 * j) / n)) z
    exact hfj.comp z ha
  have hsum (s : Finset ℕ) : DifferentiableAt ℂ
      (fun w : ℂ => ∑ j ∈ s, f (ofComplex ((w + 24 * j) / n))) z := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hjs ih =>
        have hsum_eq :
            (fun w : ℂ => ∑ i ∈ insert j s,
              f (ofComplex ((w + 24 * i) / n))) =
              (fun w : ℂ => f (ofComplex ((w + 24 * j) / n)) +
                ∑ i ∈ s, f (ofComplex ((w + 24 * i) / n))) := by
          funext w
          rw [Finset.sum_insert hjs]
        rw [hsum_eq]
        exact (hterm j).add ih
  exact (hsum (Finset.range n)).differentiableWithinAt

private theorem cuspAffineAverage_eq {f : UpperHalfPlane → ℂ}
    (n : ℕ) (hn : 0 < n) (τ : UpperHalfPlane) :
    (∑ j ∈ Finset.range n,
      f (ofComplex (((τ : ℂ) + 24 * j) / n))) =
      ∑ j ∈ Finset.range n, f (cuspAffinePoint n j hn τ) := by
  apply Finset.sum_congr rfl
  intro j _
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hz : 0 < (((τ : ℂ) + 24 * j) / n).im := by
    simpa using div_pos τ.im_pos hn'
  congr 1
  apply UpperHalfPlane.ext
  rw [cuspAffinePoint_coe, ofComplex_apply_of_im_pos hz]

/-- The translated finite cusp sum has a meromorphic representative in the
original period-24 nome. The finer germ alone is insufficient: holomorphy of
the actual sum and cyclic period-24 symmetry give the descent. -/
theorem meromorphicCuspRootAverage_descends {f : UpperHalfPlane → ℂ} {G : ℂ → ℂ}
    (hf : MDiff f)
    (hG : MeromorphicAt G 0)
    (hEq : ∀ τ : UpperHalfPlane, G (Function.Periodic.qParam 24 τ) = f τ)
    (n : ℕ) (hn : 0 < n) :
    ∃ J : ℂ → ℂ, MeromorphicAt J 0 ∧
      ∀ τ : UpperHalfPlane,
        J (Function.Periodic.qParam 24 τ) =
          ∑ j ∈ Finset.range n, f (cuspAffinePoint n j hn τ) := by
  let v : ℂ → ℂ := fun z => ∑ j ∈ Finset.range n,
    f (ofComplex ((z + 24 * j) / n))
  have hv : DifferentiableOn ℂ v upperHalfPlaneSet :=
    differentiableOn_cuspAffineAverage hf n hn
  have heval (τ : UpperHalfPlane) :
      v τ = ∑ j ∈ Finset.range n, f (cuspAffinePoint n j hn τ) :=
    cuspAffineAverage_eq n hn τ
  have hT : ∀ z : ℂ, 0 < z.im → v (z + 24) = v z := by
    intro z hz
    let τ : UpperHalfPlane := ⟨z, hz⟩
    calc
      v (z + 24) =
          ∑ j ∈ Finset.range n,
            f (cuspAffinePoint n j hn (cuspTranslateTwentyFour τ)) := by
              rw [← cuspTranslateTwentyFour_coe τ]
              exact heval (cuspTranslateTwentyFour τ)
      _ = ∑ j ∈ Finset.range n, f (cuspAffinePoint n j hn τ) :=
        cuspAffineAverage_periodic hEq n hn τ
      _ = v z := by
        change (∑ j ∈ Finset.range n, f (cuspAffinePoint n j hn τ)) = v (τ : ℂ)
        exact (heval τ).symm
  have hFine (τ : UpperHalfPlane) :
      cuspRootAverage G n (Function.Periodic.qParam (24 * n) τ) = v τ := by
    rw [cuspRootAverage_qParam hEq n hn τ, heval]
  obtain ⟨J, hJ, hJeq⟩ :=
    meromorphicCusp_twentyFour_mul_descends hv hT
      (meromorphicAt_cuspRootAverage hG n) n hn hFine
  exact ⟨J, hJ, fun τ => by rw [hJeq τ, heval τ]⟩

/-- The translated average of an actual inverse-eta weak form has a
meromorphic period-24 cusp representative. -/
theorem EtaInverseWeaklyHolomorphicForm.has_meromorphic_cuspAffineAverage
    {k : ℕ} (f : EtaInverseWeaklyHolomorphicForm k)
    (n : ℕ) (hn : 0 < n) :
    ∃ J : ℂ → ℂ, MeromorphicAt J 0 ∧
      ∀ τ : UpperHalfPlane,
        J (Function.Periodic.qParam 24 τ) =
          ∑ j ∈ Finset.range n, f (cuspAffinePoint n j hn τ) := by
  obtain ⟨G, hG, hEq⟩ := f.has_meromorphic_cusp
  exact meromorphicCuspRootAverage_descends f.holomorphic hG hEq n hn

end SptClassification
