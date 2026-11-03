/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.FourierRowUniqueness
public import SptClassification.ModularForms.PrincipalForms
public import SptClassification.QSeries.ConvergentProducts

/-!
# Products of complementary eta weak forms

An eta weak form of weight `k + 1/2` can be paired with a weak form carrying
the inverse eta factor and weight `l - 1/2`. When `k + l = 2`, their analytic
product has the level-one weight-two transformation law. Both cusp conditions
are expressed in the period-24 coordinate, where each factor has a meromorphic
germ [rolenManuscript, §3].
-/

public section

namespace SptClassification

open UpperHalfPlane
open Filter
open scoped MatrixGroups Manifold

private theorem isBoundedAtImInfty_of_analytic_qParam24 {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g 0) :
    IsBoundedAtImInfty (fun τ : UpperHalfPlane =>
      g (Function.Periodic.qParam 24 τ)) := by
  have hq : Tendsto (fun τ : UpperHalfPlane => Function.Periodic.qParam 24 τ)
      atImInfty (nhds 0) := qParam_tendsto_atImInfty (by norm_num)
  have hlim : Tendsto (fun τ : UpperHalfPlane =>
      g (Function.Periodic.qParam 24 τ)) atImInfty (nhds (g 0)) :=
    hg.continuousAt.tendsto.comp hq
  obtain ⟨C, hC⟩ := hlim.norm.isBoundedUnder_le
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp hC
  exact isBoundedAtImInfty_iff.mpr ⟨C, A, hA⟩

/-- A holomorphic period-one function with a period-24 meromorphic cusp germ
has a genuine meromorphic cusp germ in the level-one nome. The two germs may
take arbitrary values at zero; only their evaluations on the punctured cusp
are compared [rolenManuscript, §3]. -/
theorem meromorphicCusp24_descends_to_one {f G : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet)
    (hT : ∀ z : ℂ, 0 < z.im → f (z + 1) = f z)
    (hG : MeromorphicAt G 0)
    (hEq : ∀ τ : UpperHalfPlane, G (Function.Periodic.qParam 24 τ) = f τ) :
    ∃ J : ℂ → ℂ, MeromorphicAt J 0 ∧
      ∀ τ : UpperHalfPlane, J (Function.Periodic.qParam 1 τ) = f τ := by
  obtain ⟨N, hN⟩ := MeromorphicAt.exists_analytic_poleClearing hG
  let F : UpperHalfPlane → ℂ := fun τ => Function.Periodic.qParam 1 τ ^ N * f τ
  have hA : AnalyticAt ℂ (fun t : ℂ => t ^ (24 * N) * G t) 0 := by
    have hpow : AnalyticAt ℂ (fun t : ℂ => t ^ (23 * N)) 0 := analyticAt_id.pow _
    have h := hpow.mul hN
    have he : (fun t : ℂ => t ^ (24 * N) * G t) =
        (fun t : ℂ => t ^ (23 * N) * (t ^ N * G t)) := by
      funext t
      have hidx : 24 * N = 23 * N + N := by omega
      simp only [hidx, pow_add, mul_assoc]
    rw [he]
    exact h
  have hBound : IsBoundedAtImInfty F := by
    have hB := isBoundedAtImInfty_of_analytic_qParam24 hA
    have he (τ : UpperHalfPlane) :
        Function.Periodic.qParam 24 τ ^ (24 * N) *
          G (Function.Periodic.qParam 24 τ) = F τ := by
      rw [hEq τ, pow_mul, qParam_twentyFour_pow]
    simpa only [he] using hB
  have hper : Function.Periodic (F ∘ ofComplex) 1 := by
    exact poleClearing_periodic hT N
  have han : AnalyticAt ℂ (cuspFunction 1 F) 0 :=
    analyticAt_cuspFunction_zero (by norm_num) hper
      (mdifferentiable_poleClearing hf N) hBound
  let J : ℂ → ℂ := fun q => cuspFunction 1 F q / q ^ N
  have hJ : MeromorphicAt J 0 := by
    exact han.meromorphicAt.div (analyticAt_id.pow N).meromorphicAt
  refine ⟨J, hJ, ?_⟩
  intro τ
  have hc : cuspFunction 1 F (Function.Periodic.qParam 1 τ) = F τ := by
    change Function.Periodic.cuspFunction 1 (F ∘ ofComplex)
      (Function.Periodic.qParam 1 (τ : ℂ)) = F τ
    rw [Function.Periodic.eq_cuspFunction one_ne_zero hper]
    simp only [Function.comp_apply, ofComplex_apply]
  simp only [J, hc, F]
  exact mul_div_cancel_left₀ (f τ) (pow_ne_zero N (Complex.exp_ne_zero _))

/-- A weakly holomorphic form of weight `k - 1/2` with inverse eta factor.
The cases `k = 0` and `k = 2` are the partners of the manuscript's `K` and
`H` forms, respectively. -/
structure EtaInverseWeaklyHolomorphicForm (k : ℕ) where
  toFun : UpperHalfPlane → ℂ
  holomorphic' : MDiff toFun
  map_action' : ∀ (γ : GL (Fin 2) ℝ), γ ∈ 𝒮ℒ → ∀ τ : UpperHalfPlane,
    toFun (γ • τ) = (etaAutomorphyFactor γ τ)⁻¹ * denom γ τ ^ k * toFun τ
  meromorphic_cusp' : ∃ G : ℂ → ℂ, MeromorphicAt G 0 ∧
    ∀ τ : UpperHalfPlane, G (Function.Periodic.qParam 24 τ) = toFun τ

namespace EtaInverseWeaklyHolomorphicForm

/-- The zero inverse eta weak form, available in every integral weight shift. -/
def zero (k : ℕ) : EtaInverseWeaklyHolomorphicForm k where
  toFun := fun _ => 0
  holomorphic' := by
    simpa using (mdifferentiable_const : MDiff (fun _ : UpperHalfPlane => (0 : ℂ)))
  map_action' := by
    intro γ hγ τ
    simp
  meromorphic_cusp' := by
    refine ⟨fun _ => 0, analyticAt_const.meromorphicAt, ?_⟩
    intro τ
    rfl

instance instFunLike (k : ℕ) :
    FunLike (EtaInverseWeaklyHolomorphicForm k) UpperHalfPlane ℂ where
  coe := toFun
  coe_injective := by
    intro f g h
    cases f
    cases g
    cases h
    rfl

@[simp] theorem zero_apply (k : ℕ) (τ : UpperHalfPlane) :
    (zero k) τ = 0 := (rfl)

theorem holomorphic {k : ℕ} (g : EtaInverseWeaklyHolomorphicForm k) : MDiff g :=
  g.holomorphic'

theorem map_action {k : ℕ} (g : EtaInverseWeaklyHolomorphicForm k)
    (γ : GL (Fin 2) ℝ) (hγ : γ ∈ 𝒮ℒ) (τ : UpperHalfPlane) :
    g (γ • τ) = (etaAutomorphyFactor γ τ)⁻¹ * denom γ τ ^ k * g τ :=
  g.map_action' γ hγ τ

theorem has_meromorphic_cusp {k : ℕ} (g : EtaInverseWeaklyHolomorphicForm k) :
    ∃ G : ℂ → ℂ, MeromorphicAt G 0 ∧
      ∀ τ : UpperHalfPlane, G (Function.Periodic.qParam 24 τ) = g τ :=
  g.meromorphic_cusp'

/-- The sum of two inverse eta weak forms has the same weight and multiplier. -/
def add {k : ℕ} (f g : EtaInverseWeaklyHolomorphicForm k) :
    EtaInverseWeaklyHolomorphicForm k where
  toFun := fun τ => f τ + g τ
  holomorphic' := f.holomorphic'.add g.holomorphic'
  map_action' := by
    intro γ hγ τ
    change f.toFun (γ • τ) + g.toFun (γ • τ) =
      (etaAutomorphyFactor γ τ)⁻¹ * denom γ τ ^ k *
        (f.toFun τ + g.toFun τ)
    rw [f.map_action' γ hγ τ, g.map_action' γ hγ τ]
    ring
  meromorphic_cusp' := by
    obtain ⟨F, hF, hFeq⟩ := f.meromorphic_cusp'
    obtain ⟨G, hG, hGeq⟩ := g.meromorphic_cusp'
    refine ⟨fun t => F t + G t, hF.add hG, ?_⟩
    intro τ
    change F (Function.Periodic.qParam 24 τ) +
      G (Function.Periodic.qParam 24 τ) = f.toFun τ + g.toFun τ
    rw [hFeq τ, hGeq τ]

@[simp] theorem add_apply {k : ℕ} (f g : EtaInverseWeaklyHolomorphicForm k)
    (τ : UpperHalfPlane) : add f g τ = f τ + g τ := (rfl)

/-- Rational scaling of an inverse eta weak form preserves its analytic type. -/
def smulRat {k : ℕ} (c : ℚ) (f : EtaInverseWeaklyHolomorphicForm k) :
    EtaInverseWeaklyHolomorphicForm k where
  toFun := fun τ => (c : ℂ) * f τ
  holomorphic' := (mdifferentiable_const : MDiff (fun _ : UpperHalfPlane => (c : ℂ))).mul
    f.holomorphic'
  map_action' := by
    intro γ hγ τ
    change (c : ℂ) * f.toFun (γ • τ) =
      (etaAutomorphyFactor γ τ)⁻¹ * denom γ τ ^ k *
        ((c : ℂ) * f.toFun τ)
    rw [f.map_action' γ hγ τ]
    ring
  meromorphic_cusp' := by
    obtain ⟨F, hF, hFeq⟩ := f.meromorphic_cusp'
    refine ⟨fun t => (c : ℂ) * F t,
      (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (c : ℂ)) 0).meromorphicAt.mul hF,
      ?_⟩
    intro τ
    change (c : ℂ) * F (Function.Periodic.qParam 24 τ) =
      (c : ℂ) * f.toFun τ
    rw [hFeq τ]

@[simp] theorem smulRat_apply {k : ℕ} (c : ℚ)
    (f : EtaInverseWeaklyHolomorphicForm k) (τ : UpperHalfPlane) :
    smulRat c f τ = (c : ℂ) * f τ := (rfl)

end EtaInverseWeaklyHolomorphicForm

/-- The manuscript's actual inverse eta function `P = η⁻¹`, with its full
inverse eta automorphy law and a meromorphic period-24 cusp representative
[rolenManuscript, §3]. -/
noncomputable def inverseEtaWeakForm : EtaInverseWeaklyHolomorphicForm 0 where
  toFun := fun τ => (ModularForm.eta τ)⁻¹
  holomorphic' := by
    have hη : MDiff (fun τ : UpperHalfPlane => ModularForm.eta τ) := by
      intro τ
      apply mdifferentiableAt_iff.mpr
      apply (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet τ.im_pos).congr_of_eventuallyEq
      filter_upwards [eventuallyEq_coe_comp_ofComplex τ.im_pos] with z hz
      exact congrArg ModularForm.eta hz
    exact hη.inv (fun τ => ModularForm.eta_ne_zero τ.im_pos)
  map_action' := by
    intro γ hγ τ
    simp only [pow_zero, mul_one]
    rw [← etaAutomorphyFactor_mul_eta γ τ]
    simp only [mul_inv_rev]
    rw [mul_comm]
  meromorphic_cusp' := by
    let G : ℂ → ℂ := fun t => (t * etaEulerProduct (t ^ 24))⁻¹
    have hE : AnalyticAt ℂ (fun t : ℂ => etaEulerProduct (t ^ 24)) 0 :=
      analyticAt_etaEulerProduct_zero.fun_comp_of_eq (analyticAt_id.pow 24) (by simp)
    have hG : MeromorphicAt G 0 :=
      (analyticAt_id.mul hE).meromorphicAt.inv
    refine ⟨G, hG, ?_⟩
    intro τ
    have hη : ModularForm.eta τ = Function.Periodic.qParam 24 τ *
        etaEulerProduct (Function.Periodic.qParam 1 τ) := by
      simpa using eta_nat_mul_eq_euler 1 (τ : ℂ)
    simpa only [G, qParam_twentyFour_pow] using congrArg Inv.inv hη.symm

/-- The actual inverse eta, after removing its `q^(-1/24)` factor, has the
ordinary partition coefficients at every upper-half-plane nome
[rolenManuscript, §3]. -/
theorem inverseEtaWeakForm_hasSum (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ => (QSeries.partitionSeries.coeff n : ℂ) *
      Function.Periodic.qParam 1 τ ^ n)
      (Function.Periodic.qParam 24 τ * inverseEtaWeakForm τ) := by
  let q := Function.Periodic.qParam 1 τ
  let t := Function.Periodic.qParam 24 τ
  have hq : ‖q‖ < 1 := Function.Periodic.norm_qParam_lt_one (by norm_num) τ.im_pos
  have ht : t ≠ 0 := Complex.exp_ne_zero _
  have he : ModularForm.eta τ = t * etaEulerProduct q := by
    simpa [q, t] using eta_nat_mul_eq_euler 1 (τ : ℂ)
  have heul : etaEulerProduct q ≠ 0 := etaEulerProduct_ne_zero hq
  have hv : (etaEulerProduct q)⁻¹ = t * inverseEtaWeakForm τ := by
    change (etaEulerProduct q)⁻¹ = t * (ModularForm.eta τ)⁻¹
    rw [he]
    field_simp [ht, heul]
  rw [← hv]
  simpa [q] using QSeries.hasSum_partitionCount_inverseEuler hq

/-- The actual product of complementary eta weak forms. -/
noncomputable def etaWeightTwoProduct {k l : ℕ}
    (f : EtaWeaklyHolomorphicForm k) (g : EtaInverseWeaklyHolomorphicForm l) :
    UpperHalfPlane → ℂ := fun τ => f τ * g τ

/-- Evaluation of the complementary eta product. -/
theorem etaWeightTwoProduct_eq {k l : ℕ}
    (f : EtaWeaklyHolomorphicForm k) (g : EtaInverseWeaklyHolomorphicForm l)
    (τ : UpperHalfPlane) : etaWeightTwoProduct f g τ = f τ * g τ := (rfl)

theorem etaWeightTwoProduct_holomorphic {k l : ℕ}
    (f : EtaWeaklyHolomorphicForm k) (g : EtaInverseWeaklyHolomorphicForm l) :
    MDiff (etaWeightTwoProduct f g) :=
  (f.holomorphic).mul g.holomorphic

/-- The two canonical eta factors cancel, leaving weight two. -/
theorem etaWeightTwoProduct_map_action {k l : ℕ}
    (f : EtaWeaklyHolomorphicForm k) (g : EtaInverseWeaklyHolomorphicForm l)
    (hkl : k + l = 2) (γ : GL (Fin 2) ℝ) (hγ : γ ∈ 𝒮ℒ)
    (τ : UpperHalfPlane) :
    etaWeightTwoProduct f g (γ • τ) =
      denom γ τ ^ 2 * etaWeightTwoProduct f g τ := by
  simp only [etaWeightTwoProduct, f.map_action γ hγ τ, g.map_action γ hγ τ]
  calc
    etaAutomorphyFactor γ τ * denom γ τ ^ k * f τ *
        ((etaAutomorphyFactor γ τ)⁻¹ * denom γ τ ^ l * g τ) =
      (etaAutomorphyFactor γ τ * (etaAutomorphyFactor γ τ)⁻¹) *
        (denom γ τ ^ k * denom γ τ ^ l) * (f τ * g τ) := by ring
    _ = denom γ τ ^ 2 * (f τ * g τ) := by
      rw [mul_inv_cancel₀ (etaAutomorphyFactor_ne_zero γ τ)]
      simp only [one_mul, ← pow_add, hkl]

/-- Translation by one fixes the product of complementary eta weak forms. -/
theorem etaWeightTwoProduct_translation {k l : ℕ}
    (f : EtaWeaklyHolomorphicForm k) (g : EtaInverseWeaklyHolomorphicForm l)
    (hkl : k + l = 2) (τ : UpperHalfPlane) :
    etaWeightTwoProduct f g (upperUnipotent 1 • τ) =
      etaWeightTwoProduct f g τ := by
  have hγ : Matrix.SpecialLinearGroup.mapGL ℝ (upperUnipotent 1) ∈ 𝒮ℒ :=
    ⟨upperUnipotent 1, rfl⟩
  have h := etaWeightTwoProduct_map_action f g hkl _ hγ τ
  have hd : denom (Matrix.SpecialLinearGroup.mapGL ℝ (upperUnipotent 1)) τ = 1 := by
    have hm : ((Matrix.SpecialLinearGroup.mapGL ℝ (upperUnipotent 1) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) = !![1, 1; 0, 1] := by
      simp only [Matrix.SpecialLinearGroup.mapGL_coe_matrix,
        Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
        upperUnipotent_matrix]
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [Matrix.map_apply]
    simp [UpperHalfPlane.denom, hm]
  change etaWeightTwoProduct f g (upperUnipotent 1 • τ) =
    denom (Matrix.SpecialLinearGroup.mapGL ℝ (upperUnipotent 1)) τ ^ 2 *
      etaWeightTwoProduct f g τ at h
  simpa only [hd, one_pow, one_mul] using h

/-- The weight-two eta product is periodic in the complex upper half-plane. -/
theorem etaWeightTwoProduct_periodic {k l : ℕ}
    (f : EtaWeaklyHolomorphicForm k) (g : EtaInverseWeaklyHolomorphicForm l)
    (hkl : k + l = 2) :
    ∀ z : ℂ, 0 < z.im →
      (etaWeightTwoProduct f g ∘ ofComplex) (z + 1) =
        (etaWeightTwoProduct f g ∘ ofComplex) z := by
  intro z hz
  let τ : UpperHalfPlane := ⟨z, hz⟩
  have hz1 : 0 < (z + 1).im := by simpa using hz
  have h0 : ofComplex z = τ := ofComplex_apply_of_im_pos hz
  have h1 : ofComplex (z + 1) = upperUnipotent 1 • τ := by
    rw [ofComplex_apply_of_im_pos hz1]
    apply UpperHalfPlane.ext
    simpa [τ] using (upperUnipotent_apply 1 τ).symm
  simp only [Function.comp_apply, h1, h0]
  exact etaWeightTwoProduct_translation f g hkl τ

/-- Inversion acts on the product with the integral weight-two factor. -/
theorem etaWeightTwoProduct_inversion {k l : ℕ}
    (f : EtaWeaklyHolomorphicForm k) (g : EtaInverseWeaklyHolomorphicForm l)
    (hkl : k + l = 2) (τ : UpperHalfPlane) :
    etaWeightTwoProduct f g (ModularGroup.S • τ) =
      (τ : ℂ) ^ 2 * etaWeightTwoProduct f g τ := by
  have hγ : Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S ∈ 𝒮ℒ :=
    ⟨ModularGroup.S, rfl⟩
  have h := etaWeightTwoProduct_map_action f g hkl _ hγ τ
  have hd : denom (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S) τ = (τ : ℂ) :=
    ModularGroup.denom_S τ
  change etaWeightTwoProduct f g (ModularGroup.S • τ) =
    denom (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S) τ ^ 2 *
      etaWeightTwoProduct f g τ at h
  simpa only [hd] using h

/-- The product retains a genuine meromorphic cusp germ in the period-24
coordinate. The value of either germ at zero is unrestricted. -/
theorem etaWeightTwoProduct_has_meromorphic_cusp24 {k l : ℕ}
    (f : EtaWeaklyHolomorphicForm k) (g : EtaInverseWeaklyHolomorphicForm l) :
    ∃ G : ℂ → ℂ, MeromorphicAt G 0 ∧
      ∀ τ : UpperHalfPlane,
        G (Function.Periodic.qParam 24 τ) = etaWeightTwoProduct f g τ := by
  obtain ⟨F, hF, hFeq⟩ := f.has_meromorphic_cusp
  obtain ⟨G, hG, hGeq⟩ := g.has_meromorphic_cusp
  exact ⟨fun t => F t * G t, hF.mul hG, fun τ => by
    simp only [etaWeightTwoProduct, hFeq, hGeq]⟩

/-- The actual analytic product is a level-one meromorphic weight-two form,
so its intrinsic constant Laurent coefficient vanishes. This is the analytic
constant-term principle used for the manuscript's `H` and `K` pairings
[rolenManuscript, §3]. -/
theorem etaWeightTwoProduct_constantTerm_eq_zero {k l : ℕ}
    (f : EtaWeaklyHolomorphicForm k) (g : EtaInverseWeaklyHolomorphicForm l)
    (hkl : k + l = 2) :
    meromorphicCuspConstantTerm
      ((etaWeightTwoProduct f g) ∘ ofComplex) = 0 := by
  let u := etaWeightTwoProduct f g
  let v : ℂ → ℂ := u ∘ ofComplex
  have hv : DifferentiableOn ℂ v upperHalfPlaneSet :=
    UpperHalfPlane.mdifferentiable_iff.mp (etaWeightTwoProduct_holomorphic f g)
  have hT : ∀ z : ℂ, 0 < z.im → v (z + 1) = v z :=
    etaWeightTwoProduct_periodic f g hkl
  have hS : ∀ z : ℂ, 0 < z.im → v (-1 / z) = z ^ 2 * v z := by
    intro z hz
    let τ : UpperHalfPlane := ⟨z, hz⟩
    have h0 : ofComplex z = τ := ofComplex_apply_of_im_pos hz
    have h1 : ofComplex (-1 / z) = ModularGroup.S • τ := by
      have hsco : ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) = -1 / z := by
        rw [UpperHalfPlane.modular_S_smul]
        simp [τ, one_div, neg_div]
      rw [← hsco]
      exact ofComplex_apply _
    change u (ofComplex (-1 / z)) = z ^ 2 * u (ofComplex z)
    rw [h1, h0]
    exact etaWeightTwoProduct_inversion f g hkl τ
  obtain ⟨G, hG, hGeq⟩ := etaWeightTwoProduct_has_meromorphic_cusp24 f g
  obtain ⟨J, hJ, hJeq⟩ := meromorphicCusp24_descends_to_one hv hT hG
    (by
      intro τ
      simpa only [v, u, Function.comp_apply, ofComplex_apply] using hGeq τ)
  exact weightTwo_meromorphic_constantTerm_eq_zero hv hT hS hJ
    (by
      intro τ
      simpa only [v, u, Function.comp_apply, ofComplex_apply] using hJeq τ)

/-- The manuscript's actual `K_d P` product has vanishing constant term.
Here `P = η⁻¹`; the form `K_d` is the prescribed analytic eta polynomial
[rolenManuscript, §3, equation (K)]. -/
theorem principalKForm_inverseEta_constantTerm_eq_zero (d : ℕ) :
    meromorphicCuspConstantTerm
      ((fun τ : UpperHalfPlane => principalKForm d τ * (ModularForm.eta τ)⁻¹) ∘
        ofComplex) = 0 := by
  have h := etaWeightTwoProduct_constantTerm_eq_zero
    (principalKForm d) inverseEtaWeakForm (by decide : 2 + 0 = 2)
  change meromorphicCuspConstantTerm
    ((fun τ : UpperHalfPlane => principalKForm d τ * (ModularForm.eta τ)⁻¹) ∘
      ofComplex) = 0 at h
  exact h

/-- The ordinary integral coefficient series obtained by clearing the pole of
the actual analytic product `K_d η⁻¹`. Its coefficients are the formal Cauchy
product of the prescribed K row and the partition series. -/
noncomputable def principalKInverseEtaSeries (d : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk (fun n : ℕ =>
    QSeries.principalKFourier d (24 * (n : ℤ) - d)) * QSeries.partitionSeries

/-- The integral Cauchy coefficients of the pole-cleared `K_d η⁻¹` product. -/
theorem principalKInverseEtaSeries_coeff (d j : ℕ) :
    (principalKInverseEtaSeries d).coeff j =
      ∑ x ∈ Finset.antidiagonal j,
        QSeries.principalKFourier d (24 * (x.1 : ℤ) - d) *
          SptClassification.partitionCount x.2 := by
  simp only [principalKInverseEtaSeries, PowerSeries.coeff_mul,
    PowerSeries.coeff_mk, QSeries.partitionSeries_coeff]

/-- The complete coefficient series of `K_d η⁻¹` converges to the actual
analytic product after clearing its pole. This is the analytic side of the
manuscript's second constant-term pairing [rolenManuscript, §3, eq. (ct2)]. -/
theorem principalKInverseEtaSeries_hasSum (d : ℕ) (hd : d % 24 = 23)
    (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ => ((principalKInverseEtaSeries d).coeff n : ℂ) *
      Function.Periodic.qParam 1 τ ^ n)
      (Function.Periodic.qParam 1 τ ^ QSeries.principalIndex d *
        (principalKForm d τ * inverseEtaWeakForm τ)) := by
  let q := Function.Periodic.qParam 1 τ
  let t := Function.Periodic.qParam 24 τ
  let K : PowerSeries ℤ := PowerSeries.mk (fun n : ℕ =>
    QSeries.principalKFourier d (24 * (n : ℤ) - d))
  have hK : HasSum (fun n : ℕ => (K.coeff n : ℂ) * q ^ n)
      (q ^ QSeries.principalIndex d * t⁻¹ * principalKForm d τ) := by
    simpa only [K, PowerSeries.coeff_mk] using principalKForm_hasSum d hd τ
  have hP : HasSum (fun n : ℕ => (QSeries.partitionSeries.coeff n : ℂ) * q ^ n)
      (t * inverseEtaWeakForm τ) := by
    simpa only [q, t] using inverseEtaWeakForm_hasSum τ
  have hp := QSeries.hasSum_coefficientTerm_mul K QSeries.partitionSeries q
    (q ^ QSeries.principalIndex d * t⁻¹ * principalKForm d τ)
    (t * inverseEtaWeakForm τ) hK.summable.norm hP.summable.norm hK hP
  have ht : t ≠ 0 := Complex.exp_ne_zero _
  have he : (q ^ QSeries.principalIndex d * t⁻¹ * principalKForm d τ) *
      (t * inverseEtaWeakForm τ) =
      q ^ QSeries.principalIndex d * (principalKForm d τ * inverseEtaWeakForm τ) := by
    field_simp [ht]
  simpa only [principalKInverseEtaSeries, K, q, he] using hp

/-- For a holomorphic period-one function, an absolutely convergent series for
the pole-cleared function recovers the intrinsic constant Laurent coefficient. -/
private theorem meromorphicCuspConstantTerm_eq_coeff_of_hasSum {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet)
    (hT : ∀ z : ℂ, 0 < z.im → f (z + 1) = f z)
    (c : ℕ → ℂ) (M : ℕ)
    (hs : ∀ τ : UpperHalfPlane,
      HasSum (fun n : ℕ => c n * Function.Periodic.qParam 1 τ ^ n)
        (Function.Periodic.qParam 1 τ ^ M * f τ)) :
    c M = meromorphicCuspConstantTerm f := by
  let F : UpperHalfPlane → ℂ := fun τ => Function.Periodic.qParam 1 τ ^ M * f τ
  have hper : Function.Periodic (F ∘ ofComplex) 1 := poleClearing_periodic hT M
  have hhol : MDiff F := mdifferentiable_poleClearing hf M
  have hsF (τ : UpperHalfPlane) :
      HasSum (fun n : ℕ => c n * Function.Periodic.qParam 1 τ ^ n) (F τ) := hs τ
  have hb : IsBoundedAtImInfty F := isBoundedAtImInfty_of_fourierRow hsF
  have hc : c M = (qExpansion 1 F).coeff M :=
    fourierRow_coeff_eq_qExpansion hhol hper c hsF M
  have hi : meromorphicCuspConstantTerm f = (qExpansion 1 F).coeff M :=
    meromorphicCuspConstantTerm_eq_qExpansion_coeff_of_bounded hf hT M hb
  exact hc.trans hi.symm

/-- The coefficient at the clearing exponent of the convergent `K_d η⁻¹`
series is its intrinsic cusp constant term. This compares the specified
integral Fourier series with the analytic product, without imposing a value
on either meromorphic germ at zero [rolenManuscript, §3, eq. (ct2)]. -/
theorem principalKInverseEtaSeries_coeff_eq_constantTerm (d : ℕ)
    (hd : d % 24 = 23) :
    ((principalKInverseEtaSeries d).coeff (QSeries.principalIndex d) : ℂ) =
      meromorphicCuspConstantTerm
        ((fun τ : UpperHalfPlane => principalKForm d τ * inverseEtaWeakForm τ) ∘
          ofComplex) := by
  let v : ℂ → ℂ :=
    (fun τ : UpperHalfPlane => principalKForm d τ * inverseEtaWeakForm τ) ∘ ofComplex
  have hv : DifferentiableOn ℂ v upperHalfPlaneSet :=
    UpperHalfPlane.mdifferentiable_iff.mp
      (etaWeightTwoProduct_holomorphic (principalKForm d) inverseEtaWeakForm)
  have hT : ∀ z : ℂ, 0 < z.im → v (z + 1) = v z :=
    etaWeightTwoProduct_periodic (principalKForm d) inverseEtaWeakForm
      (by decide : 2 + 0 = 2)
  exact meromorphicCuspConstantTerm_eq_coeff_of_hasSum hv hT
    (fun n => ((principalKInverseEtaSeries d).coeff n : ℂ))
    (QSeries.principalIndex d) (by
      intro τ
      simpa only [v, Function.comp_apply, ofComplex_apply] using
        principalKInverseEtaSeries_hasSum d hd τ)

/-- The specified integral Fourier coefficient in the `K_d η⁻¹` pairing
vanishes, by the level-one weight-two constant-term theorem
[rolenManuscript, §3, eq. (ct2)]. -/
theorem principalKInverseEtaSeries_constantCoeff_eq_zero (d : ℕ)
    (hd : d % 24 = 23) :
    (principalKInverseEtaSeries d).coeff (QSeries.principalIndex d) = 0 := by
  have h := principalKInverseEtaSeries_coeff_eq_constantTerm d hd
  have hz : ((principalKInverseEtaSeries d).coeff (QSeries.principalIndex d) : ℂ) = 0 :=
    h.trans (principalKForm_inverseEta_constantTerm_eq_zero d)
  exact_mod_cast hz

/-- Convergent integral nome expansions of complementary eta weak forms
multiply to the actual analytic weight-two product. The first expansion uses
the eta factor `t⁻¹` and the second uses `t`, where `t = q^(1/24)`; their
fractional powers cancel [rolenManuscript, §3]. -/
theorem etaWeightTwoProduct_series_hasSum {k l : ℕ}
    (f : EtaWeaklyHolomorphicForm k) (g : EtaInverseWeaklyHolomorphicForm l)
    (A B : PowerSeries ℤ) (M : ℕ)
    (hA : ∀ τ : UpperHalfPlane,
      HasSum (fun n : ℕ => (A.coeff n : ℂ) * Function.Periodic.qParam 1 τ ^ n)
        (Function.Periodic.qParam 1 τ ^ M *
          (Function.Periodic.qParam 24 τ)⁻¹ * f τ))
    (hB : ∀ τ : UpperHalfPlane,
      HasSum (fun n : ℕ => (B.coeff n : ℂ) * Function.Periodic.qParam 1 τ ^ n)
        (Function.Periodic.qParam 24 τ * g τ))
    (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ => ((A * B).coeff n : ℂ) *
      Function.Periodic.qParam 1 τ ^ n)
      (Function.Periodic.qParam 1 τ ^ M * etaWeightTwoProduct f g τ) := by
  let q := Function.Periodic.qParam 1 τ
  let t := Function.Periodic.qParam 24 τ
  have ht : t ≠ 0 := Complex.exp_ne_zero _
  have hp := QSeries.hasSum_coefficientTerm_mul A B q
    (q ^ M * t⁻¹ * f τ) (t * g τ)
    (hA τ).summable.norm (hB τ).summable.norm (hA τ) (hB τ)
  have he : (q ^ M * t⁻¹ * f τ) * (t * g τ) =
      q ^ M * etaWeightTwoProduct f g τ := by
    simp only [etaWeightTwoProduct]
    field_simp [ht]
  simpa only [q, he] using hp

/-- The product coefficient at the pole-clearing index is its intrinsic
meromorphic cusp constant term. This conclusion uses the actual analytic
weak forms and their convergent Fourier evaluations [rolenManuscript, §3]. -/
theorem etaWeightTwoProduct_series_coeff_eq_constantTerm {k l : ℕ}
    (f : EtaWeaklyHolomorphicForm k) (g : EtaInverseWeaklyHolomorphicForm l)
    (hkl : k + l = 2) (A B : PowerSeries ℤ) (M : ℕ)
    (hA : ∀ τ : UpperHalfPlane,
      HasSum (fun n : ℕ => (A.coeff n : ℂ) * Function.Periodic.qParam 1 τ ^ n)
        (Function.Periodic.qParam 1 τ ^ M *
          (Function.Periodic.qParam 24 τ)⁻¹ * f τ))
    (hB : ∀ τ : UpperHalfPlane,
      HasSum (fun n : ℕ => (B.coeff n : ℂ) * Function.Periodic.qParam 1 τ ^ n)
        (Function.Periodic.qParam 24 τ * g τ)) :
    ((A * B).coeff M : ℂ) =
      meromorphicCuspConstantTerm ((etaWeightTwoProduct f g) ∘ ofComplex) := by
  let v : ℂ → ℂ := (etaWeightTwoProduct f g) ∘ ofComplex
  have hv : DifferentiableOn ℂ v upperHalfPlaneSet :=
    UpperHalfPlane.mdifferentiable_iff.mp (etaWeightTwoProduct_holomorphic f g)
  have hT : ∀ z : ℂ, 0 < z.im → v (z + 1) = v z :=
    etaWeightTwoProduct_periodic f g hkl
  exact meromorphicCuspConstantTerm_eq_coeff_of_hasSum hv hT
    (fun n => ((A * B).coeff n : ℂ)) M (by
      intro τ
      simpa only [v, Function.comp_apply, ofComplex_apply] using
        etaWeightTwoProduct_series_hasSum f g A B M hA hB τ)

/-- Any pair of complementary eta weak forms with convergent integral nome
expansions has zero weight-two product coefficient at the pole-clearing index.
The Hecke applications require a separate analytic construction of their
transformed weak forms [rolenManuscript, §3, eqs. (ct1), (ct2)]. -/
theorem etaWeightTwoProduct_series_constantCoeff_eq_zero {k l : ℕ}
    (f : EtaWeaklyHolomorphicForm k) (g : EtaInverseWeaklyHolomorphicForm l)
    (hkl : k + l = 2) (A B : PowerSeries ℤ) (M : ℕ)
    (hA : ∀ τ : UpperHalfPlane,
      HasSum (fun n : ℕ => (A.coeff n : ℂ) * Function.Periodic.qParam 1 τ ^ n)
        (Function.Periodic.qParam 1 τ ^ M *
          (Function.Periodic.qParam 24 τ)⁻¹ * f τ))
    (hB : ∀ τ : UpperHalfPlane,
      HasSum (fun n : ℕ => (B.coeff n : ℂ) * Function.Periodic.qParam 1 τ ^ n)
        (Function.Periodic.qParam 24 τ * g τ)) :
    (A * B).coeff M = 0 := by
  have h := etaWeightTwoProduct_series_coeff_eq_constantTerm
    f g hkl A B M hA hB
  have hz : ((A * B).coeff M : ℂ) = 0 :=
    h.trans (etaWeightTwoProduct_constantTerm_eq_zero f g hkl)
  exact_mod_cast hz

end SptClassification
