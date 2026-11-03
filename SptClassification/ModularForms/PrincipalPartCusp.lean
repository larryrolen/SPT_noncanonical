/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.PrincipalPartPolynomial
public import SptClassification.ModularForms.EtaQuotientExpansion
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Algebra.Polynomial.Inductions

/-!
# Cusp representations of eta polynomials

The quotient of the analytic cusp functions of `E₄` and `Δ` gives a meromorphic
representative of `j`. Using the period-24 nome removes eta's fractional exponent
and gives a meromorphic cusp representative of every `η A(j)` in the
principal-part construction [rolenManuscript, §3]. No identification with the
integral formal coefficient series is used here.
-/

public section

namespace SptClassification

open UpperHalfPlane
open scoped MatrixGroups

/-- The quotient of the level-one cusp functions representing the analytic invariant. -/
noncomputable def levelOneJCusp (q : ℂ) : ℂ :=
  cuspFunction 1 ModularForm.E₄ q ^ 3 / cuspFunction 1 CuspForm.discriminant q

/-- The quotient formula for the invariant's cusp representative. -/
theorem levelOneJCusp_eq (q : ℂ) :
    levelOneJCusp q =
      cuspFunction 1 ModularForm.E₄ q ^ 3 / cuspFunction 1 CuspForm.discriminant q :=
  (rfl)

/-- The cusp representative agrees with the actual analytic invariant. -/
theorem levelOneJCusp_qParam (τ : UpperHalfPlane) :
    levelOneJCusp (Function.Periodic.qParam 1 τ) = levelOneJ τ := by
  simp only [levelOneJCusp, levelOneJ_eq,
    SlashInvariantFormClass.eq_cuspFunction _ _ one_mem_strictPeriods_SL one_ne_zero]

/-- A quotient of the analytic cusp functions is meromorphic, even where the
denominator vanishes. -/
theorem meromorphicAt_levelOneJCusp_zero : MeromorphicAt levelOneJCusp 0 := by
  have hE := ModularFormClass.analyticAt_cuspFunction_zero ModularForm.E₄
    one_pos one_mem_strictPeriods_SL
  have hD := ModularFormClass.analyticAt_cuspFunction_zero CuspForm.discriminant
    one_pos one_mem_strictPeriods_SL
  exact (hE.pow 3).meromorphicAt.div hD.meromorphicAt

/-- The Euler product is analytic throughout a neighborhood of the cusp center. -/
theorem analyticAt_etaEulerProduct_zero : AnalyticAt ℂ etaEulerProduct 0 := by
  exact differentiableOn_etaEulerProduct.analyticAt
    (Metric.isOpen_ball.mem_nhds (by simp))

/-- The period-24 nome is a specified exponential root of the period-one nome. -/
theorem qParam_twentyFour_pow (z : ℂ) :
    Function.Periodic.qParam 24 z ^ 24 = Function.Periodic.qParam 1 z := by
  unfold Function.Periodic.qParam
  rw [← Complex.exp_nat_mul]
  congr 1
  norm_num
  ring

private theorem meromorphicAt_polynomial_eval (P : Polynomial ℂ) {f : ℂ → ℂ}
    {z : ℂ} (hf : MeromorphicAt f z) :
    MeromorphicAt (fun q => P.eval (f q)) z := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simpa only [Polynomial.eval_add] using hP.fun_add hQ
  | monomial n a =>
      simpa only [Polynomial.eval_monomial] using
        (analyticAt_const.meromorphicAt.fun_mul (hf.pow n) :
          MeromorphicAt (fun q => a * f q ^ n) z)

/-- A cusp representative in the period-24 nome for the actual eta polynomial. -/
noncomputable def etaJPolynomialCusp (P : Polynomial ℤ) (t : ℂ) : ℂ :=
  t * etaEulerProduct (t ^ 24) *
    (P.map (Int.castRingHom ℂ)).eval (levelOneJCusp (t ^ 24))

/-- This cusp representative is meromorphic at zero. -/
theorem meromorphicAt_etaJPolynomialCusp_zero (P : Polynomial ℤ) :
    MeromorphicAt (etaJPolynomialCusp P) 0 := by
  have hpower : AnalyticAt ℂ (fun t : ℂ => t ^ 24) 0 := analyticAt_id.pow 24
  have hE : AnalyticAt ℂ (fun t : ℂ => etaEulerProduct (t ^ 24)) 0 := by
    exact analyticAt_etaEulerProduct_zero.fun_comp_of_eq hpower (by simp)
  have hJ : MeromorphicAt (fun t : ℂ => levelOneJCusp (t ^ 24)) 0 := by
    exact MeromorphicAt.comp_analyticAt (𝕜 := ℂ) (𝕜' := ℂ)
      (f := levelOneJCusp) (g := fun t : ℂ => t ^ 24) (x := (0 : ℂ))
      (by simpa using meromorphicAt_levelOneJCusp_zero) hpower
  exact (analyticAt_id.mul hE).meromorphicAt.mul
    (meromorphicAt_polynomial_eval _ hJ)

/-- Evaluation at the period-24 nome recovers `η A(j)` exactly. -/
theorem etaJPolynomialCusp_qParam (P : Polynomial ℤ) (τ : UpperHalfPlane) :
    etaJPolynomialCusp P (Function.Periodic.qParam 24 τ) = etaJPolynomial P τ := by
  have hη : ModularForm.eta τ = Function.Periodic.qParam 24 τ *
      etaEulerProduct (Function.Periodic.qParam 1 τ) := by
    simpa using eta_nat_mul_eq_euler 1 (τ : ℂ)
  simp only [etaJPolynomialCusp, qParam_twentyFour_pow, levelOneJCusp_qParam,
    etaJPolynomial_eq, hη]

/-- Every integral eta polynomial has a meromorphic cusp representative with
respect to the period-24 nome. -/
theorem etaJPolynomial_has_meromorphic_cusp (P : Polynomial ℤ) :
    ∃ F : ℂ → ℂ, MeromorphicAt F 0 ∧
      ∀ τ : UpperHalfPlane, F (Function.Periodic.qParam 24 τ) = etaJPolynomial P τ :=
  ⟨etaJPolynomialCusp P, meromorphicAt_etaJPolynomialCusp_zero P,
    etaJPolynomialCusp_qParam P⟩

end SptClassification
