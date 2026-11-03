/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.WeightTwoConstantTermEta

/-!
# Rational Fourier pairings of complementary eta forms

The two factors in a Hecke product may both have poles, and the weight
`-1/2` Hecke row has rational coefficients.  We clear each pole separately
before taking the Cauchy product.  This identifies its coefficient at the
sum of the two shifts with the intrinsic weight-two constant term
[rolenManuscript, §3, eqs. (ct1), (ct2)].
-/

public section

namespace SptClassification

open UpperHalfPlane
open Filter
open scoped MatrixGroups Manifold

/-- Evaluation of the rational Cauchy coefficient at a complex nome. -/
theorem rationalCoefficientTerm_mul (A B : PowerSeries ℚ) (q : ℂ) (n : ℕ) :
    ((A * B).coeff n : ℂ) * q ^ n =
      ∑ ij ∈ Finset.antidiagonal n,
        ((A.coeff ij.1 : ℂ) * q ^ ij.1) *
          ((B.coeff ij.2 : ℂ) * q ^ ij.2) := by
  rw [PowerSeries.coeff_mul]
  simp only [Rat.cast_sum, Rat.cast_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [← Finset.mem_antidiagonal.mp hij, pow_add]
  ring

/-- Absolute convergence of two rational Fourier rows gives the complete
convergent Fourier row of their product. -/
theorem rationalProduct_hasSum (A B : PowerSeries ℚ) (q a b : ℂ)
    (ha : HasSum (fun n => (A.coeff n : ℂ) * q ^ n) a)
    (hb : HasSum (fun n => (B.coeff n : ℂ) * q ^ n) b) :
    HasSum (fun n => ((A * B).coeff n : ℂ) * q ^ n) (a * b) := by
  have hA := ha.summable.norm
  have hB := hb.summable.norm
  have hN : Summable (fun n => ‖((A * B).coeff n : ℂ) * q ^ n‖) := by
    simpa only [rationalCoefficientTerm_mul] using
      summable_norm_sum_mul_antidiagonal_of_summable_norm hA hB
  have h := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hA hB
  rw [ha.tsum_eq, hb.tsum_eq] at h
  simpa only [rationalCoefficientTerm_mul, ← h] using hN.of_norm.hasSum

/-- Both shifts contribute to the pole clearing of an actual eta product.
The fractional eta powers cancel after multiplication. -/
theorem etaWeightTwoProduct_rationalSeries_hasSum {k l : ℕ}
    (f : EtaWeaklyHolomorphicForm k) (g : EtaInverseWeaklyHolomorphicForm l)
    (A B : PowerSeries ℚ) (M N : ℕ)
    (hA : ∀ τ : UpperHalfPlane,
      HasSum (fun j => (A.coeff j : ℂ) * Function.Periodic.qParam 1 τ ^ j)
        (Function.Periodic.qParam 1 τ ^ M *
          (Function.Periodic.qParam 24 τ)⁻¹ * f τ))
    (hB : ∀ τ : UpperHalfPlane,
      HasSum (fun j => (B.coeff j : ℂ) * Function.Periodic.qParam 1 τ ^ j)
        (Function.Periodic.qParam 1 τ ^ N *
          Function.Periodic.qParam 24 τ * g τ))
    (τ : UpperHalfPlane) :
    HasSum (fun j => ((A * B).coeff j : ℂ) * Function.Periodic.qParam 1 τ ^ j)
      (Function.Periodic.qParam 1 τ ^ (M + N) *
        etaWeightTwoProduct f g τ) := by
  let q := Function.Periodic.qParam 1 τ
  let t := Function.Periodic.qParam 24 τ
  have ht : t ≠ 0 := Complex.exp_ne_zero _
  have hp := rationalProduct_hasSum A B q
    (q ^ M * t⁻¹ * f τ) (q ^ N * t * g τ) (hA τ) (hB τ)
  have he : (q ^ M * t⁻¹ * f τ) * (q ^ N * t * g τ) =
      q ^ (M + N) * etaWeightTwoProduct f g τ := by
    simp only [etaWeightTwoProduct_eq, pow_add]
    field_simp [ht]
  simpa only [q, he] using hp

/-- A convergent pole-cleared Fourier series recovers the intrinsic Laurent
coefficient at the clearing exponent. -/
private theorem rationalCuspConstantTerm_eq_coeff_of_hasSum
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f upperHalfPlaneSet)
    (hT : ∀ z : ℂ, 0 < z.im → f (z + 1) = f z)
    (c : ℕ → ℂ) (M : ℕ)
    (hs : ∀ τ : UpperHalfPlane,
      HasSum (fun j => c j * Function.Periodic.qParam 1 τ ^ j)
        (Function.Periodic.qParam 1 τ ^ M * f τ)) :
    c M = meromorphicCuspConstantTerm f := by
  let F : UpperHalfPlane → ℂ := fun τ => Function.Periodic.qParam 1 τ ^ M * f τ
  have hper : Function.Periodic (F ∘ ofComplex) 1 := poleClearing_periodic hT M
  have hhol : MDiff F := mdifferentiable_poleClearing hf M
  have hb : IsBoundedAtImInfty F := isBoundedAtImInfty_of_fourierRow hs
  have hc : c M = (qExpansion 1 F).coeff M :=
    fourierRow_coeff_eq_qExpansion hhol hper c hs M
  have hi : meromorphicCuspConstantTerm f = (qExpansion 1 F).coeff M :=
    meromorphicCuspConstantTerm_eq_qExpansion_coeff_of_bounded hf hT M hb
  exact hc.trans hi.symm

/-- The rational Cauchy coefficient at the sum of the two pole shifts is zero
for actual complementary eta weak forms [rolenManuscript, §3]. -/
theorem etaWeightTwoProduct_rationalSeries_constantCoeff_eq_zero {k l : ℕ}
    (f : EtaWeaklyHolomorphicForm k) (g : EtaInverseWeaklyHolomorphicForm l)
    (hkl : k + l = 2) (A B : PowerSeries ℚ) (M N : ℕ)
    (hA : ∀ τ : UpperHalfPlane,
      HasSum (fun j => (A.coeff j : ℂ) * Function.Periodic.qParam 1 τ ^ j)
        (Function.Periodic.qParam 1 τ ^ M *
          (Function.Periodic.qParam 24 τ)⁻¹ * f τ))
    (hB : ∀ τ : UpperHalfPlane,
      HasSum (fun j => (B.coeff j : ℂ) * Function.Periodic.qParam 1 τ ^ j)
        (Function.Periodic.qParam 1 τ ^ N *
          Function.Periodic.qParam 24 τ * g τ)) :
    (A * B).coeff (M + N) = 0 := by
  have hv : DifferentiableOn ℂ
      ((etaWeightTwoProduct f g) ∘ ofComplex) upperHalfPlaneSet :=
    UpperHalfPlane.mdifferentiable_iff.mp (etaWeightTwoProduct_holomorphic f g)
  have hT := etaWeightTwoProduct_periodic f g hkl
  have hc := rationalCuspConstantTerm_eq_coeff_of_hasSum hv hT
    (fun j => ((A * B).coeff j : ℂ)) (M + N) (by
      intro τ
      simpa only [Function.comp_apply, ofComplex_apply] using
        etaWeightTwoProduct_rationalSeries_hasSum f g A B M N hA hB τ)
  have hz : ((A * B).coeff (M + N) : ℂ) = 0 :=
    hc.trans (etaWeightTwoProduct_constantTerm_eq_zero f g hkl)
  exact_mod_cast hz

end SptClassification
