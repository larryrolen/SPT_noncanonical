/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.MeromorphicCuspPeriodDescent
public import SptClassification.ModularForms.MeromorphicCuspTranslations

/-!
# Analytic summands of a square-index Hecke operator

The three summand shapes in the square-index Hecke formula are an affine
root average, a finite weighted translation sum, and a dilation. This module
assembles their actual upper-half-plane values and proves that the result has
a meromorphic representative in the original period-24 cusp coordinate.
The finite weights and scalar normalizations remain explicit so that the
Legendre-character Gauss sum can be inserted without changing the analytic
cusp construction [rolenManuscript, §3].
-/

public section

namespace SptClassification

open UpperHalfPlane
open scoped Manifold

/-- The three analytic summand shapes of a square-index Hecke operator.
The first term selects coefficients at indices divisible by `n²`, the second
is the finite character twist, and the last term supplies coefficients at
indices multiplied by `n²`. -/
noncomputable def squareIndexAnalyticSum (f : UpperHalfPlane → ℂ)
    (n : ℕ) (hn : 0 < n) (w : ℕ → ℂ) (A B C : ℂ)
    (τ : UpperHalfPlane) : ℂ :=
  A * (∑ j ∈ Finset.range (n * n),
    f (cuspAffinePoint (n * n) j (Nat.mul_pos hn hn) τ)) +
  B * (∑ j ∈ Finset.range n,
    w j * f (cuspFractionTranslate n j hn τ)) +
  C * f (natDilation (n * n) (Nat.mul_pos hn hn) τ)

/-- The three explicit analytic Hecke summands. -/
theorem squareIndexAnalyticSum_eq (f : UpperHalfPlane → ℂ)
    (n : ℕ) (hn : 0 < n) (w : ℕ → ℂ) (A B C : ℂ)
    (τ : UpperHalfPlane) :
    squareIndexAnalyticSum f n hn w A B C τ =
      A * (∑ j ∈ Finset.range (n * n),
        f (cuspAffinePoint (n * n) j (Nat.mul_pos hn hn) τ)) +
      B * (∑ j ∈ Finset.range n,
        w j * f (cuspFractionTranslate n j hn τ)) +
      C * f (natDilation (n * n) (Nat.mul_pos hn hn) τ) := (rfl)

/-- Every finite analytic combination of the three Hecke summand shapes
has a genuine meromorphic period-24 cusp representative. This uses the
cyclic symmetry of the unweighted affine average, and retains every
character weight in the middle term. -/
theorem meromorphicCusp_squareIndexAnalyticSum
    {f : UpperHalfPlane → ℂ} {G : ℂ → ℂ}
    (hf : MDiff f) (hG : MeromorphicAt G 0)
    (hEq : ∀ τ : UpperHalfPlane,
      G (Function.Periodic.qParam 24 τ) = f τ)
    (n : ℕ) (hn : 0 < n) (w : ℕ → ℂ) (A B C : ℂ) :
    ∃ H : ℂ → ℂ, MeromorphicAt H 0 ∧
      ∀ τ : UpperHalfPlane,
        H (Function.Periodic.qParam 24 τ) =
          squareIndexAnalyticSum f n hn w A B C τ := by
  let hnn : 0 < n * n := Nat.mul_pos hn hn
  obtain ⟨J, hJ, hJeq⟩ :=
    meromorphicCuspRootAverage_descends hf hG hEq (n * n) hnn
  obtain ⟨K, hK, hKeq⟩ :=
    meromorphicCusp_weightedFractionTranslations hG hEq w n hn
  obtain ⟨L, hL, hLeq⟩ :=
    meromorphicCusp24_natDilation hG hEq (n * n) hnn
  refine ⟨fun q => A * J q + B * K q + C * L q, ?_, ?_⟩
  · have hAJ : MeromorphicAt (fun q : ℂ => A * J q) 0 :=
      ((analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => A) 0).meromorphicAt).fun_mul hJ
    have hBK : MeromorphicAt (fun q : ℂ => B * K q) 0 :=
      ((analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => B) 0).meromorphicAt).fun_mul hK
    have hCL : MeromorphicAt (fun q : ℂ => C * L q) 0 :=
      ((analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => C) 0).meromorphicAt).fun_mul hL
    exact (hAJ.fun_add hBK).fun_add hCL
  · intro τ
    simp only [squareIndexAnalyticSum, hJeq, hKeq, hLeq]

/-- The analytic square-index summand combination for an actual inverse-eta
weak form has the cusp meromorphy needed in a subsequent Hecke pairing.
Its full modular law is a separate analytic Hecke assertion. -/
theorem EtaInverseWeaklyHolomorphicForm.has_meromorphic_cusp_squareIndexAnalyticSum
    {k : ℕ} (f : EtaInverseWeaklyHolomorphicForm k)
    (n : ℕ) (hn : 0 < n) (w : ℕ → ℂ) (A B C : ℂ) :
    ∃ H : ℂ → ℂ, MeromorphicAt H 0 ∧
      ∀ τ : UpperHalfPlane,
        H (Function.Periodic.qParam 24 τ) =
          squareIndexAnalyticSum f n hn w A B C τ := by
  obtain ⟨G, hG, hEq⟩ := f.has_meromorphic_cusp
  exact meromorphicCusp_squareIndexAnalyticSum f.holomorphic hG hEq n hn w A B C

end SptClassification
