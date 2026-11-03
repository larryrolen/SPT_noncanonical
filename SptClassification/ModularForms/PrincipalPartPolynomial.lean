/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.PrincipalPartInvariant
public import SptClassification.ModularForms.EtaTranslation
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Eta polynomials in the level-one invariant

Integral polynomials in the analytic invariant give the functions `η P(j)`
used for the weight-one-half principal-part rows [rolenManuscript, §3].
Their Fourier coefficients and cusp growth require separate arguments.
-/

public section

namespace SptClassification

open scoped MatrixGroups Manifold

/-- An integral polynomial in the analytic invariant, multiplied by eta. -/
noncomputable def etaJPolynomial (P : Polynomial ℤ) (τ : UpperHalfPlane) : ℂ :=
  ModularForm.eta τ * (P.map (Int.castRingHom ℂ)).eval (levelOneJ τ)

/-- The analytic evaluation formula for an eta polynomial. -/
theorem etaJPolynomial_eq (P : Polynomial ℤ) (τ : UpperHalfPlane) :
    etaJPolynomial P τ =
      ModularForm.eta τ * (P.map (Int.castRingHom ℂ)).eval (levelOneJ τ) :=
  (rfl)

theorem etaJPolynomial_X_pow (n : ℕ) (τ : UpperHalfPlane) :
    etaJPolynomial (Polynomial.X ^ n) τ =
      ModularForm.eta τ * levelOneJ τ ^ n := by
  simp [etaJPolynomial]

theorem etaJPolynomial_add (P Q : Polynomial ℤ) (τ : UpperHalfPlane) :
    etaJPolynomial (P + Q) τ = etaJPolynomial P τ + etaJPolynomial Q τ := by
  simp [etaJPolynomial, mul_add]

theorem etaJPolynomial_sub (P Q : Polynomial ℤ) (τ : UpperHalfPlane) :
    etaJPolynomial (P - Q) τ = etaJPolynomial P τ - etaJPolynomial Q τ := by
  simp [etaJPolynomial, mul_sub]

theorem etaJPolynomial_C_mul (c : ℤ) (P : Polynomial ℤ)
    (τ : UpperHalfPlane) :
    etaJPolynomial (Polynomial.C c * P) τ =
      (c : ℂ) * etaJPolynomial P τ := by
  simp [etaJPolynomial]
  ring

/-- An integral upper-unipotent matrix representing translation by an integer. -/
def upperUnipotent (n : ℤ) : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  ⟨!![1, n; 0, 1], by norm_num [Matrix.det_fin_two]⟩

/-- The matrix underlying the integral translation element. -/
theorem upperUnipotent_matrix (n : ℤ) :
    (upperUnipotent n : Matrix (Fin 2) (Fin 2) ℤ) = !![1, n; 0, 1] := (rfl)

theorem upperUnipotent_apply (n : ℤ) (τ : UpperHalfPlane) :
    (↑(upperUnipotent n • τ : UpperHalfPlane) : ℂ) = (τ : ℂ) + n := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [upperUnipotent]

/-- The analytic invariant is periodic under every integer translation. -/
theorem levelOneJ_add_int (n : ℤ) (τ : UpperHalfPlane) :
    levelOneJ (↑((n : ℝ) +ᵥ τ) : UpperHalfPlane) = levelOneJ τ := by
  have hγ : Matrix.SpecialLinearGroup.mapGL ℝ (upperUnipotent n) ∈ 𝒮ℒ :=
    ⟨upperUnipotent n, rfl⟩
  have hsame : upperUnipotent n • τ = (n : ℝ) +ᵥ τ := by
    apply UpperHalfPlane.ext
    simpa only [UpperHalfPlane.coe_vadd, Complex.ofReal_intCast, add_comm] using
      upperUnipotent_apply n τ
  rw [← hsame]
  exact levelOneJ_invariant _ hγ τ

/-- Eta polynomials inherit eta's transformation factor under every level-one
matrix, without choosing a square-root branch for that factor. -/
theorem etaJPolynomial_cross_transform (P : Polynomial ℤ)
    (γ : GL (Fin 2) ℝ) (hγ : γ ∈ 𝒮ℒ) (τ : UpperHalfPlane) :
    etaJPolynomial P (γ • τ) * ModularForm.eta τ =
      ModularForm.eta ((γ • τ : UpperHalfPlane) : ℂ) * etaJPolynomial P τ := by
  simp only [etaJPolynomial, levelOneJ_invariant γ hγ τ]
  ring

/-- Translation acts on each eta polynomial by eta's exact multiplier. -/
theorem etaJPolynomial_add_int (P : Polynomial ℤ) (n : ℤ)
    (τ : UpperHalfPlane) :
    etaJPolynomial P ((n : ℝ) +ᵥ τ) =
      Complex.exp (Real.pi * Complex.I * n / 12) * etaJPolynomial P τ := by
  simp only [etaJPolynomial, levelOneJ_add_int]
  have hη := eta_add_int (τ : ℂ) n
  simpa only [UpperHalfPlane.coe_vadd, Complex.ofReal_intCast, add_comm, mul_assoc] using
    congrArg (fun z : ℂ => z * (P.map (Int.castRingHom ℂ)).eval (levelOneJ τ)) hη

/-- The holomorphy and both symmetries of the level-one invariant used in the
principal-part construction [rolenManuscript, §3]. -/
theorem levelOneJ_analytic_invariance :
    MDiff levelOneJ ∧
    (∀ (γ : GL (Fin 2) ℝ), γ ∈ 𝒮ℒ → ∀ τ : UpperHalfPlane,
      levelOneJ (γ • τ) = levelOneJ τ) ∧
    (∀ (n : ℤ) (τ : UpperHalfPlane),
      levelOneJ ((n : ℝ) +ᵥ τ) = levelOneJ τ) := by
  exact ⟨levelOneJ_mdifferentiable,
    fun γ hγ τ => levelOneJ_invariant γ hγ τ,
    fun n τ => levelOneJ_add_int n τ⟩

/-- Both exact eta-polynomial transformation laws, with the analytic eta
factor and integer-translation multiplier [rolenManuscript, §3]. -/
theorem etaJPolynomial_transformation_laws :
    (∀ (P : Polynomial ℤ) (γ : GL (Fin 2) ℝ), γ ∈ 𝒮ℒ →
      ∀ τ : UpperHalfPlane,
      etaJPolynomial P (γ • τ) * ModularForm.eta τ =
        ModularForm.eta ((γ • τ : UpperHalfPlane) : ℂ) * etaJPolynomial P τ) ∧
    (∀ (P : Polynomial ℤ) (n : ℤ) (τ : UpperHalfPlane),
      etaJPolynomial P ((n : ℝ) +ᵥ τ) =
        Complex.exp (Real.pi * Complex.I * n / 12) * etaJPolynomial P τ) := by
  exact ⟨fun P γ hγ τ => etaJPolynomial_cross_transform P γ hγ τ,
    fun P n τ => etaJPolynomial_add_int P n τ⟩

end SptClassification
