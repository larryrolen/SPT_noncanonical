/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.PrincipalPartIntegral
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Coeff

/-!
# Integral polynomials behind principal-part elimination

The row reduction is lifted to an explicit polynomial in `j`. This records
the actual integral polynomial needed to construct an analytic function from
the coefficient calculation [rolenManuscript, §3].
-/

public section

namespace SptClassification.QSeries

open Polynomial

/-- Interpret an integral polynomial as the corresponding integral linear
combination of a family of coefficient rows. -/
noncomputable def polynomialRows (raw : ℕ → ℤ → ℤ) :
    Polynomial ℤ →ₗ[ℤ] (ℤ → ℤ) :=
  Polynomial.lsum fun n =>
    { toFun := fun c => c • raw n
      map_add' := by intros; simp [add_smul]
      map_smul' := by intros; simp [mul_smul] }

theorem polynomialRows_X_pow (raw : ℕ → ℤ → ℤ) (n : ℕ) :
    polynomialRows raw (X ^ n) = raw n := by
  simp [polynomialRows, X_pow_eq_monomial]

theorem polynomialRows_C_mul (raw : ℕ → ℤ → ℤ) (c : ℤ) (P : Polynomial ℤ) :
    polynomialRows raw (C c * P) = c • polynomialRows raw P := by
  rw [← smul_eq_C_mul, map_smul]

theorem polynomialRows_C (raw : ℕ → ℤ → ℤ) (c : ℤ) :
    polynomialRows raw (C c) = c • raw 0 := by
  have hone : polynomialRows raw 1 = raw 0 := by
    simpa using polynomialRows_X_pow raw 0
  simpa [hone] using polynomialRows_C_mul raw c 1

/-- The integral polynomial obtained by eliminating the lower poles of a
triangular family of rows. -/
noncomputable def principalPartPolynomial (raw : ℕ → ℤ → ℤ) (n : ℕ) : Polynomial ℤ :=
  Nat.strongRecOn n fun n ih =>
    X ^ n - Finset.sum (Finset.univ : Finset (Finset.range n))
      (fun k => C (raw n (k : ℤ)) * ih k (Finset.mem_range.mp k.property))

theorem principalPartPolynomial_eq (raw : ℕ → ℤ → ℤ) (n : ℕ) :
    principalPartPolynomial raw n =
      X ^ n - Finset.sum (Finset.univ : Finset (Finset.range n))
        (fun k => C (raw n (k : ℤ)) * principalPartPolynomial raw k) := by
  unfold principalPartPolynomial
  rw [Nat.strongRecOn_eq]

/-- Evaluating the elimination polynomial in the original rows recovers the
entire eliminated coefficient sequence, including all nonpolar coefficients. -/
theorem polynomialRows_principalPartPolynomial (raw : ℕ → ℤ → ℤ) (n : ℕ) :
    polynomialRows raw (principalPartPolynomial raw n) =
      principalPartElimination raw n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    calc
      _ = raw n - Finset.sum (Finset.univ : Finset (Finset.range n))
          (fun k => raw n (k : ℤ) • polynomialRows raw (principalPartPolynomial raw k)) := by
        rw [principalPartPolynomial_eq, map_sub, map_sum, polynomialRows_X_pow]
        simp_rw [polynomialRows_C_mul]
      _ = raw n - Finset.sum (Finset.univ : Finset (Finset.range n))
          (fun k => raw n (k : ℤ) • principalPartElimination raw k) := by
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        rw [ih k (Finset.mem_range.mp k.property)]
      _ = principalPartElimination raw n := by
        funext r
        simpa only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, zsmul_eq_mul,
          Pi.mul_apply, Pi.intCast_apply, Int.cast_id] using
          (principalPartElimination_eq raw n r).symm

/-- The polynomial for the eta rows `η j^n`. -/
noncomputable def etaPrincipalPolynomial (U J : PowerSeries ℤ) (n : ℕ) : Polynomial ℤ :=
  principalPartPolynomial (etaJRow U J) n

theorem etaPrincipalPolynomial_eq (U J : PowerSeries ℤ) (n : ℕ) :
    etaPrincipalPolynomial U J n = principalPartPolynomial (etaJRow U J) n := (rfl)

/-- The polynomial for the derivative rows `-η (Θj) j^n`. -/
noncomputable def etaThetaPrincipalPolynomial (U J : PowerSeries ℤ) (n : ℕ) :
    Polynomial ℤ :=
  principalPartPolynomial (etaThetaJRow U J) n

theorem etaThetaPrincipalPolynomial_eq (U J : PowerSeries ℤ) (n : ℕ) :
    etaThetaPrincipalPolynomial U J n =
      principalPartPolynomial (etaThetaJRow U J) n := (rfl)

/-- The integral polynomial for the prescribed first coefficient of `H_d`.
Its analytic Fourier identification remains a separate theorem. -/
noncomputable def integralHPolynomial (d : ℕ) (a : ℤ) : Polynomial ℤ :=
  etaPrincipalPolynomial etaIntegralCore modularJIntegralCore (principalIndex d) - C a

theorem integralHPolynomial_eq (d : ℕ) (a : ℤ) :
    integralHPolynomial d a =
      etaPrincipalPolynomial etaIntegralCore modularJIntegralCore (principalIndex d) - C a :=
  (rfl)

/-- The integral polynomial in the derivative row family for `K_d`. -/
noncomputable def integralKPolynomial (d : ℕ) : Polynomial ℤ :=
  etaThetaPrincipalPolynomial etaIntegralCore modularJIntegralCore
    (principalIndex d - 1)

theorem integralKPolynomial_eq (d : ℕ) :
    integralKPolynomial d =
      etaThetaPrincipalPolynomial etaIntegralCore modularJIntegralCore
        (principalIndex d - 1) := (rfl)

/-- The explicit integral polynomial for `H_d` has exactly the prescribed
coefficient sequence from the formal row construction. -/
theorem polynomialRows_integralHPolynomial (d : ℕ) (a : ℤ) :
    polynomialRows (etaJRow etaIntegralCore modularJIntegralCore)
      (integralHPolynomial d a) = integralHPrincipalPart d a := by
  rw [integralHPolynomial, map_sub, polynomialRows_C]
  change polynomialRows (etaJRow etaIntegralCore modularJIntegralCore)
      (principalPartPolynomial _ _) - a • etaJRow etaIntegralCore modularJIntegralCore 0 = _
  rw [polynomialRows_principalPartPolynomial]
  funext r
  simpa only [Pi.sub_apply, zsmul_eq_mul, Pi.mul_apply, Pi.intCast_apply,
    Int.cast_id] using
    (integralHPrincipalPart_eq d a r).symm

/-- The derivative-row polynomial for `K_d` realizes its complete formal
coefficient sequence. -/
theorem polynomialRows_integralKPolynomial (d : ℕ) :
    polynomialRows (etaThetaJRow etaIntegralCore modularJIntegralCore)
      (integralKPolynomial d) = integralKPrincipalPart d := by
  rw [integralKPolynomial, integralKPrincipalPart_eq]
  exact polynomialRows_principalPartPolynomial _ _

/-- Full-row polynomial realization, including both prescribed integral
principal-part families [rolenManuscript, §3]. The first equality holds at
every integer coefficient index through equality of coefficient functions. -/
theorem principalPartPolynomial_full_rows :
    (∀ (raw : ℕ → ℤ → ℤ) (n : ℕ),
      principalPartPolynomial raw n =
        X ^ n - Finset.sum (Finset.univ : Finset (Finset.range n))
          (fun k => C (raw n (k : ℤ)) * principalPartPolynomial raw k)) ∧
    (∀ (raw : ℕ → ℤ → ℤ) (n : ℕ),
      polynomialRows raw (X ^ n) = raw n) ∧
    (∀ (raw : ℕ → ℤ → ℤ) (n : ℕ),
      polynomialRows raw (principalPartPolynomial raw n) =
        principalPartElimination raw n) ∧
    (∀ (d : ℕ) (a : ℤ),
      polynomialRows (etaJRow etaIntegralCore modularJIntegralCore)
        (integralHPolynomial d a) = integralHPrincipalPart d a) ∧
    (∀ d : ℕ,
      polynomialRows (etaThetaJRow etaIntegralCore modularJIntegralCore)
        (integralKPolynomial d) = integralKPrincipalPart d) := by
  exact ⟨principalPartPolynomial_eq, polynomialRows_X_pow,
    polynomialRows_principalPartPolynomial,
    polynomialRows_integralHPolynomial,
    polynomialRows_integralKPolynomial⟩

end SptClassification.QSeries
