/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.OrientationClasses
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.Tactic.Ring

/-!
# Analytic CM pole clearing at a cusp

The eta coordinate has the shape `t = U(q)/q` at infinity. Homogeneous
polynomial evaluation removes its pole without choosing a value for `t(0)`.
For the paired degree-`2h` CM polynomials, the square of their product has
pole order at most `8h`, canceled by the normalized `Delta^(8h)`.
This is the local analytic step in [rolenManuscript, Section 4]; global
modularity and integral comparison are separate assertions.
-/

public section

namespace SptClassification

/-- Polynomial evaluation with its possible cusp pole cleared. -/
noncomputable def polynomialCuspHomogenization (P : Polynomial ℂ)
    (U : ℂ → ℂ) (q : ℂ) : ℂ :=
  MvPolynomial.eval ![U q, q] (P.homogenize P.natDegree)

/-- Finite-sum formula for the standard homogeneous polynomial in the cusp chart. -/
theorem polynomialCuspHomogenization_sum (P : Polynomial ℂ)
    (U : ℂ → ℂ) (q : ℂ) :
    polynomialCuspHomogenization P U q =
      ∑ i ∈ Finset.range (P.natDegree + 1),
        P.coeff i * U q ^ i * q ^ (P.natDegree - i) := by
  unfold polynomialCuspHomogenization Polynomial.homogenize
  rw [MvPolynomial.eval_sum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro i hi
  rw [MvPolynomial.eval_monomial, Finsupp.update_eq_add_single,
    Finsupp.prod_add_index', Finsupp.prod_single_index, Finsupp.prod_single_index]
  all_goals simp [mul_assoc, pow_add]

/-- Away from the cusp, homogenization equals the original evaluation
multiplied by the degree power of the local parameter. -/
theorem polynomialCuspHomogenization_eq (P : Polynomial ℂ)
    (U : ℂ → ℂ) {q : ℂ} (hq : q ≠ 0) :
    polynomialCuspHomogenization P U q =
      q ^ P.natDegree * P.eval (U q / q) := by
  simpa only [polynomialCuspHomogenization, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, mul_comm] using
    (Polynomial.eval_homogenize (p := P) (le_refl P.natDegree) ![U q, q] hq)

/-- The cleared evaluation is analytic even at the cusp. -/
theorem analyticAt_polynomialCuspHomogenization (P : Polynomial ℂ)
    {U : ℂ → ℂ} {q : ℂ} (hU : AnalyticAt ℂ U q) :
    AnalyticAt ℂ (polynomialCuspHomogenization P U) q := by
  have h := (Finset.analyticAt_sum (Finset.range (P.natDegree + 1))
      (f := fun i z => P.coeff i * U z ^ i * z ^ (P.natDegree - i))
      (fun i _ => (analyticAt_const.mul (hU.pow i)).mul
        (analyticAt_id.pow (P.natDegree - i))))
  convert h using 1
  ext z
  simp only [Finset.sum_apply, polynomialCuspHomogenization_sum]

/-- The value after removing the cusp pole retains the leading coefficient. -/
theorem polynomialCuspHomogenization_zero (P : Polynomial ℂ) (U : ℂ → ℂ) :
    polynomialCuspHomogenization P U 0 = P.leadingCoeff * U 0 ^ P.natDegree := by
  rw [polynomialCuspHomogenization_sum, Finset.sum_eq_single P.natDegree]
  · simp only [Nat.sub_self, pow_zero, mul_one, Polynomial.coeff_natDegree]
  · intro i hi hne
    have hi' : i < P.natDegree :=
      lt_of_le_of_ne (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hne
    simp [Nat.ne_of_gt (Nat.sub_pos_of_lt hi')]
  · simp

/-- The analytic extension of the actual CM clearing factor in the infinity
chart. Here `U=q*t` and `V=Delta/q`; no value of `t` at zero is assumed. -/
noncomputable def cmAnalyticCuspClearingFactor (D : ℤ) [Fact (D < 0)]
    (U V : ℂ → ℂ) (q : ℂ) : ℂ :=
  (polynomialCuspHomogenization (cmClassPolynomialA D) U q *
      polynomialCuspHomogenization (cmClassPolynomialB D) U q) ^ 2 *
    V q ^ (8 * formClassNumber D)

/-- The actual degree equations give exactly the exponent `8h`, including
both CM orientations and the square needed for double poles. -/
theorem cmAnalyticCuspClearingFactor_eq (D : ℤ) [Fact (D < 0)]
    (hD : D % 24 = 1) (U V : ℂ → ℂ) {q : ℂ} (hq : q ≠ 0) :
    cmAnalyticCuspClearingFactor D U V q =
      ((cmClassPolynomialA D).eval (U q / q) *
        (cmClassPolynomialB D).eval (U q / q)) ^ 2 *
          (q * V q) ^ (8 * formClassNumber D) := by
  unfold cmAnalyticCuspClearingFactor
  rw [polynomialCuspHomogenization_eq _ _ hq,
    polynomialCuspHomogenization_eq _ _ hq,
    cmClassPolynomialA_natDegree D hD, cmClassPolynomialB_natDegree D hD,
    mul_pow]
  have hpow : q ^ (8 * formClassNumber D) =
      (q ^ (2 * formClassNumber D)) ^ 4 := by
    rw [← pow_mul]
    congr 1
    omega
  rw [mul_pow q (V q), hpow]
  ring

/-- The paired CM factor times `Delta^(8h)` is analytic at infinity once
the two normalized cusp functions are analytic. -/
theorem analyticAt_cmAnalyticCuspClearingFactor (D : ℤ) [Fact (D < 0)]
    {U V : ℂ → ℂ} {q : ℂ} (hU : AnalyticAt ℂ U q) (hV : AnalyticAt ℂ V q) :
    AnalyticAt ℂ (cmAnalyticCuspClearingFactor D U V) q :=
  (((analyticAt_polynomialCuspHomogenization _ hU).mul
    (analyticAt_polynomialCuspHomogenization _ hU)).pow 2).mul
      (hV.pow (8 * formClassNumber D))

/-- The normalized clearing factor is one at the infinity cusp, so the
clearing process preserves the leading coefficient of the lift. -/
theorem cmAnalyticCuspClearingFactor_zero (D : ℤ) [Fact (D < 0)]
    {U V : ℂ → ℂ} (hU : U 0 = 1) (hV : V 0 = 1) :
    cmAnalyticCuspClearingFactor D U V 0 = 1 := by
  simp [cmAnalyticCuspClearingFactor, polynomialCuspHomogenization_zero,
    hU, hV, (cmClassPolynomialA_monic D).leadingCoeff,
    (cmClassPolynomialB_monic D).leadingCoeff]

/-- The actual CM clearing factor removes the infinity cusp pole while
preserving the constant term of an analytic lift. The equalities `t=U/q`
and `Delta=q*V` are used only away from the cusp. -/
theorem cm_cusp_clearing_extension (D : ℤ) [Fact (D < 0)]
    (hD : D % 24 = 1) {U V J : ℂ → ℂ}
    (hU : AnalyticAt ℂ U 0) (hV : AnalyticAt ℂ V 0)
    (hJ : AnalyticAt ℂ J 0) (hU0 : U 0 = 1) (hV0 : V 0 = 1) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F 0 ∧ F 0 = J 0 ∧
      ∀ q : ℂ, q ≠ 0 → F q =
        ((cmClassPolynomialA D).eval (U q / q) *
          (cmClassPolynomialB D).eval (U q / q)) ^ 2 *
            (q * V q) ^ (8 * formClassNumber D) * J q := by
  refine ⟨fun q => cmAnalyticCuspClearingFactor D U V q * J q,
    (analyticAt_cmAnalyticCuspClearingFactor D hU hV).mul hJ, ?_, ?_⟩
  · dsimp only
    rw [cmAnalyticCuspClearingFactor_zero D hU0 hV0, one_mul]
  · intro q hq
    dsimp only
    rw [cmAnalyticCuspClearingFactor_eq D hD U V hq]

end SptClassification
