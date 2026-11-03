/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.CMFormalProduct
public import SptClassification.ModularForms.IntegralShimuraLambert
public import Mathlib.RingTheory.LaurentSeries

/-!
# The pole-cleared CM Shimura expansion at infinity

The actual oriented CM polynomials have degree `2h(-d)`. Their homogeneous
evaluations are the integral cusp expressions `q^(2h) A_d(t)` and
`q^(2h) B_d(t)`. The normalized discriminant has expansion
`q * etaEulerSeries 1 ^ 24`. Thus the two squared CM evaluations contribute
`q^(-8h)`, exactly canceled by `Delta^(8h)`. The independent integral
Shimura divisor row then gives an integral power series for the cleared
expression at infinity. This does not assert regularity on the whole
good-reduction curve. [rolenManuscript, Section 4, proof of Proposition 4.1]
-/

public section

namespace SptClassification

open PowerSeries

/-- The integral unit part of the normalized discriminant
`Delta=q*prod_{n≥1}(1-q^n)^24`. -/
noncomputable def cmDiscriminantEulerUnit : PowerSeries CMFormalCoefficientRing :=
  PowerSeries.map (algebraMap ℤ CMFormalCoefficientRing) (etaEulerSeries 1 ^ 24)

/-- The integral Shimura row transported to the coefficient ring of the
oriented CM polynomials. -/
noncomputable def cmIntegralShimuraCuspSeries (d : ℕ) :
    PowerSeries CMFormalCoefficientRing :=
  PowerSeries.map (algebraMap ℤ CMFormalCoefficientRing)
    (integralPrincipalShimuraLambertSeries d)

/-- Homogenizing at the width-one cusp puts the leading coefficient of a
polynomial in degree zero. -/
theorem cmPolynomialHomogenizationAtCusp_constantCoeff
    (P : Polynomial CMFormalCoefficientRing) :
    PowerSeries.constantCoeff (cmPolynomialHomogenizationAtCusp P) =
      P.leadingCoeff := by
  rw [← cmReversedPolynomialEval_mul_eulerUnit_pow,
    map_mul, map_pow, cmReversedPolynomialEval_constantCoeff]
  have hU : PowerSeries.constantCoeff
      (PowerSeries.map (algebraMap ℤ CMFormalCoefficientRing)
        levelSixFormalEulerUnit) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply,
      levelSixFormalEulerUnit_constantCoeff, map_one]
  rw [hU]
  simp

/-- The independently specified integral Shimura row reduces to the actual
principal characteristic-`p` Lambert series. This is the coefficient part of
the cusp comparison in [rolenManuscript, Section 4, equation (J)]. -/
theorem cmIntegralShimuraCuspSeries_reduction
    (p d : ℕ) [Fact p.Prime] (hp6 : ¬p ∣ 6) :
    PowerSeries.map (cmCoefficientReduction p hp6)
        (cmIntegralShimuraCuspSeries d) =
      QSeries.principalShimuraLambertSeries p d := by
  calc
    PowerSeries.map (cmCoefficientReduction p hp6)
        (cmIntegralShimuraCuspSeries d) =
        PowerSeries.map (Int.castRingHom (ZMod p))
          (integralPrincipalShimuraLambertSeries d) := by
          ext n
          simp [cmIntegralShimuraCuspSeries, PowerSeries.coeff_map]
    _ = QSeries.principalShimuraLambertSeries p d :=
      integralPrincipalShimuraLambertSeries_map_eq_principal p d

/-- The Fourier series obtained after clearing the `8h(-d)` poles at the
infinity cusp by the actual oriented CM factors and `Delta^(8h)`.
The degree equations for the two factors are proved by
`IntegralCMClassPolynomials.degreeA` and `.degreeB`. -/
noncomputable def cmPoleClearedShimuraCuspSeries (d : ℕ)
    [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) : PowerSeries CMFormalCoefficientRing :=
  let models := integralCMClassPolynomials d hd hsq hmod
  (cmPolynomialHomogenizationAtCusp models.modelA *
      cmPolynomialHomogenizationAtCusp models.modelB) ^ 2 *
    cmDiscriminantEulerUnit ^ (8 * formClassNumber (-(d : ℤ))) *
      cmIntegralShimuraCuspSeries d

/-- After the Laurent shift has been canceled, the factor multiplying the
Shimura row is a unit at infinity. It retains both actual oriented CM
polynomials and the normalized discriminant. -/
noncomputable def cmShimuraCuspClearingUnit (d : ℕ)
    [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) : PowerSeries CMFormalCoefficientRing :=
  let models := integralCMClassPolynomials d hd hsq hmod
  (cmPolynomialHomogenizationAtCusp models.modelA *
      cmPolynomialHomogenizationAtCusp models.modelB) ^ 2 *
    cmDiscriminantEulerUnit ^ (8 * formClassNumber (-(d : ℤ)))

/-- The pole-clearing factor has constant coefficient one because the two
oriented CM class polynomials are monic and `Delta/q` starts with one. -/
theorem cmShimuraCuspClearingUnit_constantCoeff (d : ℕ)
    [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) :
    PowerSeries.constantCoeff
      (cmShimuraCuspClearingUnit d hd hsq hmod) = 1 := by
  let models := integralCMClassPolynomials d hd hsq hmod
  simp only [cmShimuraCuspClearingUnit, map_mul, map_pow,
    cmPolynomialHomogenizationAtCusp_constantCoeff]
  rw [models.monicA, models.monicB]
  have hdelta : PowerSeries.constantCoeff cmDiscriminantEulerUnit = 1 := by
    have heta : PowerSeries.constantCoeff
        (PowerSeries.map (algebraMap ℤ CMFormalCoefficientRing)
          (etaEulerSeries 1)) = 1 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff_apply,
        etaEulerSeries_constantCoeff, map_one]
    simp [cmDiscriminantEulerUnit, map_pow, heta]
  simp [hdelta]

/-- The cleared cusp expression is the integral Shimura row times a unit.
In particular its zero constant term is retained, and clearing does not
erase the independent weight-four Fourier data. -/
theorem cmPoleClearedShimuraCuspSeries_eq_unit_mul (d : ℕ)
    [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) :
    cmPoleClearedShimuraCuspSeries d hd hsq hmod =
      cmShimuraCuspClearingUnit d hd hsq hmod *
        cmIntegralShimuraCuspSeries d := by
  rfl

theorem cmPoleClearedShimuraCuspSeries_constantCoeff (d : ℕ)
    [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) :
    PowerSeries.constantCoeff
      (cmPoleClearedShimuraCuspSeries d hd hsq hmod) = 0 := by
  rw [cmPoleClearedShimuraCuspSeries_eq_unit_mul, map_mul,
    cmShimuraCuspClearingUnit_constantCoeff]
  have hzero : PowerSeries.constantCoeff (cmIntegralShimuraCuspSeries d) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      cmIntegralShimuraCuspSeries, PowerSeries.coeff_map,
      integralPrincipalShimuraLambertSeries_coeff_zero, map_zero]
  simp [hzero]

/-- The actual pole-clearing factor is invertible at infinity. Therefore an
independently obtained integral Shimura series is determined by its cleared
cusp expansion. This is the local uniqueness step needed when comparing an
integral lift with the prescribed [liZemel2018, Theorem 5.1] row. -/
theorem cmShimuraCuspSeries_eq_of_cleared (d : ℕ)
    [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) (f : PowerSeries CMFormalCoefficientRing)
    (hclear : cmShimuraCuspClearingUnit d hd hsq hmod * f =
      cmPoleClearedShimuraCuspSeries d hd hsq hmod) :
    f = cmIntegralShimuraCuspSeries d := by
  let U := cmShimuraCuspClearingUnit d hd hsq hmod
  have hU : PowerSeries.constantCoeff U = 1 :=
    cmShimuraCuspClearingUnit_constantCoeff d hd hsq hmod
  have hunit : U.invOfUnit 1 * U = 1 := by
    rw [mul_comm]
    exact PowerSeries.mul_invOfUnit U 1 hU
  calc
    f = (U.invOfUnit 1 * U) * f := by rw [hunit, one_mul]
    _ = U.invOfUnit 1 * (U * f) := by rw [mul_assoc]
    _ = U.invOfUnit 1 *
        cmPoleClearedShimuraCuspSeries d hd hsq hmod := by rw [hclear]
    _ = U.invOfUnit 1 *
        (U * cmIntegralShimuraCuspSeries d) := by
          rw [cmPoleClearedShimuraCuspSeries_eq_unit_mul]
    _ = cmIntegralShimuraCuspSeries d := by rw [← mul_assoc, hunit, one_mul]

/-- Once the cleared cusp expansion of an independently constructed integral
lift is identified, its reduction has exactly the principal characteristic-
`p` Shimura row. The claim concerns the expansion; global good-reduction
regularity still requires the integral geometric model. -/
theorem cmShimuraCuspSeries_reduction_of_cleared
    (p d : ℕ) [Fact p.Prime] [Fact (-(d : ℤ) < 0)]
    (hp6 : ¬p ∣ 6) (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) (f : PowerSeries CMFormalCoefficientRing)
    (hclear : cmShimuraCuspClearingUnit d hd hsq hmod * f =
      cmPoleClearedShimuraCuspSeries d hd hsq hmod) :
    PowerSeries.map (cmCoefficientReduction p hp6) f =
      QSeries.principalShimuraLambertSeries p d := by
  rw [cmShimuraCuspSeries_eq_of_cleared d hd hsq hmod f hclear]
  exact cmIntegralShimuraCuspSeries_reduction p d hp6

/-- The independently prescribed Shimura row survives reduction after the
actual CM and discriminant factors are applied. This equality is local at
the infinity cusp; the geometric pole-clearing assertion is separate.
[rolenManuscript, Section 4, proof of Proposition 4.1] -/
theorem cmPoleClearedShimuraCuspSeries_reduction (p d : ℕ)
    [Fact p.Prime] [Fact (-(d : ℤ) < 0)]
    (hp6 : ¬p ∣ 6) (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) :
    PowerSeries.map (cmCoefficientReduction p hp6)
        (cmPoleClearedShimuraCuspSeries d hd hsq hmod) =
      PowerSeries.map (cmCoefficientReduction p hp6)
          (cmShimuraCuspClearingUnit d hd hsq hmod) *
        QSeries.principalShimuraLambertSeries p d := by
  rw [cmPoleClearedShimuraCuspSeries_eq_unit_mul, map_mul,
    cmIntegralShimuraCuspSeries_reduction p d hp6]

/-- Differentiating the actual pole-cleared infinity expansion separates the
derivative of its CM/discriminant factor from the derivative of the
independent Shimura row. This is the local Leibniz step used before the
weight-four Serre comparison. [rolenManuscript, Section 4, equations (J)
and (differential)] -/
theorem cmPoleClearedShimuraCuspSeries_eulerDerivative (d : ℕ)
    [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) :
    QSeries.eulerDerivative (cmPoleClearedShimuraCuspSeries d hd hsq hmod) =
      QSeries.eulerDerivative (cmShimuraCuspClearingUnit d hd hsq hmod) *
        cmIntegralShimuraCuspSeries d +
      cmShimuraCuspClearingUnit d hd hsq hmod *
        QSeries.eulerDerivative (cmIntegralShimuraCuspSeries d) := by
  rw [cmPoleClearedShimuraCuspSeries_eq_unit_mul,
    QSeries.eulerDerivative_mul]

/-- The derivative of the reduced cleared expression retains both the
actual CM/discriminant clearing factor and the independent principal
Shimura row. Thus clearing and reduction commute with the differential
calculation; global regularity is a separate geometric input.
[rolenManuscript, Section 4, proof of Proposition 4.1] -/
theorem cmPoleClearedShimuraCuspSeries_eulerDerivative_reduction
    (p d : ℕ) [Fact p.Prime] [Fact (-(d : ℤ) < 0)]
    (hp6 : ¬p ∣ 6) (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) :
    PowerSeries.map (cmCoefficientReduction p hp6)
      (QSeries.eulerDerivative (cmPoleClearedShimuraCuspSeries d hd hsq hmod)) =
      QSeries.eulerDerivative
          (PowerSeries.map (cmCoefficientReduction p hp6)
            (cmShimuraCuspClearingUnit d hd hsq hmod)) *
        QSeries.principalShimuraLambertSeries p d +
      PowerSeries.map (cmCoefficientReduction p hp6)
          (cmShimuraCuspClearingUnit d hd hsq hmod) *
        QSeries.eulerDerivative (QSeries.principalShimuraLambertSeries p d) := by
  rw [cmPoleClearedShimuraCuspSeries_eulerDerivative, map_add, map_mul,
    map_mul, ← QSeries.eulerDerivative_map,
    cmIntegralShimuraCuspSeries_reduction p d hp6,
    ← QSeries.eulerDerivative_map,
    cmIntegralShimuraCuspSeries_reduction p d hp6]

/-- A characteristic-`p` Shimura expansion is determined by its cleared
cusp series. The clearing factor is a unit at infinity, so this local
comparison needs no new modular-form premise. -/
theorem cmReducedShimuraCuspSeries_eq_of_cleared
    (p d : ℕ) [Fact p.Prime] [Fact (-(d : ℤ) < 0)]
    (hp6 : ¬p ∣ 6) (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) (f : PowerSeries (ZMod p))
    (hclear : PowerSeries.map (cmCoefficientReduction p hp6)
        (cmShimuraCuspClearingUnit d hd hsq hmod) * f =
      PowerSeries.map (cmCoefficientReduction p hp6)
        (cmPoleClearedShimuraCuspSeries d hd hsq hmod)) :
    f = QSeries.principalShimuraLambertSeries p d := by
  let U := PowerSeries.map (cmCoefficientReduction p hp6)
    (cmShimuraCuspClearingUnit d hd hsq hmod)
  have hU : PowerSeries.constantCoeff U = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      cmShimuraCuspClearingUnit_constantCoeff, map_one]
  have hunit : U.invOfUnit 1 * U = 1 := by
    rw [mul_comm]
    exact PowerSeries.mul_invOfUnit U 1 hU
  have hcleared : U * f =
      U * QSeries.principalShimuraLambertSeries p d := by
    rw [hclear, cmPoleClearedShimuraCuspSeries_reduction p d hp6 hd hsq hmod]
  calc
    f = (U.invOfUnit 1 * U) * f := by rw [hunit, one_mul]
    _ = U.invOfUnit 1 * (U * f) := by rw [mul_assoc]
    _ = U.invOfUnit 1 *
        (U * QSeries.principalShimuraLambertSeries p d) := by rw [hcleared]
    _ = QSeries.principalShimuraLambertSeries p d := by
      rw [← mul_assoc, hunit, one_mul]

/-- An exponent shift of a power-series product is the product of the
correspondingly shifted Laurent series. -/
theorem cmLaurentShift_mul {R : Type*} [CommRing R]
    (a b : ℤ) (f g : PowerSeries R) :
    (HahnSeries.single a 1 * HahnSeries.ofPowerSeries ℤ R f : LaurentSeries R) *
      (HahnSeries.single b 1 * HahnSeries.ofPowerSeries ℤ R g) =
    HahnSeries.single (a + b) 1 * HahnSeries.ofPowerSeries ℤ R (f * g) := by
  rw [map_mul]
  calc
    (HahnSeries.single a 1 * HahnSeries.ofPowerSeries ℤ R f) *
        (HahnSeries.single b 1 * HahnSeries.ofPowerSeries ℤ R g) =
      (HahnSeries.single a 1 * HahnSeries.single b 1) *
        (HahnSeries.ofPowerSeries ℤ R f * HahnSeries.ofPowerSeries ℤ R g) := by ring
    _ = HahnSeries.single (a + b) 1 *
        (HahnSeries.ofPowerSeries ℤ R f * HahnSeries.ofPowerSeries ℤ R g) := by
      rw [HahnSeries.single_mul_single, mul_one]

/-- A shifted cusp series raised to a power has the corresponding total
exponent shift. -/
theorem cmLaurentShift_pow {R : Type*} [CommRing R]
    (a : ℤ) (f : PowerSeries R) (n : ℕ) :
    (HahnSeries.single a 1 * HahnSeries.ofPowerSeries ℤ R f : LaurentSeries R) ^ n =
      HahnSeries.single ((n : ℤ) * a) 1 *
        HahnSeries.ofPowerSeries ℤ R (f ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, pow_succ, cmLaurentShift_mul]
      congr 1
      push_cast
      ring_nf

/-- Formal Laurent expression of one oriented polynomial at the infinity
cusp. Its shift is its actual monic degree; the integral power series is the
homogeneous evaluation `q^degree(P) P(t)`. -/
noncomputable def cmPolynomialLaurentCuspExpression
    (P : Polynomial CMFormalCoefficientRing) : LaurentSeries CMFormalCoefficientRing :=
  HahnSeries.single (-(P.natDegree : ℤ)) 1 *
    HahnSeries.ofPowerSeries ℤ CMFormalCoefficientRing
      (cmPolynomialHomogenizationAtCusp P)

/-- The normalized discriminant in the same Laurent parameter. -/
noncomputable def cmDiscriminantLaurentCuspExpression :
    LaurentSeries CMFormalCoefficientRing :=
  HahnSeries.single 1 1 *
    HahnSeries.ofPowerSeries ℤ CMFormalCoefficientRing cmDiscriminantEulerUnit

/-- The product's two squared poles cancel exactly with the prescribed
discriminant power. The right side is an integral power series, with no
negative Laurent coefficients. This is the infinity-cusp part of the
manuscript's pole-clearing calculation. -/
theorem cmPoleClearedShimuraCusp_laurent_eq (d : ℕ)
    [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) :
    let models := integralCMClassPolynomials d hd hsq hmod
    (cmPolynomialLaurentCuspExpression models.modelA *
      cmPolynomialLaurentCuspExpression models.modelB) ^ 2 *
      cmDiscriminantLaurentCuspExpression ^
        (8 * formClassNumber (-(d : ℤ))) *
      HahnSeries.ofPowerSeries ℤ CMFormalCoefficientRing
        (cmIntegralShimuraCuspSeries d) =
      HahnSeries.ofPowerSeries ℤ CMFormalCoefficientRing
        (cmPoleClearedShimuraCuspSeries d hd hsq hmod) := by
  let models := integralCMClassPolynomials d hd hsq hmod
  let h := formClassNumber (-(d : ℤ))
  have hA : models.modelA.natDegree = 2 * h := models.degreeA hmod
  have hB : models.modelB.natDegree = 2 * h := models.degreeB hmod
  dsimp only
  rw [cmPolynomialLaurentCuspExpression,
    cmPolynomialLaurentCuspExpression,
    cmDiscriminantLaurentCuspExpression]
  rw [cmLaurentShift_mul, cmLaurentShift_pow, cmLaurentShift_pow,
    cmLaurentShift_mul]
  have hshift : ((2 : ℤ) * (-((2 * h : ℕ) : ℤ) + -((2 * h : ℕ) : ℤ))) +
      ((8 * h : ℕ) : ℤ) * 1 = 0 := by
    push_cast
    ring
  dsimp [models, h] at hA hB hshift
  rw [hA, hB]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  rw [hshift]
  simp only [HahnSeries.single_zero_one, one_mul]
  rw [← map_mul]
  rfl

end SptClassification
