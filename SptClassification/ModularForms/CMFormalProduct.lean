/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.EtaQuotientExpansionIntegral
public import SptClassification.ModularForms.PrincipalForms
public import SptClassification.QuadraticForms.IntegralClassPolynomials
public import SptClassification.QSeries.ConditionalLambert
public import SptClassification.QSeries.EulerProductLogarithmicDerivative
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# The integral formal CM quotient at infinity

The monic oriented CM polynomials are reversed before substitution into the
reciprocal eta coordinate `q / (q t)`. Thus their evaluations both begin with
one and their quotient is the formal expansion of the actual `A_d(t)/B_d(t)`.
The precise formal product identity below is [rolen2026canonical, Theorem 4.2,
(4.4), PDF pp. 6–7]; its logarithmic derivative is a separate deduction.
-/

public section

namespace SptClassification

open PowerSeries

/-- The coefficient ring for the integral CM products. -/
abbrev CMFormalCoefficientRing := Localization.Away (6 : ℤ)

/-- The formal inverse of the eta coordinate `t = U(q)/q`, namely `q/U(q)`.
The integral Euler unit `U` has constant coefficient one. -/
noncomputable def cmReciprocalEtaParameter : PowerSeries CMFormalCoefficientRing :=
  X * (PowerSeries.map (algebraMap ℤ CMFormalCoefficientRing)
    levelSixFormalEulerUnit).invOfUnit 1

/-- Reversal removes the common pole at infinity from a monic CM polynomial
before evaluating it at `1/t`. -/
noncomputable def cmReversedPolynomialEval
    (P : Polynomial CMFormalCoefficientRing) : PowerSeries CMFormalCoefficientRing :=
  P.reverse.eval₂ PowerSeries.C cmReciprocalEtaParameter

@[simp] theorem cmReciprocalEtaParameter_constantCoeff :
    constantCoeff cmReciprocalEtaParameter = 0 := by
  simp [cmReciprocalEtaParameter]

/-- The reciprocal cusp parameter is exactly `q/U(q)`, where `U=q t`.
This identity fixes the coordinate used in the reversed CM evaluations. -/
theorem cmReciprocalEtaParameter_mul_eulerUnit :
    cmReciprocalEtaParameter *
        PowerSeries.map (algebraMap ℤ CMFormalCoefficientRing)
          levelSixFormalEulerUnit = X := by
  let U : PowerSeries CMFormalCoefficientRing :=
    PowerSeries.map (algebraMap ℤ CMFormalCoefficientRing)
      levelSixFormalEulerUnit
  have hc : constantCoeff U = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp only [U, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply,
      levelSixFormalEulerUnit_constantCoeff, map_one]
  have hunit : U.invOfUnit 1 * U = 1 := by
    rw [mul_comm]
    exact PowerSeries.mul_invOfUnit U 1 hc
  change (X * U.invOfUnit 1) * U = X
  rw [mul_assoc, hunit, mul_one]

/-- Reversal puts the leading coefficient at the cusp. In particular, a
monic CM polynomial evaluates to a unit with constant coefficient one. -/
theorem cmReversedPolynomialEval_constantCoeff
    (P : Polynomial CMFormalCoefficientRing) :
    constantCoeff (cmReversedPolynomialEval P) = P.leadingCoeff := by
  unfold cmReversedPolynomialEval
  rw [Polynomial.hom_eval₂]
  simp [cmReciprocalEtaParameter_constantCoeff, Polynomial.coeff_zero_reverse]

/-- The homogeneous evaluation of an integral CM polynomial at the cusp.
If `t=U/q`, this sum is the formal expression `q^deg(P) P(t)`, with
coefficient `j` contributing `q^j U^(deg(P)-j)`. -/
noncomputable def cmPolynomialHomogenizationAtCusp
    (P : Polynomial CMFormalCoefficientRing) : PowerSeries CMFormalCoefficientRing :=
  let U := PowerSeries.map (algebraMap ℤ CMFormalCoefficientRing)
    levelSixFormalEulerUnit
  ∑ j ∈ Finset.range (P.natDegree + 1),
    PowerSeries.C (P.coeff (P.natDegree - j)) * X ^ j * U ^ (P.natDegree - j)

/-- Reversal and the reciprocal eta coordinate give the homogeneous
evaluation of the original polynomial. This makes the formal quotient the
actual CM-polynomial quotient at `t=U/q`, after cancellation of equal poles. -/
theorem cmReversedPolynomialEval_mul_eulerUnit_pow
    (P : Polynomial CMFormalCoefficientRing) :
    cmReversedPolynomialEval P *
        (PowerSeries.map (algebraMap ℤ CMFormalCoefficientRing)
          levelSixFormalEulerUnit) ^ P.natDegree =
      cmPolynomialHomogenizationAtCusp P := by
  let U : PowerSeries CMFormalCoefficientRing :=
    PowerSeries.map (algebraMap ℤ CMFormalCoefficientRing)
      levelSixFormalEulerUnit
  let B : PowerSeries CMFormalCoefficientRing := U.invOfUnit 1
  have hc : constantCoeff U = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp only [U, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply,
      levelSixFormalEulerUnit_constantCoeff, map_one]
  have hBU : B * U = 1 := by
    rw [mul_comm]
    exact PowerSeries.mul_invOfUnit U 1 hc
  have hterm (j : ℕ) (hj : j ≤ P.natDegree) :
      (X * B) ^ j * U ^ P.natDegree =
        X ^ j * U ^ (P.natDegree - j) := by
    have hsum : j + (P.natDegree - j) = P.natDegree := Nat.add_sub_of_le hj
    calc
      (X * B) ^ j * U ^ P.natDegree =
          (X * B) ^ j * (U ^ j * U ^ (P.natDegree - j)) := by
        rw [← pow_add, hsum]
      _ = X ^ j * (B * U) ^ j * U ^ (P.natDegree - j) := by
        rw [mul_pow, mul_pow]
        ring
      _ = X ^ j * U ^ (P.natDegree - j) := by rw [hBU, one_pow, mul_one]
  change P.reverse.eval₂ PowerSeries.C (X * B) * U ^ P.natDegree = _
  rw [Polynomial.eval₂_eq_sum_range' PowerSeries.C
    (Nat.lt_succ_of_le P.reverse_natDegree_le), Finset.sum_mul]
  unfold cmPolynomialHomogenizationAtCusp
  dsimp only
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ P.natDegree := by
    have := Finset.mem_range.mp hj
    omega
  rw [Polynomial.coeff_reverse, Polynomial.revAt_le hj']
  change (PowerSeries.C (P.coeff (P.natDegree - j)) * (X * B) ^ j) *
    U ^ P.natDegree = _
  rw [mul_assoc, hterm j hj']
  ring

/-- The oriented integral CM quotient, with the numerator corresponding to
orientations `1,11` and the denominator to orientations `5,7`. -/
noncomputable def cmFormalBorcherdsQuotient (d : ℕ)
    [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) : PowerSeries CMFormalCoefficientRing :=
  let models := integralCMClassPolynomials d hd hsq hmod
  cmReversedPolynomialEval models.modelA *
    (cmReversedPolynomialEval models.modelB).invOfUnit 1

/-- The exponent of the `m`th factor in the normalized product of the actual
principal form `H_d`. -/
noncomputable def cmFormalProductExponent (d m : ℕ) : ℤ :=
  characterTwelve (m : ℤ) *
    QSeries.principalHFourier d (QSeries.fFourier d) ((m : ℤ) ^ 2)

/-- The two actual oriented CM polynomials have the same degree, so their
leading powers of the eta coordinate cancel in the quotient at infinity. -/
theorem cmIntegralOrientedPolynomial_equalDegree (d : ℕ)
    [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) :
    let models := integralCMClassPolynomials d hd hsq hmod
    models.modelA.natDegree = models.modelB.natDegree := by
  let models := integralCMClassPolynomials d hd hsq hmod
  exact (models.degreeA hmod).trans (models.degreeB hmod).symm

/-- Formal-series part of [rolen2026canonical, Theorem 4.2, (4.4), PDF
pp. 6–7]. The source states this equality over a ring integral away from six
for squarefree `d ≡ 23 (mod 24)`. Both polynomials here are the actual monic
oriented CM products supplied by its Lemma 4.1, with the same eta coordinate.
This exact formal product assertion is used as an admitted premise. -/
theorem rolen_cmFormalBorcherdsProduct (d : ℕ)
    [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) :
    cmFormalBorcherdsQuotient d hd hsq hmod =
      QSeries.integerEulerProduct (R := CMFormalCoefficientRing)
        (cmFormalProductExponent d) := by
  sorry

/-- Both oriented monic products have leading coefficient one, so their
formal quotient is normalized to one at infinity. -/
theorem cmFormalBorcherdsQuotient_constantCoeff (d : ℕ)
    [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) :
    constantCoeff (cmFormalBorcherdsQuotient d hd hsq hmod) = 1 := by
  let models := integralCMClassPolynomials d hd hsq hmod
  have hA : constantCoeff (cmReversedPolynomialEval models.modelA) = 1 := by
    rw [cmReversedPolynomialEval_constantCoeff]
    exact models.monicA
  have hB : constantCoeff (cmReversedPolynomialEval models.modelB) = 1 := by
    rw [cmReversedPolynomialEval_constantCoeff]
    exact models.monicB
  change constantCoeff (cmReversedPolynomialEval models.modelA *
    (cmReversedPolynomialEval models.modelB).invOfUnit 1) = 1
  simp [hA, hB, PowerSeries.constantCoeff_invOfUnit]

/-- Clearing the unit denominator characterizes the formal expansion of the
actual oriented CM-polynomial quotient. The equal CM degrees mean that the
common pole `t ^ (2h(-d))` cancels; reversal and `q/U` remove that pole from
each polynomial before this unit-denominator equation is formed. -/
theorem cmFormalBorcherdsQuotient_mul_denominator (d : ℕ)
    [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) :
    let models := integralCMClassPolynomials d hd hsq hmod
    cmFormalBorcherdsQuotient d hd hsq hmod *
        cmReversedPolynomialEval models.modelB =
      cmReversedPolynomialEval models.modelA := by
  let models := integralCMClassPolynomials d hd hsq hmod
  have hB : constantCoeff (cmReversedPolynomialEval models.modelB) = 1 := by
    rw [cmReversedPolynomialEval_constantCoeff]
    exact models.monicB
  have hunit : cmReversedPolynomialEval models.modelB *
      (cmReversedPolynomialEval models.modelB).invOfUnit 1 = 1 :=
    PowerSeries.mul_invOfUnit _ _ hB
  change (cmReversedPolynomialEval models.modelA *
    (cmReversedPolynomialEval models.modelB).invOfUnit 1) *
      cmReversedPolynomialEval models.modelB =
    cmReversedPolynomialEval models.modelA
  calc
    _ = cmReversedPolynomialEval models.modelA *
        (cmReversedPolynomialEval models.modelB *
          (cmReversedPolynomialEval models.modelB).invOfUnit 1) := by ring
    _ = cmReversedPolynomialEval models.modelA := by rw [hunit, mul_one]

/-- Reduction preserves the unit-denominator equation of the actual oriented
CM polynomials. It supplies the algebraic polynomial relation for the reduced
formal quotient without asserting a modular-form lift or a geometric identity. -/
theorem cmFormalBorcherdsQuotient_reduced_mul_denominator
    (p d : ℕ) [Fact p.Prime] (hp6 : ¬p ∣ 6)
    [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) :
    let models := integralCMClassPolynomials d hd hsq hmod
    PowerSeries.map (cmCoefficientReduction p hp6)
        (cmFormalBorcherdsQuotient d hd hsq hmod) *
      PowerSeries.map (cmCoefficientReduction p hp6)
        (cmReversedPolynomialEval models.modelB) =
      PowerSeries.map (cmCoefficientReduction p hp6)
        (cmReversedPolynomialEval models.modelA) := by
  have h := congrArg (PowerSeries.map (cmCoefficientReduction p hp6))
    (cmFormalBorcherdsQuotient_mul_denominator d hd hsq hmod)
  simpa only [map_mul] using h

/-- The quotient satisfies the original polynomials' homogeneous equation
at the cusp. Both degrees are `2h(-d)`, so the same power of `q` clears their
poles and no extra factor appears. -/
theorem cmFormalBorcherdsQuotient_mul_homogeneous_denominator (d : ℕ)
    [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) :
    let models := integralCMClassPolynomials d hd hsq hmod
    cmFormalBorcherdsQuotient d hd hsq hmod *
        cmPolynomialHomogenizationAtCusp models.modelB =
      cmPolynomialHomogenizationAtCusp models.modelA := by
  let models := integralCMClassPolynomials d hd hsq hmod
  have hdegree : models.modelA.natDegree = models.modelB.natDegree :=
    cmIntegralOrientedPolynomial_equalDegree d hd hsq hmod
  have hquot := cmFormalBorcherdsQuotient_mul_denominator d hd hsq hmod
  change cmFormalBorcherdsQuotient d hd hsq hmod *
      cmPolynomialHomogenizationAtCusp models.modelB =
        cmPolynomialHomogenizationAtCusp models.modelA
  rw [← cmReversedPolynomialEval_mul_eulerUnit_pow,
      ← cmReversedPolynomialEval_mul_eulerUnit_pow, hdegree]
  calc
    cmFormalBorcherdsQuotient d hd hsq hmod *
        (cmReversedPolynomialEval models.modelB *
          (PowerSeries.map (algebraMap ℤ CMFormalCoefficientRing)
            levelSixFormalEulerUnit) ^ models.modelB.natDegree) =
        (cmFormalBorcherdsQuotient d hd hsq hmod *
          cmReversedPolynomialEval models.modelB) *
          (PowerSeries.map (algebraMap ℤ CMFormalCoefficientRing)
            levelSixFormalEulerUnit) ^ models.modelB.natDegree := by ring
    _ = cmReversedPolynomialEval models.modelA *
          (PowerSeries.map (algebraMap ℤ CMFormalCoefficientRing)
            levelSixFormalEulerUnit) ^ models.modelB.natDegree := by rw [hquot]

/-- The formal product has the unit-denominator equation of the actual
oriented CM quotient. This records the numerator and denominator orientation
independently of logarithmic differentiation. -/
theorem cmFormalBorcherdsProduct_mul_denominator (d : ℕ)
    [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) :
    let models := integralCMClassPolynomials d hd hsq hmod
    QSeries.integerEulerProduct (R := CMFormalCoefficientRing)
        (cmFormalProductExponent d) *
      cmReversedPolynomialEval models.modelB =
        cmReversedPolynomialEval models.modelA := by
  rw [← rolen_cmFormalBorcherdsProduct d hd hsq hmod]
  exact cmFormalBorcherdsQuotient_mul_denominator d hd hsq hmod

/-- Rolen's formal product also satisfies the homogeneous equation of the
original oriented CM polynomials at the cusp. The common degree clears the
same power of the eta coordinate on both sides. -/
theorem cmFormalBorcherdsProduct_mul_homogeneous_denominator (d : ℕ)
    [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) :
    let models := integralCMClassPolynomials d hd hsq hmod
    QSeries.integerEulerProduct (R := CMFormalCoefficientRing)
        (cmFormalProductExponent d) *
      cmPolynomialHomogenizationAtCusp models.modelB =
        cmPolynomialHomogenizationAtCusp models.modelA := by
  rw [← rolen_cmFormalBorcherdsProduct d hd hsq hmod]
  exact cmFormalBorcherdsQuotient_mul_homogeneous_denominator d hd hsq hmod

/-- The unit-denominator equation determines the formal CM quotient uniquely. -/
theorem cmFormalBorcherdsQuotient_eq_of_mul_denominator (d : ℕ)
    [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) (F : PowerSeries CMFormalCoefficientRing)
    (hF :
      let models := integralCMClassPolynomials d hd hsq hmod
      F * cmReversedPolynomialEval models.modelB =
        cmReversedPolynomialEval models.modelA) :
    F = cmFormalBorcherdsQuotient d hd hsq hmod := by
  let models := integralCMClassPolynomials d hd hsq hmod
  have hB : constantCoeff (cmReversedPolynomialEval models.modelB) = 1 := by
    rw [cmReversedPolynomialEval_constantCoeff]
    exact models.monicB
  have hunit : cmReversedPolynomialEval models.modelB *
      (cmReversedPolynomialEval models.modelB).invOfUnit 1 = 1 :=
    PowerSeries.mul_invOfUnit _ _ hB
  change F = cmReversedPolynomialEval models.modelA *
    (cmReversedPolynomialEval models.modelB).invOfUnit 1
  calc
    F = F * (cmReversedPolynomialEval models.modelB *
        (cmReversedPolynomialEval models.modelB).invOfUnit 1) := by
      rw [hunit, mul_one]
    _ = (F * cmReversedPolynomialEval models.modelB) *
        (cmReversedPolynomialEval models.modelB).invOfUnit 1 := by ring
    _ = cmReversedPolynomialEval models.modelA *
        (cmReversedPolynomialEval models.modelB).invOfUnit 1 := by rw [hF]

/-- Logarithmic differentiation of Rolen's normalized formal product yields
the precise Lambert coefficients of the prescribed principal form. The only
literature dependency is the formal product identity above. -/
theorem cmFormalBorcherdsQuotient_logarithmicLambert (d : ℕ)
    [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) :
    QSeries.eulerDerivative (cmFormalBorcherdsQuotient d hd hsq hmod) *
        (cmFormalBorcherdsQuotient d hd hsq hmod).invOfUnit 1 =
      QSeries.logarithmicLambertSeries
        (fun r => (QSeries.principalHFourier d (QSeries.fFourier d) (r : ℤ) :
          CMFormalCoefficientRing)) := by
  rw [rolen_cmFormalBorcherdsProduct d hd hsq hmod,
    QSeries.eulerDerivative_integerEulerProduct_mul_inv]
  have hexp : cmFormalProductExponent d = fun (m : ℕ) =>
      characterTwelve (m : ℤ) *
        QSeries.principalHFourier d (QSeries.fFourier d) ((m : ℤ) ^ 2) := by
    funext m
    rfl
  rw [hexp]
  exact QSeries.integerEulerLogarithmicSeries_eq_lambert
    (R := CMFormalCoefficientRing)
    (fun r => QSeries.principalHFourier d (QSeries.fFourier d) (r : ℤ))

/-- The Lambert series is the logarithmic numerator of the actual oriented
CM polynomials in the reciprocal cusp parameter. This is the formal-series
version of the polynomial part of [rolenManuscript, equation (L)]; the
identity follows from the normalized product and the ordinary product rule. -/
theorem cmFormalBorcherdsLambert_reversedPolynomialIdentity (d : ℕ)
    [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) :
    let models := integralCMClassPolynomials d hd hsq hmod
    QSeries.logarithmicLambertSeries
        (fun r => (QSeries.principalHFourier d (QSeries.fFourier d) (r : ℤ) :
          CMFormalCoefficientRing)) *
        cmReversedPolynomialEval models.modelA *
          cmReversedPolynomialEval models.modelB =
      QSeries.eulerDerivative (cmReversedPolynomialEval models.modelA) *
          cmReversedPolynomialEval models.modelB -
        cmReversedPolynomialEval models.modelA *
          QSeries.eulerDerivative (cmReversedPolynomialEval models.modelB) := by
  let models := integralCMClassPolynomials d hd hsq hmod
  let A := cmReversedPolynomialEval models.modelA
  let B := cmReversedPolynomialEval models.modelB
  let Q := cmFormalBorcherdsQuotient d hd hsq hmod
  let L := QSeries.logarithmicLambertSeries
    (fun r => (QSeries.principalHFourier d (QSeries.fFourier d) (r : ℤ) :
      CMFormalCoefficientRing))
  have hquot : Q * B = A := cmFormalBorcherdsQuotient_mul_denominator d hd hsq hmod
  have hconstant : constantCoeff Q = 1 :=
    cmFormalBorcherdsQuotient_constantCoeff d hd hsq hmod
  have hunit : Q * Q.invOfUnit 1 = 1 :=
    PowerSeries.mul_invOfUnit Q 1 hconstant
  have hlog : QSeries.eulerDerivative Q * Q.invOfUnit 1 = L :=
    cmFormalBorcherdsQuotient_logarithmicLambert d hd hsq hmod
  have htheta : QSeries.eulerDerivative Q = Q * L := by
    calc
      QSeries.eulerDerivative Q =
          QSeries.eulerDerivative Q * (Q * Q.invOfUnit 1) := by
        rw [hunit, mul_one]
      _ = Q * (QSeries.eulerDerivative Q * Q.invOfUnit 1) := by ring
      _ = Q * L := by rw [hlog]
  have hderivative : QSeries.eulerDerivative Q * B +
      Q * QSeries.eulerDerivative B = QSeries.eulerDerivative A := by
    have h := congrArg QSeries.eulerDerivative hquot
    simpa only [QSeries.eulerDerivative_mul] using h
  have hnumerator : QSeries.eulerDerivative Q * B ^ 2 =
      QSeries.eulerDerivative A * B - A * QSeries.eulerDerivative B := by
    calc
      QSeries.eulerDerivative Q * B ^ 2 =
          (QSeries.eulerDerivative Q * B +
            Q * QSeries.eulerDerivative B) * B -
            (Q * B) * QSeries.eulerDerivative B := by ring
      _ = QSeries.eulerDerivative A * B -
            A * QSeries.eulerDerivative B := by rw [hderivative, hquot]
  change L * A * B = QSeries.eulerDerivative A * B -
    A * QSeries.eulerDerivative B
  calc
    L * A * B = (Q * L) * B ^ 2 := by rw [← hquot]; ring
    _ = QSeries.eulerDerivative Q * B ^ 2 := by rw [htheta]
    _ = QSeries.eulerDerivative A * B -
        A * QSeries.eulerDerivative B := hnumerator

/-- The logarithmic derivative of the actual oriented CM quotient has the
divisor-sum coefficients of the prescribed principal form. This includes the
zero coefficient, where the divisor sum is empty. -/
theorem coeff_cmFormalBorcherdsQuotient_logarithmicDerivative (d : ℕ)
    [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) (n : ℕ) :
    (QSeries.eulerDerivative (cmFormalBorcherdsQuotient d hd hsq hmod) *
        (cmFormalBorcherdsQuotient d hd hsq hmod).invOfUnit 1).coeff n =
      QSeries.logarithmicLambertCoeff
        (fun r => (QSeries.principalHFourier d (QSeries.fFourier d) (r : ℤ) :
          CMFormalCoefficientRing)) n := by
  rw [cmFormalBorcherdsQuotient_logarithmicLambert d hd hsq hmod]
  exact QSeries.coeff_logarithmicLambertSeries _ n

/-- Reducing the integral formal logarithmic quotient gives the exact
characteristic-`p` Lambert coefficients used for the geometric lift. This
is a coefficient statement; it does not assert existence of a modular form
with those coefficients. -/
theorem cmFormalBorcherdsQuotient_logarithmicLambert_mod
    (p d : ℕ) [Fact p.Prime] (hp6 : ¬p ∣ 6)
    [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) :
    PowerSeries.map (cmCoefficientReduction p hp6)
        (QSeries.eulerDerivative (cmFormalBorcherdsQuotient d hd hsq hmod) *
          (cmFormalBorcherdsQuotient d hd hsq hmod).invOfUnit 1) =
      QSeries.logarithmicLambertSeries
        (fun r => (QSeries.principalHFourier d (QSeries.fFourier d) (r : ℤ) :
          ZMod p)) := by
  rw [cmFormalBorcherdsQuotient_logarithmicLambert d hd hsq hmod]
  exact QSeries.map_integral_logarithmicLambertSeries
    (cmCoefficientReduction p hp6)
    (fun r => QSeries.principalHFourier d (QSeries.fFourier d) (r : ℤ))

/-- The reduction above is exactly the previously defined principal-form
Lambert series used in the conditional differential relation. -/
theorem cmFormalBorcherdsQuotient_logarithmicLambert_mod_principal
    (p d : ℕ) [Fact p.Prime] (hp6 : ¬p ∣ 6)
    [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) :
    PowerSeries.map (cmCoefficientReduction p hp6)
        (QSeries.eulerDerivative (cmFormalBorcherdsQuotient d hd hsq hmod) *
          (cmFormalBorcherdsQuotient d hd hsq hmod).invOfUnit 1) =
      QSeries.principalLogarithmicLambertSeries p d := by
  simpa only [QSeries.principalLogarithmicLambertSeries_eq] using
    cmFormalBorcherdsQuotient_logarithmicLambert_mod p d hp6 hd hsq hmod

/-- The reduced Lambert series is the logarithmic numerator of the same
reversed integral CM polynomials. This is the coefficientwise equation at the
infinity cusp in [rolenManuscript, Section 4, equations (product) and (L)]
needed before comparing the formal quotient with a weight-two lift. -/
theorem cmFormalBorcherdsLambert_reversedPolynomialIdentity_mod
    (p d : ℕ) [Fact p.Prime] (hp6 : ¬p ∣ 6)
    [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) :
    let models := integralCMClassPolynomials d hd hsq hmod
    QSeries.principalLogarithmicLambertSeries p d *
        PowerSeries.map (cmCoefficientReduction p hp6)
          (cmReversedPolynomialEval models.modelA) *
        PowerSeries.map (cmCoefficientReduction p hp6)
          (cmReversedPolynomialEval models.modelB) =
      QSeries.eulerDerivative
          (PowerSeries.map (cmCoefficientReduction p hp6)
            (cmReversedPolynomialEval models.modelA)) *
        PowerSeries.map (cmCoefficientReduction p hp6)
          (cmReversedPolynomialEval models.modelB) -
      PowerSeries.map (cmCoefficientReduction p hp6)
          (cmReversedPolynomialEval models.modelA) *
        QSeries.eulerDerivative
          (PowerSeries.map (cmCoefficientReduction p hp6)
            (cmReversedPolynomialEval models.modelB)) := by
  have h := congrArg (PowerSeries.map (cmCoefficientReduction p hp6))
    (cmFormalBorcherdsLambert_reversedPolynomialIdentity d hd hsq hmod)
  simpa only [QSeries.principalLogarithmicLambertSeries_eq, map_mul, map_sub,
    QSeries.map_integral_logarithmicLambertSeries,
    ← QSeries.eulerDerivative_map] using h

/-- Every reduced coefficient is the same finite divisor sum as the
principal Lambert series. The formula holds in degree zero and at indices
divisible by `p`, with no division by those indices. -/
theorem coeff_cmFormalBorcherdsQuotient_logarithmicDerivative_mod
    (p d : ℕ) [Fact p.Prime] (hp6 : ¬p ∣ 6)
    [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) (n : ℕ) :
    (PowerSeries.map (cmCoefficientReduction p hp6)
        (QSeries.eulerDerivative (cmFormalBorcherdsQuotient d hd hsq hmod) *
          (cmFormalBorcherdsQuotient d hd hsq hmod).invOfUnit 1)).coeff n =
      QSeries.logarithmicLambertCoeff
        (fun r => (QSeries.principalHFourier d (QSeries.fFourier d) (r : ℤ) :
          ZMod p)) n := by
  rw [cmFormalBorcherdsQuotient_logarithmicLambert_mod p d hp6 hd hsq hmod]
  exact QSeries.coeff_logarithmicLambertSeries _ n

/-- The reduced CM quotient itself has the prescribed mod-`p` Lambert
logarithmic derivative. Thus reduction commutes with forming the normalized
quotient, not merely with its already computed coefficients. -/
theorem cmFormalBorcherdsQuotient_reduced_logarithmicLambert
    (p d : ℕ) [Fact p.Prime] (hp6 : ¬p ∣ 6)
    [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) :
    QSeries.eulerDerivative
        (PowerSeries.map (cmCoefficientReduction p hp6)
          (cmFormalBorcherdsQuotient d hd hsq hmod)) *
      (PowerSeries.map (cmCoefficientReduction p hp6)
        (cmFormalBorcherdsQuotient d hd hsq hmod)).invOfUnit 1 =
      QSeries.principalLogarithmicLambertSeries p d := by
  rw [QSeries.eulerLogarithmicDerivative_map
    (cmCoefficientReduction p hp6) (cmFormalBorcherdsQuotient d hd hsq hmod)
    (cmFormalBorcherdsQuotient_constantCoeff d hd hsq hmod)]
  exact cmFormalBorcherdsQuotient_logarithmicLambert_mod_principal
    p d hp6 hd hsq hmod

/-- Rolen's integral formal product survives reduction at every prime away
from six, with the same integer exponents and oriented CM quotient. -/
theorem cmFormalBorcherdsProduct_reduced
    (p d : ℕ) [Fact p.Prime] (hp6 : ¬p ∣ 6)
    [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) :
    PowerSeries.map (cmCoefficientReduction p hp6)
        (cmFormalBorcherdsQuotient d hd hsq hmod) =
      QSeries.integerEulerProduct (R := ZMod p)
        (cmFormalProductExponent d) := by
  rw [rolen_cmFormalBorcherdsProduct d hd hsq hmod,
    QSeries.map_integerEulerProduct]

/-- The reduced product satisfies the equation obtained from the original
oriented CM polynomials. Its denominator still has constant coefficient one. -/
theorem cmFormalBorcherdsProduct_reduced_mul_denominator
    (p d : ℕ) [Fact p.Prime] (hp6 : ¬p ∣ 6)
    [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) :
    let models := integralCMClassPolynomials d hd hsq hmod
    QSeries.integerEulerProduct (R := ZMod p)
        (cmFormalProductExponent d) *
      PowerSeries.map (cmCoefficientReduction p hp6)
        (cmReversedPolynomialEval models.modelB) =
      PowerSeries.map (cmCoefficientReduction p hp6)
        (cmReversedPolynomialEval models.modelA) := by
  rw [← cmFormalBorcherdsProduct_reduced p d hp6 hd hsq hmod]
  exact cmFormalBorcherdsQuotient_reduced_mul_denominator
    p d hp6 hd hsq hmod

end SptClassification
