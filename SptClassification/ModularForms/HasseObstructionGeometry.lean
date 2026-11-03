/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.HasseObstructionForms
public import SptClassification.ModularForms.CMFormalProduct
public import SptClassification.Polynomials.SupersingularObstruction

/-!
# Lift and supersingular evaluation data for the character obstruction

The geometric coordinate is defined on interior points of the good-reduction
curve. Forms in the algebra are regular at infinity; their only possible
interior poles lie in the actual reduced CM support. Evaluation is therefore
provided only away from that support. The logarithmic identity has exactly
the normalization of [rolenManuscript, Section 4, equations (product) and
(L)]. The supersingular count and Hasse laws are explicit geometric input
as used in [rolenManuscript, Section 4].
-/

public section

namespace SptClassification

open Polynomial

namespace ConditionalCM

/-- The first actual CM model after reduction and extension to the
algebraic closure of the residue field. -/
noncomputable def CMDescentInput.geometricA {d p : ℕ}
    [Fact (-(d : ℤ) < 0)] [Fact p.Prime]
    (C : CMDescentInput d p) :
    Polynomial (AlgebraicClosure (ZMod p)) :=
  (C.modelA.map C.reduction).map
    (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))

/-- The second actual CM model under the same specialization. -/
noncomputable def CMDescentInput.geometricB {d p : ℕ}
    [Fact (-(d : ℤ) < 0)] [Fact p.Prime]
    (C : CMDescentInput d p) :
    Polynomial (AlgebraicClosure (ZMod p)) :=
  (C.modelB.map C.reduction).map
    (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))

/-- The geometric first model as its explicit base change. -/
theorem CMDescentInput.geometricA_eq {d p : ℕ}
    [Fact (-(d : ℤ) < 0)] [Fact p.Prime]
    (C : CMDescentInput d p) :
    C.geometricA = (C.modelA.map C.reduction).map
      (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) := (rfl)

/-- The geometric second model as its explicit base change. -/
theorem CMDescentInput.geometricB_eq {d p : ℕ}
    [Fact (-(d : ℤ) < 0)] [Fact p.Prime]
    (C : CMDescentInput d p) :
    C.geometricB = (C.modelB.map C.reduction).map
      (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) := (rfl)

/-- Monicity of the same first CM model over the algebraic closure. -/
theorem CMDescentInput.geometricA_monic {d p : ℕ}
    [Fact (-(d : ℤ) < 0)] [Fact p.Prime]
    (C : CMDescentInput d p) : C.geometricA.Monic := by
  exact C.reducedA_monic.map _

/-- Monicity of the same second CM model over the algebraic closure. -/
theorem CMDescentInput.geometricB_monic {d p : ℕ}
    [Fact (-(d : ℤ) < 0)] [Fact p.Prime]
    (C : CMDescentInput d p) : C.geometricB.Monic := by
  exact C.reducedB_monic.map _

/-- Exact degree of the first geometric CM model. -/
theorem CMDescentInput.geometricA_degree {d p : ℕ}
    [Fact (-(d : ℤ) < 0)] [Fact p.Prime]
    (C : CMDescentInput d p) (hmod : d % 24 = 23) :
    C.geometricA.natDegree = 2 * formClassNumber (-(d : ℤ)) := by
  exact (C.reducedA_monic.natDegree_map _).trans (C.reducedA_degree hmod)

/-- Exact degree of the second geometric CM model. -/
theorem CMDescentInput.geometricB_degree {d p : ℕ}
    [Fact (-(d : ℤ) < 0)] [Fact p.Prime]
    (C : CMDescentInput d p) (hmod : d % 24 = 23) :
    C.geometricB.natDegree = 2 * formClassNumber (-(d : ℤ)) := by
  exact (C.reducedB_monic.natDegree_map _).trans (C.reducedB_degree hmod)

/-- Conditional separation remains coprimality after scalar extension. -/
theorem CMDescentInput.geometric_coprime {d p : ℕ}
    [Fact (-(d : ℤ) < 0)] [Fact p.Prime]
    (C : CMDescentInput d p)
    (hd : 0 < d) (hsq : Squarefree d) (hmod : d % 24 = 23)
    (hp : 5 ≤ p) (hcop : ¬p ∣ 6 * d)
    (hbound : (d + 1) ^ 2 < 24 * p) :
    IsCoprime C.geometricA C.geometricB := by
  exact (conditional_cm_separation d p hd hsq hmod hp hcop hbound C).map
    (Polynomial.mapRingHom
      (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))

end ConditionalCM

/-- The pointwise quotient rule needed for the CM logarithmic lift. The
relations are ordinary product and coordinate derivative laws; the desired
Wronskian quotient is derived from them. -/
theorem logarithmic_value_of_quotient_derivative
    {K : Type*} [Field K]
    (a b a' b' q qinv dq da db theta L : K)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hquotient : q * b = a) (hinverse : q * qinv = 1)
    (hproduct : dq * b + q * db = da)
    (hda : da = theta * a') (hdb : db = theta * b')
    (hL : L = dq * qinv) :
    L = theta * (a' * b - a * b') / (a * b) := by
  have hqinv : qinv * a = b := by
    calc
      qinv * a = qinv * (q * b) := by rw [hquotient]
      _ = (q * qinv) * b := by ring
      _ = b := by rw [hinverse]; ring
  have hderiv : dq * b * b = da * b - a * db := by
    calc
      dq * b * b = (dq * b + q * db) * b - (q * b) * db := by ring
      _ = da * b - a * db := by rw [hproduct, hquotient]
  apply (eq_div_iff (mul_ne_zero ha hb)).2
  rw [hL]
  calc
    dq * qinv * (a * b) = dq * b * b := by rw [← hqinv]; ring
    _ = da * b - a * db := hderiv
    _ = theta * (a' * b - a * b') := by rw [hda, hdb]; ring

/-- A shared section factor and the common Serre connection term cancel in
the logarithmic derivative of an oriented quotient. -/
theorem logarithmic_value_of_equal_weight_sections
    {K : Type*} [Field K]
    (a b a' b' u connection q qinv dq da db theta L : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hu : u ≠ 0)
    (hquotient : q * (u * b) = u * a) (hinverse : q * qinv = 1)
    (hproduct : dq * (u * b) + q * db = da)
    (hda : da = u * theta * a' + connection * a)
    (hdb : db = u * theta * b' + connection * b)
    (hL : L = dq * qinv) :
    L = theta * (a' * b - a * b') / (a * b) := by
  have hs := logarithmic_value_of_quotient_derivative
    (u * a) (u * b)
    (u * theta * a' + connection * a)
    (u * theta * b' + connection * b)
    q qinv dq da db 1 L
    (mul_ne_zero hu ha) (mul_ne_zero hu hb)
    hquotient hinverse hproduct
    (by rw [hda]; ring) (by rw [hdb]; ring) hL
  rw [one_mul] at hs
  rw [hs]
  field_simp
  ring

/-- Shared good-reduction Hasse geometry. `X` is the interior of the
good-reduction curve, and coordinate is its injective affine coordinate.
The points are the distinct supersingular points. Algebra evaluation maps
exist off the reduced support of the same CM descent models used by
conditional separation. The theta coordinate is its Kodaira--Spencer
derivative. No logarithmic comparison or Wronskian-root conclusion is an input. -/
structure LiftHasseGeometry (p d : ℕ) [Fact p.Prime]
    [Fact (-(d : ℤ) < 0)]
    (C : ConditionalCM.CMDescentInput d p)
    (F X : Type*) [CommRing F] [Algebra (ZMod p) F] where
  forms : HomogeneousHasseInput p d F
  points : Finset X
  points_card : points.card = p - 1
  coordinate : X ↪ AlgebraicClosure (ZMod p)
  theta_coordinate : X → AlgebraicClosure (ZMod p)
  theta_coordinate_ne_zero : ∀ x : X, theta_coordinate x ≠ 0
  evaluate : ∀ (x : X),
    ¬(C.geometricA).IsRoot (coordinate x) →
    ¬(C.geometricB).IsRoot (coordinate x) →
    F →ₐ[ZMod p] AlgebraicClosure (ZMod p)
  hasse_zero : ∀ (x : X) (_hx : x ∈ points) ha hb,
    evaluate x ha hb forms.H = 0
  /-- Katz's simple-zero property, expressed through the Serre derivative of
  the Hasse invariant at a supersingular point. The manuscript's nonvanishing
  of `E` follows from `E_eq_serre_H` since the characteristic is at least five.
  [katz1973, Sections 2 and 4.3] -/
  serre_H_ne_zero : ∀ (x : X) (_hx : x ∈ points) ha hb,
    evaluate x ha hb (forms.serre (p - 1) forms.H) ≠ 0

/-- The previously used conditional lift: the CM quotient comparison is
kept explicit until it is obtained from the actual quotient construction. -/
structure LiftHasseInput (p d : ℕ) [Fact p.Prime]
    [Fact (-(d : ℤ) < 0)]
    (C : ConditionalCM.CMDescentInput d p)
    (F X : Type*) [CommRing F] [Algebra (ZMod p) F]
    extends LiftHasseGeometry p d C F X where
  L : F
  L_form : L ∈ forms.forms 2
  L_qexp : forms.qexp L = QSeries.principalLogarithmicLambertSeries p d
  logarithmic_identity : ∀ (x : X) ha hb,
    evaluate x ha hb L =
      theta_coordinate x *
        ((C.geometricA).derivative * C.geometricB -
          C.geometricA * (C.geometricB).derivative).eval (coordinate x) /
        ((C.geometricA).eval (coordinate x) *
          (C.geometricB).eval (coordinate x))

/-- A quotient presentation of the actual reduced CM logarithmic lift. The
four elements represent the same oriented numerator and denominator, their
quotient, and its inverse in the algebra of forms regular at infinity. The
Leibniz and coordinate derivative laws are good-reduction geometry inputs;
the CM-specific logarithmic evaluation is proved below. -/
structure CMQuotientLiftData (p d : ℕ) [Fact p.Prime]
    [Fact (-(d : ℤ) < 0)]
    (C : ConditionalCM.CMDescentInput d p)
    (F X : Type*) [CommRing F] [Algebra (ZMod p) F] where
  geometry : LiftHasseGeometry p d C F X
  sectionWeight : ℕ
  numerator : F
  denominator : F
  quotient : F
  quotientInverse : F
  hp6 : ¬p ∣ 6
  hd : 0 < d
  hsq : Squarefree d
  hmod : d % 24 = 23
  /-- The descent input and cusp expansion use the same first oriented model. -/
  modelA_eq : C.modelA =
    (integralCMClassPolynomials d hd hsq hmod).modelA
  /-- The descent input and cusp expansion use the same second oriented model. -/
  modelB_eq : C.modelB =
    (integralCMClassPolynomials d hd hsq hmod).modelB
  reduction_eq : C.reduction = cmCoefficientReduction p hp6
  quotient_mul_denominator : quotient * denominator = numerator
  quotient_mul_inverse : quotient * quotientInverse = 1
  numerator_form : numerator ∈ geometry.forms.forms sectionWeight
  denominator_form : denominator ∈ geometry.forms.forms sectionWeight
  quotient_form : quotient ∈ geometry.forms.forms 0
  quotientInverse_form : quotientInverse ∈ geometry.forms.forms 0
  numerator_qexp : geometry.forms.qexp numerator =
    PowerSeries.map C.reduction (cmReversedPolynomialEval C.modelA)
  denominator_qexp : geometry.forms.qexp denominator =
    PowerSeries.map C.reduction (cmReversedPolynomialEval C.modelB)
  serre_product : geometry.forms.serre sectionWeight (quotient * denominator) =
    geometry.forms.serre 0 quotient * denominator +
      quotient * geometry.forms.serre sectionWeight denominator
  sectionFactor : X → AlgebraicClosure (ZMod p)
  sectionFactor_ne_zero : ∀ x : X, sectionFactor x ≠ 0
  serreConnection : X → AlgebraicClosure (ZMod p)
  evaluate_numerator : ∀ (x : X) ha hb,
    geometry.evaluate x ha hb numerator =
      sectionFactor x * C.geometricA.eval (geometry.coordinate x)
  evaluate_denominator : ∀ (x : X) ha hb,
    geometry.evaluate x ha hb denominator =
      sectionFactor x * C.geometricB.eval (geometry.coordinate x)
  evaluate_derivative_numerator : ∀ (x : X) ha hb,
    geometry.evaluate x ha hb (geometry.forms.serre sectionWeight numerator) =
      sectionFactor x * geometry.theta_coordinate x *
        C.geometricA.derivative.eval (geometry.coordinate x) +
      serreConnection x * C.geometricA.eval (geometry.coordinate x)
  evaluate_derivative_denominator : ∀ (x : X) ha hb,
    geometry.evaluate x ha hb (geometry.forms.serre sectionWeight denominator) =
      sectionFactor x * geometry.theta_coordinate x *
        C.geometricB.derivative.eval (geometry.coordinate x) +
      serreConnection x * C.geometricB.eval (geometry.coordinate x)

/-- The first geometric divisor is the reduction of the first polynomial
whose reversed series occurs at the cusp. -/
theorem CMQuotientLiftData.geometricA_eq_integral
    {p d : ℕ} [Fact p.Prime] [Fact (-(d : ℤ) < 0)]
    {F X : Type*} [CommRing F] [Algebra (ZMod p) F]
    {C : ConditionalCM.CMDescentInput d p}
    (I : CMQuotientLiftData p d C F X) :
    C.geometricA =
      ((integralCMClassPolynomials d I.hd I.hsq I.hmod).modelA.map
        (cmCoefficientReduction p I.hp6)).map
          (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) := by
  rw [C.geometricA_eq, I.modelA_eq, I.reduction_eq]

/-- The second geometric divisor is the reduction of the denominator
polynomial whose reversed series occurs at the cusp. -/
theorem CMQuotientLiftData.geometricB_eq_integral
    {p d : ℕ} [Fact p.Prime] [Fact (-(d : ℤ) < 0)]
    {F X : Type*} [CommRing F] [Algebra (ZMod p) F]
    {C : ConditionalCM.CMDescentInput d p}
    (I : CMQuotientLiftData p d C F X) :
    C.geometricB =
      ((integralCMClassPolynomials d I.hd I.hsq I.hmod).modelB.map
        (cmCoefficientReduction p I.hp6)).map
          (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) := by
  rw [C.geometricB_eq, I.modelB_eq, I.reduction_eq]

/-- The separate oriented section expansions determine the quotient
expansion. The denominator is a unit at infinity because its CM polynomial
is monic; the reduced formal-product equation fixes the orientation.
[rolenManuscript, Section 4, equation (product)] -/
theorem CMQuotientLiftData.quotient_qexp
    {p d : ℕ} [Fact p.Prime] [Fact (-(d : ℤ) < 0)]
    {F X : Type*} [CommRing F] [Algebra (ZMod p) F]
    {C : ConditionalCM.CMDescentInput d p}
    (I : CMQuotientLiftData p d C F X) :
    I.geometry.forms.qexp I.quotient =
      PowerSeries.map (cmCoefficientReduction p I.hp6)
        (cmFormalBorcherdsQuotient d I.hd I.hsq I.hmod) := by
  let models := integralCMClassPolynomials d I.hd I.hsq I.hmod
  let A := PowerSeries.map (cmCoefficientReduction p I.hp6)
    (cmReversedPolynomialEval models.modelA)
  let B := PowerSeries.map (cmCoefficientReduction p I.hp6)
    (cmReversedPolynomialEval models.modelB)
  let Q := PowerSeries.map (cmCoefficientReduction p I.hp6)
    (cmFormalBorcherdsQuotient d I.hd I.hsq I.hmod)
  have hB : PowerSeries.constantCoeff B = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp only [B, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply,
      cmReversedPolynomialEval_constantCoeff]
    have hmonic : models.modelB.leadingCoeff = 1 := models.monicB
    rw [hmonic, map_one]
  have hunit : B * B.invOfUnit 1 = 1 :=
    PowerSeries.mul_invOfUnit B 1 hB
  have hsection : I.geometry.forms.qexp I.quotient * B = A := by
    have h := congrArg I.geometry.forms.qexp I.quotient_mul_denominator
    simpa only [map_mul, I.numerator_qexp, I.denominator_qexp,
      I.modelA_eq, I.modelB_eq, I.reduction_eq, A, B, models]
      using h
  have hformal : Q * B = A := by
    exact cmFormalBorcherdsQuotient_reduced_mul_denominator
      p d I.hp6 I.hd I.hsq I.hmod
  calc
    I.geometry.forms.qexp I.quotient =
        I.geometry.forms.qexp I.quotient * (B * B.invOfUnit 1) := by
      rw [hunit, mul_one]
    _ = A * B.invOfUnit 1 := by rw [← mul_assoc, hsection]
    _ = (Q * B) * B.invOfUnit 1 := by rw [hformal]
    _ = Q := by rw [mul_assoc, hunit, mul_one]

/-- Construct the weight-two logarithmic form from the actual oriented CM
quotient. The quotient inverse and the weight-zero Serre derivative are the
meromorphic logarithmic derivative. [rolenManuscript, Section 4, (L)] -/
def CMQuotientLiftData.constructedLogarithmicForm
    {p d : ℕ} [Fact p.Prime] [Fact (-(d : ℤ) < 0)]
    {F X : Type*} [CommRing F] [Algebra (ZMod p) F]
    {C : ConditionalCM.CMDescentInput d p}
    (I : CMQuotientLiftData p d C F X) : F :=
  I.geometry.forms.serre 0 I.quotient * I.quotientInverse

/-- The constructed logarithmic form has weight two and the prescribed CM
pole clearing because the two factors have weights two and zero. -/
theorem CMQuotientLiftData.constructedLogarithmicForm_form
    {p d : ℕ} [Fact p.Prime] [Fact (-(d : ℤ) < 0)]
    {F X : Type*} [CommRing F] [Algebra (ZMod p) F]
    {C : ConditionalCM.CMDescentInput d p}
    (I : CMQuotientLiftData p d C F X) :
    I.constructedLogarithmicForm ∈ I.geometry.forms.forms 2 := by
  have h := I.geometry.forms.forms_mul
    (I.geometry.forms.forms_serre I.quotient_form) I.quotientInverse_form
  simpa only [constructedLogarithmicForm, zero_add, Nat.add_zero] using h

/-- Rolen's formal CM product determines the cusp expansion of the
constructed form. This uses the oriented quotient, its inverse, and the
weight-zero Serre law.
[rolenManuscript, Section 4, equations (product) and (L)] -/
theorem CMQuotientLiftData.constructedLogarithmicForm_qexp
    {p d : ℕ} [Fact p.Prime] [Fact (-(d : ℤ) < 0)]
    {F X : Type*} [CommRing F] [Algebra (ZMod p) F]
    {C : ConditionalCM.CMDescentInput d p}
    (I : CMQuotientLiftData p d C F X) :
    I.geometry.forms.qexp I.constructedLogarithmicForm =
      QSeries.principalLogarithmicLambertSeries p d := by
  let M := I.geometry.forms
  let R := PowerSeries.map (cmCoefficientReduction p I.hp6)
    (cmFormalBorcherdsQuotient d I.hd I.hsq I.hmod)
  have hR : PowerSeries.constantCoeff R = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp only [R, PowerSeries.coeff_map]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
      cmFormalBorcherdsQuotient_constantCoeff]
    exact map_one _
  have hRinv : M.qexp I.quotientInverse = R.invOfUnit 1 := by
    have hq : R * M.qexp I.quotientInverse = 1 := by
      dsimp only [R]
      rw [← I.quotient_qexp, ← map_mul, I.quotient_mul_inverse, map_one]
    have hr : R.invOfUnit 1 * R = 1 := by
      rw [mul_comm]
      exact PowerSeries.mul_invOfUnit R 1 hR
    calc
      M.qexp I.quotientInverse = 1 * M.qexp I.quotientInverse := (one_mul _).symm
      _ = (R.invOfUnit 1 * R) * M.qexp I.quotientInverse := by rw [hr]
      _ = R.invOfUnit 1 * (R * M.qexp I.quotientInverse) := by ring
      _ = R.invOfUnit 1 := by rw [hq, mul_one]
  have hserre : M.qexp (M.serre 0 I.quotient) =
      QSeries.eulerDerivative (M.qexp I.quotient) := by
    have h := M.theta_qexp I.quotient_form
    simp only [hasseTheta_apply, Nat.cast_zero, zero_div, zero_smul, add_zero,
      map_mul, M.H_qexp, one_mul] at h
    exact h
  rw [constructedLogarithmicForm, map_mul, hserre, I.quotient_qexp, hRinv]
  exact cmFormalBorcherdsQuotient_reduced_logarithmicLambert
    p d I.hp6 I.hd I.hsq I.hmod

/-- The homogeneous identity for the logarithmic form built from the actual
oriented quotient. Its proof uses the formal CM product and the independent
Shimura lift. [rolenManuscript, Section 4, equation (hasse)] -/
theorem CMQuotientLiftData.constructed_homogeneous_lambert_identity
    {p d : ℕ} [Fact p.Prime] [Fact (-(d : ℤ) < 0)]
    {F X : Type*} [CommRing F] [Algebra (ZMod p) F]
    {C : ConditionalCM.CMDescentInput d p}
    (I : CMQuotientLiftData p d C F X)
    (hdiff : QSeries.eulerDerivative (QSeries.eulerDerivative
      (QSeries.principalLogarithmicLambertSeries p d)) =
        PowerSeries.C (d : ZMod p) *
          QSeries.eulerDerivative (QSeries.principalShimuraLambertSeries p d)) :
    hasseTheta I.geometry.forms.H I.geometry.forms.E I.geometry.forms.serre (p + 3)
        (hasseTheta I.geometry.forms.H I.geometry.forms.E I.geometry.forms.serre 2
          I.constructedLogarithmicForm) =
      (d : ZMod p) • (I.geometry.forms.H *
        hasseTheta I.geometry.forms.H I.geometry.forms.E I.geometry.forms.serre 4
          I.geometry.forms.J) := by
  exact I.geometry.forms.homogeneous_lambert_identity_of_forms
    I.constructedLogarithmicForm I.geometry.forms.J
    I.constructedLogarithmicForm_form I.geometry.forms.J_form
    I.constructedLogarithmicForm_qexp I.geometry.forms.J_qexp hdiff

/-- The CM comparison for the logarithmic form constructed from the actual
oriented quotient follows from generic Leibniz and coordinate derivative
laws. No separately supplied `L` or `L_qexp` is used. -/
theorem CMQuotientLiftData.constructed_logarithmic_identity
    {p d : ℕ} [Fact p.Prime] [Fact (-(d : ℤ) < 0)]
    {F X : Type*} [CommRing F] [Algebra (ZMod p) F]
    {C : ConditionalCM.CMDescentInput d p}
    (I : CMQuotientLiftData p d C F X)
    (x : X) (ha : ¬C.geometricA.IsRoot (I.geometry.coordinate x))
    (hb : ¬C.geometricB.IsRoot (I.geometry.coordinate x)) :
    I.geometry.evaluate x ha hb I.constructedLogarithmicForm =
      I.geometry.theta_coordinate x *
        (C.geometricA.derivative * C.geometricB -
          C.geometricA * C.geometricB.derivative).eval (I.geometry.coordinate x) /
        (C.geometricA.eval (I.geometry.coordinate x) *
          C.geometricB.eval (I.geometry.coordinate x)) := by
  let φ := I.geometry.evaluate x ha hb
  have hquotient : φ I.quotient * φ I.denominator = φ I.numerator := by
    simpa only [map_mul] using congrArg φ I.quotient_mul_denominator
  have hinverse : φ I.quotient * φ I.quotientInverse = 1 := by
    simpa only [map_mul, map_one] using congrArg φ I.quotient_mul_inverse
  have hproduct : φ (I.geometry.forms.serre 0 I.quotient) * φ I.denominator +
      φ I.quotient * φ (I.geometry.forms.serre I.sectionWeight I.denominator) =
        φ (I.geometry.forms.serre I.sectionWeight I.numerator) := by
    calc
      _ = φ (I.geometry.forms.serre I.sectionWeight
          (I.quotient * I.denominator)) := by
        rw [I.serre_product]
        simp only [map_add, map_mul]
      _ = φ (I.geometry.forms.serre I.sectionWeight I.numerator) := by
        rw [I.quotient_mul_denominator]
  have hL : φ I.constructedLogarithmicForm =
      φ (I.geometry.forms.serre 0 I.quotient) * φ I.quotientInverse := by
    rw [CMQuotientLiftData.constructedLogarithmicForm]
    exact map_mul φ _ _
  have h := logarithmic_value_of_equal_weight_sections
    (C.geometricA.eval (I.geometry.coordinate x))
    (C.geometricB.eval (I.geometry.coordinate x))
    (C.geometricA.derivative.eval (I.geometry.coordinate x))
    (C.geometricB.derivative.eval (I.geometry.coordinate x))
    (I.sectionFactor x) (I.serreConnection x)
    (φ I.quotient) (φ I.quotientInverse)
    (φ (I.geometry.forms.serre 0 I.quotient))
    (φ (I.geometry.forms.serre I.sectionWeight I.numerator))
    (φ (I.geometry.forms.serre I.sectionWeight I.denominator))
    (I.geometry.theta_coordinate x) (φ I.constructedLogarithmicForm)
    ha hb (I.sectionFactor_ne_zero x)
    (by simpa only [φ, I.evaluate_numerator x ha hb,
          I.evaluate_denominator x ha hb] using hquotient)
    hinverse
    (by simpa only [φ, I.evaluate_denominator x ha hb] using hproduct)
    (I.evaluate_derivative_numerator x ha hb)
    (I.evaluate_derivative_denominator x ha hb) hL
  simpa only [Polynomial.eval_sub, Polynomial.eval_mul] using h

/-- Assemble the established conditional Hasse deduction from quotient data,
without assuming the CM-specific logarithmic identity as a field. -/
def CMQuotientLiftData.toLiftHasseInput
    {p d : ℕ} [Fact p.Prime] [Fact (-(d : ℤ) < 0)]
    {F X : Type*} [CommRing F] [Algebra (ZMod p) F]
    {C : ConditionalCM.CMDescentInput d p}
    (I : CMQuotientLiftData p d C F X) : LiftHasseInput p d C F X :=
  { toLiftHasseGeometry := I.geometry
    L := I.constructedLogarithmicForm
    L_form := I.constructedLogarithmicForm_form
    L_qexp := I.constructedLogarithmicForm_qexp
    logarithmic_identity := I.constructed_logarithmic_identity }

end SptClassification
