/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.OrientationClasses
public import SptClassification.Polynomials.Wronskian
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# The logarithmic derivative of the CM eta quotient

The numerator and denominator below are the actual products over oriented
level-six CM classes.  This module records the elementary analytic part of
the logarithmic lift in [rolenManuscript, Section 4, equations (product)
and (L)].  The Borcherds product expansion and reduction to a homogeneous
form in characteristic `p` require separate results.
-/

public section

namespace SptClassification

open Polynomial

/-- The quotient of the actual oriented CM class polynomials evaluated at
the analytic level-six eta quotient. -/
noncomputable def cmBorcherdsQuotient (D : ℤ) [Fact (D < 0)] (z : ℂ) : ℂ :=
  (cmClassPolynomialA D).eval (levelSixEtaQuotient z) /
    (cmClassPolynomialB D).eval (levelSixEtaQuotient z)

/-- The analytic quotient as a function, for differentiation. -/
theorem cmBorcherdsQuotient_eq_fun (D : ℤ) [Fact (D < 0)] :
    cmBorcherdsQuotient D = fun z =>
      (cmClassPolynomialA D).eval (levelSixEtaQuotient z) /
        (cmClassPolynomialB D).eval (levelSixEtaQuotient z) := (rfl)

/-- The analytic `Theta` derivative of a function of the upper-half-plane
variable, with `q = exp (2 pi i z)`. -/
noncomputable def thetaDerivative (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  deriv f z / (2 * Real.pi * Complex.I)

/-- The logarithmic derivative of the genuine CM quotient. -/
noncomputable def cmLogarithmicLift (D : ℤ) [Fact (D < 0)] (z : ℂ) : ℂ :=
  thetaDerivative (cmBorcherdsQuotient D) z / cmBorcherdsQuotient D z

/-- The rational expression has precisely the derivative numerator of the
two actual CM class polynomials. -/
theorem cmClassPolynomial_logarithmic_ratio (D : ℤ) [Fact (D < 0)]
    (t : ℂ) (ha : (cmClassPolynomialA D).eval t ≠ 0)
    (hb : (cmClassPolynomialB D).eval t ≠ 0) :
    (cmClassPolynomialA D).derivative.eval t /
        (cmClassPolynomialA D).eval t -
      (cmClassPolynomialB D).derivative.eval t /
        (cmClassPolynomialB D).eval t =
      ((cmClassPolynomialA D).derivative * cmClassPolynomialB D -
        cmClassPolynomialA D * (cmClassPolynomialB D).derivative).eval t /
        ((cmClassPolynomialA D).eval t * (cmClassPolynomialB D).eval t) := by
  simp only [eval_sub, eval_mul]
  field_simp

/-- The Wronskian of the actual oriented CM class polynomials has the
equal-degree bound used in [rolenManuscript, proof of Proposition 4.1].
The stronger good-reduction assertion also needs integral CM descent and
separation. -/
theorem cmClassPolynomial_logarithmicNumerator_natDegree_le
    (D : ℤ) [Fact (D < 0)] (hD : D % 24 = 1) :
    ((cmClassPolynomialA D).derivative * cmClassPolynomialB D -
      cmClassPolynomialA D * (cmClassPolynomialB D).derivative).natDegree ≤
      4 * formClassNumber D - 2 := by
  have hdegree : (cmClassPolynomialB D).natDegree =
      (cmClassPolynomialA D).natDegree := by
    rw [cmClassPolynomialA_natDegree D hD, cmClassPolynomialB_natDegree D hD]
  have h := natDegree_logarithmicNumerator_le
    (cmClassPolynomialA_monic D) (cmClassPolynomialB_monic D) hdegree
    (cmClassPolynomialA_natDegree_pos D hD)
  rw [cmClassPolynomialA_natDegree D hD] at h
  omega

/-- The quotient rule for the actual CM products at a point where neither
product vanishes. -/
private theorem cmLogarithmicLift_eq_rational_of_hasDerivAt
    (D : ℤ) [Fact (D < 0)] (z : ℂ)
    (hA : HasDerivAt
      (fun w => (cmClassPolynomialA D).eval (levelSixEtaQuotient w))
      ((cmClassPolynomialA D).derivative.eval (levelSixEtaQuotient z) *
        deriv levelSixEtaQuotient z) z)
    (hB : HasDerivAt
      (fun w => (cmClassPolynomialB D).eval (levelSixEtaQuotient w))
      ((cmClassPolynomialB D).derivative.eval (levelSixEtaQuotient z) *
        deriv levelSixEtaQuotient z) z)
    (ha : (cmClassPolynomialA D).eval (levelSixEtaQuotient z) ≠ 0)
    (hb : (cmClassPolynomialB D).eval (levelSixEtaQuotient z) ≠ 0) :
    cmLogarithmicLift D z =
      thetaDerivative levelSixEtaQuotient z *
        ((cmClassPolynomialA D).derivative * cmClassPolynomialB D -
          cmClassPolynomialA D * (cmClassPolynomialB D).derivative).eval
            (levelSixEtaQuotient z) /
        ((cmClassPolynomialA D).eval (levelSixEtaQuotient z) *
          (cmClassPolynomialB D).eval (levelSixEtaQuotient z)) := by
  have hquot := (hA.div hB hb).deriv
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  simp only [cmLogarithmicLift, thetaDerivative, eval_sub, eval_mul]
  rw [cmBorcherdsQuotient_eq_fun]
  have hquot' := hquot
  change deriv (fun w : ℂ =>
      (cmClassPolynomialA D).eval (levelSixEtaQuotient w) /
        (cmClassPolynomialB D).eval (levelSixEtaQuotient w)) z = _ at hquot'
  rw [hquot']
  field_simp

/-- On the upper half-plane, logarithmic differentiation of the actual CM
quotient gives the Wronskian expression in [rolenManuscript, Section 4,
equation (L)]. This calculation uses holomorphy of the eta quotient and the
ordinary polynomial chain rule. The Borcherds product expansion is a separate
input. -/
theorem cmLogarithmicLift_eq_rational (D : ℤ) [Fact (D < 0)]
    (z : UpperHalfPlane)
    (ha : (cmClassPolynomialA D).eval (levelSixEtaQuotient z) ≠ 0)
    (hb : (cmClassPolynomialB D).eval (levelSixEtaQuotient z) ≠ 0) :
    cmLogarithmicLift D z =
      thetaDerivative levelSixEtaQuotient z *
        ((cmClassPolynomialA D).derivative * cmClassPolynomialB D -
          cmClassPolynomialA D * (cmClassPolynomialB D).derivative).eval
            (levelSixEtaQuotient z) /
        ((cmClassPolynomialA D).eval (levelSixEtaQuotient z) *
          (cmClassPolynomialB D).eval (levelSixEtaQuotient z)) := by
  have ht := (differentiableAt_levelSixEtaQuotient z).hasDerivAt
  have hA := ((cmClassPolynomialA D).hasDerivAt (levelSixEtaQuotient z)).comp
    (z : ℂ) ht
  have hB := ((cmClassPolynomialB D).hasDerivAt (levelSixEtaQuotient z)).comp
    (z : ℂ) ht
  exact cmLogarithmicLift_eq_rational_of_hasDerivAt D z hA hB ha hb

/-- Away from the actual CM divisor, a zero of the logarithmic lift is
exactly a zero of the CM-polynomial Wronskian whenever the eta coordinate
has nonzero `Theta` derivative.  The nonvanishing of that derivative after
good reduction is a separate geometric assertion in
[rolenManuscript, proof of Proposition 4.1]. -/
theorem cmLogarithmicLift_eq_zero_iff_wronskian (D : ℤ) [Fact (D < 0)]
    (z : UpperHalfPlane)
    (ha : (cmClassPolynomialA D).eval (levelSixEtaQuotient z) ≠ 0)
    (hb : (cmClassPolynomialB D).eval (levelSixEtaQuotient z) ≠ 0)
    (htheta : thetaDerivative levelSixEtaQuotient z ≠ 0) :
    cmLogarithmicLift D z = 0 ↔
      ((cmClassPolynomialA D).derivative * cmClassPolynomialB D -
        cmClassPolynomialA D * (cmClassPolynomialB D).derivative).eval
          (levelSixEtaQuotient z) = 0 := by
  have hden : (cmClassPolynomialA D).eval (levelSixEtaQuotient z) *
      (cmClassPolynomialB D).eval (levelSixEtaQuotient z) ≠ 0 :=
    mul_ne_zero ha hb
  rw [cmLogarithmicLift_eq_rational D z ha hb]
  constructor
  · intro h
    by_contra hw
    exact (div_ne_zero (mul_ne_zero htheta hw) hden) h
  · intro h
    simp [h]

end SptClassification
