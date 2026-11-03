/- Assembled by AxiomProver. -/

module

public import SptClassification.Theta.PrincipalWeilInput
public import SptClassification.Theta.NegativeVectorForms
public import SptClassification.QuadraticForms.ClassPolynomials
public import Mathlib.Data.Nat.Squarefree

/-!
# CM support of the principal Weil divisor

The negative coefficients of the actual input select discriminant `-d` and
orientations `1,5,7,11`. Squarefreeness makes the corresponding forms primitive,
so their eta values occur in the actual class polynomials. This proves the pole
identification in [rolenManuscript, lines 348–350].
-/

public section

namespace SptClassification

/-- A class of squarefree negative discriminant is primitive. -/
theorem CMClass.content_eq_one_of_squarefree {d : ℕ} {r : ZMod 12}
    [Fact (-(d : ℤ) < 0)] (hsq : Squarefree d) (C : CMClass (-(d : ℤ)) r) :
    C.content = 1 := by
  have hz : (C.content : ℤ) ^ 2 ∣ (d : ℤ) :=
    dvd_neg.mp C.content_sq_dvd_discriminant
  have hn : C.content * C.content ∣ d := by
    exact_mod_cast (show (C.content : ℤ) * C.content ∣ (d : ℤ) by
      simpa only [pow_two] using hz)
  exact Nat.isUnit_iff.mp (hsq C.content hn)

/-- Every primitive level-six form contributes its actual eta value to the
polynomial of its orientation. -/
theorem LevelSixForm.complexCMPolynomial_eval_of_squarefree {d : ℕ} {r : ZMod 12}
    [Fact (-(d : ℤ) < 0)] (hsq : Squarefree d) (Q : LevelSixForm (-(d : ℤ)) r) :
    (complexCMPolynomial (-(d : ℤ)) r).eval (levelSixEtaQuotient Q.cmPoint) = 0 := by
  let C : CMClass (-(d : ℤ)) r := Quotient.mk _ Q
  simpa only [C, CMClass.etaValue_mk] using complexCMPolynomial_eval_etaValue
    (⟨C, C.content_eq_one_of_squarefree hsq⟩ : PrimitiveCMClass (-(d : ℤ)) r)

namespace Theta

/-- The four orientations with nonzero coefficients in the distinguished vector. -/
theorem weilInputVector_ne_zero_iff (r : ZMod 12) :
    weilInputVector r ≠ 0 ↔ r = 1 ∨ r = 5 ∨ r = 7 ∨ r = 11 := by
  classical
  rw [weilInputVector_eq_character]
  simp only [characterTwelveResidue]
  split_ifs <;> simp_all <;> tauto

/-- A nonzero negative coefficient fixes both the discriminant and orientation. -/
theorem principalWeilCoefficient_negative_support {d : ℕ} (hd : d % 24 = 23)
    {n : ℤ} (hn : n < 0) {r : ZMod 12}
    (h : principalWeilCoefficient d n r ≠ 0) :
    n = -(d : ℤ) ∧ (r = 1 ∨ r = 5 ∨ r = 7 ∨ r = 11) := by
  rw [principalWeilCoefficient_negative d hd n hn] at h
  split at h
  · exact ⟨by assumption, (weilInputVector_ne_zero_iff r).mp h⟩
  · exact False.elim (h rfl)

/-- A positive-component negative vector with supported orientation gives a
root of the actual paired CM class polynomial. -/
theorem DualCoordinates.cmPolynomial_eval_cmPoint {d : ℕ}
    [Fact (-(d : ℤ) < 0)] (hsq : Squarefree d) (x : DualCoordinates)
    (hc : 0 < x.c) (hnorm : quadratic x.toSpace = -(d : ℚ) / 24)
    (hr : weilInputVector (x.r : ZMod 12) ≠ 0) :
    (cmClassPolynomialA (-(d : ℤ)) * cmClassPolynomialB (-(d : ℤ))).eval
      (levelSixEtaQuotient (x.toLevelSixForm d hc hnorm).cmPoint) = 0 := by
  have hroot := (x.toLevelSixForm d hc hnorm).complexCMPolynomial_eval_of_squarefree hsq
  generalize levelSixEtaQuotient (x.toLevelSixForm d hc hnorm).cmPoint = z at hroot ⊢
  rcases (weilInputVector_ne_zero_iff _).mp hr with h | h | h | h
  all_goals
    rw [h] at hroot
    simp only [cmClassPolynomialA_eq, cmClassPolynomialB_eq, Polynomial.eval_mul]
    simp [hroot]

/-- Any upper-half-plane zero of the positive-component vector quadratic is
the corresponding CM point and therefore lies in the paired CM support. -/
theorem DualCoordinates.cmPolynomial_eval_of_positive_root {d : ℕ}
    [Fact (-(d : ℤ) < 0)] (hsq : Squarefree d) (x : DualCoordinates)
    (hc : 0 < x.c) (hnorm : quadratic x.toSpace = -(d : ℚ) / 24)
    (hr : weilInputVector (x.r : ZMod 12) ≠ 0) (z : UpperHalfPlane)
    (hz : (6 * (x.c : ℂ)) * (z : ℂ) ^ 2 + (x.r : ℂ) * z + x.a = 0) :
    (cmClassPolynomialA (-(d : ℤ)) * cmClassPolynomialB (-(d : ℤ))).eval
      (levelSixEtaQuotient z) = 0 := by
  let Q := x.toLevelSixForm d hc hnorm
  have hzero : BinaryQuadraticForm.evaluateOver ℂ Q.toBinaryQuadraticForm z 1 = 0 := by
    simpa only [Q, DualCoordinates.toLevelSixForm_toBinaryQuadraticForm,
      DualCoordinates.binaryForm_eq,
      BinaryQuadraticForm.evaluateOver_one, Int.cast_mul, Int.cast_ofNat] using hz
  have heq : z = Q.cmPoint :=
    Q.toBinaryQuadraticForm.upper_root_unique (ne_of_gt Q.a_pos)
      z Q.cmPoint hzero Q.evaluateOver_cmPoint
  rw [heq]
  exact x.cmPolynomial_eval_cmPoint hsq hc hnorm hr

/-- The vector's sign does not affect its quadratic zero or Weil coefficient.
Thus either component of the negative cone gives the same CM support. -/
theorem DualCoordinates.cmPolynomial_eval_of_root {d : ℕ}
    [Fact (-(d : ℤ) < 0)] (hsq : Squarefree d) (x : DualCoordinates)
    (hnorm : quadratic x.toSpace = -(d : ℚ) / 24)
    (hr : weilInputVector (x.r : ZMod 12) ≠ 0) (z : UpperHalfPlane)
    (hz : (6 * (x.c : ℂ)) * (z : ℂ) ^ 2 + (x.r : ℂ) * z + x.a = 0) :
    (cmClassPolynomialA (-(d : ℤ)) * cmClassPolynomialB (-(d : ℤ))).eval
      (levelSixEtaQuotient z) = 0 := by
  have hd : (0 : ℚ) < d := by
    exact_mod_cast (show (0 : ℤ) < d by have := (Fact.out : -(d : ℤ) < 0); omega)
  have hc0 : x.c ≠ 0 := by
    intro hc
    rw [x.quadratic_eq, hc, Int.cast_zero, mul_zero, sub_zero] at hnorm
    nlinarith [sq_nonneg (x.r : ℚ)]
  rcases lt_or_gt_of_ne hc0 with hc | hc
  · let y : DualCoordinates := ⟨-x.a, -x.r, -x.c⟩
    have hyc : 0 < y.c := neg_pos.mpr hc
    have hyn : quadratic y.toSpace = -(d : ℚ) / 24 := by
      rw [y.quadratic_eq, x.quadratic_eq] at *
      simpa only [y, Int.cast_neg, neg_sq, neg_mul_neg] using hnorm
    have hyr : weilInputVector (y.r : ZMod 12) ≠ 0 := by
      simpa only [y, Int.cast_neg, weilInputVector_neg] using hr
    apply y.cmPolynomial_eval_of_positive_root hsq hyc hyn hyr z
    dsimp only [y]
    push_cast
    linear_combination -hz
  · exact x.cmPolynomial_eval_of_positive_root hsq hc hnorm hr z hz

/-- Every quadratic divisor selected by a nonzero negative coefficient of
the actual principal Weil input lies in the actual CM polynomial support. -/
theorem principalWeil_negative_divisor_support {d : ℕ}
    [Fact (-(d : ℤ) < 0)] (hsq : Squarefree d) (hd : d % 24 = 23)
    (x : DualCoordinates) (n : ℤ) (hn : n < 0)
    (hnorm : quadratic x.toSpace = (n : ℚ) / 24)
    (hcoeff : principalWeilCoefficient d n x.discriminantClass ≠ 0)
    (z : UpperHalfPlane)
    (hz : (6 * (x.c : ℂ)) * (z : ℂ) ^ 2 + (x.r : ℂ) * z + x.a = 0) :
    (cmClassPolynomialA (-(d : ℤ)) * cmClassPolynomialB (-(d : ℤ))).eval
      (levelSixEtaQuotient z) = 0 := by
  have hn' := (principalWeilCoefficient_negative_support hd hn hcoeff).1
  have hr : weilInputVector (x.r : ZMod 12) ≠ 0 := by
    exact (weilInputVector_ne_zero_iff _).mpr
      (principalWeilCoefficient_negative_support hd hn hcoeff).2
  apply x.cmPolynomial_eval_of_root hsq _ hr z hz
  simpa only [hn', Int.cast_neg, Int.cast_natCast] using hnorm

end Theta
end SptClassification
