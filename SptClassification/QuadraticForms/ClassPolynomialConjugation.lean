/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.CMConjugation
import Mathlib.Tactic.Linarith

/-!
# Conjugation of level-six CM class polynomials

Reflection of the middle coefficient pairs the CM factors of opposite
orientations. This proves conjugation symmetry of the complex products in
[rolen2026canonical], Section 4. It does not imply integral descent.
-/

public section

namespace SptClassification

open Polynomial

/-- Coefficientwise complex conjugation exchanges the two reflected
orientation products. -/
theorem complexCMPolynomial_map_star (D : ℤ) (r : ZMod 12) [Fact (D < 0)] :
    (complexCMPolynomial D r).map (starRingEnd ℂ) =
      complexCMPolynomial D (-r) := by
  classical
  let _ := Fintype.ofFinite (PrimitiveCMClass D r)
  let _ := Fintype.ofFinite (PrimitiveCMClass D (-r))
  rw [complexCMPolynomial_eq_prod, complexCMPolynomial_eq_prod]
  change Polynomial.map (starRingEnd ℂ)
      (∏ C : PrimitiveCMClass D r, (X - Polynomial.C C.val.etaValue)) =
    ∏ C : PrimitiveCMClass D (-r), (X - Polynomial.C C.val.etaValue)
  rw [Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  apply Fintype.prod_equiv (primitiveCMClassReverseMiddleEquiv D r)
    (fun C : PrimitiveCMClass D r => X - Polynomial.C (star C.val.etaValue))
    (fun C : PrimitiveCMClass D (-r) => X - Polynomial.C C.val.etaValue)
  intro C
  rw [primitiveCMClassReverseMiddleEquiv_apply,
    primitiveCMClassReverseMiddle_etaValue]

/-- The complex class polynomial `A_d` is fixed by coefficientwise conjugation. -/
theorem cmClassPolynomialA_map_star (D : ℤ) [Fact (D < 0)] :
    (cmClassPolynomialA D).map (starRingEnd ℂ) = cmClassPolynomialA D := by
  rw [cmClassPolynomialA_eq, Polynomial.map_mul,
    complexCMPolynomial_map_star, complexCMPolynomial_map_star]
  have h1 : -(1 : ZMod 12) = 11 := by decide
  have h11 : -(11 : ZMod 12) = 1 := by decide
  rw [h1, h11, mul_comm]

/-- The complex class polynomial `B_d` is fixed by coefficientwise conjugation. -/
theorem cmClassPolynomialB_map_star (D : ℤ) [Fact (D < 0)] :
    (cmClassPolynomialB D).map (starRingEnd ℂ) = cmClassPolynomialB D := by
  rw [cmClassPolynomialB_eq, Polynomial.map_mul,
    complexCMPolynomial_map_star, complexCMPolynomial_map_star]
  have h5 : -(5 : ZMod 12) = 7 := by decide
  have h7 : -(7 : ZMod 12) = 5 := by decide
  rw [h5, h7, mul_comm]

/-- Every coefficient of the actual complex polynomial `A` has zero imaginary part. -/
theorem cmClassPolynomialA_coeff_im_eq_zero (D : ℤ) [Fact (D < 0)] (n : ℕ) :
    ((cmClassPolynomialA D).coeff n).im = 0 := by
  have h := congrArg (fun P : ℂ[X] => P.coeff n) (cmClassPolynomialA_map_star D)
  have hs : star ((cmClassPolynomialA D).coeff n) =
      (cmClassPolynomialA D).coeff n := by simpa using h
  have hi : -((cmClassPolynomialA D).coeff n).im =
      ((cmClassPolynomialA D).coeff n).im := by
    simpa using congrArg Complex.im hs
  linarith

/-- Every coefficient of the actual complex polynomial `B` has zero imaginary part. -/
theorem cmClassPolynomialB_coeff_im_eq_zero (D : ℤ) [Fact (D < 0)] (n : ℕ) :
    ((cmClassPolynomialB D).coeff n).im = 0 := by
  have h := congrArg (fun P : ℂ[X] => P.coeff n) (cmClassPolynomialB_map_star D)
  have hs : star ((cmClassPolynomialB D).coeff n) =
      (cmClassPolynomialB D).coeff n := by simpa using h
  have hi : -((cmClassPolynomialB D).coeff n).im =
      ((cmClassPolynomialB D).coeff n).im := by
    simpa using congrArg Complex.im hs
  linarith

end SptClassification
