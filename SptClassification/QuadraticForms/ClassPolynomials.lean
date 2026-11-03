/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.CMPointAction
public import SptClassification.ModularForms.EtaQuotientInvariance
public import Mathlib.Algebra.Polynomial.Roots

/-!
# The actual complex level-six CM class polynomials

The eta quotient is evaluated at actual CM points and descends to the finite
oriented class space by its proved Γ₀(6) invariance. Products over the primitive
classes define the complex polynomials. Integral descent and the comparison of
their degrees with the proper class number are additional mathematical results.

We follow the class-polynomial construction in [rolen2026canonical], section4.
-/

public section

namespace SptClassification

instance primitiveCMClassFinite (D : ℤ) (r : ZMod 12) [Fact (D < 0)] :
    Finite (PrimitiveCMClass D r) := by
  unfold PrimitiveCMClass
  infer_instance

namespace CMClass

/-- The actual eta-quotient value, independent of the oriented class representative. -/
noncomputable def etaValue {D : ℤ} {r : ZMod 12} [Fact (D < 0)] : CMClass D r → ℂ :=
  Quotient.lift (fun Q : LevelSixForm D r => levelSixEtaQuotient Q.cmPoint) (by
    intro Q R h
    obtain ⟨g, hg⟩ := h
    rw [← hg, LevelSixForm.cmPoint_smul]
    exact levelSixEtaQuotient_gamma0 g R.cmPoint)

@[simp] theorem etaValue_mk {D : ℤ} {r : ZMod 12} [Fact (D < 0)] (Q : LevelSixForm D r) :
    etaValue (Quotient.mk _ Q : CMClass D r) = levelSixEtaQuotient Q.cmPoint := (rfl)

theorem etaValue_ne_zero {D : ℤ} {r : ZMod 12} [Fact (D < 0)] (C : CMClass D r) :
    etaValue C ≠ 0 := by
  induction C using Quotient.inductionOn with
  | h Q => exact levelSixEtaQuotient_ne_zero Q.cmPoint

end CMClass

open Polynomial

/-- The monic complex polynomial for one oriented primitive CM class space. -/
noncomputable def complexCMPolynomial (D : ℤ) (r : ZMod 12) [Fact (D < 0)] : ℂ[X] := by
  classical
  letI := Fintype.ofFinite (PrimitiveCMClass D r)
  exact ∏ C : PrimitiveCMClass D r, (X - Polynomial.C C.val.etaValue)

/-- The defining product, with its finite instance fixed in the public statement. -/
theorem complexCMPolynomial_eq_prod (D : ℤ) (r : ZMod 12) [Fact (D < 0)] :
    letI : Fintype (PrimitiveCMClass D r) := Fintype.ofFinite (PrimitiveCMClass D r);
    complexCMPolynomial D r =
      ∏ C : PrimitiveCMClass D r, (X - Polynomial.C C.val.etaValue) := by
  classical
  unfold complexCMPolynomial
  exact (rfl)

theorem complexCMPolynomial_monic (D : ℤ) (r : ZMod 12) [Fact (D < 0)] :
    (complexCMPolynomial D r).Monic := by
  classical
  let := Fintype.ofFinite (PrimitiveCMClass D r)
  unfold complexCMPolynomial
  exact Polynomial.monic_prod_X_sub_C (fun C : PrimitiveCMClass D r => C.val.etaValue) Finset.univ

/-- The product has one linear factor for each actual oriented primitive class. -/
theorem complexCMPolynomial_natDegree (D : ℤ) (r : ZMod 12) [Fact (D < 0)] :
    (complexCMPolynomial D r).natDegree = Nat.card (PrimitiveCMClass D r) := by
  classical
  let := Fintype.ofFinite (PrimitiveCMClass D r)
  unfold complexCMPolynomial
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun C _ => Polynomial.monic_X_sub_C C.val.etaValue)]
  simp [Nat.card_eq_fintype_card]

theorem complexCMPolynomial_eval_etaValue {D : ℤ} {r : ZMod 12} [Fact (D < 0)]
    (C : PrimitiveCMClass D r) : (complexCMPolynomial D r).eval C.val.etaValue = 0 := by
  classical
  let := Fintype.ofFinite (PrimitiveCMClass D r)
  unfold complexCMPolynomial
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ C)
  simp

/-- No actual CM eta value is zero, so zero is not a root of the product. -/
theorem complexCMPolynomial_eval_zero_ne_zero (D : ℤ) (r : ZMod 12) [Fact (D < 0)] :
    (complexCMPolynomial D r).eval 0 ≠ 0 := by
  classical
  unfold complexCMPolynomial
  rw [Polynomial.eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro C _
  simpa using C.val.etaValue_ne_zero

/-- The complex realization of `A_d`, with the middle-coefficient classes1 and11. -/
noncomputable def cmClassPolynomialA (D : ℤ) [Fact (D < 0)] : ℂ[X] :=
  complexCMPolynomial D 1 * complexCMPolynomial D 11

theorem cmClassPolynomialA_eq (D : ℤ) [Fact (D < 0)] :
    cmClassPolynomialA D = complexCMPolynomial D 1 * complexCMPolynomial D 11 := (rfl)

/-- The complex realization of `B_d`, with the middle-coefficient classes5 and7. -/
noncomputable def cmClassPolynomialB (D : ℤ) [Fact (D < 0)] : ℂ[X] :=
  complexCMPolynomial D 5 * complexCMPolynomial D 7

theorem cmClassPolynomialB_eq (D : ℤ) [Fact (D < 0)] :
    cmClassPolynomialB D = complexCMPolynomial D 5 * complexCMPolynomial D 7 := (rfl)

/-- The paired complex CM products on the four actual oriented level-six
class spaces [rolen2026canonical, §4]. This construction makes no assertion
about integral descent. -/
noncomputable def cmClassPolynomialPair (D : ℤ) [Fact (D < 0)] : ℂ[X] × ℂ[X] :=
  (cmClassPolynomialA D, cmClassPolynomialB D)

theorem cmClassPolynomialPair_eq (D : ℤ) [Fact (D < 0)] :
    cmClassPolynomialPair D =
      (complexCMPolynomial D 1 * complexCMPolynomial D 11,
       complexCMPolynomial D 5 * complexCMPolynomial D 7) := by
  simp only [cmClassPolynomialPair, cmClassPolynomialA_eq, cmClassPolynomialB_eq]

theorem cmClassPolynomialA_monic (D : ℤ) [Fact (D < 0)] : (cmClassPolynomialA D).Monic :=
  (complexCMPolynomial_monic D 1).mul (complexCMPolynomial_monic D 11)

theorem cmClassPolynomialB_monic (D : ℤ) [Fact (D < 0)] : (cmClassPolynomialB D).Monic :=
  (complexCMPolynomial_monic D 5).mul (complexCMPolynomial_monic D 7)

end SptClassification
