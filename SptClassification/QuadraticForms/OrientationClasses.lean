/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.OrientationResidues
public import SptClassification.QuadraticForms.ClassPolynomials

/-!
# Oriented primitive classes and class-polynomial degrees

The finite orientation certificate gives surjectivity onto proper form classes.
The fixed-unit-orientation lemma gives injectivity. Content is preserved, so the
bijection restricts to primitive classes and identifies each oriented degree
with the genuine proper class number.
-/

public section

namespace SptClassification

namespace CMClass

/-- Every proper class of discriminant one modulo24 has a representative of
each prescribed unit level-six orientation. -/
theorem toFormClass_surjective {D : ℤ} {r : ZMod 12} [Fact (D < 0)]
    (hD : D % 24 = 1) (hr : IsUnit r) : Function.Surjective (toFormClass (D := D) (r := r)) := by
  intro C
  induction C using Quotient.inductionOn with
  | h Q =>
    obtain ⟨g, hga, hgb⟩ := exists_oriented_transform Q.toBinaryQuadraticForm
      (by simpa only [Q.discriminant_eq] using hD) r hr
    let R : LevelSixForm D r := {
      toBinaryQuadraticForm := BinaryQuadraticForm.transform g Q.toBinaryQuadraticForm
      a_pos := Q.toBinaryQuadraticForm.transform_a_pos Q.a_pos (Q.discriminant_eq.trans_lt Fact.out) g
      discriminant_eq := (BinaryQuadraticForm.discriminant_transform g Q.toBinaryQuadraticForm).trans Q.discriminant_eq
      six_dvd_a := hga
      b_residue := hgb }
    refine ⟨Quotient.mk _ R, ?_⟩
    rw [CMClass.toFormClass_mk]
    apply Quotient.sound
    refine ⟨g, PositiveForm.ext ?_⟩
    simp only [LevelSixForm.toPositiveForm_toBinaryQuadraticForm,
      PositiveForm.toBinaryQuadraticForm_smul, R]

end CMClass

/-- The content-preserving map from primitive oriented classes to primitive proper classes. -/
def primitiveToFormClass {D : ℤ} {r : ZMod 12} [Fact (D < 0)]
    (C : PrimitiveCMClass D r) : PrimitiveFormClass D :=
  ⟨C.val.toFormClass, by rw [CMClass.content_toFormClass]; exact C.property⟩

theorem primitiveToFormClass_injective {D : ℤ} {r : ZMod 12} [Fact (D < 0)]
    (hr : IsUnit r) : Function.Injective (primitiveToFormClass (D := D) (r := r)) := by
  intro C E h
  apply Subtype.ext
  exact CMClass.toFormClass_injective hr (congrArg Subtype.val h)

theorem primitiveToFormClass_surjective {D : ℤ} {r : ZMod 12} [Fact (D < 0)]
    (hD : D % 24 = 1) (hr : IsUnit r) :
    Function.Surjective (primitiveToFormClass (D := D) (r := r)) := by
  intro C
  obtain ⟨E, hE⟩ := CMClass.toFormClass_surjective hD hr C.val
  have hcontent : E.content = 1 := by
    rw [← CMClass.content_toFormClass, hE]
    exact C.property
  exact ⟨⟨E, hcontent⟩, Subtype.ext hE⟩

/-- The genuine orientation-forgetting bijection on primitive classes. -/
noncomputable def primitiveOrientationEquiv (D : ℤ) (r : ZMod 12) [Fact (D < 0)]
    (hD : D % 24 = 1) (hr : IsUnit r) : PrimitiveCMClass D r ≃ PrimitiveFormClass D :=
  Equiv.ofBijective primitiveToFormClass
    ⟨primitiveToFormClass_injective hr, primitiveToFormClass_surjective hD hr⟩

/-- Each unit orientation has exactly the proper class number of primitive classes. -/
theorem primitiveCMClass_card (D : ℤ) (r : ZMod 12) [Fact (D < 0)]
    (hD : D % 24 = 1) (hr : IsUnit r) :
    Nat.card (PrimitiveCMClass D r) = formClassNumber D :=
  (Nat.card_congr (primitiveOrientationEquiv D r hD hr)).trans (formClassNumber_eq D).symm

theorem complexCMPolynomial_natDegree_eq_classNumber (D : ℤ) (r : ZMod 12) [Fact (D < 0)]
    (hD : D % 24 = 1) (hr : IsUnit r) :
    (complexCMPolynomial D r).natDegree = formClassNumber D :=
  (complexCMPolynomial_natDegree D r).trans (primitiveCMClass_card D r hD hr)

/-- The actual complex `A_d` polynomial has degree twice the proper class number. -/
theorem cmClassPolynomialA_natDegree (D : ℤ) [Fact (D < 0)] (hD : D % 24 = 1) :
    (cmClassPolynomialA D).natDegree = 2 * formClassNumber D := by
  have h1 : IsUnit (1 : ZMod 12) := isUnit_one
  have h11 : IsUnit (11 : ZMod 12) := (ZMod.isUnit_iff_coprime 11 12).mpr (by decide)
  rw [cmClassPolynomialA_eq, Polynomial.natDegree_mul (complexCMPolynomial_monic D 1).ne_zero
    (complexCMPolynomial_monic D 11).ne_zero,
    complexCMPolynomial_natDegree_eq_classNumber D 1 hD h1,
    complexCMPolynomial_natDegree_eq_classNumber D 11 hD h11]
  omega

/-- The actual complex `B_d` polynomial has degree twice the proper class number. -/
theorem cmClassPolynomialB_natDegree (D : ℤ) [Fact (D < 0)] (hD : D % 24 = 1) :
    (cmClassPolynomialB D).natDegree = 2 * formClassNumber D := by
  have h5 : IsUnit (5 : ZMod 12) := (ZMod.isUnit_iff_coprime 5 12).mpr (by decide)
  have h7 : IsUnit (7 : ZMod 12) := (ZMod.isUnit_iff_coprime 7 12).mpr (by decide)
  rw [cmClassPolynomialB_eq, Polynomial.natDegree_mul (complexCMPolynomial_monic D 5).ne_zero
    (complexCMPolynomial_monic D 7).ne_zero,
    complexCMPolynomial_natDegree_eq_classNumber D 5 hD h5,
    complexCMPolynomial_natDegree_eq_classNumber D 7 hD h7]
  omega

theorem cmClassPolynomialA_natDegree_pos (D : ℤ) [Fact (D < 0)] (hD : D % 24 = 1) :
    0 < (cmClassPolynomialA D).natDegree := by
  rw [cmClassPolynomialA_natDegree D hD]
  have h := formClassNumber_pos D (by omega)
  omega

theorem cmClassPolynomialB_natDegree_pos (D : ℤ) [Fact (D < 0)] (hD : D % 24 = 1) :
    0 < (cmClassPolynomialB D).natDegree := by
  rw [cmClassPolynomialB_natDegree D hD]
  have h := formClassNumber_pos D (by omega)
  omega

end SptClassification
