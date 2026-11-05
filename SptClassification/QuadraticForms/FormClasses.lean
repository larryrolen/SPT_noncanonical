/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.PositiveForms
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Proper classes and the class number of positive integral forms

Proper equivalence is the actual `SL(2, ℤ)` orbit relation. The class number
counts the classes of content one, with each class counted once.
-/

@[expose] public section

namespace SptClassification

/-- Proper classes of positive integral forms of a negative discriminant. -/
@[expose]
def FormClass (D : ℤ) [Fact (D < 0)] :=
  MulAction.orbitRel.Quotient (Matrix.SpecialLinearGroup (Fin 2) ℤ) (PositiveForm D)

namespace FormClass

instance finite (D : ℤ) [Fact (D < 0)] : Finite (FormClass D) := by
  unfold FormClass
  infer_instance

/-- The content is independent of the chosen proper representative. -/
def content {D : ℤ} [Fact (D < 0)] : FormClass D → ℕ :=
  Quotient.lift (fun Q : PositiveForm D => Q.toBinaryQuadraticForm.content) (by
    intro Q R h
    obtain ⟨g, hg⟩ := h
    rw [← hg, PositiveForm.toBinaryQuadraticForm_smul, BinaryQuadraticForm.content_transform])

@[simp] theorem content_mk {D : ℤ} [Fact (D < 0)] (Q : PositiveForm D) :
    content (Quotient.mk _ Q : FormClass D) = Q.toBinaryQuadraticForm.content := (rfl)

/-- Send a reduced form to its proper equivalence class. -/
def ofReduced {D : ℤ} [Fact (D < 0)] (Q : ReducedForm D) : FormClass D := Quotient.mk _ Q.1

theorem ofReduced_surjective {D : ℤ} [Fact (D < 0)] :
    Function.Surjective (ofReduced (D := D)) := by
  intro C
  induction C using Quotient.inductionOn with
  | h Q =>
    obtain ⟨g, hg⟩ := Q.toBinaryQuadraticForm.exists_reduced_transform Q.a_pos
      (Q.discriminant_eq.trans_lt Fact.out)
    refine ⟨⟨g • Q, ?_⟩, ?_⟩
    · simpa only [PositiveForm.toBinaryQuadraticForm_smul] using hg
    exact Quotient.sound ⟨g, rfl⟩

end FormClass

/-- Proper primitive classes, expressed as the content-one part of the class space. -/
@[expose]
def PrimitiveFormClass (D : ℤ) [Fact (D < 0)] := {C : FormClass D // C.content = 1}

instance primitiveFormClassFinite (D : ℤ) [Fact (D < 0)] : Finite (PrimitiveFormClass D) := by
  unfold PrimitiveFormClass
  infer_instance

/-- The proper class number, in its integral binary-form realization. -/
noncomputable def formClassNumber (D : ℤ) [Fact (D < 0)] : ℕ := Nat.card (PrimitiveFormClass D)

theorem formClassNumber_eq (D : ℤ) [Fact (D < 0)] :
    formClassNumber D = Nat.card (PrimitiveFormClass D) := (rfl)

/-- Counting all reduced forms gives an upper bound for the primitive class number. -/
theorem formClassNumber_le_reduced_card (D : ℤ) [Fact (D < 0)] :
    formClassNumber D ≤ Nat.card (ReducedForm D) := by
  have hprimitive : formClassNumber D ≤ Nat.card (FormClass D) :=
    Nat.card_le_card_of_injective (fun C : PrimitiveFormClass D => C.val) Subtype.val_injective
  exact hprimitive.trans (Nat.card_le_card_of_surjective FormClass.ofReduced FormClass.ofReduced_surjective)

/-- The principal integral form of an odd discriminant. -/
def principalForm (D : ℤ) (hD : D % 4 = 1) : PositiveForm D where
  toBinaryQuadraticForm := ⟨1, 1, (1 - D) / 4⟩
  a_pos := by norm_num
  discriminant_eq := by
    simp only [BinaryQuadraticForm.discriminant, one_pow, mul_one]
    omega

/-- The principal proper class is primitive. -/
def principalFormClass (D : ℤ) [Fact (D < 0)] (hD : D % 4 = 1) : PrimitiveFormClass D :=
  ⟨Quotient.mk _ (principalForm D hD), by
    change (principalForm D hD).toBinaryQuadraticForm.content = 1
    exact BinaryQuadraticForm.content_of_a_eq_one _ (by rfl)⟩

theorem formClassNumber_pos (D : ℤ) [Fact (D < 0)] (hD : D % 4 = 1) :
    0 < formClassNumber D := by
  let : Nonempty (PrimitiveFormClass D) := ⟨principalFormClass D hD⟩
  exact Nat.card_pos

end SptClassification
