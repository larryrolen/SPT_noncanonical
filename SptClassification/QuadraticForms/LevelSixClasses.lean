/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.LevelSixForms
public import Mathlib.GroupTheory.Index

/-!
# Classes of oriented level-six forms

We form the actual orbit quotient under `Γ₀(6)`. Content descends to this quotient
because it is invariant under the action. Every class, including imprimitive
classes, remains in the quotient.

## References

See [ahlgrenAndersen2016], sections 1 and 2.1.
-/

@[expose] public section

namespace SptClassification

/-- The `Γ₀(6)`-orbit space of positive forms with fixed negative discriminant
and fixed middle-coefficient residue. -/
@[expose]
def CMClass (D : ℤ) (r : ZMod 12) [Fact (D < 0)] :=
  Quotient (MulAction.orbitRel (CongruenceSubgroup.Gamma0 6) (LevelSixForm D r))

namespace CMClass

/-- The content of a class, independent of the representative. -/
def content {D : ℤ} {r : ZMod 12} [Fact (D < 0)] : CMClass D r → ℕ :=
  Quotient.lift (fun Q : LevelSixForm D r => Q.toBinaryQuadraticForm.content) (by
    intro Q R h
    obtain ⟨g, hg⟩ := h
    rw [← hg, LevelSixForm.content_smul])

@[simp] theorem content_mk {D : ℤ} {r : ZMod 12} [Fact (D < 0)]
    (Q : LevelSixForm D r) : content (Quotient.mk _ Q : CMClass D r) =
      Q.toBinaryQuadraticForm.content := (rfl)

theorem content_pos {D : ℤ} {r : ZMod 12} [Fact (D < 0)] (C : CMClass D r) :
    0 < content C := by
  induction C using Quotient.inductionOn with
  | h Q => exact Q.toBinaryQuadraticForm.content_pos (ne_of_gt Q.a_pos)

theorem content_sq_dvd_discriminant {D : ℤ} {r : ZMod 12} [Fact (D < 0)]
    (C : CMClass D r) : (content C : ℤ) ^ 2 ∣ D := by
  induction C using Quotient.inductionOn with
  | h Q =>
    change (Q.toBinaryQuadraticForm.content : ℤ) ^ 2 ∣ D
    simpa only [Q.discriminant_eq] using Q.toBinaryQuadraticForm.content_sq_dvd_discriminant

end CMClass

/-- Classes whose representatives have content one. -/
@[expose]
def PrimitiveCMClass (D : ℤ) (r : ZMod 12) [Fact (D < 0)] :=
  {C : CMClass D r // CMClass.content C = 1}

namespace LevelSixForm

/-- Forget the level and orientation conditions. -/
def toPositiveForm {D : ℤ} {r : ZMod 12} (Q : LevelSixForm D r) : PositiveForm D where
  toBinaryQuadraticForm := Q.toBinaryQuadraticForm
  a_pos := Q.a_pos
  discriminant_eq := Q.discriminant_eq

@[simp] theorem toPositiveForm_toBinaryQuadraticForm {D : ℤ} {r : ZMod 12}
    (Q : LevelSixForm D r) :
    (Q.toPositiveForm).toBinaryQuadraticForm = Q.toBinaryQuadraticForm := (rfl)

theorem toPositiveForm_injective {D : ℤ} {r : ZMod 12} :
    Function.Injective (toPositiveForm (D := D) (r := r)) := by
  intro Q R h
  apply LevelSixForm.ext
  exact congrArg PositiveForm.toBinaryQuadraticForm h

theorem toPositiveForm_smul {D : ℤ} {r : ZMod 12} [Fact (D < 0)]
    (g : CongruenceSubgroup.Gamma0 6) (Q : LevelSixForm D r) :
    toPositiveForm (g • Q) = g • toPositiveForm Q := by
  apply PositiveForm.ext
  change (toPositiveForm (g • Q)).toBinaryQuadraticForm =
    (((g : Matrix.SpecialLinearGroup (Fin 2) ℤ) • toPositiveForm Q).toBinaryQuadraticForm)
  simp only [toPositiveForm_toBinaryQuadraticForm,
    LevelSixForm.toBinaryQuadraticForm_smul, PositiveForm.toBinaryQuadraticForm_smul]

end LevelSixForm

namespace CMClass

/-- The class map that forgets the preserved level-six conditions. -/
def toPositiveOrbit {D : ℤ} {r : ZMod 12} [Fact (D < 0)] :
    CMClass D r → MulAction.orbitRel.Quotient (CongruenceSubgroup.Gamma0 6) (PositiveForm D) :=
  Quotient.map LevelSixForm.toPositiveForm (by
    intro Q R h
    obtain ⟨g, hg⟩ := h
    refine ⟨g, ?_⟩
    exact (LevelSixForm.toPositiveForm_smul g R).symm.trans
      (congrArg LevelSixForm.toPositiveForm hg))

theorem toPositiveOrbit_injective {D : ℤ} {r : ZMod 12} [Fact (D < 0)] :
    Function.Injective (toPositiveOrbit (D := D) (r := r)) := by
  intro C E h
  induction C using Quotient.inductionOn with
  | h Q =>
    induction E using Quotient.inductionOn with
    | h R =>
      have hr : (MulAction.orbitRel (CongruenceSubgroup.Gamma0 6) (PositiveForm D)).r
          (LevelSixForm.toPositiveForm Q) (LevelSixForm.toPositiveForm R) := Quotient.exact h
      obtain ⟨g, hg⟩ := hr
      apply Quotient.sound
      refine ⟨g, LevelSixForm.toPositiveForm_injective ?_⟩
      rw [LevelSixForm.toPositiveForm_smul]
      exact hg

instance finite {D : ℤ} {r : ZMod 12} [Fact (D < 0)] : Finite (CMClass D r) := by
  exact Finite.of_injective toPositiveOrbit toPositiveOrbit_injective

end CMClass

end SptClassification
