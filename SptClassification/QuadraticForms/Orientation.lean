/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.LevelSixClasses
public import SptClassification.QuadraticForms.FormClasses

/-!
# Forgetting a level-six orientation

For a unit middle-coefficient residue, a proper equivalence between two forms
with the same orientation already lies in Γ₀(6). This gives injectivity of the
oriented class map into the full proper class space.
-/

public section

namespace SptClassification

namespace BinaryQuadraticForm

/-- A determinant-one substitution preserving level and a unit orientation has
lower-left entry divisible by six. -/
theorem six_dvd_lower_left_of_orientation (Q : BinaryQuadraticForm)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M.det = 1)
    (hlevel : 6 ∣ Q.a) (hlevel' : 6 ∣ (Q.pullback M).a)
    (horientation : 12 ∣ (Q.pullback M).b - Q.b) (hunit : IsUnit (Q.b : ZMod 6)) :
    6 ∣ M 1 0 := by
  have hid : 2 * Q.b * M 1 0 =
      2 * M 1 1 * (Q.pullback M).a - M 1 0 * ((Q.pullback M).b - Q.b) - 2 * Q.a * M 0 0 := by
    rw [Matrix.det_fin_two] at hdet
    simp only [pullback]
    linear_combination -(2 * Q.a * M 0 0 + Q.b * M 1 0) * hdet
  have hdiv : 6 ∣ Q.b * M 1 0 := by
    obtain ⟨a, ha⟩ := hlevel
    obtain ⟨a', ha'⟩ := hlevel'
    obtain ⟨b, hb⟩ := horientation
    refine ⟨M 1 1 * a' - M 1 0 * b - a * M 0 0, ?_⟩
    rw [ha, ha', hb] at hid
    nlinarith only [hid]
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd (M 1 0) 6).mp
  apply hunit.mul_left_cancel
  rw [mul_zero]
  simpa only [Int.cast_mul] using (ZMod.intCast_zmod_eq_zero_iff_dvd (Q.b * M 1 0) 6).mpr hdiv

end BinaryQuadraticForm

namespace LevelSixForm

theorem middle_isUnit_mod_six {D : ℤ} {r : ZMod 12} (Q : LevelSixForm D r) (hr : IsUnit r) :
    IsUnit (Q.b : ZMod 6) := by
  have h12 : IsUnit (Q.b : ZMod 12) := Q.b_residue.symm ▸ hr
  simpa only [map_intCast] using h12.map (ZMod.castHom (by decide : 6 ∣ 12) (ZMod 6))

/-- A proper equivalence respecting a fixed unit orientation belongs to Γ₀(6). -/
theorem equivalence_mem_gamma0 {D : ℤ} {r : ZMod 12} (Q R : LevelSixForm D r)
    (hr : IsUnit r) (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (h : BinaryQuadraticForm.transform g R.toBinaryQuadraticForm = Q.toBinaryQuadraticForm) :
    g ∈ CongruenceSubgroup.Gamma0 6 := by
  let M : Matrix (Fin 2) (Fin 2) ℤ := (g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
  have hlevel : 6 ∣ (R.toBinaryQuadraticForm.pullback M).a := by
    change 6 ∣ (BinaryQuadraticForm.transform g R.toBinaryQuadraticForm).a
    rw [h]
    exact Q.six_dvd_a
  have horientation : 12 ∣ (R.toBinaryQuadraticForm.pullback M).b - R.b := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 12).mp
    rw [Int.cast_sub]
    change ((BinaryQuadraticForm.transform g R.toBinaryQuadraticForm).b : ZMod 12) - (R.b : ZMod 12) = 0
    rw [h, Q.b_residue, R.b_residue, sub_self]
  have hM := R.toBinaryQuadraticForm.six_dvd_lower_left_of_orientation M (g⁻¹).property
    R.six_dvd_a hlevel horientation (R.middle_isUnit_mod_six hr)
  have hinv : g⁻¹ ∈ CongruenceSubgroup.Gamma0 6 := by
    change ((g⁻¹ 1 0 : ℤ) : ZMod 6) = 0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 6).mpr hM
  simpa only [inv_inv] using (CongruenceSubgroup.Gamma0 6).inv_mem hinv

end LevelSixForm

namespace CMClass

/-- Forget the level and middle-coefficient orientation on a proper CM class. -/
def toFormClass {D : ℤ} {r : ZMod 12} [Fact (D < 0)] : CMClass D r → FormClass D :=
  Quotient.map LevelSixForm.toPositiveForm (by
    intro Q R h
    obtain ⟨g, hg⟩ := h
    refine ⟨(g : Matrix.SpecialLinearGroup (Fin 2) ℤ), ?_⟩
    exact (LevelSixForm.toPositiveForm_smul g R).symm.trans
      (congrArg LevelSixForm.toPositiveForm hg))

@[simp] theorem toFormClass_mk {D : ℤ} {r : ZMod 12} [Fact (D < 0)]
    (Q : LevelSixForm D r) :
    toFormClass (Quotient.mk _ Q) = Quotient.mk _ Q.toPositiveForm := (rfl)

theorem content_toFormClass {D : ℤ} {r : ZMod 12} [Fact (D < 0)] (C : CMClass D r) :
    (toFormClass C).content = C.content := by
  induction C using Quotient.inductionOn with
  | h Q =>
    change (FormClass.content (Quotient.mk _ Q.toPositiveForm)) =
      CMClass.content (Quotient.mk _ Q)
    simp only [FormClass.content_mk, CMClass.content_mk,
      LevelSixForm.toPositiveForm_toBinaryQuadraticForm]

theorem toFormClass_injective {D : ℤ} {r : ZMod 12} [Fact (D < 0)] (hr : IsUnit r) :
    Function.Injective (toFormClass (D := D) (r := r)) := by
  intro C E h
  induction C using Quotient.inductionOn with
  | h Q =>
    induction E using Quotient.inductionOn with
    | h R =>
      change Quotient.mk _ Q.toPositiveForm = Quotient.mk _ R.toPositiveForm at h
      obtain ⟨g, hg⟩ := Quotient.exact h
      have hraw : BinaryQuadraticForm.transform g R.toBinaryQuadraticForm = Q.toBinaryQuadraticForm :=
        by simpa only [PositiveForm.toBinaryQuadraticForm_smul,
          LevelSixForm.toPositiveForm_toBinaryQuadraticForm] using
            congrArg PositiveForm.toBinaryQuadraticForm hg
      let g0 : CongruenceSubgroup.Gamma0 6 := ⟨g, Q.equivalence_mem_gamma0 R hr g hraw⟩
      apply Quotient.sound
      refine ⟨g0, ?_⟩
      apply LevelSixForm.ext
      simpa only [LevelSixForm.toBinaryQuadraticForm_smul] using hraw

end CMClass

end SptClassification
