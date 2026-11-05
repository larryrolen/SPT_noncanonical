/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.PositiveForms
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Tactic.LinearCombination

/-! # Actual positive integral forms with level-six orientation

We follow [ahlgrenAndersen2016], section 2.1.
-/

@[expose] public section

namespace SptClassification

/-- All positive integral forms with the prescribed level-six orientation.
No condition on the content is imposed. -/
structure LevelSixForm (D : ℤ) (r : ZMod 12) extends BinaryQuadraticForm where
  a_pos : 0 < a
  discriminant_eq : toBinaryQuadraticForm.discriminant = D
  six_dvd_a : 6 ∣ a
  b_residue : (b : ZMod 12) = r

namespace BinaryQuadraticForm

theorem six_dvd_pullback_a (Q : BinaryQuadraticForm)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hQ : 6 ∣ Q.a) (hM : 6 ∣ M 1 0) :
    6 ∣ (Q.pullback M).a := by
  obtain ⟨a, ha⟩ := hQ
  obtain ⟨m, hm⟩ := hM
  refine ⟨a * M 0 0 ^ 2 + Q.b * M 0 0 * m + 6 * Q.c * m ^ 2, ?_⟩
  simp only [pullback, ha, hm]
  ring

theorem twelve_dvd_pullback_b_sub (Q : BinaryQuadraticForm)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hQ : 6 ∣ Q.a) (hM : 6 ∣ M 1 0)
    (hdet : M.det = 1) : 12 ∣ (Q.pullback M).b - Q.b := by
  obtain ⟨a, ha⟩ := hQ
  obtain ⟨m, hm⟩ := hM
  refine ⟨a * M 0 0 * M 0 1 + Q.b * M 0 1 * m + Q.c * m * M 1 1, ?_⟩
  rw [Matrix.det_fin_two, hm] at hdet
  simp only [pullback, ha, hm]
  linear_combination Q.b * hdet

theorem pullback_b_residue (Q : BinaryQuadraticForm)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hQ : 6 ∣ Q.a) (hM : 6 ∣ M 1 0)
    (hdet : M.det = 1) : ((Q.pullback M).b : ZMod 12) = Q.b := by
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd ((Q.pullback M).b - Q.b) 12).mpr
    (Q.twelve_dvd_pullback_b_sub M hQ hM hdet)
  rw [Int.cast_sub] at h
  exact sub_eq_zero.mp h

end BinaryQuadraticForm

namespace LevelSixForm

@[ext] theorem ext {D : ℤ} {r : ZMod 12} {Q R : LevelSixForm D r}
    (h : Q.toBinaryQuadraticForm = R.toBinaryQuadraticForm) : Q = R := by
  cases Q
  cases R
  cases h
  rfl

/-- The action with the negative-discriminant hypothesis made explicit. -/
def transform {D : ℤ} {r : ZMod 12} (hD : D < 0)
    (g : CongruenceSubgroup.Gamma0 6) (Q : LevelSixForm D r) : LevelSixForm D r := by
  let M : Matrix.SpecialLinearGroup (Fin 2) ℤ := (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)⁻¹
  have hM : 6 ∣ M 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (M 1 0) 6).mp
    (show (M 1 0 : ZMod 6) = 0 from (g⁻¹).property)
  refine {
    toBinaryQuadraticForm := Q.toBinaryQuadraticForm.pullback (M : Matrix (Fin 2) (Fin 2) ℤ)
    a_pos := Q.toBinaryQuadraticForm.pullback_a_pos Q.a_pos (Q.discriminant_eq.trans_lt hD) _ M.property
    discriminant_eq := ?_
    six_dvd_a := Q.toBinaryQuadraticForm.six_dvd_pullback_a _ Q.six_dvd_a hM
    b_residue := (Q.toBinaryQuadraticForm.pullback_b_residue _ Q.six_dvd_a hM M.property).trans Q.b_residue }
  rw [BinaryQuadraticForm.discriminant_pullback, M.property, one_pow, one_mul]
  exact Q.discriminant_eq

@[simp] theorem toBinaryQuadraticForm_transform {D : ℤ} {r : ZMod 12} (hD : D < 0)
    (g : CongruenceSubgroup.Gamma0 6) (Q : LevelSixForm D r) :
    (transform hD g Q).toBinaryQuadraticForm =
      BinaryQuadraticForm.transform g Q.toBinaryQuadraticForm := (rfl)

@[simp] theorem transform_one {D : ℤ} {r : ZMod 12} (hD : D < 0)
    (Q : LevelSixForm D r) : transform hD 1 Q = Q := by
  apply LevelSixForm.ext
  rw [toBinaryQuadraticForm_transform]
  exact BinaryQuadraticForm.transform_one Q.toBinaryQuadraticForm

theorem transform_mul {D : ℤ} {r : ZMod 12} (hD : D < 0)
    (g h : CongruenceSubgroup.Gamma0 6) (Q : LevelSixForm D r) :
    transform hD (g * h) Q = transform hD g (transform hD h Q) := by
  apply LevelSixForm.ext
  simpa only [toBinaryQuadraticForm_transform, Subgroup.coe_mul] using
    BinaryQuadraticForm.transform_mul
      (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)
      (h : Matrix.SpecialLinearGroup (Fin 2) ℤ) Q.toBinaryQuadraticForm

instance gammaZeroAction {D : ℤ} {r : ZMod 12} [Fact (D < 0)] :
    MulAction (CongruenceSubgroup.Gamma0 6) (LevelSixForm D r) where
  smul := transform Fact.out
  one_smul := transform_one Fact.out
  mul_smul := transform_mul Fact.out

@[simp] theorem toBinaryQuadraticForm_smul {D : ℤ} {r : ZMod 12} [Fact (D < 0)]
    (g : CongruenceSubgroup.Gamma0 6) (Q : LevelSixForm D r) :
    (g • Q).toBinaryQuadraticForm = BinaryQuadraticForm.transform g Q.toBinaryQuadraticForm := by
  change (transform Fact.out g Q).toBinaryQuadraticForm = _
  exact toBinaryQuadraticForm_transform Fact.out g Q

theorem content_smul {D : ℤ} {r : ZMod 12} [Fact (D < 0)]
    (g : CongruenceSubgroup.Gamma0 6) (Q : LevelSixForm D r) :
    (g • Q).toBinaryQuadraticForm.content = Q.toBinaryQuadraticForm.content := by
  rw [toBinaryQuadraticForm_smul, BinaryQuadraticForm.content_transform]

end LevelSixForm

end SptClassification
