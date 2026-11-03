/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.ClassPolynomials
public import SptClassification.ModularForms.EtaQuotientConjugation

/-!
# Conjugation of oriented CM forms

Reversing the middle coefficient preserves the discriminant and content,
exchanges the level-six orientations `r` and `-r`, and reflects the associated
CM point by `z ↦ -conj z`. This is the form-level operation underlying complex
conjugation of CM values in [rolen2026canonical], Section 4.
-/

public section

namespace SptClassification

namespace BinaryQuadraticForm

/-- Reversal of the middle coefficient of a binary quadratic form. -/
def reverseMiddle (Q : BinaryQuadraticForm) : BinaryQuadraticForm :=
  ⟨Q.a, -Q.b, Q.c⟩

@[simp] theorem reverseMiddle_reverseMiddle (Q : BinaryQuadraticForm) :
    Q.reverseMiddle.reverseMiddle = Q := by
  ext <;> simp [reverseMiddle]

@[simp] theorem discriminant_reverseMiddle (Q : BinaryQuadraticForm) :
    Q.reverseMiddle.discriminant = Q.discriminant := by
  simp [reverseMiddle, discriminant]

@[simp] theorem content_reverseMiddle (Q : BinaryQuadraticForm) :
    Q.reverseMiddle.content = Q.content := by
  simp [reverseMiddle, content_eq_gcd]

/-- Conjugation of a change-of-variables matrix by `diag(1, -1)`. -/
def reverseMiddleMatrix (M : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  fun i j => if i = j then M i j else -M i j

@[simp] theorem reverseMiddleMatrix_det (M : Matrix (Fin 2) (Fin 2) ℤ) :
    (reverseMiddleMatrix M).det = M.det := by
  simp [reverseMiddleMatrix, Matrix.det_fin_two]

@[simp] theorem reverseMiddleMatrix_one :
    reverseMiddleMatrix (1 : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [reverseMiddleMatrix]

theorem reverseMiddleMatrix_mul (M N : Matrix (Fin 2) (Fin 2) ℤ) :
    reverseMiddleMatrix (M * N) = reverseMiddleMatrix M * reverseMiddleMatrix N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reverseMiddleMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

@[simp] theorem reverseMiddleMatrix_adjugate (M : Matrix (Fin 2) (Fin 2) ℤ) :
    reverseMiddleMatrix M.adjugate = (reverseMiddleMatrix M).adjugate := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reverseMiddleMatrix, Matrix.adjugate_fin_two]

/-- The determinant-one change of variables induced by middle-coefficient reversal. -/
def reverseMiddleSL : Matrix.SpecialLinearGroup (Fin 2) ℤ →*
    Matrix.SpecialLinearGroup (Fin 2) ℤ where
  toFun g := ⟨reverseMiddleMatrix g, by simp [g.property]⟩
  map_one' := by
    apply Subtype.ext
    exact reverseMiddleMatrix_one
  map_mul' g h := by
    apply Subtype.ext
    exact reverseMiddleMatrix_mul g h

@[simp] theorem reverseMiddleSL_coe (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ((reverseMiddleSL g : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
      Matrix (Fin 2) (Fin 2) ℤ) = reverseMiddleMatrix g := (rfl)

/-- Reflection preserves the level-six congruence subgroup. -/
def reverseMiddleGamma0 (g : CongruenceSubgroup.Gamma0 6) :
    CongruenceSubgroup.Gamma0 6 :=
  ⟨reverseMiddleSL g, by
    simpa [reverseMiddleMatrix] using congrArg Neg.neg g.property⟩

@[simp] theorem reverseMiddle_pullback (Q : BinaryQuadraticForm)
    (M : Matrix (Fin 2) (Fin 2) ℤ) :
    (Q.pullback M).reverseMiddle = Q.reverseMiddle.pullback (reverseMiddleMatrix M) := by
  ext <;> simp [pullback, reverseMiddle, reverseMiddleMatrix] ; ring

end BinaryQuadraticForm

namespace LevelSixForm

/-- Middle-coefficient reversal exchanges the two opposite orientations. -/
def reverseMiddle {D : ℤ} {r : ZMod 12} (Q : LevelSixForm D r) :
    LevelSixForm D (-r) where
  toBinaryQuadraticForm := Q.toBinaryQuadraticForm.reverseMiddle
  a_pos := Q.a_pos
  discriminant_eq := by simpa using Q.discriminant_eq
  six_dvd_a := Q.six_dvd_a
  b_residue := by
    simpa [BinaryQuadraticForm.reverseMiddle] using congrArg Neg.neg Q.b_residue

@[simp] theorem reverseMiddle_toBinaryQuadraticForm {D : ℤ} {r : ZMod 12}
    (Q : LevelSixForm D r) :
    Q.reverseMiddle.toBinaryQuadraticForm = Q.toBinaryQuadraticForm.reverseMiddle := (rfl)

@[simp] theorem reverseMiddle_reverseMiddle {D : ℤ} {r : ZMod 12}
    (Q : LevelSixForm D r) :
    Q.reverseMiddle.reverseMiddle.toBinaryQuadraticForm = Q.toBinaryQuadraticForm :=
  Q.toBinaryQuadraticForm.reverseMiddle_reverseMiddle

theorem toBinaryQuadraticForm_cast {D : ℤ} {s t : ZMod 12}
    (h : s = t) (Q : LevelSixForm D s) :
    (h ▸ Q).toBinaryQuadraticForm = Q.toBinaryQuadraticForm := by
  cases h
  rfl

theorem reverseMiddle_involutive {D : ℤ} {r : ZMod 12}
    (Q : LevelSixForm D r) : (neg_neg r) ▸ Q.reverseMiddle.reverseMiddle = Q := by
  apply LevelSixForm.ext
  rw [toBinaryQuadraticForm_cast]
  exact Q.reverseMiddle_reverseMiddle

@[simp] theorem reverseMiddle_content {D : ℤ} {r : ZMod 12}
    (Q : LevelSixForm D r) :
    Q.reverseMiddle.toBinaryQuadraticForm.content = Q.toBinaryQuadraticForm.content :=
  Q.toBinaryQuadraticForm.content_reverseMiddle

/-- Reflection intertwines the two oriented `Γ₀(6)` actions. -/
theorem reverseMiddle_smul {D : ℤ} {r : ZMod 12} [Fact (D < 0)]
    (g : CongruenceSubgroup.Gamma0 6) (Q : LevelSixForm D r) :
    (g • Q).reverseMiddle = BinaryQuadraticForm.reverseMiddleGamma0 g • Q.reverseMiddle := by
  apply LevelSixForm.ext
  simp only [reverseMiddle_toBinaryQuadraticForm, LevelSixForm.toBinaryQuadraticForm_smul]
  simp [BinaryQuadraticForm.transform, BinaryQuadraticForm.reverseMiddle_pullback,
    BinaryQuadraticForm.reverseMiddleGamma0, BinaryQuadraticForm.reverseMiddleSL_coe]

/-- Reversal of the middle coefficient reflects the upper-half-plane CM point. -/
theorem cmPoint_reverseMiddle {D : ℤ} {r : ZMod 12} [Fact (D < 0)]
    (Q : LevelSixForm D r) :
    (Q.reverseMiddle.cmPoint : ℂ) = -star (Q.cmPoint : ℂ) := by
  apply Complex.ext
  · simp [LevelSixForm.cmPoint_re, reverseMiddle,
      BinaryQuadraticForm.reverseMiddle]
    ring
  · simp [LevelSixForm.cmPoint_im, reverseMiddle,
      BinaryQuadraticForm.reverseMiddle]

end LevelSixForm

namespace CMClass

theorem cast_mk {D : ℤ} {s t : ZMod 12} [Fact (D < 0)]
    (h : s = t) (Q : LevelSixForm D s) :
    (h ▸ (Quotient.mk _ Q : CMClass D s)) =
      (Quotient.mk _ (h ▸ Q) : CMClass D t) := by
  cases h
  rfl

/-- The class of a reflected form, with the opposite level-six orientation. -/
def reverseMiddle {D : ℤ} {r : ZMod 12} [Fact (D < 0)] :
    CMClass D r → CMClass D (-r) :=
  Quotient.map LevelSixForm.reverseMiddle (by
    intro Q R h
    obtain ⟨g, hg⟩ := h
    exact ⟨BinaryQuadraticForm.reverseMiddleGamma0 g,
      (LevelSixForm.reverseMiddle_smul g R).symm.trans
        (congrArg LevelSixForm.reverseMiddle hg)⟩)

@[simp] theorem reverseMiddle_mk {D : ℤ} {r : ZMod 12} [Fact (D < 0)]
    (Q : LevelSixForm D r) :
    reverseMiddle (Quotient.mk _ Q : CMClass D r) =
      (Quotient.mk _ Q.reverseMiddle : CMClass D (-r)) := (rfl)

@[simp] theorem content_reverseMiddle {D : ℤ} {r : ZMod 12} [Fact (D < 0)]
    (C : CMClass D r) : content C.reverseMiddle = content C := by
  induction C using Quotient.inductionOn with
  | h Q => simpa only [reverseMiddle_mk, content_mk] using Q.reverseMiddle_content

theorem reverseMiddle_involutive {D : ℤ} {r : ZMod 12} [Fact (D < 0)]
    (C : CMClass D r) : (neg_neg r) ▸ C.reverseMiddle.reverseMiddle = C := by
  induction C using Quotient.inductionOn with
  | h Q =>
    change (neg_neg r) ▸
      (Quotient.mk _ Q.reverseMiddle.reverseMiddle : CMClass D (-(-r))) =
      (Quotient.mk _ Q : CMClass D r)
    exact (cast_mk (neg_neg r) Q.reverseMiddle.reverseMiddle).trans
      (congrArg (fun P : LevelSixForm D r => (Quotient.mk _ P : CMClass D r))
        Q.reverseMiddle_involutive)

/-- Reflection conjugates the value of the actual eta quotient on an oriented
CM class. -/
theorem etaValue_reverseMiddle {D : ℤ} {r : ZMod 12} [Fact (D < 0)]
    (C : CMClass D r) : C.reverseMiddle.etaValue = star C.etaValue := by
  induction C using Quotient.inductionOn with
  | h Q =>
    simp only [reverseMiddle_mk, etaValue_mk]
    rw [LevelSixForm.cmPoint_reverseMiddle]
    exact levelSixEtaQuotient_neg_star Q.cmPoint

end CMClass

/-- Reflection restricts to primitive oriented CM classes. -/
def primitiveCMClassReverseMiddle {D : ℤ} {r : ZMod 12} [Fact (D < 0)]
    (C : PrimitiveCMClass D r) : PrimitiveCMClass D (-r) :=
  ⟨C.val.reverseMiddle, by simpa using C.property⟩

theorem primitiveCMClassReverseMiddle_etaValue {D : ℤ} {r : ZMod 12}
    [Fact (D < 0)] (C : PrimitiveCMClass D r) :
    (primitiveCMClassReverseMiddle C).val.etaValue = star C.val.etaValue :=
  C.val.etaValue_reverseMiddle

theorem primitiveCMClass_cast_val {D : ℤ} {s t : ZMod 12}
    [Fact (D < 0)] (h : s = t) (C : PrimitiveCMClass D s) :
    (h ▸ C).val = h ▸ C.val := by
  cases h
  rfl

/-- Reversing the middle coefficient twice returns the original primitive class. -/
theorem primitiveCMClassReverseMiddle_involutive {D : ℤ} {r : ZMod 12}
    [Fact (D < 0)] (C : PrimitiveCMClass D r) :
    (neg_neg r) ▸ primitiveCMClassReverseMiddle
      (primitiveCMClassReverseMiddle C) = C := by
  apply Subtype.ext
  rw [primitiveCMClass_cast_val]
  exact CMClass.reverseMiddle_involutive C.val

theorem primitiveCMClassReverseMiddle_cast {D : ℤ} {s t : ZMod 12}
    [Fact (D < 0)] (h : s = t) (C : PrimitiveCMClass D s) :
    primitiveCMClassReverseMiddle (h ▸ C) =
      (congrArg Neg.neg h) ▸ primitiveCMClassReverseMiddle C := by
  cases h
  rfl

/-- Reflection is an equivalence between opposite primitive CM orientations. -/
def primitiveCMClassReverseMiddleEquiv (D : ℤ) (r : ZMod 12)
    [Fact (D < 0)] : PrimitiveCMClass D r ≃ PrimitiveCMClass D (-r) where
  toFun := primitiveCMClassReverseMiddle
  invFun C := (neg_neg r) ▸ primitiveCMClassReverseMiddle C
  left_inv := primitiveCMClassReverseMiddle_involutive
  right_inv := by
    intro C
    rw [primitiveCMClassReverseMiddle_cast]
    exact primitiveCMClassReverseMiddle_involutive C

theorem primitiveCMClassReverseMiddleEquiv_apply (D : ℤ) (r : ZMod 12)
    [Fact (D < 0)] (C : PrimitiveCMClass D r) :
    (primitiveCMClassReverseMiddleEquiv D r) C = primitiveCMClassReverseMiddle C := (rfl)

end SptClassification
