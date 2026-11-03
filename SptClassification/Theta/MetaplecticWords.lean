/- Assembled by AxiomProver. -/

module

public import SptClassification.Theta.WeilCubicRelation
public import SptClassification.Theta.EtaWeilAutomorphyGroup

/-!
# Matrices and square roots for eta–Weil generator words

The generated automorphy data are attached to actual integral determinant-one
matrices. Their ordered factor squares to the denominator of the fractional
linear action. This makes the standard metaplectic lifts in
[rolenManuscript, lines 339–343] explicit.
-/

public section

namespace SptClassification
namespace Theta

/-- The integral matrix of a standard inversion or translation step. -/
def EtaWeilStep.matrix : EtaWeilStep → Matrix.SpecialLinearGroup (Fin 2) ℤ
  | .inversion => ModularGroup.S
  | .translation n => ⟨!![1, n; 0, 1], by norm_num [Matrix.det_fin_two]⟩

@[simp] theorem EtaWeilStep.matrix_inversion :
    EtaWeilStep.inversion.matrix = ModularGroup.S := (rfl)

@[simp] theorem EtaWeilStep.matrix_translation_one :
    (EtaWeilStep.translation 1).matrix = ModularGroup.T := (rfl)

@[simp] theorem EtaWeilStep.matrix_translation_zero :
    (EtaWeilStep.translation 0).matrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [EtaWeilStep.matrix]

@[simp] theorem EtaWeilStep.matrix_translation_apply (n : ℤ) (i j : Fin 2) :
    (EtaWeilStep.translation n).matrix i j = !![1, n; 0, 1] i j := (rfl)

/-- The linear denominator `cτ+d` of an integral determinant-one matrix. -/
noncomputable def metaplecticDenominator
    (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane) : ℂ :=
  (g 1 0 : ℂ) * (z : ℂ) + (g 1 1 : ℂ)

/-- Compatibility with the denominator used by analytic modular forms. -/
theorem metaplecticDenominator_eq_denom
    (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane) :
    metaplecticDenominator g z =
      UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ g) z := (rfl)

@[simp] theorem metaplecticDenominator_one (z : UpperHalfPlane) :
    metaplecticDenominator 1 z = 1 := by
  simp [metaplecticDenominator]

/-- Each chosen generator factor squares to its matrix denominator. -/
theorem EtaWeilStep.factor_sq (g : EtaWeilStep) (z : UpperHalfPlane) :
    g.factor z ^ 2 = metaplecticDenominator g.matrix z := by
  cases g with
  | inversion =>
      simp [EtaWeilStep.factor_inversion, EtaWeilStep.matrix,
        metaplecticDenominator, complex_sqrt_sq, ModularGroup.S]
  | translation n =>
      simp [EtaWeilStep.factor_translation, EtaWeilStep.matrix,
        metaplecticDenominator]

/-- A generator's concrete matrix has the action used in its eta formula. -/
theorem EtaWeilStep.matrix_smul (g : EtaWeilStep) (z : UpperHalfPlane) :
    g.matrix • z = g.act z := by
  cases g with
  | inversion => simp only [EtaWeilStep.matrix, EtaWeilStep.act_inversion]
  | translation n =>
      apply UpperHalfPlane.ext
      rw [UpperHalfPlane.coe_specialLinearGroup_apply]
      simp [EtaWeilStep.matrix, EtaWeilStep.act_translation,
        UpperHalfPlane.coe_vadd, add_comm]

/-- Multiply the matrices in the same order as the finite Weil operators. -/
def etaWeilWordMatrix : List EtaWeilStep → Matrix.SpecialLinearGroup (Fin 2) ℤ
  | [] => 1
  | g :: w => g.matrix * etaWeilWordMatrix w

@[simp] theorem etaWeilWordMatrix_nil : etaWeilWordMatrix [] = 1 := (rfl)

@[simp] theorem etaWeilWordMatrix_cons (g : EtaWeilStep) (w : List EtaWeilStep) :
    etaWeilWordMatrix (g :: w) = g.matrix * etaWeilWordMatrix w := (rfl)

/-- Four inversion matrices multiply to the identity. -/
theorem etaWeilInversionFour_matrix_eq_one :
    etaWeilWordMatrix (List.replicate 4 EtaWeilStep.inversion) = 1 := by
  decide +kernel

/-- The word's upper-half-plane action is its fractional linear matrix action. -/
theorem etaWeilWordMatrix_smul (w : List EtaWeilStep) (z : UpperHalfPlane) :
    etaWeilWordMatrix w • z = etaWeilWordAction w z := by
  induction w with
  | nil => simp only [etaWeilWordMatrix_nil, etaWeilWordAction_nil, one_smul]
  | cons g w ih =>
      simp only [etaWeilWordMatrix_cons, etaWeilWordAction_cons, mul_smul, ih]
      exact g.matrix_smul _

/-- The matrix denominator obeys the metaplectic cocycle. -/
theorem metaplecticDenominator_mul
    (g h : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane)
    (hden : metaplecticDenominator h z ≠ 0) :
    metaplecticDenominator (g * h) z =
      metaplecticDenominator g (h • z) * metaplecticDenominator h z := by
  have hact : ((h • z : UpperHalfPlane) : ℂ) =
      ((h 0 0 : ℂ) * (z : ℂ) + (h 0 1 : ℂ)) /
        metaplecticDenominator h z := by
    simpa [metaplecticDenominator] using
      (UpperHalfPlane.coe_specialLinearGroup_apply h z)
  rw [metaplecticDenominator, metaplecticDenominator, hact]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
    Fin.sum_univ_two]
  dsimp only [metaplecticDenominator] at hden ⊢
  push_cast
  field_simp [hden]
  ring

/-- The ordered factor of a word squares to its matrix denominator. -/
theorem etaWeilWordFactor_sq (w : List EtaWeilStep) (z : UpperHalfPlane) :
    etaWeilWordFactor w z ^ 2 =
      metaplecticDenominator (etaWeilWordMatrix w) z := by
  induction w generalizing z with
  | nil => simp only [etaWeilWordFactor_nil, etaWeilWordMatrix_nil,
      one_pow, metaplecticDenominator_one]
  | cons g w ih =>
      have hden : metaplecticDenominator (etaWeilWordMatrix w) z ≠ 0 := by
        rw [← ih]
        exact pow_ne_zero _ (etaWeilWordFactor_ne_zero w z)
      rw [etaWeilWordFactor_cons, etaWeilWordMatrix_cons,
        metaplecticDenominator_mul _ _ z hden,
        etaWeilWordMatrix_smul]
      rw [mul_pow, g.factor_sq, ih]

end Theta
end SptClassification
