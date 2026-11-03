/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.EtaQuotientCuspsThirdExpansion
public import SptClassification.ModularForms.PositiveCuspMatrix
public import SptClassification.Theta.Lattice

/-!
# Nome charts at the three finite cusps of level six

The width-three parameter is built into the half and third approaches.
The weight-four slash includes the square of the rational matrix
determinant. These charts are used to specialize the isotropic-cusp
expansion of [borcherds1998, Theorem 14.3(5), PDF p. 56].
-/

public section

namespace SptClassification

/-- The three finite cusps of `X₀(6)`. -/
inductive FiniteLevelSixCusp where
  | zero
  | half
  | third

namespace FiniteLevelSixCusp

open OnePoint

/-- A rational cusp chart matrix, recorded by its four integral entries. -/
structure ChartMatrix where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ

/-- The matrices used by the three local nome charts. The width-three
parameter has already been absorbed into the half and third matrices. -/
def chartMatrix : FiniteLevelSixCusp → ChartMatrix
  | .zero => ⟨0, -1, 6, 0⟩
  | .half => ⟨3, 0, 6, 1⟩
  | .third => ⟨6, 1, 18, 6⟩

/-- Atkin–Lehner matrices taking infinity to the corresponding finite cusp.
The half and third nome charts differ from these by translation by `-1/3`;
the third chart also uses a scalar multiple of its matrix. -/
def atkinLehnerMatrix : FiniteLevelSixCusp → ChartMatrix
  | .zero => ⟨0, -1, 6, 0⟩
  | .half => ⟨3, 1, 6, 3⟩
  | .third => ⟨2, 1, 6, 4⟩

/-- Eigenvalues of the distinguished Weil vector under these three
Atkin–Lehner substitutions, in cusp order. -/
def atkinSign : FiniteLevelSixCusp → ℤ
  | .zero => 1
  | .half => -1
  | .third => -1

def ChartMatrix.det (M : ChartMatrix) : ℤ := M.a * M.d - M.b * M.c

def ChartMatrix.denominator (M : ChartMatrix) (z : UpperHalfPlane) : ℂ :=
  (M.c : ℂ) * z + M.d

noncomputable def ChartMatrix.act (M : ChartMatrix) (z : UpperHalfPlane) : ℂ :=
  ((M.a : ℂ) * z + M.b) / M.denominator z

/-- The width-three nome charts use an ordinary translate of the high cusp. -/
noncomputable def widthThreeShift (z : UpperHalfPlane) : UpperHalfPlane :=
  ⟨(z : ℂ) - 1 / 3, by simpa using z.im_pos⟩

@[simp] theorem widthThreeShift_coe (z : UpperHalfPlane) :
    (widthThreeShift z : ℂ) = (z : ℂ) - 1 / 3 := (rfl)

/-- The exact Atkin–Lehner determinant in each finite chart. -/
theorem atkinLehnerMatrix_det (c : FiniteLevelSixCusp) :
    c.atkinLehnerMatrix.det = match c with
      | .zero => 6
      | .half => 3
      | .third => 2 := by
  cases c <;> norm_num [atkinLehnerMatrix, ChartMatrix.det]

theorem chartMatrix_det : ∀ c : FiniteLevelSixCusp,
    c.chartMatrix.det = match c with
      | .zero => 6
      | .half => 3
      | .third => 18 := by
  intro c
  cases c <;> norm_num [chartMatrix, ChartMatrix.det]

/-- The same positive matrices as genuine real `GL₂` elements, for Mathlib's
cusp action and slash operator. -/
noncomputable def chartGL : FiniteLevelSixCusp → GL (Fin 2) ℝ
  | .zero => PositiveCuspAction.positiveMatrix 0 (-1) 6 0 (by norm_num)
  | .half => PositiveCuspAction.positiveMatrix 3 0 6 1 (by norm_num)
  | .third => PositiveCuspAction.positiveMatrix 6 1 18 6 (by norm_num)

theorem chartGL_det_pos (c : FiniteLevelSixCusp) : 0 < c.chartGL.det.val := by
  cases c <;> norm_num [chartGL]

theorem chartGL_det (c : FiniteLevelSixCusp) :
    c.chartGL.det.val = (c.chartMatrix.det : ℝ) := by
  cases c <;> norm_num [chartGL, chartMatrix, ChartMatrix.det]

theorem chartGL_denominator (c : FiniteLevelSixCusp) (z : UpperHalfPlane) :
    UpperHalfPlane.denom c.chartGL z = c.chartMatrix.denominator z := by
  cases c <;> simp [chartGL, chartMatrix, ChartMatrix.denominator]

/-- Explicit denominators of the three normalized cusp matrices. -/
theorem chartMatrix_denominator (c : FiniteLevelSixCusp)
    (z : UpperHalfPlane) :
    c.chartMatrix.denominator z = match c with
      | .zero => 6 * (z : ℂ)
      | .half => 6 * (z : ℂ) + 1
      | .third => 18 * (z : ℂ) + 6 := by
  cases c <;> simp [chartMatrix, ChartMatrix.denominator]

/-- Rational representatives of the three finite cusps. -/
def rationalPoint : FiniteLevelSixCusp → ℚ
  | .zero => 0
  | .half => 1 / 2
  | .third => 1 / 3

@[simp] theorem rationalPoint_zero :
    FiniteLevelSixCusp.zero.rationalPoint = 0 := (rfl)

@[simp] theorem rationalPoint_half :
    FiniteLevelSixCusp.half.rationalPoint = 1 / 2 := (rfl)

@[simp] theorem rationalPoint_third :
    FiniteLevelSixCusp.third.rationalPoint = 1 / 3 := (rfl)

/-- Primitive isotropic vectors in the lattice `Q(a,b,c) = 6b²-ac`.
The associated quadratic `6cτ²+12bτ+a` has its double root at the
corresponding rational cusp. -/
def isotropicVector : FiniteLevelSixCusp → Theta.Lattice
  | .zero => ⟨0, 0, 1⟩
  | .half => ⟨3, -1, 2⟩
  | .third => ⟨2, -1, 3⟩

theorem isotropicVector_norm_zero (c : FiniteLevelSixCusp) :
    Theta.integralQuadratic c.isotropicVector = 0 := by
  cases c <;> norm_num [isotropicVector, Theta.integralQuadratic]

theorem isotropicVector_primitive (c : FiniteLevelSixCusp) :
    ((c.isotropicVector.a.natAbs.gcd c.isotropicVector.b.natAbs).gcd
      c.isotropicVector.c.natAbs) = 1 := by
  cases c <;> norm_num [isotropicVector]

theorem isotropicVector_root (c : FiniteLevelSixCusp) :
    6 * (c.isotropicVector.c : ℚ) * c.rationalPoint ^ 2 +
      12 * (c.isotropicVector.b : ℚ) * c.rationalPoint +
        (c.isotropicVector.a : ℚ) = 0 := by
  cases c <;> norm_num [isotropicVector, rationalPoint]

/-- The orthogonal cusp quadratic is the square of the vanishing linear
form for the corresponding rational chart. The determinant is the exact
normalization relating the primitive lattice vector to that chart. -/
theorem isotropicQuadratic_chartMatrix (c : FiniteLevelSixCusp) (x : ℚ) :
    (c.chartMatrix.det : ℚ) *
      (6 * (c.isotropicVector.c : ℚ) * x ^ 2 +
        12 * (c.isotropicVector.b : ℚ) * x +
          (c.isotropicVector.a : ℚ)) =
        ((c.chartMatrix.c : ℚ) * x - c.chartMatrix.a) ^ 2 := by
  cases c <;> norm_num [chartMatrix, ChartMatrix.det, isotropicVector] <;> ring

/-- The previously established cusp approaches in their nome charts. -/
noncomputable def approach : FiniteLevelSixCusp → UpperHalfPlane → ℂ
  | .zero, z => -1 / (6 * (z : ℂ))
  | .half, z => cuspHalfApproach (cuspHalfTriplePoint z)
  | .third, z => cuspThirdApproach (cuspHalfTriplePoint z)

noncomputable def shiftedPoint : FiniteLevelSixCusp → UpperHalfPlane → UpperHalfPlane
  | .zero, z => z
  | .half, z => widthThreeShift z
  | .third, z => widthThreeShift z

theorem shiftedPoint_im (c : FiniteLevelSixCusp) (z : UpperHalfPlane) :
    (c.shiftedPoint z).im = z.im := by
  cases c <;> simp [shiftedPoint, widthThreeShift]

/-- The width-three translation contributes a fixed nome phase. -/
noncomputable def nomePhase : FiniteLevelSixCusp → ℂ
  | .zero => 1
  | .half => Function.Periodic.qParam 1 (-1 / 3)
  | .third => Function.Periodic.qParam 1 (-1 / 3)

theorem norm_nomePhase (c : FiniteLevelSixCusp) : ‖c.nomePhase‖ = 1 := by
  cases c with
  | zero => simp [nomePhase]
  | half =>
      change ‖Function.Periodic.qParam 1 (-1 / 3 : ℂ)‖ = 1
      unfold Function.Periodic.qParam
      rw [Complex.norm_exp]
      simp [Complex.mul_re]
  | third =>
      change ‖Function.Periodic.qParam 1 (-1 / 3 : ℂ)‖ = 1
      unfold Function.Periodic.qParam
      rw [Complex.norm_exp]
      simp [Complex.mul_re]

theorem qParam_shiftedPoint (c : FiniteLevelSixCusp) (z : UpperHalfPlane) :
    Function.Periodic.qParam 1 (c.shiftedPoint z) =
      c.nomePhase * Function.Periodic.qParam 1 z := by
  cases c with
  | zero => simp [shiftedPoint, nomePhase]
  | half =>
      change Function.Periodic.qParam 1 ((z : ℂ) - 1 / 3) =
        Function.Periodic.qParam 1 (-1 / 3) * Function.Periodic.qParam 1 z
      rw [show (z : ℂ) - 1 / 3 = (-1 / 3 : ℂ) + z by ring,
        qParam_one_add_complex]
  | third =>
      change Function.Periodic.qParam 1 ((z : ℂ) - 1 / 3) =
        Function.Periodic.qParam 1 (-1 / 3) * Function.Periodic.qParam 1 z
      rw [show (z : ℂ) - 1 / 3 = (-1 / 3 : ℂ) + z by ring,
        qParam_one_add_complex]

@[simp] theorem approach_zero (z : UpperHalfPlane) :
    FiniteLevelSixCusp.zero.approach z = -1 / (6 * (z : ℂ)) := (rfl)

@[simp] theorem approach_half (z : UpperHalfPlane) :
    FiniteLevelSixCusp.half.approach z = cuspHalfApproach (cuspHalfTriplePoint z) := (rfl)

@[simp] theorem approach_third (z : UpperHalfPlane) :
    FiniteLevelSixCusp.third.approach z = cuspThirdApproach (cuspHalfTriplePoint z) := (rfl)

/-- Each chosen approach is the fractional action of its explicit rational
matrix, with the width already included in that matrix. -/
theorem chartMatrix_act_eq_approach (c : FiniteLevelSixCusp)
    (z : UpperHalfPlane) : c.chartMatrix.act z = c.approach z := by
  cases c with
  | zero =>
      simp [chartMatrix, ChartMatrix.act, ChartMatrix.denominator, approach_zero]
  | half =>
      simp only [ChartMatrix.act, ChartMatrix.denominator, chartMatrix, approach_half]
      simp only [Int.cast_ofNat, Int.cast_zero, Int.cast_one, Nat.cast_one, add_zero]
      change (3 * (z : ℂ)) / (6 * (z : ℂ) + 1) =
        cuspHalfApproach (cuspHalfTriplePoint z)
      rw [cuspHalfApproach_eq]
      rw [cuspHalfTriplePoint_coe]
      change (3 * (z : ℂ)) / (6 * (z : ℂ) + 1) =
        (3 * (z : ℂ)) / (2 * (3 * (z : ℂ)) + 1)
      congr 1 <;> ring

  | third =>
      simp only [ChartMatrix.act, ChartMatrix.denominator, chartMatrix, approach_third]
      simp only [Int.cast_ofNat, Int.cast_one, Nat.cast_one]
      change (6 * (z : ℂ) + 1) / (18 * (z : ℂ) + 6) =
        cuspThirdApproach (cuspHalfTriplePoint z)
      rw [cuspThirdApproach_eq]
      rw [cuspHalfTriplePoint_coe]
      change (6 * (z : ℂ) + 1) / (18 * (z : ℂ) + 6) =
        (2 * (3 * (z : ℂ)) + 1) / (6 * (3 * (z : ℂ) + 1))
      congr 1 <;> ring

theorem chartGL_smul (c : FiniteLevelSixCusp) (z : UpperHalfPlane) :
    ((c.chartGL • z : UpperHalfPlane) : ℂ) = c.approach z := by
  rw [← c.chartMatrix_act_eq_approach]
  cases c <;>
    simp [chartGL, chartMatrix, ChartMatrix.act, ChartMatrix.denominator,
      PositiveCuspAction.positiveMatrix_smul]

theorem chartGL_smul_infty (c : FiniteLevelSixCusp) :
    c.chartGL • (∞ : OnePoint ℝ) = (↑(c.rationalPoint : ℝ) : OnePoint ℝ) := by
  cases c <;>
    simp [chartGL, rationalPoint, PositiveCuspAction.positiveMatrix_smul_infty] <;>
    norm_num

/-- The chart denominator cannot vanish on the upper half-plane. -/
theorem chartMatrix_denominator_ne_zero (c : FiniteLevelSixCusp)
    (z : UpperHalfPlane) : c.chartMatrix.denominator z ≠ 0 := by
  have him : 0 < (c.chartMatrix.denominator z).im := by
    cases c <;> simp [chartMatrix, ChartMatrix.denominator,
      Complex.mul_im, Complex.add_im] <;> positivity
  intro h
  simp [h] at him

theorem atkinLehnerMatrix_denominator_ne_zero (c : FiniteLevelSixCusp)
    (z : UpperHalfPlane) : c.atkinLehnerMatrix.denominator z ≠ 0 := by
  have him : 0 < (c.atkinLehnerMatrix.denominator z).im := by
    cases c <;> simp [atkinLehnerMatrix, ChartMatrix.denominator,
      Complex.mul_im, Complex.add_im] <;> positivity
  intro h
  simp [h] at him

/-- The three local approaches are the stated Atkin–Lehner actions on
the translated high cusp. The third matrix is scaled by three, which does
not change its fractional action. -/
theorem chartMatrix_act_eq_atkinLehner_shift (c : FiniteLevelSixCusp)
    (z : UpperHalfPlane) :
    c.chartMatrix.act z = c.atkinLehnerMatrix.act (c.shiftedPoint z) := by
  cases c with
  | zero =>
      rfl
  | half =>
      simp only [chartMatrix, atkinLehnerMatrix, shiftedPoint,
        ChartMatrix.act, ChartMatrix.denominator, widthThreeShift_coe]
      push_cast
      congr 1 <;> ring
  | third =>
      simp only [chartMatrix, atkinLehnerMatrix, shiftedPoint,
        ChartMatrix.act, ChartMatrix.denominator, widthThreeShift_coe]
      push_cast
      have hden : (6 : ℂ) * ((z : ℂ) - 1 / 3) + 4 ≠ 0 := by
        change (FiniteLevelSixCusp.third.atkinLehnerMatrix.denominator
          (widthThreeShift z)) ≠ 0
        exact atkinLehnerMatrix_denominator_ne_zero _ _
      have hden' : (18 : ℂ) * (z : ℂ) + 6 ≠ 0 := by
        change (FiniteLevelSixCusp.third.chartMatrix.denominator z) ≠ 0
        exact chartMatrix_denominator_ne_zero _ _
      field_simp [hden, hden']
      ring

/-- The quadratic attached to the primitive isotropic cusp vector. -/
def isotropicQuadratic (c : FiniteLevelSixCusp) (w : ℂ) : ℂ :=
  6 * (c.isotropicVector.c : ℂ) * w ^ 2 +
    12 * (c.isotropicVector.b : ℂ) * w + c.isotropicVector.a

/-- In the chosen rational chart, the isotropic quadratic is exactly the
determinant divided by the square of the automorphy denominator. -/
theorem isotropicQuadratic_approach (c : FiniteLevelSixCusp)
    (z : UpperHalfPlane) :
    c.isotropicQuadratic (c.approach z) =
      (c.chartMatrix.det : ℂ) / c.chartMatrix.denominator z ^ 2 := by
  rw [← chartMatrix_act_eq_approach]
  have hden : c.chartMatrix.denominator z ≠ 0 := c.chartMatrix_denominator_ne_zero z
  have hdet : (c.chartMatrix.det : ℂ) ≠ 0 := by
    cases c <;> norm_num [chartMatrix, ChartMatrix.det]
  have hpoly (w : ℂ) :
      (c.chartMatrix.det : ℂ) * c.isotropicQuadratic w =
        ((c.chartMatrix.c : ℂ) * w - c.chartMatrix.a) ^ 2 := by
    cases c <;> norm_num [chartMatrix, ChartMatrix.det,
      isotropicQuadratic, isotropicVector] <;> ring
  have hlin :
      (c.chartMatrix.c : ℂ) * c.chartMatrix.act z - c.chartMatrix.a =
        -(c.chartMatrix.det : ℂ) / c.chartMatrix.denominator z := by
    unfold ChartMatrix.act ChartMatrix.det ChartMatrix.denominator at *
    field_simp [hden]
    push_cast
    ring
  apply (mul_left_cancel₀ hdet)
  rw [hpoly, hlin]
  field_simp [hden]

/-- Weight-four slash in the normalized finite-cusp charts. The rational
matrix determinants are `6`, `3`, and `18`, respectively. -/
noncomputable def weightFourSlash (c : FiniteLevelSixCusp)
    (F : ℂ → ℂ) (z : UpperHalfPlane) : ℂ :=
  match c with
  | .zero => 36 * F (c.approach z) / (6 * (z : ℂ)) ^ 4
  | .half => 9 * F (c.approach z) / (6 * (z : ℂ) + 1) ^ 4
  | .third => 324 * F (c.approach z) / (18 * (z : ℂ) + 6) ^ 4

/-- The uniform weight-four rational slash, including the square of the
determinant because the classical weight is four. -/
noncomputable def ChartMatrix.weightFourSlash (M : ChartMatrix)
    (F : ℂ → ℂ) (z : UpperHalfPlane) : ℂ :=
  (M.det : ℂ) ^ 2 * F (M.act z) / M.denominator z ^ 4

theorem weightFourSlash_eq_matrix (c : FiniteLevelSixCusp)
    (F : ℂ → ℂ) (z : UpperHalfPlane) :
    c.weightFourSlash F z = c.chartMatrix.weightFourSlash F z := by
  rw [ChartMatrix.weightFourSlash, chartMatrix_act_eq_approach]
  cases c <;> norm_num [weightFourSlash, chartMatrix, ChartMatrix.det,
    ChartMatrix.denominator]

/-- The explicit weight-four chart formula is the classical slash by its
positive real matrix. -/
theorem weightFourSlash_eq_evenWeightSlash (c : FiniteLevelSixCusp)
    (F : ℂ → ℂ) (z : UpperHalfPlane) :
    c.weightFourSlash F z =
      PositiveCuspAction.evenWeightSlash 2 c.chartGL
        (fun w : UpperHalfPlane => F w) z := by
  rw [weightFourSlash_eq_matrix, PositiveCuspAction.evenWeightSlash_apply]
  rw [c.chartGL_det, c.chartGL_denominator, c.chartGL_smul]
  simp only [ChartMatrix.weightFourSlash, c.chartMatrix_act_eq_approach,
    Nat.reduceMul]
  cases c <;> norm_num [chartMatrix, ChartMatrix.det]

/-- Finite-cusp weight-four slash is exactly the Atkin–Lehner slash at a
translated high-cusp point. The determinant normalization removes the
scalar-three difference in the third chart. -/
theorem weightFourSlash_eq_atkinLehner_shift (c : FiniteLevelSixCusp)
    (F : ℂ → ℂ) (z : UpperHalfPlane) :
    c.weightFourSlash F z =
      c.atkinLehnerMatrix.weightFourSlash F (c.shiftedPoint z) := by
  rw [weightFourSlash_eq_matrix]
  simp only [ChartMatrix.weightFourSlash, chartMatrix_act_eq_atkinLehner_shift]
  cases c with
  | zero =>
      rfl
  | half =>
      simp only [chartMatrix, atkinLehnerMatrix, shiftedPoint,
        ChartMatrix.det, ChartMatrix.denominator, widthThreeShift_coe]
      push_cast
      congr 1 <;> ring
  | third =>
      simp only [chartMatrix, atkinLehnerMatrix, shiftedPoint,
        ChartMatrix.det, ChartMatrix.denominator, widthThreeShift_coe]
      push_cast
      have hscale : (18 : ℂ) * (z : ℂ) + 6 =
          3 * (6 * ((z : ℂ) - 1 / 3) + 4) := by ring
      have hden : (6 : ℂ) * ((z : ℂ) - 1 / 3) + 4 ≠ 0 := by
        change (FiniteLevelSixCusp.third.atkinLehnerMatrix.denominator
          (widthThreeShift z)) ≠ 0
        exact atkinLehnerMatrix_denominator_ne_zero _ _
      rw [hscale, mul_pow]
      field_simp [hden]
      ring

end FiniteLevelSixCusp
end SptClassification
