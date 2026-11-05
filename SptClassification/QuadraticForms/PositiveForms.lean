/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.Reduction
public import Mathlib.Data.Int.Interval
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Positive forms and finiteness of their proper classes

Reduced forms have coefficients in explicit finite integer intervals. Reduction
makes their map onto the full modular-group orbit space surjective.
-/

@[expose] public section

namespace SptClassification

/-- Positive integral forms of fixed discriminant, without a level condition. -/
structure PositiveForm (D : ℤ) extends BinaryQuadraticForm where
  a_pos : 0 < a
  discriminant_eq : toBinaryQuadraticForm.discriminant = D

namespace PositiveForm

@[ext] theorem ext {D : ℤ} {Q R : PositiveForm D}
    (h : Q.toBinaryQuadraticForm = R.toBinaryQuadraticForm) : Q = R := by
  cases Q
  cases R
  cases h
  rfl

def transform {D : ℤ} (hD : D < 0) (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (Q : PositiveForm D) : PositiveForm D where
  toBinaryQuadraticForm := BinaryQuadraticForm.transform g Q.toBinaryQuadraticForm
  a_pos := Q.toBinaryQuadraticForm.transform_a_pos Q.a_pos (Q.discriminant_eq.trans_lt hD) g
  discriminant_eq := (BinaryQuadraticForm.discriminant_transform g Q.toBinaryQuadraticForm).trans
    Q.discriminant_eq

@[simp] theorem toBinaryQuadraticForm_transform {D : ℤ} (hD : D < 0)
    (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) (Q : PositiveForm D) :
    (transform hD g Q).toBinaryQuadraticForm =
      BinaryQuadraticForm.transform g Q.toBinaryQuadraticForm := (rfl)

@[simp] theorem transform_one {D : ℤ} (hD : D < 0) (Q : PositiveForm D) :
    transform hD 1 Q = Q := by
  apply ext
  simp only [toBinaryQuadraticForm_transform, BinaryQuadraticForm.transform_one]

theorem transform_mul {D : ℤ} (hD : D < 0) (g h : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (Q : PositiveForm D) : transform hD (g * h) Q = transform hD g (transform hD h Q) := by
  apply ext
  simp only [toBinaryQuadraticForm_transform, BinaryQuadraticForm.transform_mul]

instance modularAction {D : ℤ} [Fact (D < 0)] :
    MulAction (Matrix.SpecialLinearGroup (Fin 2) ℤ) (PositiveForm D) where
  smul := transform Fact.out
  one_smul := transform_one Fact.out
  mul_smul := transform_mul Fact.out

@[simp] theorem toBinaryQuadraticForm_smul {D : ℤ} [Fact (D < 0)]
    (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) (Q : PositiveForm D) :
    (g • Q).toBinaryQuadraticForm = BinaryQuadraticForm.transform g Q.toBinaryQuadraticForm := by
  change (transform Fact.out g Q).toBinaryQuadraticForm = _
  exact toBinaryQuadraticForm_transform Fact.out g Q

end PositiveForm

/-- Reduced positive forms, using the inequalities needed for finiteness. -/
@[expose]
def ReducedForm (D : ℤ) := {Q : PositiveForm D // |Q.b| ≤ Q.a ∧ Q.a ≤ Q.c}

theorem reduced_coordinates_mem {D : ℤ} (Q : ReducedForm D) (i : Fin 3) :
    ![Q.1.a, Q.1.b, Q.1.c] i ∈ Finset.Icc (-(D ^ 2 - D)) (D ^ 2 - D) := by
  have ha := Q.1.a_pos
  have hac := Q.2.2
  have hA : Q.1.a ≤ -D := by
    simpa only [Q.1.discriminant_eq] using
      Q.1.toBinaryQuadraticForm.reduced_a_bound ha Q.2.1 hac
  have hAB : Q.1.a ≤ D ^ 2 - D := by nlinarith [sq_nonneg D]
  have hC : Q.1.c ≤ D ^ 2 - D := by
    simpa only [Q.1.discriminant_eq] using
      Q.1.toBinaryQuadraticForm.reduced_c_bound ha Q.2.1 hac
  obtain ⟨hbL, hbU⟩ := abs_le.mp Q.2.1
  fin_cases i
  · change Q.1.a ∈ Finset.Icc (-(D ^ 2 - D)) (D ^ 2 - D)
    exact Finset.mem_Icc.mpr ⟨by linarith, hAB⟩
  · change Q.1.b ∈ Finset.Icc (-(D ^ 2 - D)) (D ^ 2 - D)
    exact Finset.mem_Icc.mpr ⟨by linarith, by linarith⟩
  · change Q.1.c ∈ Finset.Icc (-(D ^ 2 - D)) (D ^ 2 - D)
    exact Finset.mem_Icc.mpr ⟨by linarith, hC⟩

instance reducedFormFinite (D : ℤ) : Finite (ReducedForm D) := by
  classical
  let f : ReducedForm D → (Fin 3 → {z : ℤ // z ∈ Finset.Icc (-(D ^ 2 - D)) (D ^ 2 - D)}) :=
    fun Q i => ⟨![Q.1.a, Q.1.b, Q.1.c] i, reduced_coordinates_mem Q i⟩
  apply Finite.of_injective f
  intro Q R h
  apply Subtype.ext
  apply PositiveForm.ext
  apply BinaryQuadraticForm.ext
  · exact congrArg (fun v => (v 0).val) h
  · exact congrArg (fun v => (v 1).val) h
  · exact congrArg (fun v => (v 2).val) h

instance positiveOrbitFinite {D : ℤ} [Fact (D < 0)] :
    Finite (MulAction.orbitRel.Quotient (Matrix.SpecialLinearGroup (Fin 2) ℤ) (PositiveForm D)) := by
  classical
  let f : ReducedForm D →
      MulAction.orbitRel.Quotient (Matrix.SpecialLinearGroup (Fin 2) ℤ) (PositiveForm D) :=
    fun Q => Quotient.mk _ Q.1
  apply Finite.of_surjective f
  intro C
  induction C using Quotient.inductionOn with
  | h Q =>
    obtain ⟨g, hg⟩ := Q.toBinaryQuadraticForm.exists_reduced_transform Q.a_pos
      (Q.discriminant_eq.trans_lt Fact.out)
    refine ⟨⟨g • Q, hg⟩, ?_⟩
    apply Quotient.sound
    exact ⟨g, rfl⟩

end SptClassification
