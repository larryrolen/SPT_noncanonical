/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.CMPoint
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction

/-!
# Equivariance of the CM point

Homogeneity of a binary quadratic form and the inverse Moebius transformation
show that transforming an upper-half-plane root gives a root of the transformed
form. Uniqueness of that root proves equivariance of the CM-point construction.
-/

public section

open scoped MatrixGroups

namespace SptClassification

namespace BinaryQuadraticForm

theorem root_transform (Q : BinaryQuadraticForm)
    (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane)
    (hz : evaluateOver ℂ Q z 1 = 0) :
    evaluateOver ℂ (transform g Q) (↑(g • z : UpperHalfPlane) : ℂ) 1 = 0 := by
  let w : UpperHalfPlane := g • z
  let M := g⁻¹
  let d : ℂ := (M 1 0 : ℂ) * w + (M 1 1 : ℂ)
  let n : ℂ := (M 0 0 : ℂ) * w + (M 0 1 : ℂ)
  have hd : d ≠ 0 := UpperHalfPlane.denom_ne_zero (M : GL (Fin 2) ℝ) w
  have hf : (z : ℂ) = n / d := by
    calc
      (z : ℂ) = ((M • w : UpperHalfPlane) : ℂ) :=
        congrArg (fun v : UpperHalfPlane => (v : ℂ)) (inv_smul_smul g z).symm
      _ = n / d := by
        simpa [n, d] using UpperHalfPlane.coe_specialLinearGroup_apply M w
  have hn : n = d * (z : ℂ) := by
    simpa only [mul_comm] using (div_eq_iff hd).mp hf.symm
  change evaluateOver ℂ (Q.pullback (M : Matrix (Fin 2) (Fin 2) ℤ)) (w : ℂ) 1 = 0
  rw [evaluateOver_pullback]
  simp only [mul_one]
  change evaluateOver ℂ Q n d = 0
  rw [hn]
  have hom := evaluateOver_homogeneous Q d (z : ℂ) (1 : ℂ)
  rw [mul_one] at hom
  rw [hom, hz, mul_zero]

end BinaryQuadraticForm

namespace PositiveForm

theorem cmPoint_smul {D : ℤ} [Fact (D < 0)]
    (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) (Q : PositiveForm D) :
    (g • Q).cmPoint = g • Q.cmPoint := by
  symm
  apply ((g • Q).eq_cmPoint_iff _).mpr
  rw [toBinaryQuadraticForm_smul]
  exact Q.toBinaryQuadraticForm.root_transform g Q.cmPoint Q.evaluateOver_cmPoint

end PositiveForm

namespace LevelSixForm

theorem cmPoint_smul {D : ℤ} {r : ZMod 12} [Fact (D < 0)]
    (g : CongruenceSubgroup.Gamma0 6) (Q : LevelSixForm D r) :
    (g • Q).cmPoint = g • Q.cmPoint := by
  calc
    (g • Q).cmPoint = (g • Q.toPositiveForm).cmPoint := by
      rw [cmPoint_eq_toPositiveForm, toPositiveForm_smul]
    _ = ((g : Matrix.SpecialLinearGroup (Fin 2) ℤ) •
        Q.toPositiveForm).cmPoint :=
      congrArg PositiveForm.cmPoint (MulAction.subgroup_smul_def g Q.toPositiveForm)
    _ = (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) • Q.toPositiveForm.cmPoint :=
      PositiveForm.cmPoint_smul _ _
    _ = g • Q.toPositiveForm.cmPoint :=
      (MulAction.subgroup_smul_def g Q.toPositiveForm.cmPoint).symm
    _ = g • Q.cmPoint := congrArg (g • ·) (cmPoint_eq_toPositiveForm Q).symm

end LevelSixForm

end SptClassification
