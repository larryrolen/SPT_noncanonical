/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.EtaQuotientCuspsHalfExpansion
public import SptClassification.ModularForms.EtaQuotientCuspZero

/-!
# The level-six eta quotient at the cusp one-third

The Fricke involution exchanges the cusps `1/2` and `1/3`. Composing it
with the level-six cusp-zero parabolic gives an approach to `1/3` for which
the eta quotient has value `-8`. This supplies another point of the cusp
divisor needed for the coordinate in [rolen2026canonical], Section 4.
-/

public section

namespace SptClassification

/-- The integral matrix taking infinity to the cusp one-half. -/
def cuspHalfMatrix : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  ⟨!![1, 0; 2, 1], by norm_num [Matrix.det_fin_two]⟩

/-- The upper-half-plane point represented by the one-half cusp approach. -/
noncomputable def cuspHalfPoint (z : UpperHalfPlane) : UpperHalfPlane :=
  cuspHalfMatrix • z

theorem cuspHalfPoint_coe (z : UpperHalfPlane) :
    (cuspHalfPoint z : ℂ) = cuspHalfApproach z := by
  unfold cuspHalfPoint
  rw [cuspHalfApproach_eq]
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  norm_num [cuspHalfMatrix]

/-- Apply the Fricke involution of level six to the one-half cusp approach. -/
noncomputable def frickeCuspHalfPoint (z : UpperHalfPlane) : UpperHalfPlane :=
  ⟨(ModularGroup.S • cuspHalfPoint z : UpperHalfPlane) / 6, by
    simpa using div_pos (ModularGroup.S • cuspHalfPoint z).im_pos
      (by norm_num : (0 : ℝ) < 6)⟩

theorem frickeCuspHalfPoint_coe (z : UpperHalfPlane) :
    (frickeCuspHalfPoint z : ℂ) = -1 / (6 * (cuspHalfPoint z : ℂ)) := by
  change ((ModularGroup.S • cuspHalfPoint z : UpperHalfPlane) : ℂ) / 6 = _
  rw [UpperHalfPlane.modular_S_smul]
  field_simp [UpperHalfPlane.ne_zero (cuspHalfPoint z)]

/-- The cusp-zero parabolic after Fricke approaches the cusp one-third. -/
noncomputable def cuspThirdApproach (z : UpperHalfPlane) : ℂ :=
  (frickeCuspHalfPoint z : ℂ) / (6 * (frickeCuspHalfPoint z : ℂ) + 1)

theorem cuspThirdApproach_eq (z : UpperHalfPlane) :
    cuspThirdApproach z = (2 * (z : ℂ) + 1) / (6 * ((z : ℂ) + 1)) := by
  rw [cuspThirdApproach, frickeCuspHalfPoint_coe, cuspHalfPoint_coe]
  rw [cuspHalfApproach_eq]
  have hden : 2 * (z : ℂ) + 1 ≠ 0 := by
    intro he
    have hp : 0 < (2 * (z : ℂ) + 1).im := by
      simpa using mul_pos (by norm_num : (0 : ℝ) < 2) z.im_pos
    rw [he] at hp
    simp at hp
  have hz1 : (z : ℂ) + 1 ≠ 0 := by
    intro he
    have hp : 0 < ((z : ℂ) + 1).im := by simpa using z.im_pos
    rw [he] at hp
    simp at hp
  field_simp [hden, hz1, z.ne_zero]
  rw [show -(↑z * 2 + 1) + (z : ℂ) = -((z : ℂ) + 1) by ring]
  field_simp [hz1]

/-- Fricke and the cusp-zero parabolic give `t` at one-third as `72/t`
at one-half. -/
theorem levelSixEtaQuotient_cuspThird (z : UpperHalfPlane) :
    levelSixEtaQuotient (cuspThirdApproach z) =
      72 / levelSixEtaQuotient (cuspHalfApproach z) := by
  rw [cuspThirdApproach, levelSixEtaQuotient_cusp_zero,
    frickeCuspHalfPoint_coe, levelSixEtaQuotient_fricke_six,
    cuspHalfPoint_coe]

/-- The unit governing the eta quotient at the cusp one-third. -/
noncomputable def cuspThirdEulerUnit (q : ℂ) : ℂ :=
  (cuspHalfEulerUnit q)⁻¹

/-- The cusp-one-third unit is the reciprocal of the cusp-one-half unit. -/
theorem cuspThirdEulerUnit_eq (q : ℂ) :
    cuspThirdEulerUnit q = (cuspHalfEulerUnit q)⁻¹ := (rfl)

theorem cuspThirdEulerUnit_zero : cuspThirdEulerUnit 0 = 1 := by
  simp [cuspThirdEulerUnit, cuspHalfEulerUnit_zero]

/-- The reciprocal Euler unit is holomorphic at the cusp. -/
theorem differentiableAt_cuspThirdEulerUnit_zero :
    DifferentiableAt ℂ cuspThirdEulerUnit 0 := by
  exact differentiableAt_cuspHalfEulerUnit_zero.inv
    (by simp [cuspHalfEulerUnit_zero])

/-- Along this cusp-one-third approach, the eta quotient is `-8` times a
holomorphic Euler unit. -/
theorem levelSixEtaQuotient_cuspThird_euler (w : UpperHalfPlane) :
    levelSixEtaQuotient (cuspThirdApproach (cuspHalfTriplePoint w)) =
      -8 * cuspThirdEulerUnit (Function.Periodic.qParam 1 w) := by
  rw [levelSixEtaQuotient_cuspThird,
    levelSixEtaQuotient_cuspHalf_widthThree]
  unfold cuspThirdEulerUnit
  ring

/-- The exact value at the cusp one-third is `-8`. -/
theorem tendsto_levelSixEtaQuotient_cuspThird
    {α : Type*} {l : Filter α} (w : α → UpperHalfPlane)
    (hw : Filter.Tendsto
      (fun a => Function.Periodic.qParam 1 (w a : ℂ)) l (nhds 0)) :
    Filter.Tendsto
      (fun a => levelSixEtaQuotient
        (cuspThirdApproach (cuspHalfTriplePoint (w a)))) l (nhds (-8)) := by
  have hunit := differentiableAt_cuspThirdEulerUnit_zero.continuousAt.tendsto.comp hw
  have hprod := (tendsto_const_nhds.mul hunit :
    Filter.Tendsto
      (fun a => (-8 : ℂ) *
        cuspThirdEulerUnit (Function.Periodic.qParam 1 (w a : ℂ)))
      l (nhds ((-8 : ℂ) * cuspThirdEulerUnit 0)))
  simpa only [levelSixEtaQuotient_cuspThird_euler,
    cuspThirdEulerUnit_zero, mul_one] using hprod

end SptClassification
