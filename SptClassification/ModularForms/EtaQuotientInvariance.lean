/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.GammaZeroSixGenerators
public import SptClassification.ModularForms.EtaQuotientCuspZero
public import SptClassification.ModularForms.EtaQuotientCuspHalf

/-! # Full Γ₀(6) invariance of the explicit eta quotient -/

@[expose] public section

namespace SptClassification

namespace GammaZeroSix

/-- Invariance under the cusp generators extends to the actual congruence subgroup. -/
theorem invariant_of_cusp_generators (u : UpperHalfPlane → ℂ)
    (hT : ∀ z, u (ModularGroup.T • z) = u z)
    (hU : ∀ z, u (cuspZeroTranslation • z) = u z)
    (hW : ∀ z, u (cuspHalfTranslation • z) = u z)
    (g : CongruenceSubgroup.Gamma0 6) (z : UpperHalfPlane) :
    u ((g : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z) = u z := by
  have hg : (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ cuspSubgroup := by
    rw [cuspSubgroup_eq]
    exact g.property
  rw [cuspSubgroup_eq_closure] at hg
  refine Subgroup.closure_induction
    (p := fun a _ => ∀ z : UpperHalfPlane, u (a • z) = u z) ?_ ?_ ?_ ?_ hg z
  · intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact hT
    · exact hU
    · exact hW
    · intro w
      have hw : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) • w = w := by
        apply UpperHalfPlane.ext
        rw [UpperHalfPlane.coe_specialLinearGroup_apply]
        simp
      rw [hw]
  · intro w
    simp
  · intro a b ha hb hia hib w
    rw [mul_smul, hia, hib]
  · intro a ha hia w
    simpa only [smul_inv_smul] using (hia (a⁻¹ • w)).symm

end GammaZeroSix

/-- The actual analytic eta quotient is invariant under every element of Γ₀(6). -/
theorem levelSixEtaQuotient_gamma0 (g : CongruenceSubgroup.Gamma0 6) (z : UpperHalfPlane) :
    levelSixEtaQuotient (↑((g : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z : UpperHalfPlane) : ℂ) =
      levelSixEtaQuotient z := by
  apply GammaZeroSix.invariant_of_cusp_generators (fun w => levelSixEtaQuotient w) _ _ _ g z
  · intro w
    rw [UpperHalfPlane.modular_T_smul]
    simpa only [UpperHalfPlane.coe_vadd, Complex.ofReal_one, add_comm] using
      levelSixEtaQuotient_add_one (w : ℂ)
  · intro w
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simpa [GammaZeroSix.cuspZeroTranslation_matrix] using
      levelSixEtaQuotient_cusp_zero w
  · intro w
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simpa [GammaZeroSix.cuspHalfTranslation_matrix] using levelSixEtaQuotient_cusp_half w

end SptClassification
