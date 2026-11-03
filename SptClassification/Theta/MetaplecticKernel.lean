/- Assembled by AxiomProver. -/

module

public import SptClassification.Theta.MetaplecticPairs

/-!
# The central fiber of the generated metaplectic pairs

When a standard generator word has identity matrix, its square-root factor is
constant. This follows from the nonvanishing of eta and its transformation law;
it identifies the central fiber of the generated pairs without imposing an
unjustified continuity condition on all algebraic matrix–factor pairs. See
[rolenManuscript, lines 339–343].
-/

public section

namespace SptClassification
namespace Theta

/-- An identity-matrix generator word has a constant square-root factor,
determined by its eta phase. -/
theorem etaWeilWordFactor_of_matrix_one (w : List EtaWeilStep)
    (hmatrix : etaWeilWordMatrix w = 1) (z : UpperHalfPlane) :
    etaWeilWordFactor w z = (etaWeilWordPhase w)⁻¹ := by
  have haction : etaWeilWordAction w z = z := by
    rw [← etaWeilWordMatrix_smul, hmatrix, one_smul]
  have htransform := eta_action_generator_word w z
  rw [haction] at htransform
  have heta : ModularForm.eta (z : ℂ) ≠ 0 :=
    ModularForm.eta_ne_zero z.im_pos
  have hproduct : etaWeilWordPhase w * etaWeilWordFactor w z = 1 := by
    apply (mul_right_cancel₀ heta)
    simpa only [one_mul] using htransform.symm
  have hphase : etaWeilWordPhase w ≠ 0 := etaWeilWordPhase_ne_zero w
  calc
    etaWeilWordFactor w z =
        1 * etaWeilWordFactor w z := by rw [one_mul]
    _ = ((etaWeilWordPhase w)⁻¹ * etaWeilWordPhase w) *
          etaWeilWordFactor w z := by rw [inv_mul_cancel₀ hphase]
    _ = (etaWeilWordPhase w)⁻¹ := by rw [mul_assoc, hproduct, mul_one]

/-- In the generated metaplectic submonoid, the fiber over the identity
matrix has constant factor, equal to the inverse eta character. -/
theorem generatedPair_factor_of_matrix_one (g : etaWeilGeneratedPairs)
    (hmatrix : g.val.matrix = 1) (z : UpperHalfPlane) :
    g.val.factor z = (generatedPairPhase g)⁻¹ := by
  have hword := generatedPairWord_eq g
  have hmatrixWord : etaWeilWordMatrix (generatedPairWord g) = 1 := by
    rw [← hmatrix]
    simpa only [etaWeilWordMetaplecticPair_matrix] using
      congrArg MetaplecticPair.matrix hword
  have hfactor := etaWeilWordFactor_of_matrix_one
    (generatedPairWord g) hmatrixWord z
  change etaWeilWordMetaplecticPair (generatedPairWord g) = g.val at hword
  rw [← hword]
  change (etaWeilWordMetaplecticPair (generatedPairWord g)).factor z =
    (generatedPairPhase g)⁻¹
  rw [etaWeilWordMetaplecticPair_factor]
  rw [generatedPairPhase_eq]
  exact hfactor

end Theta
end SptClassification
