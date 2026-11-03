/- Assembled by AxiomProver. -/

module

public import SptClassification.Theta.MetaplecticCentralSign

/-!
# The cubic relation for the chosen metaplectic lifts

The standard lifts of inversion and translation satisfy `(S̃ T̃)³ = S̃²`
as concrete matrix–factor pairs. We identify their eta phases using the
full-vector finite Weil cubic relation, then use eta's nonvanishing to identify
their square-root factors. This verifies a relation required for descent; it
does not itself present the generated metaplectic group. See
[rolenManuscript, lines 339–343].
-/

public section

namespace SptClassification
namespace Theta

/-- The six-generator word `(S̃ T̃)³`, acting from the right. -/
def etaWeilSTCubeWord : List EtaWeilStep :=
  [.inversion, .translation 1, .inversion, .translation 1,
    .inversion, .translation 1]

/-- The two-generator word `S̃²`. -/
def etaWeilInversionSquareWord : List EtaWeilStep :=
  [.inversion, .inversion]

/-- The finite formula for translation by one is the standard Weil `T`. -/
theorem finiteWeilTranslation_one (f : ZMod 12 → ℂ) :
    finiteWeilTranslation 1 f = finiteWeilT f := by
  funext r
  simp only [finiteWeilTranslation_apply, finiteWeilT, Int.cast_one, mul_one]

/-- The two cubic-relation words have equal finite action on every
discriminant coefficient vector. -/
theorem etaWeilSTCube_finiteAction (f : ZMod 12 → ℂ) :
    etaWeilWordFiniteAction etaWeilSTCubeWord f =
      etaWeilWordFiniteAction etaWeilInversionSquareWord f := by
  simpa only [etaWeilSTCubeWord, etaWeilInversionSquareWord,
    etaWeilWordFiniteAction_cons, etaWeilWordFiniteAction_nil,
    EtaWeilStep.finiteAction_inversion, EtaWeilStep.finiteAction_translation,
    finiteWeilTranslation_one] using finiteWeilST_cube f

/-- Evaluation of the finite cubic relation on the nonzero input vector
identifies the eta phases of the two words. -/
theorem etaWeilSTCube_phase_eq :
    etaWeilWordPhase etaWeilSTCubeWord =
      etaWeilWordPhase etaWeilInversionSquareWord := by
  have h := etaWeilSTCube_finiteAction (weilInputVectorAs ℂ)
  simp only [etaWeilWordFiniteAction_input] at h
  have h1 := congrFun h (1 : ZMod 12)
  have hv : weilInputVectorAs ℂ (1 : ZMod 12) = 1 := by
    change ((weilInputVector (1 : ZMod 12) : ℤ) : ℂ) = 1
    have hval : weilInputVector (1 : ZMod 12) = 1 := by decide +kernel
    norm_num [hval]
  simpa only [hv, mul_one] using h1

/-- The integral matrices in the two standard cubic-relation words agree. -/
theorem etaWeilSTCube_matrix_eq :
    etaWeilWordMatrix etaWeilSTCubeWord =
      etaWeilWordMatrix etaWeilInversionSquareWord := by
  simp only [etaWeilSTCubeWord, etaWeilInversionSquareWord,
    etaWeilWordMatrix_cons, etaWeilWordMatrix_nil,
    EtaWeilStep.matrix_inversion, EtaWeilStep.matrix_translation_one, mul_one]
  decide +kernel

/-- For standard-generator words, matrix and eta phase together determine
the entire concrete square-root pair. -/
theorem etaWeilWordMetaplecticPair_eq_of_matrix_phase_eq
    (w v : List EtaWeilStep)
    (hmatrix : etaWeilWordMatrix w = etaWeilWordMatrix v)
    (hphase : etaWeilWordPhase w = etaWeilWordPhase v) :
    etaWeilWordMetaplecticPair w = etaWeilWordMetaplecticPair v := by
  apply MetaplecticPair.ext
  · simpa only [etaWeilWordMetaplecticPair_matrix] using hmatrix
  · funext z
    simp only [etaWeilWordMetaplecticPair_factor]
    have haction : etaWeilWordAction w z = etaWeilWordAction v z := by
      rw [← etaWeilWordMatrix_smul, ← etaWeilWordMatrix_smul, hmatrix]
    have hproduct : etaWeilWordPhase w * etaWeilWordFactor w z *
        ModularForm.eta z =
        etaWeilWordPhase v * etaWeilWordFactor v z * ModularForm.eta z := by
      calc
        _ = ModularForm.eta (etaWeilWordAction w z : ℂ) :=
          (eta_action_generator_word w z).symm
        _ = ModularForm.eta (etaWeilWordAction v z : ℂ) := by rw [haction]
        _ = _ := eta_action_generator_word v z
    rw [hphase] at hproduct
    have hn : etaWeilWordPhase v * ModularForm.eta z ≠ 0 :=
      mul_ne_zero (etaWeilWordPhase_ne_zero v)
        (ModularForm.eta_ne_zero z.im_pos)
    apply (mul_right_cancel₀ hn)
    calc
      etaWeilWordFactor w z *
          (etaWeilWordPhase v * ModularForm.eta z) =
        etaWeilWordPhase v * etaWeilWordFactor w z *
          ModularForm.eta z := by ring
      _ = etaWeilWordPhase v * etaWeilWordFactor v z *
          ModularForm.eta z := hproduct
      _ = etaWeilWordFactor v z *
          (etaWeilWordPhase v * ModularForm.eta z) := by ring

/-- The chosen concrete metaplectic lifts obey `(S̃ T̃)³ = S̃²`. -/
theorem etaWeilSTCube_pair_eq_inversionSquare :
    etaWeilWordMetaplecticPair etaWeilSTCubeWord =
      etaWeilWordMetaplecticPair etaWeilInversionSquareWord :=
  etaWeilWordMetaplecticPair_eq_of_matrix_phase_eq _ _
    etaWeilSTCube_matrix_eq etaWeilSTCube_phase_eq

end Theta
end SptClassification
