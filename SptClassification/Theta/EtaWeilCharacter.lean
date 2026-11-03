/- Assembled by AxiomProver. -/

module

public import SptClassification.Theta.EtaWeilAutomorphyGroup

/-!
# The eta–Weil character of generated automorphy data

The scalar shared by eta and the distinguished finite Weil input is nonzero
and multiplicative on the group of generated automorphy data. The resulting
character takes values in `ℂˣ`. This identifies the invariant line for the
generator formulas; it does not assert that the full finite Weil operator
descends to the automorphy-data quotient. See [rolenManuscript, lines 339–343].
-/

public section

namespace SptClassification
namespace Theta

/-- The eta–Weil scalar of generated automorphy data never vanishes. -/
theorem EtaWeilAutomorphyWords.phase_ne_zero (g : EtaWeilAutomorphyWords) :
    g.phase ≠ 0 := by
  have h : g.phase * g⁻¹.phase = 1 := by
    rw [← EtaWeilAutomorphyWords.phase_compose]
    change (g * g⁻¹).phase = 1
    rw [mul_inv_cancel]
    change EtaWeilAutomorphyWords.identity.phase = 1
    rw [EtaWeilAutomorphyWords.identity_eq_mk,
      EtaWeilAutomorphyWords.phase_mk]
    exact etaWeilWordPhase_nil
  exact left_ne_zero_of_mul_eq_one h

/-- The shared eta and Weil scalar as a character of the generated group. -/
noncomputable def etaWeilCharacter : EtaWeilAutomorphyWords →* ℂˣ where
  toFun g := Units.mk0 g.phase g.phase_ne_zero
  map_one' := by
    apply Units.ext
    change (1 : EtaWeilAutomorphyWords).phase = 1
    change EtaWeilAutomorphyWords.identity.phase = 1
    rw [EtaWeilAutomorphyWords.identity_eq_mk,
      EtaWeilAutomorphyWords.phase_mk]
    exact etaWeilWordPhase_nil
  map_mul' g h := by
    apply Units.ext
    exact EtaWeilAutomorphyWords.phase_compose g h

/-- On the input vector, the product of two generated automorphy data acts
by the product of their eta–Weil scalars. -/
theorem EtaWeilAutomorphyWords.inputAction_mul
    (g h : EtaWeilAutomorphyWords) :
    (g * h).inputAction =
      fun r => g.phase * h.inputAction r := by
  funext r
  simp only [EtaWeilAutomorphyWords.inputAction_apply]
  change (g.compose h).phase * weilInputVectorAs ℂ r =
    g.phase * (h.phase * weilInputVectorAs ℂ r)
  rw [EtaWeilAutomorphyWords.phase_compose]
  ring

end Theta
end SptClassification
