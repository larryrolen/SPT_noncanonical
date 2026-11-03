/- Assembled by AxiomProver. -/

module

public import SptClassification.Theta.MetaplecticGroup

/-!
# Central relation for the finite Weil inversion

The square of the standard inversion lift is scalar reflection. Since the
discriminant quadratic form is even, that reflection commutes with every
integral translation operator. This is one of the full-vector relations needed
for descent from generator words to the metaplectic group in
[rolenManuscript, lines 339–343].
-/

public section

namespace SptClassification
namespace Theta

/-- Integral translation has the same diagonal phase at opposite residue
classes of the discriminant group. -/
theorem finiteWeilTranslation_phase_neg (n : ℤ) (r : ZMod 12) :
    Complex.exp (Real.pi * Complex.I * n *
      (discriminantQuadratic (-r)).val / 12) =
    Complex.exp (Real.pi * Complex.I * n *
      (discriminantQuadratic r).val / 12) := by
  rw [discriminantQuadratic_neg]

/-- The square of `S` commutes with every integral `T` translation on the
whole twelve-component coefficient space. -/
theorem finiteWeilS_sq_commute_translation (n : ℤ)
    (f : ZMod 12 → ℂ) :
    finiteWeilS (finiteWeilS (finiteWeilTranslation n f)) =
      finiteWeilTranslation n (finiteWeilS (finiteWeilS f)) := by
  funext r
  rw [congrFun (finiteWeilS_sq (finiteWeilTranslation n f)) r]
  simp only [finiteWeilTranslation_apply]
  rw [congrFun (finiteWeilS_sq f) r]
  simp only [discriminantQuadratic_neg]
  ring

end Theta
end SptClassification
