/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.LevelSixTateCoordinates
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.NormNum

/-!
# Selection of the Tate parameter at the width-one cusp

The reciprocal j-invariant has derivative `9/8` at `c = -1/9`.
Consequently two parameter families approaching this cusp and having equal
reciprocal invariants agree eventually. The common cusp limit is essential:
equality of unmarked invariants alone does not determine a cyclic subgroup.
-/

public section

namespace SptClassification.LevelSixWeierstrass

/-- The rational reciprocal invariant, extended by field division at its poles.
On nonsingular curves with nonzero c₄ this is the reciprocal of j. -/
noncomputable def tateReciprocalInvariant (c : ℂ) : ℂ :=
  c ^ 6 * (c + 1) ^ 3 * (9 * c + 1) /
    (9 * c ^ 4 + 12 * c ^ 3 + 30 * c ^ 2 + 12 * c + 1) ^ 3

theorem tateReciprocalInvariant_eq (c : ℂ) :
    tateReciprocalInvariant c = (tateCurve c).Δ / (tateCurve c).c₄ ^ 3 := by
  rw [tateCurve_discriminant, tateCurve_c₄]
  rfl

/-- The width-one cusp is a simple zero of the reciprocal invariant. -/
theorem tateReciprocalInvariant_hasStrictDerivAt :
    HasStrictDerivAt tateReciprocalInvariant (9 / 8) (-1 / 9) := by
  have h := hasStrictDerivAt_id (-1 / 9 : ℂ)
  have hn := ((h.pow 6).mul ((h.add_const 1).pow 3)).mul ((h.const_mul 9).add_const 1)
  have hd := (((((h.pow 4).const_mul 9).add ((h.pow 3).const_mul 12)).add
    ((h.pow 2).const_mul 30)).add (h.const_mul 12)).add_const 1
  convert hn.div (hd.pow 3) (by norm_num) using 1 <;> norm_num [tateReciprocalInvariant] <;> rfl

/-- A common invariant selects a unique branch once both parameters approach
`-1/9`. No analyticity of the parameter families is needed for this local step. -/
theorem tateParameter_eventuallyEq_of_cusp_limit {α : Type*} {l : Filter α}
    {u v : α → ℂ}
    (hu : Filter.Tendsto u l (nhds (-1 / 9)))
    (hv : Filter.Tendsto v l (nhds (-1 / 9)))
    (heq : ∀ᶠ x in l, tateReciprocalInvariant (u x) = tateReciprocalInvariant (v x)) :
    u =ᶠ[l] v := by
  have hinv := tateReciprocalInvariant_hasStrictDerivAt.eventually_left_inverse
    (by norm_num : (9 / 8 : ℂ) ≠ 0)
  filter_upwards [hu hinv, hv hinv, heq] with x hx hy hxy
  rw [← hx, ← hy, hxy]

end SptClassification.LevelSixWeierstrass
