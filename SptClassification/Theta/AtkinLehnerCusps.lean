/- Assembled by AxiomProver. -/

module

public import SptClassification.Theta.AtkinLehnerLattice
public import SptClassification.Theta.PeriodDomain

/-!
# The Atkin–Lehner images of the infinity cusp line

The normalized pullbacks by `W₂`, `W₃`, and `W₆` send the infinity
isotropic line to the three other level-six cusp lines. For `W₂` and `W₃`
we apply an inverse integral translation to obtain the rational representatives
`1/3` and `1/2` used in `PeriodDomain`. These are the finite-dimensional
cusp identities behind [rolenManuscript, lines 350–353]. The analytic
transformation and holomorphy argument remains separate.
-/

public section

namespace SptClassification
namespace Theta

/-- The first isotropic axis, expressed in dual coordinates. -/
def infinityCuspDual : DualCoordinates := ⟨1, 0, 0⟩

/-- Pullback by `τ ↦ τ - 1`, an element of `Γ₀(6)`. -/
def inverseTranslation : LevelSixMatrix :=
  ⟨1, -1, 0, 1, by norm_num⟩

theorem inverseTranslation_discriminant :
    inverseTranslation.actOnDiscriminantGroup = id :=
  inverseTranslation.actOnDiscriminantGroup_eq_id

/-- The determinant-two image of infinity becomes the `1/3` cusp line
after inverse translation. -/
theorem atkinLehnerTwo_infinity_cusp :
    inverseTranslation.act (atkinLehnerTwo infinityCuspDual) =
      (⟨2, -12, 3⟩ : DualCoordinates) := by
  ext <;> norm_num [inverseTranslation, LevelSixMatrix.act_a,
    LevelSixMatrix.act_r, LevelSixMatrix.act_c,
    atkinLehnerTwo_eq, infinityCuspDual]

/-- The determinant-three image of infinity becomes the `1/2` cusp line
after inverse translation. -/
theorem atkinLehnerThree_infinity_cusp :
    inverseTranslation.act (atkinLehnerThree infinityCuspDual) =
      (⟨3, -12, 2⟩ : DualCoordinates) := by
  ext <;> norm_num [inverseTranslation, LevelSixMatrix.act_a,
    LevelSixMatrix.act_r, LevelSixMatrix.act_c,
    atkinLehnerThree_eq, infinityCuspDual]

/-- Fricke sends infinity directly to the zero cusp line. -/
theorem frickeSix_infinity_cusp :
    frickeSix infinityCuspDual = (⟨0, 0, 1⟩ : DualCoordinates) := by
  ext <;> norm_num [frickeSix_eq, infinityCuspDual]

theorem atkinLehnerTwo_infinity_period :
    periodVector (1 / 3 : ℂ) =
      complexScale (-(1 / 3 : ℂ))
        (inverseTranslation.act (atkinLehnerTwo infinityCuspDual)).toComplex := by
  rw [atkinLehnerTwo_infinity_cusp]
  ext <;> norm_num [periodVector_eq, complexScale_eq, DualCoordinates.toComplex_eq]

theorem atkinLehnerThree_infinity_period :
    periodVector (1 / 2 : ℂ) =
      complexScale (-(1 / 2 : ℂ))
        (inverseTranslation.act (atkinLehnerThree infinityCuspDual)).toComplex := by
  rw [atkinLehnerThree_infinity_cusp]
  ext <;> norm_num [periodVector_eq, complexScale_eq, DualCoordinates.toComplex_eq]

theorem frickeSix_infinity_period :
    periodVector 0 =
      complexScale (-1) (frickeSix infinityCuspDual).toComplex := by
  rw [frickeSix_infinity_cusp]
  ext <;> norm_num [periodVector_eq, complexScale_eq, DualCoordinates.toComplex_eq]

end Theta
end SptClassification
