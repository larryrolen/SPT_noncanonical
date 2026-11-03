/- Assembled by AxiomProver. -/

module

public import SptClassification.Theta.MetaplecticKernel
public import SptClassification.Theta.MetaplecticGeneratedGroup

/-!
# The central sign in the generated metaplectic group

Four standard inversion lifts have identity matrix and square-root factor
minus one. Their finite Weil action is minus the identity on every component.
The identity-matrix fiber of the concrete generated pairs therefore consists
of the two central signs. These are the central pairs for the convention in
[rolenManuscript, lines 339–343].
-/

public section

namespace SptClassification
namespace Theta

/-- The nontrivial central pair over the identity integral matrix. -/
def MetaplecticPair.centralSign : MetaplecticPair where
  matrix := 1
  factor _ := -1
  factor_sq z := by simp only [neg_one_sq, metaplecticDenominator_one]
  factor_ne_zero _ := by norm_num

@[simp] theorem MetaplecticPair.centralSign_matrix : centralSign.matrix = 1 := (rfl)

@[simp] theorem MetaplecticPair.centralSign_factor (z : UpperHalfPlane) :
    centralSign.factor z = -1 := (rfl)

/-- The fourth power of eta's inversion phase is minus one. -/
theorem etaWeilInversionFour_phase_eq_neg_one :
    etaWeilWordPhase (List.replicate 4 EtaWeilStep.inversion) = -1 := by
  have hphase : etaWeilWordPhase (List.replicate 4 EtaWeilStep.inversion) =
      (Complex.I.sqrt⁻¹) ^ 4 := by
    simp only [List.replicate_succ, List.replicate_zero,
      etaWeilWordPhase_cons, etaWeilWordPhase_nil,
      EtaWeilStep.phase_inversion, mul_one]
    ring
  rw [hphase, eta_inversion_phase]
  calc
    Complex.exp (-(Real.pi / 4) * Complex.I) ^ 4 =
        (Complex.exp (-(Real.pi / 4) * Complex.I) ^ 2) ^ 2 := by ring
    _ = (-Complex.I) ^ 2 := by rw [finiteWeilInversionPhase_sq]
    _ = -1 := by rw [neg_sq, Complex.I_sq]

/-- Four standard inversion lifts represent the nontrivial central pair. -/
theorem etaWeilInversionFour_pair_eq_centralSign :
    etaWeilWordMetaplecticPair (List.replicate 4 EtaWeilStep.inversion) =
      MetaplecticPair.centralSign := by
  apply MetaplecticPair.ext
  · simpa only [etaWeilWordMetaplecticPair_matrix,
      MetaplecticPair.centralSign] using etaWeilInversionFour_matrix_eq_one
  · funext z
    simp only [etaWeilWordMetaplecticPair_factor]
    rw [etaWeilWordFactor_of_matrix_one _ etaWeilInversionFour_matrix_eq_one,
      etaWeilInversionFour_phase_eq_neg_one]
    norm_num [MetaplecticPair.centralSign]

/-- Four finite inversion operators act by the nontrivial central sign on
the whole discriminant coefficient space. -/
theorem etaWeilInversionFour_finiteAction (f : ZMod 12 → ℂ) :
    etaWeilWordFiniteAction (List.replicate 4 EtaWeilStep.inversion) f =
      fun r => -f r := by
  simp only [List.replicate_succ, List.replicate_zero,
    etaWeilWordFiniteAction_cons, etaWeilWordFiniteAction_nil,
    EtaWeilStep.finiteAction_inversion]
  exact finiteWeilS_fourth f

/-- A concrete generated pair above the identity matrix is exactly one of
the two central signs. -/
theorem generatedPair_matrix_one_eq_one_or_centralSign
    (g : etaWeilGeneratedPairs) (hmatrix : g.val.matrix = 1) :
    g.val = 1 ∨ g.val = MetaplecticPair.centralSign := by
  have hconst (z : UpperHalfPlane) :
      g.val.factor z = g.val.factor UpperHalfPlane.I := by
    rw [generatedPair_factor_of_matrix_one g hmatrix z,
      generatedPair_factor_of_matrix_one g hmatrix UpperHalfPlane.I]
  have hsquare : g.val.factor UpperHalfPlane.I ^ 2 = 1 := by
    rw [g.val.factor_sq, hmatrix]
    simp only [metaplecticDenominator_one]
  have hprod : (g.val.factor UpperHalfPlane.I - 1) *
      (g.val.factor UpperHalfPlane.I + 1) = 0 := by
    calc
      (g.val.factor UpperHalfPlane.I - 1) *
          (g.val.factor UpperHalfPlane.I + 1) =
        g.val.factor UpperHalfPlane.I ^ 2 - 1 := by ring
      _ = 0 := by rw [hsquare]; ring
  rcases mul_eq_zero.mp hprod with hplus | hminus
  · left
    have hvalue : g.val.factor UpperHalfPlane.I = 1 := sub_eq_zero.mp hplus
    apply MetaplecticPair.ext
    · simpa only [MetaplecticPair.one_eq_identity,
        MetaplecticPair.identity_matrix] using hmatrix
    · funext z
      simp only [MetaplecticPair.one_eq_identity,
        MetaplecticPair.identity_factor]
      rw [hconst z, hvalue]
  · right
    have hvalue : g.val.factor UpperHalfPlane.I = -1 := by
      exact add_eq_zero_iff_eq_neg.mp hminus
    apply MetaplecticPair.ext
    · exact hmatrix
    · funext z
      change g.val.factor z = -1
      rw [hconst z, hvalue]

end Theta
end SptClassification
