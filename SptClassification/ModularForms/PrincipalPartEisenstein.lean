/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.PrincipalPartJ
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-!
# The normalized Eisenstein series in the principal-part construction

The actual analytic `E₄` has the integer coefficients used in
`QSeries.eisensteinFourSeries`. Its convergent Fourier expansion therefore
agrees with that formal series. This supplies the Eisenstein component of the
analytic-to-formal comparison for `j = E₄³/Δ` [rolenManuscript, §3].
-/

public section

namespace SptClassification

open UpperHalfPlane
open scoped MatrixGroups

/-- The normalized analytic Eisenstein series has the prescribed integer coefficients. -/
theorem eisensteinFour_qExpansion_coeff (n : ℕ) :
    (qExpansion 1 ModularForm.E₄).coeff n = (QSeries.eisensteinFourCoefficient n : ℂ) := by
  rw [EisensteinSeries.E_qExpansion_coeff (by norm_num : 3 ≤ 4) (by decide)]
  norm_num [bernoulli_eq_bernoulli'_of_ne_one (by decide : 4 ≠ 1), bernoulli'_four]
  by_cases hn : n = 0
  · subst n
    simp
  · rw [QSeries.eisensteinFourCoefficient_of_ne_zero hn]
    simp [hn, ArithmeticFunction.sigma_apply]

/-- Equality of the analytic Fourier series and the coefficientwise complex image
of the integral series used for principal-part elimination. -/
theorem eisensteinFour_qExpansion :
    qExpansion 1 ModularForm.E₄ =
      QSeries.eisensteinFourSeries.map (Int.castRingHom ℂ) := by
  ext n
  simpa [PowerSeries.coeff_map, QSeries.eisensteinFourSeries_coeff] using
    eisensteinFour_qExpansion_coeff n

/-- The integral Fourier coefficients sum to the actual normalized analytic `E₄`
at every point of the upper half-plane. -/
theorem hasSum_eisensteinFourCoefficient (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ => (QSeries.eisensteinFourCoefficient n : ℂ) *
      Function.Periodic.qParam 1 τ ^ n) (ModularForm.E₄ τ) := by
  simpa only [eisensteinFour_qExpansion_coeff] using
    ModularForm.hasSum_qExpansion ModularForm.E₄ one_pos one_mem_strictPeriods_SL τ

end SptClassification
