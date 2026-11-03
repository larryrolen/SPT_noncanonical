/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.ConvergentProducts
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Powers of convergent integral coefficient series

Finite Cauchy multiplication identifies the analytic sum of each formal power.
This is used for the integral core `E₄³ P²⁴` of the modular invariant in
[rolenManuscript, §3].
-/

public section

namespace SptClassification.QSeries

/-- Evaluating a formal power commutes with taking powers of the analytic sum. -/
theorem hasSum_coefficientTerm_pow (F : PowerSeries ℤ) (q a : ℂ) (k : ℕ)
    (hF : HasSum (fun n => (F.coeff n : ℂ) * q ^ n) a) :
    HasSum (fun n => ((F ^ k).coeff n : ℂ) * q ^ n) (a ^ k) := by
  induction k with
  | zero =>
    simpa +contextual [PowerSeries.coeff_one] using hasSum_ite_eq (0 : ℕ) (1 : ℂ)
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact hasSum_coefficientTerm_mul _ _ _ _ _ ih.summable.norm hF.summable.norm ih hF

end SptClassification.QSeries
