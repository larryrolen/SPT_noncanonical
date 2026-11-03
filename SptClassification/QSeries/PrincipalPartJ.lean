/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.PrincipalPartBasis
public import Mathlib.NumberTheory.Divisors
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# The integral core of the modular invariant

The normalized Eisenstein series is `E₄=1+240∑_{n≥1}σ₃(n)qⁿ`.
When `P=q^(1/24)η⁻¹` is the ordinary partition series, the identity
`Δ=η²⁴` gives `j=q⁻¹ E₄³ P²⁴`. Thus the ordinary unit series `J` in the
principal-part rows is `E₄³ P²⁴` [rolenManuscript, §3]. This file proves
the integral leading coefficient required for row reduction; the analytic
identity with the Klein invariant is a separate obligation.
-/

public section

namespace SptClassification.QSeries

open PowerSeries

/-- The normalized integral Fourier coefficients of the weight-four Eisenstein series. -/
def eisensteinFourCoefficient (n : ℕ) : ℤ :=
  if n = 0 then 1 else 240 * ∑ d ∈ n.divisors, (d : ℤ) ^ 3

/-- The normalized Eisenstein coefficient at the constant term. -/
@[simp] theorem eisensteinFourCoefficient_zero : eisensteinFourCoefficient 0 = 1 := by
  simp [eisensteinFourCoefficient]

/-- The divisor sum for a positive-index Eisenstein coefficient. -/
theorem eisensteinFourCoefficient_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    eisensteinFourCoefficient n = 240 * ∑ d ∈ n.divisors, (d : ℤ) ^ 3 := by
  simp [eisensteinFourCoefficient, hn]

/-- The integral ordinary power series of the normalized weight-four Eisenstein series. -/
noncomputable def eisensteinFourSeries : PowerSeries ℤ :=
  PowerSeries.mk eisensteinFourCoefficient

/-- Coefficients of the integral Eisenstein series. -/
@[simp] theorem eisensteinFourSeries_coeff (n : ℕ) :
    eisensteinFourSeries.coeff n = eisensteinFourCoefficient n := by
  simp [eisensteinFourSeries]

@[simp] theorem eisensteinFourSeries_coeff_zero : eisensteinFourSeries.coeff 0 = 1 := by
  simp

/-- The unit series `qj` expressed through the ordinary eta reciprocal core. -/
noncomputable def modularJCore (P : PowerSeries ℤ) : PowerSeries ℤ :=
  eisensteinFourSeries ^ 3 * P ^ 24

/-- The integral ordinary core has the expected Eisenstein and partition factors. -/
theorem modularJCore_eq (P : PowerSeries ℤ) :
    modularJCore P = eisensteinFourSeries ^ 3 * P ^ 24 := (rfl)

theorem modularJCore_coeff_zero (P : PowerSeries ℤ) (hP : P.coeff 0 = 1) :
    (modularJCore P).coeff 0 = 1 := by
  have hp : constantCoeff P = 1 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hP
  have he : constantCoeff eisensteinFourSeries = 1 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using
      eisensteinFourSeries_coeff_zero
  simp [modularJCore, hp, he]

/-- The ordinary integral core `q^(-1/24)η`, formed from a partition series. -/
noncomputable def etaCoreFromPartition (P : PowerSeries ℤ) : PowerSeries ℤ :=
  P.invOfUnit 1

/-- The eta core is the unit inverse of the supplied partition series. -/
theorem etaCoreFromPartition_eq_invOfUnit (P : PowerSeries ℤ) :
    etaCoreFromPartition P = P.invOfUnit 1 := (rfl)

theorem partition_mul_etaCoreFromPartition (P : PowerSeries ℤ)
    (hP : P.coeff 0 = 1) :
    P * etaCoreFromPartition P = 1 := by
  have hp : constantCoeff P = 1 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hP
  exact PowerSeries.mul_invOfUnit P 1 hp

theorem etaCoreFromPartition_coeff_zero (P : PowerSeries ℤ)
    (hP : P.coeff 0 = 1) :
    (etaCoreFromPartition P).coeff 0 = 1 := by
  have hp : constantCoeff P = 1 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hP
  have h := congrArg constantCoeff (partition_mul_etaCoreFromPartition P hP)
  simp only [map_mul, map_one, hp, one_mul] at h
  simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using h

end SptClassification.QSeries
