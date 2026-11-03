/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.PrincipalPartElimination
public import SptClassification.QSeries.EulerDerivative

/-!
# Formal rows for the eta and derivative principal parts

If `U` is the ordinary unit series of `η=q^(1/24) U` and `J` is the unit
series of `j=q⁻¹ J`, then the rows below are the full Laurent coefficient
sequences of `η j^n` and `-η (Θ j) j^n`, respectively. In the second family
the pole index is shifted by one: row zero starts with `q^(-23/24)`.

The construction is coefficientwise and integral. Identification of `U` and
`J` with the analytic eta and modular invariant remains a separate bridge.
-/

public section

namespace SptClassification.QSeries

open PowerSeries

/-- The Laurent coefficients of `q^(-n) F`, indexed by the possible pole. -/
noncomputable def shiftedPrincipalRow (F : PowerSeries ℤ) (n : ℕ) (k : ℤ) : ℤ :=
  if k ≤ (n : ℤ) then F.coeff (((n : ℤ) - k).toNat) else 0

theorem shiftedPrincipalRow_eq (F : PowerSeries ℤ) (n : ℕ) (k : ℤ) :
    shiftedPrincipalRow F n k =
      if k ≤ (n : ℤ) then F.coeff (((n : ℤ) - k).toNat) else 0 := (rfl)

theorem shiftedPrincipalRow_leading (F : PowerSeries ℤ) (n : ℕ)
    (hF : F.coeff 0 = 1) :
    shiftedPrincipalRow F n (n : ℤ) = 1 := by
  simp [shiftedPrincipalRow, hF]

theorem shiftedPrincipalRow_above (F : PowerSeries ℤ) (n k : ℕ)
    (h : n < k) : shiftedPrincipalRow F n (k : ℤ) = 0 := by
  simp [shiftedPrincipalRow, show ¬(k : ℤ) ≤ n by exact_mod_cast Nat.not_le.mpr h]

/-- Coefficients of `η j^n`, provided `U` and `J` are the associated unit series. -/
noncomputable def etaJRow (U J : PowerSeries ℤ) (n : ℕ) : ℤ → ℤ :=
  shiftedPrincipalRow (U * J ^ n) n

theorem etaJRow_eq (U J : PowerSeries ℤ) (n : ℕ) (k : ℤ) :
    etaJRow U J n k = shiftedPrincipalRow (U * J ^ n) n k := (rfl)

/-- Coefficients of `-η (Θ j) j^n`, with the leading pole reindexed by `n`. -/
noncomputable def etaThetaJRow (U J : PowerSeries ℤ) (n : ℕ) : ℤ → ℤ :=
  shiftedPrincipalRow (U * (J - eulerDerivative J) * J ^ n) n

theorem etaThetaJRow_eq (U J : PowerSeries ℤ) (n : ℕ) (k : ℤ) :
    etaThetaJRow U J n k =
      shiftedPrincipalRow (U * (J - eulerDerivative J) * J ^ n) n k := (rfl)

/-- The ordinary core of `-Θ(q⁻¹ J)` has coefficient `(1-m)J_m`. -/
theorem coeff_negative_j_derivative_core (J : PowerSeries ℤ) (m : ℕ) :
    (J - eulerDerivative J).coeff m = (1 - (m : ℤ)) * J.coeff m := by
  rw [map_sub, coeff_eulerDerivative]
  ring

theorem etaJRow_leading (U J : PowerSeries ℤ)
    (hU : U.coeff 0 = 1) (hJ : J.coeff 0 = 1) (n : ℕ) :
    etaJRow U J n (n : ℤ) = 1 := by
  apply shiftedPrincipalRow_leading
  have hu : constantCoeff U = 1 := by simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hU
  have hj : constantCoeff J = 1 := by simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hJ
  simp [hu, hj]

theorem etaJRow_above (U J : PowerSeries ℤ) (n k : ℕ)
    (h : n < k) : etaJRow U J n (k : ℤ) = 0 :=
  shiftedPrincipalRow_above _ n k h

theorem etaThetaJRow_leading (U J : PowerSeries ℤ)
    (hU : U.coeff 0 = 1) (hJ : J.coeff 0 = 1) (n : ℕ) :
    etaThetaJRow U J n (n : ℤ) = 1 := by
  apply shiftedPrincipalRow_leading
  have hu : constantCoeff U = 1 := by simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hU
  have hj : constantCoeff J = 1 := by simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hJ
  simp [hu, hj]

theorem etaThetaJRow_above (U J : PowerSeries ℤ) (n k : ℕ)
    (h : n < k) : etaThetaJRow U J n (k : ℤ) = 0 :=
  shiftedPrincipalRow_above _ n k h

end SptClassification.QSeries
