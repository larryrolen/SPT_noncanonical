/- Assembled by AxiomProver. -/

module

public import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# The Euler derivative of ordinary formal power series

The operator `X * d/dX` multiplies the coefficient of `X^n` by `n`. This is
the ordinary integral-exponent normalization used for the Lambert lifts.
-/

public section

namespace SptClassification.QSeries

open PowerSeries

/-- The Euler derivative on ordinary formal power series. -/
noncomputable def eulerDerivative {R : Type*} [CommSemiring R]
    (F : PowerSeries R) : PowerSeries R :=
  X * PowerSeries.derivative F

@[simp] theorem coeff_eulerDerivative {R : Type*} [CommSemiring R]
    (F : PowerSeries R) (n : ℕ) :
    (eulerDerivative F).coeff n = (n : R) * F.coeff n := by
  cases n with
  | zero => simp [eulerDerivative]
  | succ n =>
    rw [eulerDerivative, ← pow_one (X : PowerSeries R), PowerSeries.coeff_X_pow_mul,
      PowerSeries.coeff_derivative]
    simp [Nat.cast_add, Nat.cast_one, mul_comm]

@[simp] theorem constantCoeff_eulerDerivative {R : Type*} [CommSemiring R]
    (F : PowerSeries R) : constantCoeff (eulerDerivative F) = 0 := by
  calc
    constantCoeff (eulerDerivative F) = (eulerDerivative F).coeff 0 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff]
    _ = 0 := by simp

end SptClassification.QSeries
