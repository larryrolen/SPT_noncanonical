/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.ConditionalCoefficient
public import SptClassification.QSeries.LambertCoefficients

/-!
# Lambert derivatives of the prescribed principal forms

The two formal series use the actual integral Fourier rows of `H_d` and
`K_d`, reduced modulo `p`. Their coefficients are the finite divisor sums
for the logarithmic and weight-four lifts in [rolenManuscript, §4,
equations (L) and (J)]. The differential relation is conditional only on
the finite product constant terms specified in `ConstantTermInputs`.
-/

@[expose] public section

namespace SptClassification.QSeries

/-- The logarithmic Lambert series formed from the prescribed `H_d`
square-index coefficients. Its constant coefficient is zero. -/
noncomputable def principalLogarithmicLambertSeries (p d : ℕ) [Fact p.Prime] :
    PowerSeries (ZMod p) :=
  logarithmicLambertSeries
    (fun r => (principalHFourier d (fFourier d) (r : ℤ) : ZMod p))

/-- The principal logarithmic lift as the Lambert series of its prescribed Fourier row. -/
theorem principalLogarithmicLambertSeries_eq (p d : ℕ) [Fact p.Prime] :
    principalLogarithmicLambertSeries p d =
      logarithmicLambertSeries
        (fun r => (principalHFourier d (fFourier d) (r : ℤ) : ZMod p)) :=
  (rfl)

/-- The weight-four Lambert series formed from the prescribed `K_d`
square-index coefficients. Its constant coefficient is zero. -/
noncomputable def principalShimuraLambertSeries (p d : ℕ) [Fact p.Prime] :
    PowerSeries (ZMod p) :=
  shimuraLambertSeries
    (fun r => (principalKFourier d (r : ℤ) : ZMod p))

/-- The principal weight-four lift as the Lambert series of its Fourier row. -/
theorem principalShimuraLambertSeries_eq (p d : ℕ) [Fact p.Prime] :
    principalShimuraLambertSeries p d =
      shimuraLambertSeries
        (fun r => (principalKFourier d (r : ℤ) : ZMod p)) :=
  (rfl)

/-- The coefficientwise relation `Θ²L_d = d ΘJ_d` for the actual principal
form rows, under the finite constant-term inputs. Terms supported at two
or three vanish by `χ₁₂`, and the outer derivative kills terms divisible by
`p`. [rolenManuscript, §4, equation (differential)] -/
theorem conditional_principal_lambert_coefficient_relation
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (sign : ℤ)
    (hsign : sign = 1 ∨ sign = -1) (d : ℕ) (hdPos : 0 < d)
    (hd : d % 24 = 23)
    (hr : legendreSym p (-(d : ℤ)) = sign)
    (hspt : ∀ j : ℕ, legendreSym p (1 - 24 * (j : ℤ)) = sign →
      ((spt j : ℤ) : ZMod p) = 0)
    (hCT : ConstantTermInputs p) (n : ℕ) :
    (n : ZMod p) ^ 2 * (principalLogarithmicLambertSeries p d).coeff n =
      (d : ZMod p) * (n : ZMod p) *
        (principalShimuraLambertSeries p d).coeff n := by
  have hcoeff : ∀ m : ℕ, 0 < m → m.Coprime (6 * p) →
      (m : ZMod p) ^ 2 *
        (principalHFourier d (fFourier d) ((m : ℤ) ^ 2) : ZMod p) +
        (d : ZMod p) * (principalKFourier d ((m : ℤ) ^ 2) : ZMod p) = 0 :=
    fun m hmPos hmCop =>
      conditional_square_coefficient_relation_mod p hp sign hsign d hdPos hd
        hr hspt hCT m hmPos hmCop
  simpa only [principalLogarithmicLambertSeries,
    principalShimuraLambertSeries, coeff_logarithmicLambertSeries,
    coeff_shimuraLambertSeries] using
    lambert_differential_relation p (d : ZMod p)
      (fun r => (principalHFourier d (fFourier d) (r : ℤ) : ZMod p))
      (fun r => (principalKFourier d (r : ℤ) : ZMod p)) hcoeff n

/-- The formal differential identity for the two genuine principal-form
Lambert series. It is the q-expansion input for the later homogeneous
modular-form argument. [rolenManuscript, §4] -/
theorem conditional_principal_lambert_differential
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (sign : ℤ)
    (hsign : sign = 1 ∨ sign = -1) (d : ℕ) (hdPos : 0 < d)
    (hd : d % 24 = 23)
    (hr : legendreSym p (-(d : ℤ)) = sign)
    (hspt : ∀ j : ℕ, legendreSym p (1 - 24 * (j : ℤ)) = sign →
      ((spt j : ℤ) : ZMod p) = 0)
    (hCT : ConstantTermInputs p) :
    eulerDerivative (eulerDerivative (principalLogarithmicLambertSeries p d)) =
      PowerSeries.C (d : ZMod p) *
        eulerDerivative (principalShimuraLambertSeries p d) := by
  have hcoeff : ∀ m : ℕ, 0 < m → m.Coprime (6 * p) →
      (m : ZMod p) ^ 2 *
        (principalHFourier d (fFourier d) ((m : ℤ) ^ 2) : ZMod p) +
        (d : ZMod p) * (principalKFourier d ((m : ℤ) ^ 2) : ZMod p) = 0 :=
    fun m hmPos hmCop =>
      conditional_square_coefficient_relation_mod p hp sign hsign d hdPos hd
        hr hspt hCT m hmPos hmCop
  simpa only [principalLogarithmicLambertSeries,
    principalShimuraLambertSeries] using
    eulerDerivative_twice_logarithmicLambert p (d : ZMod p)
      (fun r => (principalHFourier d (fFourier d) (r : ℤ) : ZMod p))
      (fun r => (principalKFourier d (r : ℤ) : ZMod p)) hcoeff

end SptClassification.QSeries
