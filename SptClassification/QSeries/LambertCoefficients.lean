/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.CharacterTwelve
public import SptClassification.QSeries.EulerDerivative
public import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.LinearCombination

/-!
# The coefficientwise differential relation between the two Lambert lifts

The coefficients of the logarithmic lift and the weight-four lift are finite
divisor sums. A relation at square indices implies their second/first Euler
derivative relation in characteristic `p`. Terms with indices divisible by two
or three vanish by the character; terms divisible by `p` are killed by the
outer Euler derivative.
-/

public section

namespace SptClassification.QSeries

/-- The coefficient of the logarithmic Lambert series attached to square coefficients. -/
def logarithmicLambertCoeff {K : Type*} [CommRing K] (h : ℕ → K) (n : ℕ) : K :=
  -∑ m ∈ n.divisors, (characterTwelve (m : ℤ) : K) * (m : K) * h (m ^ 2)

/-- The finite divisor sum defining a logarithmic Lambert coefficient. -/
theorem logarithmicLambertCoeff_eq_divisors {K : Type*} [CommRing K]
    (h : ℕ → K) (n : ℕ) :
    logarithmicLambertCoeff h n =
      -∑ m ∈ n.divisors, (characterTwelve (m : ℤ) : K) * (m : K) * h (m ^ 2) :=
  (rfl)

/-- The coefficient of the weight-four Lambert series attached to square coefficients. -/
def shimuraLambertCoeff {K : Type*} [CommRing K] (k : ℕ → K) (n : ℕ) : K :=
  ∑ m ∈ n.divisors, (characterTwelve (m : ℤ) : K) * (n / m : ℕ) * k (m ^ 2)

/-- The finite divisor sum defining a weight-four Lambert coefficient. -/
theorem shimuraLambertCoeff_eq_divisors {K : Type*} [CommRing K]
    (k : ℕ → K) (n : ℕ) :
    shimuraLambertCoeff k n =
      ∑ m ∈ n.divisors, (characterTwelve (m : ℤ) : K) * (n / m : ℕ) * k (m ^ 2) :=
  (rfl)

/-- A square-index coefficient relation yields the Euler derivative identity. -/
theorem lambert_differential_relation {K : Type*} [CommRing K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (d : K) (h k : ℕ → K)
    (hcoeff : ∀ m : ℕ, 0 < m → m.Coprime (6 * p) →
      (m : K) ^ 2 * h (m ^ 2) + d * k (m ^ 2) = 0) (n : ℕ) :
    (n : K) ^ 2 * logarithmicLambertCoeff h n =
      d * (n : K) * shimuraLambertCoeff k n := by
  simp only [logarithmicLambertCoeff, shimuraLambertCoeff, mul_neg,
    Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  have hdiv : m ∣ n := (Nat.mem_divisors.mp hm).1
  have hnpos : 0 < n := Nat.pos_of_ne_zero (Nat.mem_divisors.mp hm).2
  have hmpos : 0 < m := Nat.pos_of_dvd_of_pos hdiv hnpos
  by_cases htwo : 2 ∣ m
  · have hc : characterTwelve (m : ℤ) = 0 :=
      characterTwelve_eq_zero_of_two_dvd (by exact_mod_cast htwo)
    simp [hc]
  by_cases hthree : 3 ∣ m
  · have hc : characterTwelve (m : ℤ) = 0 :=
      characterTwelve_eq_zero_of_three_dvd (by exact_mod_cast hthree)
    simp [hc]
  by_cases hp : p ∣ m
  · have hn : (n : K) = 0 := (CharP.cast_eq_zero_iff K p n).mpr (hp.trans hdiv)
    simp [hn]
  have hcopTwo : m.Coprime 2 := (Nat.prime_two.coprime_iff_not_dvd.mpr htwo).symm
  have hcopThree : m.Coprime 3 := (Nat.prime_three.coprime_iff_not_dvd.mpr hthree).symm
  have hcopP : m.Coprime p := ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hp).symm
  have hcop : m.Coprime (6 * p) := by
    simpa only [show 2 * 3 = 6 by decide] using
      (hcopTwo.mul_right hcopThree).mul_right hcopP
  have hrelation := hcoeff m hmpos hcop
  have hquot : (n : K) = (m : K) * (n / m : ℕ) := by
    have hnat : n / m * m = n := Nat.div_mul_cancel hdiv
    simpa only [Nat.cast_mul, mul_comm] using congrArg (fun a : ℕ => (a : K)) hnat.symm
  rw [hquot]
  linear_combination -(characterTwelve (m : ℤ) : K) * (m : K) *
    ((n / m : ℕ) : K) ^ 2 * hrelation

/-- The formal logarithmic Lambert series, specified by its finite divisor-sum coefficients. -/
def logarithmicLambertSeries {K : Type*} [CommRing K] (h : ℕ → K) : PowerSeries K :=
  PowerSeries.mk (logarithmicLambertCoeff h)

theorem coeff_logarithmicLambertSeries {K : Type*} [CommRing K]
    (h : ℕ → K) (n : ℕ) :
    (logarithmicLambertSeries h).coeff n = logarithmicLambertCoeff h n := by
  simp [logarithmicLambertSeries]

/-- The formal weight-four Lambert series, specified by its finite divisor-sum coefficients. -/
def shimuraLambertSeries {K : Type*} [CommRing K] (k : ℕ → K) : PowerSeries K :=
  PowerSeries.mk (shimuraLambertCoeff k)

theorem coeff_shimuraLambertSeries {K : Type*} [CommRing K]
    (k : ℕ → K) (n : ℕ) :
    (shimuraLambertSeries k).coeff n = shimuraLambertCoeff k n := by
  simp [shimuraLambertSeries]

/-- The formal-series version of the differential identity for the two lifts. -/
theorem eulerDerivative_twice_logarithmicLambert {K : Type*} [CommRing K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (d : K) (h k : ℕ → K)
    (hcoeff : ∀ m : ℕ, 0 < m → m.Coprime (6 * p) →
      (m : K) ^ 2 * h (m ^ 2) + d * k (m ^ 2) = 0) :
    eulerDerivative (eulerDerivative (logarithmicLambertSeries h)) =
      PowerSeries.C d * eulerDerivative (shimuraLambertSeries k) := by
  ext n
  simp only [coeff_eulerDerivative, PowerSeries.coeff_C_mul,
    logarithmicLambertSeries, shimuraLambertSeries, PowerSeries.coeff_mk]
  simpa only [pow_two, mul_assoc] using lambert_differential_relation p d h k hcoeff n

end SptClassification.QSeries
