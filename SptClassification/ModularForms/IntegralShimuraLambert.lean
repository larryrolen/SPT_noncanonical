/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.ConditionalLambert
public import SptClassification.ModularForms.PrincipalForms

/-!
# Integral q-expansion of the principal Shimura lift

The coefficient row is the actual integral row of `principalKForm`. The
finite divisor sum is the expansion of the Lambert series in
[rolenManuscript, Section 4, equation (J)], obtained there from
[borcherds1998, Theorem 14.3] and [liZemel2018, Theorem 5.1]. This file
establishes the formal integral series and its reduction; geometric
existence of a modular form with this expansion is a separate input.
-/

public section

namespace SptClassification

/-- The integral Lambert expansion prescribed for the weight-four Shimura
lift of the actual principal form `K_d`. -/
noncomputable def integralPrincipalShimuraLambertSeries (d : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk (fun n =>
    ∑ m ∈ n.divisors,
      characterTwelve (m : ℤ) * (n / m : ℕ) *
        QSeries.principalKFourier d ((m : ℤ) ^ 2))

/-- Every coefficient is the finite divisor sum of the actual `K_d` row. -/
theorem integralPrincipalShimuraLambertSeries_coeff (d n : ℕ) :
    (integralPrincipalShimuraLambertSeries d).coeff n =
      ∑ m ∈ n.divisors,
        characterTwelve (m : ℤ) * (n / m : ℕ) *
          QSeries.principalKFourier d ((m : ℤ) ^ 2) := by
  rw [integralPrincipalShimuraLambertSeries,
    PowerSeries.coeff_mk]

/-- The prescribed Shimura expansion has zero constant term at infinity,
as in [liZemel2018, Theorem 5.1] after the level-six specialization of
[rolenManuscript, Section 4, equation (J)]. -/
theorem integralPrincipalShimuraLambertSeries_coeff_zero (d : ℕ) :
    (integralPrincipalShimuraLambertSeries d).coeff 0 = 0 := by
  rw [integralPrincipalShimuraLambertSeries_coeff]
  simp

/-- Coefficientwise reduction of the integral Shimura expansion is precisely
the previously prescribed characteristic-`p` series. -/
theorem integralPrincipalShimuraLambertSeries_reduction
    (p d : ℕ) [Fact p.Prime] :
    PowerSeries.map (Int.castRingHom (ZMod p))
        (integralPrincipalShimuraLambertSeries d) =
      PowerSeries.mk (fun n =>
        ∑ m ∈ n.divisors, (characterTwelve (m : ℤ) : ZMod p) *
          (n / m : ℕ) *
            (QSeries.principalKFourier d ((m : ℤ) ^ 2) : ZMod p)) := by
  ext n
  rw [PowerSeries.coeff_map, integralPrincipalShimuraLambertSeries_coeff,
    PowerSeries.coeff_mk]
  change ((∑ m ∈ n.divisors,
      characterTwelve (m : ℤ) * (n / m : ℕ) *
        QSeries.principalKFourier d ((m : ℤ) ^ 2) : ℤ) : ZMod p) = _
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast]

/-- The integral divisor-sum expansion reduces to the principal weight-four
Lambert series. This identifies the q-expansion fixed by
[rolenManuscript, Section 4, equation (J)] with the existing formal
Shimura-lift row; it does not assert existence of an integral modular lift. -/
theorem integralPrincipalShimuraLambertSeries_map_eq_principal
    (p d : ℕ) [Fact p.Prime] :
    PowerSeries.map (Int.castRingHom (ZMod p))
        (integralPrincipalShimuraLambertSeries d) =
      QSeries.principalShimuraLambertSeries p d := by
  rw [integralPrincipalShimuraLambertSeries_reduction,
    QSeries.principalShimuraLambertSeries_eq]
  ext n
  rw [PowerSeries.coeff_mk, QSeries.coeff_shimuraLambertSeries,
    QSeries.shimuraLambertCoeff_eq_divisors]
  simp only [Int.natCast_pow]

/-- An integral q-expansion with the Fourier coefficients prescribed by the
complex Shimura lift has the exact integral divisor-sum expansion. This is
the coefficientwise descent step; existence of the integral modular lift is
a separate geometric question. [liZemel2018, Theorem 5.1]
[rolenManuscript, Section 4, equation (J)] -/
theorem integralPrincipalShimuraLambertSeries_eq_of_complex_expansion
    (d : ℕ) (f : PowerSeries ℤ)
    (hcomplex : PowerSeries.map (Int.castRingHom ℂ) f =
      PowerSeries.map (Int.castRingHom ℂ)
        (integralPrincipalShimuraLambertSeries d)) :
    f = integralPrincipalShimuraLambertSeries d := by
  ext n
  have h := congrArg (fun g : PowerSeries ℂ => g.coeff n) hcomplex
  simp only [PowerSeries.coeff_map] at h
  exact (Int.cast_injective : Function.Injective (fun z : ℤ => (z : ℂ))) h

/-- Any integral model with the complex Fourier expansion prescribed by the
independent Shimura lift has the principal reduction. This uses the
coefficient formula in [liZemel2018, Theorem 5.1] and leaves existence and
good-reduction regularity of that model as separate questions. -/
theorem integralShimuraExpansion_map_eq_principal
    (p d : ℕ) [Fact p.Prime] (f : PowerSeries ℤ)
    (hcomplex : PowerSeries.map (Int.castRingHom ℂ) f =
      PowerSeries.map (Int.castRingHom ℂ)
        (integralPrincipalShimuraLambertSeries d)) :
    PowerSeries.map (Int.castRingHom (ZMod p)) f =
      QSeries.principalShimuraLambertSeries p d := by
  rw [integralPrincipalShimuraLambertSeries_eq_of_complex_expansion d f hcomplex,
    integralPrincipalShimuraLambertSeries_map_eq_principal]

end SptClassification
