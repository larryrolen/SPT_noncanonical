/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.EtaQuotientCuspsThirdCyclotomic
public import SptClassification.ModularForms.EtaQuotientCuspsDivisor
public import SptClassification.ModularForms.EtaQuotientCuspsDerivatives

/-!
# First-order arithmetic at the four cusps of the level-six eta quotient

The universal cubic-phase expansion is formed from the integral eta Euler
core, before any specialization of its phase. Its first coefficient controls
the actual analytic germs at the two width-three cusps. The reciprocal
infinity germ and the Fricke zero germ have slopes `1` and `72`.
These are local calculations for the coordinate in [rolen2026canonical],
Section 4; they do not construct the integral modular-curve model.
-/

public section

namespace SptClassification

open PowerSeries

private theorem etaIntegralCore_coeff_one :
    QSeries.etaIntegralCore.coeff 1 = -1 := by
  have h := congrArg (fun F : PowerSeries ℤ => F.coeff 1)
    QSeries.partitionSeries_mul_etaIntegralCore
  norm_num [PowerSeries.coeff_mul, Finset.antidiagonal] at h
  omega

theorem etaEulerCoreAtPolynomialPhase_one_coeff_one (P : Polynomial ℤ) :
    (etaEulerCoreAtPolynomialPhase 1 P).coeff 1 = -P := by
  simp [coeff_etaEulerCoreAtPolynomialPhase, etaIntegralCore_coeff_one]

theorem etaEulerCoreAtPolynomialPhase_coeff_one_of_two_le
    (n : ℕ) (hn : 2 ≤ n) (P : Polynomial ℤ) :
    (etaEulerCoreAtPolynomialPhase n P).coeff 1 = 0 := by
  have hndiv : ¬ n ∣ 1 := by
    intro h
    have := Nat.le_of_dvd (by decide : 0 < 1) h
    omega
  simp [coeff_etaEulerCoreAtPolynomialPhase, hndiv]

private theorem coeff_one_mul (F G : PowerSeries (Polynomial ℤ)) :
    (F * G).coeff 1 = F.coeff 0 * G.coeff 1 + F.coeff 1 * G.coeff 0 := by
  simp [PowerSeries.coeff_mul, Finset.antidiagonal]

private theorem coeff_one_pow_zero (F : PowerSeries (Polynomial ℤ))
    (hF : F.coeff 1 = 0) (m : ℕ) : (F ^ m).coeff 1 = 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, coeff_one_mul, ih, hF]
      simp

/-- The universal numerator has constant term one and slope `-X`. -/
theorem cuspHalfPolynomialNumerator_constantCoeff :
    constantCoeff cuspHalfPolynomialNumerator = 1 := by
  simp [cuspHalfPolynomialNumerator_eq,
    etaEulerCoreAtPolynomialPhase_constantCoeff]

theorem cuspHalfPolynomialNumerator_coeff_one :
    cuspHalfPolynomialNumerator.coeff 1 = -Polynomial.X := by
  rw [cuspHalfPolynomialNumerator_eq, coeff_one_mul,
    coeff_one_pow_zero _
      (etaEulerCoreAtPolynomialPhase_coeff_one_of_two_le 3 (by omega) 1) 5,
    etaEulerCoreAtPolynomialPhase_one_coeff_one]
  simp [etaEulerCoreAtPolynomialPhase_constantCoeff]

/-- The universal denominator has no linear term. -/
theorem cuspHalfPolynomialDenominator_coeff_one :
    cuspHalfPolynomialDenominator.coeff 1 = 0 := by
  rw [cuspHalfPolynomialDenominator_eq, coeff_one_mul,
    etaEulerCoreAtPolynomialPhase_coeff_one_of_two_le 6 (by omega),
    coeff_one_pow_zero _
      (etaEulerCoreAtPolynomialPhase_coeff_one_of_two_le 2 (by omega)
        (Polynomial.X ^ 2)) 5]
  simp

/-- The existing integral-polynomial half-cusp Euler quotient begins
`1 - Xq`. -/
theorem cuspHalfPolynomialEulerUnit_coeff_one :
    cuspHalfPolynomialEulerUnit.coeff 1 = -Polynomial.X := by
  have h := congrArg (fun F : PowerSeries (Polynomial ℤ) => F.coeff 1)
    cuspHalfPolynomialEulerUnit_mul_denominator
  rw [coeff_one_mul, cuspHalfPolynomialDenominator_coeff_one,
    coeff_zero_eq_constantCoeff_apply,
    cuspHalfPolynomialDenominator_constantCoeff,
    cuspHalfPolynomialNumerator_coeff_one] at h
  simpa using h

/-- The reciprocal universal third-cusp Euler quotient also has constant
coefficient one. -/
theorem cuspThirdPolynomialEulerUnit_constantCoeff :
    constantCoeff cuspThirdPolynomialEulerUnit = 1 := by
  simp [cuspThirdPolynomialEulerUnit_eq, PowerSeries.constantCoeff_invOfUnit]

/-- The reciprocal universal third-cusp Euler quotient begins `1 + Xq`. -/
theorem cuspThirdPolynomialEulerUnit_coeff_one :
    cuspThirdPolynomialEulerUnit.coeff 1 = Polynomial.X := by
  have h := congrArg (fun F : PowerSeries (Polynomial ℤ) => F.coeff 1)
    cuspThirdPolynomialEulerUnit_mul_half
  rw [coeff_one_mul, cuspHalfPolynomialEulerUnit_coeff_one] at h
  simp only [coeff_zero_eq_constantCoeff_apply,
    cuspHalfPolynomialEulerUnit_constantCoeff,
    cuspThirdPolynomialEulerUnit_constantCoeff] at h
  simp at h
  exact eq_of_sub_eq_zero h

/-- Evaluating the universal cusp expansions in a field gives the slopes
of the actual half- and third-cusp eta-quotient germs. -/
theorem cuspHalfPolynomialGerm_slope {k : Type*} [Field k] (ω : k) :
    Polynomial.eval₂ (Int.castRingHom k) ω
        ((-9 : Polynomial ℤ) * cuspHalfPolynomialEulerUnit.coeff 1) =
      9 * ω := by
  rw [cuspHalfPolynomialEulerUnit_coeff_one]
  simp

theorem cuspThirdPolynomialGerm_slope {k : Type*} [Field k] (ω : k) :
    Polynomial.eval₂ (Int.castRingHom k) ω
        ((-8 : Polynomial ℤ) * cuspThirdPolynomialEulerUnit.coeff 1) =
      -8 * ω := by
  rw [cuspThirdPolynomialEulerUnit_coeff_one]
  simp

/-- The whole universal half-cusp germ, multiplied by its exact eta
transformation factor and then specialized at a cubic phase, has slope
`9ω`. -/
theorem cuspHalfPolynomialGerm_coeff_one {k : Type*} [Field k] (ω : k) :
    (((-9 : PowerSeries (Polynomial ℤ)) * cuspHalfPolynomialEulerUnit).map
      (Polynomial.eval₂RingHom (Int.castRingHom k) ω)).coeff 1 = 9 * ω := by
  have hC : (-9 : PowerSeries (Polynomial ℤ)) = PowerSeries.C (-9 : Polynomial ℤ) := by
    exact (map_neg (PowerSeries.C : Polynomial ℤ →+* PowerSeries (Polynomial ℤ))
      (9 : Polynomial ℤ)).symm ▸ congrArg Neg.neg
        (map_ofNat (PowerSeries.C : Polynomial ℤ →+* PowerSeries (Polynomial ℤ)) 9).symm
  rw [hC]
  simp [PowerSeries.coeff_map, PowerSeries.coeff_mul, Finset.antidiagonal,
    cuspHalfPolynomialEulerUnit_coeff_one, cuspHalfPolynomialEulerUnit_constantCoeff]

/-- The reciprocal universal third-cusp germ, with its exact factor `-8`,
has slope `-8ω` after specialization. -/
theorem cuspThirdPolynomialGerm_coeff_one {k : Type*} [Field k] (ω : k) :
    (((-8 : PowerSeries (Polynomial ℤ)) * cuspThirdPolynomialEulerUnit).map
      (Polynomial.eval₂RingHom (Int.castRingHom k) ω)).coeff 1 = -8 * ω := by
  have hC : (-8 : PowerSeries (Polynomial ℤ)) = PowerSeries.C (-8 : Polynomial ℤ) := by
    exact (map_neg (PowerSeries.C : Polynomial ℤ →+* PowerSeries (Polynomial ℤ))
      (8 : Polynomial ℤ)).symm ▸ congrArg Neg.neg
        (map_ofNat (PowerSeries.C : Polynomial ℤ →+* PowerSeries (Polynomial ℤ)) 8).symm
  rw [hC]
  simp [PowerSeries.coeff_map, PowerSeries.coeff_mul, Finset.antidiagonal,
    cuspThirdPolynomialEulerUnit_coeff_one,
    cuspThirdPolynomialEulerUnit_constantCoeff]

/-- The cubic cusp phase is a unit in any field. -/
theorem cubicPhase_ne_zero {k : Type*} [Field k] {ω : k}
    (hω : ω ^ 3 = 1) : ω ≠ 0 := by
  intro hz
  simp [hz] at hω

/-- In characteristic at least five both width-three cusp slopes survive
reduction. The slopes are those of the existing analytic eta germs. -/
theorem cuspPolynomialGerm_slopes_ne_zero {k : Type*} [Field k]
    (p : ℕ) [CharP k p] (hp : 5 ≤ p) {ω : k} (hω : ω ^ 3 = 1) :
    9 * ω ≠ 0 ∧ -8 * ω ≠ 0 := by
  have h2 : (2 : k) ≠ 0 := by
    intro hz
    have hd : p ∣ 2 := (CharP.cast_eq_zero_iff k p 2).mp hz
    exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) hd
  have h3 : (3 : k) ≠ 0 := by
    intro hz
    have hd : p ∣ 3 := (CharP.cast_eq_zero_iff k p 3).mp hz
    exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) hd
  have h9 : (9 : k) ≠ 0 := by
    convert pow_ne_zero 2 h3 using 1; norm_num
  have h8 : (8 : k) ≠ 0 := by
    convert pow_ne_zero 3 h2 using 1; norm_num
  exact ⟨mul_ne_zero h9 (cubicPhase_ne_zero hω),
    mul_ne_zero (neg_ne_zero.mpr h8) (cubicPhase_ne_zero hω)⟩

/-- The other two cusp slopes, from the actual reciprocal and Fricke germs,
also survive reduction in characteristic at least five. -/
theorem levelSixInfinityZeroGerm_slopes_ne_zero {k : Type*} [Field k]
    (p : ℕ) [CharP k p] (hp : 5 ≤ p) :
    (1 : k) ≠ 0 ∧ (72 : k) ≠ 0 := by
  have h2 : (2 : k) ≠ 0 := by
    intro hz
    have hd : p ∣ 2 := (CharP.cast_eq_zero_iff k p 2).mp hz
    exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) hd
  have h3 : (3 : k) ≠ 0 := by
    intro hz
    have hd : p ∣ 3 := (CharP.cast_eq_zero_iff k p 3).mp hz
    exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) hd
  constructor
  · exact one_ne_zero
  · have h72 : (72 : k) = 2 ^ 3 * 3 ^ 2 := by norm_num
    rw [h72]
    exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)

/-- The integral Euler series for `q t(τ)` remains a unit at the infinity
cusp. Its inverse supplies the existing reciprocal eta-quotient germ. -/
theorem levelSixRescaledEulerUnit_constantCoeff :
    constantCoeff levelSixRescaledEulerUnit = 1 := by
  have h := congrArg constantCoeff levelSixRescaledEulerUnit_mul_denominator
  simpa only [map_mul, levelSixRescaledEulerDenominator_constantCoeff,
    levelSixRescaledEulerNumerator_constantCoeff, mul_one] using h

/-- The reciprocal-coordinate expansion formed from the integral Euler unit
has first coefficient one. This is the infinity local parameter. -/
theorem levelSixInfinityReciprocalIntegral_coeff_one :
    (PowerSeries.X * levelSixRescaledEulerUnit.invOfUnit 1).coeff 1 = 1 := by
  simp [PowerSeries.coeff_mul, Finset.antidiagonal,
    PowerSeries.constantCoeff_invOfUnit]

/-- The Fricke cusp expansion has the same integral local parameter, scaled
by the exact eta transformation factor `72`. -/
theorem levelSixZeroCuspIntegral_coeff_one :
    ((72 : PowerSeries ℤ) * PowerSeries.X *
      levelSixRescaledEulerUnit.invOfUnit 1).coeff 1 = 72 := by
  simp [PowerSeries.coeff_mul, Finset.antidiagonal,
    PowerSeries.constantCoeff_invOfUnit]

/-- The arithmetic infinity coefficient equals the derivative of the actual
reciprocal eta-quotient germ from the cusp divisor calculation. -/
theorem levelSixInfinityReciprocalIntegral_matches_deriv :
    (deriv (fun q : ℂ => q / levelSixEulerUnit q) 0) =
      ((PowerSeries.X * levelSixRescaledEulerUnit.invOfUnit 1).coeff 1 : ℂ) := by
  rw [hasDerivAt_levelSixInfinityReciprocalGerm.deriv,
    levelSixInfinityReciprocalIntegral_coeff_one]
  norm_num

/-- The arithmetic Fricke coefficient equals the derivative of the actual
zero-cusp eta-quotient germ. -/
theorem levelSixZeroCuspIntegral_matches_deriv :
    (deriv (fun q : ℂ => 72 * q / levelSixEulerUnit q) 0) =
      (((72 : PowerSeries ℤ) * PowerSeries.X *
        levelSixRescaledEulerUnit.invOfUnit 1).coeff 1 : ℂ) := by
  rw [hasDerivAt_levelSixZeroGerm.deriv,
    levelSixZeroCuspIntegral_coeff_one]
  norm_num

/-- At the complex cubic phase, the arithmetic slopes coincide with the
first Taylor coefficients of the genuine analytic cusp Euler units. -/
theorem cuspHalfEulerTaylorCoeff_one :
    cuspHalfEulerTaylorSeries.coeff 1 =
      -Function.Periodic.qParam 1 (-1 / 3 : ℂ) := by
  rw [cuspHalfEulerTaylorCoeff_cyclotomic,
    cuspHalfPolynomialEulerUnit_coeff_one]
  simp

theorem cuspThirdEulerTaylorCoeff_one :
    cuspThirdEulerTaylorSeries.coeff 1 =
      Function.Periodic.qParam 1 (-1 / 3 : ℂ) := by
  rw [cuspThirdEulerTaylorCoeff_cyclotomic,
    cuspThirdPolynomialEulerUnit_coeff_one]
  simp

/-- The specialized integral-polynomial half-cusp coefficient is the
derivative of the actual analytic eta-quotient germ. -/
theorem cuspHalfPolynomialGerm_coeff_one_matches_deriv :
    deriv (fun q : ℂ => -9 * cuspHalfEulerUnit q) 0 =
      (((-9 : PowerSeries (Polynomial ℤ)) * cuspHalfPolynomialEulerUnit).map
        (Polynomial.eval₂RingHom (Int.castRingHom ℂ)
          (Function.Periodic.qParam 1 (-1 / 3 : ℂ)))).coeff 1 := by
  rw [hasDerivAt_levelSixHalfCuspGerm.deriv,
    cuspHalfPolynomialGerm_coeff_one]

/-- The specialized integral-polynomial third-cusp coefficient is the
derivative of the actual analytic eta-quotient germ. -/
theorem cuspThirdPolynomialGerm_coeff_one_matches_deriv :
    deriv (fun q : ℂ => -8 * cuspThirdEulerUnit q) 0 =
      (((-8 : PowerSeries (Polynomial ℤ)) * cuspThirdPolynomialEulerUnit).map
        (Polynomial.eval₂RingHom (Int.castRingHom ℂ)
          (Function.Periodic.qParam 1 (-1 / 3 : ℂ)))).coeff 1 := by
  rw [hasDerivAt_levelSixThirdCuspGerm.deriv,
    cuspThirdPolynomialGerm_coeff_one]

/-- All four arithmetic local slopes are nonzero after reduction to a field
of characteristic at least five, for any cubic phase. -/
theorem levelSixFourCuspLocalSlopes_ne_zero {k : Type*} [Field k]
    (p : ℕ) [CharP k p] (hp : 5 ≤ p) {ω : k} (hω : ω ^ 3 = 1) :
    (1 : k) ≠ 0 ∧ (72 : k) ≠ 0 ∧ 9 * ω ≠ 0 ∧ -8 * ω ≠ 0 := by
  rcases levelSixInfinityZeroGerm_slopes_ne_zero (k := k) p hp with
    ⟨hinfty, hzero⟩
  rcases cuspPolynomialGerm_slopes_ne_zero (k := k) p hp hω with
    ⟨hhalf, hthird⟩
  exact ⟨hinfty, hzero, hhalf, hthird⟩

end SptClassification
