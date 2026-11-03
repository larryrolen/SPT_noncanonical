/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.NormalizedDenominators
public import SptClassification.ModularForms.CyclotomicSlash

/-!
# Uniform denominators in the powered progression argument

The divided progression in [rolenManuscript, §2] is raised to a power and
multiplied by a power of the integral discriminant. These operations preserve
a common denominator prime to the reduction characteristic. The cited
cyclotomic slash principle then preserves this same denominator.
-/

public section

namespace SptClassification

namespace HasPrimeLocalCommonDenominator

variable {p : ℕ} [Fact p.Prime]

/-- Clearing a bounded-below row produces an actual integral Laurent series. -/
theorem exists_integral_laurent {F : LaurentSeries ℚ}
    (hF : HasPrimeLocalCommonDenominator p F.coeff)
    (hbelow : ∃ B : ℤ, ∀ r < B, F.coeff r = 0) :
    ∃ D : ℤ, ¬(p : ℤ) ∣ D ∧ ∃ Z : LaurentSeries ℤ,
      Z.map (Int.castRingHom ℚ) = (D : ℚ) • F := by
  classical
  obtain ⟨D, hD, hclear⟩ := iff_exists.mp hF
  choose z hz using hclear
  have hzbelow : ∃ B : ℤ, ∀ r < B, z r = 0 := by
    obtain ⟨B, hB⟩ := hbelow
    refine ⟨B, fun r hr => ?_⟩
    have heq := hz r
    rw [hB r hr, mul_zero] at heq
    exact_mod_cast heq.symm
  refine ⟨D, hD, QSeries.laurentOfRow z hzbelow, ?_⟩
  apply HahnSeries.ext
  funext r
  simpa only [QSeries.laurent_map_coeff, QSeries.laurentOfRow_coeff,
    Int.coe_castRingHom, HahnSeries.coeff_smul, smul_eq_mul] using (hz r).symm

/-- The denominator of a powered progression may grow to `D^R`, but stays
prime to `p`. No coprimality between the exponent and `p` is needed. -/
theorem integral_mul_pow {F : LaurentSeries ℚ}
    (hF : HasPrimeLocalCommonDenominator p F.coeff)
    (hbelow : ∃ B : ℤ, ∀ r < B, F.coeff r = 0)
    (δ : LaurentSeries ℤ) (s R : ℕ) :
    HasPrimeLocalCommonDenominator p
      (((δ.map (Int.castRingHom ℚ)) ^ s * F ^ R).coeff) := by
  obtain ⟨D, hD, Z, hZ⟩ := hF.exists_integral_laurent hbelow
  apply iff_exists.mpr
  have hp : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using
    (Fact.out : p.Prime))
  refine ⟨D ^ R, fun h => hD (hp.dvd_of_dvd_pow h), ?_⟩
  have hprod : (δ ^ s * Z ^ R).map (Int.castRingHom ℚ) =
      (D : ℚ) ^ R • ((δ.map (Int.castRingHom ℚ)) ^ s * F ^ R) := by
    rw [QSeries.laurent_map_mul, QSeries.laurent_map_pow,
      QSeries.laurent_map_pow, hZ, smul_pow, mul_smul_comm]
  intro r
  refine ⟨(δ ^ s * Z ^ R).coeff r, ?_⟩
  have heq := congrArg (fun A : LaurentSeries ℚ => A.coeff r) hprod
  simpa only [QSeries.laurent_map_coeff, Int.coe_castRingHom,
    HahnSeries.coeff_smul, smul_eq_mul, Int.cast_pow] using heq.symm

/-- On rational Fourier rows the integral slash theorem preserves a uniform
prime-local denominator, even at levels divisible by `p`. -/
theorem slash {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ N)
    (F : UpperHalfPlane → ℂ) (hF : HolomorphicGammaOneForm N k F)
    (γ : CongruenceSubgroup.Gamma0 N) (a b : ℕ → ℚ)
    (ha : HasIntegralWeightQExpansion F (fun n => (a n : ℂ)))
    (hb : HasIntegralWeightQExpansion (progressionIntegralSlash k γ F)
      (fun n => (b n : ℂ)))
    (hden : HasPrimeLocalCommonDenominator p a) :
    HasPrimeLocalCommonDenominator p b := by
  obtain ⟨D, hD, hclear⟩ := iff_exists.mp hden
  have hs := ha.const_mul (D : ℂ)
  have ht : HasIntegralWeightQExpansion
      (progressionIntegralSlash k γ (fun τ => (D : ℂ) * F τ))
      (fun n => (D : ℂ) * (b n : ℂ)) := by
    simpa only [progressionIntegralSlash_const_mul] using hb.const_mul (D : ℂ)
  have hi : ∀ n, (D : ℂ) * (a n : ℂ) ∈ cyclotomicCoefficientRing ζ := by
    intro n
    obtain ⟨z, hz⟩ := hclear n
    have hzC : (D : ℂ) * (a n : ℂ) = (z : ℂ) := by exact_mod_cast hz
    rw [hzC]
    exact (cyclotomicCoefficientRing ζ).algebraMap_mem z
  have hout := garthwaiteJameson_slash_cyclotomic_integral N k hN hk ζ hζ
    (fun τ => (D : ℂ) * F τ) (hF.const_mul D) γ _ _ hs ht hi
  refine iff_exists.mpr ⟨D, hD, fun n => ?_⟩
  have hint := cyclotomicCoefficientRing_isIntegral hN hζ (hout n)
  obtain ⟨z, hz⟩ := rational_eq_integer_of_complex_integral ((D : ℚ) * b n)
    (by simpa only [Rat.cast_mul, Rat.cast_intCast] using hint)
  exact ⟨z, hz.symm⟩

end HasPrimeLocalCommonDenominator

/-- The exact pole-cleared divided power used in the manuscript has one
denominator prime to `p`. The integral series `δ` may in particular be the
discriminant in the variable `q^(1/M)`. -/
theorem SptModularApproximation.poleClearedPower_commonDenominator
    {p Q : ℕ} {hp : 5 ≤ p} [Fact p.Prime] [Fact Q.Prime]
    (A : SptModularApproximation p Q hp) (M : ℕ) (u : ℤ)
    (hzero : ∀ r : ℤ, (r : ZMod M) = (u : ZMod M) → A.form.coeffMod r = 0)
    (δ : LaurentSeries ℤ) (s R : ℕ) :
    HasPrimeLocalCommonDenominator p
      (((δ.map (Int.castRingHom ℚ)) ^ s *
        ((p : ℚ)⁻¹ • QSeries.progressionLaurent A.form.coeff M u
          A.form.lowerBound) ^ R).coeff) := by
  let F := (p : ℚ)⁻¹ • QSeries.progressionLaurent A.form.coeff M u A.form.lowerBound
  have hcoeff (r : ℤ) : F.coeff r =
      (if (r : ZMod M) = (u : ZMod M) then A.form.coeff r else 0) / p := by
    change (p : ℚ)⁻¹ * (QSeries.progressionLaurent A.form.coeff M u
      A.form.lowerBound).coeff r = _
    rw [QSeries.progressionLaurent_coeff]
    by_cases hr : (r : ZMod M) = (u : ZMod M)
    · rw [QSeries.progressionRow_eq_of _ _ _ _ hr, if_pos hr]
      ring
    · rw [QSeries.progressionRow_eq_zero_of _ _ _ _ hr, if_neg hr]
      simp
  have hden : HasPrimeLocalCommonDenominator p F.coeff := by
    have heq : F.coeff = fun r : ℤ =>
        (if (r : ZMod M) = (u : ZMod M) then A.form.coeff r else 0) / p :=
      funext hcoeff
    rw [heq]
    exact A.dividedProjection_commonDenominator M u hzero
  apply hden.integral_mul_pow ?_ δ s R
  obtain ⟨B, hB⟩ := A.form.lowerBound
  refine ⟨B, fun r hr => ?_⟩
  rw [hcoeff, hB r hr]
  simp

end SptClassification
