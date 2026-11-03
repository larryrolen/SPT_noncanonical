/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.ProgressionDenominators

/-!
# Reduction of a divided Laurent power

Clearing the two prime-to-`p` denominators reduces the final step of
[rolenManuscript, §2] to cancellation in `𝔽ₚ((X))`. This retains the
actual rational coefficients and allows `p` to divide the power.
-/

public section

namespace SptClassification

/-- A prime-local divided power forces the original row to vanish modulo `p`,
provided the integral pole-clearing factor has nonzero reduction. -/
theorem reduction_zero_of_divided_power
    {p : ℕ} [Fact p.Prime] (R s : ℕ) (hR : 0 < R)
    (δ : LaurentSeries ℤ) (hδ : δ.map (Int.castRingHom (ZMod p)) ≠ 0)
    (F : LaurentSeries ℚ) (f : ℤ → ZMod p)
    (hred : ∀ r, RationalReduces p (F.coeff r) (f r))
    (hF : HasPrimeLocalCommonDenominator p F.coeff)
    (hbelow : ∃ B : ℤ, ∀ r < B, F.coeff r = 0)
    (hH : HasPrimeLocalCommonDenominator p
      (((δ.map (Int.castRingHom ℚ)) ^ s * ((p : ℚ)⁻¹ • F) ^ R).coeff))
    (hHbelow : ∃ B : ℤ, ∀ r < B,
      ((δ.map (Int.castRingHom ℚ)) ^ s * ((p : ℚ)⁻¹ • F) ^ R).coeff r = 0) :
    ∀ r, f r = 0 := by
  let H := (δ.map (Int.castRingHom ℚ)) ^ s * ((p : ℚ)⁻¹ • F) ^ R
  obtain ⟨E, hE, Z, hZ⟩ := hF.exists_integral_laurent hbelow
  obtain ⟨D, hD, T, hT⟩ := hH.exists_integral_laurent hHbelow
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hscale : (p : ℚ) ^ R • H = (δ.map (Int.castRingHom ℚ)) ^ s * F ^ R := by
    dsimp [H]
    rw [smul_pow, mul_smul_comm, smul_smul]
    simp [← mul_pow, hp0]
  have heq : (D : ℤ) • (δ ^ s * Z ^ R) =
      (p : ℤ) ^ R • ((E : ℤ) ^ R • T) := by
    have heqQ : ((D : ℤ) • (δ ^ s * Z ^ R)).map (Int.castRingHom ℚ) =
        ((p : ℤ) ^ R • ((E : ℤ) ^ R • T)).map (Int.castRingHom ℚ) := by
      simp only [QSeries.laurent_map_smul, QSeries.laurent_map_mul,
        QSeries.laurent_map_pow, map_pow, Int.coe_castRingHom, Int.cast_natCast]
      rw [hZ, hT, smul_pow, mul_smul_comm]
      change (D : ℚ) • ((E : ℚ) ^ R •
        ((δ.map (Int.castRingHom ℚ)) ^ s * F ^ R)) =
        (p : ℚ) ^ R • ((E : ℚ) ^ R • ((D : ℚ) • H))
      rw [← hscale]
      simp only [smul_smul]
      congr 1
      ring
    apply HahnSeries.ext
    funext r
    have hc := congrArg (fun A : LaurentSeries ℚ => A.coeff r) heqQ
    simp only [QSeries.laurent_map_coeff, Int.coe_castRingHom] at hc
    exact_mod_cast hc
  let red := Int.castRingHom (ZMod p)
  have hD0 : (D : ZMod p) ≠ 0 := fun hz =>
    hD ((ZMod.intCast_zmod_eq_zero_iff_dvd D p).mp hz)
  have hE0 : (E : ZMod p) ≠ 0 := fun hz =>
    hE ((ZMod.intCast_zmod_eq_zero_iff_dvd E p).mp hz)
  have hzero : (δ.map red) ^ s * (Z.map red) ^ R = 0 := by
    have hm := congrArg (fun A : LaurentSeries ℤ => A.map red) heq
    simp only [QSeries.laurent_map_smul, QSeries.laurent_map_mul,
      QSeries.laurent_map_pow, map_pow] at hm
    have hp : red (p : ℤ) = 0 := by simp [red]
    rw [hp, zero_pow (by omega : R ≠ 0), zero_smul] at hm
    exact (smul_eq_zero.mp hm).resolve_left hD0
  have hZzero := QSeries.laurent_eq_zero_of_delta_power_zero p R s
    (δ.map red) (Z.map red) hδ hR hzero
  intro r
  have hcoeff := congrArg (fun A : LaurentSeries ℚ => A.coeff r) hZ
  have hzred := (RationalReduces.intCast p E).mul (hred r)
  have hzq : (E : ℚ) * F.coeff r = (Z.coeff r : ℚ) := by
    simpa only [QSeries.laurent_map_coeff, Int.coe_castRingHom,
      HahnSeries.coeff_smul, smul_eq_mul] using hcoeff.symm
  rw [hzq] at hzred
  have hr := hzred.unique (RationalReduces.intCast p (Z.coeff r))
  have hz0 : (Z.coeff r : ZMod p) = 0 := by
    have hc := congrArg (fun A : LaurentSeries (ZMod p) => A.coeff r) hZzero
    exact hc
  rw [hz0] at hr
  exact (mul_eq_zero.mp hr).resolve_left hE0

end SptClassification
