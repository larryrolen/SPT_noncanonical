/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.HolomorphicProducts
public import SptClassification.ModularForms.PoweredProjectionExpansion
public import SptClassification.ModularForms.PoweredDenominatorReduction
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Transporting the actual divided projection

The width-one expansions and uniform denominator are constructed from the
Laurent rows. [garthwaiteJameson2021, Theorem 5] then transports integrality
of the pole-cleared power. No prime-coprime-level hypothesis is used.
-/

public section

namespace SptClassification

/-- The actual rational pole-cleared power in the progression parameter. -/
noncomputable def poleClearedProjectionLaurent {p : ℕ}
    (g : ModularProgressionForm p) (M : ℕ) (hM : 0 < M)
    (u : ℤ) (c : ℚ) (s : ℕ) : LaurentSeries ℚ :=
  ((discriminantProgressionLaurent M (Nat.ne_of_gt hM)).map (Int.castRingHom ℚ)) ^ s *
    (c • QSeries.progressionLaurent g.coeff M u g.lowerBound) ^ (24 * M * g.level)

/-- Every nonzero coefficient is visible in the width-one Fourier row. -/
theorem poleClearedProjectionLaurent_support {p : ℕ}
    (g : ModularProgressionForm p) (M : ℕ) (hM : 0 < M)
    (u : ℤ) (c : ℚ) (s B : ℕ)
    (hB : ∀ r : ℤ, r < -(B : ℤ) → g.coeff r = 0)
    (hs : B * (24 * M * g.level) ≤ s * M) :
    ∀ r, (poleClearedProjectionLaurent g M hM u c s).coeff r ≠ 0 →
      ∃ n : ℕ, r = (M : ℤ) * n := by
  have hl : ∀ r, (c • QSeries.progressionLaurent g.coeff M u g.lowerBound).coeff r ≠ 0 →
      -(B : ℤ) ≤ r := by
    intro r hr
    by_contra hn
    apply hr
    rw [HahnSeries.coeff_smul, QSeries.progressionLaurent_coeff]
    by_cases hu : (r : ZMod M) = (u : ZMod M)
    · rw [QSeries.progressionRow_eq_of _ _ _ _ hu, hB r (by omega), smul_zero]
    · rw [QSeries.progressionRow_eq_zero_of _ _ _ _ hu, smul_zero]
  have hr : ∀ r, (c • QSeries.progressionLaurent g.coeff M u g.lowerBound).coeff r ≠ 0 →
      (r : ZMod M) = (u : ZMod M) := by
    intro r hr
    by_contra hn
    apply hr
    rw [HahnSeries.coeff_smul, QSeries.progressionLaurent_coeff,
      QSeries.progressionRow_eq_zero_of _ _ _ _ hn, smul_zero]
  intro r hnonzero
  obtain ⟨hpos, hmod⟩ := poleClearedLaurent_support M (Nat.ne_of_gt hM) _ B u hl hr
    s (24 * M * g.level) (dvd_mul_of_dvd_left (dvd_mul_left M 24) _) hs r hnonzero
  obtain ⟨n, hn⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd r M).mp hmod
  have hn0 : 0 ≤ n := by
    have hM' : (0 : ℤ) < M := by exact_mod_cast hM
    nlinarith
  exact ⟨n.toNat, by rw [Int.toNat_of_nonneg hn0]; exact hn⟩

/-- A sufficiently large holomorphic pole-clearing exponent gives a uniform
prime-local denominator for the entire transformed Laurent row. All coefficients
are those of the actual divided projection, not a separately postulated form. -/
theorem poleClearedProjection_transport {p : ℕ} [Fact p.Prime]
    (g : ModularProgressionForm p) (M : ℕ) (hM : 0 < M)
    (u : ℤ) (c : ℚ) (B : ℕ)
    (hB : ∀ r : ℤ, r < -(B : ℤ) → g.coeff r = 0)
    (hden : HasPrimeLocalCommonDenominator p
      (c • QSeries.progressionLaurent g.coeff M u g.lowerBound).coeff)
    (a : ℕ) (ha : a.Coprime 6)
    (γ : CongruenceSubgroup.Gamma0 (24 * M * g.level))
    (hγ : (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ)
      0 0) = a) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (24 * M * g.level)) :
    ∃ s : ℕ, 0 < s ∧ B * (24 * M * g.level) ≤ s * M ∧
      HasPrimeLocalCommonDenominator p
        (poleClearedProjectionLaurent g M hM ((a : ℤ) ^ 2 * u) c s).coeff := by
  let R := 24 * M * g.level
  obtain ⟨s, hs, hhol⟩ := analyticProgression_divided_pole_clearing_ge
    g M hM u ((c : ℂ) ^ R) (B * R + 1)
  have hs0 : 0 < s := by omega
  have hbound : B * R ≤ s * M := by nlinarith
  refine ⟨s, hs0, hbound, ?_⟩
  let F : UpperHalfPlane → ℂ := fun τ => (ModularForm.eta τ ^ 24) ^ s *
    ((c : ℂ) * analyticProgression M hM u g.toFun τ) ^ R
  have hholF : HolomorphicGammaOneForm (24 * M * g.level)
      (12 * s + progressionPowerWeight g M) F := by
    simpa only [F, mul_pow, mul_left_comm] using hhol
  have hR : M ∣ R := by dsimp [R]; exact dvd_mul_of_dvd_left (dvd_mul_left M 24) _
  have hexp (v : ℤ) := analyticProgression_poleCleared_hasSum_width_one
    g M hM v c B hB s R hR hbound
  have hsource : HasPrimeLocalCommonDenominator p
      (poleClearedProjectionLaurent g M hM u c s).coeff := by
    apply hden.integral_mul_pow
    refine ⟨-(B : ℤ), fun r hr => ?_⟩
    rw [HahnSeries.coeff_smul, QSeries.progressionLaurent_coeff]
    by_cases hu : (r : ZMod M) = (u : ZMod M)
    · rw [QSeries.progressionRow_eq_of _ _ _ _ hu, hB r hr, smul_zero]
    · rw [QSeries.progressionRow_eq_zero_of _ _ _ _ hu, smul_zero]
  suffices htransport : HasPrimeLocalCommonDenominator p (fun n : ℕ =>
      (poleClearedProjectionLaurent g M hM ((a : ℤ) ^ 2 * u) c s).coeff ((M : ℤ) * n)) by
    obtain ⟨D, hD, hclear⟩ := HasPrimeLocalCommonDenominator.iff_exists.mp htransport
    apply HasPrimeLocalCommonDenominator.iff_exists.mpr
    refine ⟨D, hD, fun r => ?_⟩
    by_cases hr : (poleClearedProjectionLaurent g M hM ((a : ℤ) ^ 2 * u) c s).coeff r = 0
    · exact ⟨0, by rw [hr]; simp⟩
    · obtain ⟨n, rfl⟩ := poleClearedProjectionLaurent_support g M hM
        ((a : ℤ) ^ 2 * u) c s B hB hbound r hr
      exact hclear n
  apply HasPrimeLocalCommonDenominator.slash (progressionPower_pos M g.level hM g.level_pos)
    (by positivity) ζ hζ F hholF γ
    (fun n : ℕ => (poleClearedProjectionLaurent g M hM u c s).coeff ((M : ℤ) * n))
  · apply HasIntegralWeightQExpansion.of_hasSum
    intro τ
    exact hexp u τ
  · rw [show progressionIntegralSlash (12 * s + progressionPowerWeight g M) γ F =
        (fun τ : UpperHalfPlane => (ModularForm.eta τ ^ 24) ^ s *
          ((c : ℂ) * analyticProgression M hM ((a : ℤ) ^ 2 * u) g.toFun τ) ^ R)
        from analyticProgression_poleCleared_slash g M hM u a ha γ hγ c s]
    apply HasIntegralWeightQExpansion.of_hasSum
    intro τ
    exact hexp ((a : ℤ) ^ 2 * u) τ
  · exact hsource.comp (fun n : ℕ => (M : ℤ) * n)

/-- The manuscript's powered-slash argument for forms with one denominator
prime to `p`. The modulus and exponent may both be divisible by `p`.
The normalized smallest-parts approximation satisfies this denominator condition. -/
theorem ModularProgressionForm.transport_of_commonDenominator
    {p : ℕ} [Fact p.Prime] (g : ModularProgressionForm p)
    (hden : HasPrimeLocalCommonDenominator p g.coeff)
    (M : ℕ) (hM : 0 < M) (u : ℤ) (a : ℕ)
    (ha : a.Coprime (6 * M * g.level))
    (hzero : ∀ r : ℤ, (r : ZMod M) = (u : ZMod M) → g.coeffMod r = 0) :
    ∀ r : ℤ, (r : ZMod M) = ((a : ZMod M) ^ 2 * (u : ZMod M)) →
      g.coeffMod r = 0 := by
  have hreduce (r : ℤ) : RationalReduces p (g.coeff r) (g.coeffMod r) := by
    obtain ⟨num, den, hd, hq, hz⟩ := g.pIntegral r
    rw [hq]
    exact RationalReduces.ofFraction p num den hd _ hz
  have hrowden (v : ℤ) : HasPrimeLocalCommonDenominator p
      (QSeries.progressionLaurent g.coeff M v g.lowerBound).coeff := by
    have heq : (QSeries.progressionLaurent g.coeff M v g.lowerBound).coeff =
        (fun r : ℤ => if (r : ZMod M) = (v : ZMod M) then g.coeff r else 0) := by
      funext r
      rw [QSeries.progressionLaurent_coeff]
      by_cases hr : (r : ZMod M) = (v : ZMod M)
      · rw [QSeries.progressionRow_eq_of _ _ _ _ hr, if_pos hr]
      · rw [QSeries.progressionRow_eq_zero_of _ _ _ _ hr, if_neg hr]
    rw [heq]
    exact hden.restrict (fun r : ℤ => (r : ZMod M) = (v : ZMod M))
  have hdivden : HasPrimeLocalCommonDenominator p
      ((p : ℚ)⁻¹ • QSeries.progressionLaurent g.coeff M u g.lowerBound).coeff := by
    have hh := (hrowden u).div_prime_of_zero (fun r => by
      rw [QSeries.progressionLaurent_coeff]
      by_cases hr : (r : ZMod M) = (u : ZMod M)
      · rw [QSeries.progressionRow_eq_of _ _ _ _ hr]
        simpa only [hzero r hr] using hreduce r
      · rw [QSeries.progressionRow_eq_zero_of _ _ _ _ hr]
        simpa only [Int.cast_zero] using RationalReduces.intCast p 0)
    convert hh using 1
    funext r
    simp only [HahnSeries.coeff_smul, smul_eq_mul, div_eq_mul_inv, mul_comm]
  obtain ⟨L, hL⟩ := g.lowerBound
  let B := (-L).toNat
  have hB : ∀ r : ℤ, r < -(B : ℤ) → g.coeff r = 0 := by
    intro r hr
    apply hL r
    dsimp [B] at hr
    omega
  obtain ⟨γ, hγ⟩ := exists_progression_gamma M g.level a hM g.level_pos ha
  have ha6 : a.Coprime 6 := Nat.Coprime.of_dvd_right
    (by exact ⟨M * g.level, by ring⟩) ha
  have hR := progressionPower_pos M g.level hM g.level_pos
  obtain ⟨s, _, hs, ht⟩ := poleClearedProjection_transport g M hM u (p : ℚ)⁻¹
    B hB hdivden a ha6 γ hγ _
    (Complex.isPrimitiveRoot_exp _ (Nat.ne_of_gt hR))
  let v : ℤ := (a : ℤ) ^ 2 * u
  let F := QSeries.progressionLaurent g.coeff M v g.lowerBound
  have hFbelow : ∃ L : ℤ, ∀ r < L, F.coeff r = 0 := by
    obtain ⟨B', hB'⟩ := QSeries.progressionRow_zero_below g.coeff M v g.lowerBound
    exact ⟨B', fun r hr => (QSeries.progressionLaurent_coeff _ _ _ _ r).trans (hB' r hr)⟩
  have hδ : (discriminantProgressionLaurent M (Nat.ne_of_gt hM)).map
      (Int.castRingHom (ZMod p)) ≠ 0 := by
    intro hz
    have hc := congrArg (fun A : LaurentSeries (ZMod p) => A.coeff (M : ℤ)) hz
    apply one_ne_zero (α := ZMod p)
    simpa only [QSeries.laurent_map_coeff, discriminantProgressionLaurent_coeff,
      map_one, HahnSeries.coeff_zero] using hc
  have hHbelow : ∃ L : ℤ, ∀ r < L,
      (poleClearedProjectionLaurent g M hM v (p : ℚ)⁻¹ s).coeff r = 0 := by
    refine ⟨0, fun r hr => ?_⟩
    by_contra hn
    obtain ⟨n, hn⟩ := poleClearedProjectionLaurent_support g M hM v _ s B hB hs r hn
    have : 0 ≤ r := by rw [hn]; positivity
    omega
  have hvanish := reduction_zero_of_divided_power (24 * M * g.level) s hR
    (discriminantProgressionLaurent M (Nat.ne_of_gt hM)) hδ F
    (QSeries.progressionRow g.coeffMod M v) (fun r => by
      dsimp only [F]
      rw [QSeries.progressionLaurent_coeff]
      by_cases hr : (r : ZMod M) = (v : ZMod M)
      · rw [QSeries.progressionRow_eq_of _ _ _ _ hr,
          QSeries.progressionRow_eq_of _ _ _ _ hr]
        exact hreduce r
      · rw [QSeries.progressionRow_eq_zero_of _ _ _ _ hr,
          QSeries.progressionRow_eq_zero_of _ _ _ _ hr]
        simpa only [Int.cast_zero] using RationalReduces.intCast p 0)
    (hrowden v) hFbelow ht hHbelow
  intro r hr
  have hrv : (r : ZMod M) = (v : ZMod M) := by simpa [v] using hr
  simpa only [QSeries.progressionRow_eq_of _ _ _ _ hrv] using hvanish r

end SptClassification
