/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.AnalyticProjection
public import SptClassification.ModularForms.CyclotomicSlash
public import SptClassification.ModularForms.LaurentProductExpansion

/-!
# The powered projection at the manuscript level

The literature theorem is stated at the exact level `N N_M` of
[garthwaiteJameson2021, Proposition 4, PDF p. 4], with `B = 0`.
Restriction to the manuscript's level `24 M N` and constant scaling are
proved below.
-/

public section

namespace SptClassification

open UpperHalfPlane
open scoped MatrixGroups

/-- The auxiliary level `N_M` in [garthwaiteJameson2021, (1), PDF p. 4]. -/
def progressionAuxiliaryLevel (M : ℕ) : ℕ :=
  if M.gcd 6 = 1 then M else
  if M.gcd 6 = 2 then 8 * M else
  if M.gcd 6 = 3 then 3 * M else 24 * M

/-- The cited level always divides the uniform level used in the manuscript. -/
theorem progressionAuxiliaryLevel_dvd (M : ℕ) :
    progressionAuxiliaryLevel M ∣ 24 * M := by
  unfold progressionAuxiliaryLevel
  split_ifs
  · exact ⟨24, by ring⟩
  · exact ⟨3, by ring⟩
  · exact ⟨8, by ring⟩
  · exact dvd_rfl

/-- The full level in the cited theorem divides `24 M N`. -/
theorem progression_source_level_dvd (M N : ℕ) :
    N * progressionAuxiliaryLevel M ∣ 24 * M * N := by
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    Nat.mul_dvd_mul_left N (progressionAuxiliaryLevel_dvd M)

/-- Congruence of integer entries descends along a divisibility of levels. -/
theorem intCast_congr_of_level_dvd {L N : ℕ} (hLN : L ∣ N) (a b : ℤ)
    (h : (a : ZMod N) = (b : ZMod N)) : (a : ZMod L) = (b : ZMod L) := by
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub a b L).2
  exact (show (L : ℤ) ∣ (N : ℤ) by exact_mod_cast hLN).trans
    ((ZMod.intCast_eq_intCast_iff_dvd_sub a b N).1 h)

/-- The same integral matrix belongs to `Γ₀(L)` if `L ∣ N`. -/
def gammaZeroOfLevelDvd {L N : ℕ} (hLN : L ∣ N)
    (γ : CongruenceSubgroup.Gamma0 N) : CongruenceSubgroup.Gamma0 L :=
  ⟨γ, by
    apply CongruenceSubgroup.Gamma0_mem.mpr
    simpa using intCast_congr_of_level_dvd hLN
      (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 1 0)
      0 (by simpa only [Int.cast_zero] using
        (CongruenceSubgroup.Gamma0_mem.mp γ.property))⟩

/-- Restricting the congruence subgroup preserves holomorphy at all cusps. -/
theorem HolomorphicGammaOneForm.of_level_dvd {L N k : ℕ}
    {F : UpperHalfPlane → ℂ} (hF : HolomorphicGammaOneForm L k F)
    (hLN : L ∣ N) : HolomorphicGammaOneForm N k F := by
  refine ⟨hF.holomorphic, ?_, hF.boundedAtCusps⟩
  intro γ ha hc hd τ
  apply hF.gammaOne γ
  · simpa using intCast_congr_of_level_dvd hLN _ 1 (by simpa using ha)
  · simpa using intCast_congr_of_level_dvd hLN _ 0 (by simpa using hc)
  · simpa using intCast_congr_of_level_dvd hLN _ 1 (by simpa using hd)

/-- [garthwaiteJameson2021, Proposition 4, PDF p. 4], specialized to `B = 0`.
The standard theta multiplier and finite pole orders are part of `g`; the
projection is the actual finite average. The exponent is `24 M N`, the
integral weight is that exponent times the original weight, and the level is
exactly `N N_M`. Rationality, faithful reduction and quadratic character in
`g` restrict the source theorem, which allows general Nebentypus. This is
an admitted literature result, not an admission of congruence propagation. -/
theorem garthwaiteJameson_powered_projection {p : ℕ}
    (g : ModularProgressionForm p) (M : ℕ) (hM : 0 < M) (u : ℤ) :
    (∀ (a : ℕ) (_ha : a.Coprime 6)
      (γ : CongruenceSubgroup.Gamma0 (g.level * progressionAuxiliaryLevel M)),
      (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ)
        0 0) = a →
      ∀ τ, progressionIntegralSlash (progressionPowerWeight g M) γ
        (fun z => analyticProgression M hM u g.toFun z ^ (24 * M * g.level)) τ =
        analyticProgression M hM ((a : ℤ) ^ 2 * u) g.toFun τ ^ (24 * M * g.level)) ∧
    (∃ s : ℕ, HolomorphicGammaOneForm (g.level * progressionAuxiliaryLevel M)
      (12 * s + progressionPowerWeight g M)
      (fun τ => (ModularForm.eta τ ^ 24) ^ s *
        analyticProgression M hM u g.toFun τ ^ (24 * M * g.level))) := by
  sorry

/-- The Fourier identity immediately before (1) in
[garthwaiteJameson2021, §2, PDF p. 4], specialized to `B = 0` and written
with all integer indices in the variable `X = q^(1/M)`. The row is exactly
the congruence-class mask of the original coefficients. This standard finite
Fourier projection identity is a named literature input. -/
theorem garthwaiteJameson_projection_expansion {p : ℕ}
    (g : ModularProgressionForm p) (M : ℕ) (hM : 0 < M) (u : ℤ)
    (τ : UpperHalfPlane) :
    HasSum (fun r : ℤ => ((QSeries.progressionRow g.coeff M u r : ℚ) : ℂ) *
      Function.Periodic.qParam M τ ^ r)
      (analyticProgression M hM u g.toFun τ) := by
  sorry

/-- The actual analytic projection realizes its bounded-below rational
Laurent series; no Fourier coefficients of a separate function are assumed. -/
theorem analyticProgression_laurent_hasSum {p : ℕ}
    (g : ModularProgressionForm p) (M : ℕ) (hM : 0 < M) (u : ℤ)
    (τ : UpperHalfPlane) :
    HasSum (fun r : ℤ =>
      ((QSeries.progressionLaurent g.coeff M u g.lowerBound).coeff r : ℂ) *
        Function.Periodic.qParam M τ ^ r)
      (analyticProgression M hM u g.toFun τ) := by
  simpa only [QSeries.progressionLaurent_coeff] using
    garthwaiteJameson_projection_expansion g M hM u τ

/-- Dividing the projection divides the actual convergent Laurent row.
This is used with the inverse reduction prime in the manuscript. -/
theorem analyticProgression_scaled_laurent_hasSum {p : ℕ}
    (g : ModularProgressionForm p) (M : ℕ) (hM : 0 < M) (u : ℤ)
    (c : ℚ) (τ : UpperHalfPlane) :
    HasSum (fun r : ℤ =>
      ((c • QSeries.progressionLaurent g.coeff M u g.lowerBound).coeff r : ℂ) *
        Function.Periodic.qParam M τ ^ r)
      ((c : ℂ) * analyticProgression M hM u g.toFun τ) := by
  simpa only [HahnSeries.coeff_smul, smul_eq_mul, Rat.cast_mul, mul_assoc] using
    (analyticProgression_laurent_hasSum g M hM u τ).mul_left (c : ℂ)

/-- Every power of the divided analytic projection has the coefficients of
the actual rational Laurent power. In particular the exponent `24 M N`
requires no coprimality hypothesis. -/
theorem analyticProgression_scaled_pow_laurent_hasSum {p : ℕ}
    (g : ModularProgressionForm p) (M : ℕ) (hM : 0 < M) (u : ℤ)
    (c : ℚ) (n : ℕ) (τ : UpperHalfPlane) :
    HasSum (fun r : ℤ =>
      (((c • QSeries.progressionLaurent g.coeff M u g.lowerBound) ^ n).coeff r : ℂ) *
        Function.Periodic.qParam M τ ^ r)
      (((c : ℂ) * analyticProgression M hM u g.toFun τ) ^ n) := by
  obtain ⟨B, hB⟩ := g.lowerBound
  apply laurent_pow_hasSum _ (-B).toNat ?_ _ _ (Complex.exp_ne_zero _)
    (analyticProgression_scaled_laurent_hasSum g M hM u c τ) n
  intro r hr
  have hrB : r < B := by omega
  rw [HahnSeries.coeff_smul, QSeries.progressionLaurent_coeff]
  by_cases hu : (r : ZMod M) = (u : ZMod M)
  · rw [QSeries.progressionRow_eq_of _ _ _ _ hu, hB r hrB, smul_zero]
  · rw [QSeries.progressionRow_eq_zero_of _ _ _ _ hu, smul_zero]

/-- Only the residue class of the progression label matters for the actual
analytic average. This justifies the source's choice of any representative
for its transformed label. -/
theorem analyticProgression_eq_of_congr {p : ℕ}
    (g : ModularProgressionForm p) (M : ℕ) (hM : 0 < M) (u v : ℤ)
    (huv : (u : ZMod M) = (v : ZMod M)) :
    analyticProgression M hM u g.toFun = analyticProgression M hM v g.toFun := by
  funext τ
  apply (garthwaiteJameson_projection_expansion g M hM u τ).unique
  simpa only [QSeries.progressionRow_congr g.coeff M u v huv] using
    garthwaiteJameson_projection_expansion g M hM v τ

/-- The powered transformation in the manuscript follows by inclusion of
congruence subgroups; the matrix and its upper-left entry are unchanged. -/
theorem analyticProgression_powered_slash {p : ℕ}
    (g : ModularProgressionForm p) (M : ℕ) (hM : 0 < M) (u : ℤ)
    (a : ℕ) (ha : a.Coprime 6)
    (γ : CongruenceSubgroup.Gamma0 (24 * M * g.level))
    (hγ : (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ)
      0 0) = a) (τ : UpperHalfPlane) :
    progressionIntegralSlash (progressionPowerWeight g M) γ
      (fun z => analyticProgression M hM u g.toFun z ^ (24 * M * g.level)) τ =
      analyticProgression M hM ((a : ℤ) ^ 2 * u) g.toFun τ ^ (24 * M * g.level) := by
  exact (garthwaiteJameson_powered_projection g M hM u).1 a ha
    (gammaZeroOfLevelDvd (progression_source_level_dvd M g.level) γ) hγ τ

/-- Pole clearing at every cusp, including after division by the power of the
reduction prime. No condition that the prime avoid the level is used. -/
theorem analyticProgression_divided_pole_clearing {p : ℕ}
    (g : ModularProgressionForm p) (M : ℕ) (hM : 0 < M) (u : ℤ) (c : ℂ) :
    ∃ s : ℕ, HolomorphicGammaOneForm (24 * M * g.level)
      (12 * s + progressionPowerWeight g M)
      (fun τ => c * ((ModularForm.eta τ ^ 24) ^ s *
        analyticProgression M hM u g.toFun τ ^ (24 * M * g.level))) := by
  obtain ⟨s, hs⟩ := (garthwaiteJameson_powered_projection g M hM u).2
  exact ⟨s, (hs.of_level_dvd (progression_source_level_dvd M g.level)).const_mul c⟩

end SptClassification
