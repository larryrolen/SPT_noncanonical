/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.PoweredProjection
public import Mathlib.NumberTheory.ModularForms.Discriminant

/-!
# Increasing the discriminant power in pole clearing

The actual discriminant is holomorphic at every cusp. Multiplying by further
powers therefore preserves pole clearing, so the exponent in
[garthwaiteJameson2021, Proposition 4] can also meet an explicit Fourier bound.
-/

public section

namespace SptClassification

open UpperHalfPlane
open scoped MatrixGroups ModularForm

/-- The natural-weight slash agrees with mathlib's integral-weight action. -/
theorem progressionIntegralSlash_eq_slash (k : ℕ)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (F : UpperHalfPlane → ℂ) :
    progressionIntegralSlash k γ F = F ∣[(k : ℤ)] γ := by
  funext τ
  simp only [progressionIntegralSlash_apply, ModularForm.SL_slash_apply,
    zpow_neg, zpow_natCast, div_eq_mul_inv]
  rfl

/-- Products add integral weights. -/
theorem progressionIntegralSlash_mul (k l : ℕ)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (F G : UpperHalfPlane → ℂ) :
    progressionIntegralSlash (k + l) γ (fun τ : UpperHalfPlane => F τ * G τ) =
      fun τ => progressionIntegralSlash k γ F τ *
        progressionIntegralSlash l γ G τ := by
  funext τ
  simp only [progressionIntegralSlash_apply, pow_add, mul_div_mul_comm]

/-- Holomorphic forms at the same level are closed under multiplication. -/
theorem HolomorphicGammaOneForm.mul {N k l : ℕ}
    {F G : UpperHalfPlane → ℂ} (hF : HolomorphicGammaOneForm N k F)
    (hG : HolomorphicGammaOneForm N l G) :
    HolomorphicGammaOneForm N (k + l) (fun τ : UpperHalfPlane => F τ * G τ) := by
  refine ⟨hF.holomorphic.mul hG.holomorphic, ?_, ?_⟩
  · intro γ ha hc hd τ
    simp only [progressionIntegralSlash_mul,
      hF.gammaOne γ ha hc hd, hG.gammaOne γ ha hc hd]
  · intro γ
    rw [progressionIntegralSlash_mul]
    exact (hF.boundedAtCusps γ).mul (hG.boundedAtCusps γ)

/-- The weight-zero unit is holomorphic at every level. -/
theorem holomorphicGammaOneForm_one (N : ℕ) :
    HolomorphicGammaOneForm N 0 (fun _ => 1) := by
  refine ⟨mdifferentiable_const, ?_, ?_⟩
  · intro γ _ _ _ τ
    simp [progressionIntegralSlash_apply]
  · intro γ
    have heq : progressionIntegralSlash 0 γ (fun _ => (1 : ℂ)) = (fun _ => 1) := by
      funext τ
      simp [progressionIntegralSlash_apply]
    rw [heq]
    exact Filter.const_boundedAtFilter UpperHalfPlane.atImInfty (1 : ℂ)

/-- Powers multiply integral weights and preserve all cusp conditions. -/
theorem HolomorphicGammaOneForm.pow {N k : ℕ}
    {F : UpperHalfPlane → ℂ} (hF : HolomorphicGammaOneForm N k F) (n : ℕ) :
    HolomorphicGammaOneForm N (k * n) (fun τ : UpperHalfPlane => F τ ^ n) := by
  induction n with
  | zero => simpa using holomorphicGammaOneForm_one N
  | succ n ih => simpa only [Nat.mul_succ, pow_succ] using ih.mul hF

/-- Every power of the full-level discriminant is invariant under slash. -/
theorem progressionIntegralSlash_discriminant_pow (s : ℕ)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    progressionIntegralSlash (12 * s) γ (fun τ : UpperHalfPlane => (ModularForm.eta τ ^ 24) ^ s) =
      (fun τ : UpperHalfPlane => (ModularForm.eta τ ^ 24) ^ s) := by
  have hd : progressionIntegralSlash 12 γ (fun τ : UpperHalfPlane => ModularForm.eta τ ^ 24) =
      (fun τ : UpperHalfPlane => ModularForm.eta τ ^ 24) := by
    rw [progressionIntegralSlash_eq_slash]
    exact SlashInvariantForm.slash_action_generators_SL2Z
      ModularForm.discriminant_S_invariant ModularForm.discriminant_T_invariant γ
  funext τ
  have h := congrFun hd τ
  simp only [progressionIntegralSlash_apply] at h ⊢
  rw [pow_mul, ← div_pow, h]

/-- Mathlib's discriminant cusp form gives holomorphy at any level. -/
theorem holomorphicGammaOneForm_discriminant (N : ℕ) :
    HolomorphicGammaOneForm N 12 (fun τ : UpperHalfPlane => ModularForm.eta τ ^ 24) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ModularFormClass.holo CuspForm.discriminant
  · intro γ _ _ _ τ
    rw [progressionIntegralSlash_eq_slash]
    exact congrFun (SlashInvariantForm.slash_action_generators_SL2Z
      ModularForm.discriminant_S_invariant ModularForm.discriminant_T_invariant γ) τ
  · intro γ
    rw [progressionIntegralSlash_eq_slash]
    exact ModularFormClass.bdd_at_infty_slash CuspForm.discriminant γ

/-- A pole-clearing exponent may be chosen above any prescribed bound. -/
theorem analyticProgression_divided_pole_clearing_ge {p : ℕ}
    (g : ModularProgressionForm p) (M : ℕ) (hM : 0 < M) (u : ℤ)
    (c : ℂ) (bound : ℕ) :
    ∃ s : ℕ, bound ≤ s ∧ HolomorphicGammaOneForm (24 * M * g.level)
      (12 * s + progressionPowerWeight g M)
      (fun τ : UpperHalfPlane => c * ((ModularForm.eta τ ^ 24) ^ s *
        analyticProgression M hM u g.toFun τ ^ (24 * M * g.level))) := by
  obtain ⟨s, hs⟩ := analyticProgression_divided_pole_clearing g M hM u c
  refine ⟨bound + s, Nat.le_add_right _ _, ?_⟩
  have h := ((holomorphicGammaOneForm_discriminant (24 * M * g.level)).pow bound).mul hs
  simpa only [Nat.mul_add, Nat.add_assoc, pow_add, mul_left_comm, mul_assoc] using h

/-- The pole-cleared divided power transforms to the actual square-indexed
projection, with the discriminant factor unchanged. -/
theorem analyticProgression_poleCleared_slash {p : ℕ}
    (g : ModularProgressionForm p) (M : ℕ) (hM : 0 < M) (u : ℤ)
    (a : ℕ) (ha : a.Coprime 6)
    (γ : CongruenceSubgroup.Gamma0 (24 * M * g.level))
    (hγ : (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ)
      0 0) = a) (c : ℂ) (s : ℕ) :
    progressionIntegralSlash (12 * s + progressionPowerWeight g M) γ
      (fun τ : UpperHalfPlane => (ModularForm.eta τ ^ 24) ^ s *
        (c * analyticProgression M hM u g.toFun τ) ^ (24 * M * g.level)) =
    (fun τ : UpperHalfPlane => (ModularForm.eta τ ^ 24) ^ s *
      (c * analyticProgression M hM ((a : ℤ) ^ 2 * u) g.toFun τ) ^
        (24 * M * g.level)) := by
  simp_rw [mul_pow]
  rw [progressionIntegralSlash_mul]
  simp_rw [progressionIntegralSlash_discriminant_pow,
    progressionIntegralSlash_const_mul,
    analyticProgression_powered_slash g M hM u a ha γ hγ]

end SptClassification

