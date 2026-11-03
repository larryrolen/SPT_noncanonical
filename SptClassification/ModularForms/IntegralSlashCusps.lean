/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.MeromorphicCusp

/-!
# Meromorphic cusps of integral slash transforms

Principal congruence normality supplies the period at every integral cusp.
An eventual exponential estimate on one strip then gives a meromorphic
q representative, as needed in [rolenManuscript, §3].
-/

public section

namespace SptClassification

open UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm

/-- A power of the standard translation acts by translation even at an
arbitrary integral weight. -/
theorem integral_slash_translation (f : UpperHalfPlane → ℂ) (k : ℤ) (n : ℤ)
    (τ : UpperHalfPlane) :
    (f ∣[k] (ModularGroup.T ^ n)) τ = f ((n : ℝ) +ᵥ τ) := by
  rw [ModularForm.SL_slash_apply, modular_T_zpow_smul]
  have hd : denom (ModularGroup.T ^ n : SL(2, ℤ)) (τ : ℂ) = 1 := by
    change (((ModularGroup.T ^ n) 1 0 : ℤ) : ℂ) * τ +
      (((ModularGroup.T ^ n) 1 1 : ℤ) : ℂ) = 1
    simp [ModularGroup.coe_T_zpow]
  rw [hd, one_zpow, mul_one]

/-- At a natural weight, the integral slash is the familiar quotient by
`(cτ+d)^k`, with no determinant factor. -/
theorem integral_slash_nat_apply (f : UpperHalfPlane → ℂ) (k : ℕ)
    (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    (f ∣[(k : ℤ)] γ) τ = f (γ • τ) / denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ ^ k := by
  rw [ModularForm.SL_slash_apply, zpow_neg, zpow_natCast, div_eq_mul_inv]
  rfl

/-- Level `N` is a period of every integral slash of a `Gamma0 N` invariant
function. This need not be the minimal cusp width. -/
theorem integral_slash_periodic_of_Gamma0
    {f : UpperHalfPlane → ℂ} {k : ℤ} {N : ℕ}
    (hinv : ∀ δ : SL(2, ℤ), δ ∈ CongruenceSubgroup.Gamma0 N → f ∣[k] δ = f)
    (γ : SL(2, ℤ)) :
    Function.Periodic ((f ∣[k] γ) ∘ ofComplex) (N : ℂ) := by
  have ht : ModularGroup.T ^ (N : ℤ) ∈ CongruenceSubgroup.Gamma N := by
    simpa using CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma
      (N : ℤ) (N : ℤ) (dvd_refl _)
  have hc := (CongruenceSubgroup.Gamma_normal N).conj_mem
    (ModularGroup.T ^ (N : ℤ)) ht γ
  have hc₀ : γ * ModularGroup.T ^ (N : ℤ) * γ⁻¹ ∈ CongruenceSubgroup.Gamma0 N :=
    CongruenceSubgroup.Gamma0_mem.mpr (CongruenceSubgroup.Gamma_mem.mp hc).2.2.1
  have he : (f ∣[k] γ) ∣[k] (ModularGroup.T ^ (N : ℤ)) = f ∣[k] γ := by
    have := congrArg (fun g : UpperHalfPlane → ℂ => g ∣[k] γ) (hinv _ hc₀)
    simpa only [← SlashAction.slash_mul, inv_mul_cancel_right] using this
  apply UpperHalfPlane.periodic_comp_ofComplex
  intro τ
  have := congrFun he τ
  simpa only [integral_slash_translation, Int.cast_natCast] using this

/-- Holomorphic integral slash transforms have meromorphic q representatives
if their growth on a strip of width `N` is at most exponential. -/
theorem exists_meromorphic_integral_slash_cusp
    {f : UpperHalfPlane → ℂ} {k : ℤ} {N : ℕ} (hN : 0 < N)
    (hhol : MDiff f)
    (hinv : ∀ δ : SL(2, ℤ), δ ∈ CongruenceSubgroup.Gamma0 N → f ∣[k] δ = f)
    (γ : SL(2, ℤ)) {a C A Y : ℝ} (hC : 0 ≤ C)
    (hgrowth : ∀ τ : UpperHalfPlane, a ≤ τ.re → τ.re < a + N → Y ≤ τ.im →
      ‖(f ∣[k] γ) τ‖ ≤ C * Real.exp (A * τ.im)) :
    ∃ G : ℂ → ℂ, MeromorphicAt G 0 ∧ ∀ τ : UpperHalfPlane,
      G (Function.Periodic.qParam N τ) = (f ∣[k] γ) τ := by
  exact exists_meromorphic_cusp_of_strip_exp_bound (by exact_mod_cast hN)
    (integral_slash_periodic_of_Gamma0 hinv γ)
    (hhol.slash k (γ : GL (Fin 2) ℝ)) hC hgrowth

/-- Strip estimates at every integral cusp give positive natural cusp widths
and meromorphic representatives at every cusp. -/
theorem meromorphic_integral_cusps_of_strip_exp_bounds
    {f : UpperHalfPlane → ℂ} {k : ℤ} {N : ℕ} (hN : 0 < N)
    (hhol : MDiff f)
    (hinv : ∀ δ : SL(2, ℤ), δ ∈ CongruenceSubgroup.Gamma0 N → f ∣[k] δ = f)
    (hgrowth : ∀ γ : SL(2, ℤ), ∃ a C A Y : ℝ, 0 ≤ C ∧
      ∀ τ : UpperHalfPlane, a ≤ τ.re → τ.re < a + N → Y ≤ τ.im →
        ‖(f ∣[k] γ) τ‖ ≤ C * Real.exp (A * τ.im)) :
    ∀ γ : SL(2, ℤ), ∃ width : ℕ, 0 < width ∧
      ∃ G : ℂ → ℂ, MeromorphicAt G 0 ∧ ∀ τ : UpperHalfPlane,
        G (Function.Periodic.qParam width τ) = (f ∣[k] γ) τ := by
  intro γ
  obtain ⟨a, C, A, Y, hC, hg⟩ := hgrowth γ
  exact ⟨N, hN, exists_meromorphic_integral_slash_cusp hN hhol hinv γ hC hg⟩

/-- A symmetric strip estimate also suffices. In applications it is enough
to request the strip radius `N`; its right half contains a full period. -/
theorem meromorphic_integral_cusps_of_symmetric_strip_exp_bounds
    {f : UpperHalfPlane → ℂ} {k : ℤ} {N : ℕ} (hN : 0 < N)
    (hhol : MDiff f)
    (hinv : ∀ δ : SL(2, ℤ), δ ∈ CongruenceSubgroup.Gamma0 N → f ∣[k] δ = f)
    (hgrowth : ∀ γ : SL(2, ℤ), ∃ C A Y : ℝ, 0 ≤ C ∧
      ∀ τ : UpperHalfPlane, |τ.re| ≤ N → Y ≤ τ.im →
        ‖(f ∣[k] γ) τ‖ ≤ C * Real.exp (A * τ.im)) :
    ∀ γ : SL(2, ℤ), ∃ width : ℕ, 0 < width ∧
      ∃ G : ℂ → ℂ, MeromorphicAt G 0 ∧ ∀ τ : UpperHalfPlane,
        G (Function.Periodic.qParam width τ) = (f ∣[k] γ) τ := by
  apply meromorphic_integral_cusps_of_strip_exp_bounds hN hhol hinv
  intro γ
  obtain ⟨C, A, Y, hC, hg⟩ := hgrowth γ
  refine ⟨0, C, A, Y, hC, ?_⟩
  intro τ hlo hhi hY
  apply hg τ _ hY
  rw [abs_of_nonneg hlo]
  simpa only [zero_add] using hhi.le

end SptClassification
