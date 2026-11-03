/- Assembled by AxiomProver. -/

module

public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# Four-cusp criterion at level six

The classical cusp classification is the only literature input. Boundedness
transport and construction of a modular form are proved using Mathlib's slash
action. The criterion applies to any weight and any slash-invariant function.
-/

public section

open UpperHalfPlane Matrix OnePoint
open scoped MatrixGroups ModularForm Manifold

namespace SptClassification.LevelSixCuspCriterion

local notation "Γ₆" =>
  Subgroup.map (SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma0 6)

/-- The four cusp representatives of `Γ₀(6)`: infinity, zero, one half and
one third. This is [maier2009], §2, the cusp classification immediately before
(2.1), specialized to the divisors `1, 2, 3, 6` of six. Each contributes one
orbit since `gcd(d, 6/d) = 1`. The denominator-six orbit contains infinity,
and the denominator-one orbit contains zero. The statement concerns only
cusp orbits, independently of a modular form or its Fourier coefficients. -/
theorem maier_cusp_representatives_literature {c : OnePoint ℝ}
    (hc : IsCusp c Γ₆) :
    ∃ γ : GL (Fin 2) ℝ, γ ∈ Γ₆ ∧
      (γ • ∞ = c ∨ γ • (↑(0 : ℝ) : OnePoint ℝ) = c ∨
        γ • (↑(1 / 2 : ℝ) : OnePoint ℝ) = c ∨
        γ • (↑(1 / 3 : ℝ) : OnePoint ℝ) = c) := by
  sorry

/-- Boundedness is preserved along the group orbit of a cusp. -/
theorem boundedAt_translate {k : ℤ} (f : SlashInvariantForm Γ₆ k)
    {c : OnePoint ℝ} (hc : c.IsBoundedAt f k)
    {γ : GL (Fin 2) ℝ} (hγ : γ ∈ Γ₆) :
    (γ • c).IsBoundedAt f k := by
  rw [OnePoint.IsBoundedAt.smul_iff]
  change c.IsBoundedAt (f.toFun ∣[k] γ) k
  rw [f.slash_action_eq' γ hγ]
  exact hc

/-- Four independently proved cusp bounds imply boundedness at every cusp. -/
theorem boundedAt_all_cusps {k : ℤ} (f : SlashInvariantForm Γ₆ k)
    (hinfty : IsBoundedAtImInfty f)
    (hzero : (↑(0 : ℝ) : OnePoint ℝ).IsBoundedAt f k)
    (hhalf : (↑(1 / 2 : ℝ) : OnePoint ℝ).IsBoundedAt f k)
    (hthird : (↑(1 / 3 : ℝ) : OnePoint ℝ).IsBoundedAt f k)
    {c : OnePoint ℝ} (hc : IsCusp c Γ₆) : c.IsBoundedAt f k := by
  obtain ⟨γ, hγ, h | h | h | h⟩ := maier_cusp_representatives_literature hc
  · rw [← h]
    exact boundedAt_translate f (OnePoint.isBoundedAt_infty_iff.mpr hinfty) hγ
  · rw [← h]
    exact boundedAt_translate f hzero hγ
  · rw [← h]
    exact boundedAt_translate f hhalf hγ
  · rw [← h]
    exact boundedAt_translate f hthird hγ

/-- Bundle an independently holomorphic slash-invariant function after
checking its four cusp representatives. -/
def modularFormOfFourCusps {k : ℤ} (f : SlashInvariantForm Γ₆ k)
    (hhol : MDiff f) (hinfty : IsBoundedAtImInfty f)
    (hzero : (↑(0 : ℝ) : OnePoint ℝ).IsBoundedAt f k)
    (hhalf : (↑(1 / 2 : ℝ) : OnePoint ℝ).IsBoundedAt f k)
    (hthird : (↑(1 / 3 : ℝ) : OnePoint ℝ).IsBoundedAt f k) :
    ModularForm Γ₆ k where
  toSlashInvariantForm := f
  holo' := hhol
  bdd_at_cusps' := boundedAt_all_cusps f hinfty hzero hhalf hthird

@[simp] theorem modularFormOfFourCusps_apply {k : ℤ}
    (f : SlashInvariantForm Γ₆ k) (hhol : MDiff f)
    (hinfty : IsBoundedAtImInfty f)
    (hzero : (↑(0 : ℝ) : OnePoint ℝ).IsBoundedAt f k)
    (hhalf : (↑(1 / 2 : ℝ) : OnePoint ℝ).IsBoundedAt f k)
    (hthird : (↑(1 / 3 : ℝ) : OnePoint ℝ).IsBoundedAt f k)
    (z : UpperHalfPlane) :
    modularFormOfFourCusps f hhol hinfty hzero hhalf hthird z = f z := (rfl)

end SptClassification.LevelSixCuspCriterion
