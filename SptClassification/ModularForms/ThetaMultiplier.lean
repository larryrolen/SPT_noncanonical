/- Assembled by AxiomProver. -/

module

public import Mathlib.NumberTheory.ModularForms.JacobiTheta.Manifold
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# Classical theta inputs

The convention is `jacobiTheta (2τ) = ∑ n, exp (2πi n²τ)`.
These two named literature premises concern theta alone, independently of
the smallest-parts function, its twists and its approximation.
-/

public section

namespace SptClassification

open UpperHalfPlane
open scoped MatrixGroups

/-- Nonvanishing of the theta constant in the upper half-plane.
This is the `z = 0` consequence of [nistDLMF, §20.2(iv)]: the zeros of
`θ₃(z | τ)` are `(m + 1/2 + (n + 1/2)τ)π`, for integers `m,n`.
The normalization `jacobiTheta τ = θ₃(0 | τ)` is that of §20.2(i), (20.2.3).
This is an admitted classical literature premise. -/
theorem dlmf_jacobiTheta_ne_zero (τ : ℂ) (hτ : 0 < τ.im) :
    jacobiTheta τ ≠ 0 := by
  sorry

/-- The fourth power of the standard theta multiplier on `Γ₀(4)`.
This is the fourth-power consequence of [koblitz1993, theorem on p. 148],
reproduced in [kunduMuller2025, arXiv v1, §2.5, p. 6]:
`Θ(γτ)/Θ(τ) = (c/d) ε_d⁻¹ sqrt(cτ+d)`.
For a unimodular matrix in `Γ₀(4)`, the symbol is ±1 and `ε_d⁴ = 1`.
The primary book has not been inspected; the cited secondary display has.
This admission uses neither a twisting theorem nor any weight restriction. -/
theorem koblitz_theta_multiplier_fourth
    (γ : CongruenceSubgroup.Gamma0 4) (τ : UpperHalfPlane) :
    (jacobiTheta (2 * ((γ • τ : UpperHalfPlane) : ℂ)) /
      jacobiTheta (2 * (τ : ℂ))) ^ 4 =
      denom (Matrix.SpecialLinearGroup.mapGL ℝ
        (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)) τ ^ 2 := by
  sorry

/-- The manuscript's theta constant has no zeros. -/
theorem theta_twice_ne_zero (τ : UpperHalfPlane) :
    jacobiTheta (2 * (τ : ℂ)) ≠ 0 := by
  apply dlmf_jacobiTheta_ne_zero
  simpa using mul_pos (by norm_num : (0 : ℝ) < 2) τ.im_pos

/-- Restrict the classical theta law to a level divisible by four. -/
theorem theta_multiplier_fourth_of_level_dvd {N : ℕ} (hN : 4 ∣ N)
    (γ : CongruenceSubgroup.Gamma0 N) (τ : UpperHalfPlane) :
    (jacobiTheta (2 * ((γ • τ : UpperHalfPlane) : ℂ)) /
      jacobiTheta (2 * (τ : ℂ))) ^ 4 =
      denom (Matrix.SpecialLinearGroup.mapGL ℝ
        (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)) τ ^ 2 := by
  let γ4 : CongruenceSubgroup.Gamma0 4 := ⟨γ, by
    apply CongruenceSubgroup.Gamma0_mem.mpr
    have h := CongruenceSubgroup.Gamma0_mem.mp γ.property
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h ⊢
    exact (show (4 : ℤ) ∣ (N : ℤ) by exact_mod_cast hN).trans h⟩
  exact koblitz_theta_multiplier_fourth γ4 τ

end SptClassification
