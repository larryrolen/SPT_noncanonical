/- Assembled by AxiomProver. -/

module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.Basic.Complex.Basic

/-!
# Finite character sums

Elementary orthogonality and moment identities used in the Burgess argument for
the corrected interval estimate of Treviño [trevino2012, trevino2017].
-/

public section

namespace SptClassification

/-- The mean of a nonprincipal character vanishes on every translated residue field. -/
theorem sum_character_translate_eq_zero (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) (a : ZMod p) :
    (∑ x : ZMod p, χ (x + a)) = 0 := by
  have hsum := Equiv.sum_comp (Equiv.addRight a) (fun x : ZMod p => χ x)
  simpa [Equiv.addRight] using hsum.trans (MulChar.sum_eq_zero_of_ne_one hχ)

/-- Every full block of residues contains both a zero and a unit value of a
Dirichlet character. In particular, a constant interval is shorter than its
prime modulus. -/
theorem constant_character_interval_lt_modulus (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (start : ℤ) (length : ℕ) (c : ℂ)
    (hconstant : ∀ i : ℕ, i < length → χ ((start : ZMod p) + (i : ZMod p)) = c) :
    length < p := by
  by_contra hnot
  have hle : p ≤ length := Nat.le_of_not_gt hnot
  let i₀ := (-(start : ZMod p)).val
  let i₁ := ((1 : ZMod p) - (start : ZMod p)).val
  have hi₀ : i₀ < length := lt_of_lt_of_le (ZMod.val_lt _) hle
  have hi₁ : i₁ < length := lt_of_lt_of_le (ZMod.val_lt _) hle
  have h₀ : χ ((start : ZMod p) + (i₀ : ZMod p)) = 0 := by
    simpa [i₀] using (MulChar.map_zero χ)
  have h₁ : χ ((start : ZMod p) + (i₁ : ZMod p)) = 1 := by
    simp [i₁]
  have hc₀ := hconstant i₀ hi₀
  have hc₁ := hconstant i₁ hi₁
  rw [h₀] at hc₀
  rw [h₁] at hc₁
  exact one_ne_zero (hc₁.trans hc₀.symm)

end SptClassification
