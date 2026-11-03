/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.SquareClasses
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Translating discriminant characters to consecutive intervals

Multiplication by the inverse of24 turns the affine argument `1 - 24j` into a
translate of consecutive integers. The nonzero multiplier changes only the common
character value. The resulting interval has length `k - 1`, so an interval-length
estimate gives the least-index estimate with the required additive one.
-/

public section

namespace SptClassification

/-- Legendre symbols agree on equal residue-field elements. -/
theorem legendreSym_eq_of_cast_eq (p : ℕ) [Fact p.Prime] {a b : ℤ}
    (h : (a : ZMod p) = (b : ZMod p)) : legendreSym p a = legendreSym p b := by
  exact congrArg (quadraticChar (ZMod p)) h

/-- The discriminant character is a fixed nonzero multiplier times a translate. -/
theorem exists_discriminant_character_translation (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) :
    ∃ a : ℤ, ∀ j : ℤ, legendreSym p (1 - 24 * j) =
      legendreSym p (-24) * legendreSym p (j - a) := by
  have h24 : (24 : ZMod p) ≠ 0 :=
    ((ZMod.isUnit_iff_coprime 24 p).mpr
      (prime_coprime_twentyFour (Fact.out : p.Prime) hp).symm).ne_zero
  let u : ZMod p := (24 : ZMod p)⁻¹
  refine ⟨(u.val : ℤ), ?_⟩
  intro j
  have hmul : (24 : ZMod p) * (u.val : ZMod p) = 1 := by
    rw [ZMod.natCast_zmod_val]
    exact mul_inv_cancel₀ h24
  have hcast : ((1 - 24 * j : ℤ) : ZMod p) = ((-24 * (j - (u.val : ℤ)) : ℤ) : ZMod p) := by
    push_cast
    linear_combination -hmul
  exact (legendreSym_eq_of_cast_eq p hcast).trans (legendreSym.mul p _ _)

/-- A constant discriminant prefix gives a genuinely consecutive character interval. -/
theorem exists_constant_interval_of_discriminant_prefix (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) {k : ℕ} {c : ℤ}
    (hprefix : ∀ j : ℕ, 1 ≤ j → j < k → legendreSym p (1 - 24 * (j : ℤ)) = c) :
    ∃ start : ℤ, ∀ i : ℕ, i < k - 1 →
      legendreSym p (start + (i : ℤ)) = legendreSym p (-24) * c := by
  obtain ⟨a, htranslate⟩ := exists_discriminant_character_translation p hp
  have h24 : (24 : ZMod p) ≠ 0 :=
    ((ZMod.isUnit_iff_coprime 24 p).mpr
      (prime_coprime_twentyFour (Fact.out : p.Prime) hp).symm).ne_zero
  have hunit : ((-24 : ℤ) : ZMod p) ≠ 0 := by simpa using h24
  have hsquare := legendreSym.sq_one p hunit
  refine ⟨1 - a, ?_⟩
  intro i hi
  have hindex : (1 - a) + (i : ℤ) = ((i + 1 : ℕ) : ℤ) - a := by push_cast; ring
  rw [hindex]
  have hproduct := (htranslate ((i + 1 : ℕ) : ℤ)).symm.trans
    (hprefix (i + 1) (by omega) (by omega))
  calc
    legendreSym p (((i + 1 : ℕ) : ℤ) - a) =
        legendreSym p (-24) ^ 2 * legendreSym p (((i + 1 : ℕ) : ℤ) - a) := by rw [hsquare, one_mul]
    _ = legendreSym p (-24) *
        (legendreSym p (-24) * legendreSym p (((i + 1 : ℕ) : ℤ) - a)) := by ring
    _ = legendreSym p (-24) * c := by rw [hproduct]

/-- An interval estimate gives the source's least-index bound. The analytic
interval estimate is an explicit prerequisite of this arithmetic transfer lemma. -/
theorem character_prefix_index_le_of_interval_bound (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) (bound : ℝ)
    (hinterval : ∀ start : ℤ, ∀ length : ℕ, ∀ c : ℤ,
      (∀ i : ℕ, i < length → legendreSym p (start + (i : ℤ)) = c) → (length : ℝ) ≤ bound)
    {k : ℕ} (hk : 1 ≤ k) {c : ℤ}
    (hprefix : ∀ j : ℕ, 1 ≤ j → j < k → legendreSym p (1 - 24 * (j : ℤ)) = c) :
    (k : ℝ) ≤ bound + 1 := by
  obtain ⟨start, hconstant⟩ := exists_constant_interval_of_discriminant_prefix p hp hprefix
  have h := hinterval start (k - 1) (legendreSym p (-24) * c) hconstant
  rw [Nat.cast_sub hk, Nat.cast_one] at h
  linarith

end SptClassification
