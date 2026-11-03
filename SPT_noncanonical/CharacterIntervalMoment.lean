/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.CharacterSumsMoment

/-!
# Quadratic moments over consecutive residue shifts

For an interval shorter than the modulus, its natural shifts are distinct.
The general correlation identity therefore specializes to an exact quadratic
moment with the actual interval length [trevino2012, trevino2017].
-/

public section

namespace SptClassification

/-- The residue classes of the natural shifts in an interval. -/
def intervalResidues (p length : ℕ) : Finset (ZMod p) :=
  (Finset.range length).image (fun i : ℕ => (i : ZMod p))

/-- Natural shifts remain distinct after reduction modulo `p` while the
interval is no longer than the modulus. -/
theorem intervalResidues_natCast_injOn (p : ℕ) [Fact p.Prime]
    (length : ℕ) (hlength : length ≤ p) :
    Set.InjOn (fun i : ℕ => (i : ZMod p)) (Finset.range length) := by
  intro i hi j hj hij
  have hip : i < p := lt_of_lt_of_le (Finset.mem_range.mp hi) hlength
  have hjp : j < p := lt_of_lt_of_le (Finset.mem_range.mp hj) hlength
  calc
    i = (i : ZMod p).val := (ZMod.val_natCast_of_lt hip).symm
    _ = (j : ZMod p).val := congrArg ZMod.val hij
    _ = j := ZMod.val_natCast_of_lt hjp

/-- An interval of length at most the modulus has distinct residue shifts. -/
theorem intervalResidues_card (p : ℕ) [Fact p.Prime]
    (length : ℕ) (hlength : length ≤ p) :
    (intervalResidues p length).card = length := by
  unfold intervalResidues
  exact (Finset.card_image_iff.mpr
    (intervalResidues_natCast_injOn p length hlength)).trans
      (Finset.card_range length)

/-- Summing over the residue shifts agrees with the original interval sum. -/
theorem sum_character_intervalResidues_eq_range (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (start : ZMod p)
    (length : ℕ) (hlength : length ≤ p) :
    (∑ a ∈ intervalResidues p length, χ (start + a)) =
      ∑ i ∈ Finset.range length, χ (start + (i : ZMod p)) := by
  unfold intervalResidues
  exact Finset.sum_image (fun i hi j hj hij =>
    intervalResidues_natCast_injOn p length hlength hi hj hij)

/-- Exact ratio correlation moment for `length` consecutive residue shifts. -/
theorem sum_character_interval_ratio_moment (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1)
    (length : ℕ) (hlength : length ≤ p) :
    (∑ a ∈ intervalResidues p length,
      ∑ b ∈ intervalResidues p length,
        ∑ x : ZMod p, χ ((x + a) / (x + b))) =
      (length : ℂ) * ((p : ℂ) - length) := by
  simpa [intervalResidues_card p length hlength] using
    sum_character_ratio_quadratic_moment p χ hχ (intervalResidues p length)

/-- Exact quadratic moment for the actual consecutive character sums. -/
theorem sum_character_interval_quadratic_moment (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1)
    (length : ℕ) (hlength : length ≤ p) :
    (∑ x : ZMod p,
      (∑ a ∈ intervalResidues p length, χ (x + a)) *
        (∑ b ∈ intervalResidues p length, (χ (x + b))⁻¹)) =
      (length : ℂ) * ((p : ℂ) - length) := by
  simpa [intervalResidues_card p length hlength] using
    sum_character_shift_sums_mul_inverse p χ hχ (intervalResidues p length)

end SptClassification
