/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.PeriodicBits
public import Mathlib.Data.Nat.Sqrt

/-!
# Packed squares in a finite interval

Square roots restrict the candidate list to a small interval. Each candidate is
guarded by its actual square bounds before being packed. Membership soundness
therefore follows directly from the packed image and integer arithmetic.
-/

public section

namespace SptClassification.Sieve

/-- A mask of the perfect squares in `[start,start+length)`. -/
@[expose] def squareMask (length start : ℕ) : ℕ :=
  let first := start.sqrt
  let last := (start + length).sqrt
  let candidates := (List.range (last + 1 - first)).map fun i => first + i
  imageMask
    (candidates.filter fun a => decide (start ≤ a * a ∧ a * a < start + length))
    (fun a => a * a - start)

/-- Every bit admitted by the square mask is an actual square after restoring its offset. -/
theorem squareMask_sound {length start i : ℕ} (h : (squareMask length start).testBit i = true) :
    IsSquare (start + i) := by
  unfold squareMask at h
  obtain ⟨a, ha, hindex⟩ := (testBit_imageMask _ _ i).mp h
  have hb : start ≤ a * a ∧ a * a < start + length :=
    of_decide_eq_true (List.mem_filter.mp ha).2
  exact ⟨a, by omega⟩

end SptClassification.Sieve
