/- Assembled by AxiomProver. -/

module

public import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Ring

/-!
# Packed periodic bit patterns

A natural number represents a finite set of bit positions. Repeating a bounded
pattern has a fast geometric-quotient expression; the proof compares it with
successive block concatenation. Window extraction then gives a periodic mask on
an arbitrary interval of natural numbers.
-/

namespace SptClassification.Sieve

private def repeatedReference (width pattern : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 ^ width * repeatedReference width pattern n + pattern

private theorem repeatedReference_telescope (width pattern n : ℕ) :
    repeatedReference width pattern n * 2 ^ width + pattern =
      repeatedReference width pattern n + pattern * (2 ^ width) ^ n := by
  induction n with
  | zero => simp [repeatedReference]
  | succ n ih =>
    simpa only [repeatedReference, Nat.pow_succ, mul_add, add_mul, mul_assoc,
      mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm] using
      congrArg (fun x : ℕ => 2 ^ width * x + pattern) ih

private theorem repeatedReference_bits (width pattern n : ℕ) (hp : pattern < 2 ^ width) :
    ∀ i : ℕ, (repeatedReference width pattern n).testBit i =
      if i < width * n then pattern.testBit (i % width) else false := by
  induction n with
  | zero => simp [repeatedReference]
  | succ n ih =>
    intro i
    rw [repeatedReference, Nat.testBit_two_pow_mul_add _ hp]
    by_cases hi : i < width
    · have hbound : i < width * (n + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
        omega
      simp only [ite_eq_left hi, ite_eq_left hbound, Nat.mod_eq_of_lt hi]
    · have hle : width ≤ i := by omega
      have hmod : (i - width) % width = i % width := by
        calc
          (i - width) % width = ((i - width) + width) % width := by simp
          _ = i % width := by rw [Nat.sub_add_cancel hle]
      have hbound : i - width < width * n ↔ i < width * (n + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
        omega
      rw [ite_eq_right hi, ih]
      simp only [hbound, hmod]

public section

/-- Repeat the low `width` bits of a pattern using a geometric quotient. -/
@[expose] def repeatBits (width pattern count : ℕ) : ℕ :=
  (pattern % (1 <<< width)) * ((1 <<< (width * count)) - 1) / ((1 <<< width) - 1)

private theorem repeatBits_eq_reference {width : ℕ} (hw : 0 < width) (pattern count : ℕ) :
    repeatBits width pattern count =
      repeatedReference width (pattern % 2 ^ width) count := by
  let P := pattern % 2 ^ width
  have ht := repeatedReference_telescope width P count
  have hm : repeatedReference width P count * (2 ^ width - 1) =
      P * ((2 ^ width) ^ count - 1) := by
    simp only [Nat.mul_sub_left_distrib, mul_one]
    omega
  have hd : 0 < 2 ^ width - 1 := Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))
  simp only [repeatBits, Nat.shiftLeft_eq, one_mul, pow_mul]
  change P * ((2 ^ width) ^ count - 1) / (2 ^ width - 1) = _
  rw [← hm]
  exact Nat.mul_div_cancel _ hd

/-- The packed repetition has exactly the intended periodic bits and no others. -/
theorem testBit_repeatBits (width pattern count i : ℕ) :
    (repeatBits width pattern count).testBit i =
      if i < width * count then pattern.testBit (i % width) else false := by
  by_cases hw : width = 0
  · subst width
    simp [repeatBits]
  · have hpos : 0 < width := by omega
    rw [repeatBits_eq_reference hpos,
      repeatedReference_bits _ _ _ (Nat.mod_lt _ (Nat.two_pow_pos _))]
    simp only [Nat.testBit_mod_two_pow, Nat.mod_lt i hpos, decide_true, Bool.true_and]

/-- The bits of a periodic pattern on the interval `[start,start+length)`. -/
@[expose] def periodicMask (period pattern length start : ℕ) : ℕ :=
  (repeatBits period pattern (length / period + 2) >>> (start % period)) % (1 <<< length)

/-- Window extraction preserves the periodic residue at every position in the window. -/
theorem testBit_periodicMask {period : ℕ} (hp : 0 < period) (pattern length start i : ℕ) :
    (periodicMask period pattern length start).testBit i =
      if i < length then pattern.testBit ((start + i) % period) else false := by
  simp only [periodicMask, Nat.shiftLeft_eq, one_mul, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftRight, testBit_repeatBits]
  by_cases hi : i < length
  · have hstart := Nat.mod_lt start hp
    have hlength := Nat.mod_lt length hp
    have hdiv := Nat.mod_add_div length period
    have hbound : start % period + i < period * (length / period + 2) := by
      rw [Nat.mul_add]
      omega
    have hmod : (start % period + i) % period = (start + i) % period := by
      simp [Nat.add_mod]
    simp only [hi, decide_true, Bool.true_and, ite_eq_left hbound, hmod, ite_eq_left]
  · simp [hi]

/-- A packed union of finite masks. -/
@[expose] def unionMasks (masks : List ℕ) : ℕ := masks.foldr (· ||| ·) 0

theorem testBit_unionMasks (masks : List ℕ) (i : ℕ) :
    (unionMasks masks).testBit i = true ↔ ∃ m ∈ masks, m.testBit i = true := by
  induction masks with
  | nil => simp [unionMasks]
  | cons m masks ih => simp [unionMasks, Nat.testBit_or, ← ih]

/-- Pack the image of a finite list as a set of bit positions. -/
@[expose] def imageMask {α : Type*} (items : List α) (f : α → ℕ) : ℕ :=
  unionMasks (items.map fun a => 1 <<< f a)

theorem testBit_imageMask {α : Type*} (items : List α) (f : α → ℕ) (i : ℕ) :
    (imageMask items f).testBit i = true ↔ ∃ a ∈ items, f a = i := by
  simp [imageMask, testBit_unionMasks, Nat.shiftLeft_eq, Nat.testBit_two_pow]

/-- Intersect masks inside a fixed finite window. -/
def intersectionMasks (length : ℕ) (masks : List ℕ) : ℕ :=
  masks.foldr (· &&& ·) ((1 <<< length) - 1)

theorem testBit_intersectionMasks (length : ℕ) (masks : List ℕ) (i : ℕ) :
    (intersectionMasks length masks).testBit i = true ↔
      i < length ∧ ∀ m ∈ masks, m.testBit i = true := by
  induction masks with
  | nil => simp [intersectionMasks, Nat.shiftLeft_eq]
  | cons m masks ih =>
    simp only [intersectionMasks, List.foldr_cons, Nat.testBit_and, Bool.and_eq_true]
    rw [show (masks.foldr (· &&& ·) ((1 <<< length) - 1)).testBit i = true ↔
        i < length ∧ ∀ m ∈ masks, m.testBit i = true from ih]
    simp [and_left_comm]

/-- A checked bitwise inclusion transfers membership to the containing mask. -/
theorem testBit_of_intersection_eq {a b i : ℕ} (h : a &&& b = a) (hi : a.testBit i = true) :
    b.testBit i = true := by
  have hb := congrArg (fun n : ℕ => n.testBit i) h
  simpa only [Nat.testBit_and, hi, Bool.true_and] using hb

end

end SptClassification.Sieve
