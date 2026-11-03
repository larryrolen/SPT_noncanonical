/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.QuadraticMasks
public import SptClassification.Arithmetic.Sieve.SquareMasks
public import SptClassification.Arithmetic.ExceptionalPrimes
public import Mathlib.Data.Nat.GCD.Basic

/-!
# A sound packed checker for constant quadratic-character blocks

The checker intersects the two possible nonzero character patterns with the
units modulo six. The negative pattern must be empty; the positive pattern must
be contained in the guarded square mask. The generic soundness proof is separate
from the finite numerical certificates.
-/

public section

namespace SptClassification.Sieve

/-- A computational list representation of the exact discriminant-prime set. -/
@[expose] def sievePrimes : List ℕ :=
  [23,47,71,167,191,239,263,311,359,383,431,479,503,599,647,719,743,839,
   863,887,911,983,1031,1103,1151,1223,1319,1367,1439,1487,1511,1559,
   1583,1607,1823,1847,1871,2039,2063,2087]

theorem sievePrimes_toFinset : sievePrimes.toFinset = discriminantPrimes := by
  decide +kernel

/-- Intersect character masks, stopping as soon as the accumulated mask is empty. -/
@[expose] def filterPrimeMasks (negative : Bool) (length start : ℕ) : List ℕ → ℕ → ℕ
  | [], acc => acc
  | q :: qs, acc => if acc = 0 then 0 else
      filterPrimeMasks negative length start qs (acc &&& characterMask q negative length start)

/-- Every integer satisfying the tested characters survives the mask intersection. -/
theorem filterPrimeMasks_preserves_bit (negative : Bool) (length start : ℕ)
    (primes : List ℕ) (hprimes : ∀ q ∈ primes, q.Prime) {i : ℕ} (hi : i < length)
    (hchars : ∀ q ∈ primes, jacobiSym ((start + i : ℕ) : ℤ) q = if negative then -1 else 1)
    (acc : ℕ) (hacc : acc.testBit i = true) :
    (filterPrimeMasks negative length start primes acc).testBit i = true := by
  induction primes generalizing acc with
  | nil => exact hacc
  | cons q qs ih =>
    have ha : acc ≠ 0 := by
      intro hz
      simp only [hz, Nat.zero_testBit, Bool.false_eq_true] at hacc
    let : Fact q.Prime := ⟨hprimes q (by simp)⟩
    have hqbit : (characterMask q negative length start).testBit i = true :=
      (testBit_characterMask q negative length start hi).mpr (hchars q (by simp))
    rw [filterPrimeMasks, ite_eq_right ha]
    apply ih (fun r hr => hprimes r (by simp [hr])) (fun r hr => hchars r (by simp [hr]))
    simp only [Nat.testBit_and, hacc, hqbit, Bool.true_and]

/-- The residue mask with bits one and five recognizes the units modulo six. -/
theorem unit_six_bit {x : ℕ} (hx : x.Coprime 6) : (34 : ℕ).testBit (x % 6) = true := by
  have hmod : (x % 6).Coprime 6 := by
    have h := hx.symm
    change Nat.gcd 6 x = 1 at h
    rw [Nat.gcd_rec] at h
    exact h
  have htable : ∀ r : Fin 6, r.val.Coprime 6 → (34 : ℕ).testBit r.val = true := by
    decide +kernel
  exact htable ⟨x % 6, Nat.mod_lt _ (by decide)⟩ hmod

/-- The constant-character mask in a block, restricted to units modulo six. -/
@[expose] def classMask (negative : Bool) (length start : ℕ) : ℕ :=
  filterPrimeMasks negative length start sievePrimes (periodicMask 6 34 length start)

theorem classMask_preserves_character (negative : Bool) (length start : ℕ) {i : ℕ}
    (hi : i < length) (hcop : (start + i).Coprime 6)
    (hchars : ∀ q ∈ discriminantPrimes,
      jacobiSym ((start + i : ℕ) : ℤ) q = if negative then -1 else 1) :
    (classMask negative length start).testBit i = true := by
  have hmem : ∀ q ∈ sievePrimes, q ∈ discriminantPrimes := by
    intro q hq
    rw [← sievePrimes_toFinset]
    exact List.mem_toFinset.mpr hq
  apply filterPrimeMasks_preserves_bit negative length start sievePrimes
    (fun q hq => (mem_discriminantPrimes.mp (hmem q hq)).1) hi
    (fun q hq => hchars q (hmem q hq))
  rw [testBit_periodicMask (by decide : 0 < 6), ite_eq_left hi]
  exact unit_six_bit hcop

/-- Check both nonzero character patterns on one finite block. -/
@[expose] def checkBlock (length start : ℕ) : Bool :=
  let positive := classMask false length start
  let negative := classMask true length start
  (negative == 0) && ((positive &&& squareMask length start) == positive)

/-- A successful packed block check forces every qualifying integer to be a square. -/
theorem checkBlock_sound {length start i : ℕ} (hcheck : checkBlock length start = true)
    (hi : i < length) (hcop : (start + i).Coprime 6) {sign : ℤ}
    (hsign : sign = 1 ∨ sign = -1)
    (hchars : ∀ q ∈ discriminantPrimes, jacobiSym ((start + i : ℕ) : ℤ) q = sign) :
    IsSquare (start + i) := by
  simp only [checkBlock, Bool.and_eq_true, beq_iff_eq] at hcheck
  rcases hsign with rfl | rfl
  · have hbit := classMask_preserves_character false length start hi hcop hchars
    exact squareMask_sound (testBit_of_intersection_eq hcheck.2 hbit)
  · have hbit := classMask_preserves_character true length start hi hcop hchars
    rw [hcheck.1, Nat.zero_testBit] at hbit
    contradiction

/-- The portion of block `k` that is contained in the inclusive range up to `bound`. -/
def checkedBlockLength (width bound k : ℕ) : ℕ := min width (bound + 1 - width * k)

/-- A block wholly below the inclusive bound has its full width. -/
theorem checkedBlockLength_eq_width {width bound k : ℕ}
    (h : width * k + width ≤ bound + 1) :
    checkedBlockLength width bound k = width := by
  unfold checkedBlockLength
  exact Nat.min_eq_left (by omega)

/-- The clipped length is the minimum of the width and the remaining interval. -/
theorem checkedBlockLength_eq_min (width bound k : ℕ) :
    checkedBlockLength width bound k = min width (bound + 1 - width * k) := (rfl)

/-- Soundness of a complete bounded family of block certificates. -/
theorem character_sieve_of_blocks (width bound : ℕ) (hwidth : 0 < width)
    (hblocks : ∀ k : ℕ, k ≤ bound / width →
      checkBlock (checkedBlockLength width bound k) (width * k) = true)
    {x : ℕ} (hx : x ≤ bound) (hcop : x.Coprime (6 * ∏ q ∈ discriminantPrimes, q))
    (hconstant : ∀ q ∈ discriminantPrimes, ∀ r ∈ discriminantPrimes,
      jacobiSym (x : ℤ) q = jacobiSym (x : ℤ) r) : IsSquare x := by
  have hcop6 : x.Coprime 6 := Nat.Coprime.of_dvd_right (dvd_mul_right 6 _) hcop
  have h23 : 23 ∈ discriminantPrimes := by decide +kernel
  have hdiv23 : 23 ∣ ∏ q ∈ discriminantPrimes, q := Finset.dvd_prod_of_mem id h23
  have hcop23 : x.Coprime 23 := Nat.Coprime.of_dvd_right (dvd_mul_of_dvd_right hdiv23 6) hcop
  let : Fact (Nat.Prime 23) := ⟨(mem_discriminantPrimes.mp h23).1⟩
  have hx23 : (x : ZMod 23) ≠ 0 := ((ZMod.isUnit_iff_coprime x 23).mpr hcop23).ne_zero
  have hsign : jacobiSym (x : ℤ) 23 = 1 ∨ jacobiSym (x : ℤ) 23 = -1 := by
    simpa only [jacobiSym.legendreSym.to_jacobiSym] using
      legendreSym.eq_one_or_neg_one 23 (a := (x : ℤ)) (by simpa only [Int.cast_natCast] using hx23)
  have hk : x / width ≤ bound / width := Nat.div_le_div_right hx
  have hrep : width * (x / width) + x % width = x := by
    have h := Nat.mod_add_div x width
    omega
  have hi : x % width < checkedBlockLength width bound (x / width) := by
    have hm := Nat.mod_lt x hwidth
    unfold checkedBlockLength
    omega
  have hchars : ∀ q ∈ discriminantPrimes,
      jacobiSym (((width * (x / width) + x % width) : ℕ) : ℤ) q = jacobiSym (x : ℤ) 23 := by
    intro q hq
    rw [hrep]
    exact hconstant q hq 23 h23
  have hsquare := checkBlock_sound (hblocks (x / width) hk) hi
    (by simpa only [hrep] using hcop6) hsign hchars
  simpa only [hrep] using hsquare

end SptClassification.Sieve
