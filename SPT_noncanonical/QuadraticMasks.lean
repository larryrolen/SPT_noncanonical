/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.PeriodicBits
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic.NormNum

/-!
# Packed quadratic-character classes

The square-residue mask is the image of all residues under squaring. Removing
zero gives the positive Legendre class, and complementing inside the residue
interval gives the negative class. Periodic window extraction therefore encodes
the exact Jacobi character values at each integer in a block.
-/

public section

namespace SptClassification.Sieve

/-- The set of square residues modulo `q`, including zero. -/
@[expose] def squareResidueMask (q : ℕ) : ℕ :=
  imageMask (List.range q) (fun a => a * a % q)

/-- The packed square residues are exactly the squares in the residue field. -/
theorem testBit_squareResidueMask (q : ℕ) [Fact q.Prime] {r : ℕ} (hr : r < q) :
    (squareResidueMask q).testBit r = true ↔ IsSquare (r : ZMod q) := by
  rw [squareResidueMask, testBit_imageMask]
  simp only [List.mem_range]
  constructor
  · rintro ⟨a, ha, hmod⟩
    have hcast : ((a * a : ℕ) : ZMod q) = (r : ZMod q) := by
      rw [ZMod.natCast_eq_natCast_iff]
      show (a * a) % q = r % q
      simpa only [Nat.mod_eq_of_lt hr] using hmod
    exact ⟨(a : ZMod q), by simpa only [Nat.cast_mul] using hcast.symm⟩
  · rintro ⟨a, ha⟩
    refine ⟨a.val, ZMod.val_lt a, ?_⟩
    have hcast : ((a.val * a.val : ℕ) : ZMod q) = (r : ZMod q) := by
      simpa only [Nat.cast_mul, ZMod.natCast_zmod_val] using ha.symm
    rw [ZMod.natCast_eq_natCast_iff] at hcast
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt hr] using hcast

/-- One period of a nonzero quadratic-character class; `true` selects the negative sign. -/
@[expose] def characterPattern (q : ℕ) (negative : Bool) : ℕ :=
  if negative then ((1 <<< q) - 1) ^^^ squareResidueMask q
  else squareResidueMask q &&& ((1 <<< q) - 2)

/-- The mask bits equal the prescribed nonzero Legendre class. -/
theorem testBit_characterPattern (q : ℕ) [Fact q.Prime] (negative : Bool)
    {r : ℕ} (hr : r < q) :
    (characterPattern q negative).testBit r = true ↔
      legendreSym q (r : ℤ) = if negative then -1 else 1 := by
  have hqpos : 0 < q := (Fact.out : q.Prime).pos
  have hpow : 1 < 2 ^ q := Nat.one_lt_two_pow (by omega)
  cases negative with
  | false =>
    change (squareResidueMask q &&& ((1 <<< q) - 2)).testBit r = true ↔
      legendreSym q (r : ℤ) = 1
    by_cases hr0 : r = 0
    · subst r
      have hz : (2 ^ q - 2).testBit 0 = false := by
        simpa using Nat.testBit_two_pow_sub_succ (n := q) (x := 1) hpow 0
      rw [Nat.testBit_and, Nat.shiftLeft_eq, one_mul, hz]
      simp
    · have hbit : (1 : ℕ).testBit r = false := by
        simpa only [Nat.pow_zero] using Nat.testBit_two_pow_of_ne (Ne.symm hr0)
      have hmask : ((1 <<< q) - 2).testBit r = true := by
        simpa [Nat.shiftLeft_eq, hr, hbit] using
          Nat.testBit_two_pow_sub_succ (n := q) (x := 1) hpow r
      have hcast : (r : ZMod q) ≠ 0 := by
        intro hz
        exact Nat.not_dvd_of_pos_of_lt (by omega) hr ((ZMod.natCast_eq_zero_iff r q).mp hz)
      rw [Nat.testBit_and, hmask, Bool.and_true, legendreSym.eq_one_iff' q hcast]
      exact testBit_squareResidueMask q hr
  | true =>
    change (((1 <<< q) - 1) ^^^ squareResidueMask q).testBit r = true ↔
      legendreSym q (r : ℤ) = -1
    rw [Nat.testBit_xor, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow_sub_one,
      legendreSym.eq_neg_one_iff' q]
    have hsquare := testBit_squareResidueMask q hr
    cases hb : (squareResidueMask q).testBit r <;> simp_all

/-- Jacobi evaluation at a natural number is determined by its residue in the prime field. -/
theorem jacobi_eq_legendre_residue (q : ℕ) [Fact q.Prime] (x : ℕ) :
    jacobiSym (x : ℤ) q = legendreSym q ((x % q : ℕ) : ℤ) := by
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  have hcast : ((x : ℤ) : ZMod q) = (((x % q : ℕ) : ℤ) : ZMod q) := by
    simp only [Int.cast_natCast]
    rw [ZMod.natCast_eq_natCast_iff]
    simp [Nat.ModEq]
  simp only [legendreSym, hcast]

/-- A block of integers with the specified nonzero character value modulo `q`. -/
@[expose] def characterMask (q : ℕ) (negative : Bool) (length start : ℕ) : ℕ :=
  periodicMask q (characterPattern q negative) length start

theorem testBit_characterMask (q : ℕ) [Fact q.Prime] (negative : Bool)
    (length start : ℕ) {i : ℕ} (hi : i < length) :
    (characterMask q negative length start).testBit i = true ↔
      jacobiSym ((start + i : ℕ) : ℤ) q = if negative then -1 else 1 := by
  rw [characterMask, testBit_periodicMask (Fact.out : q.Prime).pos,
    ite_eq_left hi, testBit_characterPattern q negative (Nat.mod_lt _ (Fact.out : q.Prime).pos),
    ← jacobi_eq_legendre_residue]

end SptClassification.Sieve
