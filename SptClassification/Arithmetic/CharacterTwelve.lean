/- Assembled by AxiomProver. -/

module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
public import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-!
# The quadratic character of conductor twelve

The character is one at residues `1,11`, minus one at `5,7`, and zero elsewhere.
Its comparison with the Jacobi symbol fixes the normalization used in the eta
and lift coefficient formulas. We follow [ahlgrenAndersen2016], section 3.
-/

public section

namespace SptClassification

/-- The quadratic character on residue classes modulo twelve. -/
@[expose] def characterTwelveResidue (a : ZMod 12) : ℤ :=
  if a = 1 ∨ a = 11 then 1 else if a = 5 ∨ a = 7 then -1 else 0

/-- The integer-periodic quadratic character of conductor twelve. -/
def characterTwelve (a : ℤ) : ℤ := characterTwelveResidue a

theorem characterTwelve_eq_residue (a : ℤ) :
    characterTwelve a = characterTwelveResidue (a : ZMod 12) := (rfl)

theorem characterTwelveResidue_mul (a b : ZMod 12) :
    characterTwelveResidue (a * b) = characterTwelveResidue a * characterTwelveResidue b := by
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem characterTwelve_mul (a b : ℤ) :
    characterTwelve (a * b) = characterTwelve a * characterTwelve b := by
  simp only [characterTwelve, Int.cast_mul, characterTwelveResidue_mul]

@[simp] theorem characterTwelve_add_twelve (a : ℤ) :
    characterTwelve (a + 12) = characterTwelve a := by
  have h : (12 : ZMod 12) = 0 := by decide +kernel
  simp [characterTwelve, h]

@[simp] theorem characterTwelve_neg (a : ℤ) : characterTwelve (-a) = characterTwelve a := by
  have h (b : ZMod 12) : characterTwelveResidue (-b) = characterTwelveResidue b := by
    fin_cases b <;> decide +kernel
  simpa only [characterTwelve, Int.cast_neg] using h (a : ZMod 12)

@[simp] theorem characterTwelve_zero : characterTwelve 0 = 0 := by decide +kernel
@[simp] theorem characterTwelve_one : characterTwelve 1 = 1 := by decide +kernel
@[simp] theorem characterTwelve_two : characterTwelve 2 = 0 := by decide +kernel
@[simp] theorem characterTwelve_three : characterTwelve 3 = 0 := by decide +kernel
@[simp] theorem characterTwelve_five : characterTwelve 5 = -1 := by decide +kernel
@[simp] theorem characterTwelve_seven : characterTwelve 7 = -1 := by decide +kernel
@[simp] theorem characterTwelve_eleven : characterTwelve 11 = 1 := by decide +kernel

theorem characterTwelve_eq_zero_of_two_dvd {a : ℤ} (ha : 2 ∣ a) :
    characterTwelve a = 0 := by
  obtain ⟨b, rfl⟩ := ha
  simp [characterTwelve_mul]

theorem characterTwelve_eq_zero_of_three_dvd {a : ℤ} (ha : 3 ∣ a) :
    characterTwelve a = 0 := by
  obtain ⟨b, rfl⟩ := ha
  simp [characterTwelve_mul]

/-- The conductor-twelve character factors into the mod-four and mod-three characters. -/
theorem characterTwelve_eq_chiFour_mul_jacobi (m : ℕ) :
    characterTwelve (m : ℤ) = ZMod.χ₄ (m : ZMod 4) * jacobiSym (m : ℤ) 3 := by
  have hleft : characterTwelve (m : ℤ) = characterTwelve ((m % 12 : ℕ) : ℤ) := by
    simp only [characterTwelve, Int.cast_natCast]
    apply congrArg characterTwelveResidue
    rw [ZMod.natCast_eq_natCast_iff]
    simp [Nat.ModEq]
  have hfour : ZMod.χ₄ (m : ZMod 4) = ZMod.χ₄ ((m % 12 : ℕ) : ZMod 4) := by
    rw [ZMod.χ₄_nat_mod_four m, ZMod.χ₄_nat_mod_four (m % 12)]
    have hmod : m % 4 = (m % 12) % 4 := by omega
    rw [hmod]
  have hthree : jacobiSym (m : ℤ) 3 = jacobiSym ((m % 12 : ℕ) : ℤ) 3 :=
    jacobiSym.mod_left' (by omega)
  rw [hleft, hfour, hthree]
  have hbound : m % 12 < 12 := Nat.mod_lt _ (by decide)
  generalize m % 12 = r at hbound ⊢
  interval_cases r <;> norm_num [characterTwelve, characterTwelveResidue] <;> decide +kernel

/-- At odd positive denominators, the residue table equals the Jacobi symbol `(12/m)`. -/
theorem characterTwelve_eq_jacobi_of_odd {m : ℕ} (hm : Odd m) :
    characterTwelve (m : ℤ) = jacobiSym 12 m := by
  have hrec := jacobiSym.quadratic_reciprocity (show Odd 3 by decide) hm
  have hthree : jacobiSym 3 m = (-1) ^ (m / 2) * jacobiSym (m : ℤ) 3 := by
    simpa using hrec
  calc
    characterTwelve (m : ℤ) = ZMod.χ₄ (m : ZMod 4) * jacobiSym (m : ℤ) 3 :=
      characterTwelve_eq_chiFour_mul_jacobi m
    _ = jacobiSym 3 m := by
      rw [ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp hm)]
      exact hthree.symm
    _ = jacobiSym (4 * 3) m := by rw [jacobiSym.mul_left, jacobiSym.at_four hm, one_mul]
    _ = jacobiSym 12 m := by norm_num

/-- The Kronecker symbol with numerator twelve and a nonnegative denominator.
For an even denominator the factor at two is zero, including the denominator zero. -/
def kroneckerTwelve (m : ℕ) : ℤ := if Odd m then jacobiSym 12 m else 0

/-- The residue-table and Kronecker normalizations agree. -/
theorem characterTwelve_eq_kronecker (m : ℕ) :
    characterTwelve (m : ℤ) = kroneckerTwelve m := by
  unfold kroneckerTwelve
  split_ifs with hm
  · exact characterTwelve_eq_jacobi_of_odd hm
  · apply characterTwelve_eq_zero_of_two_dvd
    have heven : Even m := (Nat.even_or_odd m).resolve_right hm
    obtain ⟨k, hk⟩ := heven
    refine ⟨(k : ℤ), ?_⟩
    rw [hk]
    push_cast
    ring

end SptClassification
