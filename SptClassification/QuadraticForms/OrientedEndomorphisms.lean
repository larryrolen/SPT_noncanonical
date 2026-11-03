/- Assembled by AxiomProver. -/

module

public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

/-!
# Oriented CM actions in the integral endomorphism ring

The noncommutation argument of [rolenManuscript, Lemma `lem:separation`]
uses only absence of zero divisors in the integral endomorphism ring. It
does not require constructing its rational division algebra. These lemmas
apply to a ring preserving the cyclic subgroup once its restriction map
and the two specialized CM generators have been constructed.
-/

public section

namespace SptClassification

/-- Two commuting roots of the same trace-one quadratic are equal or
complementary in any ring without zero divisors. -/
theorem commuting_quadratic_eq_or_eq_one_sub
    {O : Type*} [Ring O] [NoZeroDivisors O]
    (a b c : O) (ha : a * a - a + c = 0) (hb : b * b - b + c = 0)
    (hcomm : a * b = b * a) : b = a ∨ b = 1 - a := by
  have hprod : (a - b) * (a + b - 1) = 0 := by
    calc
      (a - b) * (a + b - 1) = (a * a - a + c) - (b * b - b + c) := by
        noncomm_ring [hcomm]
      _ = 0 := by rw [ha, hb, sub_self]
  rcases mul_eq_zero.mp hprod with h | h
  · exact Or.inl (sub_eq_zero.mp h).symm
  · right
    have hs : a + b = 1 := sub_eq_zero.mp h
    calc
      b = a + b - a := by abel
      _ = 1 - a := by rw [hs]

/-- The two oriented scalar sets rule out commuting CM generators directly
in the integral preserving ring. No ordinary/supersingular dichotomy or
rational endomorphism algebra is needed for this deduction. -/
theorem oriented_endomorphisms_not_commute
    {O : Type*} [Ring O] [NoZeroDivisors O]
    (restriction : O →+* ZMod 6) (a b c : O)
    (ha : a * a - a + c = 0) (hb : b * b - b + c = 0)
    (hares : restriction a = 0 ∨ restriction a = 1)
    (hbres : restriction b = 3 ∨ restriction b = 4) : a * b ≠ b * a := by
  intro hcomm
  have hdisjoint : restriction b ≠ restriction a ∧
      restriction b ≠ 1 - restriction a := by
    rcases hares with hares | hares <;> rcases hbres with hbres | hbres <;>
      simp [hares, hbres] <;> decide
  rcases commuting_quadratic_eq_or_eq_one_sub a b c ha hb hcomm with h | h
  · exact hdisjoint.1 (congrArg restriction h)
  · exact hdisjoint.2 (by simpa only [map_sub, map_one] using congrArg restriction h)

/-- The manuscript bound follows directly in the integral preserving ring
from ordinary commutativity and the supersingular degree estimate
of [rolen2026canonical, Lemma 5.2]. The geometric hypotheses are separate
parameters: this theorem does not construct a reduced elliptic pair. -/
theorem oriented_endomorphisms_force_prime_bound
    {O : Type*} [Ring O] [NoZeroDivisors O]
    (restriction : O →+* ZMod 6) (d p n : ℕ) (a b : O)
    (hn : 4 * n = d + 1)
    (ha : a * a - a + (n : O) = 0) (hb : b * b - b + (n : O) = 0)
    (hares : restriction a = 0 ∨ restriction a = 1)
    (hbres : restriction b = 3 ∨ restriction b = 4)
    (ordinary : Prop) (hordinary : ordinary → a * b = b * a)
    (hsupersingular : ¬ordinary → a * b ≠ b * a → 6 * p ≤ 4 * n * n) :
    24 * p ≤ (d + 1) ^ 2 := by
  have hnoncomm := oriented_endomorphisms_not_commute restriction a b (n : O)
    ha hb hares hbres
  have hnotOrd : ¬ordinary := fun h => hnoncomm (hordinary h)
  have hdegree := hsupersingular hnotOrd hnoncomm
  calc
    24 * p = 4 * (6 * p) := by ring
    _ ≤ 4 * (4 * n * n) := Nat.mul_le_mul_left 4 hdegree
    _ = (d + 1) ^ 2 := by rw [← hn]; ring

end SptClassification
