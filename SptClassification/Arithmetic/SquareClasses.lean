/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.QuadraticTwist
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

/-!
# Square multipliers and simultaneous congruences

Equal nonzero Legendre symbols give a nonzero square multiplier in the residue
field. A Chinese remainder lift can prescribe this multiplier at one modulus
and the value one at a coprime auxiliary modulus.
-/

public section

namespace SptClassification

/-- Two nonzero indices with equal Legendre symbols differ by a nonzero square. -/
theorem exists_square_multiplier (p : ℕ) [Fact p.Prime] {x y : ℤ}
    (hx : (x : ZMod p) ≠ 0) (hy : (y : ZMod p) ≠ 0)
    (hxy : legendreSym p x = legendreSym p y) :
    ∃ a : ZMod p, a ≠ 0 ∧ a ^ 2 * (x : ZMod p) = (y : ZMod p) := by
  have hprod : legendreSym p (x * y) = 1 := by
    rw [legendreSym.mul, ← hxy, ← pow_two, legendreSym.sq_one p hx]
  have hnonzero : ((x * y : ℤ) : ZMod p) ≠ 0 := by
    simpa only [Int.cast_mul] using mul_ne_zero hx hy
  obtain ⟨z, hz⟩ := (legendreSym.eq_one_iff p hnonzero).mp hprod
  have hz' : (x : ZMod p) * (y : ZMod p) = z ^ 2 := by
    simpa only [Int.cast_mul, pow_two] using hz
  have heq : (z / (x : ZMod p)) ^ 2 * (x : ZMod p) = (y : ZMod p) := by
    field_simp
    linear_combination -hz'
  refine ⟨z / (x : ZMod p), ?_, heq⟩
  intro hzero
  rw [hzero, zero_pow (by decide), zero_mul] at heq
  exact hy heq.symm

/-- A natural representative can prescribe a residue and be one at a coprime modulus. -/
theorem exists_nat_lift_one {p M : ℕ} [NeZero p] (hcop : p.Coprime M) (x : ZMod p) :
    ∃ a : ℕ, (a : ZMod p) = x ∧ Nat.ModEq M a 1 := by
  let a := Nat.chineseRemainder hcop x.val 1
  refine ⟨a.val, ?_, a.property.2⟩
  calc
    (a.val : ZMod p) = (x.val : ZMod p) := by
      rw [ZMod.natCast_eq_natCast_iff]
      exact a.property.1
    _ = x := ZMod.natCast_zmod_val x

/-- The square multiplier can simultaneously be chosen to be one modulo `M`. -/
theorem exists_square_multiplier_lift (p : ℕ) [Fact p.Prime] {M : ℕ}
    (hcop : p.Coprime M) {x y : ℤ}
    (hx : (x : ZMod p) ≠ 0) (hy : (y : ZMod p) ≠ 0)
    (hxy : legendreSym p x = legendreSym p y) :
    ∃ a : ℕ, (a : ZMod p) ≠ 0 ∧
      (a : ZMod p) ^ 2 * (x : ZMod p) = (y : ZMod p) ∧ Nat.ModEq M a 1 := by
  obtain ⟨u, hu, hmul⟩ := exists_square_multiplier p hx hy hxy
  obtain ⟨a, ha, haM⟩ := exists_nat_lift_one hcop u
  exact ⟨a, by simpa only [ha] using hu, by simpa only [ha] using hmul, haM⟩

/-- The simultaneous lift is coprime to both moduli. -/
theorem exists_coprime_square_multiplier_lift (p : ℕ) [Fact p.Prime] {M : ℕ}
    (hcop : p.Coprime M) {x y : ℤ}
    (hx : (x : ZMod p) ≠ 0) (hy : (y : ZMod p) ≠ 0)
    (hxy : legendreSym p x = legendreSym p y) :
    ∃ a : ℕ, a.Coprime (p * M) ∧
      (a : ZMod p) ^ 2 * (x : ZMod p) = (y : ZMod p) ∧ Nat.ModEq M a 1 := by
  obtain ⟨a, ha, hmul, haM⟩ := exists_square_multiplier_lift p hcop hx hy hxy
  have hpa : a.Coprime p := (ZMod.isUnit_iff_coprime a p).mp (isUnit_iff_ne_zero.mpr ha)
  have haMcast : (a : ZMod M) = (1 : ℕ) := by
    rw [ZMod.natCast_eq_natCast_iff]
    exact haM
  have hMa : a.Coprime M := (ZMod.isUnit_iff_coprime a M).mp (by
    rw [haMcast]
    simpa only [Nat.cast_one] using (isUnit_one : IsUnit (1 : ZMod M)))
  exact ⟨a, hpa.mul_right hMa, hmul, haM⟩

/-- The square relation lifts from the prime modulus to the Fourier-index modulus. -/
theorem exists_square_index_transport (p : ℕ) [Fact p.Prime] {M : ℕ}
    (hcop : p.Coprime M) (hM : 24 ∣ M) {x y : ℤ}
    (hx : (x : ZMod p) ≠ 0) (hy : (y : ZMod p) ≠ 0)
    (hxy : legendreSym p x = legendreSym p y)
    (h24 : (x : ZMod 24) = (y : ZMod 24)) :
    ∃ a : ℕ, a.Coprime (p * M) ∧ Nat.ModEq M a 1 ∧
      (a : ZMod (24 * p)) ^ 2 * (x : ZMod (24 * p)) = (y : ZMod (24 * p)) := by
  obtain ⟨a, ha, hmul, haM⟩ := exists_coprime_square_multiplier_lift p hcop hx hy hxy
  have ha24 : (a : ZMod 24) = (1 : ℕ) := by
    rw [ZMod.natCast_eq_natCast_iff]
    exact Nat.ModEq.of_dvd hM haM
  have h24p : Nat.Coprime 24 p := (Nat.Coprime.of_dvd_right hM hcop).symm
  refine ⟨a, ha, haM, ?_⟩
  apply (ZMod.chineseRemainder h24p).injective
  simp only [map_mul, map_pow, map_natCast, map_intCast]
  apply Prod.ext
  · change (a : ZMod 24) ^ 2 * (x : ZMod 24) = (y : ZMod 24)
    rw [ha24, Nat.cast_one, one_pow, one_mul, h24]
  · exact hmul

/-- Primes at least five are coprime to the Fourier rescaling factor. -/
theorem prime_coprime_twentyFour {p : ℕ} (hp : p.Prime) (hfive : 5 ≤ p) :
    p.Coprime 24 := by
  apply hp.coprime_iff_not_dvd.mpr
  intro hdiv
  have hbound : p ≤ 24 := Nat.le_of_dvd (by decide) hdiv
  interval_cases p <;> norm_num at *

/-- The simultaneous square transport of the two smallest-parts Fourier indices. -/
theorem exists_progression_square_transport (p : ℕ) [Fact p.Prime]
    (hfive : 5 ≤ p) {Q b N : ℕ} (hQ : Q.Prime) (hQavoid : ¬Q ∣ 6 * p)
    (hzero : legendreSym p (1 - 24 * (b : ℤ)) ≠ 0)
    (hclass : legendreSym p (1 - 24 * (b : ℤ)) =
      legendreSym p (1 - 24 * (N : ℤ))) :
    ∃ a : ℕ, a.Coprime (6 * p * Q) ∧ Nat.ModEq (24 * Q) a 1 ∧
      24 * (N : ZMod (24 * p)) - 1 =
        (a : ZMod (24 * p)) ^ 2 * (24 * (b : ZMod (24 * p)) - 1) := by
  have hp : p.Prime := Fact.out
  have hpQ : p.Coprime Q := by
    apply hp.coprime_iff_not_dvd.mpr
    intro hdvd
    have heq : p = Q := (Nat.prime_dvd_prime_iff_eq hp hQ).mp hdvd
    subst Q
    exact hQavoid (dvd_mul_left p 6)
  have hcop : p.Coprime (24 * Q) := (prime_coprime_twentyFour hp hfive).mul_right hpQ
  have hx : ((1 - 24 * (b : ℤ) : ℤ) : ZMod p) ≠ 0 := by
    intro hz
    exact hzero ((legendreSym.eq_zero_iff p _).mpr hz)
  have hy : ((1 - 24 * (N : ℤ) : ℤ) : ZMod p) ≠ 0 := by
    intro hz
    apply hzero
    rw [hclass, (legendreSym.eq_zero_iff p _).mpr hz]
  have h24 : ((1 - 24 * (b : ℤ) : ℤ) : ZMod 24) =
      ((1 - 24 * (N : ℤ) : ℤ) : ZMod 24) := by
    have hz : (24 : ZMod 24) = 0 := by decide +kernel
    push_cast
    rw [hz]
    simp
  obtain ⟨a, ha, haM, hmul⟩ := exists_square_index_transport p hcop
    (dvd_mul_right 24 Q) hx hy hclass h24
  refine ⟨a, Nat.Coprime.of_dvd_right ?_ ha, haM, ?_⟩
  · exact ⟨4, by ring⟩
  · push_cast at hmul
    linear_combination hmul

end SptClassification
