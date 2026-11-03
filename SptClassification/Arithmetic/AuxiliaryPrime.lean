/- Assembled by AxiomProver. -/

module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

/-!
# An auxiliary prime with prescribed negative character

For `N > 0`, the integer `1-24N` is a nonsquare modulo some prime avoiding
any specified positive modulus. Jacobi reciprocity supplies a prime factor of
`24 * (24 * N - 1) * l - 1`, so no prime-distribution theorem is needed.
-/

public section

namespace SptClassification

/-- Reciprocity evaluates a negative numerator at a suitable composite denominator. -/
theorem jacobi_neg_eq_neg_one {d r : ℕ} (hd : d % 4 = 3) (hr : r % 4 = 3)
    (hres : (r : ℤ) % d = (-1 : ℤ) % d) : jacobiSym (-(d : ℤ)) r = -1 := by
  have hdodd : Odd d := Nat.odd_iff.mpr (by omega)
  have hrodd : Odd r := Nat.odd_iff.mpr (by omega)
  have hχd : ZMod.χ₄ (d : ZMod 4) = -1 := by
    rw [ZMod.χ₄_nat_mod_four, hd]
    decide
  have hχr : ZMod.χ₄ (r : ZMod 4) = -1 := by
    rw [ZMod.χ₄_nat_mod_four, hr]
    decide
  have hj : jacobiSym (r : ℤ) d = -1 := by
    rw [jacobiSym.mod_left' hres, jacobiSym.at_neg_one hdodd, hχd]
  rw [jacobiSym.neg _ hrodd, hχr,
    jacobiSym.quadratic_reciprocity_three_mod_four hd hr, hj]
  norm_num

/-- The negative discriminant `1-24N` has a nonresidue prime avoiding `6*l`. -/
theorem exists_auxiliary_prime {l N : ℕ} (hl : 0 < l) (hN : 0 < N) :
    ∃ Q : ℕ, ∃ hQ : Q.Prime,
      ¬Q ∣ 6 * l ∧ @legendreSym Q ⟨hQ⟩ (1 - 24 * (N : ℤ)) = -1 := by
  let d := 24 * N - 1
  have hdpos : 0 < d := by dsimp [d]; omega
  have hdadd : d + 1 = 24 * N := by dsimp [d]; omega
  have hd4 : d % 4 = 3 := by omega
  let r := 24 * d * l - 1
  have hprod : 1 ≤ 24 * d * l := by nlinarith
  have hradd : r + 1 = 24 * d * l := Nat.sub_add_cancel hprod
  have hr4 : r % 4 = 3 := by
    have heq : 24 * d * l = 4 * (6 * d * l) := by ring
    omega
  have hrcast : (r : ℤ) = 24 * (d : ℤ) * (l : ℤ) - 1 := by
    have h := congrArg (fun n : ℕ => (n : ℤ)) hradd
    push_cast at h
    omega
  have hres : (r : ℤ) % d = (-1 : ℤ) % d := by
    rw [hrcast]
    rw [show 24 * (d : ℤ) * (l : ℤ) - 1 = -1 + (d : ℤ) * (24 * l) by ring]
    simp [Int.add_emod]
  obtain ⟨Q, hQ, hQr, hsym⟩ := jacobiSym.eq_neg_one_at_prime_divisor_of_eq_neg_one
    (jacobi_neg_eq_neg_one hd4 hr4 hres)
  refine ⟨Q, hQ, ?_, ?_⟩
  · intro hQsix
    have hQprod : Q ∣ 24 * d * l := by
      have heq : 24 * d * l = (6 * l) * (4 * d) := by ring
      rw [heq]
      exact dvd_mul_of_dvd_left hQsix _
    obtain ⟨k, hk⟩ := hQr
    obtain ⟨j, hj⟩ := hQprod
    have hlt : k < j := by nlinarith [hQ.pos]
    have hbound : Q * (k + 1) ≤ Q * j := Nat.mul_le_mul_left Q hlt
    nlinarith [hQ.two_le]
  · let : Fact Q.Prime := ⟨hQ⟩
    rw [jacobiSym.legendreSym.to_jacobiSym]
    have hdc : -(d : ℤ) = 1 - 24 * (N : ℤ) := by
      have h := congrArg (fun n : ℕ => (n : ℤ)) hdadd
      push_cast at h
      omega
    simpa only [hdc] using hsym

end SptClassification
