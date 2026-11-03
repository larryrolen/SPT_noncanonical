/- Assembled by AxiomProver. -/

module

public import Mathlib.RingTheory.Polynomial.Wronskian
public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.NormNum

/-!
# Wronskians of equal-degree monic polynomials

For two monic polynomials of degree `n`, cancellation of the leading terms
improves the usual Wronskian degree bound to `2 * n - 2`. Coprime polynomials
have nonzero Wronskian when the degree of one monic polynomial is nonzero in
the coefficient field.

## Implementation notes

Mathlib's convention is `wronskian A B = A * B' - A' * B`. The logarithmic
derivative of `A / B` therefore uses `wronskian B A`.
-/

public section

namespace SptClassification

open Polynomial

/-- Equal monic leading terms improve the usual Wronskian degree estimate. -/
theorem natDegree_wronskian_le {K : Type*} [Field K] {A B : K[X]}
    (hA : A.Monic) (hB : B.Monic) (hdegree : B.natDegree = A.natDegree)
    (hpos : 0 < A.natDegree) :
    (wronskian A B).natDegree ≤ 2 * A.natDegree - 2 := by
  by_cases hw : wronskian A B = 0
  · simp [hw]
  have hsub : (B - A).natDegree < A.natDegree :=
    Polynomial.IsMonicOfDegree.natDegree_sub_lt hpos.ne' ⟨hdegree, hB⟩ ⟨rfl, hA⟩
  have heq : wronskian A (B - A) = wronskian A B := by
    simp [sub_eq_add_neg, wronskian_add_right, wronskian_neg_right,
      wronskian_self_eq_zero]
  have hlt := Polynomial.natDegree_wronskian_lt_add (heq ▸ hw)
  rw [heq] at hlt
  omega

/-- A monic polynomial has nonzero derivative if its degree is nonzero in the field. -/
theorem derivative_ne_zero_of_monic_degree {K : Type*} [Field K] {A : K[X]}
    (hA : A.Monic) (hn : (A.natDegree : K) ≠ 0) : A.derivative ≠ 0 := by
  have hpos : 0 < A.natDegree := by
    by_contra h
    have hz : A.natDegree = 0 := by omega
    exact hn (by simp [hz])
  have hcoeff : A.derivative.coeff (A.natDegree - 1) = (A.natDegree : K) := by
    rw [coeff_derivative]
    have hindex : A.natDegree - 1 + 1 = A.natDegree := by omega
    rw [hindex, hA.coeff_natDegree, one_mul]
    simpa only [Nat.cast_add, Nat.cast_one] using
      congrArg (fun n : ℕ => (n : K)) hindex
  intro hz
  exact hn (by simpa [hz] using hcoeff.symm)

/-- Coprimality and a nonzero degree in the coefficient field force a nonzero Wronskian. -/
theorem wronskian_ne_zero_of_monic_degree {K : Type*} [Field K] {A B : K[X]}
    (hcop : IsCoprime A B) (hA : A.Monic) (hn : (A.natDegree : K) ≠ 0) :
    wronskian A B ≠ 0 := by
  intro hw
  exact derivative_ne_zero_of_monic_degree hA hn
    ((hcop.wronskian_eq_zero_iff.mp hw).1)

/-- In prime characteristic, a positive degree below the prime cannot vanish. -/
theorem wronskian_ne_zero_of_degree_lt (p : ℕ) [Fact p.Prime]
    {A B : (ZMod p)[X]} (hcop : IsCoprime A B) (hA : A.Monic)
    (hpos : 0 < A.natDegree) (hlt : A.natDegree < p) :
    wronskian A B ≠ 0 := by
  refine wronskian_ne_zero_of_monic_degree (K := ZMod p) (A := A) (B := B) hcop hA ?_
  intro hzero
  have hdvd : p ∣ A.natDegree := (ZMod.natCast_eq_zero_iff _ _).mp hzero
  exact (Nat.not_dvd_of_pos_of_lt hpos hlt) hdvd

/-- The numerator of the logarithmic derivative has the equal-degree bound. -/
theorem natDegree_logarithmicNumerator_le {K : Type*} [Field K] {A B : K[X]}
    (hA : A.Monic) (hB : B.Monic) (hdegree : B.natDegree = A.natDegree)
    (hpos : 0 < A.natDegree) :
    (A.derivative * B - A * B.derivative).natDegree ≤ 2 * A.natDegree - 2 := by
  have heq : A.derivative * B - A * B.derivative = -(wronskian A B) := by
    simp [wronskian, neg_sub]
  rw [heq, Polynomial.natDegree_neg]
  exact natDegree_wronskian_le hA hB hdegree hpos

/-- The logarithmic derivative numerator is nonzero below the prime characteristic. -/
theorem logarithmicNumerator_ne_zero (p : ℕ) [Fact p.Prime]
    {A B : (ZMod p)[X]} (hcop : IsCoprime A B) (hA : A.Monic)
    (hpos : 0 < A.natDegree) (hlt : A.natDegree < p) :
    A.derivative * B - A * B.derivative ≠ 0 := by
  intro hzero
  apply wronskian_ne_zero_of_degree_lt p hcop hA hpos hlt
  exact sub_eq_zero.mpr (sub_eq_zero.mp hzero).symm

/-- The same nonvanishing holds over every field of the given characteristic. -/
theorem logarithmicNumerator_ne_zero_of_char {K : Type*} [Field K] (p : ℕ) [CharP K p]
    {A B : K[X]} (hcop : IsCoprime A B) (hA : A.Monic)
    (hpos : 0 < A.natDegree) (hlt : A.natDegree < p) :
    A.derivative * B - A * B.derivative ≠ 0 := by
  have hdegree : (A.natDegree : K) ≠ 0 := by
    intro hz
    exact (Nat.not_dvd_of_pos_of_lt hpos hlt) ((CharP.cast_eq_zero_iff K p _).mp hz)
  intro hzero
  apply wronskian_ne_zero_of_monic_degree hcop hA hdegree
  exact sub_eq_zero.mpr (sub_eq_zero.mp hzero).symm

/-- The logarithmic numerator degree bound, including the zero-polynomial convention. -/
theorem degree_logarithmicNumerator_le {K : Type*} [Field K] {A B : K[X]}
    (hA : A.Monic) (hB : B.Monic) (hdegree : B.natDegree = A.natDegree)
    (hpos : 0 < A.natDegree) :
    (A.derivative * B - A * B.derivative).degree ≤ (2 * A.natDegree - 2 : ℕ) :=
  Polynomial.degree_le_of_natDegree_le (natDegree_logarithmicNumerator_le hA hB hdegree hpos)

/-- A finite set of distinct zeros of the logarithmic numerator satisfies the degree bound. -/
theorem logarithmicNumerator_roots_card_le {K : Type*} [Field K] (p : ℕ) [CharP K p]
    {A B : K[X]} (hcop : IsCoprime A B) (hA : A.Monic) (hB : B.Monic)
    (hdegree : B.natDegree = A.natDegree) (hpos : 0 < A.natDegree)
    (hlt : A.natDegree < p) (s : Finset K)
    (hs : ∀ x ∈ s, (A.derivative * B - A * B.derivative).IsRoot x) :
    s.card ≤ 2 * A.natDegree - 2 := by
  classical
  have hne := logarithmicNumerator_ne_zero_of_char p hcop hA hpos hlt
  calc
    s.card ≤ (A.derivative * B - A * B.derivative).roots.toFinset.card := by
      apply Finset.card_le_card
      intro x hx
      exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hne).mpr (hs x hx))
    _ ≤ (A.derivative * B - A * B.derivative).roots.card := Multiset.toFinset_card_le _
    _ ≤ (A.derivative * B - A * B.derivative).natDegree := Polynomial.card_roots' _
    _ ≤ 2 * A.natDegree - 2 := natDegree_logarithmicNumerator_le hA hB hdegree hpos

end SptClassification
