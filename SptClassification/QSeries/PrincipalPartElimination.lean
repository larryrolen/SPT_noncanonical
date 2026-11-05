/- Assembled by AxiomProver. -/

module

public import Mathlib.Data.Finset.Range
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Linarith

/-!
# Integral elimination of principal parts

The rows arising from `η j^n` and `-η (Θ j) j^n` have integral coefficients,
leading coefficient one, and no pole above their leading pole. The elementary
row reduction below is the algebraic step in constructing the forms of
[rolenManuscript, §3]. Analytic modularity and the identification of these
rows with the eta and Klein functions are separate obligations.

An integer index `k` labels a possible pole. For the eta rows, `k` means the
term `q^(1/24-k)`; for the derivative rows it means `q^(1/24-(k+1))`.
Indices outside the nonnegative pole range retain the other Fourier terms.
-/

@[expose] public section

namespace SptClassification.QSeries

/-- Integral row reduction, retaining every Fourier coefficient of the rows. -/
noncomputable def principalPartElimination (raw : ℕ → ℤ → ℤ) (n : ℕ) : ℤ → ℤ :=
  Nat.strongRecOn n fun n ih r =>
    raw n r - Finset.sum (Finset.univ : Finset (Finset.range n))
      (fun k => raw n (k : ℤ) * ih k (Finset.mem_range.mp k.property) r)

theorem principalPartElimination_eq (raw : ℕ → ℤ → ℤ) (n : ℕ) (r : ℤ) :
    principalPartElimination raw n r =
      raw n r - Finset.sum (Finset.univ : Finset (Finset.range n))
        (fun k => raw n (k : ℤ) * principalPartElimination raw k r) := by
  unfold principalPartElimination
  rw [Nat.strongRecOn_eq]

/-- Every eliminated row has exactly its own pole among the indexed poles. -/
theorem principalPartElimination_pole (raw : ℕ → ℤ → ℤ)
    (leading : ∀ n, raw n (n : ℤ) = 1)
    (above : ∀ n k, n < k → raw n (k : ℤ) = 0)
    (n k : ℕ) :
    principalPartElimination raw n (k : ℤ) = if k = n then 1 else 0 := by
  induction n using Nat.strong_induction_on generalizing k with
  | h n ih =>
    rw [principalPartElimination_eq]
    by_cases hkn : k < n
    · let target : Finset.range n := ⟨k, Finset.mem_range.mpr hkn⟩
      have hsum :
          Finset.sum (Finset.univ : Finset (Finset.range n))
              (fun i => raw n (i : ℤ) * principalPartElimination raw i (k : ℤ)) =
            raw n (k : ℤ) := by
        classical
        calc
          _ = raw n (target : ℤ) * principalPartElimination raw target (k : ℤ) := by
            apply Finset.sum_eq_single target
            · intro i _ hne
              have hik : (i : ℕ) ≠ k := by
                intro h
                exact hne (Subtype.ext h)
              rw [ih i (Finset.mem_range.mp i.property) k]
              simp [hik.symm]
            · intro h
              exact False.elim (h (Finset.mem_univ target))
          _ = raw n (k : ℤ) := by simp [target, ih k hkn k]
      rw [hsum, sub_self]
      simp [show k ≠ n by omega]
    · have hno : ∀ i : Finset.range n,
          principalPartElimination raw i (k : ℤ) = 0 := by
        intro i
        have hi : (i : ℕ) < n := Finset.mem_range.mp i.property
        have hki : k ≠ (i : ℕ) := by omega
        simpa [hki] using ih i hi k
      have hsum :
          Finset.sum (Finset.univ : Finset (Finset.range n))
              (fun i => raw n (i : ℤ) * principalPartElimination raw i (k : ℤ)) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        rw [hno i, mul_zero]
      rw [hsum, sub_zero]
      by_cases h : k = n
      · subst k
        simpa using leading n
      · have hlt : n < k := by omega
        simp [above n k hlt, h]

/-- Elimination uses only integral linear combinations of the original rows. -/
theorem principalPartElimination_mem (raw : ℕ → ℤ → ℤ)
    (V : AddSubgroup (ℤ → ℤ)) (hraw : ∀ n, raw n ∈ V) (n : ℕ) :
    principalPartElimination raw n ∈ V := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hsum_apply (s : Finset (Finset.range n)) (r : ℤ) :
        (Finset.sum s
          (fun i => raw n (i : ℤ) • principalPartElimination raw i)) r =
        Finset.sum s
          (fun i => raw n (i : ℤ) * principalPartElimination raw i r) := by
      classical
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi hs => simp [hi, hs, Pi.add_apply, Pi.smul_apply]
    have hrow : principalPartElimination raw n =
        raw n - Finset.sum (Finset.univ : Finset (Finset.range n))
          (fun i => raw n (i : ℤ) • principalPartElimination raw i) := by
      funext r
      simpa only [Pi.sub_apply, hsum_apply] using principalPartElimination_eq raw n r
    rw [hrow]
    apply V.sub_mem (hraw n)
    have hsum_mem (s : Finset (Finset.range n)) :
        Finset.sum s (fun i => raw n (i : ℤ) • principalPartElimination raw i) ∈ V := by
      classical
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi hs =>
        rw [Finset.sum_insert hi]
        exact V.add_mem (V.zsmul_mem
          (ih i (Finset.mem_range.mp i.property)) (raw n (i : ℤ))) hs
    exact hsum_mem _

end SptClassification.QSeries
