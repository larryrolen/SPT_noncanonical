/- Assembled by AxiomProver. -/

module

public import Mathlib.RingTheory.PowerSeries.Basic
import Lean.Elab.Tactic.Omega

/-!
# Integral coefficients in triangular cusp expansions

A finite family with distinct initial exponents and leading coefficient one
detects its coefficient ring from its sum. This supplies coefficient descent
after a holomorphic level-six form has been expressed in the basis `t^i b^k`:
reverse the indices so that the initial exponents increase. The existence of
that global polynomial expression is a separate geometric input.
-/

public section

namespace SptClassification

open PowerSeries

/-- A triangular family with diagonal coefficients one detects membership in
a subring. No field or division assumption is needed. -/
theorem coefficients_mem_subring_of_triangular_qexp
    {K : Type*} [CommRing K] (R : Subring K) (N : ℕ)
    (B : ℕ → PowerSeries K) (c : ℕ → K)
    (hB : ∀ i ≤ N, ∀ j, coeff j (B i) ∈ R)
    (hlower : ∀ i ≤ N, ∀ j < i, coeff j (B i) = 0)
    (hdiag : ∀ i ≤ N, coeff i (B i) = 1)
    (hsum : ∀ j, coeff j (∑ i ∈ Finset.range (N + 1), C (c i) * B i) ∈ R) :
    ∀ i ≤ N, c i ∈ R := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have hcut :
        (∑ i ∈ Finset.range (N + 1), c i * coeff n (B i)) =
          ∑ i ∈ Finset.range (n + 1), c i * coeff n (B i) := by
      symm
      apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hn 1))
      intro i hi hni
      have hiN : i ≤ N := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
      have hni' : n < i := by simp only [Finset.mem_range] at hni; omega
      rw [hlower i hiN n hni', mul_zero]
    have hrow : (∑ i ∈ Finset.range n, c i * coeff n (B i)) + c n ∈ R := by
      have h := hsum n
      simp only [map_sum, coeff_C_mul] at h
      rw [hcut, Finset.sum_range_succ, hdiag n hn, mul_one] at h
      exact h
    have hprev : (∑ i ∈ Finset.range n, c i * coeff n (B i)) ∈ R := by
      apply R.sum_mem
      intro i hi
      have hin : i < n := Finset.mem_range.mp hi
      exact R.mul_mem (ih i hin (by omega)) (hB i (by omega) n)
    simpa only [add_sub_cancel_left] using R.sub_mem hrow hprev

/-- Shifted series with constant coefficient one give an integral triangular
basis. The map may be any ring homomorphism; the conclusion is membership in
its actual image, without choosing or assuming inverse coefficients. -/
theorem coefficients_mem_range_of_shifted_qexp
    {R K : Type*} [CommRing R] [CommRing K] (f : R →+* K)
    (N : ℕ) (U : ℕ → PowerSeries R) (c : ℕ → K)
    (hU : ∀ i ≤ N, constantCoeff (U i) = 1)
    (hsum : ∀ j, coeff j
      (∑ i ∈ Finset.range (N + 1),
        C (c i) * PowerSeries.map f (X ^ i * U i)) ∈ f.range) :
    ∀ i ≤ N, c i ∈ f.range := by
  apply coefficients_mem_subring_of_triangular_qexp f.range N
    (fun i => PowerSeries.map f (X ^ i * U i)) c
  · intro i _ j
    exact ⟨coeff j (X ^ i * U i), by rw [coeff_map]⟩
  · intro i _ j hji
    simp [coeff_X_pow_mul', Nat.not_le.mpr hji]
  · intro i hi
    simpa [coeff_X_pow_mul'] using congrArg f (hU i hi)
  · exact hsum

end SptClassification
