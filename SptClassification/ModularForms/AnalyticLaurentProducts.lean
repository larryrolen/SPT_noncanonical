/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.HeckeProductPairings
public import SptClassification.ModularForms.FourierRowUniqueness

/-!
# Products of convergent rational Laurent rows

Clearing the poles turns bounded-below Laurent rows into power-series rows.
The Cauchy product can then be evaluated analytically and shifted back. This
is the convergence step needed for the normalized approximation in
[rolenManuscript, §2, (2.5)].
-/

public section

namespace SptClassification

open UpperHalfPlane

/-- Restore a Laurent Fourier row from its convergent pole-cleared row. -/
theorem laurentRow_hasSum_of_poleCleared (c : ℤ → ℂ) (M : ℕ)
    (hbelow : ∀ r : ℤ, r < -(M : ℤ) → c r = 0)
    (q F : ℂ) (hq : q ≠ 0)
    (hs : HasSum (fun n : ℕ => c ((n : ℤ) - M) * q ^ n) (q ^ M * F)) :
    HasSum (fun r : ℤ => c r * q ^ r) F := by
  let shift : ℕ → ℤ := fun n => (n : ℤ) - M
  have hinj : Function.Injective shift := by
    intro n k h
    dsimp [shift] at h
    omega
  have hout (r : ℤ) (hr : r ∉ Set.range shift) : c r * q ^ r = 0 := by
    have hrlt : r < -(M : ℤ) := by
      by_contra h
      let n : ℕ := (r + M).toNat
      have hn : (n : ℤ) = r + M := Int.toNat_of_nonneg (by omega)
      apply hr
      exact ⟨n, by dsimp [shift]; omega⟩
    simp [hbelow r hrlt]
  apply (hinj.hasSum_iff hout).mp
  have hmul := hs.mul_left (q ^ (-(M : ℤ)))
  convert hmul using 1
  · ext n
    dsimp [shift]
    have hpow : q ^ ((n : ℤ) - M) = q ^ (-(M : ℤ)) * q ^ n := by
      rw [← zpow_natCast q n, ← zpow_add₀ hq]
      congr 1
      omega
    rw [hpow]
    ring
  · symm
    calc
      q ^ (-(M : ℤ)) * (q ^ M * F) =
          (q ^ (-(M : ℤ)) * q ^ M) * F := by ring
      _ = F := by
        rw [← zpow_natCast q M, ← zpow_add₀ hq]
        simp

/-- Coefficients of a rational Laurent row after clearing a pole of order
`M`. The lower-bound hypothesis ensures no information is discarded. -/
noncomputable def poleClearedRationalRow (c : ℤ → ℚ) (M : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk (fun n => c ((n : ℤ) - M))

@[simp] theorem poleClearedRationalRow_coeff (c : ℤ → ℚ) (M n : ℕ) :
    (poleClearedRationalRow c M).coeff n = c ((n : ℤ) - M) := by
  simp [poleClearedRationalRow]

/-- The Laurent coefficient row obtained by Cauchy multiplication after
clearing the two poles. Its normalization uses the sum of pole orders. -/
noncomputable def rationalLaurentProductRow
    (a b : ℤ → ℚ) (M N : ℕ) (r : ℤ) : ℚ :=
  if r < -((M + N : ℕ) : ℤ) then 0 else
    ((poleClearedRationalRow a M * poleClearedRationalRow b N).coeff
      (r + (M + N : ℕ)).toNat)

/-- The pole-cleared coefficient description, including the zero range. -/
theorem rationalLaurentProductRow_eq (a b : ℤ → ℚ) (M N : ℕ) (r : ℤ) :
    rationalLaurentProductRow a b M N r =
      if r < -((M + N : ℕ) : ℤ) then 0 else
        (poleClearedRationalRow a M * poleClearedRationalRow b N).coeff
          (r + (M + N : ℕ)).toNat := by
  rfl

theorem rationalLaurentProductRow_zero_below (a b : ℤ → ℚ) (M N : ℕ)
    (r : ℤ) (hr : r < -((M + N : ℕ) : ℤ)) :
    rationalLaurentProductRow a b M N r = 0 := by
  simp only [rationalLaurentProductRow, if_pos hr]

/-- Finite Cauchy formula for a rational Laurent product coefficient. -/
theorem rationalLaurentProductRow_eq_sum (a b : ℤ → ℚ) (M N : ℕ)
    (r : ℤ) (hr : ¬r < -((M + N : ℕ) : ℤ)) :
    rationalLaurentProductRow a b M N r =
      ∑ ij ∈ Finset.antidiagonal ((r + (M + N : ℕ)).toNat),
        a ((ij.1 : ℤ) - M) * b ((ij.2 : ℤ) - N) := by
  simp only [rationalLaurentProductRow, if_neg hr, PowerSeries.coeff_mul,
    poleClearedRationalRow_coeff]

/-- Absolutely convergent rational Laurent rows multiply to the Cauchy
Laurent row. This uses no modularity or coefficient congruence. -/
theorem rationalLaurentProductRow_hasSum
    (a b : ℤ → ℚ) (M N : ℕ)
    (haBelow : ∀ r : ℤ, r < -(M : ℤ) → a r = 0)
    (hbBelow : ∀ r : ℤ, r < -(N : ℤ) → b r = 0)
    (q A B : ℂ) (hq : q ≠ 0)
    (ha : HasSum (fun r : ℤ => (a r : ℂ) * q ^ r) A)
    (hb : HasSum (fun r : ℤ => (b r : ℂ) * q ^ r) B) :
    HasSum (fun r : ℤ =>
      (rationalLaurentProductRow a b M N r : ℂ) * q ^ r) (A * B) := by
  let C := poleClearedRationalRow a M * poleClearedRationalRow b N
  have ha' : HasSum (fun n : ℕ =>
      ((poleClearedRationalRow a M).coeff n : ℂ) * q ^ n) (q ^ M * A) := by
    simpa only [poleClearedRationalRow_coeff] using
      laurentRow_poleCleared_hasSum (fun r => (a r : ℂ)) M
        (by intro r hr; simp [haBelow r hr]) q A hq ha
  have hb' : HasSum (fun n : ℕ =>
      ((poleClearedRationalRow b N).coeff n : ℂ) * q ^ n) (q ^ N * B) := by
    simpa only [poleClearedRationalRow_coeff] using
      laurentRow_poleCleared_hasSum (fun r => (b r : ℂ)) N
        (by intro r hr; simp [hbBelow r hr]) q B hq hb
  have hp := rationalProduct_hasSum (poleClearedRationalRow a M)
    (poleClearedRationalRow b N) q (q ^ M * A) (q ^ N * B) ha' hb'
  have hprod : (q ^ M * A) * (q ^ N * B) = q ^ (M + N) * (A * B) := by
    rw [pow_add]
    ring
  rw [hprod] at hp
  apply laurentRow_hasSum_of_poleCleared
    (fun r => (rationalLaurentProductRow a b M N r : ℂ)) (M + N)
    (by intro r hr; simp [rationalLaurentProductRow_zero_below a b M N r hr])
    q (A * B) hq
  convert hp using 1
  ext n
  have hn : ¬ ((n : ℤ) - (M + N : ℕ) : ℤ) < -((M + N : ℕ) : ℤ) := by omega
  have hindex : (((n : ℤ) - (M + N : ℕ)) + (M + N : ℕ)).toNat = n := by
    have heq : ((n : ℤ) - (M + N : ℕ)) + (M + N : ℕ) = (n : ℤ) := by omega
    rw [heq, Int.toNat_natCast]
  simp only [rationalLaurentProductRow, if_neg hn, hindex]

/-- A power series regarded as a Laurent row with no negative coefficients. -/
noncomputable def nonnegativeRationalRow (A : PowerSeries ℚ) (r : ℤ) : ℚ :=
  if r < 0 then 0 else A.coeff r.toNat

theorem nonnegativeRationalRow_zero_below (A : PowerSeries ℚ)
    (r : ℤ) (hr : r < 0) : nonnegativeRationalRow A r = 0 := by
  simp [nonnegativeRationalRow, hr]

@[simp] theorem nonnegativeRationalRow_natCast (A : PowerSeries ℚ) (n : ℕ) :
    nonnegativeRationalRow A n = A.coeff n := by
  simp [nonnegativeRationalRow]

/-- An everywhere convergent rational power-series row also sums as a
Laurent row, with zero coefficients at negative indices. -/
theorem nonnegativeRationalRow_hasSum (A : PowerSeries ℚ)
    (q F : ℂ) (hq : q ≠ 0)
    (hs : HasSum (fun n : ℕ => (A.coeff n : ℂ) * q ^ n) F) :
    HasSum (fun r : ℤ => (nonnegativeRationalRow A r : ℂ) * q ^ r) F := by
  apply laurentRow_hasSum_of_poleCleared
    (fun r => (nonnegativeRationalRow A r : ℂ)) 0
    (by intro r hr; simp [nonnegativeRationalRow_zero_below A r (by omega)])
    q F hq
  simpa using hs

end SptClassification
