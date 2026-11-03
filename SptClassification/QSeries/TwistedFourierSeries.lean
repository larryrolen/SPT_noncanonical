/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.FourierCoefficients
public import SptClassification.QSeries.ProgressionLaurent
public import SptClassification.Arithmetic.QuadraticTwist

/-!
# Quadratically selected Fourier rows

The Laurent variable is `q^(1/24)` and its index is the integral exponent
`24n - 1`. These are the formal reductions of the selected smallest-parts,
inverse-eta, and theta-inverse-eta rows in [rolenManuscript, §2, (2.5)].
-/

public section

namespace SptClassification.QSeries

/-- The `-1` quadratic-character part of a bounded-below integral Fourier
row, reduced modulo `p`. -/
noncomputable def quadraticTwistedLaurent (p Q : ℕ) [Fact Q.Prime]
    (f : ℤ → ℤ) (B : ℤ) (hB : ∀ r < B, f r = 0) :
    LaurentSeries (ZMod p) :=
  HahnSeries.ofSuppBddBelow
    (fun r => if legendreSym Q (-r) = -1 then (f r : ZMod p) else 0)
    (by
      refine ⟨B, ?_⟩
      intro r hr
      have hnot : ¬r < B := by
        intro hlt
        simp only [Function.mem_support] at hr
        exact hr (by simp [hB r hlt])
      exact le_of_not_gt hnot)

@[simp] theorem quadraticTwistedLaurent_coeff (p Q : ℕ) [Fact Q.Prime]
    (f : ℤ → ℤ) (B : ℤ) (hB : ∀ r < B, f r = 0) (r : ℤ) :
    (quadraticTwistedLaurent p Q f B hB).coeff r =
      if legendreSym Q (-r) = -1 then (f r : ZMod p) else 0 := by
  rfl

/-- The selected smallest-parts series, with its true `24n - 1` support. -/
noncomputable def sptTwistedLaurent (p Q : ℕ) [Fact Q.Prime] :
    LaurentSeries (ZMod p) :=
  quadraticTwistedLaurent p Q sptFourier (-1)
    (fun _ hr => sptFourier_eq_zero_of_lt hr)

@[simp] theorem sptTwistedLaurent_coeff (p Q : ℕ) [Fact Q.Prime]
    (r : ℤ) :
    (sptTwistedLaurent p Q).coeff r =
      if legendreSym Q (-r) = -1 then (sptFourier r : ZMod p) else 0 := by
  exact quadraticTwistedLaurent_coeff p Q _ _ _ r

/-- The selected inverse-eta row `P_Q`. -/
noncomputable def partitionTwistedLaurent (p Q : ℕ) [Fact Q.Prime] :
    LaurentSeries (ZMod p) :=
  quadraticTwistedLaurent p Q partitionFourier (-1)
    (fun _ hr => partitionFourier_eq_zero_of_lt hr)

@[simp] theorem partitionTwistedLaurent_coeff (p Q : ℕ) [Fact Q.Prime]
    (r : ℤ) :
    (partitionTwistedLaurent p Q).coeff r =
      if legendreSym Q (-r) = -1 then (partitionFourier r : ZMod p) else 0 := by
  exact quadraticTwistedLaurent_coeff p Q _ _ _ r

/-- The selected theta-inverse-eta row, indexed by `24n - 1`. -/
noncomputable def thetaPartitionTwistedLaurent (p Q : ℕ) [Fact Q.Prime] :
    LaurentSeries (ZMod p) :=
  quadraticTwistedLaurent p Q (fun r => r * partitionFourier r) (-1)
    (fun _ hr => by simp [partitionFourier_eq_zero_of_lt hr])

@[simp] theorem thetaPartitionTwistedLaurent_coeff (p Q : ℕ) [Fact Q.Prime]
    (r : ℤ) :
    (thetaPartitionTwistedLaurent p Q).coeff r =
      (r : ZMod p) *
        (if legendreSym Q (-r) = -1 then (partitionFourier r : ZMod p) else 0) := by
  rw [thetaPartitionTwistedLaurent, quadraticTwistedLaurent_coeff]
  split_ifs <;> simp

end SptClassification.QSeries
