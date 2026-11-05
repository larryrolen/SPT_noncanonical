/- Assembled by AxiomProver. -/

module

public import SptClassification.Partitions.Basic
public import SptClassification.QSeries.HeckeCoefficients

/-!
# Fourier coefficients at exponents `r/24`

The sequences below give the unscaled expansions of `P = η⁻¹`, the
smallest-parts series `S`, and `f = -12 S - 24 Θ P`.  An index outside
`24n - 1`, for `n : ℕ`, has coefficient zero, including every index below
`-1`. We follow the normalization in [rolenManuscript].
-/

@[expose] public section

namespace SptClassification.QSeries

/-- Place a sequence at the integral indices `24n - 1` and extend it by zero.
The support test is used by modular-form propagation proofs. -/
@[expose] noncomputable def shiftedTwentyFour (a : ℕ → ℤ) (r : ℤ) : ℤ :=
  by
    classical
    exact if h : (∃ n : ℕ, r = 24 * (n : ℤ) - 1) then a (Classical.choose h) else 0

@[simp] theorem shiftedTwentyFour_at (a : ℕ → ℤ) (n : ℕ) :
    shiftedTwentyFour a (24 * (n : ℤ) - 1) = a n := by
  unfold shiftedTwentyFour
  classical
  split_ifs with h
  · have hn : Classical.choose h = n := by
      have hc := Classical.choose_spec h
      omega
    rw [hn]
  · exact False.elim (h ⟨n, rfl⟩)

theorem shiftedTwentyFour_eq_zero_of_lt (a : ℕ → ℤ) {r : ℤ} (hr : r < -1) :
    shiftedTwentyFour a r = 0 := by
  unfold shiftedTwentyFour
  classical
  split_ifs with h
  · obtain ⟨n, hn⟩ := h
    omega
  · rfl

/-- Every nonzero shifted coefficient has its prescribed exponent residue. -/
theorem shiftedTwentyFour_support (a : ℕ → ℤ) (r : ℤ)
    (h : shiftedTwentyFour a r ≠ 0) : -1 ≤ r ∧ r % 24 = 23 := by
  classical
  unfold shiftedTwentyFour at h
  split_ifs at h with hr
  · obtain ⟨n, hn⟩ := hr
    constructor <;> omega
  · exact (h rfl).elim

/-- Coefficients of `P = η⁻¹` at exponents `r/24`. -/
noncomputable def partitionFourier (r : ℤ) : ℤ :=
  shiftedTwentyFour (fun n => (partitionCount n : ℤ)) r

/-- Coefficients of the smallest-parts series at exponents `r/24`. -/
@[expose] noncomputable def sptFourier (r : ℤ) : ℤ :=
  shiftedTwentyFour (fun n => (spt n : ℤ)) r

/-- The unscaled coefficients `a(r)` of `f = -12 S - 24 Θ P`. -/
noncomputable def fFourier (r : ℤ) : ℤ :=
  -12 * sptFourier r - r * partitionFourier r

@[simp] theorem partitionFourier_at (n : ℕ) :
    partitionFourier (24 * (n : ℤ) - 1) = partitionCount n :=
  shiftedTwentyFour_at _ n

@[simp] theorem sptFourier_at (n : ℕ) :
    sptFourier (24 * (n : ℤ) - 1) = spt n :=
  shiftedTwentyFour_at _ n

theorem fFourier_at (n : ℕ) :
    fFourier (24 * (n : ℤ) - 1) =
      -12 * (spt n : ℤ) - (24 * (n : ℤ) - 1) * (partitionCount n : ℤ) := by
  simp [fFourier]

@[simp] theorem partitionFourier_neg_one : partitionFourier (-1) = 1 := by
  convert partitionFourier_at 0 using 1 <;> norm_num

@[simp] theorem sptFourier_neg_one : sptFourier (-1) = 0 := by
  convert sptFourier_at 0 using 1 <;> norm_num

@[simp] theorem fFourier_neg_one : fFourier (-1) = 1 := by
  simp [fFourier]

theorem partitionFourier_eq_zero_of_lt {r : ℤ} (hr : r < -1) :
    partitionFourier r = 0 := shiftedTwentyFour_eq_zero_of_lt _ hr

/-- The inverse-eta row starts at `-1` and is supported on `23` modulo `24`. -/
theorem partitionFourier_support (r : ℤ) (h : partitionFourier r ≠ 0) :
    -1 ≤ r ∧ r % 24 = 23 :=
  shiftedTwentyFour_support _ r h

theorem sptFourier_eq_zero_of_lt {r : ℤ} (hr : r < -1) :
    sptFourier r = 0 := shiftedTwentyFour_eq_zero_of_lt _ hr

theorem fFourier_eq_zero_of_lt {r : ℤ} (hr : r < -1) : fFourier r = 0 := by
  simp [fFourier, partitionFourier_eq_zero_of_lt hr, sptFourier_eq_zero_of_lt hr]

/-- The integral coefficient form of the derivative relation. -/
theorem fFourier_add_twelve_spt (r : ℤ) :
    fFourier r + 12 * sptFourier r = -r * partitionFourier r := by
  unfold fFourier
  ring

/-- On negative indices the smallest-parts series vanishes. -/
theorem fFourier_negative {r : ℤ} (hr : r < 0) :
    fFourier r = -r * partitionFourier r := by
  by_cases h : r = -1
  · subst r
    simp
  · have hlt : r < -1 := by omega
    simp [fFourier, sptFourier_eq_zero_of_lt hlt]

end SptClassification.QSeries
