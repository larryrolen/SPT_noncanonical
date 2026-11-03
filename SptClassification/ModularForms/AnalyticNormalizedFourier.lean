/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.AnalyticLaurentProducts
public import SptClassification.ModularForms.ConditionalPropagation

/-!
# Analytic Fourier products in the normalized spt approximation

The quasimodular correction in [rolenManuscript, §2, (2.5)] has a genuine
convergent rational Laurent row. Its coefficient convolution is constructed
from the independently supplied expansions of `E₂` and the twisted partition
series, without identifying the normalized modular form's coefficients.
-/

public section

namespace SptClassification

open UpperHalfPlane

/-- The rational power-series row of the normalized weight-two Eisenstein
series. -/
noncomputable def eisensteinTwoRationalSeries : PowerSeries ℚ :=
  PowerSeries.mk eisensteinTwoCoefficient

@[simp] theorem eisensteinTwoRationalSeries_coeff (n : ℕ) :
    eisensteinTwoRationalSeries.coeff n = eisensteinTwoCoefficient n := by
  simp [eisensteinTwoRationalSeries]

/-- The actual quadratically selected inverse-eta row, over `ℚ`. -/
noncomputable def twistedPartitionRationalRow (Q : ℕ) [Fact Q.Prime] (r : ℤ) : ℚ :=
  negativeSquareSelector Q r * QSeries.partitionFourier r

@[simp] theorem twistedPartitionRationalRow_eq (Q : ℕ) [Fact Q.Prime]
    (r : ℤ) :
    twistedPartitionRationalRow Q r =
      negativeSquareSelector Q r * QSeries.partitionFourier r := by
  rfl

theorem twistedPartitionRationalRow_zero_below (Q : ℕ) [Fact Q.Prime]
    (r : ℤ) (hr : r < -1) : twistedPartitionRationalRow Q r = 0 := by
  simp [twistedPartitionRationalRow, QSeries.partitionFourier_eq_zero_of_lt hr]

/-- Analytic Cauchy expansion of the `E₂ P_Q` correction. The two input
expansions are already present in the approximation; no coefficient of its
normalized modular form is assumed here. -/
theorem SptTwistedAnalyticData.eisensteinTwo_twistedP_hasSum
    {Q : ℕ} [Fact Q.Prime]
    (A : SptTwistedAnalyticData Q) (τ : UpperHalfPlane) :
    HasSum (fun r : ℤ =>
      (rationalLaurentProductRow
        (nonnegativeRationalRow eisensteinTwoRationalSeries)
        (twistedPartitionRationalRow Q) 0 1 r : ℂ) *
          Function.Periodic.qParam 1 τ ^ r)
      (A.eisensteinTwo τ * A.twistedP τ) := by
  let q := Function.Periodic.qParam 1 τ
  have hq : q ≠ 0 := Complex.exp_ne_zero _
  have hE : HasSum (fun r : ℤ =>
      (nonnegativeRationalRow eisensteinTwoRationalSeries r : ℂ) * q ^ r)
      (A.eisensteinTwo τ) := by
    apply nonnegativeRationalRow_hasSum eisensteinTwoRationalSeries q
      (A.eisensteinTwo τ) hq
    simpa only [eisensteinTwoRationalSeries_coeff] using A.eisensteinTwo_expansion τ
  have hP : HasSum (fun r : ℤ =>
      (twistedPartitionRationalRow Q r : ℂ) * q ^ r) (A.twistedP τ) := by
    simpa only [twistedPartitionRationalRow] using A.twistedP_expansion τ
  exact rationalLaurentProductRow_hasSum
    (nonnegativeRationalRow eisensteinTwoRationalSeries)
    (twistedPartitionRationalRow Q) 0 1
    (by intro r hr; exact nonnegativeRationalRow_zero_below _ r (by omega))
    (twistedPartitionRationalRow_zero_below Q)
    q (A.eisensteinTwo τ) (A.twistedP τ) hq hE hP

/-- The selected smallest-parts row before multiplying by the two ordinary
Eisenstein series in the normalized approximation. -/
noncomputable def twistedSmallestPartsRationalRow (Q : ℕ) [Fact Q.Prime]
    (r : ℤ) : ℚ :=
  negativeSquareSelector Q r * (QSeries.sptFourier r : ℚ)

@[simp] theorem twistedSmallestPartsRationalRow_eq (Q : ℕ) [Fact Q.Prime]
    (r : ℤ) :
    twistedSmallestPartsRationalRow Q r =
      negativeSquareSelector Q r * (QSeries.sptFourier r : ℚ) := by
  rfl

theorem twistedSmallestPartsRationalRow_zero_below (Q : ℕ) [Fact Q.Prime]
    (r : ℤ) (hr : r < -1) : twistedSmallestPartsRationalRow Q r = 0 := by
  rw [twistedSmallestPartsRationalRow_eq, QSeries.sptFourier_eq_zero_of_lt hr]
  simp

/-- The full rational Laurent row of the inner factor
`M_Q - D₋₁/₂ P_Q / 12` after cancelling its theta part. Its product
coefficient is obtained by analytic Cauchy multiplication. -/
noncomputable def normalizedInnerRationalRow (Q : ℕ) [Fact Q.Prime]
    (r : ℤ) : ℚ :=
  twistedSmallestPartsRationalRow Q r -
    rationalLaurentProductRow
      (nonnegativeRationalRow eisensteinTwoRationalSeries)
      (twistedPartitionRationalRow Q) 0 1 r / 288

theorem normalizedInnerRationalRow_eq (Q : ℕ) [Fact Q.Prime] (r : ℤ) :
    normalizedInnerRationalRow Q r =
      twistedSmallestPartsRationalRow Q r -
        rationalLaurentProductRow
          (nonnegativeRationalRow eisensteinTwoRationalSeries)
          (twistedPartitionRationalRow Q) 0 1 r / 288 := by
  rfl

theorem normalizedInnerRationalRow_zero_below (Q : ℕ) [Fact Q.Prime]
    (r : ℤ) (hr : r < -1) : normalizedInnerRationalRow Q r = 0 := by
  rw [normalizedInnerRationalRow,
    twistedSmallestPartsRationalRow_zero_below Q r hr,
    rationalLaurentProductRow_zero_below
      (nonnegativeRationalRow eisensteinTwoRationalSeries)
      (twistedPartitionRationalRow Q) 0 1 r (by omega : r < -((0 + 1 : ℕ) : ℤ))]
  norm_num

/-- Genuine convergent Fourier expansion of the inner factor in (2.5).
This assertion uses the stated expansions of the twisted forms and `E₂`;
it makes no assertion about reduction of the final modular form. -/
theorem SptTwistedAnalyticData.normalizedInner_hasSum
    {Q : ℕ} [Fact Q.Prime]
    (A : SptTwistedAnalyticData Q) (τ : UpperHalfPlane) :
    HasSum (fun r : ℤ => (normalizedInnerRationalRow Q r : ℂ) *
      Function.Periodic.qParam 1 τ ^ r)
      (A.twistedS τ - A.eisensteinTwo τ * A.twistedP τ / 288) := by
  have hs := A.twistedS_expansion τ
  have hp := (A.eisensteinTwo_twistedP_hasSum τ).const_smul (1 / 288 : ℂ)
  have h := hs.sub hp
  convert h using 1
  · ext r
    simp only [normalizedInnerRationalRow, twistedSmallestPartsRationalRow]
    push_cast
    ring
  · ring

end SptClassification
