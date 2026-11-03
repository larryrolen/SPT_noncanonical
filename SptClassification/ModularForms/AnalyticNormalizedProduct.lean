/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.AnalyticEisensteinRows
public import SptClassification.ModularForms.AnalyticNormalizedFourier
public import SptClassification.ModularForms.ProgressionFourierUniqueness

/-!
# Fourier row of the normalized modular approximation

The two level-one Eisenstein factors in [rolenManuscript, §2, (2.5)]
multiply the convergent selected rows. The resulting rational Laurent row is
identified with the actual modular form by analytic coefficient uniqueness.
Reduction of its rational coefficients is a separate arithmetic question.
-/

public section

namespace SptClassification

open UpperHalfPlane

/-- The rational Laurent row of the complete normalized representative in
(2.5), before reduction modulo the auxiliary prime. -/
noncomputable def normalizedRepresentativeRationalRow (p Q : ℕ)
    [Fact Q.Prime] (r : ℤ) : ℚ :=
  rationalLaurentProductRow
      (nonnegativeRationalRow (normalizedEisensteinRationalSeries (p - 1)))
      (normalizedInnerRationalRow Q) 0 1 r +
    rationalLaurentProductRow
      (nonnegativeRationalRow (normalizedEisensteinRationalSeries (p + 1)))
      (twistedPartitionRationalRow Q) 0 1 r / 288

theorem normalizedRepresentativeRationalRow_eq (p Q : ℕ)
    [Fact Q.Prime] (r : ℤ) :
    normalizedRepresentativeRationalRow p Q r =
      rationalLaurentProductRow
          (nonnegativeRationalRow (normalizedEisensteinRationalSeries (p - 1)))
          (normalizedInnerRationalRow Q) 0 1 r +
        rationalLaurentProductRow
          (nonnegativeRationalRow (normalizedEisensteinRationalSeries (p + 1)))
          (twistedPartitionRationalRow Q) 0 1 r / 288 := by
  rfl

theorem normalizedRepresentativeRationalRow_zero_below (p Q : ℕ)
    [Fact Q.Prime] (r : ℤ) (hr : r < -1) :
    normalizedRepresentativeRationalRow p Q r = 0 := by
  simp [normalizedRepresentativeRationalRow,
    rationalLaurentProductRow_zero_below
      (nonnegativeRationalRow (normalizedEisensteinRationalSeries (p - 1)))
      (normalizedInnerRationalRow Q) 0 1 r (by omega),
    rationalLaurentProductRow_zero_below
      (nonnegativeRationalRow (normalizedEisensteinRationalSeries (p + 1)))
      (twistedPartitionRationalRow Q) 0 1 r (by omega)]

/-- The complete normalized representative has the Cauchy-product row, as
an equality of analytic Fourier sums. -/
theorem SptTwistedAnalyticData.normalizedRepresentative_hasSum
    {p Q : ℕ} {hfive : 5 ≤ p} [Fact p.Prime] [Fact Q.Prime]
    (A : SptTwistedAnalyticData Q) (τ : UpperHalfPlane) :
    HasSum (fun r : ℤ =>
      (normalizedRepresentativeRationalRow p Q r : ℂ) *
        Function.Periodic.qParam 1 τ ^ r) (A.normalizedRepresentative p hfive τ) := by
  let q := Function.Periodic.qParam 1 τ
  have hq : q ≠ 0 := Complex.exp_ne_zero _
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  obtain ⟨j, hj⟩ := hpodd
  have hevenMinus : Even (p - 1) := ⟨j, by omega⟩
  have hevenPlus : Even (p + 1) := ⟨j + 1, by omega⟩
  have hminus : HasSum (fun r : ℤ =>
      (nonnegativeRationalRow
        (normalizedEisensteinRationalSeries (p - 1)) r : ℂ) * q ^ r)
      (ModularForm.E (k := p - 1) (by omega) τ) := by
    apply nonnegativeRationalRow_hasSum _ q _ hq
    exact normalizedEisensteinRationalSeries_hasSum (by omega) hevenMinus τ
  have hplus : HasSum (fun r : ℤ =>
      (nonnegativeRationalRow
        (normalizedEisensteinRationalSeries (p + 1)) r : ℂ) * q ^ r)
      (ModularForm.E (k := p + 1) (by omega) τ) := by
    apply nonnegativeRationalRow_hasSum _ q _ hq
    exact normalizedEisensteinRationalSeries_hasSum (by omega) hevenPlus τ
  have hfirst := rationalLaurentProductRow_hasSum
    (nonnegativeRationalRow (normalizedEisensteinRationalSeries (p - 1)))
    (normalizedInnerRationalRow Q) 0 1
    (by intro r hr; exact nonnegativeRationalRow_zero_below _ r (by omega))
    (normalizedInnerRationalRow_zero_below Q)
    q (ModularForm.E (k := p - 1) (by omega) τ)
      (A.twistedS τ - A.eisensteinTwo τ * A.twistedP τ / 288)
      hq hminus (A.normalizedInner_hasSum τ)
  have hsecond := rationalLaurentProductRow_hasSum
    (nonnegativeRationalRow (normalizedEisensteinRationalSeries (p + 1)))
    (twistedPartitionRationalRow Q) 0 1
    (by intro r hr; exact nonnegativeRationalRow_zero_below _ r (by omega))
    (twistedPartitionRationalRow_zero_below Q)
    q (ModularForm.E (k := p + 1) (by omega) τ)
      (A.twistedP τ) hq hplus
      (by simpa only [twistedPartitionRationalRow_eq] using A.twistedP_expansion τ)
  have h := hfirst.add (hsecond.const_smul (1 / 288 : ℂ))
  convert h using 1
  · ext r
    simp only [normalizedRepresentativeRationalRow]
    push_cast
    ring
  · rw [A.normalizedRepresentative_eq p hfive τ]
    ring

/-- The constructed approximation has the same analytic row. -/
theorem SptModularApproximation.normalizedRepresentative_hasSum
    {p Q : ℕ} {hfive : 5 ≤ p} [Fact p.Prime] [Fact Q.Prime]
    (A : SptModularApproximation p Q hfive) (τ : UpperHalfPlane) :
    HasSum (fun r : ℤ =>
      (normalizedRepresentativeRationalRow p Q r : ℂ) *
        Function.Periodic.qParam 1 τ ^ r) (A.form.toFun τ) := by
  rw [A.normalized_representative τ]
  simpa only [SptTwistedAnalyticData.normalizedRepresentative_apply] using
    A.toSptTwistedAnalyticData.normalizedRepresentative_hasSum (p := p) (hfive := hfive) τ

/-- Analytic uniqueness removes the coefficient-comparison field for the
actual normalized representative. The pole bound is a property of the
modular form, not an extra coefficient identification. -/
theorem SptModularApproximation.form_coeff_eq_normalizedRepresentative
    {p Q : ℕ} {hfive : 5 ≤ p} [Fact p.Prime] [Fact Q.Prime]
    (A : SptModularApproximation p Q hfive) (M : ℕ) (hM : 1 ≤ M)
    (hbelow : ∀ r : ℤ, r < -(M : ℤ) → A.form.coeff r = 0)
    (r : ℤ) :
    A.form.coeff r = normalizedRepresentativeRationalRow p Q r := by
  apply A.form.coeff_eq_of_laurentRow M
    (normalizedRepresentativeRationalRow p Q) hbelow
  · intro n hn
    exact normalizedRepresentativeRationalRow_zero_below p Q n (by omega)
  · exact A.normalizedRepresentative_hasSum

/-- Every coefficient of the actual modular form is the corresponding
coefficient of the analytically derived rational row. -/
theorem SptModularApproximation.form_coeff_eq_normalizedRepresentative_all
    {p Q : ℕ} {hfive : 5 ≤ p} [Fact p.Prime] [Fact Q.Prime]
    (A : SptModularApproximation p Q hfive) (r : ℤ) :
    A.form.coeff r = normalizedRepresentativeRationalRow p Q r := by
  obtain ⟨B, hB⟩ := A.form.lowerBound
  let M := (-B).toNat + 2
  have hM : 1 ≤ M := by omega
  have hNeg : -(M : ℤ) ≤ B := by
    dsimp [M]
    omega
  exact A.form_coeff_eq_normalizedRepresentative M hM
    (by intro n hn; exact hB n (lt_of_lt_of_le hn hNeg)) r

end SptClassification
