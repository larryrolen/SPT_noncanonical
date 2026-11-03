/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.ActualNormalizedFourthPower
public import SptClassification.ModularForms.NormalizedCuspGrowth
public import SptClassification.ModularForms.ScaledGeneratingGrowth

/-!
# Meromorphy at the cusps of the actual normalized representative

Coefficient growth, finite Fourier filtering, and fourth-power automorphy
supply the cusp condition for the representative of [rolenManuscript, (2.5)].
-/

public section

namespace SptClassification

open UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm

/-- The actual normalized fourth power has a meromorphic q representative at
every cusp. Its exponential estimate follows from the partition asymptotic;
no cusp condition on the manuscript representative is assumed. -/
theorem sptTwistedAnalyticData_normalizedRepresentative_cusps
    {p Q : ℕ} [Fact p.Prime] [Fact Q.Prime] (hp : 5 ≤ p) (hQ : Odd Q)
    (γ : SL(2, ℤ)) :
    ∃ width : ℕ, 0 < width ∧ ∃ G : ℂ → ℂ, MeromorphicAt G 0 ∧
      ∀ τ : UpperHalfPlane,
        G (Function.Periodic.qParam width τ) =
          (sptTwistedAnalyticData Q).normalizedRepresentative p hp (γ • τ) ^ 4 /
            denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ ^ (4 * p + 2) := by
  have hlevel : 0 < 576 * Q ^ 4 := by
    have := (Fact.out : Q.Prime).pos
    positivity
  have hhol : MDiff (fun τ =>
      (sptTwistedAnalyticData Q).normalizedRepresentative p hp τ ^ 4) :=
    (sptTwistedAnalyticData_normalizedRepresentative_holomorphic p Q hp).pow 4
  have hgrowth : ∀ δ : SL(2, ℤ), ∃ C A Y : ℝ, 0 ≤ C ∧
      ∀ τ : UpperHalfPlane, |τ.re| ≤ (576 * Q ^ 4 : ℕ) → Y ≤ τ.im →
        ‖((fun z => (sptTwistedAnalyticData Q).normalizedRepresentative p hp z ^ 4)
          ∣[((4 * p + 2 : ℕ) : ℤ)] δ) τ‖ ≤ C * Real.exp (A * τ.im) := by
    intro δ
    obtain ⟨C, A, hC, hA, hbound⟩ := exists_scaledPartition_spt_height_growth
    have hS := fourierFilter_hasExponentialGrowthOnStrip
      (negativeSquareResidueSelector Q) scaledSptFunction hC.le hA.le
      (fun τ => (hbound τ).2) δ (R := (576 * Q ^ 4 : ℕ)) (by positivity)
    have hP := fourierFilter_hasExponentialGrowthOnStrip
      (negativeSquareResidueSelector Q) scaledPartitionFunction hC.le hA.le
      (fun τ => (hbound τ).1) δ (R := (576 * Q ^ 4 : ℕ)) (by positivity)
    obtain ⟨C', A', Y, hC', _, _, h⟩ :=
      (sptTwistedAnalyticData_normalizedSlash_growth p Q hp δ (by positivity) hS hP).exists_bounds
    refine ⟨C', A', Y, hC', ?_⟩
    simpa only [integral_slash_nat_apply] using h
  obtain ⟨w, hw, G, hG, h⟩ :=
    meromorphic_integral_cusps_of_symmetric_strip_exp_bounds hlevel hhol
      (sptTwistedAnalyticData_normalizedFourthPower_slash hp hQ) hgrowth γ
  refine ⟨w, hw, G, hG, ?_⟩
  simpa only [integral_slash_nat_apply] using h

end SptClassification
