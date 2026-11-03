/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.NormalizedAutomorphy

/-!
# Cusp expansions of the normalized representative

The separate twisted forms have meromorphic expansions after a common
half-integral slash and a common cusp width. Their normalized combination
in [rolenManuscript, §2, (2.5)] then has a meromorphic fourth-power slash.
The local expansions below concern the constituent forms, not the desired
approximation or its reduction.
-/

public section

namespace SptClassification

open UpperHalfPlane

/-- Assemble the meromorphic cusp expansion of the normalized representative
from expansions of its three half-integral constituents and its two
Eisenstein factors. The same slash factor and width are required explicitly. -/
theorem SptTwistedAnalyticData.normalizedRepresentative_meromorphic_cusp
    {p Q : ℕ} [Fact p.Prime] [Fact Q.Prime]
    (A : SptTwistedAnalyticData Q) (hp : 5 ≤ p)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (width : ℕ)
    (j : UpperHalfPlane → ℂ)
    (GM GD GP GEminus GEplus : ℂ → ℂ)
    (hGM : MeromorphicAt GM 0) (hGD : MeromorphicAt GD 0)
    (hGP : MeromorphicAt GP 0) (hGEminus : MeromorphicAt GEminus 0)
    (hGEplus : MeromorphicAt GEplus 0)
    (hj : ∀ τ, j τ ≠ 0)
    (hfour : ∀ τ, j τ ^ 4 = (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ) ^ 2)
    (hM : ∀ τ, A.twistedM (γ • τ) =
      j τ ^ 3 * GM (Function.Periodic.qParam width τ))
    (hD : ∀ τ, A.serreDerivativeP (γ • τ) =
      j τ ^ 3 * GD (Function.Periodic.qParam width τ))
    (hP : ∀ τ, A.twistedP (γ • τ) =
      GP (Function.Periodic.qParam width τ) / j τ)
    (hEminus : ∀ τ, ModularForm.E (k := p - 1) (by omega) τ =
      GEminus (Function.Periodic.qParam width τ))
    (hEplus : ∀ τ, ModularForm.E (k := p + 1) (by omega) τ =
      GEplus (Function.Periodic.qParam width τ)) :
    ∃ G : ℂ → ℂ, MeromorphicAt G 0 ∧ ∀ τ : UpperHalfPlane,
      G (Function.Periodic.qParam width τ) =
        A.normalizedRepresentative p hp (γ • τ) ^ 4 /
          (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ) ^ (4 * p + 2) := by
  let H : ℂ → ℂ := fun q =>
    GEminus q * (GM q - GD q / 12) + GEplus q * GP q / 288
  have hH : MeromorphicAt H 0 :=
    (hGEminus.mul (hGM.sub (hGD.div (MeromorphicAt.const (12 : ℂ) 0)))).add
      ((hGEplus.mul hGP).div (MeromorphicAt.const (288 : ℂ) 0))
  refine ⟨fun q => H q ^ 4, hH.pow 4, ?_⟩
  intro τ
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  obtain ⟨hm, hp'⟩ := normalizedThetaFactors hodd (hj τ) (hfour τ)
  have hF : A.normalizedRepresentative p hp (γ • τ) =
      j τ ^ (2 * p + 1) * H (Function.Periodic.qParam width τ) := by
    rw [A.normalizedRepresentative_apply, hM, hD, hP,
      eisenstein_map_action, eisenstein_map_action, hEminus, hEplus]
    dsimp only [H]
    linear_combination
      (GEminus (Function.Periodic.qParam width τ) *
        (GM (Function.Periodic.qParam width τ) -
          GD (Function.Periodic.qParam width τ) / 12)) * hm +
      (GEplus (Function.Periodic.qParam width τ) *
        GP (Function.Periodic.qParam width τ) / 288) * hp'
  have hpower : (j τ ^ (2 * p + 1)) ^ 4 =
      (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ) ^ (4 * p + 2) := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hfour, ← pow_mul]
    congr 1
    omega
  rw [hF, mul_pow, hpower]
  exact (mul_div_cancel_left₀ _ (pow_ne_zero _ (denom_ne_zero _ τ))).symm

end SptClassification
