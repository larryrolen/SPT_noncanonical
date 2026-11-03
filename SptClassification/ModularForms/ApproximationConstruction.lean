/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.PrimeLocalNormalizedProduct

/-!
# Constructing the normalized approximation from analytic modularity

The Fourier coefficients, prime-local reductions and pole bound of the
representative in [rolenManuscript, §2, (2.5)] are constructed here. Only
holomorphy, the standard transformation law and meromorphy at cusps remain
to be supplied by the twisted mock-form and Serre-derivative construction.
No approximation or coefficient-identification theorem is assumed.
-/

public section

namespace SptClassification

open UpperHalfPlane
open scoped MatrixGroups Manifold

/-- Build the actual normalized approximation once its analytic modularity
has been established. Its rational row and residue row are fixed by the
convergent Fourier calculation and the two Eisenstein congruences, including
all negative indices. The hypotheses here concern the analytic function,
not a putative modular coefficient object. -/
noncomputable def SptTwistedAnalyticData.approximationOfModularity
    {p Q : ℕ} [Fact p.Prime] [Fact Q.Prime] (A : SptTwistedAnalyticData Q)
    (hp : 5 ≤ p) (N : ℕ) (hN : 0 < N) (hfour : 4 ∣ N)
    (hlevel : N ∣ 576 * Q ^ 4)
    (χ : CongruenceSubgroup.Gamma0 N →* ℂ)
    (ψ : DirichletCharacter ℂ N)
    (hχψ : ∀ γ, χ γ = ψ
      ((((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ)
        1 1 : ℤ) : ZMod N))
    (hχ : ∀ γ, χ γ ^ 2 = 1)
    (hhol : MDiff (A.normalizedRepresentative p hp))
    (htrans : ∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : UpperHalfPlane),
      A.normalizedRepresentative p hp ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • τ) =
        χ γ * standardProgressionFactor p true γ τ *
          A.normalizedRepresentative p hp τ)
    (hcusps : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      ∃ width : ℕ, 0 < width ∧ ∃ G : ℂ → ℂ, MeromorphicAt G 0 ∧
        ∀ τ : UpperHalfPlane,
          G (Function.Periodic.qParam width τ) =
            A.normalizedRepresentative p hp (γ • τ) ^ 4 /
              (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ) ^ (4 * p + 2)) :
    SptModularApproximation p Q hp where
  toSptTwistedAnalyticData := A
  form := {
    level := N
    level_pos := hN
    weightNumerator := p
    halfIntegral := true
    level_four := fun _ => hfour
    toFun := A.normalizedRepresentative p hp
    holomorphic := hhol
    character := χ
    nebentypus := ψ
    character_eq_nebentypus := hχψ
    character_one := χ.map_one
    character_mul := χ.map_mul
    character_quadratic := hχ
    map_action := htrans
    meromorphic_cusps := hcusps
    coeff := normalizedRepresentativeRationalRow p Q
    coeffMod := fun r => (QSeries.sptTwistedLaurent p Q).coeff r
    pIntegral := by
      intro r
      exact (normalizedRepresentativeRationalRow_reduces_twistedS (Q := Q) hp r).witnesses
    lowerBound := ⟨-1, normalizedRepresentativeRationalRow_zero_below p Q⟩
    hasSum_qExpansion := A.normalizedRepresentative_hasSum }
  weight_eq := rfl
  halfIntegral_eq := rfl
  level_divides := hlevel
  normalized_representative := A.normalizedRepresentative_apply p hp

end SptClassification
