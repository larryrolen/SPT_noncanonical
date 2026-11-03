/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.FourierFilterTransformation
public import SptClassification.ModularForms.ThetaMultiplier

/-!
# Rational translation and the theta multiplier

The matrix calculation in [kunduMuller2025, Proposition 2.5, proof, p. 7]
intertwines rational translates and congruence transformations. Unlike the
positive-weight twisting proposition, this calculation concerns only
matrices and theta. The finite-filter transformation is proved from it for
arbitrary integral powers of the theta multiplier.
-/

public section

namespace SptClassification

open UpperHalfPlane
open scoped MatrixGroups

/-- The weight-independent calculation in [kunduMuller2025, Proposition 2.5,
proof, p. 7], using the theta formula of [koblitz1993, p. 148]. The source
uses translations `-v/M`; here `j=-v` and `j'=d²j`. Conjugating by those
translations gives an integral matrix at level `N`, with lower-right entry
unchanged modulo `N`, and the same theta multiplier. The odd modulus
restriction suffices for the application here. This named literature
premise asserts no transformation law for any other function. -/
theorem koblitz_theta_rational_translation
    {N M : ℕ} [NeZero M] (hN : 0 < N) (h4 : 4 ∣ N) (hM : Odd M)
    (γ : CongruenceSubgroup.Gamma0 (N * M ^ 2)) :
    ∃ u : (ZMod M)ˣ,
      (u : ZMod M) = (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
        Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) ∧
      ∀ j : ZMod M, ∃ δ : CongruenceSubgroup.Gamma0 N,
        ((((δ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
          Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N) =
        ((((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
          Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N) ∧
        ∀ τ : UpperHalfPlane,
          fourierTranslate j (γ • τ) =
            δ • fourierTranslate ((u : ZMod M) ^ 2 * j) τ ∧
          jacobiTheta (2 * ((δ • fourierTranslate ((u : ZMod M) ^ 2 * j) τ :
              UpperHalfPlane) : ℂ)) /
              jacobiTheta (2 * (fourierTranslate ((u : ZMod M) ^ 2 * j) τ : ℂ)) =
            jacobiTheta (2 * ((γ • τ : UpperHalfPlane) : ℂ)) /
              jacobiTheta (2 * (τ : ℂ)) := by
  sorry

/-- A square-invariant Fourier selector preserves arbitrary integer powers
of the theta transformation law. In particular this applies to harmonic
functions of weight `3/2` and holomorphic functions of weight `-1/2`. -/
theorem fourierFilter_theta_map_action
    {N M : ℕ} [NeZero M] (hN : 0 < N) (h4 : 4 ∣ N) (hM : Odd M)
    (c : ZMod M → ℂ)
    (hc : ∀ (u : (ZMod M)ˣ) x, c ((u : ZMod M) ^ 2 * x) = c x)
    (F : UpperHalfPlane → ℂ) (χ : ZMod N → ℂ) (k : ℤ)
    (hF : ∀ (δ : CongruenceSubgroup.Gamma0 N) (τ : UpperHalfPlane),
      F (δ • τ) = χ ((((δ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
        Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N) *
        (jacobiTheta (2 * ((δ • τ : UpperHalfPlane) : ℂ)) /
          jacobiTheta (2 * (τ : ℂ))) ^ k * F τ)
    (γ : CongruenceSubgroup.Gamma0 (N * M ^ 2)) (τ : UpperHalfPlane) :
    fourierFilter c F (γ • τ) =
      χ ((((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
        Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N) *
        (jacobiTheta (2 * ((γ • τ : UpperHalfPlane) : ℂ)) /
          jacobiTheta (2 * (τ : ℂ))) ^ k * fourierFilter c F τ := by
  obtain ⟨u, _, hu⟩ := koblitz_theta_rational_translation hN h4 hM γ
  apply fourierFilter_map_of_translate c F (u ^ 2)
    (by simpa only [Units.val_pow_eq_pow_val] using hc u)
  intro j
  obtain ⟨δ, hd, hδ⟩ := hu j
  obtain ⟨haction, htheta⟩ := hδ τ
  simpa only [Units.val_pow_eq_pow_val, haction, hF, hd, htheta]

end SptClassification
