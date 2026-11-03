/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.MockCompletion
public import SptClassification.ModularForms.ConditionalPropagation
public import SptClassification.Arithmetic.CharacterTwelve

/-!
# Transformation of the completed smallest-parts function

The source statement concerns the actual completed function, before any
quadratic twist or modular approximation is constructed.
-/

public section

namespace SptClassification

open UpperHalfPlane
open scoped MatrixGroups

/-- The weight `3/2`, level `576`, character `(12/·)` transformation law
recorded in [ahlgrenAndersen2016, §3, immediately after (3.2), PDF p. 9],
attributed there to [bringmann2008]. The normalization of the function is
the integral (3.1) of that source. The multiplier here is the standard
theta multiplier cubed. This is an admitted literature theorem, not the
twisted modularity or propagation conclusion of the submitted manuscript. -/
theorem ahlgrenAndersen_sptCompletion_map_action
    (γ : CongruenceSubgroup.Gamma0 576) (τ : UpperHalfPlane) :
    sptCompletion ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • τ) =
      (characterTwelve
        (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) *
      standardProgressionFactor 1 true γ τ * sptCompletion τ := by
  sorry

end SptClassification
