/- Assembled by AxiomProver. -/

module

public import SptClassification.Classification.ConditionalClassification
public import SptClassification.QuadraticForms.RealizedCMSeparation
public import SptClassification.QSeries.AnalyticConstantTerms

/-!
# Classification from realized CM trace geometry

The positive trace realization supplies the general Hadamard bound used in
CM separation. The lift uses exactly the same descended polynomials and
reduction map. All remaining analytic and geometric inputs stay explicit.
[rolenManuscript, Sections 4--5] [rolen2026canonical, Lemma 5.2]
-/

public section

namespace SptClassification

/-- CM descent with positive trace realization and the lift/Hasse data on
those same models. No determinant inequality is assumed.
[rolenManuscript, Section 4] -/
structure RealizedCharacterObstructionGeometry (p d : ℕ) [Fact p.Prime]
    [Fact (-(d : ℤ) < 0)] where
  cm : ConditionalCM.RealizedCMDescentInput d p
  Form : Type
  formRing : CommRing Form
  formAlgebra : letI : CommRing Form := formRing
    Algebra (ZMod p) Form
  Point : Type
  lift : letI : CommRing Form := formRing
    letI : Algebra (ZMod p) Form := formAlgebra
    LiftHasseInput p d cm.toCMDescentInput Form Point

/-- Supply the proved trace bound without changing the models or lift. -/
def RealizedCharacterObstructionGeometry.toCharacterObstructionGeometry
    {p d : ℕ} [Fact p.Prime] [Fact (-(d : ℤ) < 0)]
    (G : RealizedCharacterObstructionGeometry p d) : CharacterObstructionGeometry p d where
  cm := G.cm.toCMDescentInput
  Form := G.Form
  formRing := G.formRing
  formAlgebra := G.formAlgebra
  Point := G.Point
  lift := G.lift

/-- Realized geometry at every admissible discriminant, independently of
any vanishing character class. The bounds are precisely those used by the
finite/effective witness argument. [rolenManuscript, Sections 4--5] -/
structure RealizedCharacterObstructionInputFamily where
  atDiscriminant : ∀ (p d : ℕ) [Fact p.Prime]
    [Fact (-(d : ℤ) < 0)],
    5 ≤ p → 23 ≤ d → d % 24 = 23 → Squarefree d →
    ¬p ∣ 6 * d → (d + 1) ^ 2 < 24 * p →
    8 * formClassNumber (-(d : ℤ)) < p + 1 →
    RealizedCharacterObstructionGeometry p d

/-- Convert the family pointwise using the proved trace bound. -/
def RealizedCharacterObstructionInputFamily.toCharacterObstructionInputFamily
    (G : RealizedCharacterObstructionInputFamily) : CharacterObstructionInputFamily where
  atDiscriminant := fun p d _ _ hp hd hmod hsq hcop hbound hclassBound =>
    RealizedCharacterObstructionGeometry.toCharacterObstructionGeometry
      (G.atDiscriminant p d hp hd hmod hsq hcop hbound hclassBound)

/-- Conditional noncanonical exclusion with the Hadamard hypothesis
replaced by positive trace realization. All remaining CT, TR/AP, TV,
CM/descent/EO and LF/QX/HG inputs are explicit.
[rolenManuscript, Theorem 1] -/
theorem noncanonical_exclusion_of_realized_geometry
    (tv : CharacterIntervalInput)
    (ct : ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → QSeries.ConstantTermInputs p)
    (progression : ∀ (p : ℕ), p.Prime → ∀ hp5 : 5 ≤ p, ProgressionInputs p hp5)
    (geometry : RealizedCharacterObstructionInputFamily)
    (p b : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hb : b < p)
    (hspt : ∀ n : ℕ, p ∣ spt (p * n + b)) :
    ((24 * b : ℕ) : ZMod p) = 1 := by
  exact conditional_noncanonical_exclusion tv ct progression
    geometry.toCharacterObstructionInputFamily p b hp hp5 hb hspt

/-- Conditional classification for every prime, with the general
Hadamard bound derived from trace realization. Canonical necessity and
the three Andrews congruences remain explicit literature inputs.
[rolenManuscript, Corollary 1] -/
theorem simple_congruence_classification_of_realized_geometry
    (tv : CharacterIntervalInput)
    (ct : ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → QSeries.ConstantTermInputs p)
    (progression : ∀ (p : ℕ), p.Prime → ∀ hp5 : 5 ≤ p, ProgressionInputs p hp5)
    (geometry : RealizedCharacterObstructionInputFamily)
    (canonical : CanonicalInputs)
    (p b : ℕ) (hp : p.Prime) (hb : b < p) :
    (∀ n : ℕ, p ∣ spt (p * n + b)) ↔
      (p = 5 ∧ b = 4) ∨ (p = 7 ∧ b = 5) ∨ (p = 13 ∧ b = 6) := by
  exact conditional_simple_congruence_classification tv ct progression
    geometry.toCharacterObstructionInputFamily canonical p b hp hb


/-- The character obstruction with constant terms proved from analytic Hecke
rows and the trace bound proved from positive realization. The lift and CM
reduction use the same descended models. [rolenManuscript, Proposition 4.1] -/
theorem character_obstruction_of_analytic_inputs
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (sign : ℤ) (hsign : sign = 1 ∨ sign = -1)
    (d : ℕ) [Fact (-(d : ℤ) < 0)]
    (hd : 0 < d) (hsq : Squarefree d) (hmod : d % 24 = 23)
    (hr : legendreSym p (-(d : ℤ)) = sign)
    (hsep : (d + 1) ^ 2 < 24 * p)
    (hclass : 8 * formClassNumber (-(d : ℤ)) < p + 1)
    (hecke : QSeries.AnalyticHeckePairingInputs)
    (geometry : RealizedCharacterObstructionGeometry p d) :
    ¬∀ j : ℕ, legendreSym p (1 - 24 * (j : ℤ)) = sign →
      ((spt j : ℤ) : ZMod p) = 0 := by
  let : CommRing geometry.Form := geometry.formRing
  let : Algebra (ZMod p) geometry.Form := geometry.formAlgebra
  exact conditional_character_obstruction p hp sign hsign d hd hsq hmod hr
    hsep hclass (hecke.toConstantTermInputs p hp)
    geometry.cm.toCMDescentInput geometry.lift

end SptClassification
