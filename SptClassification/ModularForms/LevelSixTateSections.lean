/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.LevelSixHasseGeometry
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.NumberTheory.Divisors

/-!
# Tate expansions of framed level-six sections

An expansion is specified by an actual change of Weierstrass coordinates to
the standard Tate equation. Both the modular coordinate and the differential
frame are retained. The target may be a Laurent-series algebra; polynomial
coefficients in the invariant frame need not have holomorphic expansions.
No existence of a particular cusp chart, or integral pole clearing, is assumed
by the construction. Those are separate realization questions.
-/

public noncomputable section

namespace SptClassification.LevelSixTateSections

open Polynomial WeierstrassHasse LevelSixModularSections LevelSixHasseGeometry

variable (K : Type*) [Field K]

/-- The positive Lambert series `Σ σ_k(n) q^n`. -/
def divisorSeries (k : ℕ) : PowerSeries K :=
  PowerSeries.mk (fun n => ∑ d ∈ n.divisors, (d : K) ^ k)

/-- The standard Tate equation with differential `dx/(2y+x)`.
[katz1973], Appendix A1.2.3, p. 160 (equation), and A1.2, p. 161
(canonical differential); see also Appendix A1.4, Remark 2.
The formula is used only away from characteristics two and three. -/
def tateCurve : WeierstrassCurve (PowerSeries K) where
  a₁ := 1
  a₂ := 0
  a₃ := 0
  a₄ := -5 * divisorSeries K 3
  a₆ := -PowerSeries.C (12 : K)⁻¹ *
    (5 * divisorSeries K 3 + 7 * divisorSeries K 5)

/-- The actual Hasse coefficient of the canonical Tate equation is one.
[katz1973], §2.0, pp. 97–98, and Appendix A1.4, Remark 2, p. 172.
This is a generic Tate theorem, independent of the level-six family. -/
theorem hasse_tate_literature (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 3 < p) :
    hasse p (tateCurve K) = 1 := by
  sorry

variable {K} {S : Type*} [CommRing S]

/-- An actual framed Tate realization in a coefficient algebra. The coordinate
change, rather than an asserted Hasse value, fixes the differential frame. -/
structure TateRealization where
  base : PowerSeries K →+* S
  parameter : S
  change : WeierstrassCurve.VariableChange S
  equation : change • LevelSixWeierstrass.curve parameter = (tateCurve K).map base

/-- Expand both the coordinate and the differential generator. -/
def TateRealization.expansion (T : TateRealization (K := K) (S := S)) :
    SectionRing K →+* S :=
  framedEval (T.base.comp PowerSeries.C) T.parameter (↑T.change.u⁻¹ : S)

/-- The Hasse section constructed from the actual level-six equation has
normalized expansion one in every actual Tate realization. -/
theorem TateRealization.expansion_hasse (p : ℕ) [Fact p.Prime]
    [CharP K p] [CharP S p] (hp : 3 < p) (T : TateRealization (K := K) (S := S)) :
    T.expansion (hasseSection p) = 1 := by
  rw [TateRealization.expansion, framedEval_hasseSection, mul_comm,
    ← hasse_variableChange_literature p hp, T.equation, ← map_hasse,
    hasse_tate_literature K p hp, map_one]

/-- Homogeneous expansion evaluates the weight as a power of the frame. -/
theorem TateRealization.expansion_sectionOf
    (T : TateRealization (K := K) (S := S)) (k : ℕ) (f : K[X]) :
    T.expansion (sectionOf k f) =
      f.eval₂ (T.base.comp PowerSeries.C) T.parameter * (↑T.change.u⁻¹ : S) ^ k := by
  rw [TateRealization.expansion, framedEval_sectionOf]

end SptClassification.LevelSixTateSections
