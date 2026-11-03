/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.LevelSixModularSections
public import Mathlib.FieldTheory.RatFunc.Basic
import all SptClassification.ModularForms.LevelSixModularSections
import Mathlib.Tactic.Ring

/-!
# Rational sections in the level-six invariant frame

The coefficient field is `K(t)`; the outer variable retains the power of the
actual invariant differential. No global holomorphy or cusp integrality is
asserted. The Serre connection extends by the ordinary quotient rule.
-/

public noncomputable section

namespace SptClassification.LevelSixRationalSections

open Polynomial
variable {K : Type*} [Field K]

abbrev SectionRing (K : Type*) [Field K] := Polynomial (RatFunc K)

/-- A rational coefficient times the invariant differential to weight `k`. -/
def sectionOf (k : ℕ) (f : RatFunc K) : SectionRing K := monomial k f

/-- Homogeneity retains the weight independently of a cusp expansion. -/
def IsWeight (k : ℕ) (F : SectionRing K) : Prop := ∃ f, F = sectionOf k f

@[simp] theorem coeff_sectionOf (k : ℕ) (f : RatFunc K) :
    (sectionOf k f).coeff k = f := by simp [sectionOf]

theorem sectionOf_injective (k : ℕ) : Function.Injective (sectionOf (K := K) k) := by
  intro f g h
  simpa using congrArg (fun F : SectionRing K => F.coeff k) h

theorem sectionOf_mul (k l : ℕ) (f g : RatFunc K) :
    sectionOf (k + l) (f * g) = sectionOf k f * sectionOf l g := by
  simp [sectionOf, monomial_mul_monomial]

/-- Inclusion of the existing polynomial section model. -/
def ofPolynomial : LevelSixModularSections.SectionRing K →+* SectionRing K :=
  Polynomial.mapRingHom (algebraMap K[X] (RatFunc K))

@[simp] theorem ofPolynomial_sectionOf (k : ℕ) (f : K[X]) :
    ofPolynomial (LevelSixModularSections.sectionOf k f) =
      sectionOf k (algebraMap K[X] (RatFunc K) f) := by
  simp [ofPolynomial, LevelSixModularSections.sectionOf, sectionOf]

/-- Extension of the connection by the quotient rule, using the canonical
nonzero denominator. The denominator is a weight-zero function. -/
def serre (k : ℕ) (f : RatFunc K) : RatFunc K :=
  algebraMap K[X] (RatFunc K) (LevelSixModularSections.serre k f.num) /
      algebraMap K[X] (RatFunc K) f.denom -
    algebraMap K[X] (RatFunc K)
      (f.num * LevelSixModularSections.serre 0 f.denom) /
        (algebraMap K[X] (RatFunc K) f.denom) ^ 2

@[simp] theorem serre_polynomial (k : ℕ) (f : K[X]) :
    serre k (algebraMap K[X] (RatFunc K) f) =
      algebraMap K[X] (RatFunc K) (LevelSixModularSections.serre k f) := by
  simp [serre, RatFunc.num_algebraMap, RatFunc.denom_algebraMap,
    LevelSixModularSections.serre]

/-- The weight-raising connection on a homogeneous component. -/
def serreSection (k : ℕ) (F : SectionRing K) : SectionRing K :=
  sectionOf (k + 2) (serre k (F.coeff k))

@[simp] theorem serreSection_sectionOf (k : ℕ) (f : RatFunc K) :
    serreSection k (sectionOf k f) = sectionOf (k + 2) (serre k f) := by
  simp [serreSection]

theorem serreSection_isWeight (k : ℕ) (F : SectionRing K) :
    IsWeight (k + 2) (serreSection k F) := ⟨_, rfl⟩

theorem serreSection_ofPolynomial (k : ℕ) (F : LevelSixModularSections.SectionRing K)
    (hF : LevelSixModularSections.IsWeight k F) :
    serreSection k (ofPolynomial F) =
      ofPolynomial (LevelSixModularSections.serreSection k F) := by
  obtain ⟨f, rfl⟩ := hF
  simp

end SptClassification.LevelSixRationalSections
