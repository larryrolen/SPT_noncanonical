/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.ConditionalSeparationGeometry
public import SptClassification.QuadraticForms.OrientationClasses
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Conditional separation of the actual CM class polynomials

The input records integral models over `ℤ[1/6]` whose complex specializations
are the actual oriented eta-quotient class polynomials. A common geometric root
of their reductions yields the level-six CM actions represented by
`CommonRootAction`. The resulting coprimality is the separation lemma of
[rolenManuscript, Section 4], conditional on descent and Eichler geometry.
The companion argument is [rolen2026canonical, Lemma 5.2].
-/

public section

namespace SptClassification
namespace ConditionalCM

/-- The manuscript's integral models of its two actual complex class
polynomials, together with the geometric meaning of a common reduced root.
The coefficient maps are specializations of the same localized integral ring. -/
structure CMDescentInput (d p : ℕ) [Fact (-(d : ℤ) < 0)] [Fact p.Prime] where
  modelA : Polynomial (Localization.Away (6 : ℤ))
  modelB : Polynomial (Localization.Away (6 : ℤ))
  modelA_monic : modelA.Monic
  modelB_monic : modelB.Monic
  complexSpecialization : Localization.Away (6 : ℤ) →+* ℂ
  complexA : modelA.map complexSpecialization = cmClassPolynomialA (-(d : ℤ))
  complexB : modelB.map complexSpecialization = cmClassPolynomialB (-(d : ℤ))
  reduction : Localization.Away (6 : ℤ) →+* ZMod p
  commonRoot : ∀ x : AlgebraicClosure (ZMod p),
    (Polynomial.aeval x) (modelA.map reduction) = 0 →
    (Polynomial.aeval x) (modelB.map reduction) = 0 →
    CommonRootAction d p

/-- The model for the first orientation set has the manuscript's degree
`2 h(-d)` because its complex specialization is the actual CM polynomial. -/
theorem CMDescentInput.modelA_degree {d p : ℕ}
    [Fact (-(d : ℤ) < 0)] [Fact p.Prime] (I : CMDescentInput d p)
    (hmod : d % 24 = 23) :
    I.modelA.natDegree = 2 * formClassNumber (-(d : ℤ)) := by
  have hD : (-(d : ℤ)) % 24 = 1 := by omega
  calc
    I.modelA.natDegree = (I.modelA.map I.complexSpecialization).natDegree :=
      (I.modelA_monic.natDegree_map I.complexSpecialization).symm
    _ = 2 * formClassNumber (-(d : ℤ)) := by
      rw [I.complexA, cmClassPolynomialA_natDegree _ hD]

/-- The model for the second orientation set has the same exact degree. -/
theorem CMDescentInput.modelB_degree {d p : ℕ}
    [Fact (-(d : ℤ) < 0)] [Fact p.Prime] (I : CMDescentInput d p)
    (hmod : d % 24 = 23) :
    I.modelB.natDegree = 2 * formClassNumber (-(d : ℤ)) := by
  have hD : (-(d : ℤ)) % 24 = 1 := by omega
  calc
    I.modelB.natDegree = (I.modelB.map I.complexSpecialization).natDegree :=
      (I.modelB_monic.natDegree_map I.complexSpecialization).symm
    _ = 2 * formClassNumber (-(d : ℤ)) := by
      rw [I.complexB, cmClassPolynomialB_natDegree _ hD]

/-- Reduction preserves the monic first oriented class polynomial. -/
theorem CMDescentInput.reducedA_monic {d p : ℕ}
    [Fact (-(d : ℤ) < 0)] [Fact p.Prime] (I : CMDescentInput d p) :
    (I.modelA.map I.reduction).Monic :=
  I.modelA_monic.map I.reduction

/-- Reduction preserves the monic second oriented class polynomial. -/
theorem CMDescentInput.reducedB_monic {d p : ℕ}
    [Fact (-(d : ℤ) < 0)] [Fact p.Prime] (I : CMDescentInput d p) :
    (I.modelB.map I.reduction).Monic :=
  I.modelB_monic.map I.reduction

/-- The first reduced polynomial retains its exact `2 h(-d)` degree. -/
theorem CMDescentInput.reducedA_degree {d p : ℕ}
    [Fact (-(d : ℤ) < 0)] [Fact p.Prime] (I : CMDescentInput d p)
    (hmod : d % 24 = 23) :
    (I.modelA.map I.reduction).natDegree =
      2 * formClassNumber (-(d : ℤ)) := by
  calc
    (I.modelA.map I.reduction).natDegree = I.modelA.natDegree :=
      I.modelA_monic.natDegree_map I.reduction
    _ = 2 * formClassNumber (-(d : ℤ)) := I.modelA_degree hmod

/-- The second reduced polynomial retains its exact `2 h(-d)` degree. -/
theorem CMDescentInput.reducedB_degree {d p : ℕ}
    [Fact (-(d : ℤ) < 0)] [Fact p.Prime] (I : CMDescentInput d p)
    (hmod : d % 24 = 23) :
    (I.modelB.map I.reduction).natDegree =
      2 * formClassNumber (-(d : ℤ)) := by
  calc
    (I.modelB.map I.reduction).natDegree = I.modelB.natDegree :=
      I.modelB_monic.natDegree_map I.reduction
    _ = 2 * formClassNumber (-(d : ℤ)) := I.modelB_degree hmod

/-- Conditional separation for the reductions of the actual oriented CM
polynomials. The reduction geometry and general Eichler lower bound are
explicit inputs; the lattice contradiction is proved above. -/
theorem conditional_cm_separation (d p : ℕ)
    [Fact (-(d : ℤ) < 0)] [Fact p.Prime]
    (hd : 0 < d) (_hsq : Squarefree d) (_hmod : d % 24 = 23)
    (_hp : 5 ≤ p) (_hcop : ¬p ∣ 6 * d)
    (hbound : (d + 1) ^ 2 < 24 * p)
    (I : CMDescentInput d p) :
    IsCoprime (I.modelA.map I.reduction) (I.modelB.map I.reduction) := by
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
    (ZMod p) (AlgebraicClosure (ZMod p))
    (I.modelA.map I.reduction) (I.modelB.map I.reduction)).2
  intro x
  by_contra h
  push Not at h
  obtain ⟨ha, hb⟩ := h
  have hreverse := (I.commonRoot x ha hb).bound hd
  have hstrict : ((d : ℝ) + 1) ^ 2 < 24 * (p : ℝ) := by
    exact_mod_cast hbound
  linarith

end ConditionalCM
end SptClassification
