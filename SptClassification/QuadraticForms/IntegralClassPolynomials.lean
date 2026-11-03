/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.OrientationClasses
public import Mathlib.RingTheory.Localization.Away.Basic

/-! # Integral models of the oriented CM class polynomials

The complex products are already constructed. Their descent to `ℤ[1/6]`
is the integral class-polynomial assertion of [rolen2026canonical, Lemma 4.1].
Section 4 of that source uses the same primitive `Γ₀(6)` form classes,
orientations `1, 11` and `5, 7`, CM points, and eta quotient. These models
introduce no arbitrary roots or coefficient defaults, and their choice is
independent of a reduction prime.
-/

public section

namespace SptClassification

/-- The canonical complex specialization of `ℤ[1/6]`. -/
noncomputable def cmCoefficientComplexMap : Localization.Away (6 : ℤ) →+* ℂ :=
  IsLocalization.Away.lift (6 : ℤ) (g := Int.castRingHom ℂ) (by norm_num)

/-- Localized integral models of the actual products over orientations `1,11`
and `5,7`, respectively. This records coefficient descent, not separation. -/
structure IntegralCMClassPolynomials (d : ℕ) [Fact (-(d : ℤ) < 0)] where
  modelA : Polynomial (Localization.Away (6 : ℤ))
  modelB : Polynomial (Localization.Away (6 : ℤ))
  monicA : modelA.Monic
  monicB : modelB.Monic
  complexA : modelA.map cmCoefficientComplexMap = cmClassPolynomialA (-(d : ℤ))
  complexB : modelB.map cmCoefficientComplexMap = cmClassPolynomialB (-(d : ℤ))

/-- The integral first product has the degree of the actual first pair of
oriented primitive CM class spaces. -/
theorem IntegralCMClassPolynomials.degreeA {d : ℕ} [Fact (-(d : ℤ) < 0)]
    (models : IntegralCMClassPolynomials d) (hmod : d % 24 = 23) :
    models.modelA.natDegree = 2 * formClassNumber (-(d : ℤ)) := by
  have hD : (-(d : ℤ)) % 24 = 1 := by omega
  calc
    models.modelA.natDegree =
        (models.modelA.map cmCoefficientComplexMap).natDegree :=
      (models.monicA.natDegree_map cmCoefficientComplexMap).symm
    _ = 2 * formClassNumber (-(d : ℤ)) := by
      rw [models.complexA, cmClassPolynomialA_natDegree _ hD]

/-- The integral second product has the same exact degree. -/
theorem IntegralCMClassPolynomials.degreeB {d : ℕ} [Fact (-(d : ℤ) < 0)]
    (models : IntegralCMClassPolynomials d) (hmod : d % 24 = 23) :
    models.modelB.natDegree = 2 * formClassNumber (-(d : ℤ)) := by
  have hD : (-(d : ℤ)) % 24 = 1 := by omega
  calc
    models.modelB.natDegree =
        (models.modelB.map cmCoefficientComplexMap).natDegree :=
      (models.monicB.natDegree_map cmCoefficientComplexMap).symm
    _ = 2 * formClassNumber (-(d : ℤ)) := by
      rw [models.complexB, cmClassPolynomialB_natDegree _ hD]

/-- The monic-descent assertion of [rolen2026canonical, Lemma 4.1, pp. 5–6].
The source's `n` is `d` here: `n > 0` is squarefree and `n ≡ 23 (mod 24)`, so
the discriminant is `-d`. Its products (4.2) and (4.3) use the primitive
`Γ₀(6)` classes with orientations `1,11` and `5,7`, the same CM points and
the eta quotient (4.1). The source gives monic coefficients in `ℤ[1/6]`;
`complexA` and `complexB` express equality with those actual complex products.
Only this exact literature assertion is admitted; the coordinate and reduction
claims in that lemma are separate. -/
theorem integralCMClassPolynomials_literature (d : ℕ) [Fact (-(d : ℤ) < 0)]
    (hd : 0 < d) (hsq : Squarefree d) (hmod : d % 24 = 23) :
    Nonempty (IntegralCMClassPolynomials d) := by
  sorry

/-- The actual oriented CM products descend to monic polynomials over
`ℤ[1/6]`, using the precisely matching monic-descent assertion of
[rolen2026canonical, Lemma 4.1, pp. 5–6]. -/
theorem integralCMClassPolynomials_nonempty (d : ℕ) [Fact (-(d : ℤ) < 0)]
    (hd : 0 < d) (hsq : Squarefree d) (hmod : d % 24 = 23) :
    Nonempty (IntegralCMClassPolynomials d) :=
  integralCMClassPolynomials_literature d hd hsq hmod

/-- The localized integral models furnished by CM coefficient descent. -/
noncomputable def integralCMClassPolynomials (d : ℕ) [Fact (-(d : ℤ) < 0)]
    (hd : 0 < d) (hsq : Squarefree d) (hmod : d % 24 = 23) :
    IntegralCMClassPolynomials d :=
  Classical.choice (integralCMClassPolynomials_nonempty d hd hsq hmod)

/-- The canonical specialization of `ℤ[1/6]` to a residue field away from six. -/
noncomputable def cmCoefficientReduction (p : ℕ) [Fact p.Prime] (hp6 : ¬p ∣ 6) :
    Localization.Away (6 : ℤ) →+* ZMod p :=
  IsLocalization.Away.lift (6 : ℤ) (g := Int.castRingHom (ZMod p))
    (by
      apply isUnit_iff_ne_zero.mpr
      simpa using (show (6 : ZMod p) ≠ 0 from
        fun hz => hp6 ((ZMod.natCast_eq_zero_iff 6 p).mp hz)))

/-- Reduction away from six preserves the exact degree of the first monic
oriented CM class polynomial. -/
theorem IntegralCMClassPolynomials.reducedDegreeA {d p : ℕ}
    [Fact (-(d : ℤ) < 0)] [Fact p.Prime]
    (models : IntegralCMClassPolynomials d) (hmod : d % 24 = 23)
    (hp6 : ¬p ∣ 6) :
    (models.modelA.map (cmCoefficientReduction p hp6)).natDegree =
      2 * formClassNumber (-(d : ℤ)) := by
  calc
    (models.modelA.map (cmCoefficientReduction p hp6)).natDegree =
        models.modelA.natDegree := models.monicA.natDegree_map _
    _ = 2 * formClassNumber (-(d : ℤ)) := models.degreeA hmod

/-- Reduction away from six also preserves the second degree. -/
theorem IntegralCMClassPolynomials.reducedDegreeB {d p : ℕ}
    [Fact (-(d : ℤ) < 0)] [Fact p.Prime]
    (models : IntegralCMClassPolynomials d) (hmod : d % 24 = 23)
    (hp6 : ¬p ∣ 6) :
    (models.modelB.map (cmCoefficientReduction p hp6)).natDegree =
      2 * formClassNumber (-(d : ℤ)) := by
  calc
    (models.modelB.map (cmCoefficientReduction p hp6)).natDegree =
        models.modelB.natDegree := models.monicB.natDegree_map _
    _ = 2 * formClassNumber (-(d : ℤ)) := models.degreeB hmod

end SptClassification
