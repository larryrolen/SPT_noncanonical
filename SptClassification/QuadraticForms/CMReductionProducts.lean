/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.IntegralClassPolynomials
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Roots of specialized oriented CM products

The finite products defining the two CM class polynomials have factors indexed
by the actual primitive oriented classes. Once their integral factors are
realized in a common coefficient ring, a common root after reduction comes
from one class in each orientation pair. Constructing that coefficient ring
and identifying the reduced classes with one level-six pair are separate
geometric obligations in [rolen2026canonical, Lemma 4.1 and Proposition 5.3].
-/

public section

namespace SptClassification

/-- Over the complex fiber, the chosen integral first class polynomial has
exactly the factors indexed by its two actual primitive orientation spaces.
This is the comparison that an integral splitting construction must preserve
before reducing its factors. -/
theorem IntegralCMClassPolynomials.complexFactorsA
    (d : ℕ) [Fact (-(d : ℤ) < 0)] (models : IntegralCMClassPolynomials d) :
    letI : Fintype (PrimitiveCMClass (-(d : ℤ)) 1) :=
      Fintype.ofFinite (PrimitiveCMClass (-(d : ℤ)) 1)
    letI : Fintype (PrimitiveCMClass (-(d : ℤ)) 11) :=
      Fintype.ofFinite (PrimitiveCMClass (-(d : ℤ)) 11)
    models.modelA.map cmCoefficientComplexMap =
      (Finset.univ.prod (fun C : PrimitiveCMClass (-(d : ℤ)) 1 =>
        Polynomial.X - Polynomial.C C.val.etaValue)) *
      (Finset.univ.prod (fun C : PrimitiveCMClass (-(d : ℤ)) 11 =>
        Polynomial.X - Polynomial.C C.val.etaValue)) := by
  classical
  rw [models.complexA, cmClassPolynomialA_eq,
    complexCMPolynomial_eq_prod, complexCMPolynomial_eq_prod]

/-- The analogous exact factorization of the second integral model over its
complex fiber, with orientations five and seven. -/
theorem IntegralCMClassPolynomials.complexFactorsB
    (d : ℕ) [Fact (-(d : ℤ) < 0)] (models : IntegralCMClassPolynomials d) :
    letI : Fintype (PrimitiveCMClass (-(d : ℤ)) 5) :=
      Fintype.ofFinite (PrimitiveCMClass (-(d : ℤ)) 5)
    letI : Fintype (PrimitiveCMClass (-(d : ℤ)) 7) :=
      Fintype.ofFinite (PrimitiveCMClass (-(d : ℤ)) 7)
    models.modelB.map cmCoefficientComplexMap =
      (Finset.univ.prod (fun C : PrimitiveCMClass (-(d : ℤ)) 5 =>
        Polynomial.X - Polynomial.C C.val.etaValue)) *
      (Finset.univ.prod (fun C : PrimitiveCMClass (-(d : ℤ)) 7 =>
        Polynomial.X - Polynomial.C C.val.etaValue)) := by
  classical
  rw [models.complexB, cmClassPolynomialB_eq,
    complexCMPolynomial_eq_prod, complexCMPolynomial_eq_prod]

/-- Every eta value in the first pair of primitive orientations is a root of
the complex specialization of the integral first class polynomial. Together
with monicity, this is the integral equation used when adjoining the actual CM
values before reduction. -/
theorem IntegralCMClassPolynomials.etaValue_rootA
    {d : ℕ} [Fact (-(d : ℤ) < 0)]
    (models : IntegralCMClassPolynomials d) {r : ZMod 12}
    (C : PrimitiveCMClass (-(d : ℤ)) r) (hr : r = 1 ∨ r = 11) :
    (models.modelA.map cmCoefficientComplexMap).eval (C.val.etaValue) = 0 := by
  rcases hr with rfl | rfl
  · rw [models.complexA, cmClassPolynomialA_eq, Polynomial.eval_mul]
    exact mul_eq_zero.mpr (Or.inl (complexCMPolynomial_eval_etaValue C))
  · rw [models.complexA, cmClassPolynomialA_eq, Polynomial.eval_mul]
    exact mul_eq_zero.mpr (Or.inr (complexCMPolynomial_eval_etaValue C))

/-- Every eta value in the second primitive orientation pair satisfies the
second monic integral equation. -/
theorem IntegralCMClassPolynomials.etaValue_rootB
    {d : ℕ} [Fact (-(d : ℤ) < 0)]
    (models : IntegralCMClassPolynomials d) {r : ZMod 12}
    (C : PrimitiveCMClass (-(d : ℤ)) r) (hr : r = 5 ∨ r = 7) :
    (models.modelB.map cmCoefficientComplexMap).eval (C.val.etaValue) = 0 := by
  rcases hr with rfl | rfl
  · rw [models.complexB, cmClassPolynomialB_eq, Polynomial.eval_mul]
    exact mul_eq_zero.mpr (Or.inl (complexCMPolynomial_eval_etaValue C))
  · rw [models.complexB, cmClassPolynomialB_eq, Polynomial.eval_mul]
    exact mul_eq_zero.mpr (Or.inr (complexCMPolynomial_eval_etaValue C))

private theorem polynomial_eq_of_injective_map
    {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (hf : Function.Injective f)
    {P Q : Polynomial R} (h : P.map f = Q.map f) : P = Q := by
  apply Polynomial.ext
  intro n
  apply hf
  have hn := congrArg (fun T : Polynomial S => T.coeff n) h
  simpa only [Polynomial.coeff_map] using hn

/-- Lifts of the actual first-pair eta values through an injective complex
embedding force the integral first polynomial to split as their product.
Thus the factorization hypothesis in a common-root reduction follows from
the chosen lifts, rather than requiring a separate product identity. -/
theorem IntegralCMClassPolynomials.factorsA_of_complex_lifts
    (d : ℕ) [Fact (-(d : ℤ) < 0)]
    {R : Type*} [CommRing R] (models : IntegralCMClassPolynomials d)
    (lift : Localization.Away (6 : ℤ) →+* R) (embed : R →+* ℂ)
    (hinj : Function.Injective embed)
    (hcompat : embed.comp lift = cmCoefficientComplexMap)
    (a1 : PrimitiveCMClass (-(d : ℤ)) 1 → R)
    (a11 : PrimitiveCMClass (-(d : ℤ)) 11 → R)
    (ha1 : ∀ C, embed (a1 C) = C.val.etaValue)
    (ha11 : ∀ C, embed (a11 C) = C.val.etaValue) :
    letI : Fintype (PrimitiveCMClass (-(d : ℤ)) 1) :=
      Fintype.ofFinite (PrimitiveCMClass (-(d : ℤ)) 1)
    letI : Fintype (PrimitiveCMClass (-(d : ℤ)) 11) :=
      Fintype.ofFinite (PrimitiveCMClass (-(d : ℤ)) 11)
    models.modelA.map lift =
      (Finset.univ.prod (fun C : PrimitiveCMClass (-(d : ℤ)) 1 =>
        Polynomial.X - Polynomial.C (a1 C))) *
      (Finset.univ.prod (fun C : PrimitiveCMClass (-(d : ℤ)) 11 =>
        Polynomial.X - Polynomial.C (a11 C))) := by
  classical
  letI : Fintype (PrimitiveCMClass (-(d : ℤ)) 1) := Fintype.ofFinite _
  letI : Fintype (PrimitiveCMClass (-(d : ℤ)) 11) := Fintype.ofFinite _
  apply polynomial_eq_of_injective_map embed hinj
  calc
    (models.modelA.map lift).map embed =
        models.modelA.map cmCoefficientComplexMap := by
      rw [Polynomial.map_map, hcompat]
    _ = (Finset.univ.prod (fun C : PrimitiveCMClass (-(d : ℤ)) 1 =>
          Polynomial.X - Polynomial.C (C.val.etaValue))) *
        (Finset.univ.prod (fun C : PrimitiveCMClass (-(d : ℤ)) 11 =>
          Polynomial.X - Polynomial.C (C.val.etaValue))) :=
      IntegralCMClassPolynomials.complexFactorsA d models
    _ = ((Finset.univ.prod (fun C : PrimitiveCMClass (-(d : ℤ)) 1 =>
          Polynomial.X - Polynomial.C (a1 C))) *
        (Finset.univ.prod (fun C : PrimitiveCMClass (-(d : ℤ)) 11 =>
          Polynomial.X - Polynomial.C (a11 C)))).map embed := by
      simp only [Polynomial.map_mul, Polynomial.map_prod, Polynomial.map_sub,
        Polynomial.map_X, Polynomial.map_C, ha1, ha11]
  all_goals rfl

/-- The second-pair product similarly follows from lifts of its actual eta
values to the same coefficient ring. -/
theorem IntegralCMClassPolynomials.factorsB_of_complex_lifts
    (d : ℕ) [Fact (-(d : ℤ) < 0)]
    {R : Type*} [CommRing R] (models : IntegralCMClassPolynomials d)
    (lift : Localization.Away (6 : ℤ) →+* R) (embed : R →+* ℂ)
    (hinj : Function.Injective embed)
    (hcompat : embed.comp lift = cmCoefficientComplexMap)
    (b5 : PrimitiveCMClass (-(d : ℤ)) 5 → R)
    (b7 : PrimitiveCMClass (-(d : ℤ)) 7 → R)
    (hb5 : ∀ C, embed (b5 C) = C.val.etaValue)
    (hb7 : ∀ C, embed (b7 C) = C.val.etaValue) :
    letI : Fintype (PrimitiveCMClass (-(d : ℤ)) 5) :=
      Fintype.ofFinite (PrimitiveCMClass (-(d : ℤ)) 5)
    letI : Fintype (PrimitiveCMClass (-(d : ℤ)) 7) :=
      Fintype.ofFinite (PrimitiveCMClass (-(d : ℤ)) 7)
    models.modelB.map lift =
      (Finset.univ.prod (fun C : PrimitiveCMClass (-(d : ℤ)) 5 =>
        Polynomial.X - Polynomial.C (b5 C))) *
      (Finset.univ.prod (fun C : PrimitiveCMClass (-(d : ℤ)) 7 =>
        Polynomial.X - Polynomial.C (b7 C))) := by
  classical
  letI : Fintype (PrimitiveCMClass (-(d : ℤ)) 5) := Fintype.ofFinite _
  letI : Fintype (PrimitiveCMClass (-(d : ℤ)) 7) := Fintype.ofFinite _
  apply polynomial_eq_of_injective_map embed hinj
  calc
    (models.modelB.map lift).map embed =
        models.modelB.map cmCoefficientComplexMap := by
      rw [Polynomial.map_map, hcompat]
    _ = (Finset.univ.prod (fun C : PrimitiveCMClass (-(d : ℤ)) 5 =>
          Polynomial.X - Polynomial.C (C.val.etaValue))) *
        (Finset.univ.prod (fun C : PrimitiveCMClass (-(d : ℤ)) 7 =>
          Polynomial.X - Polynomial.C (C.val.etaValue))) :=
      IntegralCMClassPolynomials.complexFactorsB d models
    _ = ((Finset.univ.prod (fun C : PrimitiveCMClass (-(d : ℤ)) 5 =>
          Polynomial.X - Polynomial.C (b5 C))) *
        (Finset.univ.prod (fun C : PrimitiveCMClass (-(d : ℤ)) 7 =>
          Polynomial.X - Polynomial.C (b7 C)))).map embed := by
      simp only [Polynomial.map_mul, Polynomial.map_prod, Polynomial.map_sub,
        Polynomial.map_X, Polynomial.map_C, hb5, hb7]
  all_goals rfl

private theorem exists_factor_of_mapped_product_root
    {R K ι : Type*} [CommRing R] [Field K]
    (reduction : R →+* K) (s : Finset ι) (value : ι → R) (x : K)
    (h : ((∏ i ∈ s, (Polynomial.X - Polynomial.C (value i))).map reduction).eval x = 0) :
    ∃ i ∈ s, reduction (value i) = x := by
  rw [Polynomial.map_prod, Polynomial.eval_prod] at h
  obtain ⟨i, hi, hz⟩ := Finset.prod_eq_zero_iff.mp h
  refine ⟨i, hi, ?_⟩
  have hsub : x - reduction (value i) = 0 := by
    simpa only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] using hz
  exact (sub_eq_zero.mp hsub).symm

/-- If the actual integral class polynomials split into factors indexed by
their primitive oriented classes in one coefficient ring, a common reduced
root is represented by one class from each of the two orientation sets. This
is the finite-product deduction used before the geometric specialization of
the corresponding elliptic curves and cyclic subgroups. -/
theorem integralCMClassPolynomials_common_root_factors
    (d : ℕ) [Fact (-(d : ℤ) < 0)]
    {R K : Type*} [CommRing R] [Field K]
    [Fintype (PrimitiveCMClass (-(d : ℤ)) 1)]
    [Fintype (PrimitiveCMClass (-(d : ℤ)) 11)]
    [Fintype (PrimitiveCMClass (-(d : ℤ)) 5)]
    [Fintype (PrimitiveCMClass (-(d : ℤ)) 7)]
    (models : IntegralCMClassPolynomials d)
    (lift : Localization.Away (6 : ℤ) →+* R) (reduction : R →+* K)
    (a1 : PrimitiveCMClass (-(d : ℤ)) 1 → R)
    (a11 : PrimitiveCMClass (-(d : ℤ)) 11 → R)
    (b5 : PrimitiveCMClass (-(d : ℤ)) 5 → R)
    (b7 : PrimitiveCMClass (-(d : ℤ)) 7 → R)
    (hA : models.modelA.map lift =
      (∏ C : PrimitiveCMClass (-(d : ℤ)) 1,
        (Polynomial.X - Polynomial.C (a1 C))) *
      (∏ C : PrimitiveCMClass (-(d : ℤ)) 11,
        (Polynomial.X - Polynomial.C (a11 C))))
    (hB : models.modelB.map lift =
      (∏ C : PrimitiveCMClass (-(d : ℤ)) 5,
        (Polynomial.X - Polynomial.C (b5 C))) *
      (∏ C : PrimitiveCMClass (-(d : ℤ)) 7,
        (Polynomial.X - Polynomial.C (b7 C))))
    (x : K)
    (ha : ((models.modelA.map lift).map reduction).eval x = 0)
    (hb : ((models.modelB.map lift).map reduction).eval x = 0) :
    ((∃ C : PrimitiveCMClass (-(d : ℤ)) 1, reduction (a1 C) = x) ∨
      (∃ C : PrimitiveCMClass (-(d : ℤ)) 11, reduction (a11 C) = x)) ∧
    ((∃ C : PrimitiveCMClass (-(d : ℤ)) 5, reduction (b5 C) = x) ∨
      (∃ C : PrimitiveCMClass (-(d : ℤ)) 7, reduction (b7 C) = x)) := by
  constructor
  · rw [hA, Polynomial.map_mul, Polynomial.eval_mul] at ha
    rcases mul_eq_zero.mp ha with h1 | h11
    · left
      obtain ⟨C, _, hC⟩ := exists_factor_of_mapped_product_root reduction
        Finset.univ a1 x h1
      exact ⟨C, hC⟩
    · right
      obtain ⟨C, _, hC⟩ := exists_factor_of_mapped_product_root reduction
        Finset.univ a11 x h11
      exact ⟨C, hC⟩
  · rw [hB, Polynomial.map_mul, Polynomial.eval_mul] at hb
    rcases mul_eq_zero.mp hb with h5 | h7
    · left
      obtain ⟨C, _, hC⟩ := exists_factor_of_mapped_product_root reduction
        Finset.univ b5 x h5
      exact ⟨C, hC⟩
    · right
      obtain ⟨C, _, hC⟩ := exists_factor_of_mapped_product_root reduction
        Finset.univ b7 x h7
      exact ⟨C, hC⟩

/-- A common root in the algebraic closure selects one factor from each
orientation pair after an integral splitting has been reduced. The compatibility
equation identifies the splitting's residue map with the canonical reduction
of `ℤ[1/6]`; no geometric identification of the two selected CM curves is
used here. -/
theorem integralCMClassPolynomials_common_aeval_root_factors
    (d p : ℕ) [Fact (-(d : ℤ) < 0)] [Fact p.Prime]
    (hp6 : ¬p ∣ 6)
    {R : Type*} [CommRing R]
    [Fintype (PrimitiveCMClass (-(d : ℤ)) 1)]
    [Fintype (PrimitiveCMClass (-(d : ℤ)) 11)]
    [Fintype (PrimitiveCMClass (-(d : ℤ)) 5)]
    [Fintype (PrimitiveCMClass (-(d : ℤ)) 7)]
    (models : IntegralCMClassPolynomials d)
    (lift : Localization.Away (6 : ℤ) →+* R)
    (reduction : R →+* AlgebraicClosure (ZMod p))
    (hcompat : reduction.comp lift =
      (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).comp
        (cmCoefficientReduction p hp6))
    (a1 : PrimitiveCMClass (-(d : ℤ)) 1 → R)
    (a11 : PrimitiveCMClass (-(d : ℤ)) 11 → R)
    (b5 : PrimitiveCMClass (-(d : ℤ)) 5 → R)
    (b7 : PrimitiveCMClass (-(d : ℤ)) 7 → R)
    (hA : models.modelA.map lift =
      (∏ C : PrimitiveCMClass (-(d : ℤ)) 1,
        (Polynomial.X - Polynomial.C (a1 C))) *
      (∏ C : PrimitiveCMClass (-(d : ℤ)) 11,
        (Polynomial.X - Polynomial.C (a11 C))))
    (hB : models.modelB.map lift =
      (∏ C : PrimitiveCMClass (-(d : ℤ)) 5,
        (Polynomial.X - Polynomial.C (b5 C))) *
      (∏ C : PrimitiveCMClass (-(d : ℤ)) 7,
        (Polynomial.X - Polynomial.C (b7 C))))
    (x : AlgebraicClosure (ZMod p))
    (ha : (Polynomial.aeval x)
      (models.modelA.map (cmCoefficientReduction p hp6)) = 0)
    (hb : (Polynomial.aeval x)
      (models.modelB.map (cmCoefficientReduction p hp6)) = 0) :
    ((∃ C : PrimitiveCMClass (-(d : ℤ)) 1, reduction (a1 C) = x) ∨
      (∃ C : PrimitiveCMClass (-(d : ℤ)) 11, reduction (a11 C) = x)) ∧
    ((∃ C : PrimitiveCMClass (-(d : ℤ)) 5, reduction (b5 C) = x) ∨
      (∃ C : PrimitiveCMClass (-(d : ℤ)) 7, reduction (b7 C) = x)) := by
  have hAmap : ((models.modelA.map lift).map reduction) =
      (models.modelA.map (cmCoefficientReduction p hp6)).map
        (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) := by
    simpa only [Polynomial.map_map] using congrArg
      (fun f : Localization.Away (6 : ℤ) →+* AlgebraicClosure (ZMod p) =>
        models.modelA.map f) hcompat
  have hBmap : ((models.modelB.map lift).map reduction) =
      (models.modelB.map (cmCoefficientReduction p hp6)).map
        (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) := by
    simpa only [Polynomial.map_map] using congrArg
      (fun f : Localization.Away (6 : ℤ) →+* AlgebraicClosure (ZMod p) =>
        models.modelB.map f) hcompat
  have ha' : ((models.modelA.map lift).map reduction).eval x = 0 := by
    rw [hAmap, Polynomial.eval_map]
    exact ha
  have hb' : ((models.modelB.map lift).map reduction).eval x = 0 := by
    rw [hBmap, Polynomial.eval_map]
    exact hb
  exact integralCMClassPolynomials_common_root_factors d models lift reduction
    a1 a11 b5 b7 hA hB x ha' hb'

/-- An injective complex realization of the chosen coefficient ring and lifts
of the actual oriented eta values supply the factorization needed to select
both CM classes from a common reduced root. The identification of those two
classes with one reduced level-six pair remains a geometric step. -/
theorem integralCMClassPolynomials_common_aeval_root_of_complex_lifts
    (d p : ℕ) [Fact (-(d : ℤ) < 0)] [Fact p.Prime]
    (hp6 : ¬p ∣ 6)
    {R : Type*} [CommRing R]
    (models : IntegralCMClassPolynomials d)
    (lift : Localization.Away (6 : ℤ) →+* R)
    (embed : R →+* ℂ) (hinj : Function.Injective embed)
    (hcomplex : embed.comp lift = cmCoefficientComplexMap)
    (reduction : R →+* AlgebraicClosure (ZMod p))
    (hred : reduction.comp lift =
      (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).comp
        (cmCoefficientReduction p hp6))
    (a1 : PrimitiveCMClass (-(d : ℤ)) 1 → R)
    (a11 : PrimitiveCMClass (-(d : ℤ)) 11 → R)
    (b5 : PrimitiveCMClass (-(d : ℤ)) 5 → R)
    (b7 : PrimitiveCMClass (-(d : ℤ)) 7 → R)
    (ha1 : ∀ C, embed (a1 C) = C.val.etaValue)
    (ha11 : ∀ C, embed (a11 C) = C.val.etaValue)
    (hb5 : ∀ C, embed (b5 C) = C.val.etaValue)
    (hb7 : ∀ C, embed (b7 C) = C.val.etaValue)
    (x : AlgebraicClosure (ZMod p))
    (ha : (Polynomial.aeval x)
      (models.modelA.map (cmCoefficientReduction p hp6)) = 0)
    (hb : (Polynomial.aeval x)
      (models.modelB.map (cmCoefficientReduction p hp6)) = 0) :
    letI : Fintype (PrimitiveCMClass (-(d : ℤ)) 1) :=
      Fintype.ofFinite (PrimitiveCMClass (-(d : ℤ)) 1)
    letI : Fintype (PrimitiveCMClass (-(d : ℤ)) 11) :=
      Fintype.ofFinite (PrimitiveCMClass (-(d : ℤ)) 11)
    letI : Fintype (PrimitiveCMClass (-(d : ℤ)) 5) :=
      Fintype.ofFinite (PrimitiveCMClass (-(d : ℤ)) 5)
    letI : Fintype (PrimitiveCMClass (-(d : ℤ)) 7) :=
      Fintype.ofFinite (PrimitiveCMClass (-(d : ℤ)) 7)
    ((∃ C : PrimitiveCMClass (-(d : ℤ)) 1, reduction (a1 C) = x) ∨
      (∃ C : PrimitiveCMClass (-(d : ℤ)) 11, reduction (a11 C) = x)) ∧
    ((∃ C : PrimitiveCMClass (-(d : ℤ)) 5, reduction (b5 C) = x) ∨
      (∃ C : PrimitiveCMClass (-(d : ℤ)) 7, reduction (b7 C) = x)) := by
  classical
  letI : Fintype (PrimitiveCMClass (-(d : ℤ)) 1) := Fintype.ofFinite _
  letI : Fintype (PrimitiveCMClass (-(d : ℤ)) 11) := Fintype.ofFinite _
  letI : Fintype (PrimitiveCMClass (-(d : ℤ)) 5) := Fintype.ofFinite _
  letI : Fintype (PrimitiveCMClass (-(d : ℤ)) 7) := Fintype.ofFinite _
  exact integralCMClassPolynomials_common_aeval_root_factors d p hp6
    models lift reduction hred a1 a11 b5 b7
    (IntegralCMClassPolynomials.factorsA_of_complex_lifts
      d models lift embed hinj hcomplex a1 a11 ha1 ha11)
    (IntegralCMClassPolynomials.factorsB_of_complex_lifts
      d models lift embed hinj hcomplex b5 b7 hb5 hb7)
    x ha hb

end SptClassification
