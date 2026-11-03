/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.CMReductionProducts
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# A common integral ring for the oriented CM values

The monic equations for the actual eta values put them in the integral
closure of `ℤ[1/6]` in `ℂ`. This construction uses the coefficient descent
of [rolen2026canonical, Lemma 4.1]; it does not assume a common reduced
elliptic curve or an action on that curve.
-/

public section

namespace SptClassification
namespace CMIntegralValues

noncomputable instance coefficientAlgebra : Algebra (Localization.Away (6 : ℤ)) ℂ :=
  cmCoefficientComplexMap.toAlgebra

theorem coefficientAlgebra_map :
    algebraMap (Localization.Away (6 : ℤ)) ℂ = cmCoefficientComplexMap := (rfl)

/-- All complex numbers integral over the coefficient ring, independently of
the discriminant and of the reduction prime. -/
abbrev Ring : Type := integralClosure (Localization.Away (6 : ℤ)) ℂ

noncomputable instance : CommRing Ring := inferInstanceAs
  (CommRing (integralClosure (Localization.Away (6 : ℤ)) ℂ))

/-- The inclusion into the complex fiber. -/
noncomputable def complexEmbedding : Ring →+* ℂ :=
  (integralClosure (Localization.Away (6 : ℤ)) ℂ).val.toRingHom

theorem complexEmbedding_apply (x : Ring) : complexEmbedding x = (x : ℂ) := (rfl)

theorem complexEmbedding_injective : Function.Injective complexEmbedding :=
  Subtype.val_injective

theorem complexEmbedding_comp :
    complexEmbedding.comp (algebraMap (Localization.Away (6 : ℤ)) Ring) =
      cmCoefficientComplexMap := (rfl)

/-- An actual first-pair eta value belongs to the common integral ring. -/
theorem integral_first {d : ℕ} [Fact (-(d : ℤ) < 0)]
    (models : IntegralCMClassPolynomials d) {r : ZMod 12}
    (C : PrimitiveCMClass (-(d : ℤ)) r) (hr : r = 1 ∨ r = 11) :
    IsIntegral (Localization.Away (6 : ℤ)) C.val.etaValue := by
  refine ⟨models.modelA, models.monicA, ?_⟩
  simpa only [coefficientAlgebra_map, Polynomial.eval_map] using models.etaValue_rootA C hr

/-- The same integral ring contains the actual second-pair eta values. -/
theorem integral_second {d : ℕ} [Fact (-(d : ℤ) < 0)]
    (models : IntegralCMClassPolynomials d) {r : ZMod 12}
    (C : PrimitiveCMClass (-(d : ℤ)) r) (hr : r = 5 ∨ r = 7) :
    IsIntegral (Localization.Away (6 : ℤ)) C.val.etaValue := by
  refine ⟨models.modelB, models.monicB, ?_⟩
  simpa only [coefficientAlgebra_map, Polynomial.eval_map] using models.etaValue_rootB C hr

/-- The integral lift retains the actual eta value, rather than a selected
abstract root of its polynomial. -/
noncomputable def first {d : ℕ} [Fact (-(d : ℤ) < 0)]
    (models : IntegralCMClassPolynomials d) {r : ZMod 12}
    (C : PrimitiveCMClass (-(d : ℤ)) r) (hr : r = 1 ∨ r = 11) : Ring :=
  ⟨C.val.etaValue, integral_first models C hr⟩

/-- The second-pair lift into the same ring. -/
noncomputable def second {d : ℕ} [Fact (-(d : ℤ) < 0)]
    (models : IntegralCMClassPolynomials d) {r : ZMod 12}
    (C : PrimitiveCMClass (-(d : ℤ)) r) (hr : r = 5 ∨ r = 7) : Ring :=
  ⟨C.val.etaValue, integral_second models C hr⟩

theorem complexEmbedding_first {d : ℕ} [Fact (-(d : ℤ) < 0)]
    (models : IntegralCMClassPolynomials d) {r : ZMod 12}
    (C : PrimitiveCMClass (-(d : ℤ)) r) (hr : r = 1 ∨ r = 11) :
    complexEmbedding (first models C hr) = C.val.etaValue := (rfl)

theorem complexEmbedding_second {d : ℕ} [Fact (-(d : ℤ) < 0)]
    (models : IntegralCMClassPolynomials d) {r : ZMod 12}
    (C : PrimitiveCMClass (-(d : ℤ)) r) (hr : r = 5 ∨ r = 7) :
    complexEmbedding (second models C hr) = C.val.etaValue := (rfl)

/-- The coefficient ring embeds faithfully in the complex numbers. -/
theorem coefficientMap_injective : Function.Injective cmCoefficientComplexMap := by
  apply IsLocalization.injective_of_map_algebraMap_zero
    (M := Submonoid.powers (6 : ℤ)) (Localization.Away (6 : ℤ)) cmCoefficientComplexMap
  intro n hn
  have hn' : (n : ℂ) = 0 := by simpa using hn
  have hn0 : n = 0 := Int.cast_eq_zero.mp hn'
  simp [hn0]

/-- Lying-over selects a prime of the common integral ring over the given
reduction of the coefficient ring. -/
theorem exists_prime_over (p : ℕ) [Fact p.Prime] (hp6 : ¬p ∣ 6) :
    ∃ Q : Ideal Ring, Q.IsPrime ∧
      Q.under (Localization.Away (6 : ℤ)) = RingHom.ker (cmCoefficientReduction p hp6) := by
  have hinj : Function.Injective (algebraMap (Localization.Away (6 : ℤ)) Ring) := by
    intro x y h
    apply coefficientMap_injective
    have hh := congrArg complexEmbedding h
    simpa only [← RingHom.comp_apply, complexEmbedding_comp] using hh
  haveI : (RingHom.ker (cmCoefficientReduction p hp6)).IsPrime :=
    RingHom.ker_isPrime (cmCoefficientReduction p hp6)
  apply Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
    (S := Ring) (RingHom.ker (cmCoefficientReduction p hp6))
  rw [RingHom.injective_iff_ker_eq_bot] at hinj
  simp [hinj]

/-- Every ring map out of the common integral ring in characteristic `p`
restricts to the prescribed reduction away from six. -/
theorem reduction_comp (p : ℕ) [Fact p.Prime] (hp6 : ¬p ∣ 6)
    {K : Type*} [CommRing K] [Algebra (ZMod p) K]
    (f : Ring →+* K) :
    f.comp (algebraMap (Localization.Away (6 : ℤ)) Ring) =
      (algebraMap (ZMod p) K).comp (cmCoefficientReduction p hp6) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (6 : ℤ))
  ext n
  simp

/-- A common reduction exists for all the integral CM values at any prime
away from six. Lying-over and algebraic-closure lifting are ordinary ring
constructions, independent of the geometry of CM reduction. -/
theorem exists_reduction (p : ℕ) [Fact p.Prime] (hp6 : ¬p ∣ 6) :
    Nonempty (Ring →+* AlgebraicClosure (ZMod p)) := by
  obtain ⟨Q, hprime, hQ⟩ := exists_prime_over p hp6
  letI : Q.IsPrime := hprime
  have hpQ : (p : Ring) ∈ Q := by
    have hpA : (p : Localization.Away (6 : ℤ)) ∈ Q.under (Localization.Away (6 : ℤ)) := by
      rw [hQ]
      change cmCoefficientReduction p hp6 (p : Localization.Away (6 : ℤ)) = 0
      simp
    simpa using hpA
  letI : CharP (Ring ⧸ Q) p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr (by
    rw [← map_natCast (Ideal.Quotient.mk Q) p]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hpQ)
  letI : Algebra (ZMod p) (Ring ⧸ Q) := (ZMod.castHom (dvd_refl p) (Ring ⧸ Q)).toAlgebra
  haveI : Algebra.IsIntegral (ZMod p) (Ring ⧸ Q) := by
    constructor
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact IsIntegral.map_of_comp_eq (cmCoefficientReduction p hp6) (Ideal.Quotient.mk Q)
      (reduction_comp p hp6 (Ideal.Quotient.mk Q)).symm
      (integralClosure.isIntegral y)
  exact ⟨(IsAlgClosed.lift (R := ZMod p) (S := Ring ⧸ Q)
    (M := AlgebraicClosure (ZMod p))).toRingHom.comp (Ideal.Quotient.mk Q)⟩

/-- Fix one common reduction for all discriminants at the given prime. -/
noncomputable def reduction (p : ℕ) [Fact p.Prime] (hp6 : ¬p ∣ 6) :
    Ring →+* AlgebraicClosure (ZMod p) :=
  Classical.choice (exists_reduction p hp6)

/-- A common reduced polynomial root selects actual CM classes from both
orientation pairs, using a single reduction of their integral eta values.
No common elliptic curve or specialization of CM actions is assumed here. -/
theorem common_root_classes (d p : ℕ) [Fact (-(d : ℤ) < 0)] [Fact p.Prime]
    (hp6 : ¬p ∣ 6) (models : IntegralCMClassPolynomials d)
    (x : AlgebraicClosure (ZMod p))
    (ha : (Polynomial.aeval x)
      (models.modelA.map (cmCoefficientReduction p hp6)) = 0)
    (hb : (Polynomial.aeval x)
      (models.modelB.map (cmCoefficientReduction p hp6)) = 0) :
    ((∃ C : PrimitiveCMClass (-(d : ℤ)) 1,
        reduction p hp6 (first models C (Or.inl rfl)) = x) ∨
      (∃ C : PrimitiveCMClass (-(d : ℤ)) 11,
        reduction p hp6 (first models C (Or.inr rfl)) = x)) ∧
    ((∃ C : PrimitiveCMClass (-(d : ℤ)) 5,
        reduction p hp6 (second models C (Or.inl rfl)) = x) ∨
      (∃ C : PrimitiveCMClass (-(d : ℤ)) 7,
        reduction p hp6 (second models C (Or.inr rfl)) = x)) := by
  exact integralCMClassPolynomials_common_aeval_root_of_complex_lifts d p hp6 models
    (algebraMap (Localization.Away (6 : ℤ)) Ring) complexEmbedding
    complexEmbedding_injective complexEmbedding_comp (reduction p hp6)
    (reduction_comp p hp6 (reduction p hp6))
    (fun C => first models C (Or.inl rfl)) (fun C => first models C (Or.inr rfl))
    (fun C => second models C (Or.inl rfl)) (fun C => second models C (Or.inr rfl))
    (fun C => complexEmbedding_first models C (Or.inl rfl))
    (fun C => complexEmbedding_first models C (Or.inr rfl))
    (fun C => complexEmbedding_second models C (Or.inl rfl))
    (fun C => complexEmbedding_second models C (Or.inr rfl)) x ha hb

end CMIntegralValues
end SptClassification
