/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.IntegralClassPolynomials
public import SptClassification.QuadraticForms.ConditionalSeparation
public import SptClassification.QuadraticForms.CMReductionAction
public import SptClassification.QuadraticForms.CMReductionProducts
public import SptClassification.QuadraticForms.EichlerTraceCovolume
public import SptClassification.QuadraticForms.CMIntegralSeparation
import Mathlib.Tactic.Ring

/-! # Separation of the two oriented CM class polynomials -/

public section

namespace SptClassification

/-- Two specialized generators from the actual primitive CM products cannot
commute if their actions on the cyclic subgroup retain the oriented complex
scalars. This isolates scalar persistence as a geometric reduction obligation;
the quadratic relation and contradiction are proved algebraically. -/
theorem primitiveCM_actions_not_commute
    {D : ℤ} {r s : ZMod 12} [Fact (D < 0)]
    (C : PrimitiveCMClass D r) (E : PrimitiveCMClass D s)
    (hr : r = 1 ∨ r = 11) (hs : s = 5 ∨ s = 7)
    {O K : Type*} [Ring O] [DivisionRing K]
    (order : ConditionalCM.PreservingOrder O K) (n : ℕ) (α β : O)
    (hα : order.intoDivision α * order.intoDivision α - order.intoDivision α +
      (n : K) = 0)
    (hβ : order.intoDivision β * order.intoDivision β - order.intoDivision β +
      (n : K) = 0)
    (hαres : order.restriction α = C.val.cmGeneratorResidue)
    (hβres : order.restriction β = E.val.cmGeneratorResidue) :
    order.intoDivision α * order.intoDivision β ≠
      order.intoDivision β * order.intoDivision α := by
  apply ConditionalCM.oriented_actions_not_commute order n α β hα hβ
  · rw [hαres]
    exact C.cmGeneratorResidue_first_pair hr
  · rw [hβres]
    exact E.cmGeneratorResidue_second_pair hs

/-- If two oriented CM lattices specialize equivariantly to cyclic six-torsion
subgroups in one reduced pair, their integral CM endomorphisms cannot commute.
Faithfulness of each selected subgroup suffices; the two chosen generators need
not be identified. Scalar persistence and incompatibility are deductions here. -/
theorem levelSixCM_actions_not_commute_of_specialization
    {D : ℤ} {r s : ZMod 12}
    (Q : LevelSixForm D r) (R : LevelSixForm D s)
    (hr : r = 1 ∨ r = 11) (hs : s = 5 ∨ s = 7)
    {O K G : Type*} [Ring O] [DivisionRing K]
    [AddCommGroup G] [Module (ZMod 6) G]
    (order : ConditionalCM.PreservingOrder O K) (n : ℕ) (α β : O)
    (hα : order.intoDivision α * order.intoDivision α - order.intoDivision α +
      (n : K) = 0)
    (hβ : order.intoDivision β * order.intoDivision β - order.intoDivision β +
      (n : K) = 0)
    (specializeQ specializeR : (ZMod 6 × ZMod 6) →ₗ[ZMod 6] G)
    (actionα actionβ : G → G)
    (hQ : ∀ v, actionα (specializeQ v) =
      specializeQ (Q.cmGeneratorSixTorsionCoordinates v))
    (hR : ∀ v, actionβ (specializeR v) =
      specializeR (R.cmGeneratorSixTorsionCoordinates v))
    (hαscalar : actionα (specializeQ (1, 0)) =
      order.restriction α • specializeQ (1, 0))
    (hβscalar : actionβ (specializeR (1, 0)) =
      order.restriction β • specializeR (1, 0))
    (hfaithfulQ : Function.Injective
      (fun a : ZMod 6 => a • specializeQ (1, 0)))
    (hfaithfulR : Function.Injective
      (fun a : ZMod 6 => a • specializeR (1, 0))) :
    order.intoDivision α * order.intoDivision β ≠
      order.intoDivision β * order.intoDivision α := by
  have hαres : order.restriction α = Q.cmGeneratorResidue :=
    Q.cmGeneratorResidue_eq_of_specialization specializeQ actionα
      (order.restriction α) hQ hαscalar hfaithfulQ
  have hβres : order.restriction β = R.cmGeneratorResidue :=
    R.cmGeneratorResidue_eq_of_specialization specializeR actionβ
      (order.restriction β) hR hβscalar hfaithfulR
  apply ConditionalCM.oriented_actions_not_commute order n α β hα hβ
  · rw [hαres]
    exact Q.cmGeneratorResidue_first_pair hr
  · rw [hβres]
    exact R.cmGeneratorResidue_second_pair hs

/-- Prime-to-characteristic injectivity on the two full six-torsion modules
supplies both faithful cyclic lines. Their generators may specialize through
different identifications with the same reduced pair. -/
theorem levelSixCM_actions_not_commute_of_injective_specialization
    {D : ℤ} {r s : ZMod 12}
    (Q : LevelSixForm D r) (R : LevelSixForm D s)
    (hr : r = 1 ∨ r = 11) (hs : s = 5 ∨ s = 7)
    {O K G : Type*} [Ring O] [DivisionRing K]
    [AddCommGroup G] [Module (ZMod 6) G]
    (order : ConditionalCM.PreservingOrder O K) (n : ℕ) (α β : O)
    (hα : order.intoDivision α * order.intoDivision α - order.intoDivision α +
      (n : K) = 0)
    (hβ : order.intoDivision β * order.intoDivision β - order.intoDivision β +
      (n : K) = 0)
    (specializeQ specializeR : (ZMod 6 × ZMod 6) →ₗ[ZMod 6] G)
    (hinjectiveQ : Function.Injective specializeQ)
    (hinjectiveR : Function.Injective specializeR)
    (actionα actionβ : G → G)
    (hQ : ∀ v, actionα (specializeQ v) =
      specializeQ (Q.cmGeneratorSixTorsionCoordinates v))
    (hR : ∀ v, actionβ (specializeR v) =
      specializeR (R.cmGeneratorSixTorsionCoordinates v))
    (hαscalar : actionα (specializeQ (1, 0)) =
      order.restriction α • specializeQ (1, 0))
    (hβscalar : actionβ (specializeR (1, 0)) =
      order.restriction β • specializeR (1, 0)) :
    order.intoDivision α * order.intoDivision β ≠
      order.intoDivision β * order.intoDivision α := by
  exact levelSixCM_actions_not_commute_of_specialization Q R hr hs order n α β
    hα hβ specializeQ specializeR actionα actionβ hQ hR hαscalar hβscalar
    (LevelSixForm.firstLine_injective_of_injective_specialization
      specializeQ hinjectiveQ)
    (LevelSixForm.firstLine_injective_of_injective_specialization
      specializeR hinjectiveR)

/-- The arithmetic part of the two splitting-type argument in
[rolenManuscript, Lemma `lem:separation`]. The first pair of orientations
rules out ordinary commutative reduction. In the supersingular case, the
degree estimate `6p ≤ 4N(α)N(β)` of [rolen2026canonical, Lemma 5.2] gives the
manuscript's bound with `N(α) = N(β) = (d+1)/4`. The parameters here expose
those geometric facts separately; no reduced elliptic pair is asserted. -/
theorem oriented_cm_actions_force_prime_bound
    {O D : Type*} [Ring O] [DivisionRing D]
    (order : ConditionalCM.PreservingOrder O D)
    (d p n : ℕ) (α β : O) (hn : 4 * n = d + 1)
    (hα : order.intoDivision α * order.intoDivision α - order.intoDivision α +
      (n : D) = 0)
    (hβ : order.intoDivision β * order.intoDivision β - order.intoDivision β +
      (n : D) = 0)
    (hαres : order.restriction α = 0 ∨ order.restriction α = 1)
    (hβres : order.restriction β = 3 ∨ order.restriction β = 4)
    (ordinary : Prop)
    (hordinary : ordinary → ∀ x y : O,
      order.intoDivision x * order.intoDivision y =
        order.intoDivision y * order.intoDivision x)
    (hsupersingular : ¬ordinary →
      order.intoDivision α * order.intoDivision β ≠
        order.intoDivision β * order.intoDivision α →
      6 * p ≤ 4 * n * n) :
    24 * p ≤ (d + 1) ^ 2 := by
  have hnoncomm := ConditionalCM.oriented_actions_not_commute order n α β
    hα hβ hαres hβres
  have hnotOrd : ¬ordinary := by
    intro ho
    exact hnoncomm (hordinary ho α β)
  have hdegree := hsupersingular hnotOrd hnoncomm
  calc
    24 * p = 4 * (6 * p) := by ring
    _ ≤ 4 * (4 * n * n) := Nat.mul_le_mul_left 4 hdegree
    _ = (d + 1) ^ 2 := by rw [← hn]; ring

/-- Under the manuscript's strict separation bound, the reduction prime is
larger than the norm `(d + 1) / 4` of the two CM generators. In particular,
their reductions have degree prime to the residue characteristic. -/
theorem cm_separation_prime_gt_generator_norm (d p n : ℕ)
    (hmod : d % 24 = 23) (hn : 4 * n = d + 1)
    (hbound : (d + 1) ^ 2 < 24 * p) : n < p := by
  have hn6 : 6 ≤ n := by omega
  have hthree : 3 ≤ 2 * n := by omega
  have hsq : 24 * n ≤ (4 * n) ^ 2 := by
    calc
      24 * n = (8 * n) * 3 := by ring
      _ ≤ (8 * n) * (2 * n) := Nat.mul_le_mul_left _ hthree
      _ = (4 * n) ^ 2 := by ring
  rw [← hn] at hbound
  omega

/-- Consequently, that norm is nonzero in the residue characteristic. -/
theorem cm_separation_prime_not_dvd_generator_norm (d p n : ℕ)
    (hmod : d % 24 = 23) (hn : 4 * n = d + 1)
    (hbound : (d + 1) ^ 2 < 24 * p) : ¬p ∣ n := by
  have hnpos : 0 < n := by omega
  have hlt := cm_separation_prime_gt_generator_norm d p n hmod hn hbound
  intro hdiv
  have hle := Nat.le_of_dvd hnpos hdiv
  omega

/-- Separation for the canonical integral CM polynomials once a common root
has been realized as two oriented actions on one reduced level-six pair.
The algebraic contradiction and trace-covolume estimate are supplied by the
proved conditional separation argument. This statement isolates the remaining
specialization step in the all-prime manuscript proof. -/
theorem cm_separation_of_common_root_action (d p : ℕ)
    [Fact (-(d : ℤ) < 0)] [Fact p.Prime]
    (hd : 0 < d) (hsq : Squarefree d) (hmod : d % 24 = 23)
    (hcop : ¬p ∣ 6 * d)
    (hbound : (d + 1) ^ 2 < 24 * p)
    (hcommon :
      let models := integralCMClassPolynomials d hd hsq hmod
      let reduction := cmCoefficientReduction p (fun h => hcop (dvd_mul_of_dvd_left h d))
      ∀ x : AlgebraicClosure (ZMod p),
        (Polynomial.aeval x) (models.modelA.map reduction) = 0 →
        (Polynomial.aeval x) (models.modelB.map reduction) = 0 →
        ConditionalCM.CommonRootAction d p) :
    let models := integralCMClassPolynomials d hd hsq hmod
    let reduction := cmCoefficientReduction p (fun h => hcop (dvd_mul_of_dvd_left h d))
    IsCoprime (models.modelA.map reduction) (models.modelB.map reduction) := by
  let models := integralCMClassPolynomials d hd hsq hmod
  let reduction := cmCoefficientReduction p (fun h => hcop (dvd_mul_of_dvd_left h d))
  have hp6 : ¬p ∣ 6 := fun h => hcop (dvd_mul_of_dvd_left h d)
  have hp2 : p ≠ 2 := by
    intro h
    subst p
    exact hp6 (by decide)
  have hp3 : p ≠ 3 := by
    intro h
    subst p
    exact hp6 (by decide)
  have hp4 : p ≠ 4 := by
    intro h
    subst p
    exact (by decide : ¬Nat.Prime 4) Fact.out
  have hp : 5 ≤ p := by
    have hprime : Nat.Prime p := Fact.out
    have htwo := hprime.two_le
    omega
  let I : ConditionalCM.CMDescentInput d p := {
    modelA := models.modelA
    modelB := models.modelB
    modelA_monic := models.monicA
    modelB_monic := models.monicB
    complexSpecialization := cmCoefficientComplexMap
    complexA := models.complexA
    complexB := models.complexB
    reduction := reduction
    commonRoot := hcommon }
  exact ConditionalCM.conditional_cm_separation d p hd hsq hmod hp hcop hbound I

/-- The reductions of the actual oriented class polynomials are coprime under
the manuscript bound, for both splitting types. The models come from the
explicit admitted integral-descent theorem, with no geometric hypothesis added
to this original target [rolenManuscript, label lem:separation]. -/
theorem cm_separation (d p : ℕ) [Fact (-(d : ℤ) < 0)] [Fact p.Prime]
    (hd : 0 < d) (hsq : Squarefree d) (hmod : d % 24 = 23)
    (hcop : ¬p ∣ 6 * d) (hbound : (d + 1) ^ 2 < 24 * p) :
    let models := integralCMClassPolynomials d hd hsq hmod
    let reduction := cmCoefficientReduction p (fun h => hcop (dvd_mul_of_dvd_left h d))
    IsCoprime (models.modelA.map reduction) (models.modelB.map reduction) := by
  classical
  have hp6 : ¬p ∣ 6 := fun h => hcop (dvd_mul_of_dvd_left h d)
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hp6 (by decide)
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact hp6 (by decide)
  have hp : 3 < p := by
    have htwo := (Fact.out : p.Prime).two_le
    omega
  exact CMIntegralValues.isCoprime_of_bound d p hp6 hp hmod hbound
    (integralCMClassPolynomials d hd hsq hmod)

end SptClassification
