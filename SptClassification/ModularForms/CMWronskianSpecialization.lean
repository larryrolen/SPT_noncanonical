/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.HasseObstructionGeometry
public import SptClassification.ModularForms.CMLogarithmicLift
public import SptClassification.QuadraticForms.IntegralClassPolynomials

/-!
# Specialization of the CM logarithmic numerator

The numerator in the logarithmic derivative of the actual oriented CM
polynomial quotient is formed over `ℤ[1/6]` before either complex
specialization or reduction modulo a good prime. This identifies the
polynomial used in the analytic identity with the polynomial used in the
supersingular root count of [rolenManuscript, Section 4].
-/

public section

namespace SptClassification

open Polynomial

/-- Polynomial logarithmic numerators commute with coefficient base change. -/
theorem cmLogarithmicNumerator_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A B : R[X]) :
    (A.derivative * B - A * B.derivative).map f =
      (A.map f).derivative * B.map f -
        A.map f * (B.map f).derivative := by
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.derivative_map]

/-- The logarithmic numerator of the actual oriented CM products, formed
over `ℤ[1/6]` using their integral descent [rolen2026canonical, Lemma 4.1]. -/
noncomputable def integralCMLogarithmicNumerator (d : ℕ)
    [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) : Polynomial (Localization.Away (6 : ℤ)) :=
  let C := integralCMClassPolynomials d hd hsq hmod
  C.modelA.derivative * C.modelB - C.modelA * C.modelB.derivative

/-- Complex specialization of the integral numerator is exactly the
Wronskian in the manuscript's logarithmic formula. -/
theorem integralCMLogarithmicNumerator_complex (d : ℕ)
    [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) :
    (integralCMLogarithmicNumerator d hd hsq hmod).map cmCoefficientComplexMap =
      (cmClassPolynomialA (-(d : ℤ))).derivative *
          cmClassPolynomialB (-(d : ℤ)) -
        cmClassPolynomialA (-(d : ℤ)) *
          (cmClassPolynomialB (-(d : ℤ))).derivative := by
  rw [integralCMLogarithmicNumerator, cmLogarithmicNumerator_map,
    (integralCMClassPolynomials d hd hsq hmod).complexA,
    (integralCMClassPolynomials d hd hsq hmod).complexB]

/-- The analytic logarithmic lift uses the complex specialization of the
same integral numerator that is reduced at good primes. This is the
polynomial identity in [rolenManuscript, Section 4, equation (L)]. -/
theorem cmLogarithmicLift_eq_integralNumerator (d : ℕ)
    [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) (z : UpperHalfPlane)
    (ha : (cmClassPolynomialA (-(d : ℤ))).eval (levelSixEtaQuotient z) ≠ 0)
    (hb : (cmClassPolynomialB (-(d : ℤ))).eval (levelSixEtaQuotient z) ≠ 0) :
    cmLogarithmicLift (-(d : ℤ)) z =
      thetaDerivative levelSixEtaQuotient z *
        ((integralCMLogarithmicNumerator d hd hsq hmod).map
          cmCoefficientComplexMap).eval (levelSixEtaQuotient z) /
        ((cmClassPolynomialA (-(d : ℤ))).eval (levelSixEtaQuotient z) *
          (cmClassPolynomialB (-(d : ℤ))).eval (levelSixEtaQuotient z)) := by
  rw [integralCMLogarithmicNumerator_complex]
  exact cmLogarithmicLift_eq_rational (-(d : ℤ)) z ha hb

/-- Reduction of this same integral numerator agrees with the Wronskian
of the reduced CM products at every prime away from six. -/
theorem integralCMLogarithmicNumerator_reduction (d p : ℕ)
    [Fact (-(d : ℤ) < 0)] [Fact p.Prime]
    (hd : 0 < d) (hsq : Squarefree d) (hmod : d % 24 = 23)
    (hp6 : ¬p ∣ 6) :
    (integralCMLogarithmicNumerator d hd hsq hmod).map
        (cmCoefficientReduction p hp6) =
      ((integralCMClassPolynomials d hd hsq hmod).modelA.map
          (cmCoefficientReduction p hp6)).derivative *
        (integralCMClassPolynomials d hd hsq hmod).modelB.map
          (cmCoefficientReduction p hp6) -
      (integralCMClassPolynomials d hd hsq hmod).modelA.map
          (cmCoefficientReduction p hp6) *
        ((integralCMClassPolynomials d hd hsq hmod).modelB.map
          (cmCoefficientReduction p hp6)).derivative := by
  rw [integralCMLogarithmicNumerator, cmLogarithmicNumerator_map]

/-- Over the geometric residue field, the reduced integral numerator is
still the Wronskian of the two actual descended CM polynomials. -/
theorem integralCMLogarithmicNumerator_geometric (d p : ℕ)
    [Fact (-(d : ℤ) < 0)] [Fact p.Prime]
    (hd : 0 < d) (hsq : Squarefree d) (hmod : d % 24 = 23)
    (hp6 : ¬p ∣ 6) :
    ((integralCMLogarithmicNumerator d hd hsq hmod).map
        (cmCoefficientReduction p hp6)).map
          (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) =
      (((integralCMClassPolynomials d hd hsq hmod).modelA.map
          (cmCoefficientReduction p hp6)).map
            (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))).derivative *
        ((integralCMClassPolynomials d hd hsq hmod).modelB.map
          (cmCoefficientReduction p hp6)).map
            (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) -
      ((integralCMClassPolynomials d hd hsq hmod).modelA.map
          (cmCoefficientReduction p hp6)).map
            (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) *
        (((integralCMClassPolynomials d hd hsq hmod).modelB.map
          (cmCoefficientReduction p hp6)).map
            (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))).derivative := by
  rw [integralCMLogarithmicNumerator_reduction, cmLogarithmicNumerator_map]

namespace ConditionalCM

/-- The numerator of the quotient of the two descended, oriented CM products. -/
noncomputable def CMDescentInput.modelLogarithmicNumerator {d p : ℕ}
    [Fact (-(d : ℤ) < 0)] [Fact p.Prime]
    (C : CMDescentInput d p) : Polynomial (Localization.Away (6 : ℤ)) :=
  C.modelA.derivative * C.modelB - C.modelA * C.modelB.derivative

/-- Its complex specialization is the Wronskian of the actual oriented
CM products, with the order and signs in the manuscript's equation (L). -/
theorem CMDescentInput.modelLogarithmicNumerator_complex {d p : ℕ}
    [Fact (-(d : ℤ) < 0)] [Fact p.Prime]
    (C : CMDescentInput d p) :
    C.modelLogarithmicNumerator.map C.complexSpecialization =
      (cmClassPolynomialA (-(d : ℤ))).derivative *
          cmClassPolynomialB (-(d : ℤ)) -
        cmClassPolynomialA (-(d : ℤ)) *
          (cmClassPolynomialB (-(d : ℤ))).derivative := by
  rw [CMDescentInput.modelLogarithmicNumerator,
    cmLogarithmicNumerator_map, C.complexA, C.complexB]

/-- Reduction of the same integral numerator is the Wronskian of the
geometric CM models over the algebraic closure of the residue field. -/
theorem CMDescentInput.modelLogarithmicNumerator_geometric {d p : ℕ}
    [Fact (-(d : ℤ) < 0)] [Fact p.Prime]
    (C : CMDescentInput d p) :
    (C.modelLogarithmicNumerator.map C.reduction).map
        (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) =
      C.geometricA.derivative * C.geometricB -
        C.geometricA * C.geometricB.derivative := by
  rw [CMDescentInput.modelLogarithmicNumerator,
    cmLogarithmicNumerator_map, cmLogarithmicNumerator_map]
  rw [C.geometricA_eq, C.geometricB_eq]

/-- The specialized numerator retains the manuscript's degree bound.
This is a bound for the Wronskian of the actual descended CM products,
independent of any assertion about supersingular points. -/
theorem CMDescentInput.geometricLogarithmicNumerator_natDegree_le {d p : ℕ}
    [Fact (-(d : ℤ) < 0)] [Fact p.Prime]
    (C : CMDescentInput d p) (hmod : d % 24 = 23) :
    (C.geometricA.derivative * C.geometricB -
      C.geometricA * C.geometricB.derivative).natDegree ≤
        4 * formClassNumber (-(d : ℤ)) - 2 := by
  have hD : (-(d : ℤ)) % 4 = 1 := by omega
  have hpositive : 0 < formClassNumber (-(d : ℤ)) :=
    formClassNumber_pos _ hD
  have hA := C.geometricA_degree hmod
  have hB := C.geometricB_degree hmod
  have hdegree : C.geometricB.natDegree = C.geometricA.natDegree := by
    rw [hA, hB]
  have hpos : 0 < C.geometricA.natDegree := by
    rw [hA]
    omega
  have hbound := natDegree_logarithmicNumerator_le
    C.geometricA_monic C.geometricB_monic hdegree hpos
  rw [hA] at hbound
  omega

/-- Coprimality after good reduction keeps this particular numerator
nonzero when the common CM degree is below the characteristic. -/
theorem CMDescentInput.geometricLogarithmicNumerator_ne_zero {d p : ℕ}
    [Fact (-(d : ℤ) < 0)] [Fact p.Prime]
    (C : CMDescentInput d p) (hmod : d % 24 = 23)
    (hcop : IsCoprime C.geometricA C.geometricB)
    (hlt : 2 * formClassNumber (-(d : ℤ)) < p) :
    C.geometricA.derivative * C.geometricB -
      C.geometricA * C.geometricB.derivative ≠ 0 := by
  have hD : (-(d : ℤ)) % 4 = 1 := by omega
  have hpositive : 0 < formClassNumber (-(d : ℤ)) :=
    formClassNumber_pos _ hD
  have hA := C.geometricA_degree hmod
  have hpos : 0 < C.geometricA.natDegree := by
    rw [hA]
    omega
  have hlt' : C.geometricA.natDegree < p := by
    rw [hA]
    exact hlt
  exact logarithmicNumerator_ne_zero_of_char p hcop
    C.geometricA_monic hpos hlt'

/-- Distinct roots of the reduction of the actual integral CM numerator
obey the manuscript's `4h-2` bound. The root hypothesis refers to the
specialization of the same polynomial that yields the complex logarithmic
derivative, rather than to a separately chosen polynomial. -/
theorem CMDescentInput.geometricLogarithmicNumerator_roots_card_le {d p : ℕ}
    [Fact (-(d : ℤ) < 0)] [Fact p.Prime]
    (C : CMDescentInput d p) (hmod : d % 24 = 23)
    (hcop : IsCoprime C.geometricA C.geometricB)
    (hlt : 2 * formClassNumber (-(d : ℤ)) < p)
    (s : Finset (AlgebraicClosure (ZMod p)))
    (hs : ∀ x ∈ s,
      ((C.modelLogarithmicNumerator.map C.reduction).map
        (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))).IsRoot x) :
    s.card ≤ 4 * formClassNumber (-(d : ℤ)) - 2 := by
  have hD : (-(d : ℤ)) % 4 = 1 := by omega
  have hpositive : 0 < formClassNumber (-(d : ℤ)) :=
    formClassNumber_pos _ hD
  have hA := C.geometricA_degree hmod
  have hB := C.geometricB_degree hmod
  have hdegree : C.geometricB.natDegree = C.geometricA.natDegree := by
    rw [hA, hB]
  have hpos : 0 < C.geometricA.natDegree := by
    rw [hA]
    omega
  have hlt' : C.geometricA.natDegree < p := by
    rw [hA]
    exact hlt
  have hs' : ∀ x ∈ s,
      (C.geometricA.derivative * C.geometricB -
        C.geometricA * C.geometricB.derivative).IsRoot x := by
    intro x hx
    simpa only [C.modelLogarithmicNumerator_geometric] using hs x hx
  have hbound := logarithmicNumerator_roots_card_le p hcop
    C.geometricA_monic C.geometricB_monic hdegree hpos hlt' s hs'
  rw [hA] at hbound
  omega

end ConditionalCM
end SptClassification
