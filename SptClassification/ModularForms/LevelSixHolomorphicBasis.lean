/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.LevelSixEtaQuotient
public import SptClassification.ModularForms.LevelSixEtaFrame
public import SptClassification.ModularForms.TriangularQExpansionDescent
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# The holomorphic eta basis at level six

The actual coordinate is `t = 72/t₆` and the weight-one form is
`b = (t₆/72) h₆` in [maier2009]. Even powers have trivial character.
The integral basis is ordered by its initial exponent, so its `i`th member
is `t^(k-i) b^k`, beginning with `q^i`.
-/

public noncomputable section

namespace SptClassification.LevelSixHolomorphicBasis

/-- Maier's alternative weight-one form, with its original leading coefficient one.
It has quadratic character; it is not a trivial-character weight-one modular form. -/
def b (z : ℂ) : ℂ :=
  ModularForm.eta z * ModularForm.eta (6 * z) ^ 6 /
    (ModularForm.eta (2 * z) ^ 2 * ModularForm.eta (3 * z) ^ 3)

theorem b_ne_zero (z : UpperHalfPlane) : b z ≠ 0 := by
  have h2 : ModularForm.eta (2 * (z : ℂ)) ≠ 0 := by
    simpa using eta_pos_mul_ne_zero 2 (by norm_num) z
  have h3 : ModularForm.eta (3 * (z : ℂ)) ≠ 0 := by
    simpa using eta_pos_mul_ne_zero 3 (by norm_num) z
  have h6 : ModularForm.eta (6 * (z : ℂ)) ≠ 0 := by
    simpa using eta_pos_mul_ne_zero 6 (by norm_num) z
  exact div_ne_zero (mul_ne_zero (ModularForm.eta_ne_zero z.im_pos) (pow_ne_zero _ h6))
    (mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3))

/-- A consequence of [maier2009], Corollary 5.5.1, pp.23–24, Table 8,
p.26, the character calculation p.28, and Table 11, p.31 (arXiv v4),
together with compact genus-zero divisor theory. This is not a verbatim
statement in Maier: `t=72/t₆` and `b=(t₆/72)h₆`, so `F/b^k` is invariant,
has no finite poles, and has a pole of order at most `k` at infinity.
Evenness kills the quadratic character. The bundled modular form requires
global holomorphy, including boundedness at every cusp through
`ModularForm.bdd_at_cusps'`. -/
theorem holomorphic_polynomial_representation_literature
    (k : ℕ) (hk : Even k)
    (F : ModularForm ((CongruenceSubgroup.Gamma0 6).map
      (Matrix.SpecialLinearGroup.mapGL ℝ)) (k : ℤ)) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ k ∧
      ∀ z : UpperHalfPlane, F z = P.eval (levelSixEtaQuotient z) * b z ^ k := by
  sorry

/-- The unit in `t^(k-i) b^k = q^i U^(k-i) V^k`, for `i ≤ k`.
Here `q t = U` and `b = q V`; both units are over the integers. -/
def basisUnit (k i : ℕ) : PowerSeries ℤ :=
  levelSixFormalEulerUnit ^ (k - i) * LevelSixEtaFrame.cuspFormUnit ^ k

@[simp] theorem basisUnit_constantCoeff (k i : ℕ) :
    PowerSeries.constantCoeff (basisUnit k i) = 1 := by
  simp [basisUnit, map_mul, map_pow, levelSixFormalEulerUnit_constantCoeff]

/-- The integral Fourier series of the reversed eta basis. No pole is sent
into a power-series ring: only the holomorphic product with `i ≤ k` is used. -/
def basisSeries (k i : ℕ) : PowerSeries ℤ := PowerSeries.X ^ i * basisUnit k i

/-- The formal expansion of a degree-at-most-`k` polynomial times `b^k`.
The reversed polynomial coefficients match the increasing initial exponents. -/
def polynomialSeries (k : ℕ) (P : Polynomial ℂ) : PowerSeries ℂ :=
  ∑ i ∈ Finset.range (k + 1),
    PowerSeries.C (P.coeff (k - i)) *
      PowerSeries.map (Int.castRingHom ℂ) (basisSeries k i)

/-- The Fourier expansion of a holomorphic eta polynomial. Derived from
the convergent eta product in [maier2009], Tables 8 and 11, pp.26,31, with
`t=q⁻¹ U`, `b=q V`, and uniqueness of Taylor coefficients at the cusp.
Only `deg P ≤ k` is allowed: individual powers of the pole `t` are not
asserted to have power-series expansions. This is an analytic/formal Euler
product comparison, not an integral-descent or global modularity assertion. -/
theorem polynomial_qExpansion_literature (k : ℕ) (P : Polynomial ℂ)
    (hdeg : P.natDegree ≤ k) :
    UpperHalfPlane.qExpansion 1
      (fun z : UpperHalfPlane => P.eval (levelSixEtaQuotient z) * b z ^ k) =
      polynomialSeries k P := by
  sorry

/-- The reversed integral basis works over every complex subring, including
local coefficient rings. No denominator bound on the ring is imposed. -/
theorem coefficients_mem_subring_of_polynomialSeries (R : Subring ℂ)
    (k : ℕ) (P : Polynomial ℂ) (hdeg : P.natDegree ≤ k)
    (h : ∀ n, PowerSeries.coeff n (polynomialSeries k P) ∈ R) :
    ∀ n, P.coeff n ∈ R := by
  have hc : ∀ i ≤ k, P.coeff (k - i) ∈ R := by
    apply coefficients_mem_subring_of_triangular_qexp R k
      (fun i => PowerSeries.map (Int.castRingHom ℂ) (basisSeries k i))
      (fun i => P.coeff (k - i))
    · intro i _ j
      simp only [PowerSeries.coeff_map]
      exact intCast_mem R _
    · intro i _ j hji
      simp [basisSeries, PowerSeries.coeff_X_pow_mul', Nat.not_le.mpr hji]
    · intro i _
      simp [basisSeries, PowerSeries.coeff_X_pow_mul',
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
    · exact h
  intro n
  by_cases hn : n ≤ k
  · simpa [Nat.sub_sub_self hn] using hc (k - n) (Nat.sub_le k n)
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < n)]
    exact R.zero_mem

/-- Integrality of the Fourier row forces integrality of every polynomial
coefficient. This is triangular algebra and uses no literature admission. -/
theorem coefficients_integral_of_polynomialSeries (k : ℕ) (P : Polynomial ℂ)
    (hdeg : P.natDegree ≤ k)
    (h : ∀ n, PowerSeries.coeff n (polynomialSeries k P) ∈ (Int.castRingHom ℂ).range) :
    ∀ n, P.coeff n ∈ (Int.castRingHom ℂ).range := by
  exact coefficients_mem_subring_of_polynomialSeries
    (Int.castRingHom ℂ).range k P hdeg h

/-- Coefficient descent for an actual function represented by an eta polynomial.
Only the analytic expansion comparison is admitted; the descent is proved. -/
theorem coefficients_mem_subring_of_qExpansion (R : Subring ℂ)
    (k : ℕ) (P : Polynomial ℂ) (hdeg : P.natDegree ≤ k)
    (F : UpperHalfPlane → ℂ)
    (hF : ∀ z, F z = P.eval (levelSixEtaQuotient z) * b z ^ k)
    (hcoeff : ∀ n, PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 F) ∈ R) :
    ∀ n, P.coeff n ∈ R := by
  apply coefficients_mem_subring_of_polynomialSeries R k P hdeg
  have heq : F = fun z : UpperHalfPlane => P.eval (levelSixEtaQuotient z) * b z ^ k := funext hF
  simpa only [heq, polynomial_qExpansion_literature k P hdeg] using hcoeff

/-- Every globally holomorphic even-weight form with Fourier coefficients in
`R` has an eta polynomial whose coefficients lie in the same subring. -/
theorem holomorphic_polynomial_representation_over_subring
    (R : Subring ℂ) (k : ℕ) (hk : Even k)
    (F : ModularForm ((CongruenceSubgroup.Gamma0 6).map
      (Matrix.SpecialLinearGroup.mapGL ℝ)) (k : ℤ))
    (hcoeff : ∀ n, PowerSeries.coeff n
      (UpperHalfPlane.qExpansion 1 (fun z => F z)) ∈ R) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ k ∧
      (∀ z : UpperHalfPlane, F z = P.eval (levelSixEtaQuotient z) * b z ^ k) ∧
      ∀ n, P.coeff n ∈ R := by
  obtain ⟨P, hdeg, hF⟩ := holomorphic_polynomial_representation_literature k hk F
  exact ⟨P, hdeg, hF,
    coefficients_mem_subring_of_qExpansion R k P hdeg (fun z => F z) hF hcoeff⟩

/-- Coefficient membership gives a polynomial over the coefficient subring,
with the same degree bound. This construction is purely algebraic. -/
theorem exists_polynomial_over_subring (R : Subring ℂ) (k : ℕ)
    (P : Polynomial ℂ) (hdeg : P.natDegree ≤ k)
    (hcoeff : ∀ n, P.coeff n ∈ R) :
    ∃ Q : Polynomial R, Q.map R.subtype = P ∧ Q.natDegree ≤ k := by
  let Q : Polynomial R := ∑ n ∈ Finset.range (k + 1),
    Polynomial.monomial n ⟨P.coeff n, hcoeff n⟩
  have hmap : Q.map R.subtype = P := by
    ext n
    by_cases hn : n ≤ k
    · simp [Q, Polynomial.coeff_sum, Polynomial.coeff_monomial, Finset.mem_range,
        Nat.lt_succ_iff, hn]
    · simp [Q, Polynomial.coeff_sum, Polynomial.coeff_monomial, Finset.mem_range,
        Nat.lt_succ_iff, hn,
        Polynomial.coeff_eq_zero_of_natDegree_lt (show P.natDegree < n by omega)]
  refine ⟨Q, hmap, ?_⟩
  rw [← Polynomial.natDegree_map_eq_of_injective R.subtype_injective, hmap]
  exact hdeg

/-- The integral eta-basis interface, usable also for local complex coefficient
rings. Global holomorphy comes from `F`; the Fourier row is the only arithmetic
hypothesis. Both literature inputs remain explicit named admissions. -/
theorem holomorphic_basis_over_subring
    (R : Subring ℂ) (k : ℕ) (hk : Even k)
    (F : ModularForm ((CongruenceSubgroup.Gamma0 6).map
      (Matrix.SpecialLinearGroup.mapGL ℝ)) (k : ℤ))
    (hcoeff : ∀ n, PowerSeries.coeff n
      (UpperHalfPlane.qExpansion 1 (fun z => F z)) ∈ R) :
    ∃ Q : Polynomial R, Q.natDegree ≤ k ∧
      ∀ z : UpperHalfPlane,
        F z = (Q.map R.subtype).eval (levelSixEtaQuotient z) * b z ^ k := by
  obtain ⟨P, hdeg, hF, hP⟩ :=
    holomorphic_polynomial_representation_over_subring R k hk F hcoeff
  obtain ⟨Q, hmap, hQ⟩ := exists_polynomial_over_subring R k P hdeg hP
  exact ⟨Q, hQ, by simpa only [hmap] using hF⟩

end SptClassification.LevelSixHolomorphicBasis
