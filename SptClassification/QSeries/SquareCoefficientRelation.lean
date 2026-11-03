/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.PrimeInverseEtaHeckeInversion
public import SptClassification.QSeries.QuadraticGaussLiterature

/-! # The square-index coefficient congruence for the prescribed principal forms -/

public section

namespace SptClassification.QSeries

/-- The exact rational identities (ct1) and (ct2) in
[rolenManuscript, §3] for the manuscript's prescribed principal forms.
The signed quadratic Gauss evaluation is admitted separately as classical
literature; the shadow forms and their one-prime laws are the named inputs
from [rolen2026canonical, Proposition 2.2 and Lemma 2.4]. The pairings and
repeated-prime Hecke iteration are proved in this library. -/
theorem constant_term_pairings
    (d n : ℕ) (hd : d % 24 = 23) (hn : 0 < n) (hc : n.Coprime 6) :
    heckeThreeHalfWord n.primeFactorsList (fun r => (fFourier r : ℚ)) d =
        -∑ t ∈ n.divisors,
          (heckePrincipalCoefficient n.primeFactorsList t : ℚ) *
            (principalHFourier d (fFourier d) ((t : ℤ) ^ 2) : ℚ) ∧
      (n : ℚ) ^ 2 *
        heckeMinusHalfWord n.primeFactorsList
          (fun r => (partitionFourier r : ℚ)) d =
          -∑ t ∈ n.divisors,
            ((heckePrincipalCoefficient n.primeFactorsList t : ℚ) /
              (t : ℚ) ^ 2) *
              (principalKFourier d ((t : ℤ) ^ 2) : ℚ) := by
  let forms : IndividualShadowForms := Classical.choice rolen_individualShadowForms
  exact constant_term_pairings_of_primeInverseEtaLaw forms
    (rolenPrimeShadowRelations forms)
    (primeInverseEtaHeckeLawOfSignedGauss
      (fun q hqPrime hq5 =>
        letI : Fact q.Prime := hqPrime
        quadraticGaussSum_positivePhase q (by omega)))
    d n hd hn hc

/-- The identity Hecke word already gives the square-index relation at one.
Both product constant terms are those of the actual prescribed forms, so no
analytic Hecke or shadow-cancellation premise is needed in this base case.
[rolenManuscript, §3, equations (ct1) and (ct2)] -/
theorem square_coefficient_relation_one
    (p : ℕ) [Fact p.Prime] (sign : ℤ) (d : ℕ)
    (hd : d % 24 = 23) (hr : legendreSym p (-(d : ℤ)) = sign)
    (hspt : ∀ j : ℕ, legendreSym p (1 - 24 * (j : ℤ)) = sign → p ∣ spt j) :
    (p : ℤ) ∣ principalHFourier d (fFourier d) 1 +
      (d : ℤ) * principalKFourier d 1 := by
  have hsptMod : ∀ j : ℕ, legendreSym p (1 - 24 * (j : ℤ)) = sign →
      ((spt j : ℤ) : ZMod p) = 0 := by
    intro j hj
    simpa only [Int.cast_natCast] using
      (ZMod.natCast_eq_zero_iff (spt j) p).mpr (hspt j hj)
  have hmod := principalForms_squareCoefficient_mod_of_rat_constantTerms_zero
    p 1 d (by decide) (by simp) hd sign hr hsptMod
    (by
      intro n hn _
      have hn1 : n = 1 := Nat.eq_one_of_dvd_one hn
      subst n
      simpa only [Nat.primeFactorsList_one, List.prod_nil,
        heckeThreeHalfWord_nil] using
        principalH_f_finiteConstantTerm_zero d hd)
    (by
      intro n hn _
      have hn1 : n = 1 := Nat.eq_one_of_dvd_one hn
      subst n
      simpa only [Nat.primeFactorsList_one, List.prod_nil,
        heckeMinusHalfWord_nil, Nat.cast_one, one_pow, one_mul] using
        principalK_partition_finiteConstantTerm_one_zero d hd)
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  simpa only [Nat.cast_one, Int.cast_one, one_pow, one_mul,
    Int.cast_add, Int.cast_mul, Int.cast_natCast] using hmod

/-- The original coefficient lemma for the actual integral principal-form rows.
No squarefreeness hypothesis is imposed on `d`. The normalization is
`H_d = q^(-d/24) - a(d) q^(1/24) + …` and `K_d` has unit principal pole.
The proof uses the named signed Gauss evaluation and the separately admitted
eta transformation and shadow literature inputs.
[rolenManuscript, label lem:coeff] -/
theorem square_coefficient_relation
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (sign : ℤ)
    (hsign : sign = 1 ∨ sign = -1) (d : ℕ) (hdPos : 0 < d)
    (hd : d % 24 = 23) (hr : legendreSym p (-(d : ℤ)) = sign)
    (hspt : ∀ j : ℕ, legendreSym p (1 - 24 * (j : ℤ)) = sign → p ∣ spt j)
    (m : ℕ) (hmPos : 0 < m) (hmCop : m.Coprime (6 * p)) :
    (p : ℤ) ∣ (m : ℤ) ^ 2 * principalHFourier d (fFourier d) ((m : ℤ) ^ 2) +
      (d : ℤ) * principalKFourier d ((m : ℤ) ^ 2) := by
  have hsptMod : ∀ j : ℕ, legendreSym p (1 - 24 * (j : ℤ)) = sign →
      ((spt j : ℤ) : ZMod p) = 0 := by
    intro j hj
    simpa only [Int.cast_natCast] using
      (ZMod.natCast_eq_zero_iff (spt j) p).mpr (hspt j hj)
  exact square_coefficient_relation_of_signedGauss p hp5 sign hsign d hdPos hd hr
    hsptMod (fun q hqPrime hq5 =>
      letI : Fact q.Prime := hqPrime
      quadraticGaussSum_positivePhase q (by omega)) m hmPos hmCop

end SptClassification.QSeries
