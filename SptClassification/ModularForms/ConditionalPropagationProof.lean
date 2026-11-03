/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.PrimeLocalNormalizedProduct

/-!
# Propagation from the actual normalized approximation

The modular progression transport applies to the Fourier residue row obtained
from the analytically identified normalized form. The arithmetic deduction
uses the auxiliary prime and square-class transport of [rolenManuscript, Lemma 1].
-/

public section

namespace SptClassification

/-- The source progression vanishes at every Fourier index, including indices
outside the support and negative indices. -/
private theorem sptFourier_zero_on_simple_progression (p b : ℕ)
    (hp : p.Prime) (hfive : 5 ≤ p) (hb : b < p)
    (hspt : ∀ n : ℕ, p ∣ spt (p * n + b))
    (r : ℤ)
    (hr : (r : ZMod (24 * p)) =
      (24 * (b : ZMod (24 * p)) - 1)) :
    (QSeries.sptFourier r : ZMod p) = 0 := by
  classical
  by_cases hsupport : ∃ n : ℕ, r = 24 * (n : ℤ) - 1
  · obtain ⟨n, hn⟩ := hsupport
    subst r
    have hcast := congrArg
      (ZMod.castHom (by exact ⟨24, by ring⟩ : p ∣ 24 * p) (ZMod p)) hr
    have h24eq : (24 : ZMod p) * n - 1 = (24 : ZMod p) * b - 1 := by
      have hcast24 : ZMod.cast (24 : ZMod (24 * p)) = (24 : ZMod p) := by
        exact ZMod.cast_natCast (by exact ⟨24, by ring⟩ : p ∣ 24 * p) 24
      norm_num at hcast ⊢
      simpa only [hcast24] using hcast
    have h24unit : IsUnit (24 : ZMod p) :=
      (ZMod.isUnit_iff_coprime 24 p).mpr
        (prime_coprime_twentyFour hp hfive).symm
    have hnmod : Nat.ModEq p n b := by
      rw [← ZMod.natCast_eq_natCast_iff]
      apply h24unit.mul_left_cancel
      calc
        (24 : ZMod p) * n = ((24 : ZMod p) * n - 1) + 1 := by ring
        _ = ((24 : ZMod p) * b - 1) + 1 := by rw [h24eq]
        _ = (24 : ZMod p) * b := by ring
    have hnrem : n % p = b := by
      simpa [Nat.ModEq, Nat.mod_eq_of_lt hb] using hnmod
    have hnrep : n = p * (n / p) + b := by
      have hdiv := Nat.mod_add_div n p
      omega
    rw [QSeries.sptFourier_at, hnrep]
    simpa only [Int.cast_natCast] using
      (ZMod.natCast_eq_zero_iff (spt (p * (n / p) + b)) p).2 (hspt (n / p))
  · simp [QSeries.sptFourier, QSeries.shiftedTwentyFour, hsupport]

/-- Coprimality with the CRT modulus extends to every level dividing
`576 Q⁴`; no exclusion `p ∤ M` is used. -/
private theorem coprime_progression_level {p Q a N₀ : ℕ}
    (ha : a.Coprime (6 * p * Q)) (haQ : Nat.ModEq (24 * Q) a 1)
    (hlevel : N₀ ∣ 576 * Q ^ 4) :
    a.Coprime (6 * (24 * p) * N₀) := by
  have hac24Q : a.Coprime (24 * Q) := by
    have hcast : (a : ZMod (24 * Q)) = 1 := by
      have hcast' : (a : ZMod (24 * Q)) = ((1 : ℕ) : ZMod (24 * Q)) := by
        rw [ZMod.natCast_eq_natCast_iff]
        exact haQ
      simpa using hcast'
    exact (ZMod.isUnit_iff_coprime a (24 * Q)).mp
      (by rw [hcast]; exact isUnit_one)
  have ha24 : a.Coprime 24 :=
    Nat.Coprime.of_dvd_right (dvd_mul_right 24 Q) hac24Q
  have ha6 : a.Coprime 6 :=
    Nat.Coprime.of_dvd_right (by exact ⟨p * Q, by ring⟩) ha
  have hap : a.Coprime p :=
    Nat.Coprime.of_dvd_right (by exact ⟨6 * Q, by ring⟩) ha
  have haQ' : a.Coprime Q :=
    Nat.Coprime.of_dvd_right (dvd_mul_left Q (6 * p)) ha
  have ha576 : a.Coprime 576 := by
    convert ha24.pow_right 2 using 1
  have haN₀ : a.Coprime N₀ :=
    Nat.Coprime.of_dvd_right hlevel
      (ha576.mul_right (haQ'.pow_right 4))
  convert (ha6.mul_right (ha24.mul_right hap)).mul_right haN₀ using 1

/-- Conditional form of the manuscript's propagation lemma. The conclusion
uses the actual partition-based smallest-parts function. -/
theorem propagation_of_approximation_transport (p b : ℕ) (hp : p.Prime)
    (hfive : 5 ≤ p) (hb : b < p)
    (hnotcanonical : ((24 * (b : ℤ) - 1 : ℤ) : ZMod p) ≠ 0)
    (hspt : ∀ n : ℕ, p ∣ spt (p * n + b))
    (approximation : SptApproximationInput p hfive)
    (transport : ∀ (Q : ℕ) (hQ : Q.Prime) (hQavoid : ¬ Q ∣ 6 * p),
      letI : Fact Q.Prime := ⟨hQ⟩
      let g := (approximation.forPrime Q hQ hQavoid).form
      ∀ (M : ℕ) (_hM : 0 < M) (u : ℤ) (a : ℕ),
        a.Coprime (6 * M * g.level) →
        (∀ r : ℤ, (r : ZMod M) = (u : ZMod M) → g.coeffMod r = 0) →
        ∀ r : ℤ, (r : ZMod M) = (a : ZMod M) ^ 2 * (u : ZMod M) →
          g.coeffMod r = 0)
    (N : ℕ)
    (hclass : @legendreSym p ⟨hp⟩ (1 - 24 * (N : ℤ)) =
      @legendreSym p ⟨hp⟩ (1 - 24 * (b : ℤ))) :
    p ∣ spt N := by
  by_cases hN : N = 0
  · subst N
    simp
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, hQ, hQavoid, hQleg⟩ := exists_auxiliary_prime hp.pos hNpos
  let : Fact Q.Prime := ⟨hQ⟩
  have hbnonzero : legendreSym p (1 - 24 * (b : ℤ)) ≠ 0 := by
    intro hz
    have hzcast : ((1 - 24 * (b : ℤ) : ℤ) : ZMod p) = 0 :=
      (legendreSym.eq_zero_iff p _).mp hz
    apply hnotcanonical
    calc
      ((24 * (b : ℤ) - 1 : ℤ) : ZMod p) =
          -((1 - 24 * (b : ℤ) : ℤ) : ZMod p) := by push_cast; ring
      _ = 0 := by rw [hzcast]; ring
  obtain ⟨a, hacop, ha24Q, hasquare⟩ :=
    exists_progression_square_transport p hfive hQ hQavoid hbnonzero hclass.symm
  let A := approximation.forPrime Q hQ hQavoid
  have haLevel : a.Coprime (6 * (24 * p) * A.form.level) :=
    coprime_progression_level hacop ha24Q A.level_divides
  have hzero : ∀ r : ℤ, (r : ZMod (24 * p)) =
      ((24 * (b : ℤ) - 1 : ℤ) : ZMod (24 * p)) → A.form.coeffMod r = 0 := by
    intro r hr
    rw [A.form_coeffMod_eq_twistedS, QSeries.sptTwistedLaurent_coeff]
    split_ifs
    · exact sptFourier_zero_on_simple_progression p b hp hfive hb hspt r (by
        convert hr using 1
        push_cast
        ring)
    · rfl
  have htransport := transport Q hQ hQavoid (24 * p) (by positivity)
    (24 * (b : ℤ) - 1) a haLevel hzero (24 * (N : ℤ) - 1)
  have htarget : ((24 * (N : ℤ) - 1 : ℤ) : ZMod (24 * p)) =
      (a : ZMod (24 * p)) ^ 2 *
        ((24 * (b : ℤ) - 1 : ℤ) : ZMod (24 * p)) := by
    simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat,
      Int.cast_one] using hasquare
  have hzeroN := htransport htarget
  rw [A.form_coeffMod_eq_twistedS, QSeries.sptTwistedLaurent_coeff] at hzeroN
  have hsel : legendreSym Q (-(24 * (N : ℤ) - 1)) = -1 := by
    convert hQleg using 1
    ring_nf
  simp only [hsel, ↓ite_true, QSeries.sptFourier_at] at hzeroN
  exact (ZMod.natCast_eq_zero_iff (spt N) p).1 (by
    simpa only [Int.cast_natCast] using hzeroN)

/-- The original explicit-parameter propagation API, retained as a specialization
of transport for the supplied approximations. -/
theorem conditional_propagation (p b : ℕ) (hp : p.Prime)
    (hfive : 5 ≤ p) (hb : b < p)
    (hnotcanonical : ((24 * (b : ℤ) - 1 : ℤ) : ZMod p) ≠ 0)
    (hspt : ∀ n : ℕ, p ∣ spt (p * n + b))
    (inputs : ProgressionInputs p hfive)
    (N : ℕ)
    (hclass : @legendreSym p ⟨hp⟩ (1 - 24 * (N : ℤ)) =
      @legendreSym p ⟨hp⟩ (1 - 24 * (b : ℤ))) :
    p ∣ spt N :=
  propagation_of_approximation_transport p b hp hfive hb hnotcanonical hspt
    inputs.approximation (fun Q hQ hQavoid => by
      letI : Fact Q.Prime := ⟨hQ⟩
      exact inputs.transport.transport (inputs.approximation.forPrime Q hQ hQavoid).form)
    N hclass

end SptClassification
