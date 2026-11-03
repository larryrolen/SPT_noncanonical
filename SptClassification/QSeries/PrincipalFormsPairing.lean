/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.ConstantTermPairing
public import SptClassification.QSeries.PrincipalFormsCoefficients

/-!
# Finite pairings with the prescribed principal forms

The integer Fourier rows of the actual forms `H_d` and `K_d` give the two
finite coefficient pairings in [rolenManuscript, §3, equations (H), (K),
(ct1), and (ct2)]. Vanishing of the weight-two product constant terms is a
separate analytic premise. The untransformed `H_d f` cancellation is purely
coefficient algebra.
-/

public section

namespace SptClassification.QSeries

private theorem pairingPrimeWord_prod_pos (ps : List ℕ)
    (hps : ∀ p ∈ ps, p.Prime) : 0 < ps.prod := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    have hp : p.Prime := hps p (by simp)
    have ht : ∀ q ∈ ps, q.Prime := fun q hq => hps q (by simp [hq])
    simpa only [List.prod_cons] using Nat.mul_pos hp.pos (ih ht)

/-- The prescribed leading coefficient of `H_d`, viewed in the rational
coefficient ring used by the Hecke pairings. -/
theorem principalHFourier_rat_neg_d (d : ℕ) (hd : d % 24 = 23) :
    (principalHFourier d (fFourier d) (-(d : ℤ)) : ℚ) = 1 := by
  have hdPos : 0 < d := by omega
  rw [principalHFourier_negative d hd _ _ (by omega)]
  simp

/-- The prescribed leading coefficient of `K_d`, in the same ring. -/
theorem principalKFourier_rat_neg_d (d : ℕ) (hd : d % 24 = 23) :
    (principalKFourier d (-(d : ℤ)) : ℚ) = 1 := by
  have hdPos : 0 < d := by omega
  rw [principalKFourier_negative d hd _ (by omega)]
  simp

/-- The constant coefficient of the untransformed `H_d f` vanishes by its
two contributing Fourier terms `a(d)` and `-a(d)`. -/
theorem principalH_f_finiteConstantTerm_zero (d : ℕ) (hd : d % 24 = 23) :
    finiteConstantTerm (constantTermIndices 1 d)
      (fun r => (fFourier r : ℚ))
      (fun r => (principalHFourier d (fFourier d) r : ℚ)) = 0 := by
  have hdPos : 0 < d := by omega
  rw [finiteConstantTerm_divisorSquares hdPos]
  simp [principalHFourier_rat_neg_d d hd, principalHFourier_one d hd]

/-- The first finite pairing with the exact Fourier coefficients of `H_d`. -/
theorem principalH_hecke_finiteConstantTerm (ps : List ℕ)
    (hps : ∀ p ∈ ps, p.Prime) (d : ℕ) (hd : d % 24 = 23) :
    finiteConstantTerm (constantTermIndices ps.prod d)
      (heckeThreeHalfWord ps (fun r => (fFourier r : ℚ)))
      (fun r => (principalHFourier d (fFourier d) r : ℚ)) =
      heckeThreeHalfWord ps (fun r => (fFourier r : ℚ)) d +
        ∑ t ∈ ps.prod.divisors,
          (heckePrincipalCoefficient ps t : ℚ) *
            (principalHFourier d (fFourier d) ((t : ℤ) ^ 2) : ℚ) := by
  exact heckeThreeHalf_finiteConstantTerm ps hps (by omega)
    _ (principalHFourier_rat_neg_d d hd)

/-- The second finite pairing with the exact Fourier coefficients of `K_d`. -/
theorem principalK_hecke_finiteConstantTerm (ps : List ℕ)
    (hps : ∀ p ∈ ps, p.Prime) (d : ℕ) (hd : d % 24 = 23) :
    finiteConstantTerm (constantTermIndices ps.prod d)
      (fun r => (ps.prod : ℚ) ^ 2 *
        heckeMinusHalfWord ps (fun s => (partitionFourier s : ℚ)) r)
      (fun r => (principalKFourier d r : ℚ)) =
      (ps.prod : ℚ) ^ 2 *
        heckeMinusHalfWord ps (fun s => (partitionFourier s : ℚ)) d +
        ∑ t ∈ ps.prod.divisors,
          ((heckePrincipalCoefficient ps t : ℚ) / (t : ℚ) ^ 2) *
            (principalKFourier d ((t : ℤ) ^ 2) : ℚ) := by
  exact heckeMinusHalf_finiteConstantTerm ps hps (by omega)
    _ (principalKFourier_rat_neg_d d hd)

/-- Every product term outside the finite support of the first pairing
vanishes for the actual prescribed `H_d` Fourier row. -/
theorem principalH_hecke_product_zero_outside (ps : List ℕ)
    (hps : ∀ p ∈ ps, p.Prime) (d : ℕ) (hd : d % 24 = 23)
    (r : ℤ) (hr : r ∉ constantTermIndices ps.prod d) :
    heckeThreeHalfWord ps (fun s => (fFourier s : ℚ)) r *
      (principalHFourier d (fFourier d) (-r) : ℚ) = 0 := by
  apply coefficientProduct_zero_outside (m := ps.prod) (d := d) (r := r)
    (pairingPrimeWord_prod_pos ps hps)
    (heckeThreeHalfWord ps (fun s => (fFourier s : ℚ)))
    (fun s => (principalHFourier d (fFourier d) s : ℚ))
  · intro s hs hne
    have hneInt : heckeThreeHalfWordInt ps fFourier s ≠ 0 := by
      intro hz
      apply hne
      rw [← heckeThreeHalfWordInt_cast, hz]
      simp
    exact heckePrincipalCoefficient_support ps hps s hs hneInt
  · intro s hs hne
    by_contra hnot
    have hzero := principalHFourier_negative d hd (fFourier d) s hs
    simp only [ite_eq_right hnot] at hzero
    exact hne (by simp [hzero])
  · have hzero := (principalFourier_zero_of_mod_ne d (fFourier d) 0
      (by norm_num)).1
    simp [hzero]
  · exact hr

/-- Every product term outside the finite support of the second pairing
vanishes for the actual prescribed `K_d` Fourier row. -/
theorem principalK_hecke_product_zero_outside (ps : List ℕ)
    (hps : ∀ p ∈ ps, p.Prime) (d : ℕ) (hd : d % 24 = 23)
    (r : ℤ) (hr : r ∉ constantTermIndices ps.prod d) :
    ((ps.prod : ℚ) ^ 2 *
      heckeMinusHalfWord ps (fun s => (partitionFourier s : ℚ)) r) *
      (principalKFourier d (-r) : ℚ) = 0 := by
  apply coefficientProduct_zero_outside (m := ps.prod) (d := d) (r := r)
    (pairingPrimeWord_prod_pos ps hps)
    (fun s => (ps.prod : ℚ) ^ 2 *
      heckeMinusHalfWord ps (fun t => (partitionFourier t : ℚ)) s)
    (fun s => (principalKFourier d s : ℚ))
  · exact heckeMinusHalfWord_scaled_support ps hps
  · intro s hs hne
    by_contra hnot
    have hzero := principalKFourier_negative d hd s hs
    simp only [ite_eq_right hnot] at hzero
    exact hne (by simp [hzero])
  · have hzero := (principalFourier_zero_of_mod_ne d (fFourier d) 0
      (by norm_num)).2
    simp [hzero]
  · exact hr

/-- The two coefficient identities of [rolenManuscript, eqs. (ct1), (ct2)]
follow once the actual weight-two products have zero constant coefficient. -/
theorem principalForms_hecke_coefficients_of_constantTerms_zero
    (ps : List ℕ) (hps : ∀ p ∈ ps, p.Prime)
    (d : ℕ) (hd : d % 24 = 23)
    (hH : finiteConstantTerm (constantTermIndices ps.prod d)
      (heckeThreeHalfWord ps (fun r => (fFourier r : ℚ)))
      (fun r => (principalHFourier d (fFourier d) r : ℚ)) = 0)
    (hK : finiteConstantTerm (constantTermIndices ps.prod d)
      (fun r => (ps.prod : ℚ) ^ 2 *
        heckeMinusHalfWord ps (fun s => (partitionFourier s : ℚ)) r)
      (fun r => (principalKFourier d r : ℚ)) = 0) :
    heckeThreeHalfWord ps (fun r => (fFourier r : ℚ)) d =
        -∑ t ∈ ps.prod.divisors,
          (heckePrincipalCoefficient ps t : ℚ) *
            (principalHFourier d (fFourier d) ((t : ℤ) ^ 2) : ℚ) ∧
      (ps.prod : ℚ) ^ 2 *
        heckeMinusHalfWord ps (fun s => (partitionFourier s : ℚ)) d =
          -∑ t ∈ ps.prod.divisors,
            ((heckePrincipalCoefficient ps t : ℚ) / (t : ℚ) ^ 2) *
              (principalKFourier d ((t : ℤ) ^ 2) : ℚ) := by
  constructor
  · exact heckeThreeHalf_coefficient_of_constantTerm_zero ps hps (by omega)
      _ (principalHFourier_rat_neg_d d hd) hH
  · exact heckeMinusHalf_coefficient_of_constantTerm_zero ps hps (by omega)
      _ (principalKFourier_rat_neg_d d hd) hK

end SptClassification.QSeries
