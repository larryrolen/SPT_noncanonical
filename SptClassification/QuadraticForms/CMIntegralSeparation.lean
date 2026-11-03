/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.CMReducedEtaSeparation

/-! # Coprimality of the actual oriented CM class polynomials -/

public section

namespace SptClassification.CMIntegralValues

open LevelSixWeierstrass RationalPointMap

/-- A common root of the actual integral class polynomials produces two
oriented actions on the same eta curve and its same point of order six.
The equations retain the trace-one CM polynomial; no inequality on the prime
or assumption of supersingularity is needed for this construction. -/
theorem common_root_oriented_actions
    (d p : ℕ) [Fact (-(d : ℤ) < 0)] [Fact p.Prime]
    [DecidableEq (AlgebraicClosure (ZMod p))]
    (hp6 : ¬p ∣ 6) (hp : 3 < p) (hmod : d % 24 = 23)
    (models : IntegralCMClassPolynomials d)
    (x : AlgebraicClosure (ZMod p))
    (ha : (Polynomial.aeval x) (models.modelA.map (cmCoefficientReduction p hp6)) = 0)
    (hb : (Polynomial.aeval x) (models.modelB.map (cmCoefficientReduction p hp6)) = 0) :
    ∃ hΔ : (curve x).Δ ≠ 0,
      ∃ a b : endomorphismRing (curve x), ∃ m k : ℤ,
        addOrderOf (sixPoint x hΔ) = 6 ∧
        a * a - a + ((d + 1) / 4 : ℕ) = 0 ∧
        b * b - b + ((d + 1) / 4 : ℕ) = 0 ∧
        pointAction _ a (sixPoint x hΔ) = m • sixPoint x hΔ ∧
        pointAction _ b (sixPoint x hΔ) = k • sixPoint x hΔ ∧
        (m % 6 = 0 ∨ m % 6 = 1) ∧ (k % 6 = 3 ∨ k % 6 = 4) := by
  have hn : 4 * (((d + 1) / 4 : ℕ) : ℤ) = 1 - (-(d : ℤ)) := by omega
  have h6 : (6 : AlgebraicClosure (ZMod p)) ≠ 0 := by
    exact fun h => hp6 ((CharP.cast_eq_zero_iff _ p 6).mp h)
  have hpair {r s : ZMod 12} (C : PrimitiveCMClass (-(d : ℤ)) r)
      (E : PrimitiveCMClass (-(d : ℤ)) s)
      (hr : r = 1 ∨ r = 11) (hs : s = 5 ∨ s = 7)
      (hC : reduction p hp6 (first models C hr) = x)
      (hE : reduction p hp6 (second models E hs) = x) :
      ∃ hΔ : (curve x).Δ ≠ 0,
      ∃ a b : endomorphismRing (curve x), ∃ m k : ℤ,
        addOrderOf (sixPoint x hΔ) = 6 ∧
        a * a - a + ((d + 1) / 4 : ℕ) = 0 ∧
        b * b - b + ((d + 1) / 4 : ℕ) = 0 ∧
        pointAction _ a (sixPoint x hΔ) = m • sixPoint x hΔ ∧
        pointAction _ b (sixPoint x hΔ) = k • sixPoint x hΔ ∧
        (m % 6 = 0 ∨ m % 6 = 1) ∧ (k % 6 = 3 ∨ k % 6 = 4) := by
    obtain ⟨Q, hQ⟩ := Quotient.exists_rep C.val
    obtain ⟨R, hR⟩ := Quotient.exists_rep E.val
    have hoddQ := Q.middle_coefficient_odd_of_product_orientation
      (hr.elim (fun h => Or.inl h) (fun h => Or.inr (Or.inr (Or.inr h))))
    have hoddR := R.middle_coefficient_odd_of_product_orientation
      (hs.elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr (Or.inl h))))
    have hvQ : complexEmbedding (first models C hr) = levelSixEtaQuotient Q.cmPoint := by
      rw [complexEmbedding_first, ← hQ, CMClass.etaValue_mk]
    have hvR : complexEmbedding (second models E hs) = levelSixEtaQuotient R.cmPoint := by
      rw [complexEmbedding_second, ← hR, CMClass.etaValue_mk]
    have hΔ : (curve x).Δ ≠ 0 := by
      rw [← hC]
      exact (Q.integralEta_reduction_isElliptic hoddQ _ hvQ (reduction p hp6) h6).isUnit.ne_zero
    have haction {j : ZMod 12} (T : LevelSixForm (-(d : ℤ)) j) (hodd : T.b % 2 = 1)
        (t : Ring) (ht : complexEmbedding t = levelSixEtaQuotient T.cmPoint)
        (v : AlgebraicClosure (ZMod p)) (hv : (curve v).Δ ≠ 0)
        (he : v = reduction p hp6 t) :
        ∃ a : endomorphismRing (curve v),
          a * a - a + ((d + 1) / 4 : ℕ) = 0 ∧
          pointAction _ a (sixPoint v hv) = ((T.b + 1) / 2 : ℤ) • sixPoint v hv := by
      subst v
      exact T.exists_reduced_eta_CM_action hodd _ hn t ht p hp (reduction p hp6) h6 hv
    obtain ⟨a, ha, hPa⟩ := haction Q hoddQ _ hvQ x hΔ hC.symm
    obtain ⟨b, hb, hPb⟩ := haction R hoddR _ hvR x hΔ hE.symm
    exact ⟨hΔ, a, b, (Q.b + 1) / 2, (R.b + 1) / 2, sixPoint_order _ _, ha, hb,
      hPa, hPb, Q.generatorScalar_first_pair hr, R.generatorScalar_second_pair hs⟩
  obtain ⟨hA, hB⟩ := common_root_classes d p hp6 models x ha hb
  rcases hA with ⟨C, hC⟩ | ⟨C, hC⟩ <;>
    rcases hB with ⟨E, hE⟩ | ⟨E, hE⟩
  · exact hpair C E (Or.inl rfl) (Or.inl rfl) hC hE
  · exact hpair C E (Or.inl rfl) (Or.inr rfl) hC hE
  · exact hpair C E (Or.inr rfl) (Or.inl rfl) hC hE
  · exact hpair C E (Or.inr rfl) (Or.inr rfl) hC hE

/-- Opposite primitive orientations have distinct reduced eta values under
 the manuscript bound, using the common integral closure and residue map. -/
theorem reduced_values_ne_of_bound
    (d p : ℕ) [Fact (-(d : ℤ) < 0)] [Fact p.Prime]
    [DecidableEq (AlgebraicClosure (ZMod p))]
    (hp6 : ¬p ∣ 6) (hp : 3 < p)
    (n : ℕ) (hn : 4 * (n : ℤ) = 1 + (d : ℤ))
    (hbound : (1 + (d : ℤ)) ^ 2 < 24 * (p : ℤ))
    (models : IntegralCMClassPolynomials d)
    {r s : ZMod 12} (C : PrimitiveCMClass (-(d : ℤ)) r)
    (E : PrimitiveCMClass (-(d : ℤ)) s)
    (hr : r = 1 ∨ r = 11) (hs : s = 5 ∨ s = 7) :
    reduction p hp6 (first models C hr) ≠ reduction p hp6 (second models E hs) := by
  obtain ⟨Q, hQ⟩ := Quotient.exists_rep C.val
  obtain ⟨R, hR⟩ := Quotient.exists_rep E.val
  have hoddQ := Q.middle_coefficient_odd_of_product_orientation
    (hr.elim (fun h => Or.inl h) (fun h => Or.inr (Or.inr (Or.inr h))))
  have hoddR := R.middle_coefficient_odd_of_product_orientation
    (hs.elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr (Or.inl h))))
  have hvQ : complexEmbedding (first models C hr) = levelSixEtaQuotient Q.cmPoint := by
    rw [complexEmbedding_first, ← hQ, CMClass.etaValue_mk]
  have hvR : complexEmbedding (second models E hs) = levelSixEtaQuotient R.cmPoint := by
    rw [complexEmbedding_second, ← hR, CMClass.etaValue_mk]
  have h6 : (6 : AlgebraicClosure (ZMod p)) ≠ 0 := by
    exact fun h => hp6 ((CharP.cast_eq_zero_iff _ p 6).mp h)
  exact Q.reduced_eta_values_ne_of_bound R hoddQ hoddR n (by simpa using hn)
    _ _ hvQ hvR p hp (reduction p hp6) h6 (by simpa using hbound) hr hs

/-- The manuscript polynomial separation follows from the actual integral
eta values and the named literature inputs. Both splitting types are covered;
no common-pair or specialization hypothesis is added. -/
theorem isCoprime_of_bound
    (d p : ℕ) [Fact (-(d : ℤ) < 0)] [Fact p.Prime]
    [DecidableEq (AlgebraicClosure (ZMod p))]
    (hp6 : ¬p ∣ 6) (hp : 3 < p) (hmod : d % 24 = 23)
    (hbound : (d + 1) ^ 2 < 24 * p)
    (models : IntegralCMClassPolynomials d) :
    IsCoprime (models.modelA.map (cmCoefficientReduction p hp6))
      (models.modelB.map (cmCoefficientReduction p hp6)) := by
  have hn : 4 * (((d + 1) / 4 : ℕ) : ℤ) = 1 + (d : ℤ) := by omega
  have hb : (1 + (d : ℤ)) ^ 2 < 24 * (p : ℤ) := by
    exact_mod_cast (show (1 + d) ^ 2 < 24 * p by simpa [Nat.add_comm] using hbound)
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
    (ZMod p) (AlgebraicClosure (ZMod p)) _ _).2
  intro x
  by_contra h
  push Not at h
  obtain ⟨ha, hb'⟩ := h
  obtain ⟨hA, hB⟩ := common_root_classes d p hp6 models x ha hb'
  have hne {r s : ZMod 12} (C : PrimitiveCMClass (-(d : ℤ)) r)
      (E : PrimitiveCMClass (-(d : ℤ)) s) :=
    reduced_values_ne_of_bound d p hp6 hp ((d + 1) / 4) hn hb
      models C E
  rcases hA with ⟨C, hC⟩ | ⟨C, hC⟩ <;>
    rcases hB with ⟨E, hE⟩ | ⟨E, hE⟩
  · exact hne C E (Or.inl rfl) (Or.inl rfl) (hC.trans hE.symm)
  · exact hne C E (Or.inl rfl) (Or.inr rfl) (hC.trans hE.symm)
  · exact hne C E (Or.inr rfl) (Or.inl rfl) (hC.trans hE.symm)
  · exact hne C E (Or.inr rfl) (Or.inr rfl) (hC.trans hE.symm)


end SptClassification.CMIntegralValues
