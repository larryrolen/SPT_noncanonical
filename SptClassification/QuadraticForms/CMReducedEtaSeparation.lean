/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.CMGoodReductionAction
public import SptClassification.QuadraticForms.OrientedPointKernelBound

/-! # Separation of the actual reduced eta values at every prime away from six -/

public section

namespace SptClassification.LevelSixForm

open LevelSixWeierstrass RationalPointMap

/-- A common reduced eta value would place the two oriented CM actions on the
same explicit curve and the same point of order six. Their kernel bound
contradicts the strict manuscript bound, for either splitting type. -/
theorem reduced_eta_values_ne_of_bound
    {D : ℤ} {r s : ZMod 12} [Fact (D < 0)]
    (Q : LevelSixForm D r) (R : LevelSixForm D s)
    (hQ : Q.b % 2 = 1) (hR : R.b % 2 = 1)
    (n : ℕ) (hn : 4 * (n : ℤ) = 1 - D)
    (t u : CMIntegralValues.Ring)
    (ht : CMIntegralValues.complexEmbedding t = levelSixEtaQuotient Q.cmPoint)
    (hu : CMIntegralValues.complexEmbedding u = levelSixEtaQuotient R.cmPoint)
    {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
    (p : ℕ) [Fact p.Prime] [CharP F p] (hp : 3 < p)
    (red : CMIntegralValues.Ring →+* F) (h6 : (6 : F) ≠ 0)
    (hbound : (1 - D) ^ 2 < 24 * (p : ℤ))
    (hr : r = 1 ∨ r = 11) (hs : s = 5 ∨ s = 7) : red t ≠ red u := by
  have hD : D < 0 := Fact.out
  have hnpos : 0 < n := by omega
  have hboundNat : 16 * n * n < 24 * p := by
    have h : (16 : ℤ) * n * n < 24 * p := by nlinarith [hbound]
    exact_mod_cast h
  have hnp : n < p := by
    by_contra h
    have hpn : p ≤ n := by omega
    have hsquare := Nat.mul_self_le_mul_self hpn
    nlinarith
  have hpn : ¬p ∣ n := Nat.not_dvd_of_pos_of_lt hnpos hnp
  have hEt := Q.integralEta_reduction_isElliptic hQ t ht red h6
  have hEu := R.integralEta_reduction_isElliptic hR u hu red h6
  have hΔt : (curve (red t)).Δ ≠ 0 := hEt.isUnit.ne_zero
  have hΔu : (curve (red u)).Δ ≠ 0 := hEu.isUnit.ne_zero
  obtain ⟨a, ha, hPa⟩ := Q.exists_reduced_eta_CM_action hQ n hn t ht p hp red h6 hΔt
  intro heq
  have hB (v : F) (hv : (curve v).Δ ≠ 0) (he : v = red u) :
      ∃ b : endomorphismRing (curve v),
        b * b - b + (n : endomorphismRing (curve v)) = 0 ∧
        pointAction _ b (sixPoint v hv) = ((R.b + 1) / 2 : ℤ) • sixPoint v hv := by
    subst v
    exact R.exists_reduced_eta_CM_action hR n hn u hu p hp red h6 hΔu
  obtain ⟨b, hb, hPb⟩ := hB (red t) hΔt heq
  have h := kernel_bound_of_oriented_point_actions p hp (curve (red t)) hEt
    (sixPoint (red t) hΔt) (sixPoint_order _ _) n hnpos hpn a b ha hb
    ((Q.b + 1) / 2) ((R.b + 1) / 2) hPa hPb
    (Q.generatorScalar_first_pair hr) (R.generatorScalar_second_pair hs)
  nlinarith

end SptClassification.LevelSixForm
