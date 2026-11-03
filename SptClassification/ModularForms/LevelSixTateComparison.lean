/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.LevelSixSerreExpansion
public import SptClassification.ModularForms.EtaQuotientExpansionIntegral
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Tactic.Ring

/-!
# The eta cusp as an actual framed Tate chart

The eta parameter is a Laurent series with a simple pole. Rescaling the
Weierstrass equation by the cusp parameter gives an integral nodal model.
The split multiplicative comparison retains a square root of `-12` in the
coefficient field; no descent of this differential frame is asserted.
-/

public noncomputable section

namespace SptClassification.LevelSixTateComparison

open LevelSixSerreExpansion LevelSixTateSections LevelSixModularSections

variable (K : Type*) [Field K]

/-- The integral eta Euler unit, reduced to the coefficient field. -/
def etaUnit : PowerSeries K :=
  PowerSeries.map (Int.castRingHom K) levelSixFormalEulerUnit

@[simp] theorem etaUnit_constantCoeff : PowerSeries.constantCoeff (etaUnit K) = 1 := by
  rw [etaUnit, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, levelSixFormalEulerUnit_constantCoeff,
    map_one]

/-- The actual formal eta coordinate `q⁻¹ U(q)`. -/
def etaParameter : LaurentSeries K :=
  HahnSeries.single (-1) 1 * tateBase K (etaUnit K)

/-- The cusp uniformizer in the Laurent algebra. -/
def q : LaurentSeries K := tateBase K PowerSeries.X

@[simp] theorem q_mul_etaParameter : q K * etaParameter K = tateBase K (etaUnit K) := by
  simp [q, etaParameter, tateBase_apply, ← mul_assoc, HahnSeries.single_mul_single]

@[simp] theorem etaParameter_coeff_neg_one : (etaParameter K).coeff (-1) = 1 := by
  simp only [etaParameter, HahnSeries.coeff_single_mul, sub_self, one_mul, tateBase_apply]
  have h : ((HahnSeries.ofPowerSeries ℤ K) (etaUnit K)).coeff 0 =
      PowerSeries.coeff 0 (etaUnit K) := HahnSeries.ofPowerSeries_apply_coeff (etaUnit K) 0
  rw [h, PowerSeries.coeff_zero_eq_constantCoeff_apply, etaUnit_constantCoeff]

/-- The pole excludes every constant coordinate, in particular all three
singular finite fibers. -/
theorem etaParameter_ne_constant (a : K) : etaParameter K ≠ constants K a := by
  intro h
  have hc := congrArg (fun F : LaurentSeries K => F.coeff (-1)) h
  simpa [constants_apply] using hc

/-- The integral model obtained by the change `x=q⁻²x', y=q⁻³y'`. -/
def cuspCurve : WeierstrassCurve (PowerSeries K) where
  a₁ := 10 * etaUnit K + 72 * PowerSeries.X
  a₂ := 8 * etaUnit K * (etaUnit K + 9 * PowerSeries.X)
  a₃ := 72 * etaUnit K * (etaUnit K + 9 * PowerSeries.X) *
    (etaUnit K + 8 * PowerSeries.X)
  a₄ := 0
  a₆ := 0

/-- The rescaling is an admissible variable change over Laurent series. -/
def cuspChange : WeierstrassCurve.VariableChange (LaurentSeries K) :=
  ⟨(Units.mk0 (q K) (by
    simpa [q, tateBase_apply] using
      (show (HahnSeries.single (1 : ℤ) (1 : K) : LaurentSeries K) ≠ 0 by simp)))⁻¹,
    0, 0, 0⟩

theorem cuspChange_curve :
    cuspChange K • LevelSixWeierstrass.curve (etaParameter K) =
      (cuspCurve K).map (tateBase K) := by
  have ht := q_mul_etaParameter K
  ext1 <;> simp [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
    WeierstrassCurve.variableChange_a₆, cuspChange, cuspCurve, WeierstrassCurve.map, map_ofNat]
  all_goals
    rw [← ht]
    simp only [show tateBase K PowerSeries.X = q K from rfl]
    ring

theorem cuspCurve_c₄_constant :
    PowerSeries.constantCoeff (cuspCurve K).c₄ = 144 := by
  simp [cuspCurve, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, map_ofNat]
  <;> ring

theorem cuspCurve_c₆_constant :
    PowerSeries.constantCoeff (cuspCurve K).c₆ = 1728 := by
  simp [cuspCurve, WeierstrassCurve.c₆, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, map_ofNat]
  <;> ring

theorem cuspCurve_discriminant_constant :
    PowerSeries.constantCoeff (cuspCurve K).Δ = 0 := by
  simp [cuspCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈, map_ofNat]
  <;> ring

/-- The simple pole makes every finite singular parameter impossible. -/
theorem eta_discriminant_ne_zero (h6 : (6 : K) ≠ 0) :
    (LevelSixWeierstrass.curve (etaParameter K)).Δ ≠ 0 := by
  have h6' : (6 : LaurentSeries K) ≠ 0 := by
    intro h
    apply h6
    apply (constants K).injective
    simpa only [map_ofNat, map_zero] using h
  rw [Ne, LevelSixWeierstrass.discriminant_eq_zero_iff _ h6']
  have h0 := etaParameter_ne_constant K 0
  have h8 := etaParameter_ne_constant K (-8)
  have h9 := etaParameter_ne_constant K (-9)
  simpa only [map_zero, map_neg, map_ofNat, not_or] using And.intro h0 (And.intro h8 h9)

/-- Rescaling preserves the nonsingular generic fiber. -/
theorem cuspCurve_discriminant_ne_zero (h6 : (6 : K) ≠ 0) :
    (cuspCurve K).Δ ≠ 0 := by
  intro h
  have heq := congrArg WeierstrassCurve.Δ (cuspChange_curve K)
  simp only [WeierstrassCurve.variableChange_Δ, WeierstrassCurve.map_Δ, h, map_zero] at heq
  exact (mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) (eta_discriminant_ne_zero K h6)) heq

/-- Formal version of the eta covering identity [maier2009], §3.1 Table 2,
p.11 and §3.2 Table 4, p.12 (arXiv v4), with Maier's parameter `72/t`.
This is the denominator-cleared identity on the actual integral Euler series
and canonical Tate invariants, not a framed or marked isomorphism assertion.
The formal formulation follows by the convergent complex expansions and
coefficient equality over `ℤ[1/6]`, then reduction to `K`. It is a derived
literature interface; the source table itself is a complex function identity. -/
theorem eta_tate_invariant_literature (h6 : (6 : K) ≠ 0) :
    (tateCurve K).c₄ ^ 3 * (cuspCurve K).Δ =
      (cuspCurve K).c₄ ^ 3 * (tateCurve K).Δ := by
  sorry

/-- Split multiplicative Tate uniformization over `K((q))`, in integral
Weierstrass coordinates; [silverman1994], Chapter V, Theorem 3.1 (Tate
uniformization and characterization by split multiplicative reduction).
The nonzero discriminant and unit `c₄` specify multiplicative reduction;
`r² c₄(0) = -c₆(0)` retains the splitting condition. Equality of invariants
identifies the Tate parameter with this very `q`. This is the formal-DVR
specialization of the theorem, not a statement that equal `j` alone gives
an isomorphism over an arbitrary field. No Hasse or Serre value is assumed. -/
theorem split_multiplicative_tate_comparison_literature
    (h6 : (6 : K) ≠ 0) (W : WeierstrassCurve (PowerSeries K))
    (hΔ : W.Δ ≠ 0) (hΔ₀ : PowerSeries.constantCoeff W.Δ = 0)
    (hc₄ : PowerSeries.constantCoeff W.c₄ ≠ 0)
    (r : K) (hr : r ^ 2 * PowerSeries.constantCoeff W.c₄ =
      -PowerSeries.constantCoeff W.c₆)
    (hj : (tateCurve K).c₄ ^ 3 * W.Δ = W.c₄ ^ 3 * (tateCurve K).Δ) :
    ∃ Cw : WeierstrassCurve.VariableChange (LaurentSeries K),
      Cw • W.map (tateBase K) = (tateCurve K).map (tateBase K) := by
  sorry

/-- An actual change to the canonical Tate curve for the eta coordinate.
The square root supplies exactly the split tangent cone of the integral cusp. -/
theorem exists_eta_change (h6 : (6 : K) ≠ 0) (r : K) (hr : r ^ 2 = -12) :
    ∃ Cw : WeierstrassCurve.VariableChange (LaurentSeries K),
      Cw • LevelSixWeierstrass.curve (etaParameter K) =
        (tateCurve K).map (tateBase K) := by
  have h144 : (144 : K) ≠ 0 := by
    have h23 : (2 : K) * 3 ≠ 0 := by norm_num; exact h6
    have h2 := (mul_ne_zero_iff.mp h23).1
    have h3 := (mul_ne_zero_iff.mp h23).2
    convert mul_ne_zero (pow_ne_zero 4 h2) (pow_ne_zero 2 h3) using 1 <;> norm_num
  obtain ⟨Cw, hCw⟩ := split_multiplicative_tate_comparison_literature K h6
    (cuspCurve K) (cuspCurve_discriminant_ne_zero K h6)
    (cuspCurve_discriminant_constant K)
    (by rwa [cuspCurve_c₄_constant]) r
    (by rw [cuspCurve_c₄_constant, cuspCurve_c₆_constant, hr]; ring)
    (eta_tate_invariant_literature K h6)
  refine ⟨Cw * cuspChange K, ?_⟩
  rw [mul_smul, cuspChange_curve, hCw]

/-- The chosen actual eta chart, with its differential frame and Laurent target.
No arbitrary evaluation on a rational-function field is involved. -/
def etaRealization (h6 : (6 : K) ≠ 0) (r : K) (hr : r ^ 2 = -12) :
    TateRealization (K := K) (S := LaurentSeries K) where
  base := tateBase K
  parameter := etaParameter K
  change := (exists_eta_change K h6 r hr).choose
  equation := (exists_eta_change K h6 r hr).choose_spec

@[simp] theorem etaRealization_base (h6 : (6 : K) ≠ 0) (r : K) (hr : r ^ 2 = -12) :
    (etaRealization K h6 r hr).base = tateBase K := (rfl)

@[simp] theorem etaRealization_parameter (h6 : (6 : K) ≠ 0) (r : K) (hr : r ^ 2 = -12) :
    (etaRealization K h6 r hr).parameter = etaParameter K := (rfl)

/-- The polynomial discriminant remains nonzero after the actual cusp substitution. -/
theorem eta_eval_discriminant_ne_zero (h6 : (6 : K) ≠ 0) :
    (LevelSixWeierstrass.curve (Polynomial.X : Polynomial K)).Δ.eval₂
      (constants K) (etaParameter K) ≠ 0 := by
  have h := eta_discriminant_ne_zero K h6
  rw [← map_curve (etaParameter K), WeierstrassCurve.map_Δ] at h
  exact h

/-- Fourier Serre comparison specialized to this particular eta cusp and frame. -/
theorem eta_expansion_serre (h6 : (6 : K) ≠ 0) (r : K) (hr : r ^ 2 = -12)
    (k : ℕ) (F : SectionRing K) (hF : IsWeight k F) :
    (etaRealization K h6 r hr).expansion (serreSection k F) =
      theta K ((etaRealization K h6 r hr).expansion F) -
        (k : LaurentSeries K) / 12 * eisensteinTwo K *
          (etaRealization K h6 r hr).expansion F := by
  apply expansion_serreSection h6 _ (etaRealization_base K h6 r hr) _ k F hF
  simpa only [etaRealization_parameter] using eta_eval_discriminant_ne_zero K h6

/-- The existing geometric coordinate section is the Fourier derivative
of the eta parameter, with the differential-frame cancellation included. -/
theorem eta_expansion_coordinateSection
    (h6 : (6 : K) ≠ 0) (r : K) (hr : r ^ 2 = -12) :
    (etaRealization K h6 r hr).expansion coordinateSection =
      theta K (etaParameter K) := by
  have h := expansion_coordinateSection h6 (etaRealization K h6 r hr)
    (etaRealization_base K h6 r hr)
    (by simpa only [etaRealization_parameter] using eta_eval_discriminant_ne_zero K h6)
  simpa only [etaRealization_parameter] using h

/-- The actual Hasse section is one in the chosen eta frame. -/
theorem eta_expansion_hasse (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 3 < p)
    (h6 : (6 : K) ≠ 0) (r : K) (hr : r ^ 2 = -12) :
    (etaRealization K h6 r hr).expansion (LevelSixHasseGeometry.hasseSection p) = 1 := by
  letI : CharP (LaurentSeries K) p :=
    ((constants K).charP_iff_charP p).mp inferInstance
  exact (etaRealization K h6 r hr).expansion_hasse p hp

/-- The same frame sends `12 D H` to the normalized weight-two Eisenstein series. -/
theorem eta_expansion_serreHasse (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 3 < p)
    (h6 : (6 : K) ≠ 0) (r : K) (hr : r ^ 2 = -12) :
    (etaRealization K h6 r hr).expansion (LevelSixHasseGeometry.serreHasseSection p) =
      eisensteinTwo K := by
  apply expansion_serreHasse p hp h6 _ (etaRealization_base K h6 r hr)
  simpa only [etaRealization_parameter] using eta_eval_discriminant_ne_zero K h6

end SptClassification.LevelSixTateComparison
