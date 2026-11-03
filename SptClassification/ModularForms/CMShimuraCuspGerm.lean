/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.CMShimuraNomeGerm
public import SptClassification.ModularForms.CMShimuraLift
public import SptClassification.ModularForms.CMActualCuspClearing

/-!
# The principal Shimura lift at the actual infinity cusp

The independently lifted Fourier row converges above some height. A point
in that region determines an analytic nome germ. Multiplication by the
actual oriented CM polynomials and discriminant clears its cusp pole.
-/

public section

namespace SptClassification

/-- The principal complex lift has an analytic nome germ on a smaller cusp
disc. Its actual CM and discriminant pole clearing has an analytic germ as
well, and the germ agrees with the lift on the overlap with the high cusp.
[rolenManuscript, Section 4, proof of Proposition 4.1] -/
theorem principalCMShimuraLift_actual_cusp_germ (d : ℕ)
    [Fact (-(d : ℤ) < 0)] (hD : (-(d : ℤ)) % 24 = 1)
    (F : ℂ → ℂ) (Y : ℝ)
    (hsum : ∀ z : UpperHalfPlane, Y < z.im →
      HasSum (fun n : ℕ =>
        ((integralPrincipalShimuraLambertSeries d).coeff n : ℂ) *
          Function.Periodic.qParam 1 z ^ n) (F z))
    (z₀ : UpperHalfPlane) (hz₀ : Y < z₀.im) :
    ∃ J G : ℂ → ℂ,
      (∀ q : ℂ, ‖q‖ < ‖Function.Periodic.qParam 1 z₀‖ → AnalyticAt ℂ J q) ∧
      (∀ q : ℂ, ‖q‖ < ‖Function.Periodic.qParam 1 z₀‖ →
        ‖q‖ < 1 → AnalyticAt ℂ G q) ∧
      J 0 = 0 ∧ G 0 = 0 ∧
      (∀ z : UpperHalfPlane, Y < z.im →
        ‖Function.Periodic.qParam 1 z‖ <
          ‖Function.Periodic.qParam 1 z₀‖ →
          J (Function.Periodic.qParam 1 z) = F z ∧
          G (Function.Periodic.qParam 1 z) =
            ((cmClassPolynomialA (-(d : ℤ))).eval (levelSixEtaQuotient z) *
              (cmClassPolynomialB (-(d : ℤ))).eval (levelSixEtaQuotient z)) ^ 2 *
              ModularForm.discriminant z ^
                (8 * formClassNumber (-(d : ℤ))) * F z) := by
  let c : ℕ → ℂ := fun n =>
    ((integralPrincipalShimuraLambertSeries d).coeff n : ℂ)
  let q₀ := Function.Periodic.qParam 1 z₀
  have hq₀ : q₀ ≠ 0 := Complex.exp_ne_zero _
  obtain ⟨J, hJ, hJsum⟩ :=
    analytic_nome_germ_of_hasSum_at_nonzero c q₀ hq₀ (by
      simpa only [c, q₀] using (hsum z₀ hz₀).summable.hasSum)
  let G : ℂ → ℂ := fun q => cmActualCuspClearingFactor (-(d : ℤ)) q * J q
  have hG : ∀ q : ℂ, ‖q‖ < ‖q₀‖ → ‖q‖ < 1 → AnalyticAt ℂ G q := by
    intro q hq hq1
    have hFactor : AnalyticAt ℂ (cmActualCuspClearingFactor (-(d : ℤ))) q :=
      analyticAt_cmActualCuspClearingFactor_of_norm_lt_one (-(d : ℤ)) hq1
    convert hFactor.mul (hJ q hq) using 1
  have hJ0 : J 0 = 0 := by
    have hsum0 := hJsum 0 (by simpa only [norm_zero] using (norm_pos_iff.mpr hq₀))
    have heq : J 0 = c 0 := by
      simpa using hsum0.unique (hasSum_single 0 (by
        intro n hn
        simp [c, hn]))
    simpa [c, integralPrincipalShimuraLambertSeries_coeff_zero] using heq
  refine ⟨J, G, hJ, hG, hJ0, ?_, ?_⟩
  · simp [G, hJ0]
  intro z hz hq
  have hJq : J (Function.Periodic.qParam 1 z) = F z := by
    apply HasSum.unique (hJsum _ (by simpa only [q₀] using hq))
    simpa only [c] using hsum z hz
  refine ⟨hJq, ?_⟩
  change cmActualCuspClearingFactor (-(d : ℤ)) _ * J _ = _
  rw [cmActualCuspClearingFactor_qParam _ hD, hJq]

end SptClassification
