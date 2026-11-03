/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.EtaQuotientExpansion

/-!
# The holomorphic Euler unit near infinity

The Euler product is differentiable on the open unit disk. Its nonzero value
at zero therefore gives a neighborhood on which the level-six Euler quotient
is complex differentiable. This supplies the analytic germ used for the cusp
expansion in [rolen2026canonical], Section 4.
-/

public section

namespace SptClassification

/-- Near zero, Euler's product is complex differentiable and nonzero. -/
theorem eventually_etaEulerProduct_differentiable_ne_zero :
    ∀ᶠ q : ℂ in nhds 0,
      DifferentiableAt ℂ etaEulerProduct q ∧ etaEulerProduct q ≠ 0 := by
  have hball : ∀ᶠ q : ℂ in nhds 0, q ∈ Metric.ball (0 : ℂ) 1 :=
    Metric.isOpen_ball.mem_nhds (by simp)
  have hne : ∀ᶠ q : ℂ in nhds 0, etaEulerProduct q ≠ 0 :=
    continuousAt_etaEulerProduct_zero.eventually_ne (by simp)
  filter_upwards [hball, hne] with q hq hne
  exact ⟨differentiableAt_etaEulerProduct (by simpa [Metric.mem_ball, dist_zero_right] using hq),
    hne⟩

/-- Complex differentiability holds throughout a neighborhood of zero, rather
than only at its center. -/
theorem eventually_differentiableAt_levelSixEulerUnit :
    ∀ᶠ q : ℂ in nhds 0, DifferentiableAt ℂ levelSixEulerUnit q := by
  have hpower (n : ℕ) (hn : 0 < n) :
      ∀ᶠ q : ℂ in nhds 0,
        DifferentiableAt ℂ etaEulerProduct (q ^ n) ∧ etaEulerProduct (q ^ n) ≠ 0 := by
    have ht : Filter.Tendsto (fun q : ℂ => q ^ n) (nhds 0) (nhds 0) := by
      simpa [zero_pow hn.ne'] using
        (show ContinuousAt (fun q : ℂ => q ^ n) 0 from continuousAt_id.pow n).tendsto
    exact ht.eventually eventually_etaEulerProduct_differentiable_ne_zero
  filter_upwards [eventually_etaEulerProduct_differentiable_ne_zero,
    hpower 2 (by decide), hpower 3 (by decide), hpower 6 (by decide)] with q h h2 h3 h6
  have hd2 : DifferentiableAt ℂ (fun z : ℂ => etaEulerProduct (z ^ 2)) q :=
    DifferentiableAt.comp (x := q) (f := fun z : ℂ => z ^ 2)
      (g := etaEulerProduct) h2.1 (differentiableAt_id.pow 2)
  have hd3 : DifferentiableAt ℂ (fun z : ℂ => etaEulerProduct (z ^ 3)) q :=
    DifferentiableAt.comp (x := q) (f := fun z : ℂ => z ^ 3)
      (g := etaEulerProduct) h3.1 (differentiableAt_id.pow 3)
  have hd6 : DifferentiableAt ℂ (fun z : ℂ => etaEulerProduct (z ^ 6)) q :=
    DifferentiableAt.comp (x := q) (f := fun z : ℂ => z ^ 6)
      (g := etaEulerProduct) h6.1 (differentiableAt_id.pow 6)
  have hunit : levelSixEulerUnit = fun z : ℂ =>
      etaEulerProduct z ^ 5 * etaEulerProduct (z ^ 3) /
        (etaEulerProduct (z ^ 2) * etaEulerProduct (z ^ 6) ^ 5) :=
    funext levelSixEulerUnit_eq
  rw [hunit]
  exact
    ((h.1.pow 5).mul hd3).div (hd2.mul (hd6.pow 5))
      (mul_ne_zero h2.2 (pow_ne_zero 5 h6.2))

end SptClassification
