/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.LevelSixEtaQuotient
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.Ring

/-!
# The expansion of the level-six eta quotient at infinity

We separate the Euler factors of the actual eta quotient from their exponential
prefactor. The exponent calculation gives a simple pole at the infinity cusp
once the Euler unit is known to tend to one. The eta product and the coordinate
are those of [rolen2026canonical], Section 4.
-/

public section

namespace SptClassification

/-- Euler's product appearing in eta after removal of its exponential factor. -/
noncomputable def etaEulerProduct (q : ℂ) : ℂ :=
  ∏' n : ℕ, (1 - q ^ (n + 1))

/-- The Euler product formula for the analytic eta factor. -/
theorem etaEulerProduct_eq (q : ℂ) :
    etaEulerProduct q = ∏' n : ℕ, (1 - q ^ (n + 1)) :=
  (rfl)

/-- The Euler product has constant value one at the punctured cusp's center. -/
@[simp] theorem etaEulerProduct_zero : etaEulerProduct 0 = 1 := by
  simp [etaEulerProduct]

/-- Euler's product has no zero in the open unit disc. This is the analytic
unit property needed when comparing its cusp expansion with an integral formal
series. -/
theorem etaEulerProduct_ne_zero {q : ℂ} (hq : ‖q‖ < 1) :
    etaEulerProduct q ≠ 0 := by
  unfold etaEulerProduct
  refine tprod_one_add_ne_zero_of_summable (f := fun n ↦ -(q ^ (n + 1))) ?_ ?_
  · intro n
    have hpow : ‖q ^ (n + 1)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg q) hq (Nat.succ_ne_zero n)
    have hne : q ^ (n + 1) ≠ 1 := by
      intro he
      rw [he, norm_one] at hpow
      exact (lt_irrefl _ hpow)
    simpa [sub_eq_add_neg] using sub_ne_zero.mpr hne.symm
  · simpa [norm_neg, norm_pow, summable_nat_add_iff] using
      summable_geometric_of_lt_one (norm_nonneg q) hq

/-- Euler's product is holomorphic throughout the open unit disc. -/
theorem differentiableOn_etaEulerProduct :
    DifferentiableOn ℂ etaEulerProduct (Metric.ball 0 1) :=
  ModularForm.differentiableOn_tprod_one_sub_pow

/-- Pointwise holomorphy of the Euler product on the unit disc. -/
theorem differentiableAt_etaEulerProduct {q : ℂ} (hq : ‖q‖ < 1) :
    DifferentiableAt ℂ etaEulerProduct q := by
  apply differentiableOn_etaEulerProduct.differentiableAt
  apply Metric.isOpen_ball.mem_nhds
  simpa [Metric.mem_ball, dist_zero_right] using hq

/-- Euler's product is holomorphic at the infinity-cusp nome. -/
theorem differentiableAt_etaEulerProduct_zero : DifferentiableAt ℂ etaEulerProduct 0 := by
  exact differentiableAt_etaEulerProduct (by simp)

/-- Euler's product is continuous at the infinity-cusp nome. -/
theorem continuousAt_etaEulerProduct_zero : ContinuousAt etaEulerProduct 0 :=
  differentiableAt_etaEulerProduct_zero.continuousAt

/-- Scaling the upper-half-plane variable raises its nome to the same power. -/
theorem qParam_nat_mul (n : ℕ) (z : ℂ) :
    Function.Periodic.qParam 1 ((n : ℂ) * z) =
      Function.Periodic.qParam 1 z ^ n := by
  unfold Function.Periodic.qParam
  rw [← Complex.exp_nat_mul]
  congr 1
  norm_num
  ring

/-- Eta is its exponential factor times Euler's product in the nome. -/
theorem eta_nat_mul_eq_euler (n : ℕ) (z : ℂ) :
    ModularForm.eta ((n : ℂ) * z) =
      Function.Periodic.qParam 24 ((n : ℂ) * z) *
        etaEulerProduct (Function.Periodic.qParam 1 z ^ n) := by
  unfold ModularForm.eta etaEulerProduct
  congr 1
  apply tprod_congr
  intro k
  simp only [ModularForm.eta_q, qParam_nat_mul]

/-- The unshifted Euler quotient; its constant value at the cusp is one. -/
noncomputable def levelSixEulerUnit (q : ℂ) : ℂ :=
  etaEulerProduct q ^ 5 * etaEulerProduct (q ^ 3) /
    (etaEulerProduct (q ^ 2) * etaEulerProduct (q ^ 6) ^ 5)

/-- The explicit Euler-unit formula for the level-six quotient. -/
theorem levelSixEulerUnit_eq (q : ℂ) :
    levelSixEulerUnit q =
      etaEulerProduct q ^ 5 * etaEulerProduct (q ^ 3) /
        (etaEulerProduct (q ^ 2) * etaEulerProduct (q ^ 6) ^ 5) :=
  (rfl)

/-- The normalized eta quotient is a unit on the entire open nome disc. -/
theorem levelSixEulerUnit_ne_zero {q : ℂ} (hq : ‖q‖ < 1) :
    levelSixEulerUnit q ≠ 0 := by
  have hpow (n : ℕ) (hn : n ≠ 0) : ‖q ^ n‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq hn
  unfold levelSixEulerUnit
  exact div_ne_zero
    (mul_ne_zero (pow_ne_zero _ (etaEulerProduct_ne_zero hq))
      (etaEulerProduct_ne_zero (hpow 3 (by decide))))
    (mul_ne_zero (etaEulerProduct_ne_zero (hpow 2 (by decide)))
      (pow_ne_zero _ (etaEulerProduct_ne_zero (hpow 6 (by decide)))))

/-- The Euler unit of the level-six quotient is holomorphic on the nome disc. -/
theorem differentiableAt_levelSixEulerUnit {q : ℂ} (hq : ‖q‖ < 1) :
    DifferentiableAt ℂ levelSixEulerUnit q := by
  have hpow (n : ℕ) (hn : n ≠ 0) : ‖q ^ n‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq hn
  have hdiff (n : ℕ) (hn : n ≠ 0) :
      DifferentiableAt ℂ (fun x : ℂ => etaEulerProduct (x ^ n)) q := by
    exact (differentiableAt_etaEulerProduct (hpow n hn)).comp q
      (differentiableAt_id.pow n)
  unfold levelSixEulerUnit
  exact ((differentiableAt_etaEulerProduct hq).pow 5 |>.mul
    (hdiff 3 (by decide))).div
    ((hdiff 2 (by decide)).mul ((hdiff 6 (by decide)).pow 5))
    (mul_ne_zero (etaEulerProduct_ne_zero (hpow 2 (by decide)))
      (pow_ne_zero _ (etaEulerProduct_ne_zero (hpow 6 (by decide)))))

/-- The Euler quotient takes value one at the origin of the nome disk. -/
@[simp] theorem levelSixEulerUnit_zero : levelSixEulerUnit 0 = 1 := by
  simp [levelSixEulerUnit]

/-- The Euler quotient is continuous at the infinity-cusp nome. -/
theorem continuousAt_levelSixEulerUnit_zero : ContinuousAt levelSixEulerUnit 0 :=
  (differentiableAt_levelSixEulerUnit (by simp)).continuousAt

/-- The normalized analytic quotient has a holomorphic germ at infinity. -/
theorem differentiableAt_levelSixEulerUnit_zero :
    DifferentiableAt ℂ levelSixEulerUnit 0 :=
  differentiableAt_levelSixEulerUnit (by simp)

/-- The holomorphic Euler unit has no zero in some neighborhood of the cusp. -/
theorem eventually_levelSixEulerUnit_ne_zero :
    ∀ᶠ q : ℂ in nhds 0, levelSixEulerUnit q ≠ 0 := by
  exact continuousAt_levelSixEulerUnit_zero.eventually_ne (by simp)

private theorem exp_product_quotient (a b c d e : ℂ) :
    Complex.exp a * (Complex.exp b * Complex.exp c /
      (Complex.exp d * Complex.exp e)) =
      Complex.exp (a + b + c - (d + e)) := by
  rw [Complex.exp_sub, Complex.exp_add, Complex.exp_add,
    Complex.exp_add]
  ring

/-- The exponential prefactors of the four eta factors contribute `q⁻¹`. -/
theorem levelSixEta_prefactor (z : ℂ) :
    Function.Periodic.qParam 1 z *
      (Function.Periodic.qParam 24 z ^ 5 *
        Function.Periodic.qParam 24 (3 * z) /
        (Function.Periodic.qParam 24 (2 * z) *
          Function.Periodic.qParam 24 (6 * z) ^ 5)) = 1 := by
  unfold Function.Periodic.qParam
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  rw [exp_product_quotient]
  convert Complex.exp_zero using 1
  congr 1
  norm_num
  ring

/-- The actual analytic eta quotient has a normalized simple-pole expansion. -/
theorem qParam_mul_levelSixEtaQuotient (z : ℂ) :
    Function.Periodic.qParam 1 z * levelSixEtaQuotient z =
      levelSixEulerUnit (Function.Periodic.qParam 1 z) := by
  rw [levelSixEtaQuotient_eq]
  unfold levelSixEulerUnit
  have h1 : ModularForm.eta z =
      Function.Periodic.qParam 24 z *
        etaEulerProduct (Function.Periodic.qParam 1 z) := by
    simpa using eta_nat_mul_eq_euler 1 z
  have h2 : ModularForm.eta (2 * z) =
      Function.Periodic.qParam 24 (2 * z) *
        etaEulerProduct (Function.Periodic.qParam 1 z ^ 2) := by
    simpa using eta_nat_mul_eq_euler 2 z
  have h3 : ModularForm.eta (3 * z) =
      Function.Periodic.qParam 24 (3 * z) *
        etaEulerProduct (Function.Periodic.qParam 1 z ^ 3) := by
    simpa using eta_nat_mul_eq_euler 3 z
  have h6 : ModularForm.eta (6 * z) =
      Function.Periodic.qParam 24 (6 * z) *
        etaEulerProduct (Function.Periodic.qParam 1 z ^ 6) := by
    simpa using eta_nat_mul_eq_euler 6 z
  rw [h1, h2, h3, h6]
  have hp := levelSixEta_prefactor z
  calc
    _ = (Function.Periodic.qParam 1 z *
          (Function.Periodic.qParam 24 z ^ 5 *
            Function.Periodic.qParam 24 (3 * z) /
            (Function.Periodic.qParam 24 (2 * z) *
              Function.Periodic.qParam 24 (6 * z) ^ 5))) *
          (etaEulerProduct (Function.Periodic.qParam 1 z) ^ 5 *
            etaEulerProduct (Function.Periodic.qParam 1 z ^ 3) /
            (etaEulerProduct (Function.Periodic.qParam 1 z ^ 2) *
              etaEulerProduct (Function.Periodic.qParam 1 z ^ 6) ^ 5)) := by
      simp only [mul_pow, div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by rw [hp, one_mul]

/-- On the upper half-plane the quotient is the holomorphic Euler unit divided
by the nonzero nome, exhibiting its simple pole at infinity. -/
theorem levelSixEtaQuotient_eq_unit_div_qParam (z : ℂ) :
    levelSixEtaQuotient z =
      levelSixEulerUnit (Function.Periodic.qParam 1 z) /
        Function.Periodic.qParam 1 z := by
  have hq : Function.Periodic.qParam 1 z ≠ 0 := by
    unfold Function.Periodic.qParam
    exact Complex.exp_ne_zero _
  apply (eq_div_iff hq).2
  exact (mul_comm _ _).trans (qParam_mul_levelSixEtaQuotient z)

/-- Along every approach to the infinity cusp, the normalized quotient tends to one. -/
theorem tendsto_qParam_mul_levelSixEtaQuotient
    {α : Type*} {l : Filter α} (z : α → ℂ)
    (hz : Filter.Tendsto (fun a => Function.Periodic.qParam 1 (z a)) l (nhds 0)) :
    Filter.Tendsto
      (fun a => Function.Periodic.qParam 1 (z a) * levelSixEtaQuotient (z a))
      l (nhds 1) := by
  simpa only [Function.comp_def, qParam_mul_levelSixEtaQuotient,
    levelSixEulerUnit_zero] using
    continuousAt_levelSixEulerUnit_zero.tendsto.comp hz

end SptClassification
