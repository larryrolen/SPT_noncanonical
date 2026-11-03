/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.EtaQuotientExpansion

/-!
# Complex conjugation of the level-six eta expansion

The eta quotient has real Fourier coefficients. This identifies its value at
the reflected upper-half-plane point with the conjugate original value.
We follow [rolen2026canonical], Section 4.
-/

public section

namespace SptClassification

/-- The convergent eta Euler product has real Taylor coefficients. -/
theorem etaEulerProduct_star {q : ℂ} (hq : ‖q‖ < 1) :
    etaEulerProduct (star q) = star (etaEulerProduct q) := by
  have hcont : Continuous (starRingEnd ℂ : ℂ → ℂ) := by
    simpa using (continuous_star : Continuous (fun z : ℂ => star z))
  have h := (ModularForm.multipliable_one_sub_pow hq).hasProd.map
    (starRingEnd ℂ) hcont
  have hs : HasProd (fun n : ℕ => 1 - (star q) ^ (n + 1))
      (star (etaEulerProduct q)) := by
    simpa only [Function.comp_def, map_sub, map_one, map_pow,
      starRingEnd_apply, etaEulerProduct_eq] using h
  rw [etaEulerProduct_eq]
  exact hs.tprod_eq

/-- Reflection in the imaginary axis conjugates the Fourier nome. -/
theorem qParam_neg_star (z : ℂ) :
    Function.Periodic.qParam 1 (-star z) =
      star (Function.Periodic.qParam 1 z) := by
  unfold Function.Periodic.qParam
  change Complex.exp (2 * ↑Real.pi * Complex.I * -star z / (1 : ℂ)) =
    (starRingEnd ℂ) (Complex.exp (2 * ↑Real.pi * Complex.I * z / (1 : ℂ)))
  rw [← Complex.exp_conj]
  apply congrArg Complex.exp
  simp [map_mul]
  left
  change (2 : ℂ) = star (2 : ℂ)
  simp

/-- The normalized level-six Euler quotient is compatible with conjugation
throughout the open nome disc. -/
theorem levelSixEulerUnit_star {q : ℂ} (hq : ‖q‖ < 1) :
    levelSixEulerUnit (star q) = star (levelSixEulerUnit q) := by
  have hpow (n : ℕ) (hn : n ≠ 0) : ‖q ^ n‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq hn
  have hE (n : ℕ) (hn : n ≠ 0) :
      etaEulerProduct ((star q) ^ n) = star (etaEulerProduct (q ^ n)) := by
    simpa only [star_pow] using
      (etaEulerProduct_star (hpow n hn))
  rw [levelSixEulerUnit_eq (star q), levelSixEulerUnit_eq q]
  rw [etaEulerProduct_star hq, hE 2 (by decide), hE 3 (by decide),
    hE 6 (by decide)]
  simp

/-- The actual eta quotient takes conjugate values at points reflected in
the imaginary axis. -/
theorem levelSixEtaQuotient_neg_star (z : UpperHalfPlane) :
    levelSixEtaQuotient (-star (z : ℂ)) =
      star (levelSixEtaQuotient (z : ℂ)) := by
  have hq : ‖Function.Periodic.qParam 1 (z : ℂ)‖ < 1 :=
    Function.Periodic.norm_qParam_lt_one one_pos z.im_pos
  rw [levelSixEtaQuotient_eq_unit_div_qParam,
    qParam_neg_star, levelSixEulerUnit_star hq,
    levelSixEtaQuotient_eq_unit_div_qParam]
  simp

end SptClassification
