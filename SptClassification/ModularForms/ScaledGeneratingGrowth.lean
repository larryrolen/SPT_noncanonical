/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.ScaledGeneratingSeries
public import SptClassification.QSeries.PartitionGrowth

/-!
# Height growth of the actual scaled generating functions

The square-root exponential coefficient estimate implies a height bound for
the two convergent generating series. The rescaling to exponents `24n-1`
adds the elementary factor `exp (2π Im τ)`.
-/

public section

namespace SptClassification

open UpperHalfPlane

private theorem sqrt_exponent_le (B y : ℝ) (hy : 0 < y) (n : ℕ) :
    B * Real.sqrt n ≤ B ^ 2 / (2 * y) + y * n / 2 := by
  have hs : (Real.sqrt (n : ℝ)) ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg _)
  have hsq : 2 * y * (B * Real.sqrt n) ≤ B ^ 2 + y ^ 2 * n := by
    calc
      2 * y * (B * Real.sqrt n) ≤ B ^ 2 + (y * Real.sqrt n) ^ 2 := by
        nlinarith [sq_nonneg (B - y * Real.sqrt n)]
      _ = B ^ 2 + y ^ 2 * n := by rw [mul_pow, hs]
  have heq : B ^ 2 / (2 * y) + y * n / 2 =
      (B ^ 2 + y ^ 2 * n) / (2 * y) := by
    field_simp
  rw [heq]
  exact (le_div_iff₀ (by positivity : 0 < 2 * y)).2 (by nlinarith [hsq])

private theorem geometric_exp_bound (t : ℝ) (ht : 0 < t) :
    (∑' n : ℕ, Real.exp (-t * n)) ≤ Real.exp (1 / t) := by
  let r := Real.exp (-t)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    dsimp [r]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hsum : (∑' n : ℕ, Real.exp (-t * n)) = (1 - r)⁻¹ := by
    have hf : (fun n : ℕ => Real.exp (-t * n)) = (fun n : ℕ => r ^ n) := by
      funext n
      dsimp [r]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hf]
    exact (hasSum_geometric_of_norm_lt_one
      (show ‖r‖ < 1 by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1)).tsum_eq
  rw [hsum]
  have he : 1 + t ≤ Real.exp t := by
    simpa [add_comm] using Real.add_one_le_exp t
  have her : (1 + t) * r ≤ 1 := by
    dsimp [r]
    have he' := mul_le_mul_of_nonneg_right he (Real.exp_pos (-t)).le
    simpa [← Real.exp_add] using he'
  have hden : 0 < 1 - r := sub_pos.mpr hr1
  have hbound : (1 - r)⁻¹ ≤ 1 + 1 / t := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hden).2
    rw [show 1 + 1 / t = (1 + t) / t by field_simp; ring]
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ ht).2 (by nlinarith [her])
  calc
    (1 - r)⁻¹ ≤ 1 + 1 / t := hbound
    _ ≤ Real.exp (1 / t) := by simpa [add_comm] using Real.add_one_le_exp (1 / t)

/-- A convergent complex power series with square-root exponential coefficients
has exponential growth in the reciprocal nome height. -/
theorem norm_powerSeries_le_exp_inv_height
    (c : ℕ → ℂ) (C B y : ℝ) (hC : 0 < C) (hy : 0 < y)
    (hc : ∀ n, ‖c n‖ ≤ C * Real.exp (B * Real.sqrt n))
    (q : ℂ) (hq : ‖q‖ = Real.exp (-y))
    (hs : Summable (fun n => ‖c n * q ^ n‖)) :
    ‖∑' n, c n * q ^ n‖ ≤ C * Real.exp ((B ^ 2 + 2) / y) := by
  let K := C * Real.exp (B ^ 2 / (2 * y))
  let r := Real.exp (-y / 2)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    dsimp [r]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hgeo : Summable (fun n : ℕ => K * r ^ n) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left K
  have hterm (n : ℕ) : ‖c n * q ^ n‖ ≤ K * r ^ n := by
    have hb := sqrt_exponent_le B y hy n
    have hexp : B * Real.sqrt n - y * n ≤ B ^ 2 / (2 * y) - y * n / 2 := by
      linarith
    calc
      ‖c n * q ^ n‖ = ‖c n‖ * Real.exp (-y * n) := by
        rw [norm_mul, norm_pow, hq, ← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ (C * Real.exp (B * Real.sqrt n)) * Real.exp (-y * n) := by
        gcongr
        exact hc n
      _ = C * Real.exp (B * Real.sqrt n - y * n) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 1
        ring
      _ ≤ C * Real.exp (B ^ 2 / (2 * y) - y * n / 2) := by
        gcongr
      _ = K * r ^ n := by
        dsimp [K, r]
        rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
        congr 1
        ring
  calc
    ‖∑' n, c n * q ^ n‖ ≤ ∑' n, ‖c n * q ^ n‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n, K * r ^ n := Summable.tsum_le_tsum hterm hs hgeo
    _ = K * (∑' n, r ^ n) := by rw [tsum_mul_left]
    _ ≤ K * Real.exp (2 / y) := by
      have hK : 0 ≤ K := by positivity
      apply mul_le_mul_of_nonneg_left _ hK
      convert geometric_exp_bound (y / 2) (by positivity) using 1
      · congr 1
        funext n
        dsimp [r]
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      · congr 1
        field_simp
    _ = C * Real.exp ((B ^ 2 / 2 + 2) / y) := by
      dsimp [K]
      rw [mul_assoc, ← Real.exp_add]
      congr 1
      ring
    _ ≤ C * Real.exp ((B ^ 2 + 2) / y) := by
      gcongr
      nlinarith [sq_nonneg B]

private theorem norm_scaledFourierFunction_le_height
    (c : ℕ → ℂ) (f : ℂ → ℂ) (C B : ℝ) (hC : 0 < C)
    (hc : ∀ n, ‖c n‖ ≤ C * Real.exp (B * Real.sqrt n))
    (τ : UpperHalfPlane)
    (hf : f (Function.Periodic.qParam 1 τ ^ 24) =
      ∑' n, c n * (Function.Periodic.qParam 1 τ ^ 24) ^ n)
    (hs : Summable (fun n =>
      ‖c n * (Function.Periodic.qParam 1 τ ^ 24) ^ n‖)) :
    ‖scaledFourierFunction f τ‖ ≤
      C * Real.exp ((2 * Real.pi + (B ^ 2 + 2) / (48 * Real.pi)) *
        (τ.im + 1 / τ.im)) := by
  let q := Function.Periodic.qParam 1 τ
  let y := τ.im
  let D := (B ^ 2 + 2) / (48 * Real.pi)
  have hy : 0 < y := τ.im_pos
  have hpi : 0 < Real.pi := Real.pi_pos
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hq : ‖q‖ = Real.exp (-2 * Real.pi * y) := by
    dsimp [q, y]
    rw [Function.Periodic.norm_qParam]
    congr 1
    simp
  have hq24 : ‖q ^ 24‖ = Real.exp (-(48 * Real.pi * y)) := by
    rw [norm_pow, hq, ← Real.exp_nat_mul]
    congr 1
    ring
  have hqinv : ‖q⁻¹‖ = Real.exp (2 * Real.pi * y) := by
    rw [norm_inv, hq, ← Real.exp_neg]
    congr 1
    ring
  have hcore := norm_powerSeries_le_exp_inv_height c C B (48 * Real.pi * y)
    hC (by positivity) hc (q ^ 24) hq24 hs
  have hmain : ‖scaledFourierFunction f τ‖ ≤
      C * Real.exp (2 * Real.pi * y + D / y) := by
    calc
      ‖scaledFourierFunction f τ‖ =
          Real.exp (2 * Real.pi * y) * ‖∑' n, c n * (q ^ 24) ^ n‖ := by
        rw [scaledFourierFunction_apply, norm_mul, hqinv]
        change Real.exp (2 * Real.pi * y) * ‖f (q ^ 24)‖ = _
        rw [hf]
      _ ≤ Real.exp (2 * Real.pi * y) *
          (C * Real.exp ((B ^ 2 + 2) / (48 * Real.pi * y))) := by
        gcongr
      _ = C * Real.exp (2 * Real.pi * y + D / y) := by
        dsimp [D]
        rw [mul_left_comm, mul_assoc, ← Real.exp_add]
        congr 1
        field_simp
  have hexp : 2 * Real.pi * y + D / y ≤
      (2 * Real.pi + D) * (y + 1 / y) := by
    have hz : 0 ≤ 2 * Real.pi / y + D * y := by positivity
    have heq : (2 * Real.pi + D) * (y + 1 / y) =
        2 * Real.pi * y + D / y + (2 * Real.pi / y + D * y) := by ring
    rw [heq]
    exact le_add_of_nonneg_right hz
  calc
    ‖scaledFourierFunction f τ‖ ≤ C * Real.exp (2 * Real.pi * y + D / y) := hmain
    _ ≤ C * Real.exp ((2 * Real.pi + D) * (y + 1 / y)) := by
      gcongr
    _ = C * Real.exp ((2 * Real.pi + (B ^ 2 + 2) / (48 * Real.pi)) *
        (τ.im + 1 / τ.im)) := (rfl)

/-- The actual partition and smallest-parts generating functions admit one
common exponential height bound. The only literature input is the named
Hardy–Ramanujan coefficient estimate in `PartitionGrowth`. -/
theorem exists_scaledPartition_spt_height_growth :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ τ : UpperHalfPlane,
        ‖scaledPartitionFunction τ‖ ≤
          C * Real.exp (A * (τ.im + 1 / τ.im)) ∧
        ‖scaledSptFunction τ‖ ≤
          C * Real.exp (A * (τ.im + 1 / τ.im)) := by
  obtain ⟨C, B, hC, _hB, hp, hspt⟩ := exists_partition_spt_coefficient_growth
  let A := 2 * Real.pi + (B ^ 2 + 2) / (48 * Real.pi)
  refine ⟨C, A, hC, ?_, ?_⟩
  · dsimp [A]
    positivity
  intro τ
  let q := Function.Periodic.qParam 1 τ ^ 24
  have hq : ‖q‖ < 1 := by
    dsimp [q]
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (Function.Periodic.norm_qParam_lt_one
      one_pos τ.im_pos) (by norm_num)
  constructor
  · have hvalue : (etaEulerProduct q)⁻¹ = ∑' n, (partitionCount n : ℂ) * q ^ n :=
      (QSeries.hasSum_partitionCount_inverseEuler hq).tsum_eq.symm
    have hcoef (n : ℕ) : ‖(partitionCount n : ℂ)‖ ≤
        C * Real.exp (B * Real.sqrt n) := by
      simpa using hp n
    rw [scaledPartitionFunction_eq]
    exact norm_scaledFourierFunction_le_height _ (fun z => (etaEulerProduct z)⁻¹)
      C B hC hcoef τ (by simpa only [q] using hvalue)
      (by simpa only [q] using QSeries.summable_norm_partitionCount hq)
  · have hcoef (n : ℕ) : ‖(spt n : ℂ)‖ ≤
        C * Real.exp (B * Real.sqrt n) := by
      simpa using hspt n
    rw [scaledSptFunction_eq]
    exact norm_scaledFourierFunction_le_height _ sptAnalyticCore C B hC hcoef τ
      (by simpa only [q] using (hasSum_sptAnalyticCore hq).tsum_eq.symm)
      (by simpa only [q] using summable_norm_spt hq)

end SptClassification
