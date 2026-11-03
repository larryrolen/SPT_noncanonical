/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.AnalyticLaurentProducts
public import SptClassification.QSeries.ProgressionLaurent

/-! # Laurent products and their convergent Fourier expansions -/

public section

namespace SptClassification

/-- Shifting a power series by a Laurent monomial retains its full coefficient row. -/
theorem shiftedPowerSeries_coeff (s : ℤ) (f : PowerSeries ℚ) (r : ℤ) :
    ((HahnSeries.single s 1 * HahnSeries.ofPowerSeries ℤ ℚ f) :
      LaurentSeries ℚ).coeff r =
      if 0 ≤ r - s then f.coeff (r - s).toNat else 0 := by
  rw [HahnSeries.coeff_single_mul, one_mul]
  by_cases h : 0 ≤ r - s
  · rw [if_pos h, ← Int.toNat_of_nonneg h]
    exact HahnSeries.ofPowerSeries_apply_coeff f _
  · rw [if_neg h]
    simp [HahnSeries.ofPowerSeries, HahnSeries.embDomainRingHom,
      HahnSeries.embDomain, show (r - s) ∉ Set.range (Nat.castAddMonoidHom ℤ) by
        rintro ⟨n, hn⟩
        exact h (hn ▸ Int.natCast_nonneg n)]
    intro n _ hn
    omega

/-- A prescribed pole bound gives a monomial times its pole-cleared power series. -/
theorem laurent_eq_shifted_poleCleared (F : LaurentSeries ℚ) (M : ℕ)
    (hF : ∀ r : ℤ, r < -(M : ℤ) → F.coeff r = 0) :
    F = HahnSeries.single (-(M : ℤ)) 1 *
      HahnSeries.ofPowerSeries ℤ ℚ (poleClearedRationalRow F.coeff M) := by
  apply HahnSeries.ext
  funext r
  rw [shiftedPowerSeries_coeff]
  split_ifs with h
  · rw [poleClearedRationalRow_coeff, Int.toNat_of_nonneg h]
    congr 1
    omega
  · exact hF r (by omega)

/-- Cauchy multiplication of pole-cleared rows is the actual Laurent product. -/
theorem laurent_mul_coeff_eq_productRow (F G : LaurentSeries ℚ) (M N : ℕ)
    (hF : ∀ r : ℤ, r < -(M : ℤ) → F.coeff r = 0)
    (hG : ∀ r : ℤ, r < -(N : ℤ) → G.coeff r = 0) (r : ℤ) :
    (F * G).coeff r = rationalLaurentProductRow F.coeff G.coeff M N r := by
  have hprod : F * G = HahnSeries.single (-((M + N : ℕ) : ℤ)) 1 *
      HahnSeries.ofPowerSeries ℤ ℚ
        (poleClearedRationalRow F.coeff M * poleClearedRationalRow G.coeff N) := by
    conv_lhs => rw [laurent_eq_shifted_poleCleared F M hF,
      laurent_eq_shifted_poleCleared G N hG]
    rw [map_mul, mul_mul_mul_comm, HahnSeries.single_mul_single, one_mul]
    have he : -(M : ℤ) + -(N : ℤ) = -((M + N : ℕ) : ℤ) := by omega
    rw [he]
  rw [hprod, shiftedPowerSeries_coeff]
  rw [rationalLaurentProductRow_eq]
  simp only [sub_neg_eq_add]
  by_cases h : r < -((M + N : ℕ) : ℤ)
  · rw [if_pos h, if_neg (by omega)]
  · rw [if_neg h, if_pos (by omega)]

/-- The convergent coefficient row of a product is the coefficient row of the
actual rational Laurent-series product, with no auxiliary coefficient map. -/
theorem laurent_mul_hasSum (F G : LaurentSeries ℚ) (M N : ℕ)
    (hF : ∀ r : ℤ, r < -(M : ℤ) → F.coeff r = 0)
    (hG : ∀ r : ℤ, r < -(N : ℤ) → G.coeff r = 0)
    (q A B : ℂ) (hq : q ≠ 0)
    (ha : HasSum (fun r : ℤ => (F.coeff r : ℂ) * q ^ r) A)
    (hb : HasSum (fun r : ℤ => (G.coeff r : ℂ) * q ^ r) B) :
    HasSum (fun r : ℤ => ((F * G).coeff r : ℂ) * q ^ r) (A * B) := by
  simpa only [laurent_mul_coeff_eq_productRow F G M N hF hG] using
    rationalLaurentProductRow_hasSum F.coeff G.coeff M N hF hG q A B hq ha hb

/-- A pole bound multiplies by the exponent under actual Laurent powers. -/
theorem laurent_pow_zero_below (F : LaurentSeries ℚ) (M : ℕ)
    (hF : ∀ r : ℤ, r < -(M : ℤ) → F.coeff r = 0) (n : ℕ) :
    ∀ r : ℤ, r < -((M * n : ℕ) : ℤ) → (F ^ n).coeff r = 0 := by
  induction n with
  | zero =>
      intro r hr
      have hr0 : r ≠ 0 := by omega
      simp [HahnSeries.coeff_one, hr0]
  | succ n ih =>
      intro r hr
      rw [pow_succ, laurent_mul_coeff_eq_productRow _ _ (M * n) M ih hF]
      apply rationalLaurentProductRow_zero_below
      simpa only [Nat.mul_succ] using hr

/-- Convergent Laurent expansions respect every natural power, including
powers divisible by the reduction prime. -/
theorem laurent_pow_hasSum (F : LaurentSeries ℚ) (M : ℕ)
    (hF : ∀ r : ℤ, r < -(M : ℤ) → F.coeff r = 0)
    (q A : ℂ) (hq : q ≠ 0)
    (ha : HasSum (fun r : ℤ => (F.coeff r : ℂ) * q ^ r) A) (n : ℕ) :
    HasSum (fun r : ℤ => ((F ^ n).coeff r : ℂ) * q ^ r) (A ^ n) := by
  induction n with
  | zero =>
      have he : (fun r : ℤ => (((1 : LaurentSeries ℚ).coeff r : ℚ) : ℂ) * q ^ r) =
          (fun r : ℤ => if r = 0 then (1 : ℂ) else 0) := by
        funext r
        by_cases hr : r = 0 <;> simp [HahnSeries.coeff_one, hr]
      simpa only [pow_zero, he] using (hasSum_ite_eq (0 : ℤ) (1 : ℂ))
  | succ n ih =>
      simpa only [pow_succ] using laurent_mul_hasSum (F ^ n) F (M * n) M
        (laurent_pow_zero_below F M hF n) hF q (A ^ n) A hq ih ha

end SptClassification
