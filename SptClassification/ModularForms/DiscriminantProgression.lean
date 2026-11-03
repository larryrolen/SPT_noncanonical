/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.PoweredProjection
public import SptClassification.ModularForms.PrincipalPartFourierJ
public import SptClassification.QSeries.LaurentSupport
public import SptClassification.QSeries.EtaIntegralCore
public import Mathlib.RingTheory.PowerSeries.Expand

/-! # The integral discriminant in the progression parameter

The parameter is `X = q^(1/M)`. The actual discriminant has integral series
`X^M ∏ (1-X^(Mn))^24`, with leading coefficient one. These proofs provide
the pole-clearing factor used in [rolenManuscript, §2].
-/

public section

namespace SptClassification

/-- Substitution of a positive power preserves a convergent integral series. -/
theorem integralPowerSeries_expand_hasSum (F : PowerSeries ℤ) (M : ℕ)
    (hM : M ≠ 0) (q a : ℂ)
    (hF : HasSum (fun n => (F.coeff n : ℂ) * (q ^ M) ^ n) a) :
    HasSum (fun n => ((PowerSeries.expand M hM F).coeff n : ℂ) * q ^ n) a := by
  have hinj : Function.Injective (fun n : ℕ => M * n) :=
    fun _ _ h => Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hM) h
  apply (hinj.hasSum_iff ?_).mp
  · change HasSum (fun n => ((PowerSeries.expand M hM F).coeff (M * n) : ℂ) *
      q ^ (M * n)) a
    simpa only [PowerSeries.coeff_expand_mul, pow_mul] using hF
  · intro n hn
    have hnot : ¬ M ∣ n := by
      rintro ⟨k, hk⟩
      exact hn ⟨k, hk.symm⟩
    simp [PowerSeries.coeff_expand_of_not_dvd M hM F hnot]

/-- The integral power series for `Δ` in the progression parameter. -/
noncomputable def discriminantProgressionPowerSeries (M : ℕ) (hM : M ≠ 0) :
    PowerSeries ℤ :=
  PowerSeries.X ^ M * PowerSeries.expand M hM (QSeries.etaIntegralCore ^ 24)

/-- The same integral discriminant as an actual Laurent series. -/
noncomputable def discriminantProgressionLaurent (M : ℕ) (hM : M ≠ 0) :
    LaurentSeries ℤ :=
  HahnSeries.ofPowerSeries ℤ ℤ (discriminantProgressionPowerSeries M hM)

/-- Its leading coefficient is one, at the index `M`. -/
theorem discriminantProgressionLaurent_coeff (M : ℕ) (hM : M ≠ 0) :
    (discriminantProgressionLaurent M hM).coeff (M : ℤ) = 1 := by
  rw [discriminantProgressionLaurent, HahnSeries.ofPowerSeries_apply_coeff]
  rw [discriminantProgressionPowerSeries]
  have hc := PowerSeries.coeff_X_pow_mul
    (PowerSeries.expand M hM (QSeries.etaIntegralCore ^ 24)) M 0
  simp only [zero_add] at hc
  rw [hc, PowerSeries.coeff_zero_eq_constantCoeff,
    PowerSeries.constantCoeff_expand, map_pow]
  simp [← PowerSeries.coeff_zero_eq_constantCoeff]

/-- The period-`M` nome is the specified `M`-th root of the ordinary nome. -/
theorem qParam_nat_pow (M : ℕ) (hM : M ≠ 0) (z : ℂ) :
    Function.Periodic.qParam M z ^ M = Function.Periodic.qParam 1 z := by
  unfold Function.Periodic.qParam
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

/-- The integral discriminant series sums to the analytic discriminant. -/
theorem discriminantProgressionPowerSeries_hasSum (M : ℕ) (hM : M ≠ 0)
    (τ : UpperHalfPlane) :
    HasSum (fun n => ((discriminantProgressionPowerSeries M hM).coeff n : ℂ) *
      Function.Periodic.qParam M τ ^ n) (ModularForm.eta τ ^ 24) := by
  let q := Function.Periodic.qParam M τ
  have hq : q ^ M = Function.Periodic.qParam 1 τ := qParam_nat_pow M hM τ
  have heta := QSeries.hasSum_etaIntegralCore
    (Function.Periodic.norm_qParam_lt_one (by norm_num : (0 : ℝ) < 1) τ.im_pos)
  have hpow := QSeries.hasSum_coefficientTerm_pow _ _ _ 24 heta
  have hexp := integralPowerSeries_expand_hasSum (QSeries.etaIntegralCore ^ 24)
    M hM q _ (by simpa only [hq] using hpow)
  have hX : HasSum (fun n => (((PowerSeries.X ^ M : PowerSeries ℤ).coeff n) : ℂ) *
      q ^ n) (q ^ M) := by
    simpa +contextual [PowerSeries.coeff_X_pow] using hasSum_ite_eq M (q ^ M)
  have hprod := QSeries.hasSum_coefficientTerm_mul _ _ _ _ _
    hX.summable.norm hexp.summable.norm hX hexp
  have hvalue : q ^ M * etaEulerProduct (Function.Periodic.qParam 1 τ) ^ 24 =
      ModularForm.eta τ ^ 24 := by
    change _ = CuspForm.discriminant τ
    rw [discriminant_eq_qParam_mul_euler, hq]
  simpa only [discriminantProgressionPowerSeries, hvalue] using hprod

/-- The discriminant has no negative powers in the progression parameter. -/
theorem discriminantProgressionLaurent_zero_below (M : ℕ) (hM : M ≠ 0)
    (r : ℤ) (hr : r < 0) :
    (discriminantProgressionLaurent M hM).coeff r = 0 := by
  rw [discriminantProgressionLaurent]
  exact (PowerSeries.coeff_coe _ r).trans (if_pos hr)

/-- Every discriminant term has degree at least `M`. -/
theorem discriminantProgressionLaurent_support_lower (M : ℕ) (hM : M ≠ 0) :
    ∀ r, (discriminantProgressionLaurent M hM).coeff r ≠ 0 → (M : ℤ) ≤ r := by
  intro r hr
  have hr0 : 0 ≤ r := le_of_not_gt (fun h =>
    hr (discriminantProgressionLaurent_zero_below M hM r h))
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hr0
  rw [discriminantProgressionLaurent, HahnSeries.ofPowerSeries_apply_coeff,
    discriminantProgressionPowerSeries, PowerSeries.coeff_X_pow_mul'] at hr
  have hMn : M ≤ n := by
    by_contra h
    exact hr (if_neg h)
  exact_mod_cast hMn

/-- The discriminant uses only integral powers of the ordinary nome. -/
theorem discriminantProgressionLaurent_support_residue (M : ℕ) (hM : M ≠ 0) :
    ∀ r, (discriminantProgressionLaurent M hM).coeff r ≠ 0 → (r : ZMod M) = 0 := by
  intro r hr
  have hr0 : 0 ≤ r := le_trans (by positivity)
    (discriminantProgressionLaurent_support_lower M hM r hr)
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hr0
  have he : discriminantProgressionPowerSeries M hM =
      PowerSeries.expand M hM (PowerSeries.X * QSeries.etaIntegralCore ^ 24) := by
    rw [discriminantProgressionPowerSeries, map_mul, PowerSeries.expand_X]
  rw [discriminantProgressionLaurent, HahnSeries.ofPowerSeries_apply_coeff, he] at hr
  have hd : M ∣ n := by
    by_contra h
    exact hr (PowerSeries.coeff_expand_of_not_dvd M hM _ h)
  simpa using (ZMod.natCast_eq_zero_iff n M).mpr hd

/-- Casting the integral discriminant to rational coefficients preserves its
analytic expansion, including its zero negative range. -/
theorem discriminantProgressionLaurent_hasSum (M : ℕ) (hM : M ≠ 0)
    (τ : UpperHalfPlane) :
    HasSum (fun r : ℤ =>
      (((discriminantProgressionLaurent M hM).map (Int.castRingHom ℚ)).coeff r : ℂ) *
        Function.Periodic.qParam M τ ^ r) (ModularForm.eta τ ^ 24) := by
  have hinj : Function.Injective (fun n : ℕ => (n : ℤ)) := by
    intro n k h
    change (n : ℤ) = (k : ℤ) at h
    omega
  apply (hinj.hasSum_iff ?_).mp
  · change HasSum (fun n : ℕ =>
      (((discriminantProgressionLaurent M hM).map (Int.castRingHom ℚ)).coeff
        (n : ℤ) : ℂ) * Function.Periodic.qParam M τ ^ (n : ℤ)) _
    simpa only [QSeries.laurent_map_coeff, discriminantProgressionLaurent,
      HahnSeries.ofPowerSeries_apply_coeff, Int.coe_castRingHom, Rat.cast_intCast,
      zpow_natCast] using discriminantProgressionPowerSeries_hasSum M hM τ
  · intro r hr
    have hneg : r < 0 := by
      by_contra h
      exact hr ⟨r.toNat, Int.toNat_of_nonneg (by omega)⟩
    simp only [QSeries.laurent_map_coeff,
      discriminantProgressionLaurent_zero_below M hM r hneg, map_zero,
      Rat.cast_zero, zero_mul]

/-- Multiplication by an actual integral power of `Δ` clears poles without
changing the analytic interpretation of a Laurent expansion. -/
theorem discriminantProgression_mul_pow_hasSum
    (M : ℕ) (hM : M ≠ 0) (F : LaurentSeries ℚ) (B : ℕ)
    (hF : ∀ r : ℤ, r < -(B : ℤ) → F.coeff r = 0)
    (τ : UpperHalfPlane) (a : ℂ)
    (ha : HasSum (fun r : ℤ => (F.coeff r : ℂ) *
      Function.Periodic.qParam M τ ^ r) a) (s R : ℕ) :
    HasSum (fun r : ℤ =>
      ((((discriminantProgressionLaurent M hM).map (Int.castRingHom ℚ)) ^ s *
        F ^ R).coeff r : ℂ) * Function.Periodic.qParam M τ ^ r)
      ((ModularForm.eta τ ^ 24) ^ s * a ^ R) := by
  have hd : ∀ r : ℤ, r < -(0 : ℤ) →
      ((discriminantProgressionLaurent M hM).map (Int.castRingHom ℚ)).coeff r = 0 := by
    intro r hr
    simp only [QSeries.laurent_map_coeff,
      discriminantProgressionLaurent_zero_below M hM r (by omega), map_zero]
  exact laurent_mul_hasSum _ _ (0 * s) (B * R)
    (laurent_pow_zero_below _ 0 hd s) (laurent_pow_zero_below F B hF R)
    _ _ _ (Complex.exp_ne_zero _)
    (laurent_pow_hasSum _ 0 hd _ _ (Complex.exp_ne_zero _)
      (discriminantProgressionLaurent_hasSum M hM τ) s)
    (laurent_pow_hasSum F B hF _ _ (Complex.exp_ne_zero _) ha R)

/-- A nonnegative row supported on multiples of `M` is an ordinary width-one
Fourier expansion. This is a reindexing of the actual convergent series. -/
theorem progression_hasSum_width_one (M : ℕ) (hM : M ≠ 0) (c : ℤ → ℂ)
    (hneg : ∀ r < 0, c r = 0)
    (hsupport : ∀ r, c r ≠ 0 → (r : ZMod M) = 0)
    (τ : UpperHalfPlane) (a : ℂ)
    (ha : HasSum (fun r : ℤ => c r * Function.Periodic.qParam M τ ^ r) a) :
    HasSum (fun n : ℕ => c ((M : ℤ) * n) * Function.Periodic.qParam 1 τ ^ n) a := by
  let idx : ℕ → ℤ := fun n => (M : ℤ) * n
  have hinj : Function.Injective idx := by
    intro n k h
    change (M : ℤ) * n = (M : ℤ) * k at h
    have h' := mul_left_cancel₀ (show (M : ℤ) ≠ 0 by exact_mod_cast hM) h
    exact_mod_cast h'
  have hout : ∀ r, r ∉ Set.range idx →
      c r * Function.Periodic.qParam M τ ^ r = 0 := by
    intro r hr
    suffices hc : c r = 0 by rw [hc, zero_mul]
    by_contra hc
    have hr0 : 0 ≤ r := le_of_not_gt (fun h => hc (hneg r h))
    have hd : (M : ℤ) ∣ r := (ZMod.intCast_zmod_eq_zero_iff_dvd r M).mp (hsupport r hc)
    obtain ⟨k, hk⟩ := hd
    have hk0 : 0 ≤ k := nonneg_of_mul_nonneg_right (hk ▸ hr0)
      (show (0 : ℤ) < M by exact_mod_cast Nat.pos_of_ne_zero hM)
    exact hr ⟨k.toNat, by dsimp [idx]; rw [Int.toNat_of_nonneg hk0, ← hk]⟩
  have hs := (hinj.hasSum_iff hout).mpr ha
  change HasSum (fun n : ℕ => c ((M : ℤ) * n) *
    Function.Periodic.qParam M τ ^ ((M : ℤ) * n)) a at hs
  have hp (n : ℕ) : Function.Periodic.qParam M τ ^ ((M : ℤ) * n) =
      Function.Periodic.qParam 1 τ ^ n := by
    rw [zpow_mul, zpow_natCast, zpow_natCast, qParam_nat_pow M hM]
  simpa only [hp] using hs

end SptClassification
