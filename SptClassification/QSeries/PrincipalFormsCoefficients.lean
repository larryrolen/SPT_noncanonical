/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.PrincipalPartIntegral

/-!
# Integer Fourier coefficients of the prescribed principal forms

The row coordinate is converted to the exponent of `exp(2πiτ/24)`. Both
families have exponents congruent to one modulo 24, but the derivative family
has the extra pole shift. These are the coefficients in
[rolenManuscript, §3, equations (H) and (K)].
-/

public section

namespace SptClassification.QSeries

/-- The full integer-indexed H coefficients, with prescribed coefficient `-a` at one. -/
noncomputable def principalHFourier (d : ℕ) (a r : ℤ) : ℤ :=
  if r % 24 = 1 then integralHPrincipalPart d a ((1 - r) / 24) else 0

/-- The full integer-indexed K coefficients, including the derivative pole shift. -/
noncomputable def principalKFourier (d : ℕ) (r : ℤ) : ℤ :=
  if r % 24 = 1 then integralKPrincipalPart d ((1 - r) / 24 - 1) else 0

/-- H row index `k` represents exponent `1 - 24k`. -/
theorem principalHFourier_row (d : ℕ) (a k : ℤ) :
    principalHFourier d a (1 - 24 * k) = integralHPrincipalPart d a k := by
  simp only [principalHFourier, show (1 - 24 * k) % 24 = 1 by omega, ite_true,
    show (1 - (1 - 24 * k)) / 24 = k by omega]

/-- K row index `k` represents exponent `1 - 24(k+1)`. -/
theorem principalKFourier_row (d : ℕ) (k : ℤ) :
    principalKFourier d (1 - 24 * (k + 1)) = integralKPrincipalPart d k := by
  simp only [principalKFourier, show (1 - 24 * (k + 1)) % 24 = 1 by omega, ite_true,
    show (1 - (1 - 24 * (k + 1))) / 24 - 1 = k by omega]

/-- The H coefficient at exponent one is exactly the prescribed integer. -/
theorem principalHFourier_one (d : ℕ) (hd : d % 24 = 23) (a : ℤ) :
    principalHFourier d a 1 = -a := by
  simpa only [mul_zero, sub_zero] using
    (principalHFourier_row d a 0).trans (integralHPrincipalPart_constant d hd a)

/-- The only negative H coefficient is the leading coefficient at `-d`. -/
theorem principalHFourier_negative (d : ℕ) (hd : d % 24 = 23) (a r : ℤ)
    (hr : r < 0) : principalHFourier d a r = if r = -(d : ℤ) then 1 else 0 := by
  have hn := principalIndex_mul d hd
  by_cases hmod : r % 24 = 1
  · let k : ℕ := ((1 - r) / 24).toNat
    have hk : 0 < k := by dsimp [k]; omega
    have hki : (1 - r) / 24 = (k : ℤ) := by dsimp [k]; omega
    rw [principalHFourier, ite_eq_left hmod, hki, integralHPrincipalPart_pole d a k hk]
    have he : k = principalIndex d ↔ r = -(d : ℤ) := by omega
    simp only [he]
  · rw [principalHFourier, ite_eq_right hmod, ite_eq_right]
    intro he
    subst r
    omega

/-- The only negative K coefficient is the leading coefficient at `-d`. -/
theorem principalKFourier_negative (d : ℕ) (hd : d % 24 = 23) (r : ℤ)
    (hr : r < 0) : principalKFourier d r = if r = -(d : ℤ) then 1 else 0 := by
  have hn := principalIndex_mul d hd
  have hnpos := principalIndex_pos d hd
  by_cases hmod : r % 24 = 1
  · let k : ℕ := ((1 - r) / 24 - 1).toNat
    have hki : (1 - r) / 24 - 1 = (k : ℤ) := by dsimp [k]; omega
    rw [principalKFourier, ite_eq_left hmod, hki, integralKPrincipalPart_pole]
    have he : k = principalIndex d - 1 ↔ r = -(d : ℤ) := by omega
    simp only [he]
  · rw [principalKFourier, ite_eq_right hmod, ite_eq_right]
    intro he
    subst r
    omega

/-- Both families have zero coefficient outside the eta exponent class. -/
theorem principalFourier_zero_of_mod_ne (d : ℕ) (a r : ℤ) (hr : r % 24 ≠ 1) :
    principalHFourier d a r = 0 ∧ principalKFourier d r = 0 := by
  simp [principalHFourier, principalKFourier, hr]

end SptClassification.QSeries
