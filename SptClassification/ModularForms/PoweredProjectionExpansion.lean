/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.DiscriminantProgression

/-! # Width-one expansions of pole-cleared powered projections

All rows below are coefficients of actual Laurent products. The exponent may
be divisible by the reduction prime [rolenManuscript, §2].
-/

public section

namespace SptClassification

/-- Pole clearing leaves only nonnegative multiples of the progression modulus. -/
theorem poleClearedLaurent_support
    (M : ℕ) (hM : M ≠ 0) (F : LaurentSeries ℚ) (B : ℕ) (u : ZMod M)
    (hbelow : ∀ r, F.coeff r ≠ 0 → -(B : ℤ) ≤ r)
    (hres : ∀ r, F.coeff r ≠ 0 → (r : ZMod M) = u)
    (s R : ℕ) (hR : M ∣ R) (hs : B * R ≤ s * M) :
    ∀ r, ((((discriminantProgressionLaurent M hM).map (Int.castRingHom ℚ)) ^ s *
      F ^ R).coeff r) ≠ 0 → 0 ≤ r ∧ (r : ZMod M) = 0 := by
  let δ := (discriminantProgressionLaurent M hM).map (Int.castRingHom ℚ)
  have hd (r : ℤ) (hr : δ.coeff r ≠ 0) :
      (discriminantProgressionLaurent M hM).coeff r ≠ 0 := by
    intro hz
    apply hr
    simp only [δ, QSeries.laurent_map_coeff, hz, map_zero]
  have hdLower : ∀ r, δ.coeff r ≠ 0 → (M : ℤ) ≤ r :=
    fun r hr => discriminantProgressionLaurent_support_lower M hM r (hd r hr)
  have hdRes : ∀ r, δ.coeff r ≠ 0 → (r : ZMod M) = 0 :=
    fun r hr => discriminantProgressionLaurent_support_residue M hM r (hd r hr)
  have hprodLower := QSeries.laurent_mul_support_lower (δ ^ s) (F ^ R)
    ((s : ℤ) * M) ((R : ℤ) * -(B : ℤ))
    (QSeries.laurent_pow_support_lower δ M hdLower s)
    (QSeries.laurent_pow_support_lower F (-(B : ℤ)) hbelow R)
  have hR0 : (R : ZMod M) = 0 := (ZMod.natCast_eq_zero_iff R M).mpr hR
  have hprodRes : ∀ r, (δ ^ s * F ^ R).coeff r ≠ 0 → (r : ZMod M) = 0 := by
    simpa only [mul_zero, hR0, zero_mul, add_zero] using
      QSeries.laurent_mul_support_residue (δ ^ s) (F ^ R) M
        ((s : ZMod M) * 0) ((R : ZMod M) * u)
        (QSeries.laurent_pow_support_residue δ M 0 hdRes s)
        (QSeries.laurent_pow_support_residue F M u hres R)
  intro r hr
  refine ⟨?_, hprodRes r hr⟩
  have hb := hprodLower r hr
  have hs' : (B : ℤ) * R ≤ (s : ℤ) * M := by exact_mod_cast hs
  nlinarith

/-- A sufficiently pole-cleared power of a single-residue Laurent series
has the width-one expansion obtained by taking its coefficients at `M*n`. -/
theorem poleClearedLaurent_hasSum_width_one
    (M : ℕ) (hM : M ≠ 0) (F : LaurentSeries ℚ) (B : ℕ) (u : ZMod M)
    (hbelow : ∀ r, F.coeff r ≠ 0 → -(B : ℤ) ≤ r)
    (hres : ∀ r, F.coeff r ≠ 0 → (r : ZMod M) = u)
    (s R : ℕ) (hR : M ∣ R) (hs : B * R ≤ s * M)
    (τ : UpperHalfPlane) (a : ℂ)
    (ha : HasSum (fun r : ℤ => (F.coeff r : ℂ) *
      Function.Periodic.qParam M τ ^ r) a) :
    HasSum (fun n : ℕ =>
      ((((discriminantProgressionLaurent M hM).map (Int.castRingHom ℚ)) ^ s *
        F ^ R).coeff ((M : ℤ) * n) : ℂ) * Function.Periodic.qParam 1 τ ^ n)
      ((ModularForm.eta τ ^ 24) ^ s * a ^ R) := by
  let δ := (discriminantProgressionLaurent M hM).map (Int.castRingHom ℚ)
  have hsupp := poleClearedLaurent_support M hM F B u hbelow hres s R hR hs
  apply progression_hasSum_width_one M hM
    (fun r => ((δ ^ s * F ^ R).coeff r : ℂ)) ?_ ?_ τ _
    (discriminantProgression_mul_pow_hasSum M hM F B
      (fun r hr => by by_contra hn; have := hbelow r hn; omega) τ a ha s R)
  · intro r hr
    have hz : (δ ^ s * F ^ R).coeff r = 0 := by
      by_contra hn
      exact (not_le_of_gt hr) (hsupp r hn).1
    rw [hz, Rat.cast_zero]
  · intro r hr
    exact (hsupp r (fun hz => hr (by rw [hz, Rat.cast_zero]))).2

/-- The manuscript's actual scaled projection has this width-one row after
raising to a modulus-divisible power and clearing its explicit pole bound. -/
theorem analyticProgression_poleCleared_hasSum_width_one {p : ℕ}
    (g : ModularProgressionForm p) (M : ℕ) (hM : 0 < M) (u : ℤ) (c : ℚ)
    (B : ℕ) (hB : ∀ r : ℤ, r < -(B : ℤ) → g.coeff r = 0)
    (s R : ℕ) (hR : M ∣ R) (hs : B * R ≤ s * M) (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ =>
      ((((discriminantProgressionLaurent M (Nat.ne_of_gt hM)).map
          (Int.castRingHom ℚ)) ^ s *
        (c • QSeries.progressionLaurent g.coeff M u g.lowerBound) ^ R).coeff
          ((M : ℤ) * n) : ℂ) * Function.Periodic.qParam 1 τ ^ n)
      ((ModularForm.eta τ ^ 24) ^ s *
        ((c : ℂ) * analyticProgression M hM u g.toFun τ) ^ R) := by
  apply poleClearedLaurent_hasSum_width_one M (Nat.ne_of_gt hM) _ B u
    ?_ ?_ s R hR hs τ _ (analyticProgression_scaled_laurent_hasSum g M hM u c τ)
  · intro r hr
    by_contra h
    apply hr
    rw [HahnSeries.coeff_smul, QSeries.progressionLaurent_coeff]
    by_cases hu : (r : ZMod M) = (u : ZMod M)
    · rw [QSeries.progressionRow_eq_of _ _ _ _ hu, hB r (by omega), smul_zero]
    · rw [QSeries.progressionRow_eq_zero_of _ _ _ _ hu, smul_zero]
  · intro r hr
    by_contra h
    apply hr
    rw [HahnSeries.coeff_smul, QSeries.progressionLaurent_coeff,
      QSeries.progressionRow_eq_zero_of _ _ _ _ h, smul_zero]

end SptClassification
