/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.WeightTwoConstantTerm

/-!
# Uniqueness of convergent Fourier rows at a cusp

For a holomorphic period-one function, an everywhere convergent power-series
row determines its analytic cusp coefficients. This comparison is useful after
clearing the pole of a Laurent Fourier series.
-/

public section

namespace SptClassification

open UpperHalfPlane Filter
open scoped Manifold

/-- Every everywhere convergent integral-index Fourier row is period one on
the upper half-plane. This supplies the periodicity used when clearing a
Laurent pole without adding it as independent analytic data. -/
theorem laurentRow_periodic {F : UpperHalfPlane → ℂ} (c : ℤ → ℂ)
    (hs : ∀ τ : UpperHalfPlane,
      HasSum (fun r : ℤ => c r * Function.Periodic.qParam 1 τ ^ r) (F τ)) :
    Function.Periodic (F ∘ ofComplex) 1 := by
  intro z
  by_cases hz : 0 < z.im
  · have hz1 : 0 < (z + 1).im := by simpa using hz
    let τ : UpperHalfPlane := ⟨z, hz⟩
    let τ1 : UpperHalfPlane := ⟨z + 1, hz1⟩
    have hq : Function.Periodic.qParam 1 τ1 =
        Function.Periodic.qParam 1 τ := by
      change Function.Periodic.qParam 1 (z + 1) =
        Function.Periodic.qParam 1 z
      simp [Function.Periodic.qParam, add_mul, mul_add, Complex.exp_add,
        mul_comm, mul_left_comm]
      convert Complex.exp_two_pi_mul_I using 1
      ring_nf
    have heq : F τ1 = F τ := by
      rw [← (hs τ1).tsum_eq, ← (hs τ).tsum_eq]
      congr 1
      funext r
      rw [hq]
    simpa only [Function.comp_apply, ofComplex_apply_of_im_pos hz,
      ofComplex_apply_of_im_pos hz1] using heq
  · have hz1 : ¬ 0 < (z + 1).im := by simpa using hz
    have hnot : ¬ ∃ a : UpperHalfPlane, a ∈ Set.univ ∧ (a : ℂ) = z := by
      rintro ⟨a, _, ha⟩
      apply hz
      rw [← ha]
      exact a.im_pos
    have hnot1 : ¬ ∃ a : UpperHalfPlane, a ∈ Set.univ ∧ (a : ℂ) = z + 1 := by
      rintro ⟨a, _, ha⟩
      apply hz1
      rw [← ha]
      exact a.im_pos
    have heq : (ofComplex (z + 1) : UpperHalfPlane) = ofComplex z := by
      simp [UpperHalfPlane.ofComplex,
        Topology.IsOpenEmbedding.toOpenPartialHomeomorph, Function.invFunOn]
      simp only [dite_eq_right hnot1, dite_eq_right hnot]
    exact congrArg F heq

/-- A convergent Fourier row on the upper half-plane is bounded at its cusp.
Convergence at one nonzero nome bounds the row at every smaller nome. -/
theorem isBoundedAtImInfty_of_fourierRow {c : ℕ → ℂ}
    {F : UpperHalfPlane → ℂ}
    (hF : ∀ τ : UpperHalfPlane,
      HasSum (fun n => c n * Function.Periodic.qParam 1 τ ^ n) (F τ)) :
    IsBoundedAtImInfty F := by
  let τ₀ : UpperHalfPlane := ⟨Complex.I, by norm_num⟩
  let q₀ : ℂ := Function.Periodic.qParam 1 τ₀
  have hq₀ : 0 < ‖q₀‖ := norm_pos_iff.mpr (Complex.exp_ne_zero _)
  have hs₀ : Summable (fun n : ℕ => ‖c n * q₀ ^ n‖) := (hF τ₀).summable.norm
  have hq : Tendsto (fun τ : UpperHalfPlane => Function.Periodic.qParam 1 τ)
      atImInfty (nhds 0) := qParam_tendsto_atImInfty (by norm_num)
  have hev : ∀ᶠ τ : UpperHalfPlane in atImInfty,
      ‖Function.Periodic.qParam 1 τ‖ < ‖q₀‖ :=
    hq.norm.eventually (Iio_mem_nhds (by simpa using hq₀))
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp hev
  refine isBoundedAtImInfty_iff.mpr ⟨∑' n : ℕ, ‖c n * q₀ ^ n‖, A, ?_⟩
  intro τ hτ
  have hn (n : ℕ) :
      ‖c n * Function.Periodic.qParam 1 τ ^ n‖ ≤ ‖c n * q₀ ^ n‖ := by
    simp only [norm_mul, norm_pow]
    gcongr
    exact (hA τ hτ).le
  calc
    ‖F τ‖ = ‖∑' n : ℕ, c n * Function.Periodic.qParam 1 τ ^ n‖ := by
      rw [(hF τ).tsum_eq]
    _ ≤ ∑' n : ℕ, ‖c n * Function.Periodic.qParam 1 τ ^ n‖ :=
      norm_tsum_le_tsum_norm ((hF τ).summable.norm)
    _ ≤ ∑' n : ℕ, ‖c n * q₀ ^ n‖ :=
      Summable.tsum_le_tsum hn ((hF τ).summable.norm) hs₀

/-- The analytic cusp expansion recovers each coefficient of any convergent
Fourier row of a holomorphic period-one function. -/
theorem fourierRow_coeff_eq_qExpansion {F : UpperHalfPlane → ℂ}
    (hhol : MDiff F)
    (hper : Function.Periodic (F ∘ ofComplex) 1)
    (c : ℕ → ℂ)
    (hs : ∀ τ : UpperHalfPlane,
      HasSum (fun n => c n * Function.Periodic.qParam 1 τ ^ n) (F τ))
    (n : ℕ) : c n = (qExpansion 1 F).coeff n := by
  have hb : IsBoundedAtImInfty F := isBoundedAtImInfty_of_fourierRow hs
  have ha : AnalyticAt ℂ (cuspFunction 1 F) 0 :=
    analyticAt_cuspFunction_zero (by norm_num) hper hhol hb
  let Fc : C(UpperHalfPlane, ℂ) := ⟨F, hhol.continuous⟩
  change c n = (qExpansion 1 Fc).coeff n
  apply qExpansion_coeff_unique (f := Fc) (by norm_num : (0 : ℝ) < 1) ha
  intro τ
  simpa only [smul_eq_mul, Fc, ContinuousMap.coe_mk] using hs τ

/-- Two convergent Fourier rows for the same holomorphic period-one function
have the same coefficients. In Laurent applications the rows are first
shifted by a common pole-clearing exponent. -/
theorem fourierRow_unique {F : UpperHalfPlane → ℂ}
    (hhol : MDiff F)
    (hper : Function.Periodic (F ∘ ofComplex) 1)
    (a b : ℕ → ℂ)
    (ha : ∀ τ : UpperHalfPlane,
      HasSum (fun n => a n * Function.Periodic.qParam 1 τ ^ n) (F τ))
    (hb : ∀ τ : UpperHalfPlane,
      HasSum (fun n => b n * Function.Periodic.qParam 1 τ ^ n) (F τ)) :
    a = b := by
  funext n
  exact (fourierRow_coeff_eq_qExpansion hhol hper a ha n).trans
    (fourierRow_coeff_eq_qExpansion hhol hper b hb n).symm

/-- Multiplication by `q ^ M` turns a Laurent Fourier row supported from
`-M` onward into an ordinary power-series row. The reindexing includes the
coefficient at the pole and does not impose any integrality condition on `M`. -/
theorem laurentRow_poleCleared_hasSum (c : ℤ → ℂ) (M : ℕ)
    (hbelow : ∀ r : ℤ, r < -(M : ℤ) → c r = 0)
    (q F : ℂ) (hq : q ≠ 0)
    (hs : HasSum (fun r : ℤ => c r * q ^ r) F) :
    HasSum (fun n : ℕ => c ((n : ℤ) - M) * q ^ n) (q ^ M * F) := by
  let shift : ℕ → ℤ := fun n => (n : ℤ) - M
  have hinj : Function.Injective shift := by
    intro n k h
    dsimp [shift] at h
    omega
  have hout (r : ℤ) (hr : r ∉ Set.range shift) :
      c r * q ^ r = 0 := by
    have hrlt : r < -(M : ℤ) := by
      by_contra h
      let n : ℕ := (r + M).toNat
      have hn : (n : ℤ) = r + M := Int.toNat_of_nonneg (by omega)
      apply hr
      refine ⟨n, ?_⟩
      dsimp [shift]
      omega
    rw [hbelow r hrlt, zero_mul]
  have hshift : HasSum (fun n : ℕ => c (shift n) * q ^ shift n) F :=
    (hinj.hasSum_iff hout).2 hs
  have hmul := hshift.mul_left (q ^ M)
  convert hmul using 1
  ext n
  dsimp [shift]
  have hidx : (M : ℤ) + ((n : ℤ) - M) = n := by omega
  have hpow : q ^ M * q ^ ((n : ℤ) - M) = q ^ n := by
    rw [← zpow_natCast q M, ← zpow_add₀ hq, hidx, zpow_natCast]
  rw [← hpow]
  ring

/-- A holomorphic period-one function has at most one convergent Laurent row
with a specified lower bound. Its pole-cleared row is compared by analytic
Fourier uniqueness, including the coefficients above the pole. -/
theorem laurentRow_unique {F : UpperHalfPlane → ℂ} (M : ℕ)
    (hhol : MDiff (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam 1 τ ^ M * F τ))
    (hper : Function.Periodic
      ((fun τ : UpperHalfPlane =>
        Function.Periodic.qParam 1 τ ^ M * F τ) ∘ ofComplex) 1)
    (a b : ℤ → ℂ)
    (haBelow : ∀ r : ℤ, r < -(M : ℤ) → a r = 0)
    (hbBelow : ∀ r : ℤ, r < -(M : ℤ) → b r = 0)
    (ha : ∀ τ : UpperHalfPlane,
      HasSum (fun r : ℤ => a r * Function.Periodic.qParam 1 τ ^ r) (F τ))
    (hb : ∀ τ : UpperHalfPlane,
      HasSum (fun r : ℤ => b r * Function.Periodic.qParam 1 τ ^ r) (F τ)) :
    a = b := by
  have ha' (τ : UpperHalfPlane) :
      HasSum (fun n : ℕ =>
        a ((n : ℤ) - M) * Function.Periodic.qParam 1 τ ^ n)
        (Function.Periodic.qParam 1 τ ^ M * F τ) :=
    laurentRow_poleCleared_hasSum a M haBelow _ _
      (Complex.exp_ne_zero _) (ha τ)
  have hb' (τ : UpperHalfPlane) :
      HasSum (fun n : ℕ =>
        b ((n : ℤ) - M) * Function.Periodic.qParam 1 τ ^ n)
        (Function.Periodic.qParam 1 τ ^ M * F τ) :=
    laurentRow_poleCleared_hasSum b M hbBelow _ _
      (Complex.exp_ne_zero _) (hb τ)
  have hrow := fourierRow_unique hhol hper
    (fun n : ℕ => a ((n : ℤ) - M))
    (fun n : ℕ => b ((n : ℤ) - M)) ha' hb'
  funext r
  by_cases hr : r < -(M : ℤ)
  · rw [haBelow r hr, hbBelow r hr]
  · let n : ℕ := (r + M).toNat
    have hn : (n : ℤ) = r + M := Int.toNat_of_nonneg (by omega)
    have hrn : (n : ℤ) - M = r := by omega
    simpa only [hrn] using congrFun hrow n

end SptClassification
