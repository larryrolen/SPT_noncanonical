/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.WeightTwoConstantTermHeckeCusp

/-!
# Fractional translations of period-24 meromorphic cusp germs

A horizontal translation by `24j/n` rotates the period-24 nome by an
`n`th root of unity. Thus finite weighted sums of these translations have
direct meromorphic cusp representatives, with the actual complex weights
retained. This supplies the cusp part of finite translation operators used
in half-integral Hecke arguments [rolenManuscript, §3].
-/

public section

namespace SptClassification

open UpperHalfPlane

/-- Translation by a rational fraction of the period 24 preserves the
upper half-plane. -/
noncomputable def cuspFractionTranslate (n j : ℕ) (_hn : 0 < n)
    (τ : UpperHalfPlane) : UpperHalfPlane :=
  ⟨(τ : ℂ) + 24 * j / n, by simpa using τ.im_pos⟩

/-- The complex coordinate of fractional translation. -/
theorem cuspFractionTranslate_coe (n j : ℕ) (hn : 0 < n)
    (τ : UpperHalfPlane) :
    (cuspFractionTranslate n j hn τ : ℂ) = (τ : ℂ) + 24 * j / n := (rfl)

/-- Fractional translation rotates the period-24 nome by the corresponding
root of unity. -/
theorem qParam_twentyFour_fractionTranslate (n j : ℕ) (hn : 0 < n)
    (z : ℂ) :
    Function.Periodic.qParam 24 (z + 24 * j / n) =
      cuspRoot n j * Function.Periodic.qParam 24 z := by
  unfold Function.Periodic.qParam
  rw [cuspRoot_eq]
  rw [← Complex.exp_add]
  congr 1
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  norm_num
  field_simp
  ring

/-- The meromorphic cusp germ of a single fractionally translated value. -/
theorem meromorphicCusp_fractionTranslate {f : UpperHalfPlane → ℂ}
    {G : ℂ → ℂ} (hG : MeromorphicAt G 0)
    (hEq : ∀ τ : UpperHalfPlane,
      G (Function.Periodic.qParam 24 τ) = f τ)
    (n j : ℕ) (hn : 0 < n) :
    ∃ H : ℂ → ℂ, MeromorphicAt H 0 ∧
      ∀ τ : UpperHalfPlane,
        H (Function.Periodic.qParam 24 τ) =
          f (cuspFractionTranslate n j hn τ) := by
  refine ⟨fun q => G (cuspRoot n j * q),
    meromorphicAt_cuspRootTwist hG (cuspRoot n j), ?_⟩
  intro τ
  change G (cuspRoot n j * Function.Periodic.qParam 24 τ) =
    f (cuspFractionTranslate n j hn τ)
  rw [← qParam_twentyFour_fractionTranslate n j hn]
  exact hEq (cuspFractionTranslate n j hn τ)

/-- The direct period-24 cusp representative of a weighted finite
translation sum. -/
noncomputable def cuspWeightedRootSum (G : ℂ → ℂ) (w : ℕ → ℂ)
    (n : ℕ) : ℂ → ℂ :=
  fun q => ∑ j ∈ Finset.range n, w j * G (cuspRoot n j * q)

/-- Finite weighted root sums preserve meromorphy at the cusp. -/
theorem meromorphicAt_cuspWeightedRootSum {G : ℂ → ℂ}
    (hG : MeromorphicAt G 0) (w : ℕ → ℂ) (n : ℕ) :
    MeromorphicAt (cuspWeightedRootSum G w n) 0 := by
  classical
  unfold cuspWeightedRootSum
  induction Finset.range n using Finset.induction_on with
  | empty =>
      simp
  | @insert j s hjs ih =>
      have hj : MeromorphicAt
          (fun q : ℂ => w j * G (cuspRoot n j * q)) 0 :=
        ((analyticAt_const :
          AnalyticAt ℂ (fun _ : ℂ => w j) 0).meromorphicAt).fun_mul
            (meromorphicAt_cuspRootTwist hG (cuspRoot n j))
      simpa [Finset.sum_insert hjs] using hj.fun_add ih

/-- The weighted root sum evaluates to the actual translated values at
every upper-half-plane point. No modularity law is needed. -/
theorem cuspWeightedRootSum_qParam {f : UpperHalfPlane → ℂ}
    {G : ℂ → ℂ}
    (hEq : ∀ τ : UpperHalfPlane,
      G (Function.Periodic.qParam 24 τ) = f τ)
    (w : ℕ → ℂ) (n : ℕ) (hn : 0 < n)
    (τ : UpperHalfPlane) :
    cuspWeightedRootSum G w n (Function.Periodic.qParam 24 τ) =
      ∑ j ∈ Finset.range n, w j * f (cuspFractionTranslate n j hn τ) := by
  unfold cuspWeightedRootSum
  apply Finset.sum_congr rfl
  intro j _
  rw [← qParam_twentyFour_fractionTranslate n j hn]
  exact congrArg (w j * ·) (hEq (cuspFractionTranslate n j hn τ))

/-- A finite weighted sum of fractional translations has a meromorphic
period-24 cusp germ, with all weights preserved exactly. -/
theorem meromorphicCusp_weightedFractionTranslations
    {f : UpperHalfPlane → ℂ} {G : ℂ → ℂ}
    (hG : MeromorphicAt G 0)
    (hEq : ∀ τ : UpperHalfPlane,
      G (Function.Periodic.qParam 24 τ) = f τ)
    (w : ℕ → ℂ) (n : ℕ) (hn : 0 < n) :
    ∃ H : ℂ → ℂ, MeromorphicAt H 0 ∧
      ∀ τ : UpperHalfPlane,
        H (Function.Periodic.qParam 24 τ) =
          ∑ j ∈ Finset.range n,
            w j * f (cuspFractionTranslate n j hn τ) := by
  exact ⟨cuspWeightedRootSum G w n,
    meromorphicAt_cuspWeightedRootSum hG w n,
    cuspWeightedRootSum_qParam hEq w n hn⟩

/-- Fractional translation sums of the actual inverse-eta weak forms have
meromorphic period-24 cusp germs. This supplies the cusp property when the
weights are later specialized to a character or multiplier. -/
theorem EtaInverseWeaklyHolomorphicForm.has_meromorphic_cusp_weightedTranslations
    {k : ℕ} (f : EtaInverseWeaklyHolomorphicForm k)
    (w : ℕ → ℂ) (n : ℕ) (hn : 0 < n) :
    ∃ H : ℂ → ℂ, MeromorphicAt H 0 ∧
      ∀ τ : UpperHalfPlane,
        H (Function.Periodic.qParam 24 τ) =
          ∑ j ∈ Finset.range n,
            w j * f (cuspFractionTranslate n j hn τ) := by
  obtain ⟨G, hG, hEq⟩ := f.has_meromorphic_cusp
  exact meromorphicCusp_weightedFractionTranslations hG hEq w n hn

end SptClassification
