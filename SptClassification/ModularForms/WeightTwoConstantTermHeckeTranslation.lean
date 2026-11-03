/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.WeightTwoConstantTermHeckeHolomorphic

/-!
# Translation of analytic inverse-eta Hecke summands

An inverse-eta weak form has the conjugate eta phase under translation by
one. Fractional translations commute with this integral translation, so
their finite weighted sum has the same phase for arbitrary complex weights.
This is the translation part of the analytic Hecke construction; the affine
root average and dilation require their own arithmetic arguments
[rolenManuscript, §3].
-/

public section

namespace SptClassification

open UpperHalfPlane
open scoped MatrixGroups

/-- Every actual inverse-eta weak form has the conjugate eta translation
phase, independently of its integral weight [apostol1990, Chapter 3]. -/
theorem EtaInverseWeaklyHolomorphicForm.translation
    {k : ℕ} (f : EtaInverseWeaklyHolomorphicForm k)
    (τ : UpperHalfPlane) :
    f (upperUnipotent 1 • τ) =
      (Complex.exp (Real.pi * Complex.I / 12))⁻¹ * f τ := by
  have hγ : Matrix.SpecialLinearGroup.mapGL ℝ (upperUnipotent 1) ∈ 𝒮ℒ :=
    ⟨upperUnipotent 1, rfl⟩
  have hd : denom (Matrix.SpecialLinearGroup.mapGL ℝ (upperUnipotent 1)) τ = 1 := by
    have hm : ((Matrix.SpecialLinearGroup.mapGL ℝ (upperUnipotent 1) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) = !![1, 1; 0, 1] := by
      simp only [Matrix.SpecialLinearGroup.mapGL_coe_matrix,
        Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [upperUnipotent_matrix, Matrix.map_apply]
    simp [UpperHalfPlane.denom, hm]
  have h := f.map_action _ hγ τ
  change f (upperUnipotent 1 • τ) =
    (etaAutomorphyFactor (Matrix.SpecialLinearGroup.mapGL ℝ (upperUnipotent 1)) τ)⁻¹ *
      denom (Matrix.SpecialLinearGroup.mapGL ℝ (upperUnipotent 1)) τ ^ k * f τ at h
  rw [etaAutomorphyFactor_upperUnipotent, hd] at h
  simpa using h

/-- A fractional translation of the period-24 cusp coordinate commutes
with translation by one on the upper half-plane. -/
theorem cuspFractionTranslate_upperUnipotent (n j : ℕ) (hn : 0 < n)
    (τ : UpperHalfPlane) :
    cuspFractionTranslate n j hn (upperUnipotent 1 • τ) =
      upperUnipotent 1 • cuspFractionTranslate n j hn τ := by
  apply UpperHalfPlane.ext
  rw [cuspFractionTranslate_coe]
  rw [upperUnipotent_apply, upperUnipotent_apply]
  rw [cuspFractionTranslate_coe]
  ring

/-- The weighted fractional Hecke sum carries the precise inverse-eta
translation phase for every choice of weights. -/
theorem EtaInverseWeaklyHolomorphicForm.weightedFractionSum_translation
    {k : ℕ} (f : EtaInverseWeaklyHolomorphicForm k)
    (w : ℕ → ℂ) (n : ℕ) (hn : 0 < n) (τ : UpperHalfPlane) :
    (∑ j ∈ Finset.range n,
      w j * f (cuspFractionTranslate n j hn (upperUnipotent 1 • τ))) =
      (Complex.exp (Real.pi * Complex.I / 12))⁻¹ *
        ∑ j ∈ Finset.range n, w j * f (cuspFractionTranslate n j hn τ) := by
  calc
    (∑ j ∈ Finset.range n,
        w j * f (cuspFractionTranslate n j hn (upperUnipotent 1 • τ))) =
      ∑ j ∈ Finset.range n,
        (Complex.exp (Real.pi * Complex.I / 12))⁻¹ *
          (w j * f (cuspFractionTranslate n j hn τ)) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [cuspFractionTranslate_upperUnipotent, f.translation]
        ring
    _ = (Complex.exp (Real.pi * Complex.I / 12))⁻¹ *
          ∑ j ∈ Finset.range n, w j * f (cuspFractionTranslate n j hn τ) := by
        rw [Finset.mul_sum]

private theorem sum_range_rotate (u : ℕ → ℂ) (N : ℕ) (hu : u N = u 0) :
    (∑ j ∈ Finset.range N, u (j + 1)) = ∑ j ∈ Finset.range N, u j := by
  have hleft := Finset.sum_range_succ' u N
  have hright := Finset.sum_range_succ u N
  calc
    (∑ j ∈ Finset.range N, u (j + 1)) =
        (∑ j ∈ Finset.range (N + 1), u j) - u 0 := by rw [hleft]; ring
    _ = ∑ j ∈ Finset.range N, u j := by rw [hright, hu]; ring

private theorem sum_range_shift (u : ℕ → ℂ) (N k : ℕ)
    (hu : ∀ j, u (j + N) = u j) :
    (∑ j ∈ Finset.range N, u (j + k)) = ∑ j ∈ Finset.range N, u j := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        (∑ j ∈ Finset.range N, u (j + (k + 1))) =
            ∑ j ∈ Finset.range N, (fun i => u (i + k)) (j + 1) := by
              congr 1
              ext j
              congr 1
              omega
        _ = ∑ j ∈ Finset.range N, u (j + k) := by
              exact sum_range_rotate (fun i => u (i + k)) N
                (by simpa only [Nat.add_zero, Nat.add_comm] using hu k)
        _ = ∑ j ∈ Finset.range N, u j := ih

private theorem qParam_twentyFour_add (z : ℂ) :
    Function.Periodic.qParam 24 (z + 24) = Function.Periodic.qParam 24 z := by
  unfold Function.Periodic.qParam
  have harg : 2 * Real.pi * Complex.I * (z + 24) / 24 =
      2 * Real.pi * Complex.I * z / 24 + 2 * Real.pi * Complex.I := by ring
  norm_num at harg ⊢
  rw [harg, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- The period-24 cusp representative makes an inverse-eta weak form
periodic after translation by 24. -/
theorem EtaInverseWeaklyHolomorphicForm.translation_twentyFour
    {k : ℕ} (f : EtaInverseWeaklyHolomorphicForm k)
    (τ : UpperHalfPlane) :
    f (cuspTranslateTwentyFour τ) = f τ := by
  obtain ⟨G, _, hEq⟩ := f.has_meromorphic_cusp
  rw [← hEq (cuspTranslateTwentyFour τ), ← hEq τ]
  rw [cuspTranslateTwentyFour_coe]
  exact congrArg G (qParam_twentyFour_add τ)

/-- Advancing the affine root index by its modulus translates the
upper-half-plane argument by 24. -/
theorem cuspAffinePoint_add_index (N j : ℕ) (hN : 0 < N)
    (τ : UpperHalfPlane) :
    cuspAffinePoint N (j + N) hN τ =
      cuspTranslateTwentyFour (cuspAffinePoint N j hN τ) := by
  apply UpperHalfPlane.ext
  rw [cuspAffinePoint_coe, cuspTranslateTwentyFour_coe, cuspAffinePoint_coe]
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  push_cast
  field_simp [hNC]
  ring

/-- When `N = 24k + 1`, shifting the affine root index by `k` after
translation by one is the same as translating its value by one. -/
theorem cuspAffinePoint_translate_index (N k j : ℕ) (hN : 0 < N)
    (hcong : N = 24 * k + 1) (τ : UpperHalfPlane) :
    cuspAffinePoint N (j + k) hN (upperUnipotent 1 • τ) =
      upperUnipotent 1 • cuspAffinePoint N j hN τ := by
  apply UpperHalfPlane.ext
  rw [cuspAffinePoint_coe]
  rw [upperUnipotent_apply, upperUnipotent_apply]
  rw [cuspAffinePoint_coe]
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hc : (N : ℂ) = 24 * (k : ℂ) + 1 := by exact_mod_cast hcong
  push_cast
  field_simp [hNC]
  rw [hc]
  ring

/-- The affine root average of an inverse-eta weak form has the eta
translation phase whenever its index is one modulo 24. This is the
congruence satisfied by square indices prime to six. -/
theorem EtaInverseWeaklyHolomorphicForm.affineAverage_translation
    {a : ℕ} (f : EtaInverseWeaklyHolomorphicForm a)
    (N k : ℕ) (hN : 0 < N) (hcong : N = 24 * k + 1)
    (τ : UpperHalfPlane) :
    (∑ j ∈ Finset.range N,
      f (cuspAffinePoint N j hN (upperUnipotent 1 • τ))) =
      (Complex.exp (Real.pi * Complex.I / 12))⁻¹ *
        ∑ j ∈ Finset.range N, f (cuspAffinePoint N j hN τ) := by
  let u : ℕ → ℂ := fun j =>
    f (cuspAffinePoint N j hN (upperUnipotent 1 • τ))
  have hu (j : ℕ) : u (j + N) = u j := by
    change f (cuspAffinePoint N (j + N) hN (upperUnipotent 1 • τ)) =
      f (cuspAffinePoint N j hN (upperUnipotent 1 • τ))
    rw [cuspAffinePoint_add_index, f.translation_twentyFour]
  calc
    (∑ j ∈ Finset.range N,
        f (cuspAffinePoint N j hN (upperUnipotent 1 • τ))) =
      ∑ j ∈ Finset.range N, u (j + k) := by
        change (∑ j ∈ Finset.range N, u j) = _
        exact (sum_range_shift u N k hu).symm
    _ = ∑ j ∈ Finset.range N,
          (Complex.exp (Real.pi * Complex.I / 12))⁻¹ *
            f (cuspAffinePoint N j hN τ) := by
        apply Finset.sum_congr rfl
        intro j _
        change f (cuspAffinePoint N (j + k) hN (upperUnipotent 1 • τ)) = _
        rw [cuspAffinePoint_translate_index N k j hN hcong, f.translation]
    _ = (Complex.exp (Real.pi * Complex.I / 12))⁻¹ *
          ∑ j ∈ Finset.range N, f (cuspAffinePoint N j hN τ) := by
        rw [Finset.mul_sum]

private theorem qParam_twentyFour_add_nat (z : ℂ) (k : ℕ) :
    Function.Periodic.qParam 24 (z + 24 * k) =
      Function.Periodic.qParam 24 z := by
  induction k with
  | zero => simp
  | succ k ih =>
      have he : z + 24 * (↑(k + 1) : ℂ) = (z + 24 * k) + 24 := by
        push_cast
        ring
      calc
        Function.Periodic.qParam 24 (z + 24 * (↑(k + 1) : ℂ)) =
            Function.Periodic.qParam 24 ((z + 24 * k) + 24) := congrArg _ he
        _ = Function.Periodic.qParam 24 (z + 24 * k) :=
          qParam_twentyFour_add _
        _ = Function.Periodic.qParam 24 z := ih

/-- Dilation by an index one modulo 24 retains the inverse-eta
translation phase. The period-24 cusp germ removes the full multiples of
24, leaving one translation of the original weak form. -/
theorem EtaInverseWeaklyHolomorphicForm.dilation_translation
    {a : ℕ} (f : EtaInverseWeaklyHolomorphicForm a)
    (N k : ℕ) (hN : 0 < N) (hcong : N = 24 * k + 1)
    (τ : UpperHalfPlane) :
    f (natDilation N hN (upperUnipotent 1 • τ)) =
      (Complex.exp (Real.pi * Complex.I / 12))⁻¹ *
        f (natDilation N hN τ) := by
  have hpoint :
      f (natDilation N hN (upperUnipotent 1 • τ)) =
        f (upperUnipotent 1 • natDilation N hN τ) := by
    obtain ⟨G, _, hEq⟩ := f.has_meromorphic_cusp
    rw [← hEq (natDilation N hN (upperUnipotent 1 • τ)),
      ← hEq (upperUnipotent 1 • natDilation N hN τ)]
    congr 1
    rw [natDilation_coe]
    rw [upperUnipotent_apply, upperUnipotent_apply]
    rw [natDilation_coe]
    have hc : (N : ℂ) = 24 * (k : ℂ) + 1 := by exact_mod_cast hcong
    have he : (N : ℂ) * ((τ : ℂ) + 1) =
        ((N : ℂ) * (τ : ℂ) + 1) + 24 * k := by
      rw [hc]
      ring
    have hcalc :
        Function.Periodic.qParam 24 ((N : ℂ) * ((τ : ℂ) + 1)) =
          Function.Periodic.qParam 24 ((N : ℂ) * (τ : ℂ) + 1) := by
      calc
        Function.Periodic.qParam 24 ((N : ℂ) * ((τ : ℂ) + 1)) =
            Function.Periodic.qParam 24
              (((N : ℂ) * (τ : ℂ) + 1) + 24 * k) := congrArg _ he
        _ = Function.Periodic.qParam 24 ((N : ℂ) * (τ : ℂ) + 1) :=
          qParam_twentyFour_add_nat _ _
    simpa using hcalc
  rw [hpoint, f.translation]

/-- The square of a positive integer prime to six is one modulo 24.
This is the congruence needed for the eta translation phase of a
square-index Hecke expression. -/
theorem squareIndex_mod_twentyFour_of_coprime_six (n : ℕ)
    (hcop : n.Coprime 6) : (n * n) % 24 = 1 := by
  have hmod : (n % 6).Coprime 6 := by
    have h := hcop.symm
    change Nat.gcd 6 n = 1 at h
    rw [Nat.gcd_rec] at h
    exact h
  have hres6 : n % 6 = 1 ∨ n % 6 = 5 := by
    have hlt : n % 6 < 6 := Nat.mod_lt _ (by decide)
    interval_cases h : n % 6 <;> norm_num [h] at hmod <;> norm_num [h]
  have hres24 : (n % 24) % 6 = 1 ∨ (n % 24) % 6 = 5 := by
    omega
  have hsq : (n % 24 * (n % 24)) % 24 = 1 := by
    have hlt : n % 24 < 24 := Nat.mod_lt _ (by decide)
    interval_cases h : n % 24 <;> norm_num [h] at hres24 <;> norm_num [h]
  calc
    (n * n) % 24 = (n % 24 * (n % 24)) % 24 := Nat.mul_mod n n 24
    _ = 1 := hsq

/-- Every analytic square-index summand combination of an actual
inverse-eta weak form transforms by the inverse-eta phase under the
translation generator when its index is prime to six. The finite weights
and scalar normalizations remain arbitrary [rolenManuscript, §3]. -/
theorem EtaInverseWeaklyHolomorphicForm.squareIndexAnalyticSum_translation
    {a : ℕ} (f : EtaInverseWeaklyHolomorphicForm a)
    (n : ℕ) (hn : 0 < n) (hcop : n.Coprime 6)
    (w : ℕ → ℂ) (A B C : ℂ) (τ : UpperHalfPlane) :
    squareIndexAnalyticSum f n hn w A B C (upperUnipotent 1 • τ) =
      (Complex.exp (Real.pi * Complex.I / 12))⁻¹ *
        squareIndexAnalyticSum f n hn w A B C τ := by
  have hmod := squareIndex_mod_twentyFour_of_coprime_six n hcop
  have hcong : n * n = 24 * ((n * n) / 24) + 1 := by omega
  let hnn : 0 < n * n := Nat.mul_pos hn hn
  rw [squareIndexAnalyticSum_eq f n hn w A B C (upperUnipotent 1 • τ),
    squareIndexAnalyticSum_eq f n hn w A B C τ]
  rw [f.affineAverage_translation (n * n) ((n * n) / 24) hnn hcong,
    f.weightedFractionSum_translation w n hn,
    f.dilation_translation (n * n) ((n * n) / 24) hnn hcong]
  ring

end SptClassification
