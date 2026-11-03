/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.WeightTwoConstantTermEta

/-!
# Cusp germs under the dilation in a half-integral Hecke operator

The inverse-eta Hecke operator contains a term evaluated at a positive
integer multiple of the upper-half-plane variable. Meromorphy of its cusp
representative is preserved by this dilation. This handles the dilation term;
the translated averaging term and its modular transformation remain separate
[rolenManuscript, §3].
-/

public section

namespace SptClassification

open UpperHalfPlane

/-- Dilation by a positive natural number preserves the upper half-plane. -/
def natDilation (n : ℕ) (hn : 0 < n) (τ : UpperHalfPlane) : UpperHalfPlane :=
  ⟨(n : ℂ) * (τ : ℂ), by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    simpa using mul_pos hn' τ.im_pos⟩

/-- The complex coordinate of a positive dilation. -/
theorem natDilation_coe (n : ℕ) (hn : 0 < n) (τ : UpperHalfPlane) :
    (natDilation n hn τ : ℂ) = (n : ℂ) * (τ : ℂ) := (rfl)

/-- Dilation raises the period-24 nome to the same power. -/
theorem qParam_twentyFour_nat_mul (n : ℕ) (z : ℂ) :
    Function.Periodic.qParam 24 ((n : ℂ) * z) =
      Function.Periodic.qParam 24 z ^ n := by
  unfold Function.Periodic.qParam
  rw [← Complex.exp_nat_mul]
  congr 1
  norm_num
  ring

/-- The period-24 cusp germ of a holomorphic function remains meromorphic
after positive integer dilation [rolenManuscript, §3]. -/
theorem meromorphicCusp24_natDilation {f : UpperHalfPlane → ℂ} {G : ℂ → ℂ}
    (hG : MeromorphicAt G 0)
    (hEq : ∀ τ : UpperHalfPlane, G (Function.Periodic.qParam 24 τ) = f τ)
    (n : ℕ) (hn : 0 < n) :
    ∃ H : ℂ → ℂ, MeromorphicAt H 0 ∧
      ∀ τ : UpperHalfPlane,
        H (Function.Periodic.qParam 24 τ) = f (natDilation n hn τ) := by
  let H : ℂ → ℂ := fun t => G (t ^ n)
  have hpow : AnalyticAt ℂ (fun t : ℂ => t ^ n) 0 := analyticAt_id.pow n
  have hH : MeromorphicAt H 0 := by
    exact MeromorphicAt.comp_analyticAt (𝕜 := ℂ) (𝕜' := ℂ)
      (f := G) (g := fun t : ℂ => t ^ n) (x := (0 : ℂ))
      (by simpa [Nat.ne_of_gt hn] using hG) hpow
  refine ⟨H, hH, ?_⟩
  intro τ
  change G (Function.Periodic.qParam 24 τ ^ n) = f (natDilation n hn τ)
  rw [← qParam_twentyFour_nat_mul]
  exact hEq (natDilation n hn τ)

/-- The cusp part of a dilated actual inverse-eta weak form. This lemma
provides the meromorphy needed for the dilation summand in the Hecke pairing;
it makes no modularity assertion about that summand alone. -/
theorem EtaInverseWeaklyHolomorphicForm.has_meromorphic_cusp_natDilation
    {k : ℕ} (f : EtaInverseWeaklyHolomorphicForm k)
    (n : ℕ) (hn : 0 < n) :
    ∃ H : ℂ → ℂ, MeromorphicAt H 0 ∧
      ∀ τ : UpperHalfPlane,
        H (Function.Periodic.qParam 24 τ) = f (natDilation n hn τ) := by
  obtain ⟨G, hG, hEq⟩ := f.has_meromorphic_cusp
  exact meromorphicCusp24_natDilation hG hEq n hn

/-- Averaging a cusp germ over rotations of its nome. The averaged germ is
the local analytic construction behind the coefficient-selection summand of
a square-index Hecke operator [rolenManuscript, §3]. -/
noncomputable def cuspRootAverage (G : ℂ → ℂ) (n : ℕ) : ℂ → ℂ :=
  fun t => ∑ j ∈ Finset.range n,
    G (Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) / n) * t)

/-- The `j`th root used in the translated cusp average of index `n`. -/
noncomputable def cuspRoot (n j : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) / n)

/-- The explicit root used by the cusp average. -/
theorem cuspRoot_eq (n j : ℕ) :
    cuspRoot n j = Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) / n) := (rfl)

private theorem cuspRoot_succ (n j : ℕ) :
    cuspRoot n (j + 1) = cuspRoot n j * cuspRoot n 1 := by
  unfold cuspRoot
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem cuspRoot_self (n : ℕ) (hn : 0 < n) : cuspRoot n n = 1 := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  unfold cuspRoot
  have harg : 2 * Real.pi * Complex.I * (n : ℂ) / n =
      2 * Real.pi * Complex.I := by
    field_simp
  rw [harg]
  exact Complex.exp_two_pi_mul_I

private theorem sum_range_rotate (u : ℕ → ℂ) (n : ℕ) (h : u n = u 0) :
    ∑ j ∈ Finset.range n, u (j + 1) = ∑ j ∈ Finset.range n, u j := by
  have hleft := Finset.sum_range_succ' u n
  have hright := Finset.sum_range_succ u n
  calc
    ∑ j ∈ Finset.range n, u (j + 1) =
        (∑ j ∈ Finset.range (n + 1), u j) - u 0 := by rw [hleft]; ring
    _ = ∑ j ∈ Finset.range n, u j := by rw [hright, h]; ring

/-- The finite root average is unchanged by one primitive rotation. This is
the exact cyclic symmetry needed to descend the translated Hecke cusp sum
from the period-`24n` nome to the period-24 nome. -/
theorem cuspRootAverage_rotate (G : ℂ → ℂ) (n : ℕ) (hn : 0 < n) (t : ℂ) :
    cuspRootAverage G n (cuspRoot n 1 * t) = cuspRootAverage G n t := by
  let u : ℕ → ℂ := fun j => G (cuspRoot n j * t)
  have hu : u n = u 0 := by
    change G (cuspRoot n n * t) = G (cuspRoot n 0 * t)
    rw [cuspRoot_self n hn]
    simp [cuspRoot]
  calc
    cuspRootAverage G n (cuspRoot n 1 * t) =
        ∑ j ∈ Finset.range n, u (j + 1) := by
      unfold cuspRootAverage
      apply Finset.sum_congr rfl
      intro j hj
      change G (cuspRoot n j * (cuspRoot n 1 * t)) =
        G (cuspRoot n (j + 1) * t)
      have hroot : cuspRoot n j * (cuspRoot n 1 * t) =
          cuspRoot n (j + 1) * t := by
        rw [cuspRoot_succ n j]
        ring
      exact congrArg G hroot
    _ = ∑ j ∈ Finset.range n, u j := sum_range_rotate u n hu
    _ = cuspRootAverage G n t := rfl

/-- Translation by 24 rotates the finer period-`24n` nome by one `n`th root. -/
theorem qParam_twentyFour_mul_add (n : ℕ) (hn : 0 < n) (z : ℂ) :
    Function.Periodic.qParam (24 * n) (z + 24) =
      cuspRoot n 1 * Function.Periodic.qParam (24 * n) z := by
  unfold Function.Periodic.qParam cuspRoot
  rw [← Complex.exp_add]
  congr 1
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  norm_num
  field_simp
  ring

/-- The translated finite cusp sum recovers period 24 from its period-`24n`
nome, by cyclic permutation of the roots. -/
theorem cuspRootAverage_qParam_periodic (G : ℂ → ℂ) (n : ℕ) (hn : 0 < n)
    (z : ℂ) :
    cuspRootAverage G n (Function.Periodic.qParam (24 * n) (z + 24)) =
      cuspRootAverage G n (Function.Periodic.qParam (24 * n) z) := by
  rw [qParam_twentyFour_mul_add n hn]
  exact cuspRootAverage_rotate G n hn _

/-- Each root-of-unity pullback is meromorphic at the infinity cusp. -/
theorem meromorphicAt_cuspRootTwist {G : ℂ → ℂ} (hG : MeromorphicAt G 0)
    (ζ : ℂ) : MeromorphicAt (fun t : ℂ => G (ζ * t)) 0 := by
  have hlin : AnalyticAt ℂ (fun t : ℂ => ζ * t) 0 := analyticAt_const.mul analyticAt_id
  exact MeromorphicAt.comp_analyticAt (𝕜 := ℂ) (𝕜' := ℂ)
    (f := G) (g := fun t : ℂ => ζ * t) (x := (0 : ℂ))
    (by simpa using hG) hlin

/-- A finite root average of a meromorphic cusp germ is meromorphic. -/
theorem meromorphicAt_cuspRootAverage {G : ℂ → ℂ}
    (hG : MeromorphicAt G 0) (n : ℕ) :
    MeromorphicAt (cuspRootAverage G n) 0 := by
  classical
  unfold cuspRootAverage
  induction Finset.range n using Finset.induction_on with
  | empty => simpa using (meromorphicAt_const : MeromorphicAt (fun _ : ℂ => (0 : ℂ)) 0)
  | @insert j s hjs ih =>
      simpa [Finset.sum_insert hjs] using
        (meromorphicAt_cuspRootTwist hG
          (Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) / n))).fun_add ih

/-- The fractional translation in a square-index Hecke operator becomes a
root-of-unity rotation in the finer cusp nome. The finer period is `24n`,
before coefficient selection restores period `24` [rolenManuscript, §3]. -/
theorem qParam_twentyFour_affine (n j : ℕ) (hn : 0 < n) (z : ℂ) :
    Function.Periodic.qParam 24 ((z + 24 * j) / n) =
      Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) / n) *
        Function.Periodic.qParam (24 * n) z := by
  unfold Function.Periodic.qParam
  rw [← Complex.exp_add]
  congr 1
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  norm_num
  field_simp
  ring

/-- The upper-half-plane point occurring in the translated Hecke average. -/
noncomputable def cuspAffinePoint (n j : ℕ) (hn : 0 < n)
    (τ : UpperHalfPlane) : UpperHalfPlane :=
  ⟨((τ : ℂ) + 24 * j) / n, by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    simpa using div_pos τ.im_pos hn'⟩

/-- The complex coordinate of the affine Hecke point. -/
theorem cuspAffinePoint_coe (n j : ℕ) (hn : 0 < n) (τ : UpperHalfPlane) :
    (cuspAffinePoint n j hn τ : ℂ) = ((τ : ℂ) + 24 * j) / n := (rfl)

/-- The meromorphic root average is exactly the finite sum of actual
upper-half-plane values over the translated Hecke points, in the finer nome.
No modular transformation law is used here. -/
theorem cuspRootAverage_qParam {f : UpperHalfPlane → ℂ} {G : ℂ → ℂ}
    (hEq : ∀ τ : UpperHalfPlane, G (Function.Periodic.qParam 24 τ) = f τ)
    (n : ℕ) (hn : 0 < n) (τ : UpperHalfPlane) :
    cuspRootAverage G n (Function.Periodic.qParam (24 * n) τ) =
      ∑ j ∈ Finset.range n, f (cuspAffinePoint n j hn τ) := by
  unfold cuspRootAverage
  apply Finset.sum_congr rfl
  intro j hj
  change G (Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) / n) *
      Function.Periodic.qParam (24 * n) τ) = f (cuspAffinePoint n j hn τ)
  rw [← qParam_twentyFour_affine n j hn]
  exact hEq (cuspAffinePoint n j hn τ)

/-- Translation by one period of the original period-24 cusp coordinate. -/
def cuspTranslateTwentyFour (τ : UpperHalfPlane) : UpperHalfPlane :=
  ⟨(τ : ℂ) + 24, by simpa using τ.im_pos⟩

/-- The complex coordinate of translation through one cusp period. -/
theorem cuspTranslateTwentyFour_coe (τ : UpperHalfPlane) :
    (cuspTranslateTwentyFour τ : ℂ) = (τ : ℂ) + 24 := (rfl)

/-- The actual finite translated sum is period 24, even though its direct
meromorphic representative uses the finer period-`24n` cusp coordinate. -/
theorem cuspAffineAverage_periodic {f : UpperHalfPlane → ℂ} {G : ℂ → ℂ}
    (hEq : ∀ τ : UpperHalfPlane, G (Function.Periodic.qParam 24 τ) = f τ)
    (n : ℕ) (hn : 0 < n) (τ : UpperHalfPlane) :
    (∑ j ∈ Finset.range n,
      f (cuspAffinePoint n j hn (cuspTranslateTwentyFour τ))) =
      ∑ j ∈ Finset.range n, f (cuspAffinePoint n j hn τ) := by
  rw [← cuspRootAverage_qParam hEq n hn (cuspTranslateTwentyFour τ),
    ← cuspRootAverage_qParam hEq n hn τ]
  exact cuspRootAverage_qParam_periodic G n hn τ

/-- The translated Hecke average has a genuine meromorphic representative in
the finer period-`24n` cusp coordinate. This applies to any actual
period-24 meromorphic weak form, without identifying its Fourier coefficients
or asserting the modularity of the average. -/
theorem meromorphicCuspRootAverage {f : UpperHalfPlane → ℂ} {G : ℂ → ℂ}
    (hG : MeromorphicAt G 0)
    (hEq : ∀ τ : UpperHalfPlane, G (Function.Periodic.qParam 24 τ) = f τ)
    (n : ℕ) (hn : 0 < n) :
    ∃ H : ℂ → ℂ, MeromorphicAt H 0 ∧
      ∀ τ : UpperHalfPlane,
        H (Function.Periodic.qParam (24 * n) τ) =
          ∑ j ∈ Finset.range n, f (cuspAffinePoint n j hn τ) := by
  exact ⟨cuspRootAverage G n, meromorphicAt_cuspRootAverage hG n,
    cuspRootAverage_qParam hEq n hn⟩

/-- The translated average of an actual inverse-eta weak form has the
meromorphic period-`24n` cusp germ supplied by its original cusp germ. -/
theorem EtaInverseWeaklyHolomorphicForm.has_meromorphic_cuspRootAverage
    {k : ℕ} (f : EtaInverseWeaklyHolomorphicForm k)
    (n : ℕ) (hn : 0 < n) :
    ∃ H : ℂ → ℂ, MeromorphicAt H 0 ∧
      ∀ τ : UpperHalfPlane,
        H (Function.Periodic.qParam (24 * n) τ) =
          ∑ j ∈ Finset.range n, f (cuspAffinePoint n j hn τ) := by
  obtain ⟨G, hG, hEq⟩ := f.has_meromorphic_cusp
  exact meromorphicCuspRootAverage hG hEq n hn

end SptClassification
