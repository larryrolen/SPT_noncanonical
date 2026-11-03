/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.WeightTwoConstantTermHeckeAnalytic

/-!
# Holomorphy of analytic square-index Hecke summands

The three affine shapes in a square-index Hecke expression preserve the
upper half-plane. Composition with a holomorphic upper-half-plane function,
finite sums, and scalar multiples are holomorphic. This proves the analytic
part needed before the separate modularity and Maass-shadow arguments
[rolenManuscript, §3].
-/

public section

namespace SptClassification

open UpperHalfPlane
open scoped Manifold

private theorem mdiff_realAffine {f : UpperHalfPlane → ℂ} (hf : MDiff f)
    (a b : ℝ) (ha : 0 < a) :
    MDiff (fun τ : UpperHalfPlane =>
      f (ofComplex ((a : ℂ) * (τ : ℂ) + b))) := by
  apply UpperHalfPlane.mdifferentiable_iff.mpr
  have hf' : DifferentiableOn ℂ (f ∘ ofComplex) upperHalfPlaneSet :=
    UpperHalfPlane.mdifferentiable_iff.mp hf
  intro z hz
  have hz' : 0 < ((a : ℂ) * z + b).im := by
    simpa using mul_pos ha hz
  have hfd : DifferentiableAt ℂ (f ∘ ofComplex) ((a : ℂ) * z + b) :=
    (hf' _ hz').differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds hz')
  have hlin : DifferentiableAt ℂ (fun w : ℂ => (a : ℂ) * w + b) z := by
    fun_prop
  have hcomp : DifferentiableAt ℂ
      (fun w : ℂ => f (ofComplex ((a : ℂ) * w + b))) z := by
    change DifferentiableAt ℂ
      ((f ∘ ofComplex) ∘ (fun w : ℂ => (a : ℂ) * w + b)) z
    exact hfd.comp z hlin
  have heq :
      (fun w : ℂ => f (ofComplex ((a : ℂ) *
        ((ofComplex w : UpperHalfPlane) : ℂ) + b))) =ᶠ[nhds z]
      (fun w : ℂ => f (ofComplex ((a : ℂ) * w + b))) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hz] with w hw
    rw [ofComplex_apply_of_im_pos hw]
  exact (hcomp.congr_of_eventuallyEq heq).differentiableWithinAt

private theorem mdiff_affineHeckeTerm {f : UpperHalfPlane → ℂ} (hf : MDiff f)
    (n j : ℕ) (hn : 0 < n) :
    MDiff (fun τ : UpperHalfPlane => f (cuspAffinePoint n j hn τ)) := by
  let a : ℝ := (n : ℝ)⁻¹
  let b : ℝ := 24 * j / n
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ha : 0 < a := inv_pos.mpr hnR
  have h := mdiff_realAffine hf a b ha
  convert h using 1
  funext τ
  congr 1
  have hz : 0 < ((a : ℂ) * (τ : ℂ) + b).im := by
    simpa using mul_pos ha τ.im_pos
  apply UpperHalfPlane.ext
  rw [ofComplex_apply_of_im_pos hz]
  rw [cuspAffinePoint_coe]
  dsimp [a, b]
  push_cast
  field_simp

private theorem mdiff_fractionHeckeTerm {f : UpperHalfPlane → ℂ} (hf : MDiff f)
    (n j : ℕ) (hn : 0 < n) :
    MDiff (fun τ : UpperHalfPlane => f (cuspFractionTranslate n j hn τ)) := by
  let b : ℝ := 24 * j / n
  have h := mdiff_realAffine hf 1 b (by norm_num)
  convert h using 1
  funext τ
  congr 1
  have hz : 0 < (((1 : ℝ) : ℂ) * (τ : ℂ) + b).im := by
    simpa using τ.im_pos
  apply UpperHalfPlane.ext
  rw [ofComplex_apply_of_im_pos hz]
  rw [cuspFractionTranslate_coe]
  dsimp [b]
  push_cast
  ring

private theorem mdiff_dilationHeckeTerm {f : UpperHalfPlane → ℂ} (hf : MDiff f)
    (n : ℕ) (hn : 0 < n) :
    MDiff (fun τ : UpperHalfPlane => f (natDilation n hn τ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h := mdiff_realAffine hf n 0 hnR
  convert h using 1
  funext τ
  congr 1
  have hz : 0 < (((n : ℝ) : ℂ) * (τ : ℂ) + (0 : ℝ)).im := by
    simpa using mul_pos hnR τ.im_pos
  apply UpperHalfPlane.ext
  rw [ofComplex_apply_of_im_pos hz]
  rw [natDilation_coe]
  simp

/-- An analytic square-index Hecke summand combination is holomorphic on
the upper half-plane. The character weights and three scalar normalizations
are arbitrary; modularity is a separate assertion [rolenManuscript, §3]. -/
theorem squareIndexAnalyticSum_holomorphic {f : UpperHalfPlane → ℂ}
    (hf : MDiff f) (n : ℕ) (hn : 0 < n) (w : ℕ → ℂ) (A B C : ℂ) :
    MDiff (squareIndexAnalyticSum f n hn w A B C) := by
  have hnn : 0 < n * n := Nat.mul_pos hn hn
  have hAffine : MDiff (fun τ : UpperHalfPlane =>
      ∑ j ∈ Finset.range (n * n), f (cuspAffinePoint (n * n) j hnn τ)) := by
    induction Finset.range (n * n) using Finset.induction_on with
    | empty => simpa using (mdifferentiable_const : MDiff (fun _ : UpperHalfPlane => (0 : ℂ)))
    | @insert j s hjs ih =>
        convert (mdiff_affineHeckeTerm hf (n * n) j hnn).add ih using 1
        funext τ
        simp only [Finset.sum_insert hjs, Pi.add_apply]
  have hFraction : MDiff (fun τ : UpperHalfPlane =>
      ∑ j ∈ Finset.range n, w j * f (cuspFractionTranslate n j hn τ)) := by
    induction Finset.range n using Finset.induction_on with
    | empty => simpa using (mdifferentiable_const : MDiff (fun _ : UpperHalfPlane => (0 : ℂ)))
    | @insert j s hjs ih =>
        have hj : MDiff (fun τ : UpperHalfPlane =>
            w j * f (cuspFractionTranslate n j hn τ)) :=
          mdifferentiable_const.mul (mdiff_fractionHeckeTerm hf n j hn)
        convert hj.add ih using 1
        funext τ
        simp only [Finset.sum_insert hjs, Pi.add_apply]
  have hA : MDiff (fun τ : UpperHalfPlane =>
      A * ∑ j ∈ Finset.range (n * n), f (cuspAffinePoint (n * n) j hnn τ)) :=
    mdifferentiable_const.mul hAffine
  have hB : MDiff (fun τ : UpperHalfPlane =>
      B * ∑ j ∈ Finset.range n, w j * f (cuspFractionTranslate n j hn τ)) :=
    mdifferentiable_const.mul hFraction
  have hC : MDiff (fun τ : UpperHalfPlane =>
      C * f (natDilation (n * n) hnn τ)) :=
    mdifferentiable_const.mul (mdiff_dilationHeckeTerm hf (n * n) hnn)
  change MDiff (fun τ : UpperHalfPlane => squareIndexAnalyticSum f n hn w A B C τ)
  convert (hA.add hB).add hC using 1
  funext τ
  simpa only [Pi.add_apply] using squareIndexAnalyticSum_eq f n hn w A B C τ

/-- The square-index analytic combination of an actual inverse-eta weak
form is holomorphic [rolenManuscript, §3]. -/
theorem EtaInverseWeaklyHolomorphicForm.squareIndexAnalyticSum_holomorphic
    {k : ℕ} (f : EtaInverseWeaklyHolomorphicForm k)
    (n : ℕ) (hn : 0 < n) (w : ℕ → ℂ) (A B C : ℂ) :
    MDiff (squareIndexAnalyticSum f n hn w A B C) :=
  SptClassification.squareIndexAnalyticSum_holomorphic f.holomorphic n hn w A B C

end SptClassification
