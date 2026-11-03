/- Assembled by AxiomProver. -/

module

public import SptClassification.Theta.PrincipalWeilDivisors
public import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Interior clearing of the CM poles

The squared product of the actual oriented CM polynomials clears the double
poles of the Shimura lift in [rolenManuscript, Section 4]. We construct a
local analytic extension: the totalized value of a meromorphic function at its
pole need not equal the value of that extension.
-/

public section

namespace SptClassification

open Filter
open scoped Topology

/-- A zero of an analytic function has meromorphic order at least one. -/
theorem one_le_meromorphicOrderAt_of_zero {g : ℂ → ℂ} {z : ℂ}
    (hg : AnalyticAt ℂ g z) (hz : g z = 0) :
    (1 : WithTop ℤ) ≤ meromorphicOrderAt g z := by
  rw [hg.meromorphicOrderAt_eq]
  have hn := hg.analyticOrderAt_ne_zero.mpr hz
  cases ho : analyticOrderAt g z with
  | top => simp
  | coe n =>
    have hn' : n ≠ 0 := by simpa [ho] using hn
    simp only [ENat.map_natCast]
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn')

/-- Squaring an analytic zero clears a meromorphic pole of order at most two. -/
theorem analytic_extension_of_double_pole {f g : ℂ → ℂ} {z : ℂ}
    (hf : MeromorphicAt f z) (hg : AnalyticAt ℂ g z) (hz : g z = 0)
    (horder : (-2 : WithTop ℤ) ≤ meromorphicOrderAt f z) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F z ∧
      (fun w => g w ^ 2 * f w) =ᶠ[𝓝[≠] z] F := by
  apply ((hg.pow 2).meromorphicAt.mul hf).meromorphicOrderAt_nonneg_iff.mp
  simp only [pow_two]
  rw [meromorphicOrderAt_mul (hg.meromorphicAt.mul hg.meromorphicAt) hf,
    meromorphicOrderAt_mul hg.meromorphicAt hg.meromorphicAt]
  have hgorder := one_le_meromorphicOrderAt_of_zero hg hz
  have h := add_le_add (add_le_add hgorder hgorder) horder
  norm_num at h
  exact h

/-- The actual eta coordinate is analytic throughout the upper half-plane. -/
theorem analyticAt_levelSixEtaQuotient (z : UpperHalfPlane) :
    AnalyticAt ℂ levelSixEtaQuotient (z : ℂ) := by
  apply DifferentiableOn.analyticAt (s := {w : ℂ | 0 < w.im})
  · intro w hw
    exact (differentiableAt_levelSixEtaQuotient ⟨w, hw⟩).differentiableWithinAt
  · exact (isOpen_lt continuous_const Complex.continuous_im).mem_nhds z.im_pos

/-- The actual paired CM factor in the analytic coordinate. -/
noncomputable def cmPoleFactor (D : ℤ) [Fact (D < 0)] (z : ℂ) : ℂ :=
  (cmClassPolynomialA D * cmClassPolynomialB D).eval (levelSixEtaQuotient z)

/-- Evaluation formula for the paired CM pole factor. -/
theorem cmPoleFactor_eq (D : ℤ) [Fact (D < 0)] (z : ℂ) :
    cmPoleFactor D z =
      (cmClassPolynomialA D * cmClassPolynomialB D).eval (levelSixEtaQuotient z) := (rfl)

/-- Polynomial evaluation preserves the interior holomorphy of the coordinate. -/
theorem analyticAt_cmPoleFactor (D : ℤ) [Fact (D < 0)] (z : UpperHalfPlane) :
    AnalyticAt ℂ (cmPoleFactor D) (z : ℂ) := by
  apply DifferentiableOn.analyticAt (s := {w : ℂ | 0 < w.im})
  · intro w hw
    exact ((cmClassPolynomialA D * cmClassPolynomialB D).differentiableAt.comp w
      (differentiableAt_levelSixEtaQuotient ⟨w, hw⟩)).differentiableWithinAt
  · exact (isOpen_lt continuous_const Complex.continuous_im).mem_nhds z.im_pos

/-- The principal Weil divisor support supplies the zero needed for local
double-pole clearing. The lift and its pole-order bound are separate inputs. -/
theorem cmPoleFactor_clears_principalWeil_pole {d : ℕ}
    [Fact (-(d : ℤ) < 0)] (hsq : Squarefree d) (hd : d % 24 = 23)
    (x : Theta.DualCoordinates) (n : ℤ) (hn : n < 0)
    (hnorm : Theta.quadratic x.toSpace = (n : ℚ) / 24)
    (hcoeff : Theta.principalWeilCoefficient d n x.discriminantClass ≠ 0)
    (z : UpperHalfPlane)
    (hz : (6 * (x.c : ℂ)) * (z : ℂ) ^ 2 + (x.r : ℂ) * z + x.a = 0)
    (f : ℂ → ℂ) (hf : MeromorphicAt f (z : ℂ))
    (horder : (-2 : WithTop ℤ) ≤ meromorphicOrderAt f (z : ℂ)) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F (z : ℂ) ∧
      (fun w => cmPoleFactor (-(d : ℤ)) w ^ 2 * f w) =ᶠ[𝓝[≠] (z : ℂ)] F := by
  apply analytic_extension_of_double_pole hf (analyticAt_cmPoleFactor _ z) _ horder
  exact Theta.principalWeil_negative_divisor_support hsq hd x n hn hnorm hcoeff z hz

/-- Canonical removal of the apparent singularities after multiplying by the
squared CM factor. No value at a pole is prescribed by totalized arithmetic. -/
noncomputable def cmPoleClearedFunction (D : ℤ) [Fact (D < 0)]
    (f : ℂ → ℂ) : ℂ → ℂ :=
  toMeromorphicNFOn (fun w => cmPoleFactor D w ^ 2 * f w) {w | 0 < w.im}

/-- Clearing supported double poles produces one analytic function on the
whole interior, with the expected germ at every point. Cusp regularity and
integral descent are separate assertions. -/
theorem cmPoleClearedFunction_analytic (D : ℤ) [Fact (D < 0)] (f : ℂ → ℂ)
    (hf : MeromorphicOn f {w | 0 < w.im})
    (horder : ∀ z : UpperHalfPlane,
      (-2 : WithTop ℤ) ≤ meromorphicOrderAt f (z : ℂ))
    (hsupport : ∀ z : UpperHalfPlane,
      meromorphicOrderAt f (z : ℂ) < 0 → cmPoleFactor D z = 0) :
    AnalyticOnNhd ℂ (cmPoleClearedFunction D f) {w | 0 < w.im} ∧
      ∀ z : UpperHalfPlane,
        (fun w => cmPoleFactor D w ^ 2 * f w) =ᶠ[𝓝[≠] (z : ℂ)]
          cmPoleClearedFunction D f := by
  have hm : MeromorphicOn (fun w => cmPoleFactor D w ^ 2 * f w)
      {w | 0 < w.im} := by
    intro w hw
    exact ((analyticAt_cmPoleFactor D ⟨w, hw⟩).pow 2).meromorphicAt.mul (hf w hw)
  constructor
  · intro w hw
    apply (meromorphicNFOn_toMeromorphicNFOn _ _ hw).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [meromorphicOrderAt_toMeromorphicNFOn hm hw]
    by_cases ho : 0 ≤ meromorphicOrderAt f w
    · change 0 ≤ meromorphicOrderAt (cmPoleFactor D ^ 2 * f) w
      rw [meromorphicOrderAt_mul
        ((analyticAt_cmPoleFactor D ⟨w, hw⟩).pow 2).meromorphicAt (hf w hw)]
      exact add_nonneg ((analyticAt_cmPoleFactor D ⟨w, hw⟩).pow 2).meromorphicOrderAt_nonneg ho
    · exact (hm w hw).meromorphicOrderAt_nonneg_iff.mpr
        (analytic_extension_of_double_pole (hf w hw) (analyticAt_cmPoleFactor D ⟨w, hw⟩)
          (hsupport ⟨w, hw⟩ (lt_of_not_ge ho)) (horder ⟨w, hw⟩))
  · intro z
    exact (hm.toMeromorphicNFOn_eq_self_on_nhdsNE z.im_pos).symm

/-- The negative-vector pole description of the lift specializes to analytic
clearing by the actual CM polynomials. The generic lifting theorem supplies
the three analytic hypotheses; the CM support is proved here. -/
theorem cmPoleClearedFunction_analytic_of_principalWeil_support {d : ℕ}
    [Fact (-(d : ℤ) < 0)] (hsq : Squarefree d) (hd : d % 24 = 23)
    (f : ℂ → ℂ) (hf : MeromorphicOn f {w | 0 < w.im})
    (horder : ∀ z : UpperHalfPlane,
      (-2 : WithTop ℤ) ≤ meromorphicOrderAt f (z : ℂ))
    (hpoles : ∀ z : UpperHalfPlane, meromorphicOrderAt f (z : ℂ) < 0 →
      ∃ (x : Theta.DualCoordinates) (n : ℤ), n < 0 ∧
        Theta.quadratic x.toSpace = (n : ℚ) / 24 ∧
        Theta.principalWeilCoefficient d n x.discriminantClass ≠ 0 ∧
        (6 * (x.c : ℂ)) * (z : ℂ) ^ 2 + (x.r : ℂ) * z + x.a = 0) :
    AnalyticOnNhd ℂ (cmPoleClearedFunction (-(d : ℤ)) f) {w | 0 < w.im} ∧
      ∀ z : UpperHalfPlane,
        (fun w => cmPoleFactor (-(d : ℤ)) w ^ 2 * f w) =ᶠ[𝓝[≠] (z : ℂ)]
          cmPoleClearedFunction (-(d : ℤ)) f := by
  apply cmPoleClearedFunction_analytic _ f hf horder
  intro z hz
  obtain ⟨x, n, hn, hnorm, hcoeff, hzero⟩ := hpoles z hz
  exact Theta.principalWeil_negative_divisor_support hsq hd x n hn hnorm hcoeff z hzero

end SptClassification
