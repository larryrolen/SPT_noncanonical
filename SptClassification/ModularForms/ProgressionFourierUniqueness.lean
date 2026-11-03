/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.ConditionalPropagation
public import SptClassification.ModularForms.FourierRowUniqueness

/-!
# Uniqueness of analytic progression coefficients

The Fourier coefficients stored in a `ModularProgressionForm` are constrained
by its convergent Laurent expansion. After clearing a common pole, a second
convergent row for the same function has the same rational coefficients.
The integral version identifies their faithful reductions modulo a prime.
-/

public section

namespace SptClassification

open UpperHalfPlane
open scoped Manifold

/-- A genuine convergent rational Laurent row for a modular progression form
agrees with the form's declared rational coefficients. The analytic hypotheses
refer only to its pole-cleared function; no coefficient comparison is assumed. -/
theorem ModularProgressionForm.coeff_eq_of_laurentRow {p : ℕ}
    (g : ModularProgressionForm p) (M : ℕ) (a : ℤ → ℚ)
    (hgBelow : ∀ r : ℤ, r < -(M : ℤ) → g.coeff r = 0)
    (haBelow : ∀ r : ℤ, r < -(M : ℤ) → a r = 0)
    (ha : ∀ τ : UpperHalfPlane,
      HasSum (fun r : ℤ => (a r : ℂ) *
        Function.Periodic.qParam 1 τ ^ r) (g.toFun τ))
    (r : ℤ) : g.coeff r = a r := by
  have hhol : MDiff (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam 1 τ ^ M * g.toFun τ) :=
    (mdifferentiable_qParam_one.pow M).mul g.holomorphic
  have hper₀ : Function.Periodic (g.toFun ∘ ofComplex) 1 :=
    laurentRow_periodic (fun n : ℤ => (g.coeff n : ℂ)) g.hasSum_qExpansion
  have hT : ∀ z : ℂ, 0 < z.im →
      g.toFun (ofComplex (z + 1)) = g.toFun (ofComplex z) := by
    intro z _
    exact hper₀ z
  have hper : Function.Periodic
      ((fun τ : UpperHalfPlane =>
        Function.Periodic.qParam 1 τ ^ M * g.toFun τ) ∘ ofComplex) 1 := by
    simpa only [Function.comp_apply, ofComplex_apply] using
      (poleClearing_periodic (f := fun z : ℂ => g.toFun (ofComplex z)) hT M)
  have hrow := laurentRow_unique M hhol hper
    (fun n : ℤ => (g.coeff n : ℂ)) (fun n : ℤ => (a n : ℂ))
    (by intro n hn; simp [hgBelow n hn])
    (by intro n hn; simp [haBelow n hn])
    g.hasSum_qExpansion ha
  exact_mod_cast congrFun hrow r

/-- If the second analytic Laurent row is integral, faithful reduction of the
progression form is simply the residue of that row. This comparison also
works when the prime divides a later progression modulus. -/
theorem ModularProgressionForm.coeffMod_eq_of_integral_laurentRow
    {p : ℕ} [Fact p.Prime]
    (g : ModularProgressionForm p) (M : ℕ) (a : ℤ → ℤ)
    (hgBelow : ∀ r : ℤ, r < -(M : ℤ) → g.coeff r = 0)
    (haBelow : ∀ r : ℤ, r < -(M : ℤ) → a r = 0)
    (ha : ∀ τ : UpperHalfPlane,
      HasSum (fun r : ℤ => (a r : ℂ) *
        Function.Periodic.qParam 1 τ ^ r) (g.toFun τ))
    (r : ℤ) : g.coeffMod r = (a r : ZMod p) := by
  have hcoeff : g.coeff r = (a r : ℚ) :=
    g.coeff_eq_of_laurentRow M (fun n => (a n : ℚ)) hgBelow
      (by intro n hn; simp [haBelow n hn])
      (by intro τ; simpa only [Rat.cast_intCast] using ha τ) r
  exact g.coeffMod_eq_intCast r (a r) hcoeff

end SptClassification
