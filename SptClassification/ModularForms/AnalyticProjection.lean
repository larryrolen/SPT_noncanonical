/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.ConditionalPropagation

/-!
# The analytic progression projection

The finite average is the `B = 0` normalization of
[garthwaiteJameson2021, §2, PDF p. 4]. It is a function on the actual upper
half-plane, with the original form evaluated at `(τ + j) / M`.
-/

public section

namespace SptClassification

open UpperHalfPlane

/-- The point occurring in the finite progression average. -/
noncomputable def progressionPoint (M : ℕ) (hM : 0 < M) (j : ℕ)
    (τ : UpperHalfPlane) : UpperHalfPlane :=
  ⟨((τ : ℂ) + j) / M, by
    simpa using div_pos τ.im_pos (show (0 : ℝ) < M by exact_mod_cast hM)⟩

@[simp] theorem progressionPoint_coe (M : ℕ) (hM : 0 < M) (j : ℕ)
    (τ : UpperHalfPlane) :
    (progressionPoint M hM j τ : ℂ) = ((τ : ℂ) + j) / M := (rfl)

/-- The phase in the `B = 0` progression average. -/
noncomputable def progressionPhase (M : ℕ) (u : ℤ) (j : ℕ) : ℂ :=
  Complex.exp (-2 * Real.pi * Complex.I * j * u / M)

/-- The analytic progression projection, before any modularity theorem. -/
noncomputable def analyticProgression (M : ℕ) (hM : 0 < M) (u : ℤ)
    (F : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) : ℂ :=
  (M : ℂ)⁻¹ * ∑ j ∈ Finset.range M,
    progressionPhase M u j * F (progressionPoint M hM j τ)

/-- Scalar division in the manuscript is compatible with the actual finite
projection; it is not an additional modular-form hypothesis. -/
theorem analyticProgression_const_mul (M : ℕ) (hM : 0 < M) (u : ℤ)
    (F : UpperHalfPlane → ℂ) (c : ℂ) :
    analyticProgression M hM u (fun τ => c * F τ) =
      fun τ => c * analyticProgression M hM u F τ := by
  funext τ
  simp only [analyticProgression]
  calc
    _ = (M : ℂ)⁻¹ * ∑ j ∈ Finset.range M,
        c * (progressionPhase M u j * F (progressionPoint M hM j τ)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- The finite projection is additive. -/
theorem analyticProgression_add (M : ℕ) (hM : 0 < M) (u : ℤ)
    (F G : UpperHalfPlane → ℂ) :
    analyticProgression M hM u (fun τ => F τ + G τ) =
      fun τ => analyticProgression M hM u F τ + analyticProgression M hM u G τ := by
  funext τ
  simp [analyticProgression, mul_add, Finset.sum_add_distrib]

end SptClassification
