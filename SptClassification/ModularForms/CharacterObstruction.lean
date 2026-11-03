/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.CMFiniteCuspBounds

/-! # The CM obstruction to a vanishing smallest-parts character class -/

public section

namespace SptClassification

/-- A squarefree discriminant satisfying the two numerical bounds obstructs
vanishing on its character class. This is the original manuscript statement,
proved from the principal lift and the finite cusp bounds.
[rolenManuscript, label prop:obstruction] -/
theorem character_obstruction (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (sign : ℤ) (hsign : sign = 1 ∨ sign = -1)
    (d : ℕ) [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) (hr : legendreSym p (-(d : ℤ)) = sign)
    (hsep : (d + 1) ^ 2 < 24 * p)
    (hclass : 8 * formClassNumber (-(d : ℤ)) < p + 1) :
    ¬∀ j : ℕ, legendreSym p (1 - 24 * (j : ℤ)) = sign → p ∣ spt j := by
  obtain ⟨F, hanalytic, htrans, hslash, hgerm, ⟨Y, hsum⟩⟩ :=
    principalCMShimuraLift_cleared d hmod hsq
  have hb (c : FiniteLevelSixCusp) :=
    principalCMShimuraLift_finite_cusp_bound d hmod F Y
      hanalytic hgerm hsum hslash c
  have hfinite : ∀ c ∈ ({0, 1 / 2, 1 / 3} : Set ℝ),
      (↑c : OnePoint ℝ).IsBoundedAt
        (fun z : UpperHalfPlane =>
          ModularForm.discriminant z ^ (8 * formClassNumber (-(d : ℤ))) *
            cmPoleClearedFunction (-(d : ℤ)) F z)
        ((96 * formClassNumber (-(d : ℤ)) + 4 : ℕ) : ℤ) := by
    intro c hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with hc | hc | hc
    · subst c
      simpa [FiniteLevelSixCusp.chartGL_smul_infty] using hb .zero
    · subst c
      simpa [FiniteLevelSixCusp.chartGL_smul_infty] using hb .half
    · subst c
      simpa [FiniteLevelSixCusp.chartGL_smul_infty] using hb .third
  exact character_obstruction_of_finite_cusp_bounds p hp5 sign hsign d hd hsq
    hmod hr hsep hclass F Y hanalytic htrans hgerm hsum hfinite

end SptClassification
