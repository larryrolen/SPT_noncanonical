/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.LevelSixWeierstrass
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.RingTheory.Ideal.Nonunits
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# Good integral models for the level-six family

If six is invertible and both the parameter and its modular invariant belong
to the base ring, the explicit equation has unit discriminant. This upgrades
the field-valued reduction criterion to a good model over the whole ring.
-/

public section

namespace SptClassification.LevelSixWeierstrass

variable {R : Type*} [CommRing R]

/-- The invariant equation excludes a singular fiber at every maximal ideal,
so the discriminant is a unit in the original ring. -/
theorem isUnit_discriminant_of_j_relation (t j : R) (h6 : IsUnit (6 : R))
    (hj : j * (curve t).Δ = (curve t).c₄ ^ 3) : IsUnit (curve t).Δ := by
  by_contra h
  obtain ⟨I, hI, hmem⟩ := exists_max_ideal_of_mem_nonunits h
  letI : I.IsMaximal := hI
  letI : Field (R ⧸ I) := Ideal.Quotient.field I
  let red := Ideal.Quotient.mk I
  have h6' : (6 : R ⧸ I) ≠ 0 := by
    have hu := h6.map red
    simpa only [map_ofNat] using hu.ne_zero
  haveI := reduction_isElliptic red t j h6' hj
  have hn : (curve (red t)).Δ ≠ 0 :=
    isUnit_iff_ne_zero.mp WeierstrassCurve.IsElliptic.isUnit
  apply hn
  have hz : red (curve t).Δ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  simpa only [curve_discriminant, map_mul, map_pow, map_add, map_ofNat] using hz

/-- An integral modular invariant gives a smooth Weierstrass model wherever
six is invertible. -/
theorem integral_isElliptic_of_j_relation (t j : R) (h6 : IsUnit (6 : R))
    (hj : j * (curve t).Δ = (curve t).c₄ ^ 3) : (curve t).IsElliptic :=
  ⟨isUnit_discriminant_of_j_relation t j h6 hj⟩

/-- All three finite cusp factors are units on a good fiber of this family. -/
theorem isUnit_cusp_factors (t : R) (hΔ : IsUnit (curve t).Δ) :
    IsUnit t ∧ IsUnit (t + 8) ∧ IsUnit (t + 9) := by
  rw [curve_discriminant] at hΔ
  obtain ⟨hrest, h9⟩ := (Commute.all _ _).isUnit_mul_iff.mp hΔ
  obtain ⟨hrest, h8⟩ := (Commute.all _ _).isUnit_mul_iff.mp hrest
  have ht := ((Commute.all _ _).isUnit_mul_iff.mp hrest).2
  exact ⟨(isUnit_pow_iff (by decide)).mp ht, (isUnit_pow_iff (by decide)).mp h8,
    (isUnit_pow_iff (by decide)).mp h9⟩

end SptClassification.LevelSixWeierstrass
