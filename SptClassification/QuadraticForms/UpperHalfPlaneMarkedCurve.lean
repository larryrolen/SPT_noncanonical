/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.EtaTateHolomorphy
public import SptClassification.QuadraticForms.TateReciprocalInvariant

/-!
# The marked lattice cubic over the upper half-plane

The point `1/6` defines the actual cyclic-six marking at every period pair
`(1,τ)`. Its short Tate coordinate is regular because this point has order six.
-/

public section

namespace SptClassification.ComplexUniformization

open LevelSixWeierstrass

/-- Membership of the real point `m/6` in the normalized period lattice. -/
theorem int_div_six_mem_upperHalfPlane_lattice (z : UpperHalfPlane) (m : ℤ) :
    (m : ℂ) / 6 ∈ (upperHalfPlanePeriods z).lattice ↔ 6 ∣ m := by
  rw [PeriodPair.mem_lattice]
  simp only [upperHalfPlanePeriods_omega_one, upperHalfPlanePeriods_omega_two,
    mul_one]
  constructor
  · rintro ⟨k, l, h⟩
    have him : (l : ℝ) * (z : ℂ).im = 0 := by
      simpa using congrArg Complex.im h
    have hlR : (l : ℝ) = 0 := (mul_eq_zero.mp him).resolve_right (ne_of_gt z.im_pos)
    have hl : l = 0 := by exact_mod_cast hlR
    subst l
    have hk : (k : ℂ) = (m : ℂ) / 6 := by simpa using h
    have hmul : (m : ℂ) = 6 * (k : ℂ) := by
      rw [eq_div_iff (by norm_num : (6 : ℂ) ≠ 0)] at hk
      simpa only [mul_comm] using hk.symm
    refine ⟨k, ?_⟩
    exact_mod_cast hmul
  · rintro ⟨k, rfl⟩
    refine ⟨k, 0, ?_⟩
    push_cast
    ring

/-- The uniformized class of `1/6` on the normalized lattice cubic. -/
noncomputable def upperHalfPlaneSixPoint (z : UpperHalfPlane) :
    (curve (upperHalfPlanePeriods z)).toAffine.Point :=
  uniformization (upperHalfPlanePeriods z)
    (QuotientAddGroup.mk' (upperHalfPlanePeriods z).lattice.toAddSubgroup (1 / 6))

theorem upperHalfPlaneSixPoint_nsmul_eq_zero (z : UpperHalfPlane) (n : ℕ) :
    n • upperHalfPlaneSixPoint z = 0 ↔ 6 ∣ n := by
  unfold upperHalfPlaneSixPoint
  rw [← map_nsmul, map_eq_zero_iff (uniformization (upperHalfPlanePeriods z))
      (uniformization (upperHalfPlanePeriods z)).injective,
    ← map_nsmul]
  have hz :
      (QuotientAddGroup.mk' (upperHalfPlanePeriods z).lattice.toAddSubgroup)
        (n • (1 / 6 : ℂ)) = 0 ↔
          n • (1 / 6 : ℂ) ∈ (upperHalfPlanePeriods z).lattice :=
    QuotientAddGroup.eq_zero_iff _
  rw [hz]
  have heq : n • (1 / 6 : ℂ) = (n : ℂ) / 6 := by rw [nsmul_eq_mul]; ring
  rw [heq]
  have hdiv : (6 : ℤ) ∣ (n : ℤ) ↔ (6 : ℕ) ∣ n := by
    exact_mod_cast (Iff.rfl : (6 : ℕ) ∣ n ↔ (6 : ℕ) ∣ n)
  exact (int_div_six_mem_upperHalfPlane_lattice z (n : ℤ)).trans hdiv

theorem upperHalfPlaneSixPoint_order (z : UpperHalfPlane) :
    addOrderOf (upperHalfPlaneSixPoint z) = 6 := by
  apply Nat.dvd_antisymm
  · exact addOrderOf_dvd_of_nsmul_eq_zero
      ((upperHalfPlaneSixPoint_nsmul_eq_zero z 6).mpr (dvd_refl 6))
  · exact (upperHalfPlaneSixPoint_nsmul_eq_zero z _).mp (addOrderOf_nsmul_eq_zero _)

/-- The normalized lattice curve with its actual cyclic-six marking. -/
@[expose] noncomputable def upperHalfPlanePair (z : UpperHalfPlane) : LevelSixPair ℂ :=
  ⟨curve (upperHalfPlanePeriods z), curve_isElliptic _,
    upperHalfPlaneSixPoint z, upperHalfPlaneSixPoint_order z⟩

/-- The marked coordinate is given by the Weierstrass functions, and its only
possible short-coordinate denominator is nonzero everywhere in the family. -/
theorem upperHalfPlanePair_tateCoordinate_eq (z : UpperHalfPlane) :
    (upperHalfPlanePeriods z).derivWeierstrassP (1 / 6) / 2 ≠ 0 ∧
      LevelSixPair.tateCoordinate (by norm_num) (upperHalfPlanePair z) =
        shortTateParameter (-(upperHalfPlanePeriods z).g₂ / 4)
          ((upperHalfPlanePeriods z).weierstrassP (1 / 6))
          ((upperHalfPlanePeriods z).derivWeierstrassP (1 / 6) / 2) := by
  have hn : (1 / 6 : ℂ) ∉ (upperHalfPlanePeriods z).lattice := by
    simpa using (not_congr (int_div_six_mem_upperHalfPlane_lattice z 1)).mpr
      (by norm_num : ¬ (6 : ℤ) ∣ 1)
  obtain ⟨h, hP⟩ := uniformization_coordinates (upperHalfPlanePeriods z) (1 / 6) hn
  simpa only [upperHalfPlanePair, curve_a₄] using
    (upperHalfPlanePair z).tateCoordinate_eq_shortTateParameter
    (curve_a₁ _) (curve_a₂ _) (curve_a₃ _) _ _ h hP

end SptClassification.ComplexUniformization
