/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.Orientation
public import SptClassification.ModularForms.GammaZeroSixGenerators

/-!
# A finite certificate for level-six orientations

For a discriminant congruent to one modulo24, only the leading and last
coefficients modulo6 and the middle coefficient modulo12 matter. The twelve
explicit coset representatives realize each unit middle-coefficient orientation.
-/

public section

namespace SptClassification

namespace BinaryQuadraticForm

/-- The bounded coefficient representative relevant to a level-six orientation. -/
def orientationResidues (Q : BinaryQuadraticForm) : BinaryQuadraticForm :=
  ⟨Q.a % 6, Q.b % 12, Q.c % 6⟩

theorem orientationResidues_divisibility (Q : BinaryQuadraticForm) :
    6 ∣ Q.a - Q.orientationResidues.a ∧
      12 ∣ Q.b - Q.orientationResidues.b ∧ 6 ∣ Q.c - Q.orientationResidues.c := by
  refine ⟨⟨Q.a / 6, ?_⟩, ⟨Q.b / 12, ?_⟩, ⟨Q.c / 6, ?_⟩⟩
  · have := Int.mul_ediv_add_emod Q.a 6
    dsimp [orientationResidues]
    omega
  · have := Int.mul_ediv_add_emod Q.b 12
    dsimp [orientationResidues]
    omega
  · have := Int.mul_ediv_add_emod Q.c 6
    dsimp [orientationResidues]
    omega

theorem orientationResidues_discriminant_mod (Q : BinaryQuadraticForm) :
    Q.orientationResidues.discriminant % 24 = Q.discriminant % 24 := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩ := Q.orientationResidues_divisibility
  have ha' : Q.a = Q.orientationResidues.a + 6 * a := by omega
  have hb' : Q.b = Q.orientationResidues.b + 12 * b := by omega
  have hc' : Q.c = Q.orientationResidues.c + 6 * c := by omega
  have hd : 24 ∣ Q.discriminant - Q.orientationResidues.discriminant := by
    refine ⟨Q.orientationResidues.b * b + 6 * b ^ 2 -
      Q.orientationResidues.a * c - Q.orientationResidues.c * a - 6 * a * c, ?_⟩
    simp only [discriminant]
    rw [ha', hb', hc']
    ring
  have he := (ZMod.intCast_zmod_eq_zero_iff_dvd (Q.discriminant - Q.orientationResidues.discriminant) 24).mpr hd
  rw [Int.cast_sub, sub_eq_zero] at he
  exact ((ZMod.intCast_eq_intCast_iff _ _ 24).mp he).symm

/-- Substitution preserves the leading-mod6/middle-mod12 coefficient congruences. -/
theorem pullback_orientation_congr (Q R : BinaryQuadraticForm)
    (M : Matrix (Fin 2) (Fin 2) ℤ)
    (ha : 6 ∣ Q.a - R.a) (hb : 12 ∣ Q.b - R.b) (hc : 6 ∣ Q.c - R.c) :
    6 ∣ (Q.pullback M).a - (R.pullback M).a ∧
      12 ∣ (Q.pullback M).b - (R.pullback M).b := by
  obtain ⟨a, ha⟩ := ha
  obtain ⟨b, hb⟩ := hb
  obtain ⟨c, hc⟩ := hc
  have ha' : Q.a = R.a + 6 * a := by omega
  have hb' : Q.b = R.b + 12 * b := by omega
  have hc' : Q.c = R.c + 6 * c := by omega
  constructor
  · refine ⟨a * M 0 0 ^ 2 + 2 * b * M 0 0 * M 1 0 + c * M 1 0 ^ 2, ?_⟩
    simp only [pullback, ha', hb', hc']
    ring
  · refine ⟨a * M 0 0 * M 0 1 + b * (M 0 0 * M 1 1 + M 0 1 * M 1 0) +
      c * M 1 0 * M 1 1, ?_⟩
    simp only [pullback, ha', hb', hc']
    ring

end BinaryQuadraticForm

/-- Units modulo12 have precisely the four source orientations. -/
theorem unit_twelve_value_cases (r : ZMod 12) (hr : IsUnit r) :
    r.val = 1 ∨ r.val = 5 ∨ r.val = 7 ∨ r.val = 11 := by
  have table : ∀ i : Fin 12, i.val.Coprime 12 →
      i.val = 1 ∨ i.val = 5 ∨ i.val = 7 ∨ i.val = 11 := by decide +kernel
  have hunit : IsUnit (r.val : ZMod 12) := by simpa using hr
  exact table ⟨r.val, ZMod.val_lt r⟩ ((ZMod.isUnit_iff_coprime r.val 12).mp hunit)

/-- The complete bounded residue certificate: one of the twelve verified
representatives realizes each admissible orientation. -/
theorem oriented_representative_certificate :
    ∀ a : Fin 6, ∀ b : Fin 12, ∀ c : Fin 6, ∀ r : Fin 12,
      (r.val = 1 ∨ r.val = 5 ∨ r.val = 7 ∨ r.val = 11) →
      ((b.val : ℤ) ^ 2 - 4 * (a.val : ℤ) * (c.val : ℤ)) % 24 = 1 →
      ∃ i : Fin 12,
        let Q : BinaryQuadraticForm := ⟨a.val, b.val, c.val⟩
        let R := BinaryQuadraticForm.transform (GammaZeroSix.representative i) Q
        6 ∣ R.a ∧ R.b % 12 = (r.val : ℤ) := by
  simp only [BinaryQuadraticForm.transform, Matrix.SpecialLinearGroup.coe_inv,
    GammaZeroSix.representative_matrix, Matrix.adjugate_fin_two,
    BinaryQuadraticForm.pullback]
  decide +kernel

/-- Every form of discriminant one modulo24 has a transform of each unit orientation. -/
theorem exists_oriented_transform (Q : BinaryQuadraticForm)
    (hD : Q.discriminant % 24 = 1) (r : ZMod 12) (hr : IsUnit r) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      6 ∣ (BinaryQuadraticForm.transform g Q).a ∧
        ((BinaryQuadraticForm.transform g Q).b : ZMod 12) = r := by
  have ha0 := Int.emod_nonneg Q.a (by decide : (6 : ℤ) ≠ 0)
  have ha6 := Int.emod_lt_of_pos Q.a (by decide : (0 : ℤ) < 6)
  have hb0 := Int.emod_nonneg Q.b (by decide : (12 : ℤ) ≠ 0)
  have hb12 := Int.emod_lt_of_pos Q.b (by decide : (0 : ℤ) < 12)
  have hc0 := Int.emod_nonneg Q.c (by decide : (6 : ℤ) ≠ 0)
  have hc6 := Int.emod_lt_of_pos Q.c (by decide : (0 : ℤ) < 6)
  let a : Fin 6 := ⟨(Q.a % 6).toNat, by omega⟩
  let b : Fin 12 := ⟨(Q.b % 12).toNat, by omega⟩
  let c : Fin 6 := ⟨(Q.c % 6).toNat, by omega⟩
  let rr : Fin 12 := ⟨r.val, ZMod.val_lt r⟩
  have hrep : (⟨a.val, b.val, c.val⟩ : BinaryQuadraticForm) = Q.orientationResidues := by
    ext <;> simp only [a, b, c, BinaryQuadraticForm.orientationResidues, Int.toNat_of_nonneg, ha0, hb0, hc0]
  have hsmall : ((b.val : ℤ) ^ 2 - 4 * (a.val : ℤ) * (c.val : ℤ)) % 24 = 1 := by
    change (⟨a.val, b.val, c.val⟩ : BinaryQuadraticForm).discriminant % 24 = 1
    rw [hrep, Q.orientationResidues_discriminant_mod, hD]
  obtain ⟨i, hi⟩ := oriented_representative_certificate a b c rr (unit_twelve_value_cases r hr) hsmall
  dsimp only at hi
  rw [hrep] at hi
  let g := GammaZeroSix.representative i
  obtain ⟨ha, hb, hc⟩ := Q.orientationResidues_divisibility
  obtain ⟨hca, hcb⟩ := Q.pullback_orientation_congr Q.orientationResidues
    (g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) ha hb hc
  change 6 ∣ (BinaryQuadraticForm.transform g Q).a -
    (BinaryQuadraticForm.transform g Q.orientationResidues).a at hca
  change 12 ∣ (BinaryQuadraticForm.transform g Q).b -
    (BinaryQuadraticForm.transform g Q.orientationResidues).b at hcb
  refine ⟨g, ?_, ?_⟩
  · simpa only [g, sub_add_cancel] using dvd_add hca hi.1
  · have heq := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 12).mpr hcb
    rw [Int.cast_sub, sub_eq_zero] at heq
    rw [heq]
    calc
      ((BinaryQuadraticForm.transform g Q.orientationResidues).b : ZMod 12) =
          (((BinaryQuadraticForm.transform g Q.orientationResidues).b % 12 : ℤ) : ZMod 12) :=
        (ZMod.intCast_mod _ 12).symm
      _ = ((r.val : ℤ) : ZMod 12) := congrArg (fun n : ℤ => (n : ZMod 12)) hi.2
      _ = r := by simp

end SptClassification
