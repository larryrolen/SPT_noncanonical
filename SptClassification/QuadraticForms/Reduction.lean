/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.Action
public import Mathlib.Data.Nat.Find

/-!
# Reduction of positive definite integral binary quadratic forms

Choose a transform with least positive leading coefficient. A translation then
puts the middle coefficient between minus that coefficient and that coefficient.
The inversion matrix shows that the last coefficient is at least the first.
The resulting bounds will make the orbit space finite.
-/

@[expose] public section

namespace SptClassification.BinaryQuadraticForm

theorem transform_a_pos (Q : BinaryQuadraticForm) (ha : 0 < Q.a)
    (hD : Q.discriminant < 0) (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    0 < (transform g Q).a :=
  Q.pullback_a_pos ha hD _ (g⁻¹).property

@[simp] theorem transform_T_zpow_a (Q : BinaryQuadraticForm) (t : ℤ) :
    (transform (ModularGroup.T ^ t) Q).a = Q.a := by
  rw [transform, ← zpow_neg, ModularGroup.coe_T_zpow]
  simp [pullback]

theorem transform_T_zpow_b (Q : BinaryQuadraticForm) (t : ℤ) :
    (transform (ModularGroup.T ^ t) Q).b = Q.b - 2 * Q.a * t := by
  rw [transform, ← zpow_neg, ModularGroup.coe_T_zpow]
  simp [pullback]
  ring

@[simp] theorem transform_S_a (Q : BinaryQuadraticForm) :
    (transform ModularGroup.S Q).a = Q.c := by
  rw [transform, Matrix.SpecialLinearGroup.SL2_inv_expl]
  simp [ModularGroup.S, pullback]

theorem exists_minimal_transform (Q : BinaryQuadraticForm) (ha : 0 < Q.a)
    (hD : Q.discriminant < 0) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      ∀ h : Matrix.SpecialLinearGroup (Fin 2) ℤ, (transform g Q).a ≤ (transform h Q).a := by
  classical
  have hex : ∃ n : ℕ, ∃ g : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      (transform g Q).a.toNat = n := ⟨Q.a.toNat, 1, by simp⟩
  obtain ⟨g, hg⟩ := Nat.find_spec hex
  refine ⟨g, ?_⟩
  intro h
  have hle := Nat.find_min' hex ⟨h, rfl⟩
  rw [← hg] at hle
  have hgpos := Q.transform_a_pos ha hD g
  have hhpos := Q.transform_a_pos ha hD h
  omega

/-- Every positive definite integral form admits a reduced transform. -/
theorem exists_reduced_transform (Q : BinaryQuadraticForm) (ha : 0 < Q.a)
    (hD : Q.discriminant < 0) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      |(transform g Q).b| ≤ (transform g Q).a ∧ (transform g Q).a ≤ (transform g Q).c := by
  obtain ⟨g, hg⟩ := Q.exists_minimal_transform ha hD
  let R := transform g Q
  have hRa : 0 < R.a := Q.transform_a_pos ha hD g
  let t : ℤ := (R.b + R.a) / (2 * R.a)
  have hrem0 := Int.emod_nonneg (R.b + R.a) (by omega : 2 * R.a ≠ 0)
  have hrem := Int.emod_lt_of_pos (R.b + R.a) (by omega : 0 < 2 * R.a)
  have heq : R.b - 2 * R.a * t = (R.b + R.a) % (2 * R.a) - R.a := by
    have h := Int.mul_ediv_add_emod (R.b + R.a) (2 * R.a)
    change 2 * R.a * t + (R.b + R.a) % (2 * R.a) = R.b + R.a at h
    linarith
  refine ⟨ModularGroup.T ^ t * g, ?_, ?_⟩
  · simp only [transform_mul, transform_T_zpow_a, transform_T_zpow_b]
    change |R.b - 2 * R.a * t| ≤ R.a
    rw [heq, abs_le]
    omega
  · simp only [transform_mul, transform_T_zpow_a]
    simpa only [transform_mul, transform_S_a] using
      hg (ModularGroup.S * (ModularGroup.T ^ t * g))

theorem square_b_le_square_a (Q : BinaryQuadraticForm) (hb : |Q.b| ≤ Q.a) :
    Q.b ^ 2 ≤ Q.a ^ 2 := by
  obtain ⟨hl, hu⟩ := abs_le.mp hb
  have h := mul_nonneg (sub_nonneg.mpr hu) (show 0 ≤ Q.a + Q.b by omega)
  nlinarith

theorem reduced_a_bound (Q : BinaryQuadraticForm) (ha : 0 < Q.a)
    (hb : |Q.b| ≤ Q.a) (hac : Q.a ≤ Q.c) : Q.a ≤ -Q.discriminant := by
  have hbsq := Q.square_b_le_square_a hb
  have haa := mul_le_mul_of_nonneg_left hac (le_of_lt ha)
  have ha1 : 1 ≤ Q.a := ha
  have hsq := mul_nonneg (le_of_lt ha) (sub_nonneg.mpr ha1)
  dsimp [discriminant]
  nlinarith

theorem reduced_c_bound (Q : BinaryQuadraticForm) (ha : 0 < Q.a)
    (hb : |Q.b| ≤ Q.a) (hac : Q.a ≤ Q.c) :
    Q.c ≤ Q.discriminant ^ 2 - Q.discriminant := by
  have haBound := Q.reduced_a_bound ha hb hac
  have hbsq := Q.square_b_le_square_a hb
  generalize hD : Q.discriminant = D at haBound ⊢
  have hdisc : D = Q.b ^ 2 - 4 * Q.a * Q.c := by rw [← hD]; rfl
  have hN := mul_nonneg (show 0 ≤ -D - Q.a by omega) (show 0 ≤ -D + Q.a by omega)
  have hc : 0 ≤ Q.c := by omega
  have hprod := mul_le_mul_of_nonneg_right (show (1 : ℤ) ≤ 4 * Q.a by omega) hc
  nlinarith only [hdisc, hbsq, hN, hprod]

end SptClassification.BinaryQuadraticForm
