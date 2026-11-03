/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.QuadraticCuspGauss
public import SptClassification.ModularForms.EtaInverseGeneratorCriterion
public import SptClassification.ModularForms.EtaOddMatrix
import SptClassification.Theta.EtaWeilGeneratorWords

/-!
# Modular generator frontier for the analytic inverse-eta Hecke step

The concrete three-term prime expression already has its full signed Fourier
row, holomorphy, cusp germ, and translation law. The generator criterion makes
its remaining inversion transformation explicit. It is an unresolved
manuscript-specific analytic obligation, not a cited literature assumption
[rolenManuscript, §3].
-/

public section

namespace SptClassification.QSeries

open UpperHalfPlane
open scoped MatrixGroups

/-- The determinant-one matrix connecting two nonzero affine Hecke points
across inversion. The equation is the exact inverse-index condition modulo
`n`; it also applies when `n` is composite. -/
def cuspAffineInversionMatrix (n j k : ℕ) (q : ℤ)
    (h : (n : ℤ) * q = (24 * j : ℤ) * (24 * k : ℤ) + 1) :
    Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  ⟨!![(24 * j : ℤ), -q; (n : ℤ), -(24 * k : ℤ)], by
    rw [Matrix.det_fin_two]
    norm_num
    linear_combination h⟩

/-- The general odd-denominator eta law specialized to the matrix that
connects two affine Hecke points. Its multiplier is a single explicit phase,
so the different affine terms cannot be assigned unrelated multipliers. -/
theorem cuspAffineInversionMatrix_eta_law (n j k : ℕ) (hn : 0 < n)
    (hodd : (n : ℤ) % 2 = 1) (q : ℤ)
    (hq : (n : ℤ) * q = (24 * j : ℤ) * (24 * k : ℤ) + 1)
    (z : UpperHalfPlane) :
    ModularForm.eta (cuspAffineInversionMatrix n j k q hq • z : UpperHalfPlane) =
      etaOddMatrixPhase (24 * j) (-q) n (-(24 * k)) *
        ((n : ℂ) * z - (24 * k : ℂ)).sqrt * ModularForm.eta z := by
  have hdet : (24 * j : ℤ) * (-(24 * k : ℤ)) - (-q) * (n : ℤ) = 1 := by
    linear_combination hq
  have heq : etaMatrix (24 * j) (-q) n (-(24 * k)) hdet =
      cuspAffineInversionMatrix n j k q hq := by
    apply Subtype.ext
    ext i l
    fin_cases i <;> fin_cases l <;>
      simp [etaMatrix, cuspAffineInversionMatrix]
  rw [← heq]
  have h := eta_odd_matrix_law (24 * j) (-q) n (-(24 * k))
    hdet (by exact_mod_cast hn) hodd z
  have hcast : (((24 * (k : ℤ)) : ℤ) : ℂ) = (24 * k : ℂ) := by
    norm_num
  rw [Int.cast_neg, hcast] at h
  simpa only [Int.cast_natCast, sub_eq_add_neg] using h

/-- Inversion permutes affine Hecke points when their indices satisfy the
inverse-index congruence. This is a point identity, independent of eta's
multiplier and the quadratic middle row. -/
theorem cuspAffinePoint_inversion_matrix (n j k : ℕ) (hn : 0 < n)
    (q : ℤ) (h : (n : ℤ) * q = (24 * j : ℤ) * (24 * k : ℤ) + 1)
    (τ : UpperHalfPlane) :
    cuspAffineInversionMatrix n j k q h •
        cuspAffinePoint n k hn (ModularGroup.S • τ) =
      cuspAffinePoint n j hn τ := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [cuspAffinePoint_coe, UpperHalfPlane.modular_S_smul]
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hC : (n : ℂ) * (q : ℂ) = (24 * j : ℂ) * (24 * k : ℂ) + 1 := by
    exact_mod_cast h
  norm_num [cuspAffineInversionMatrix]
  field_simp [hnC, τ.ne_zero]
  linear_combination -(τ : ℂ) * hC

/-- The indices divisible by `n` in the width-`n²` affine orbit form a
width-`n` orbit based at the inverted dilated point. This keeps the extra
division by `n` in the affine point; a fractional translation at that point
would have a different width. -/
theorem cuspAffinePoint_square_mul_inversion (n j : ℕ) (hn : 0 < n)
    (τ : UpperHalfPlane) :
    cuspAffinePoint (n * n) (n * j) (Nat.mul_pos hn hn)
        (ModularGroup.S • τ) =
      cuspAffinePoint n j hn (ModularGroup.S • natDilation n hn τ) := by
  apply UpperHalfPlane.ext
  simp only [cuspAffinePoint_coe, UpperHalfPlane.modular_S_smul,
    natDilation_coe]
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hnC, τ.ne_zero]
  push_cast
  ring

/-- An affine point based at an `n`-fold dilation is the corresponding
fractional translate. This identifies the unit part of the divisible
square-width orbit with the points in the quadratic middle row. -/
theorem cuspAffinePoint_dilation_eq_fractionTranslate (n j : ℕ)
    (hn : 0 < n) (τ : UpperHalfPlane) :
    cuspAffinePoint n j hn (natDilation n hn τ) =
      cuspFractionTranslate n j hn τ := by
  apply UpperHalfPlane.ext
  rw [cuspAffinePoint_coe, cuspFractionTranslate_coe, natDilation_coe]
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hnC]

/-- The divisible indices in a square-width orbit are parametrized by
the indices of the original width. -/
theorem sum_range_square_dvd (n : ℕ) (hn : 0 < n) (F : ℕ → ℂ) :
    (∑ j ∈ (Finset.range (n * n)).filter (n ∣ ·), F j) =
      ∑ t ∈ Finset.range n, F (n * t) := by
  classical
  symm
  apply Finset.sum_bij (fun t _ => n * t)
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
    exact ⟨Nat.mul_lt_mul_of_pos_left ht hn, ⟨t, rfl⟩⟩
  · intro t₁ _ t₂ _ h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hmul := Nat.mul_lt_mul_of_pos_left hlt hn
      omega
    · have hmul := Nat.mul_lt_mul_of_pos_left hgt hn
      omega
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨hjlt, ⟨t, rfl⟩⟩ := hj
    have ht : t < n := by
      by_contra hnot
      have hle : n ≤ t := by omega
      have hmul := Nat.mul_le_mul_left n hle
      omega
    exact ⟨t, Finset.mem_range.mpr ht, rfl⟩
  · intro t _
    rfl

/-- Split a square-width affine sum into indices prime to the width and
indices coming from the smaller affine orbit. -/
theorem sum_range_square_split (n : ℕ) (hn : 0 < n) (F : ℕ → ℂ) :
    (∑ j ∈ Finset.range (n * n), F j) =
      (∑ j ∈ (Finset.range (n * n)).filter (¬ n ∣ ·), F j) +
        ∑ t ∈ Finset.range n, F (n * t) := by
  classical
  rw [← sum_range_square_dvd n hn F]
  simpa only [add_comm] using
    (Finset.sum_filter_add_sum_filter_not
      (s := Finset.range (n * n)) (p := fun j => n ∣ j) F).symm

/-- For a prime width, the nondivisible indices of the square-width
affine orbit are precisely the unit indices. -/
theorem cuspAffine_unit_primeSquare_iff (p j : ℕ) (hp : p.Prime) :
    IsUnit (j : ZMod (p * p)) ↔ ¬ p ∣ j := by
  rw [ZMod.isUnit_iff_coprime]
  constructor
  · intro hcop hdiv
    have hdp : p ∣ p * p := ⟨p, rfl⟩
    have hdg := Nat.dvd_gcd hdiv hdp
    change Nat.gcd j (p * p) = 1 at hcop
    rw [hcop] at hdg
    exact hp.not_dvd_one hdg
  · intro hnot
    have hcop : j.Coprime p := (hp.coprime_iff_not_dvd.mpr hnot).symm
    simpa only [pow_two] using hcop.pow_right 2

/-- A unit affine index has an inverse partner modulo the cusp width. The
relation is the determinant-one condition for `cuspAffineInversionMatrix`.
This finite-ring statement does not require a prime cusp width. -/
theorem cuspAffine_inverseIndex_exists (n k : ℕ) (hn : 0 < n)
    (h24 : IsUnit (24 : ZMod n)) (hk : IsUnit (k : ZMod n)) :
    ∃ j : ℕ, j < n ∧ ∃ q : ℤ,
      (n : ℤ) * q = (24 * j : ℤ) * (24 * k : ℤ) + 1 := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let u : ZMod n := (24 : ZMod n) ^ 2 * k
  have hu : IsUnit u := (h24.pow 2).mul hk
  obtain ⟨v, hv⟩ := hu
  let j : ℕ := (-((v⁻¹ : (ZMod n)ˣ) : ZMod n)).val
  have hj : j < n := ZMod.val_lt _
  have hjcast : (j : ZMod n) = -((v⁻¹ : (ZMod n)ˣ) : ZMod n) :=
    ZMod.natCast_zmod_val _
  have hmod : (24 * j : ZMod n) * (24 * k : ZMod n) + 1 = 0 := by
    rw [hjcast]
    calc
      (24 : ZMod n) * -((v⁻¹ : (ZMod n)ˣ) : ZMod n) *
          ((24 : ZMod n) * k) + 1 =
          u * -((v⁻¹ : (ZMod n)ˣ) : ZMod n) + 1 := by dsimp [u]; ring
      _ = 0 := by
        have hunit : u * ((v⁻¹ : (ZMod n)ˣ) : ZMod n) = 1 := by
          rw [← hv]
          exact_mod_cast v.mul_inv
        rw [mul_neg, hunit]
        ring
  have hnat : ((576 * j * k + 1 : ℕ) : ZMod n) = 0 := by
    convert hmod using 1 <;> push_cast <;> ring
  obtain ⟨q, hq⟩ := (ZMod.natCast_eq_zero_iff (576 * j * k + 1) n).mp hnat
  refine ⟨j, hj, (q : ℤ), ?_⟩
  calc
    (n : ℤ) * q = (576 * j * k + 1 : ℕ) := by
      exact_mod_cast (show n * q = 576 * j * k + 1 by omega)
    _ = (24 * j : ℤ) * (24 * k : ℤ) + 1 := by push_cast; ring

/-- The inverse affine index is unique among the standard representatives
modulo the cusp width. -/
theorem cuspAffine_inverseIndex_unique (n k j₁ j₂ : ℕ) (hn : 0 < n)
    (h24 : IsUnit (24 : ZMod n)) (hk : IsUnit (k : ZMod n))
    (hj₁ : j₁ < n) (hj₂ : j₂ < n)
    (hq₁ : ∃ q : ℤ,
      (n : ℤ) * q = (24 * j₁ : ℤ) * (24 * k : ℤ) + 1)
    (hq₂ : ∃ q : ℤ,
      (n : ℤ) * q = (24 * j₂ : ℤ) * (24 * k : ℤ) + 1) : j₁ = j₂ := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let u : ZMod n := (24 : ZMod n) ^ 2 * k
  have hu : IsUnit u := (h24.pow 2).mul hk
  have hrel (j : ℕ) (hq : ∃ q : ℤ,
      (n : ℤ) * q = (24 * j : ℤ) * (24 * k : ℤ) + 1) :
      u * (j : ZMod n) = -1 := by
    obtain ⟨q, hq⟩ := hq
    have hz := congrArg (fun z : ℤ => (z : ZMod n)) hq
    have hprod : (24 * j : ZMod n) * (24 * k : ZMod n) + 1 = 0 := by
      norm_num [Int.cast_mul, Int.cast_add, Int.cast_natCast,
        ZMod.natCast_self] at hz
      exact hz.symm
    calc
      u * (j : ZMod n) =
          (24 * j : ZMod n) * (24 * k : ZMod n) := by dsimp [u]; ring
      _ = -1 := add_eq_zero_iff_eq_neg.mp hprod
  have heq : u * (j₁ : ZMod n) = u * (j₂ : ZMod n) :=
    (hrel j₁ hq₁).trans (hrel j₂ hq₂).symm
  obtain ⟨v, hv⟩ := hu
  have hvEq : (v : ZMod n) * (j₁ : ZMod n) =
      (v : ZMod n) * (j₂ : ZMod n) := by simpa [hv] using heq
  have hvunit : ((v⁻¹ : (ZMod n)ˣ) : ZMod n) * (v : ZMod n) = 1 := by
    exact_mod_cast v.inv_mul
  have hcast : (j₁ : ZMod n) = (j₂ : ZMod n) := by
    calc
      (j₁ : ZMod n) =
          ((v⁻¹ : (ZMod n)ˣ) : ZMod n) * ((v : ZMod n) * j₁) := by
            rw [← mul_assoc, hvunit, one_mul]
      _ = ((v⁻¹ : (ZMod n)ˣ) : ZMod n) * ((v : ZMod n) * j₂) := by
        rw [hvEq]
      _ = (j₂ : ZMod n) := by rw [← mul_assoc, hvunit, one_mul]
  have hval := congrArg ZMod.val hcast
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hj₁,
    Nat.mod_eq_of_lt hj₂] using hval

/-- A unit affine index has exactly one inverse index in the standard
finite range. This is the finite selector used to reindex the Hecke orbit. -/
theorem cuspAffine_inverseIndex_existsUnique (n k : ℕ) (hn : 0 < n)
    (h24 : IsUnit (24 : ZMod n)) (hk : IsUnit (k : ZMod n)) :
    ∃! j : Fin n, ∃ q : ℤ,
      (n : ℤ) * q = (24 * (j : ℕ) : ℤ) * (24 * k : ℤ) + 1 := by
  obtain ⟨j, hj, hq⟩ := cuspAffine_inverseIndex_exists n k hn h24 hk
  refine ⟨⟨j, hj⟩, hq, ?_⟩
  intro y hy
  apply Fin.ext
  exact (cuspAffine_inverseIndex_unique n k j y hn h24 hk hj y.isLt hq hy).symm

/-- The inverse-index determinant condition forces the new affine index to
be a unit, so the same construction can be applied a second time. -/
theorem cuspAffine_inverseIndex_isUnit (n j k : ℕ)
    (hq : ∃ q : ℤ,
      (n : ℤ) * q = (24 * j : ℤ) * (24 * k : ℤ) + 1) :
    IsUnit (j : ZMod n) := by
  obtain ⟨q, hq⟩ := hq
  have hz := congrArg (fun z : ℤ => (z : ZMod n)) hq
  norm_num [Int.cast_mul, Int.cast_add, Int.cast_natCast,
    ZMod.natCast_self] at hz
  have hprod : (24 * j : ZMod n) * (24 * k : ZMod n) = -1 := by
    exact eq_neg_of_add_eq_zero_left hz.symm
  let v : ZMod n := -((24 : ZMod n) ^ 2 * k)
  have hmul : (j : ZMod n) * v = 1 := by
    calc
      (j : ZMod n) * v =
          -((24 * j : ZMod n) * (24 * k : ZMod n)) := by dsimp [v]; ring
      _ = 1 := by rw [hprod]; ring
  exact ⟨⟨(j : ZMod n), v, hmul, by simpa only [mul_comm] using hmul⟩, rfl⟩

/-- Standard representatives of the unit affine indices at cusp width `n`. -/
abbrev CuspAffineUnitIndex (n : ℕ) :=
  {j : Fin n // IsUnit ((j : ℕ) : ZMod n)}

noncomputable instance (n : ℕ) : Fintype (CuspAffineUnitIndex n) :=
  Fintype.ofFinite _

/-- The finite sum over indices not divisible by a prime is the sum over
unit representatives modulo its square. -/
theorem sum_nondivisible_primeSquare_eq_unit (p : ℕ) (hp : p.Prime)
    (F : ℕ → ℂ) :
    (∑ j ∈ (Finset.range (p * p)).filter (¬ p ∣ ·), F j) =
      ∑ k : CuspAffineUnitIndex (p * p), F ((k : Fin (p * p)) : ℕ) := by
  classical
  apply Finset.sum_bij (fun j hj =>
    (⟨⟨j, Finset.mem_range.mp (Finset.mem_filter.mp hj).1⟩,
      (cuspAffine_unit_primeSquare_iff p j hp).mpr
        (Finset.mem_filter.mp hj).2⟩ : CuspAffineUnitIndex (p * p)))
  · intro j _
    exact Finset.mem_univ _
  · intro j₁ _ j₂ _ heq
    exact congrArg (fun k : CuspAffineUnitIndex (p * p) =>
      ((k : Fin (p * p)) : ℕ)) heq
  · intro k _
    let j : ℕ := ((k : Fin (p * p)) : ℕ)
    have hj : j ∈ (Finset.range (p * p)).filter (¬ p ∣ ·) := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (k : Fin (p * p)).isLt,
          (cuspAffine_unit_primeSquare_iff p j hp).mp k.property⟩
    refine ⟨j, hj, ?_⟩
    apply Subtype.ext
    apply Fin.ext
    rfl
  · intro j _
    rfl

/-- The inverse partner of a unit affine index, chosen in the standard range. -/
noncomputable def cuspAffineInverseIndex (n : ℕ) (hn : 0 < n)
    (h24 : IsUnit (24 : ZMod n)) (k : CuspAffineUnitIndex n) :
    CuspAffineUnitIndex n :=
  let e := cuspAffine_inverseIndex_exists n (k : Fin n) hn h24 k.property
  ⟨⟨e.choose, e.choose_spec.1⟩,
    cuspAffine_inverseIndex_isUnit n e.choose (k : Fin n) e.choose_spec.2⟩

/-- The chosen partner satisfies the determinant-one congruence as an
integer identity with an explicit quotient. -/
theorem cuspAffineInverseIndex_spec (n : ℕ) (hn : 0 < n)
    (h24 : IsUnit (24 : ZMod n)) (k : CuspAffineUnitIndex n) :
    ∃ q : ℤ, (n : ℤ) * q =
      (24 * ((cuspAffineInverseIndex n hn h24 k : Fin n) : ℕ) : ℤ) *
        (24 * ((k : Fin n) : ℕ) : ℤ) + 1 := by
  exact (cuspAffine_inverseIndex_exists n (k : Fin n) hn h24 k.property).choose_spec.2

/-- Inverting the affine index twice returns the original index. This
provides the finite reindexing permutation without choosing a prime order. -/
theorem cuspAffineInverseIndex_involutive (n : ℕ) (hn : 0 < n)
    (h24 : IsUnit (24 : ZMod n)) :
    Function.Involutive (cuspAffineInverseIndex n hn h24) := by
  intro k
  apply Subtype.ext
  apply Fin.ext
  let j := cuspAffineInverseIndex n hn h24 k
  have hkj : ∃ q : ℤ, (n : ℤ) * q =
      (24 * ((k : Fin n) : ℕ) : ℤ) * (24 * ((j : Fin n) : ℕ) : ℤ) + 1 := by
    obtain ⟨q, hq⟩ := cuspAffineInverseIndex_spec n hn h24 k
    refine ⟨q, ?_⟩
    simpa only [mul_comm (24 * ((k : Fin n) : ℕ) : ℤ)
      (24 * ((j : Fin n) : ℕ) : ℤ)] using hq
  have hjk := cuspAffineInverseIndex_spec n hn h24 j
  simpa only [j] using
    (cuspAffine_inverseIndex_unique n (j : Fin n) (k : Fin n)
      (cuspAffineInverseIndex n hn h24 j : Fin n) hn h24 j.property
      k.val.isLt (cuspAffineInverseIndex n hn h24 j).val.isLt hkj hjk).symm

/-- The inverse-index permutation changes the quadratic middle-row weight
by the character of `-1`. The two factors of `24` contribute a square and
therefore no character factor. -/
theorem quadraticCuspWeight_inverseIndex (p : ℕ) [Fact p.Prime]
    (h24 : IsUnit (24 : ZMod p)) (k : CuspAffineUnitIndex p) :
    quadraticCuspWeight p
        (cuspAffineInverseIndex p (Fact.out : p.Prime).pos h24 k : Fin p).val =
      ((quadraticChar (ZMod p) (-1) : ℤ) : ℂ) *
        quadraticCuspWeight p (k : Fin p).val := by
  let χ := quadraticChar (ZMod p)
  let j := cuspAffineInverseIndex p (Fact.out : p.Prime).pos h24 k
  have hprod : ((24 : ZMod p) * ((j : Fin p).val : ZMod p)) *
      ((24 : ZMod p) * ((k : Fin p).val : ZMod p)) = -1 := by
    obtain ⟨q, hq⟩ := cuspAffineInverseIndex_spec p
      (Fact.out : p.Prime).pos h24 k
    have hz := congrArg (fun z : ℤ => (z : ZMod p)) hq
    simp only [Int.cast_mul, Int.cast_add, Int.cast_natCast,
      ZMod.natCast_self, zero_mul] at hz
    dsimp [j]
    linear_combination -hz
  have hraw : χ (24 : ZMod p) * χ ((j : Fin p).val : ZMod p) *
      (χ (24 : ZMod p) * χ ((k : Fin p).val : ZMod p)) =
        χ (-1 : ZMod p) := by
    simpa only [map_mul] using congrArg χ hprod
  have h24sq : (χ (24 : ZMod p) : ℤ) ^ 2 = 1 :=
    quadraticChar_sq_one h24.ne_zero
  have hksq : (χ ((k : Fin p).val : ZMod p) : ℤ) ^ 2 = 1 :=
    quadraticChar_sq_one k.property.ne_zero
  have hpair : (χ ((j : Fin p).val : ZMod p) : ℤ) *
      χ ((k : Fin p).val : ZMod p) = χ (-1 : ZMod p) := by
    calc
      _ = (χ (24 : ZMod p) : ℤ) ^ 2 *
          (χ ((j : Fin p).val : ZMod p) *
            χ ((k : Fin p).val : ZMod p)) := by rw [h24sq, one_mul]
      _ = _ := by rw [← hraw]; ring
  have hj : (χ ((j : Fin p).val : ZMod p) : ℤ) =
      χ (-1 : ZMod p) * χ ((k : Fin p).val : ZMod p) := by
    calc
      _ = χ ((j : Fin p).val : ZMod p) *
          (χ ((k : Fin p).val : ZMod p) : ℤ) ^ 2 := by
            rw [hksq, mul_one]
      _ = (χ ((j : Fin p).val : ZMod p) *
            χ ((k : Fin p).val : ZMod p)) *
          χ ((k : Fin p).val : ZMod p) := by ring
      _ = _ := by rw [hpair]
  simpa only [quadraticCuspWeight_eq_character, j, χ, Int.cast_mul] using
    congrArg (fun a : ℤ => (a : ℂ)) hj

/-- Reindexing the unit affine terms by modular inversion is a permutation. -/
noncomputable def cuspAffineInverseEquiv (n : ℕ) (hn : 0 < n)
    (h24 : IsUnit (24 : ZMod n)) :
    CuspAffineUnitIndex n ≃ CuspAffineUnitIndex n where
  toFun := cuspAffineInverseIndex n hn h24
  invFun := cuspAffineInverseIndex n hn h24
  left_inv := cuspAffineInverseIndex_involutive n hn h24
  right_inv := cuspAffineInverseIndex_involutive n hn h24

/-- Inversion sends the zero translate of the affine Hecke orbit to the
dilated point. This is the first term exchanged in the inversion calculation. -/
theorem cuspAffinePoint_zero_inversion (n : ℕ) (hn : 0 < n)
    (τ : UpperHalfPlane) :
    cuspAffinePoint n 0 hn (ModularGroup.S • τ) =
      ModularGroup.S • natDilation n hn τ := by
  apply UpperHalfPlane.ext
  simp only [cuspAffinePoint_coe, UpperHalfPlane.modular_S_smul,
    natDilation_coe]
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hnC, τ.ne_zero]
  ring

/-- Inversion sends the dilated point to the zero translate of the affine
Hecke orbit. -/
theorem natDilation_inversion (n : ℕ) (hn : 0 < n)
    (τ : UpperHalfPlane) :
    natDilation n hn (ModularGroup.S • τ) =
      ModularGroup.S • cuspAffinePoint n 0 hn τ := by
  apply UpperHalfPlane.ext
  simp only [natDilation_coe, UpperHalfPlane.modular_S_smul,
    cuspAffinePoint_coe]
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hnC, τ.ne_zero]
  ring

/-- The eta multiplier at the zero affine term after inversion is evaluated
at the dilated point. -/
theorem eta_cuspAffinePoint_zero_inversion (n : ℕ) (hn : 0 < n)
    (τ : UpperHalfPlane) :
    ModularForm.eta (cuspAffinePoint n 0 hn (ModularGroup.S • τ)) =
      Complex.I.sqrt⁻¹ * (natDilation n hn τ : ℂ).sqrt *
        ModularForm.eta (natDilation n hn τ) := by
  rw [cuspAffinePoint_zero_inversion, UpperHalfPlane.modular_S_smul]
  have harg : (-(natDilation n hn τ : ℂ))⁻¹ =
      -1 / (natDilation n hn τ : ℂ) := by
    field_simp [(natDilation n hn τ).ne_zero]
  change ModularForm.eta ((-(natDilation n hn τ : ℂ))⁻¹) = _
  rw [harg]
  exact eta_neg_inv (natDilation n hn τ).im_pos

/-- The eta multiplier at the dilated term after inversion is evaluated at
the zero affine point. -/
theorem eta_natDilation_inversion (n : ℕ) (hn : 0 < n)
    (τ : UpperHalfPlane) :
    ModularForm.eta (natDilation n hn (ModularGroup.S • τ)) =
      Complex.I.sqrt⁻¹ * (cuspAffinePoint n 0 hn τ : ℂ).sqrt *
        ModularForm.eta (cuspAffinePoint n 0 hn τ) := by
  rw [natDilation_inversion, UpperHalfPlane.modular_S_smul]
  have harg : (-(cuspAffinePoint n 0 hn τ : ℂ))⁻¹ =
      -1 / (cuspAffinePoint n 0 hn τ : ℂ) := by
    field_simp [(cuspAffinePoint n 0 hn τ).ne_zero]
  change ModularForm.eta ((-(cuspAffinePoint n 0 hn τ : ℂ))⁻¹) = _
  rw [harg]
  exact eta_neg_inv (cuspAffinePoint n 0 hn τ).im_pos

/-- The product of a realized inverse-eta row with eta is modular invariant.
This applies at the points exchanged by the zero affine and dilation terms. -/
theorem InverseEtaFourierForm.form_mul_eta_invariant
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (γ : GL (Fin 2) ℝ) (hγ : γ ∈ 𝒮ℒ) (τ : UpperHalfPlane) :
    row.form (γ • τ) * ModularForm.eta (γ • τ : UpperHalfPlane) =
      row.form τ * ModularForm.eta τ := by
  have hf := row.form.map_action γ hγ τ
  have he := etaAutomorphyFactor_mul_eta γ τ
  simp only [pow_zero, mul_one] at hf
  rw [hf, ← he]
  have hne := etaAutomorphyFactor_ne_zero γ τ
  field_simp [hne]

/-- A determinant-one inverse-index matrix identifies the invariant
inverse-eta product at the two affine Hecke points. -/
theorem InverseEtaFourierForm.affine_mul_eta_inversion
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (n j k : ℕ) (hn : 0 < n) (q : ℤ)
    (h : (n : ℤ) * q = (24 * j : ℤ) * (24 * k : ℤ) + 1)
    (τ : UpperHalfPlane) :
    row.form (cuspAffinePoint n k hn (ModularGroup.S • τ)) *
        ModularForm.eta (cuspAffinePoint n k hn (ModularGroup.S • τ)) =
      row.form (cuspAffinePoint n j hn τ) *
        ModularForm.eta (cuspAffinePoint n j hn τ) := by
  let γ := cuspAffineInversionMatrix n j k q h
  rw [← cuspAffinePoint_inversion_matrix n j k hn q h τ]
  exact (row.form_mul_eta_invariant
    (Matrix.SpecialLinearGroup.mapGL ℝ γ) ⟨γ, rfl⟩ _).symm

/-- The exact eta ratio in the pointwise affine inversion formula. It is
evaluated at the two affine points and must be retained when assembling the
full Hecke sum. -/
theorem InverseEtaFourierForm.affine_inversion_eta_ratio
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (n j k : ℕ) (hn : 0 < n) (q : ℤ)
    (h : (n : ℤ) * q = (24 * j : ℤ) * (24 * k : ℤ) + 1)
    (τ : UpperHalfPlane) :
    row.form (cuspAffinePoint n k hn (ModularGroup.S • τ)) =
      (ModularForm.eta (cuspAffinePoint n j hn τ) /
          ModularForm.eta (cuspAffinePoint n k hn (ModularGroup.S • τ))) *
        row.form (cuspAffinePoint n j hn τ) := by
  have h := row.affine_mul_eta_inversion n j k hn q h τ
  have hne := ModularForm.eta_ne_zero
    (cuspAffinePoint n k hn (ModularGroup.S • τ)).im_pos
  apply mul_right_cancel₀ hne
  calc
    _ = row.form (cuspAffinePoint n j hn τ) *
        ModularForm.eta (cuspAffinePoint n j hn τ) := h
    _ = _ := by field_simp [hne]

/-- The unit affine product transforms at the inverse index selected by the
finite permutation. -/
theorem InverseEtaFourierForm.affineUnit_mul_eta_inversion
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (n : ℕ) (hn : 0 < n) (h24 : IsUnit (24 : ZMod n))
    (k : CuspAffineUnitIndex n) (τ : UpperHalfPlane) :
    row.form (cuspAffinePoint n (k : Fin n) hn (ModularGroup.S • τ)) *
        ModularForm.eta (cuspAffinePoint n (k : Fin n) hn (ModularGroup.S • τ)) =
      row.form (cuspAffinePoint n
        (cuspAffineInverseIndex n hn h24 k : Fin n) hn τ) *
        ModularForm.eta (cuspAffinePoint n
          (cuspAffineInverseIndex n hn h24 k : Fin n) hn τ) := by
  obtain ⟨q, hq⟩ := cuspAffineInverseIndex_spec n hn h24 k
  exact row.affine_mul_eta_inversion n
    (cuspAffineInverseIndex n hn h24 k : Fin n) (k : Fin n) hn q hq τ

/-- The lower row of the affine inversion matrix evaluates to the same
inversion denominator at every affine point in its orbit. -/
theorem cuspAffineInversionMatrix_lower_factor (n k : ℕ) (hn : 0 < n)
    (τ : UpperHalfPlane) :
    (n : ℂ) * (cuspAffinePoint n k hn (ModularGroup.S • τ) : ℂ) -
        (24 * k : ℂ) = -1 / (τ : ℂ) := by
  rw [cuspAffinePoint_coe, UpperHalfPlane.modular_S_smul]
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hnC, τ.ne_zero]
  ring

/-- The ratio between multiplying a unit affine row by eta at its own
evaluation point and multiplying the whole row by eta at the base point.
The two factors are kept separate to expose their different origins. -/
noncomputable def affineUnitEtaInversionRatio
    (n : ℕ) (hn : 0 < n) (h24 : IsUnit (24 : ZMod n))
    (k : CuspAffineUnitIndex n) (τ : UpperHalfPlane) : ℂ :=
  (ModularForm.eta (cuspAffinePoint n
      (cuspAffineInverseIndex n hn h24 k : Fin n) hn τ) /
    ModularForm.eta (cuspAffinePoint n (k : Fin n) hn
      (ModularGroup.S • τ))) *
    (ModularForm.eta (ModularGroup.S • τ : UpperHalfPlane) /
      ModularForm.eta τ)

/-- An explicit eta law for the determinant-one affine inversion matrix
reduces the unit-orbit ratio to its phase and the principal root of `i`.
The law is an input for the actual eta function at every upper-half-plane
point; no Hecke conclusion is assumed. -/
theorem affineUnitEtaInversionRatio_of_matrix_law
    (n : ℕ) (hn : 0 < n) (h24 : IsUnit (24 : ZMod n))
    (k : CuspAffineUnitIndex n) (τ : UpperHalfPlane)
    (q : ℤ)
    (hq : (n : ℤ) * q =
      (24 * (cuspAffineInverseIndex n hn h24 k : Fin n).val : ℤ) *
        (24 * (k : Fin n).val : ℤ) + 1)
    (ε : ℂ)
    (hη : ∀ z : UpperHalfPlane,
      ModularForm.eta
          (cuspAffineInversionMatrix n
            (cuspAffineInverseIndex n hn h24 k : Fin n) (k : Fin n) q hq • z :
              UpperHalfPlane) =
        ε * ((n : ℂ) * z - (24 * (k : Fin n).val : ℂ)).sqrt *
          ModularForm.eta z) :
    affineUnitEtaInversionRatio n hn h24 k τ = ε * Complex.I.sqrt := by
  let z := cuspAffinePoint n (k : Fin n) hn (ModularGroup.S • τ)
  let x := cuspAffinePoint n
    (cuspAffineInverseIndex n hn h24 k : Fin n) hn τ
  have hpoint : cuspAffineInversionMatrix n
      (cuspAffineInverseIndex n hn h24 k : Fin n) (k : Fin n) q hq • z = x :=
    cuspAffinePoint_inversion_matrix n
      (cuspAffineInverseIndex n hn h24 k : Fin n) (k : Fin n) hn q hq τ
  have hfactor : (n : ℂ) * (z : ℂ) - (24 * (k : Fin n).val : ℂ) =
      -1 / (τ : ℂ) :=
    cuspAffineInversionMatrix_lower_factor n (k : Fin n) hn τ
  have hηpoint : ModularForm.eta x =
      ε * (-1 / (τ : ℂ)).sqrt * ModularForm.eta z := by
    simpa only [hpoint, hfactor] using hη z
  have hηS : ModularForm.eta (ModularGroup.S • τ : UpperHalfPlane) /
      ModularForm.eta τ = Complex.I.sqrt⁻¹ * (τ : ℂ).sqrt := by
    rw [UpperHalfPlane.modular_S_smul]
    have harg : (-(τ : ℂ))⁻¹ = -1 / (τ : ℂ) := by
      field_simp [τ.ne_zero]
    change ModularForm.eta ((-(τ : ℂ))⁻¹) /
      ModularForm.eta τ = _
    rw [harg]
    exact eta_inversion_factor τ
  have hroot := complex_sqrt_neg_inv_mul τ.im_pos
  have hIroot : Complex.I.sqrt ≠ 0 := by
    intro h
    have hs := complex_sqrt_sq Complex.I
    rw [h] at hs
    norm_num at hs
    exact Complex.I_ne_zero hs.symm
  have hI : Complex.I * Complex.I.sqrt⁻¹ = Complex.I.sqrt := by
    calc
      _ = Complex.I.sqrt ^ 2 * Complex.I.sqrt⁻¹ := by rw [complex_sqrt_sq]
      _ = Complex.I.sqrt := by field_simp [hIroot]
  calc
    affineUnitEtaInversionRatio n hn h24 k τ =
        (ModularForm.eta x / ModularForm.eta z) *
          (ModularForm.eta (ModularGroup.S • τ : UpperHalfPlane) /
            ModularForm.eta τ) := rfl
    _ = (ε * (-1 / (τ : ℂ)).sqrt) *
        (Complex.I.sqrt⁻¹ * (τ : ℂ).sqrt) := by
          rw [hηpoint, hηS]
          field_simp [ModularForm.eta_ne_zero z.im_pos]
    _ = ε * (Complex.I * Complex.I.sqrt⁻¹) := by
          calc
            _ = ε * ((-1 / (τ : ℂ)).sqrt * (τ : ℂ).sqrt) *
                Complex.I.sqrt⁻¹ := by ring
            _ = ε * (Complex.I * Complex.I.sqrt⁻¹) := by rw [hroot]; ring
    _ = ε * Complex.I.sqrt := by rw [hI]

/-- A unit affine term multiplied by the global eta factor transforms with
the explicit eta ratio, rather than by the unweighted affine permutation. -/
theorem InverseEtaFourierForm.affineUnit_globalEta_inversion
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (n : ℕ) (hn : 0 < n) (h24 : IsUnit (24 : ZMod n))
    (k : CuspAffineUnitIndex n) (τ : UpperHalfPlane) :
    row.form (cuspAffinePoint n (k : Fin n) hn (ModularGroup.S • τ)) *
        ModularForm.eta (ModularGroup.S • τ : UpperHalfPlane) =
      affineUnitEtaInversionRatio n hn h24 k τ *
        (row.form (cuspAffinePoint n
          (cuspAffineInverseIndex n hn h24 k : Fin n) hn τ) *
          ModularForm.eta τ) := by
  obtain ⟨q, hq⟩ := cuspAffineInverseIndex_spec n hn h24 k
  rw [row.affine_inversion_eta_ratio n
    (cuspAffineInverseIndex n hn h24 k : Fin n) (k : Fin n) hn q hq τ]
  unfold affineUnitEtaInversionRatio
  have hne := ModularForm.eta_ne_zero τ.im_pos
  field_simp [hne]

/-- Under inversion the unit affine orbit is reindexed by the inverse-index
permutation, with its exact global-eta multiplier attached to each term. -/
theorem InverseEtaFourierForm.affineUnitSum_globalEta_inversion
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (n : ℕ) (hn : 0 < n) (h24 : IsUnit (24 : ZMod n))
    (τ : UpperHalfPlane) :
    (∑ k : CuspAffineUnitIndex n,
      row.form (cuspAffinePoint n (k : Fin n) hn (ModularGroup.S • τ)) *
        ModularForm.eta (ModularGroup.S • τ : UpperHalfPlane)) =
      ∑ j : CuspAffineUnitIndex n,
        affineUnitEtaInversionRatio n hn h24
          (cuspAffineInverseIndex n hn h24 j) τ *
          (row.form (cuspAffinePoint n (j : Fin n) hn τ) *
            ModularForm.eta τ) := by
  classical
  let inv := cuspAffineInverseIndex n hn h24
  let F : CuspAffineUnitIndex n → ℂ := fun j =>
    affineUnitEtaInversionRatio n hn h24 (inv j) τ *
      (row.form (cuspAffinePoint n (j : Fin n) hn τ) *
        ModularForm.eta τ)
  calc
    _ = ∑ k : CuspAffineUnitIndex n,
        affineUnitEtaInversionRatio n hn h24 k τ *
          (row.form (cuspAffinePoint n (inv k : Fin n) hn τ) *
            ModularForm.eta τ) := by
      apply Finset.sum_congr rfl
      intro k _
      exact row.affineUnit_globalEta_inversion n hn h24 k τ
    _ = ∑ k : CuspAffineUnitIndex n, F (inv k) := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [F, inv, cuspAffineInverseIndex_involutive]
      rw [(cuspAffineInverseIndex_involutive n hn h24) k]
    _ = ∑ k : CuspAffineUnitIndex n, F k := by
      apply Finset.sum_bij (fun k _ => inv k)
      · intro k _
        exact Finset.mem_univ _
      · intro k₁ _ k₂ _ heq
        exact (cuspAffineInverseIndex_involutive n hn h24).injective heq
      · intro k _
        exact ⟨inv k, Finset.mem_univ _,
          cuspAffineInverseIndex_involutive n hn h24 k⟩
      · intro k _
        rfl
    _ = _ := rfl

/-- The all-points eta laws for the affine inversion matrices turn the exact
unit-orbit ratios into explicit phases. The phase may depend on the affine
index; this identity makes that dependence visible in the Hecke sum. -/
theorem InverseEtaFourierForm.affineUnitSum_globalEta_of_matrix_laws
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (n : ℕ) (hn : 0 < n) (h24 : IsUnit (24 : ZMod n))
    (τ : UpperHalfPlane) (ε : CuspAffineUnitIndex n → ℂ)
    (hη : ∀ (k : CuspAffineUnitIndex n) (q : ℤ)
      (hq : (n : ℤ) * q =
        (24 * (cuspAffineInverseIndex n hn h24 k : Fin n).val : ℤ) *
          (24 * (k : Fin n).val : ℤ) + 1) (z : UpperHalfPlane),
      ModularForm.eta
          (cuspAffineInversionMatrix n
            (cuspAffineInverseIndex n hn h24 k : Fin n) (k : Fin n) q hq • z :
              UpperHalfPlane) =
        ε k * ((n : ℂ) * z - (24 * (k : Fin n).val : ℂ)).sqrt *
          ModularForm.eta z) :
    (∑ k : CuspAffineUnitIndex n,
      row.form (cuspAffinePoint n (k : Fin n) hn (ModularGroup.S • τ)) *
        ModularForm.eta (ModularGroup.S • τ : UpperHalfPlane)) =
      ∑ j : CuspAffineUnitIndex n,
        (ε (cuspAffineInverseIndex n hn h24 j) * Complex.I.sqrt) *
          (row.form (cuspAffinePoint n (j : Fin n) hn τ) *
            ModularForm.eta τ) := by
  rw [row.affineUnitSum_globalEta_inversion n hn h24 τ]
  apply Finset.sum_congr rfl
  intro j _
  let k := cuspAffineInverseIndex n hn h24 j
  obtain ⟨q, hq⟩ := cuspAffineInverseIndex_spec n hn h24 k
  have hratio := affineUnitEtaInversionRatio_of_matrix_law n hn h24 k τ q hq
    (ε k) (hη k q hq)
  simpa only [k, hratio]

/-- The phase of a unit affine matrix, using its uniquely determined integer
quotient in the determinant-one identity. -/
noncomputable def cuspAffineUnitEtaPhase (n : ℕ) (hn : 0 < n)
    (h24 : IsUnit (24 : ZMod n)) (k : CuspAffineUnitIndex n) : ℂ :=
  etaOddMatrixPhase
    (24 * (cuspAffineInverseIndex n hn h24 k : Fin n).val)
    (-(Classical.choose (cuspAffineInverseIndex_spec n hn h24 k)))
    n (-(24 * (k : Fin n).val))

/-- The phase is independent of the witness used for the determinant-one
quotient. -/
theorem cuspAffineUnitEtaPhase_eq (n : ℕ) (hn : 0 < n)
    (h24 : IsUnit (24 : ZMod n)) (k : CuspAffineUnitIndex n)
    (q : ℤ)
    (hq : (n : ℤ) * q =
      (24 * (cuspAffineInverseIndex n hn h24 k : Fin n).val : ℤ) *
        (24 * (k : Fin n).val : ℤ) + 1) :
    cuspAffineUnitEtaPhase n hn h24 k =
      etaOddMatrixPhase
        (24 * (cuspAffineInverseIndex n hn h24 k : Fin n).val)
        (-q) n (-(24 * (k : Fin n).val)) := by
  let q₀ := Classical.choose (cuspAffineInverseIndex_spec n hn h24 k)
  have hq₀ : (n : ℤ) * q₀ =
      (24 * (cuspAffineInverseIndex n hn h24 k : Fin n).val : ℤ) *
        (24 * (k : Fin n).val : ℤ) + 1 :=
    Classical.choose_spec (cuspAffineInverseIndex_spec n hn h24 k)
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hqeq : q = q₀ := mul_left_cancel₀ hn0 (hq.trans hq₀.symm)
  change etaOddMatrixPhase
      (24 * (cuspAffineInverseIndex n hn h24 k : Fin n).val)
      (-q₀) n (-(24 * (k : Fin n).val)) = _
  rw [← hqeq]

/-- The unit affine phase is the Jacobi character of its original index
times one factor depending only on the width. -/
theorem cuspAffineUnitEtaPhase_eq_jacobi (n : ℕ) (hn : 0 < n)
    (h24 : IsUnit (24 : ZMod n)) (k : CuspAffineUnitIndex n) :
    cuspAffineUnitEtaPhase n hn h24 k =
      (jacobiSym (-(24 * ((k : Fin n).val : ℤ))) n : ℂ) *
        Complex.exp (-Real.pi * Complex.I * (n : ℂ) / 4) := by
  unfold cuspAffineUnitEtaPhase
  exact etaOddMatrixPhase_affine n
    (cuspAffineInverseIndex n hn h24 k : Fin n).val (k : Fin n).val
    (Classical.choose (cuspAffineInverseIndex_spec n hn h24 k))

/-- At a prime width, the Jacobi factor is the quadratic cusp weight times
one scalar independent of the affine index. -/
theorem cuspAffineUnitEtaPhase_eq_quadraticCuspWeight
    (p : ℕ) [Fact p.Prime] (h24 : IsUnit (24 : ZMod p))
    (k : CuspAffineUnitIndex p) :
    cuspAffineUnitEtaPhase p (Fact.out : p.Prime).pos h24 k =
      (jacobiSym (-24) p : ℂ) *
        quadraticCuspWeight p (k : Fin p).val *
          Complex.exp (-Real.pi * Complex.I * (p : ℂ) / 4) := by
  rw [cuspAffineUnitEtaPhase_eq_jacobi]
  have hchar :
      jacobiSym (-(24 * ((k : Fin p).val : ℤ))) p =
        jacobiSym (-24) p *
          quadraticChar (ZMod p) (((k : Fin p).val : ℕ) : ZMod p) := by
    rw [← jacobiSym.legendreSym.to_jacobiSym,
      ← jacobiSym.legendreSym.to_jacobiSym]
    change quadraticChar (ZMod p)
        ((-(24 * ((k : Fin p).val : ℤ)) : ℤ) : ZMod p) =
      quadraticChar (ZMod p) ((-24 : ℤ) : ZMod p) *
        quadraticChar (ZMod p) (((k : Fin p).val : ℕ) : ZMod p)
    rw [show (-(24 * ((k : Fin p).val : ℤ)) : ℤ) =
        (-24 : ℤ) * (k : Fin p).val by ring]
    simp only [Int.cast_mul, Int.cast_natCast, map_mul]
  rw [hchar]
  simp only [quadraticCuspWeight_eq_character, Int.cast_mul]

/-- The unit affine orbit under inversion, with the actual classical eta
matrix phase. The only analytic input is the admitted odd-denominator eta
transformation law [apostol1990, Chapter 3]. -/
theorem InverseEtaFourierForm.affineUnitSum_globalEta_of_odd_matrix_law
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (n : ℕ) (hn : 0 < n) (hodd : (n : ℤ) % 2 = 1)
    (h24 : IsUnit (24 : ZMod n)) (τ : UpperHalfPlane) :
    (∑ k : CuspAffineUnitIndex n,
      row.form (cuspAffinePoint n (k : Fin n) hn (ModularGroup.S • τ)) *
        ModularForm.eta (ModularGroup.S • τ : UpperHalfPlane)) =
      ∑ j : CuspAffineUnitIndex n,
        (cuspAffineUnitEtaPhase n hn h24
            (cuspAffineInverseIndex n hn h24 j) * Complex.I.sqrt) *
          (row.form (cuspAffinePoint n (j : Fin n) hn τ) *
            ModularForm.eta τ) := by
  apply row.affineUnitSum_globalEta_of_matrix_laws n hn h24 τ
    (cuspAffineUnitEtaPhase n hn h24)
  intro k q hq z
  rw [cuspAffineUnitEtaPhase_eq n hn h24 k q hq]
  exact cuspAffineInversionMatrix_eta_law n
    (cuspAffineInverseIndex n hn h24 k : Fin n).val (k : Fin n).val
    hn hodd q hq z

/-- The unit orbit inversion with the eta phase reduced to a Jacobi symbol.
The resulting index dependence is the quadratic weight needed in the
middle-row Hecke comparison. -/
theorem InverseEtaFourierForm.affineUnitSum_globalEta_jacobi
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (n : ℕ) (hn : 0 < n) (hodd : (n : ℤ) % 2 = 1)
    (h24 : IsUnit (24 : ZMod n)) (τ : UpperHalfPlane) :
    (∑ k : CuspAffineUnitIndex n,
      row.form (cuspAffinePoint n (k : Fin n) hn (ModularGroup.S • τ)) *
        ModularForm.eta (ModularGroup.S • τ : UpperHalfPlane)) =
      ∑ j : CuspAffineUnitIndex n,
        (((jacobiSym (-(24 *
            (((cuspAffineInverseIndex n hn h24 j : Fin n).val) : ℤ))) n : ℂ) *
              Complex.exp (-Real.pi * Complex.I * (n : ℂ) / 4)) *
                Complex.I.sqrt) *
          (row.form (cuspAffinePoint n (j : Fin n) hn τ) *
            ModularForm.eta τ) := by
  rw [row.affineUnitSum_globalEta_of_odd_matrix_law n hn hodd h24 τ]
  apply Finset.sum_congr rfl
  intro j _
  rw [cuspAffineUnitEtaPhase_eq_jacobi]

/-- The eta exponential at an odd square width cancels the inversion
square-root phase. This is the scalar needed for the primitive part of a
prime-square affine orbit. -/
theorem oddSquare_eta_phase (n : ℕ) (hodd : n % 2 = 1) :
    Complex.exp (-Real.pi * Complex.I * ((n * n : ℕ) : ℂ) / 4) *
      Complex.I.sqrt = 1 := by
  have hmod : (n * n) % 8 = 1 := by
    have hcases : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
      omega
    rcases hcases with h | h | h | h <;> simp [Nat.mul_mod, h]
  let t := (n * n - 1) / 8
  have hn : n * n = 8 * t + 1 := by
    dsimp [t]
    omega
  have hnC : ((n * n : ℕ) : ℂ) = 8 * (t : ℂ) + 1 := by
    exact_mod_cast hn
  rw [hnC]
  have harg : -Real.pi * Complex.I * (8 * (t : ℂ) + 1) / 4 =
      -(Real.pi / 4) * Complex.I -
        2 * Real.pi * Complex.I * (t : ℂ) := by ring
  rw [harg, Complex.exp_sub]
  have hperiod : Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)) = 1 := by
    convert Complex.exp_int_mul_two_pi_mul_I (t : ℤ) using 1 <;>
      simp only [Int.cast_natCast] <;> ring_nf
  rw [hperiod, div_one, ← Theta.eta_inversion_phase]
  have hroot : Complex.I.sqrt ≠ 0 := by
    intro h
    have hs := complex_sqrt_sq Complex.I
    rw [h] at hs
    norm_num at hs
    exact Complex.I_ne_zero hs.symm
  exact inv_mul_cancel₀ hroot

/-- A Jacobi symbol with square modulus is one when its numerator is
coprime to the base modulus. -/
theorem jacobiSym_square_of_coprime (a : ℤ) (n : ℕ)
    (ha : a.gcd (n : ℤ) = 1) : jacobiSym a (n * n) = 1 := by
  rw [show n * n = n ^ 2 by ring, jacobiSym.pow_right]
  rcases jacobiSym.eq_one_or_neg_one ha with h | h <;>
    rw [h] <;> norm_num

/-- The affine eta Jacobi factor is one at a square cusp width when the
index and 24 are units there. -/
theorem cuspAffineUnitJacobi_square (n : ℕ)
    (h24 : IsUnit (24 : ZMod (n * n)))
    (k : CuspAffineUnitIndex (n * n)) :
    jacobiSym (-(24 * (((k : Fin (n * n)).val) : ℤ))) (n * n) = 1 := by
  have h24cop : (24 : ℕ).Coprime (n * n) :=
    (ZMod.isUnit_iff_coprime 24 (n * n)).mp h24
  have hkcop : ((k : Fin (n * n)).val).Coprime (n * n) :=
    (ZMod.isUnit_iff_coprime _ (n * n)).mp k.property
  have hdvd : n ∣ n * n := ⟨n, rfl⟩
  have hcop : (24 * ((k : Fin (n * n)).val)).Coprime n :=
    (h24cop.of_dvd_right hdvd).mul_left (hkcop.of_dvd_right hdvd)
  have hgcd : (-(24 * (((k : Fin (n * n)).val) : ℤ))).gcd (n : ℤ) = 1 := by
    simpa [Int.gcd_eq_natAbs, Int.natAbs_neg, Int.natAbs_mul,
      Nat.Coprime] using hcop
  exact jacobiSym_square_of_coprime _ n hgcd

/-- Inversion fixes the unit part of the square-width affine orbit after
attaching eta at the base point. The odd-matrix eta law supplies the analytic
transformation; the Jacobi and exponential phases cancel at square width. -/
theorem InverseEtaFourierForm.affineUnitSquareSum_globalEta_inversion
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (n : ℕ) (hn : 0 < n) (hodd : (n : ℤ) % 2 = 1)
    (h24 : IsUnit (24 : ZMod (n * n))) (τ : UpperHalfPlane) :
    (∑ k : CuspAffineUnitIndex (n * n),
      row.form (cuspAffinePoint (n * n) (k : Fin (n * n))
          (Nat.mul_pos hn hn) (ModularGroup.S • τ)) *
        ModularForm.eta (ModularGroup.S • τ : UpperHalfPlane)) =
      ∑ j : CuspAffineUnitIndex (n * n),
        row.form (cuspAffinePoint (n * n) (j : Fin (n * n))
            (Nat.mul_pos hn hn) τ) * ModularForm.eta τ := by
  have hoddN : n % 2 = 1 := by exact_mod_cast hodd
  have hoddSqN : (n * n) % 2 = 1 := by
    simp [Nat.mul_mod, hoddN]
  have hoddSq : (((n * n : ℕ) : ℤ) % 2) = 1 := by
    exact_mod_cast hoddSqN
  rw [row.affineUnitSum_globalEta_jacobi (n * n)
    (Nat.mul_pos hn hn) hoddSq h24 τ]
  apply Finset.sum_congr rfl
  intro j _
  rw [cuspAffineUnitJacobi_square n h24
    (cuspAffineInverseIndex (n * n) (Nat.mul_pos hn hn) h24 j)]
  simp only [Int.cast_one, one_mul, oddSquare_eta_phase n hoddN, one_mul]

/-- The primitive indices in a prime-square affine Hecke orbit are fixed
under inversion after attaching eta at the base point. This converts the
unit-index result into the range indexing of the actual Hecke expression. -/
theorem InverseEtaFourierForm.affineNondivisibleSquareSum_globalEta_inversion
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (p : ℕ) (hp : p.Prime) (hodd : (p : ℤ) % 2 = 1)
    (h24 : IsUnit (24 : ZMod (p * p))) (τ : UpperHalfPlane) :
    (∑ j ∈ (Finset.range (p * p)).filter (¬ p ∣ ·),
      row.form (cuspAffinePoint (p * p) j
          (Nat.mul_pos hp.pos hp.pos) (ModularGroup.S • τ)) *
        ModularForm.eta (ModularGroup.S • τ : UpperHalfPlane)) =
      ∑ j ∈ (Finset.range (p * p)).filter (¬ p ∣ ·),
        row.form (cuspAffinePoint (p * p) j
            (Nat.mul_pos hp.pos hp.pos) τ) * ModularForm.eta τ := by
  rw [sum_nondivisible_primeSquare_eq_unit p hp,
    sum_nondivisible_primeSquare_eq_unit p hp]
  exact row.affineUnitSquareSum_globalEta_inversion p hp.pos hodd h24 τ

/-- The scalar left after the prime affine indices acquire their quadratic
weights. It is independent of the Hecke orbit index. -/
noncomputable def primeAffineEtaScalar (p : ℕ) [Fact p.Prime] : ℂ :=
  (jacobiSym (-24) p : ℂ) *
    ((quadraticChar (ZMod p) (-1) : ℤ) : ℂ) *
      Complex.exp (-Real.pi * Complex.I * (p : ℂ) / 4) * Complex.I.sqrt

/-- The exact eta scalar contributed by the affine unit orbit. -/
theorem primeAffineEtaScalar_eq (p : ℕ) [Fact p.Prime] :
    primeAffineEtaScalar p =
      (jacobiSym (-24) p : ℂ) *
        ((quadraticChar (ZMod p) (-1) : ℤ) : ℂ) *
          Complex.exp (-Real.pi * Complex.I * (p : ℂ) / 4) * Complex.I.sqrt :=
  (rfl)

/-- Under inversion, the unit affine orbit acquires exactly the quadratic
weight of the middle Hecke row, with a common eta scalar. This uses the admitted
general eta transformation law [apostol1990, Chapter 3]. -/
theorem InverseEtaFourierForm.affineUnitSum_globalEta_quadratic
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (p : ℕ) [Fact p.Prime] (hodd : (p : ℤ) % 2 = 1)
    (h24 : IsUnit (24 : ZMod p)) (τ : UpperHalfPlane) :
    (∑ k : CuspAffineUnitIndex p,
      row.form (cuspAffinePoint p (k : Fin p) (Fact.out : p.Prime).pos
          (ModularGroup.S • τ)) *
        ModularForm.eta (ModularGroup.S • τ : UpperHalfPlane)) =
      primeAffineEtaScalar p *
        ∑ j : CuspAffineUnitIndex p,
          quadraticCuspWeight p (j : Fin p).val *
            (row.form (cuspAffinePoint p (j : Fin p)
                (Fact.out : p.Prime).pos τ) * ModularForm.eta τ) := by
  rw [row.affineUnitSum_globalEta_of_odd_matrix_law p
    (Fact.out : p.Prime).pos hodd h24 τ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [cuspAffineUnitEtaPhase_eq_quadraticCuspWeight,
    quadraticCuspWeight_inverseIndex]
  unfold primeAffineEtaScalar
  ring

/-- The sum of unit affine products is invariant under inversion. The finite
permutation handles the reindexing; eta multipliers remain attached to their
individual evaluation points. -/
theorem InverseEtaFourierForm.affineUnitSum_mul_eta_inversion
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (n : ℕ) (hn : 0 < n) (h24 : IsUnit (24 : ZMod n))
    (τ : UpperHalfPlane) :
    (∑ k : CuspAffineUnitIndex n,
      row.form (cuspAffinePoint n (k : Fin n) hn (ModularGroup.S • τ)) *
        ModularForm.eta (cuspAffinePoint n (k : Fin n) hn
          (ModularGroup.S • τ))) =
    ∑ k : CuspAffineUnitIndex n,
      row.form (cuspAffinePoint n (k : Fin n) hn τ) *
        ModularForm.eta (cuspAffinePoint n (k : Fin n) hn τ) := by
  classical
  let F : CuspAffineUnitIndex n → ℂ := fun k =>
    row.form (cuspAffinePoint n (k : Fin n) hn τ) *
      ModularForm.eta (cuspAffinePoint n (k : Fin n) hn τ)
  calc
    _ = ∑ k : CuspAffineUnitIndex n,
        F (cuspAffineInverseIndex n hn h24 k) := by
      apply Finset.sum_congr rfl
      intro k _
      exact row.affineUnit_mul_eta_inversion n hn h24 k τ
    _ = ∑ k : CuspAffineUnitIndex n, F k := by
      apply Finset.sum_bij (fun k _ => cuspAffineInverseIndex n hn h24 k)
      · intro k _
        exact Finset.mem_univ _
      · intro k₁ _ k₂ _ heq
        exact (cuspAffineInverseIndex_involutive n hn h24).injective heq
      · intro k _
        exact ⟨cuspAffineInverseIndex n hn h24 k, Finset.mem_univ _,
          cuspAffineInverseIndex_involutive n hn h24 k⟩
      · intro k _
        rfl
    _ = _ := rfl

/-- A weighted unit affine orbit carries its weights through the inverse-index
permutation. This is the form needed for the quadratic middle row. -/
theorem InverseEtaFourierForm.affineUnitWeightedSum_mul_eta_inversion
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (n : ℕ) (hn : 0 < n) (h24 : IsUnit (24 : ZMod n))
    (w : CuspAffineUnitIndex n → ℂ) (τ : UpperHalfPlane) :
    (∑ k : CuspAffineUnitIndex n,
      w k * (row.form (cuspAffinePoint n (k : Fin n) hn
            (ModularGroup.S • τ)) *
          ModularForm.eta (cuspAffinePoint n (k : Fin n) hn
            (ModularGroup.S • τ)))) =
      ∑ j : CuspAffineUnitIndex n,
        w (cuspAffineInverseIndex n hn h24 j) *
          (row.form (cuspAffinePoint n (j : Fin n) hn τ) *
            ModularForm.eta (cuspAffinePoint n (j : Fin n) hn τ)) := by
  classical
  let inv := cuspAffineInverseIndex n hn h24
  let F : CuspAffineUnitIndex n → ℂ := fun j =>
    w (inv j) *
      (row.form (cuspAffinePoint n (j : Fin n) hn τ) *
        ModularForm.eta (cuspAffinePoint n (j : Fin n) hn τ))
  calc
    _ = ∑ k : CuspAffineUnitIndex n, F (inv k) := by
      apply Finset.sum_congr rfl
      intro k _
      simpa only [F, inv, (cuspAffineInverseIndex_involutive n hn h24) k] using
        congrArg (fun z : ℂ => w k * z)
          (row.affineUnit_mul_eta_inversion n hn h24 k τ)
    _ = ∑ j : CuspAffineUnitIndex n, F j := by
      apply Finset.sum_bij (fun k _ => inv k)
      · intro k _
        exact Finset.mem_univ _
      · intro k₁ _ k₂ _ heq
        exact (cuspAffineInverseIndex_involutive n hn h24).injective heq
      · intro k _
        exact ⟨inv k, Finset.mem_univ _,
          cuspAffineInverseIndex_involutive n hn h24 k⟩
      · intro k _
        rfl
    _ = _ := rfl

/-- In the square-width affine orbit, indices divisible by the width and
primitive after division invert to the fractional translates in the middle
row. Eta is evaluated at each point; this identity does not discard the
global eta ratios of the prime Hecke expression. -/
theorem InverseEtaFourierForm.divisibleUnitSquareSum_mul_eta_inversion
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (n : ℕ) (hn : 0 < n) (h24 : IsUnit (24 : ZMod n))
    (τ : UpperHalfPlane) :
    (∑ k : CuspAffineUnitIndex n,
      row.form (cuspAffinePoint (n * n) (n * (k : Fin n).val)
          (Nat.mul_pos hn hn) (ModularGroup.S • τ)) *
        ModularForm.eta (cuspAffinePoint (n * n) (n * (k : Fin n).val)
          (Nat.mul_pos hn hn) (ModularGroup.S • τ))) =
      ∑ k : CuspAffineUnitIndex n,
        row.form (cuspFractionTranslate n (k : Fin n).val hn τ) *
          ModularForm.eta (cuspFractionTranslate n (k : Fin n).val hn τ) := by
  calc
    _ = ∑ k : CuspAffineUnitIndex n,
        row.form (cuspAffinePoint n (k : Fin n).val hn
            (ModularGroup.S • natDilation n hn τ)) *
          ModularForm.eta (cuspAffinePoint n (k : Fin n).val hn
            (ModularGroup.S • natDilation n hn τ)) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [cuspAffinePoint_square_mul_inversion]
    _ = ∑ k : CuspAffineUnitIndex n,
        row.form (cuspAffinePoint n (k : Fin n).val hn
            (natDilation n hn τ)) *
          ModularForm.eta (cuspAffinePoint n (k : Fin n).val hn
            (natDilation n hn τ)) :=
      row.affineUnitSum_mul_eta_inversion n hn h24 (natDilation n hn τ)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [cuspAffinePoint_dilation_eq_fractionTranslate]

/-- The divisible square-width orbit carries an arbitrary unit-index weight
to the quadratic middle-row points. The inverse-index permutation also acts
on the weight. -/
theorem InverseEtaFourierForm.divisibleUnitSquareWeightedSum_mul_eta_inversion
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (n : ℕ) (hn : 0 < n) (h24 : IsUnit (24 : ZMod n))
    (w : CuspAffineUnitIndex n → ℂ) (τ : UpperHalfPlane) :
    (∑ k : CuspAffineUnitIndex n,
      w k * (row.form (cuspAffinePoint (n * n) (n * (k : Fin n).val)
            (Nat.mul_pos hn hn) (ModularGroup.S • τ)) *
          ModularForm.eta (cuspAffinePoint (n * n) (n * (k : Fin n).val)
            (Nat.mul_pos hn hn) (ModularGroup.S • τ)))) =
      ∑ j : CuspAffineUnitIndex n,
        w (cuspAffineInverseIndex n hn h24 j) *
          (row.form (cuspFractionTranslate n (j : Fin n).val hn τ) *
            ModularForm.eta (cuspFractionTranslate n (j : Fin n).val hn τ)) := by
  calc
    _ = ∑ k : CuspAffineUnitIndex n,
        w k * (row.form (cuspAffinePoint n (k : Fin n).val hn
              (ModularGroup.S • natDilation n hn τ)) *
            ModularForm.eta (cuspAffinePoint n (k : Fin n).val hn
              (ModularGroup.S • natDilation n hn τ))) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [cuspAffinePoint_square_mul_inversion]
    _ = ∑ j : CuspAffineUnitIndex n,
        w (cuspAffineInverseIndex n hn h24 j) *
          (row.form (cuspAffinePoint n (j : Fin n).val hn
              (natDilation n hn τ)) *
            ModularForm.eta (cuspAffinePoint n (j : Fin n).val hn
              (natDilation n hn τ))) :=
      row.affineUnitWeightedSum_mul_eta_inversion n hn h24 w
        (natDilation n hn τ)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [cuspAffinePoint_dilation_eq_fractionTranslate]

/-- On the quadratic middle orbit, inversion of the divisible square-width
affine terms contributes exactly the character value at `-1`. Each eta
factor remains at its own cusp point. -/
theorem InverseEtaFourierForm.divisibleUnitSquareQuadraticSum_mul_eta_inversion
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (p : ℕ) [Fact p.Prime] (h24 : IsUnit (24 : ZMod p))
    (τ : UpperHalfPlane) :
    (∑ k : CuspAffineUnitIndex p,
      quadraticCuspWeight p (k : Fin p).val *
        (row.form (cuspAffinePoint (p * p) (p * (k : Fin p).val)
              (Nat.mul_pos (Fact.out : p.Prime).pos (Fact.out : p.Prime).pos)
              (ModularGroup.S • τ)) *
          ModularForm.eta (cuspAffinePoint (p * p) (p * (k : Fin p).val)
              (Nat.mul_pos (Fact.out : p.Prime).pos (Fact.out : p.Prime).pos)
              (ModularGroup.S • τ)))) =
      ((quadraticChar (ZMod p) (-1) : ℤ) : ℂ) *
        ∑ j : CuspAffineUnitIndex p,
          quadraticCuspWeight p (j : Fin p).val *
            (row.form (cuspFractionTranslate p (j : Fin p).val
                  (Fact.out : p.Prime).pos τ) *
              ModularForm.eta (cuspFractionTranslate p (j : Fin p).val
                  (Fact.out : p.Prime).pos τ)) := by
  rw [row.divisibleUnitSquareWeightedSum_mul_eta_inversion p
    (Fact.out : p.Prime).pos h24
    (fun k => quadraticCuspWeight p (k : Fin p).val) τ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [quadraticCuspWeight_inverseIndex p h24 j]
  ring

/-- The eta inversion factors at a point and its positive dilation differ
by the positive square root of the dilation width. -/
theorem eta_dilation_inversion_scale (n : ℕ) (hn : 0 < n)
    (τ : UpperHalfPlane) :
    (((Real.sqrt n : ℝ) : ℂ) *
        ModularForm.eta (ModularGroup.S • τ : UpperHalfPlane)) *
        ModularForm.eta (natDilation n hn τ) =
      ModularForm.eta
          (ModularGroup.S • natDilation n hn τ : UpperHalfPlane) *
        ModularForm.eta τ := by
  have hS (z : UpperHalfPlane) :
      ModularForm.eta (ModularGroup.S • z : UpperHalfPlane) =
        Complex.I.sqrt⁻¹ * (z : ℂ).sqrt * ModularForm.eta z := by
    rw [UpperHalfPlane.modular_S_smul]
    have harg : (-(z : ℂ))⁻¹ = -1 / (z : ℂ) := by
      field_simp [z.ne_zero]
    change ModularForm.eta ((-(z : ℂ))⁻¹) = _
    rw [harg]
    exact eta_neg_inv z.im_pos
  rw [hS τ, hS (natDilation n hn τ), natDilation_coe,
    complex_sqrt_nat_mul n hn τ.im_pos]
  ring

/-- The nonzero indices divisible by `p` in the square-width affine orbit
transform into the quadratic middle orbit. The common factor is the affine
eta phase divided by the positive square root of `p`. -/
theorem InverseEtaFourierForm.divisibleUnitSquareSum_globalEta_quadratic
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (p : ℕ) [Fact p.Prime] (hodd : (p : ℤ) % 2 = 1)
    (h24 : IsUnit (24 : ZMod p)) (τ : UpperHalfPlane) :
    (∑ k : CuspAffineUnitIndex p,
      row.form (cuspAffinePoint (p * p) (p * (k : Fin p).val)
          (Nat.mul_pos (Fact.out : p.Prime).pos (Fact.out : p.Prime).pos)
          (ModularGroup.S • τ)) *
        ModularForm.eta (ModularGroup.S • τ : UpperHalfPlane)) =
      ((((Real.sqrt p : ℝ) : ℂ)⁻¹) * primeAffineEtaScalar p) *
        ∑ j : CuspAffineUnitIndex p,
          quadraticCuspWeight p (j : Fin p).val *
            (row.form (cuspFractionTranslate p (j : Fin p).val
                  (Fact.out : p.Prime).pos τ) * ModularForm.eta τ) := by
  let hp := (Fact.out : p.Prime)
  let E := ModularForm.eta
    (ModularGroup.S • natDilation p hp.pos τ : UpperHalfPlane)
  let D := ModularForm.eta (natDilation p hp.pos τ)
  let S := ModularForm.eta (ModularGroup.S • τ : UpperHalfPlane)
  let T := ModularForm.eta τ
  let r : ℂ := ((Real.sqrt p : ℝ) : ℂ)
  let X : ℂ := ∑ k : CuspAffineUnitIndex p,
    row.form (cuspAffinePoint (p * p) (p * (k : Fin p).val)
        (Nat.mul_pos hp.pos hp.pos) (ModularGroup.S • τ))
  let Y : ℂ := ∑ j : CuspAffineUnitIndex p,
    quadraticCuspWeight p (j : Fin p).val *
      row.form (cuspFractionTranslate p (j : Fin p).val hp.pos τ)
  have hstep : X * E = primeAffineEtaScalar p * (Y * D) := by
    calc
      X * E = ∑ k : CuspAffineUnitIndex p,
          row.form (cuspAffinePoint p (k : Fin p).val hp.pos
              (ModularGroup.S • natDilation p hp.pos τ)) * E := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _
        rw [cuspAffinePoint_square_mul_inversion]
      _ = primeAffineEtaScalar p *
          ∑ j : CuspAffineUnitIndex p,
            quadraticCuspWeight p (j : Fin p).val *
              (row.form (cuspAffinePoint p (j : Fin p).val hp.pos
                    (natDilation p hp.pos τ)) * D) := by
        exact row.affineUnitSum_globalEta_quadratic p hodd h24
          (natDilation p hp.pos τ)
      _ = primeAffineEtaScalar p * (Y * D) := by
        rw [Finset.sum_mul]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        rw [cuspAffinePoint_dilation_eq_fractionTranslate]
        ring
  have hscale : (r * S) * D = E * T :=
    eta_dilation_inversion_scale p hp.pos τ
  have hrpos : 0 < Real.sqrt (p : ℝ) :=
    Real.sqrt_pos.2 (Nat.cast_pos.mpr hp.pos)
  have hr : r ≠ 0 := by
    dsimp [r]
    exact_mod_cast hrpos.ne'
  have hD : D ≠ 0 := ModularForm.eta_ne_zero
    (natDilation p hp.pos τ).im_pos
  have hratio : S * D = r⁻¹ * (E * T) := by
    calc
      S * D = r⁻¹ * ((r * S) * D) := by field_simp [hr]
      _ = r⁻¹ * (E * T) := by rw [hscale]
  have hY :
      (∑ j : CuspAffineUnitIndex p,
        quadraticCuspWeight p (j : Fin p).val *
          (row.form (cuspFractionTranslate p (j : Fin p).val hp.pos τ) * T)) =
        Y * T := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hY]
  rw [← Finset.sum_mul]
  change X * S = (r⁻¹ * primeAffineEtaScalar p) * (Y * T)
  apply mul_right_cancel₀ hD
  calc
    (X * S) * D = X * (S * D) := by ring
    _ = X * (r⁻¹ * (E * T)) := by rw [hratio]
    _ = r⁻¹ * (X * E) * T := by ring
    _ = r⁻¹ * (primeAffineEtaScalar p * (Y * D)) * T := by rw [hstep]
    _ = ((r⁻¹ * primeAffineEtaScalar p) * (Y * T)) * D := by ring

/-- The eta ratio for a divisible square-width affine term, with eta at the
base point of the full Hecke expression. Its numerator and denominator are
evaluated at different cusp points, so this ratio must remain explicit. -/
noncomputable def divisibleUnitSquareGlobalEtaRatio
    (n : ℕ) (hn : 0 < n) (h24 : IsUnit (24 : ZMod n))
    (k : CuspAffineUnitIndex n) (τ : UpperHalfPlane) : ℂ :=
  (ModularForm.eta (cuspFractionTranslate n
      (cuspAffineInverseIndex n hn h24 k : Fin n).val hn τ) /
    ModularForm.eta (cuspAffinePoint (n * n) (n * (k : Fin n).val)
      (Nat.mul_pos hn hn) (ModularGroup.S • τ))) *
    (ModularForm.eta (ModularGroup.S • τ : UpperHalfPlane) /
      ModularForm.eta τ)

/-- A divisible square-width term transforms into its inverse-index middle
row term with the exact global eta ratio. -/
theorem InverseEtaFourierForm.divisibleUnitSquare_globalEta_inversion
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (n : ℕ) (hn : 0 < n) (h24 : IsUnit (24 : ZMod n))
    (k : CuspAffineUnitIndex n) (τ : UpperHalfPlane) :
    row.form (cuspAffinePoint (n * n) (n * (k : Fin n).val)
          (Nat.mul_pos hn hn) (ModularGroup.S • τ)) *
        ModularForm.eta (ModularGroup.S • τ : UpperHalfPlane) =
      divisibleUnitSquareGlobalEtaRatio n hn h24 k τ *
        (row.form (cuspFractionTranslate n
            (cuspAffineInverseIndex n hn h24 k : Fin n).val hn τ) *
          ModularForm.eta τ) := by
  obtain ⟨q, hq⟩ := cuspAffineInverseIndex_spec n hn h24 k
  rw [cuspAffinePoint_square_mul_inversion n (k : Fin n).val hn τ]
  rw [row.affine_inversion_eta_ratio n
    (cuspAffineInverseIndex n hn h24 k : Fin n).val (k : Fin n).val
    hn q hq (natDilation n hn τ)]
  rw [cuspAffinePoint_dilation_eq_fractionTranslate]
  unfold divisibleUnitSquareGlobalEtaRatio
  rw [cuspAffinePoint_square_mul_inversion n (k : Fin n).val hn τ]
  have hne := ModularForm.eta_ne_zero τ.im_pos
  field_simp [hne]

/-- Weighted divisible square-width terms reindex to the middle row while
retaining eta at the base point of the whole Hecke expression. -/
theorem InverseEtaFourierForm.divisibleUnitSquareWeightedSum_globalEta_inversion
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (n : ℕ) (hn : 0 < n) (h24 : IsUnit (24 : ZMod n))
    (w : CuspAffineUnitIndex n → ℂ) (τ : UpperHalfPlane) :
    (∑ k : CuspAffineUnitIndex n,
      w k * (row.form (cuspAffinePoint (n * n) (n * (k : Fin n).val)
            (Nat.mul_pos hn hn) (ModularGroup.S • τ)) *
          ModularForm.eta (ModularGroup.S • τ : UpperHalfPlane))) =
      ∑ j : CuspAffineUnitIndex n,
        w (cuspAffineInverseIndex n hn h24 j) *
          (divisibleUnitSquareGlobalEtaRatio n hn h24
              (cuspAffineInverseIndex n hn h24 j) τ *
            (row.form (cuspFractionTranslate n (j : Fin n).val hn τ) *
              ModularForm.eta τ)) := by
  classical
  let inv := cuspAffineInverseIndex n hn h24
  let F : CuspAffineUnitIndex n → ℂ := fun j =>
    w (inv j) * (divisibleUnitSquareGlobalEtaRatio n hn h24 (inv j) τ *
      (row.form (cuspFractionTranslate n (j : Fin n).val hn τ) *
        ModularForm.eta τ))
  calc
    _ = ∑ k : CuspAffineUnitIndex n,
        w k * (divisibleUnitSquareGlobalEtaRatio n hn h24 k τ *
          (row.form (cuspFractionTranslate n (inv k : Fin n).val hn τ) *
            ModularForm.eta τ)) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [row.divisibleUnitSquare_globalEta_inversion n hn h24 k τ]
    _ = ∑ k : CuspAffineUnitIndex n, F (inv k) := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [F, inv, (cuspAffineInverseIndex_involutive n hn h24) k]
    _ = ∑ k : CuspAffineUnitIndex n, F k := by
      apply Finset.sum_bij (fun k _ => inv k)
      · intro k _
        exact Finset.mem_univ _
      · intro k₁ _ k₂ _ heq
        exact (cuspAffineInverseIndex_involutive n hn h24).injective heq
      · intro k _
        exact ⟨inv k, Finset.mem_univ _,
          cuspAffineInverseIndex_involutive n hn h24 k⟩
      · intro k _
        rfl
    _ = _ := rfl

/-- The quadratic middle orbit picks up the character at `-1` under
inversion; its pointwise global eta ratios remain inside the sum. -/
theorem InverseEtaFourierForm.divisibleUnitSquareQuadraticSum_globalEta_inversion
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (p : ℕ) [Fact p.Prime] (h24 : IsUnit (24 : ZMod p))
    (τ : UpperHalfPlane) :
    (∑ k : CuspAffineUnitIndex p,
      quadraticCuspWeight p (k : Fin p).val *
        (row.form (cuspAffinePoint (p * p) (p * (k : Fin p).val)
              (Nat.mul_pos (Fact.out : p.Prime).pos (Fact.out : p.Prime).pos)
              (ModularGroup.S • τ)) *
          ModularForm.eta (ModularGroup.S • τ : UpperHalfPlane))) =
      ((quadraticChar (ZMod p) (-1) : ℤ) : ℂ) *
        ∑ j : CuspAffineUnitIndex p,
          quadraticCuspWeight p (j : Fin p).val *
            (divisibleUnitSquareGlobalEtaRatio p (Fact.out : p.Prime).pos h24
                (cuspAffineInverseIndex p (Fact.out : p.Prime).pos h24 j) τ *
              (row.form (cuspFractionTranslate p (j : Fin p).val
                    (Fact.out : p.Prime).pos τ) *
                ModularForm.eta τ)) := by
  rw [row.divisibleUnitSquareWeightedSum_globalEta_inversion p
    (Fact.out : p.Prime).pos h24
    (fun k => quadraticCuspWeight p (k : Fin p).val) τ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [quadraticCuspWeight_inverseIndex p h24 j]
  ring

/-- The unit part of the width-`p²` affine product orbit is invariant under
inversion. The prime condition identifies the unit indices with those not
divisible by `p`. -/
theorem InverseEtaFourierForm.affineNondivisibleSum_mul_eta_inversion
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (p : ℕ) (hp : p.Prime) (h24 : IsUnit (24 : ZMod (p * p)))
    (τ : UpperHalfPlane) :
    (∑ j ∈ (Finset.range (p * p)).filter (¬ p ∣ ·),
      row.form (cuspAffinePoint (p * p) j
          (Nat.mul_pos hp.pos hp.pos) (ModularGroup.S • τ)) *
        ModularForm.eta (cuspAffinePoint (p * p) j
          (Nat.mul_pos hp.pos hp.pos) (ModularGroup.S • τ))) =
      ∑ j ∈ (Finset.range (p * p)).filter (¬ p ∣ ·),
        row.form (cuspAffinePoint (p * p) j
            (Nat.mul_pos hp.pos hp.pos) τ) *
          ModularForm.eta (cuspAffinePoint (p * p) j
            (Nat.mul_pos hp.pos hp.pos) τ) := by
  rw [sum_nondivisible_primeSquare_eq_unit p hp,
    sum_nondivisible_primeSquare_eq_unit p hp]
  exact row.affineUnitSum_mul_eta_inversion
    (p * p) (Nat.mul_pos hp.pos hp.pos) h24 τ

/-- The affine product orbit under inversion separates into nondivisible
indices and a smaller affine orbit based at the inverted dilation. -/
theorem InverseEtaFourierForm.affineSquareSum_mul_eta_inversion_split
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (p : ℕ) (hp : 0 < p) (τ : UpperHalfPlane) :
    (∑ j ∈ Finset.range (p * p),
      row.form (cuspAffinePoint (p * p) j (Nat.mul_pos hp hp)
          (ModularGroup.S • τ)) *
        ModularForm.eta (cuspAffinePoint (p * p) j (Nat.mul_pos hp hp)
          (ModularGroup.S • τ))) =
      (∑ j ∈ (Finset.range (p * p)).filter (¬ p ∣ ·),
        row.form (cuspAffinePoint (p * p) j (Nat.mul_pos hp hp)
            (ModularGroup.S • τ)) *
          ModularForm.eta (cuspAffinePoint (p * p) j (Nat.mul_pos hp hp)
            (ModularGroup.S • τ))) +
      ∑ t ∈ Finset.range p,
        row.form (cuspAffinePoint p t hp
            (ModularGroup.S • natDilation p hp τ)) *
          ModularForm.eta (cuspAffinePoint p t hp
            (ModularGroup.S • natDilation p hp τ)) := by
  rw [sum_range_square_split p hp]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  rw [cuspAffinePoint_square_mul_inversion]

/-- The zero affine row and the dilation row exchange after inversion once
both are multiplied by eta at their respective evaluation points. -/
theorem InverseEtaFourierForm.zeroAffine_mul_eta_inversion
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (n : ℕ) (hn : 0 < n) (τ : UpperHalfPlane) :
    row.form (cuspAffinePoint n 0 hn (ModularGroup.S • τ)) *
        ModularForm.eta (cuspAffinePoint n 0 hn (ModularGroup.S • τ)) =
      row.form (natDilation n hn τ) *
        ModularForm.eta (natDilation n hn τ) := by
  rw [cuspAffinePoint_zero_inversion]
  exact row.form_mul_eta_invariant _ ⟨ModularGroup.S, rfl⟩ _

/-- The dilation row exchanges with the zero affine row under inversion. -/
theorem InverseEtaFourierForm.dilation_mul_eta_inversion
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (n : ℕ) (hn : 0 < n) (τ : UpperHalfPlane) :
    row.form (natDilation n hn (ModularGroup.S • τ)) *
        ModularForm.eta (natDilation n hn (ModularGroup.S • τ)) =
      row.form (cuspAffinePoint n 0 hn τ) *
        ModularForm.eta (cuspAffinePoint n 0 hn τ) := by
  rw [natDilation_inversion]
  exact row.form_mul_eta_invariant _ ⟨ModularGroup.S, rfl⟩ _

/-- The zero affine point at square width has a principal root scaled by
the reciprocal width. -/
theorem cuspAffinePoint_square_zero_sqrt (n : ℕ) (hn : 0 < n)
    (τ : UpperHalfPlane) :
    (cuspAffinePoint (n * n) 0 (Nat.mul_pos hn hn) τ : ℂ).sqrt =
      (n : ℂ)⁻¹ * (τ : ℂ).sqrt := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hpoint : ((n * n : ℕ) : ℂ) *
      (cuspAffinePoint (n * n) 0 (Nat.mul_pos hn hn) τ : ℂ) = (τ : ℂ) := by
    simp only [cuspAffinePoint_coe, Nat.cast_mul, Nat.cast_zero, mul_zero, add_zero]
    field_simp [hnC]
  have hs := complex_sqrt_nat_square_mul n hn
    (cuspAffinePoint (n * n) 0 (Nat.mul_pos hn hn) τ).im_pos
  rw [hpoint] at hs
  calc
    _ = (n : ℂ)⁻¹ * ((n : ℂ) *
        (cuspAffinePoint (n * n) 0 (Nat.mul_pos hn hn) τ : ℂ).sqrt) := by
          field_simp [hnC]
    _ = _ := by rw [← hs]

/-- Eta at the inverted zero affine point is `n` times the eta ratio
between the inverted base point and the square dilation. -/
theorem eta_square_zero_global_scale (n : ℕ) (hn : 0 < n)
    (τ : UpperHalfPlane) :
    ModularForm.eta (cuspAffinePoint (n * n) 0 (Nat.mul_pos hn hn)
        (ModularGroup.S • τ)) * ModularForm.eta τ =
      (n : ℂ) * ModularForm.eta (ModularGroup.S • τ : UpperHalfPlane) *
        ModularForm.eta (natDilation (n * n) (Nat.mul_pos hn hn) τ) := by
  rw [eta_cuspAffinePoint_zero_inversion]
  have hS : ModularForm.eta (ModularGroup.S • τ : UpperHalfPlane) =
      Complex.I.sqrt⁻¹ * (τ : ℂ).sqrt * ModularForm.eta τ := by
    rw [UpperHalfPlane.modular_S_smul]
    have harg : (-(τ : ℂ))⁻¹ = -1 / (τ : ℂ) := by
      field_simp [τ.ne_zero]
    change ModularForm.eta ((-(τ : ℂ))⁻¹) = _
    rw [harg]
    exact eta_neg_inv τ.im_pos
  rw [hS, natDilation_coe, complex_sqrt_nat_square_mul n hn τ.im_pos]
  ring

/-- The zero affine and square dilation Hecke terms exchange their global
eta factors with the exact reciprocal width. -/
theorem InverseEtaFourierForm.zeroAffineSquare_globalEta_inversion
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (n : ℕ) (hn : 0 < n) (τ : UpperHalfPlane) :
    row.form (cuspAffinePoint (n * n) 0 (Nat.mul_pos hn hn)
        (ModularGroup.S • τ)) *
        ModularForm.eta (ModularGroup.S • τ : UpperHalfPlane) =
      (n : ℂ)⁻¹ *
        (row.form (natDilation (n * n) (Nat.mul_pos hn hn) τ) *
          ModularForm.eta τ) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hne := ModularForm.eta_ne_zero
    (natDilation (n * n) (Nat.mul_pos hn hn) τ).im_pos
  have hrow := row.zeroAffine_mul_eta_inversion (n * n)
    (Nat.mul_pos hn hn) τ
  have hscale := eta_square_zero_global_scale n hn τ
  have hmul : (n : ℂ) *
      (row.form (cuspAffinePoint (n * n) 0 (Nat.mul_pos hn hn)
        (ModularGroup.S • τ)) *
        ModularForm.eta (ModularGroup.S • τ : UpperHalfPlane)) =
      row.form (natDilation (n * n) (Nat.mul_pos hn hn) τ) *
        ModularForm.eta τ := by
    apply mul_right_cancel₀ hne
    calc
      _ = row.form (cuspAffinePoint (n * n) 0 (Nat.mul_pos hn hn)
            (ModularGroup.S • τ)) *
          (ModularForm.eta (cuspAffinePoint (n * n) 0 (Nat.mul_pos hn hn)
            (ModularGroup.S • τ)) * ModularForm.eta τ) := by
          rw [hscale]
          ring
      _ = _ := by rw [← mul_assoc, hrow]; ring
  calc
    _ = (n : ℂ)⁻¹ * ((n : ℂ) *
        (row.form (cuspAffinePoint (n * n) 0 (Nat.mul_pos hn hn)
          (ModularGroup.S • τ)) *
          ModularForm.eta (ModularGroup.S • τ : UpperHalfPlane))) := by
          field_simp [hnC]
    _ = _ := by rw [hmul]

/-- The square dilation has the reciprocal eta scaling of the zero affine
point under inversion. -/
theorem eta_square_dilation_global_scale (n : ℕ) (hn : 0 < n)
    (τ : UpperHalfPlane) :
    (n : ℂ) * ModularForm.eta
        (natDilation (n * n) (Nat.mul_pos hn hn) (ModularGroup.S • τ)) *
        ModularForm.eta τ =
      ModularForm.eta (ModularGroup.S • τ : UpperHalfPlane) *
        ModularForm.eta (cuspAffinePoint (n * n) 0 (Nat.mul_pos hn hn) τ) := by
  rw [eta_natDilation_inversion, cuspAffinePoint_square_zero_sqrt n hn]
  have hS : ModularForm.eta (ModularGroup.S • τ : UpperHalfPlane) =
      Complex.I.sqrt⁻¹ * (τ : ℂ).sqrt * ModularForm.eta τ := by
    rw [UpperHalfPlane.modular_S_smul]
    have harg : (-(τ : ℂ))⁻¹ = -1 / (τ : ℂ) := by
      field_simp [τ.ne_zero]
    change ModularForm.eta ((-(τ : ℂ))⁻¹) = _
    rw [harg]
    exact eta_neg_inv τ.im_pos
  rw [hS]
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hnC]

/-- Under inversion the square dilation term becomes the zero affine term,
with global eta factor multiplied by the width. -/
theorem InverseEtaFourierForm.dilationSquare_globalEta_inversion
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (n : ℕ) (hn : 0 < n) (τ : UpperHalfPlane) :
    row.form (natDilation (n * n) (Nat.mul_pos hn hn)
        (ModularGroup.S • τ)) *
        ModularForm.eta (ModularGroup.S • τ : UpperHalfPlane) =
      (n : ℂ) *
        (row.form (cuspAffinePoint (n * n) 0 (Nat.mul_pos hn hn) τ) *
          ModularForm.eta τ) := by
  have hne := ModularForm.eta_ne_zero
    (cuspAffinePoint (n * n) 0 (Nat.mul_pos hn hn) τ).im_pos
  have hrow := row.dilation_mul_eta_inversion (n * n)
    (Nat.mul_pos hn hn) τ
  have hscale := eta_square_dilation_global_scale n hn τ
  apply mul_right_cancel₀ hne
  calc
    _ = row.form (natDilation (n * n) (Nat.mul_pos hn hn)
          (ModularGroup.S • τ)) *
        ((n : ℂ) * ModularForm.eta
          (natDilation (n * n) (Nat.mul_pos hn hn) (ModularGroup.S • τ)) *
          ModularForm.eta τ) := by rw [hscale]; ring
    _ = (n : ℂ) *
        ((row.form (natDilation (n * n) (Nat.mul_pos hn hn)
              (ModularGroup.S • τ)) *
            ModularForm.eta (natDilation (n * n) (Nat.mul_pos hn hn)
              (ModularGroup.S • τ))) * ModularForm.eta τ) := by ring
    _ = _ := by rw [hrow]; ring

/-- The zero affine term and square dilation term of the prime Hecke sum
exchange under inversion with their exact `p⁻²` and `p⁻³` coefficients.
This isolates the two endpoint terms of the three-term sum; the other
affine points and the quadratic middle row are handled separately. -/
theorem InverseEtaFourierForm.squareEndpoints_globalEta_inversion
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (n : ℕ) (hn : 0 < n) (τ : UpperHalfPlane) :
    (((n : ℂ) ^ 2)⁻¹ * row.form
        (cuspAffinePoint (n * n) 0 (Nat.mul_pos hn hn)
          (ModularGroup.S • τ)) +
      ((n : ℂ) ^ 3)⁻¹ * row.form
        (natDilation (n * n) (Nat.mul_pos hn hn)
          (ModularGroup.S • τ))) *
        ModularForm.eta (ModularGroup.S • τ : UpperHalfPlane) =
      (((n : ℂ) ^ 2)⁻¹ * row.form
        (cuspAffinePoint (n * n) 0 (Nat.mul_pos hn hn) τ) +
      ((n : ℂ) ^ 3)⁻¹ * row.form
        (natDilation (n * n) (Nat.mul_pos hn hn) τ)) *
        ModularForm.eta τ := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hz := row.zeroAffineSquare_globalEta_inversion n hn τ
  have hd := row.dilationSquare_globalEta_inversion n hn τ
  calc
    _ = ((n : ℂ) ^ 2)⁻¹ *
          (row.form (cuspAffinePoint (n * n) 0 (Nat.mul_pos hn hn)
            (ModularGroup.S • τ)) *
            ModularForm.eta (ModularGroup.S • τ : UpperHalfPlane)) +
        ((n : ℂ) ^ 3)⁻¹ *
          (row.form (natDilation (n * n) (Nat.mul_pos hn hn)
            (ModularGroup.S • τ)) *
            ModularForm.eta (ModularGroup.S • τ : UpperHalfPlane)) := by ring
    _ = ((n : ℂ) ^ 2)⁻¹ *
          ((n : ℂ)⁻¹ *
            (row.form (natDilation (n * n) (Nat.mul_pos hn hn) τ) *
              ModularForm.eta τ)) +
        ((n : ℂ) ^ 3)⁻¹ *
          ((n : ℂ) *
            (row.form (cuspAffinePoint (n * n) 0 (Nat.mul_pos hn hn) τ) *
              ModularForm.eta τ)) := by rw [hz, hd]
    _ = _ := by field_simp [hnC]; ring

/-- The inversion identity for the concrete prime Hecke expression suffices
for its full inverse-eta transformation law. -/
theorem InverseEtaFourierForm.primeAnalyticHeckeStep_map_action_of_inversion
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (p : ℕ) [Fact p.Prime] (hp6 : p.Coprime 6)
    (hS : ∀ τ : UpperHalfPlane,
      inverseEtaPrimeAnalyticHeckeStep row p (ModularGroup.S • τ) *
        ModularForm.eta ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) =
      inverseEtaPrimeAnalyticHeckeStep row p τ * ModularForm.eta τ)
    (γ : GL (Fin 2) ℝ) (hγ : γ ∈ 𝒮ℒ) (τ : UpperHalfPlane) :
    inverseEtaPrimeAnalyticHeckeStep row p (γ • τ) =
      (etaAutomorphyFactor γ τ)⁻¹ *
        inverseEtaPrimeAnalyticHeckeStep row p τ := by
  let ζ : ℂ := Complex.exp (Real.pi * Complex.I / 12)
  have hTu : ∀ z : UpperHalfPlane,
      inverseEtaPrimeAnalyticHeckeStep row p (upperUnipotent 1 • z) *
        ModularForm.eta ((upperUnipotent 1 • z : UpperHalfPlane) : ℂ) =
      inverseEtaPrimeAnalyticHeckeStep row p z * ModularForm.eta z := by
    intro z
    have hf := row.primeAnalyticHeckeStep_translation p hp6 z
    have he' : ModularForm.eta ((upperUnipotent 1 • z : UpperHalfPlane) : ℂ) =
        ζ * ModularForm.eta z := by
      rw [upperUnipotent_apply]
      simpa [ζ] using (eta_add_int (z : ℂ) (1 : ℤ))
    rw [hf, he']
    calc
      ζ⁻¹ * inverseEtaPrimeAnalyticHeckeStep row p z *
          (ζ * ModularForm.eta z) =
        (ζ⁻¹ * ζ) *
          (inverseEtaPrimeAnalyticHeckeStep row p z * ModularForm.eta z) := by ring
      _ = _ := by simp [ζ, Complex.exp_ne_zero]
  have hT : ∀ z : UpperHalfPlane,
      inverseEtaPrimeAnalyticHeckeStep row p (ModularGroup.T • z) *
        ModularForm.eta ((ModularGroup.T • z : UpperHalfPlane) : ℂ) =
      inverseEtaPrimeAnalyticHeckeStep row p z * ModularForm.eta z := by
    simpa only [show ModularGroup.T = upperUnipotent 1 by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [ModularGroup.T, upperUnipotent_matrix]] using hTu
  exact inverseEta_map_action_of_generator_products
    (inverseEtaPrimeAnalyticHeckeStep row p) hS hT γ hγ τ

/-- After inversion has been proved, the analytic prime expression realizes
the exact Hecke coefficient row. The parameter `hS` names the remaining
inversion equation; this constructor does not establish it. -/
noncomputable def InverseEtaFourierForm.primeHeckeRowOfInversion
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (hm : m.Coprime 6) (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) (hp6 : p.Coprime 6)
    (hS : ∀ τ : UpperHalfPlane,
      inverseEtaPrimeAnalyticHeckeStep row p (ModularGroup.S • τ) *
        ModularForm.eta ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) =
      inverseEtaPrimeAnalyticHeckeStep row p τ * ModularForm.eta τ) :
    InverseEtaFourierForm (m * p) (heckeMinusHalf p A) where
  form := {
    toFun := inverseEtaPrimeAnalyticHeckeStep row p
    holomorphic' := row.primeAnalyticHeckeStep_holomorphic p
    map_action' := by
      intro γ hγ τ
      simpa using row.primeAnalyticHeckeStep_map_action_of_inversion p hp6 hS γ hγ τ
    meromorphic_cusp' := row.primeAnalyticHeckeStep_meromorphicCusp p
  }
  residue_support := by
    intro r hr
    have hpmod : (p : ℤ) ^ 2 % 24 = 1 := by
      have h := squareIndex_mod_twentyFour_of_coprime_six p hp6
      exact_mod_cast (show p ^ 2 % 24 = 1 by simpa [pow_two] using h)
    rw [heckeMinusHalf_eq_squareHecke] at hr
    exact squareHecke_residue_support p 24 23 hpmod _ _ A row.residue_support r hr
  support := row.primeAnalyticHeckeStep_support p
  hasSum := row.hasSum_primeAnalyticHeckeStep hm p hp hp6

end SptClassification.QSeries
