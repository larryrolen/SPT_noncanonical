/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.PrimeInverseEtaHeckeGenerator
public import SptClassification.QSeries.EtaHecke
import SptClassification.Theta.EtaWeilGeneratorWords

/-!
# Inversion of the analytic prime Hecke orbit

The middle Hecke coefficient carries the affine average factor `p⁻²`.
Applying the divisible affine orbit law twice transfers that coefficient to
the reverse middle orbit without dividing by the eta phase. This is one of
the manuscript-specific steps in the prime Hecke transformation
[rolenManuscript, §3, Hecke formula].
-/

public section

namespace SptClassification.QSeries

open UpperHalfPlane

/-- The eta phase remaining after one odd prime affine orbit is a fourth
root of unity. This fixes the sign convention before evaluating the
positive-phase quadratic Gauss sum. -/
theorem primeAffineEtaPhase_eq_power (p : ℕ) (hodd : Odd p) :
    Complex.exp (-Real.pi * Complex.I * (p : ℂ) / 4) * Complex.I.sqrt =
      (-Complex.I) ^ ((p - 1) / 2) := by
  obtain ⟨k, hk⟩ := hodd
  have hp : p = 2 * k + 1 := by omega
  subst p
  have hroot : Complex.I.sqrt ≠ 0 := by
    intro hz
    have hs := complex_sqrt_sq Complex.I
    rw [hz] at hs
    exact Complex.I_ne_zero (by simpa using hs.symm)
  have harg : -Real.pi * Complex.I * ((2 * k + 1 : ℕ) : ℂ) / 4 =
      ((2 * k + 1 : ℕ) : ℂ) * (-(Real.pi / 4) * Complex.I) := by
    push_cast
    ring
  have hphase : (Complex.I.sqrt⁻¹) ^ 2 = -Complex.I := by
    rw [inv_pow, complex_sqrt_sq]
    simp
  have hhalf : ((2 * k + 1) - 1) / 2 = k := by omega
  rw [hhalf, harg, Complex.exp_nat_mul, ← Theta.eta_inversion_phase]
  calc
    (Complex.I.sqrt⁻¹) ^ (2 * k + 1) * Complex.I.sqrt =
        ((Complex.I.sqrt⁻¹) ^ 2) ^ k *
          (Complex.I.sqrt⁻¹ * Complex.I.sqrt) := by
      rw [pow_add, pow_one, pow_mul]
      ring
    _ = (-Complex.I) ^ k := by rw [hphase, inv_mul_cancel₀ hroot, mul_one]

/-- The positive Gauss phase and the odd eta phase have the Jacobi sign
`(-2/p)`. This finite residue calculation is independent of the analytic
Hecke row and of any Gauss-sum evaluation theorem. -/
theorem primeAffineEtaPhase_mul_gaussSign (p : ℕ) (hodd : Odd p) :
    Complex.exp (-Real.pi * Complex.I * (p : ℂ) / 4) * Complex.I.sqrt *
      (if p % 4 = 1 then (1 : ℂ) else Complex.I) =
        (jacobiSym (-2) p : ℂ) := by
  have hoddmod : p % 2 = 1 := Nat.odd_iff.mp hodd
  have hchar : jacobiSym (-2) p =
      if p % 2 = 0 then 0 else if p % 8 = 1 ∨ p % 8 = 3 then 1 else -1 := by
    rw [jacobiSym.at_neg_two hodd, ZMod.χ₈'_nat_eq_if_mod_eight]
  have hfour : (-Complex.I) ^ 4 = 1 := by
    calc
      (-Complex.I) ^ 4 = (Complex.I ^ 2) ^ 2 := by ring
      _ = 1 := by rw [Complex.I_sq]; norm_num
  have hpow (k : ℕ) : (-Complex.I) ^ k = (-Complex.I) ^ (k % 4) := by
    conv_lhs => rw [← Nat.mod_add_div k 4]
    rw [pow_add, pow_mul, hfour]
    simp
  rw [primeAffineEtaPhase_eq_power p hodd, hpow, hchar]
  have hcases : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by
    omega
  rcases hcases with h | h | h | h
  · have hk : (p - 1) / 2 % 4 = 0 := by omega
    have hp : p % 4 = 1 := by omega
    simp [hoddmod, h, hk, hp]
  · have hk : (p - 1) / 2 % 4 = 1 := by omega
    have hp : p % 4 = 3 := by omega
    simp [hoddmod, h, hk, hp, Complex.I_sq]
  · have hk : (p - 1) / 2 % 4 = 2 := by omega
    have hp : p % 4 = 1 := by omega
    simp [hoddmod, h, hk, hp, Complex.I_sq]
  · have hk : (p - 1) / 2 % 4 = 3 := by omega
    have hp : p % 4 = 3 := by omega
    simp only [hk, hp, hoddmod, h, ↓reduceIte, Int.cast_neg, Int.cast_one]
    calc
      (-Complex.I) ^ 3 * Complex.I = -(Complex.I ^ 2) ^ 2 := by ring
      _ = -1 := by rw [Complex.I_sq]; ring
      _ = _ := by norm_num

/-- The two Jacobi signs in the affine eta orbit combine to the weight
`-1/2` Hecke character. The factor `4` is a square at every odd prime. -/
theorem primeAffineJacobi_product (p : ℕ) (hodd : Odd p) :
    jacobiSym (-24) p * jacobiSym (-2) p =
      characterTwelve (p : ℤ) := by
  rw [characterTwelve_eq_jacobi_of_odd hodd]
  calc
    jacobiSym (-24) p * jacobiSym (-2) p =
        jacobiSym ((-24) * (-2)) p := (jacobiSym.mul_left _ _ _).symm
    _ = jacobiSym (12 * 4) p := by norm_num
    _ = jacobiSym 12 p := by
      rw [jacobiSym.mul_left, jacobiSym.at_four hodd, mul_one]

/-- The signed positive-phase quadratic Gauss evaluation supplies exactly
the scalar needed by the three-term inverse-eta Hecke inversion. The
affine-orbit coefficient `p⁻²` is retained. The sign evaluation is kept as
a separate hypothesis; Mathlib's Gauss-square theorem alone cannot choose
the sign. -/
theorem primeAffineEtaScalar_of_signedGauss
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (hgauss :
      gaussSum (quadraticComplexChar p) ZMod.stdAddChar =
        (if p % 4 = 1 then (1 : ℂ) else Complex.I) * (Real.sqrt p : ℂ)) :
    (((p : ℂ) ^ 2)⁻¹ *
      ((((Real.sqrt p : ℝ) : ℂ)⁻¹) * primeAffineEtaScalar p)) =
        (etaHeckeMiddleScalar p : ℂ) * quadraticCuspGaussNormalizer p := by
  let g : ℂ := gaussSum (quadraticComplexChar p) ZMod.stdAddChar
  let s : ℂ := (Real.sqrt p : ℂ)
  have hpOdd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hs : s ≠ 0 := by
    have hspos : 0 < Real.sqrt p := Real.sqrt_pos.2 (by positivity)
    dsimp only [s]
    exact_mod_cast (ne_of_gt hspos)
  have hg : g ≠ 0 := quadraticCuspGauss_ne_zero p hp
  have hphase := primeAffineEtaPhase_mul_gaussSign p hpOdd
  have hcharacter := primeAffineJacobi_product p hpOdd
  have hquad : quadraticChar (ZMod p) (-1) = legendreSym p (-1) := by
    change quadraticChar (ZMod p) (-1) =
      quadraticChar (ZMod p) (((-1 : ℤ) : ZMod p))
    norm_num
  have hscaled :
      (s⁻¹ * primeAffineEtaScalar p) * g =
        (((characterTwelve (p : ℤ) * legendreSym p (-1) : ℤ) : ℂ)) := by
    dsimp only [g]
    rw [hgauss]
    rw [primeAffineEtaScalar_eq, hquad]
    simp only [Int.cast_mul]
    calc
      _ = ((jacobiSym (-24) p : ℂ) * ((legendreSym p (-1) : ℤ) : ℂ)) *
          (Complex.exp (-Real.pi * Complex.I * (p : ℂ) / 4) *
            Complex.I.sqrt *
            (if p % 4 = 1 then (1 : ℂ) else Complex.I)) *
          (s⁻¹ * s) := by ring
      _ = ((jacobiSym (-24) p : ℂ) * ((legendreSym p (-1) : ℤ) : ℂ)) *
          (jacobiSym (-2) p : ℂ) := by rw [hphase, inv_mul_cancel₀ hs, mul_one]
      _ = ((characterTwelve (p : ℤ) : ℤ) : ℂ) *
          ((legendreSym p (-1) : ℤ) : ℂ) := by
        rw [mul_right_comm, ← Int.cast_mul, hcharacter]
  have hscaled' :
      s⁻¹ * primeAffineEtaScalar p =
        (((characterTwelve (p : ℤ) * legendreSym p (-1) : ℤ) : ℂ)) * g⁻¹ := by
    calc
      _ = ((s⁻¹ * primeAffineEtaScalar p) * g) * g⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hg, mul_one]
      _ = _ := by rw [hscaled]
  change ((p : ℂ) ^ 2)⁻¹ * (s⁻¹ * primeAffineEtaScalar p) =
    (etaHeckeMiddleScalar p : ℂ) * quadraticCuspGaussNormalizer p
  rw [hscaled']
  rw [etaHeckeMiddleScalar_eq, quadraticCuspGaussNormalizer_eq]
  dsimp only [g]
  push_cast
  ring

private theorem modularS_twice (τ : UpperHalfPlane) :
    ModularGroup.S • (ModularGroup.S • τ) = τ := by
  apply UpperHalfPlane.ext
  simp only [UpperHalfPlane.modular_S_smul]
  field_simp [τ.ne_zero]

/-- At prime width, separate the zero residue from the unit residues.
This is the finite reindexing needed for both the divisible affine orbit
and the quadratic middle orbit. -/
theorem sum_range_prime_eq_zero_add_units (p : ℕ) (hp : p.Prime)
    (F : ℕ → ℂ) :
    (∑ j ∈ Finset.range p, F j) =
      F 0 + ∑ k : CuspAffineUnitIndex p, F (k : Fin p).val := by
  classical
  have hunit (j : ℕ) (hj : j < p) :
      IsUnit (j : ZMod p) ↔ j ≠ 0 := by
    rw [ZMod.isUnit_iff_coprime]
    constructor
    · intro hcop hzero
      subst j
      simp at hcop
      exact hp.ne_one hcop
    · intro hne
      apply ((hp.coprime_iff_not_dvd).mpr ?_).symm
      intro hdiv
      have hle := Nat.le_of_dvd (by omega : 0 < j) hdiv
      omega
  have hnonzero :
      (∑ j ∈ (Finset.range p).filter (· ≠ 0), F j) =
        ∑ k : CuspAffineUnitIndex p, F (k : Fin p).val := by
    apply Finset.sum_bij (fun j hj =>
      (⟨⟨j, Finset.mem_range.mp (Finset.mem_filter.mp hj).1⟩,
        (hunit j (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)).mpr
          (Finset.mem_filter.mp hj).2⟩ : CuspAffineUnitIndex p))
    · intro j _
      exact Finset.mem_univ _
    · intro j₁ _ j₂ _ heq
      exact congrArg (fun k : CuspAffineUnitIndex p => (k : Fin p).val) heq
    · intro k _
      refine ⟨(k : Fin p).val, ?_, ?_⟩
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (k : Fin p).isLt,
            (hunit _ (k : Fin p).isLt).mp k.property⟩
      · apply Subtype.ext
        apply Fin.ext
        rfl
    · intro j _
      rfl
  have hzero :
      (∑ j ∈ (Finset.range p).filter (· = 0), F j) = F 0 := by
    simp [hp.pos]
  rw [← hzero, ← hnonzero]
  simpa only [add_comm] using
    (Finset.sum_filter_add_sum_filter_not
      (s := Finset.range p) (p := fun j => j = 0) F).symm

/-- The reverse middle orbit follows from the divisible affine orbit law.
The scalar comparison includes the affine coefficient `p⁻²`; no inverse of
the eta phase or the quadratic Gauss factor is used. -/
theorem InverseEtaFourierForm.middleQuadraticSum_globalEta_inversion
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (p : ℕ) [Fact p.Prime] (hodd : (p : ℤ) % 2 = 1)
    (h24 : IsUnit (24 : ZMod p))
    (hscalar :
      (((p : ℂ) ^ 2)⁻¹ *
        ((((Real.sqrt p : ℝ) : ℂ)⁻¹) * primeAffineEtaScalar p)) =
          (etaHeckeMiddleScalar p : ℂ) * quadraticCuspGaussNormalizer p)
    (τ : UpperHalfPlane) :
    ((etaHeckeMiddleScalar p : ℂ) * quadraticCuspGaussNormalizer p) *
      (∑ j : CuspAffineUnitIndex p,
        quadraticCuspWeight p (j : Fin p).val *
          row.form (cuspFractionTranslate p (j : Fin p).val
            (Fact.out : p.Prime).pos (ModularGroup.S • τ))) *
        ModularForm.eta (ModularGroup.S • τ : UpperHalfPlane) =
      ((p : ℂ) ^ 2)⁻¹ *
        (∑ k : CuspAffineUnitIndex p,
          row.form (cuspAffinePoint (p * p) (p * (k : Fin p).val)
            (Nat.mul_pos (Fact.out : p.Prime).pos (Fact.out : p.Prime).pos) τ)) *
          ModularForm.eta τ := by
  have hforward := row.divisibleUnitSquareSum_globalEta_quadratic
    p hodd h24 (ModularGroup.S • τ)
  rw [modularS_twice] at hforward
  rw [← hscalar]
  calc
    _ = ((p : ℂ) ^ 2)⁻¹ *
        (((((Real.sqrt p : ℝ) : ℂ)⁻¹) * primeAffineEtaScalar p) *
          (∑ j : CuspAffineUnitIndex p,
            quadraticCuspWeight p (j : Fin p).val *
              (row.form (cuspFractionTranslate p (j : Fin p).val
                (Fact.out : p.Prime).pos (ModularGroup.S • τ)) *
                  ModularForm.eta (ModularGroup.S • τ : UpperHalfPlane)))) := by
      simp only [Finset.sum_mul, mul_assoc]
    _ = _ := by rw [← hforward]; simp only [Finset.sum_mul, mul_assoc]

/-- The complete three-term prime Hecke expression satisfies inversion once
the signed quadratic Gauss scalar has its stated value. All affine residues
are accounted for: primitive residues stay in the affine orbit, nonzero
divisible residues exchange with the quadratic row, and zero exchanges with
the dilation endpoint. -/
theorem InverseEtaFourierForm.primeAnalyticHeckeStep_globalEta_inversion
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (hscalar :
      (((p : ℂ) ^ 2)⁻¹ *
        ((((Real.sqrt p : ℝ) : ℂ)⁻¹) * primeAffineEtaScalar p)) =
          (etaHeckeMiddleScalar p : ℂ) * quadraticCuspGaussNormalizer p)
    (τ : UpperHalfPlane) :
    inverseEtaPrimeAnalyticHeckeStep row p (ModularGroup.S • τ) *
      ModularForm.eta ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) =
    inverseEtaPrimeAnalyticHeckeStep row p τ * ModularForm.eta τ := by
  let hpPrime : p.Prime := Fact.out
  have hp6 : p.Coprime 6 := by
    apply (hpPrime.coprime_iff_not_dvd).mpr
    intro hdiv
    rcases hpPrime.dvd_mul.mp (by simpa only [show 6 = 2 * 3 by norm_num] using hdiv)
      with h2 | h3
    · have hle := Nat.le_of_dvd (by norm_num : 0 < 2) h2
      omega
    · have hle := Nat.le_of_dvd (by norm_num : 0 < 3) h3
      omega
  have hodd : (p : ℤ) % 2 = 1 := by
    rcases hpPrime.odd_of_ne_two (by omega) with ⟨k, hk⟩
    omega
  have h24 : IsUnit (24 : ZMod p) := by
    change IsUnit ((24 : ℕ) : ZMod p)
    rw [ZMod.isUnit_iff_coprime]
    refine ((hpPrime.coprime_iff_not_dvd).mpr ?_).symm
    intro hdiv
    rcases hpPrime.dvd_mul.mp (by simpa only [show 24 = 6 * 4 by norm_num] using hdiv)
      with h6 | h4
    · exact (hpPrime.coprime_iff_not_dvd.mp hp6) h6
    · have hle := Nat.le_of_dvd (by norm_num : 0 < 4) h4
      omega
  have h24sq : IsUnit (24 : ZMod (p * p)) := by
    change IsUnit ((24 : ℕ) : ZMod (p * p))
    rw [ZMod.isUnit_iff_coprime]
    simpa only [pow_two] using
      ((ZMod.isUnit_iff_coprime 24 p).mp h24).pow_right 2
  let a : ℂ := ((p : ℂ) ^ 2)⁻¹
  let b : ℂ := (etaHeckeMiddleScalar p : ℂ) * quadraticCuspGaussNormalizer p
  let c : ℂ := ((1 / (p : ℚ) ^ 3 : ℚ) : ℂ)
  let e (z : UpperHalfPlane) : ℂ := ModularForm.eta z
  let X (z : UpperHalfPlane) : ℂ :=
    ∑ j ∈ Finset.range (p * p),
      row.form (cuspAffinePoint (p * p) j
        (Nat.mul_pos hpPrime.pos hpPrime.pos) z)
  let U (z : UpperHalfPlane) : ℂ :=
    ∑ j ∈ (Finset.range (p * p)).filter (¬ p ∣ ·),
      row.form (cuspAffinePoint (p * p) j
        (Nat.mul_pos hpPrime.pos hpPrime.pos) z)
  let V (z : UpperHalfPlane) : ℂ :=
    ∑ k : CuspAffineUnitIndex p,
      row.form (cuspAffinePoint (p * p) (p * (k : Fin p).val)
        (Nat.mul_pos hpPrime.pos hpPrime.pos) z)
  let Z (z : UpperHalfPlane) : ℂ :=
    row.form (cuspAffinePoint (p * p) 0
      (Nat.mul_pos hpPrime.pos hpPrime.pos) z)
  let Q (z : UpperHalfPlane) : ℂ :=
    ∑ j : CuspAffineUnitIndex p,
      quadraticCuspWeight p (j : Fin p).val *
        row.form (cuspFractionTranslate p (j : Fin p).val hpPrime.pos z)
  let D (z : UpperHalfPlane) : ℂ :=
    row.form (natDilation (p * p)
      (Nat.mul_pos hpPrime.pos hpPrime.pos) z)
  have hsplit (z : UpperHalfPlane) : X z = U z + Z z + V z := by
    dsimp [X, U, Z, V]
    rw [sum_range_square_split p hpPrime.pos]
    rw [sum_range_prime_eq_zero_add_units p hpPrime]
    simp only [mul_zero]
    ring
  have hmiddle (z : UpperHalfPlane) :
      (∑ j ∈ Finset.range p,
        quadraticCuspWeight p j *
          row.form (cuspFractionTranslate p j hpPrime.pos z)) = Q z := by
    rw [sum_range_prime_eq_zero_add_units p hpPrime]
    have hzero : quadraticCuspWeight p 0 = 0 := by
      rw [quadraticCuspWeight_eq_character]
      simp
    simp only [hzero, zero_mul, zero_add, Q]
  have hU : U (ModularGroup.S • τ) * e (ModularGroup.S • τ) =
      U τ * e τ := by
    simpa only [U, e, Finset.sum_mul] using
      row.affineNondivisibleSquareSum_globalEta_inversion
        p hpPrime hodd h24sq τ
  have hV : V (ModularGroup.S • τ) * e (ModularGroup.S • τ) =
      ((((Real.sqrt p : ℝ) : ℂ)⁻¹) * primeAffineEtaScalar p) *
        (Q τ * e τ) := by
    simpa only [V, Q, e, Finset.sum_mul, mul_assoc] using
      row.divisibleUnitSquareSum_globalEta_quadratic p hodd h24 τ
  have hVnormalized : a * (V (ModularGroup.S • τ) * e (ModularGroup.S • τ)) =
      b * (Q τ * e τ) := by
    rw [hV]
    calc
      a * (((((Real.sqrt p : ℝ) : ℂ)⁻¹) * primeAffineEtaScalar p) *
          (Q τ * e τ)) =
          (a * ((((Real.sqrt p : ℝ) : ℂ)⁻¹) * primeAffineEtaScalar p)) *
            (Q τ * e τ) := by ring
      _ = b * (Q τ * e τ) := by rw [show a *
        ((((Real.sqrt p : ℝ) : ℂ)⁻¹) * primeAffineEtaScalar p) = b from hscalar]
  have hQ : b * (Q (ModularGroup.S • τ) * e (ModularGroup.S • τ)) =
      a * (V τ * e τ) := by
    simpa only [b, a, Q, V, e, Finset.sum_mul, mul_assoc] using
      row.middleQuadraticSum_globalEta_inversion p hodd h24 hscalar τ
  have hc : c = ((p : ℂ) ^ 3)⁻¹ := by
    dsimp [c]
    push_cast
    ring
  have hends :
      (a * Z (ModularGroup.S • τ) + c * D (ModularGroup.S • τ)) *
          e (ModularGroup.S • τ) =
        (a * Z τ + c * D τ) * e τ := by
    rw [hc]
    simpa only [a, Z, D, e] using row.squareEndpoints_globalEta_inversion
      p hpPrime.pos τ
  simp only [inverseEtaPrimeAnalyticHeckeStep_eq]
  change (a * X (ModularGroup.S • τ) +
        b * (∑ j ∈ Finset.range p,
          quadraticCuspWeight p j *
            row.form (cuspFractionTranslate p j hpPrime.pos
              (ModularGroup.S • τ))) +
        c * D (ModularGroup.S • τ)) * e (ModularGroup.S • τ) =
      (a * X τ +
        b * (∑ j ∈ Finset.range p,
          quadraticCuspWeight p j *
            row.form (cuspFractionTranslate p j hpPrime.pos τ)) +
        c * D τ) * e τ
  rw [hmiddle (ModularGroup.S • τ), hmiddle τ,
    hsplit (ModularGroup.S • τ), hsplit τ]
  calc
    (a * (U (ModularGroup.S • τ) + Z (ModularGroup.S • τ) +
          V (ModularGroup.S • τ)) + b * Q (ModularGroup.S • τ) +
          c * D (ModularGroup.S • τ)) * e (ModularGroup.S • τ) =
      a * (U (ModularGroup.S • τ) * e (ModularGroup.S • τ)) +
        a * (V (ModularGroup.S • τ) * e (ModularGroup.S • τ)) +
        b * (Q (ModularGroup.S • τ) * e (ModularGroup.S • τ)) +
        (a * Z (ModularGroup.S • τ) + c * D (ModularGroup.S • τ)) *
          e (ModularGroup.S • τ) := by ring
    _ = a * (U τ * e τ) + b * (Q τ * e τ) +
          a * (V τ * e τ) + (a * Z τ + c * D τ) * e τ := by
      rw [hU, hVnormalized, hQ, hends]
    _ = (a * (U τ + Z τ + V τ) + b * Q τ + c * D τ) * e τ := by ring

/-- An explicit scalar comparison supplies the analytic single-prime Hecke
law. Here `hscalar` is a premise with the affine-orbit factor `p⁻²`;
the three analytic cusp orbits and their inversion are established above.
[rolenManuscript, §3, Hecke formula] -/
noncomputable def primeInverseEtaHeckeLawOfGaussScalar
    (hscalar : ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p →
      (((p : ℂ) ^ 2)⁻¹ *
        ((((Real.sqrt p : ℝ) : ℂ)⁻¹) * primeAffineEtaScalar p)) =
          (etaHeckeMiddleScalar p : ℂ) * quadraticCuspGaussNormalizer p) :
    PrimeInverseEtaHeckeLaw where
  step := by
    intro m p _hm hmc hp hp5 A row
    letI : Fact p.Prime := ⟨hp⟩
    have hp6 : p.Coprime 6 := by
      apply (hp.coprime_iff_not_dvd).mpr
      intro hdiv
      rcases hp.dvd_mul.mp (by simpa only [show 6 = 2 * 3 by norm_num] using hdiv)
        with h2 | h3
      · have hle := Nat.le_of_dvd (by norm_num : 0 < 2) h2
        omega
      · have hle := Nat.le_of_dvd (by norm_num : 0 < 3) h3
        omega
    exact row.primeHeckeRowOfInversion hmc p hp5 hp6
      (fun τ => row.primeAnalyticHeckeStep_globalEta_inversion
        p hp5 (hscalar p hp5) τ)

/-- The classical signed quadratic Gauss evaluation, with the positive
`ZMod.stdAddChar` phase, is the finite-sum input needed for the analytic
prime inverse-eta Hecke law. The eta matrix law remains a separate admitted
prerequisite. -/
noncomputable def primeInverseEtaHeckeLawOfSignedGauss
    (hgauss : ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p →
      gaussSum (quadraticComplexChar p) ZMod.stdAddChar =
        (if p % 4 = 1 then (1 : ℂ) else Complex.I) * (Real.sqrt p : ℂ)) :
    PrimeInverseEtaHeckeLaw :=
  primeInverseEtaHeckeLawOfGaussScalar
    (fun p hpPrime hp5 =>
      letI : Fact p.Prime := hpPrime
      primeAffineEtaScalar_of_signedGauss p hp5 (hgauss p hp5))

/-- The manuscript square-index coefficient relation follows assuming the
explicit scalar premise `hscalar`, together with the separately cited
individual shadow forms and single-prime shadow identities. Repeated Hecke
primes and all positive discriminants in the manuscript's congruence class
are included.
[rolenManuscript, §3, Lemma 3.1; rolen2026canonical, Proposition 2.2 and
Lemma 2.4] -/
theorem square_coefficient_relation_of_gaussScalar
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (sign : ℤ)
    (hsign : sign = 1 ∨ sign = -1) (d : ℕ) (hdPos : 0 < d)
    (hd : d % 24 = 23)
    (hr : legendreSym p (-(d : ℤ)) = sign)
    (hspt : ∀ j : ℕ, legendreSym p (1 - 24 * (j : ℤ)) = sign →
      ((spt j : ℤ) : ZMod p) = 0)
    (hscalar : ∀ (q : ℕ) [Fact q.Prime], 5 ≤ q →
      (((q : ℂ) ^ 2)⁻¹ *
        ((((Real.sqrt q : ℝ) : ℂ)⁻¹) * primeAffineEtaScalar q)) =
          (etaHeckeMiddleScalar q : ℂ) * quadraticCuspGaussNormalizer q)
    (m : ℕ) (hmPos : 0 < m) (hmCop : m.Coprime (6 * p)) :
    (p : ℤ) ∣ (m : ℤ) ^ 2 *
      principalHFourier d (fFourier d) ((m : ℤ) ^ 2) +
      (d : ℤ) * principalKFourier d ((m : ℤ) ^ 2) := by
  exact square_coefficient_relation_of_primeInverseEtaLaw p hp sign hsign d
    hdPos hd hr hspt (primeInverseEtaHeckeLawOfGaussScalar hscalar) m hmPos hmCop

/-- Assuming the positive-phase signed quadratic Gauss evaluation, the
manuscript coefficient deduction holds for every positive `d ≡ 23 (mod 24)`
and every index coprime to `6p`, including repeated prime factors.
[rolenManuscript, §3, Lemma 3.1] -/
theorem square_coefficient_relation_of_signedGauss
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (sign : ℤ)
    (hsign : sign = 1 ∨ sign = -1) (d : ℕ) (hdPos : 0 < d)
    (hd : d % 24 = 23)
    (hr : legendreSym p (-(d : ℤ)) = sign)
    (hspt : ∀ j : ℕ, legendreSym p (1 - 24 * (j : ℤ)) = sign →
      ((spt j : ℤ) : ZMod p) = 0)
    (hgauss : ∀ (q : ℕ) [Fact q.Prime], 5 ≤ q →
      gaussSum (quadraticComplexChar q) ZMod.stdAddChar =
        (if q % 4 = 1 then (1 : ℂ) else Complex.I) * (Real.sqrt q : ℂ))
    (m : ℕ) (hmPos : 0 < m) (hmCop : m.Coprime (6 * p)) :
    (p : ℤ) ∣ (m : ℤ) ^ 2 *
      principalHFourier d (fFourier d) ((m : ℤ) ^ 2) +
      (d : ℤ) * principalKFourier d ((m : ℤ) ^ 2) := by
  exact square_coefficient_relation_of_primeInverseEtaLaw p hp sign hsign d
    hdPos hd hr hspt (primeInverseEtaHeckeLawOfSignedGauss hgauss) m hmPos hmCop

end SptClassification.QSeries
