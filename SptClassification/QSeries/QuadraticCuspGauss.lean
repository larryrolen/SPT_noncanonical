/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.InverseEtaHeckeTranslation
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.GaussSum

/-!
# Quadratic weights on a prime cusp orbit

The middle row of the inverse-eta square-index Hecke expression uses a finite
quadratic-character transform. This file evaluates its zero-frequency case,
including negative signed Fourier indices [rolenManuscript, §3].
-/

public section

namespace SptClassification.QSeries

open UpperHalfPlane
open scoped Manifold

/-- The cusp translation phase agrees with Mathlib's standard additive
character, including its positive Fourier orientation. -/
theorem cuspRoot_eq_stdAddChar (p : ℕ) [NeZero p] (a : ZMod p) :
    cuspRoot p a.val = (ZMod.stdAddChar a : ℂ) := by
  rw [cuspRoot_eq, ZMod.stdAddChar_apply, ZMod.toCircle_apply]

/-- The quadratic character weight on the prime cusp orbit. -/
noncomputable def quadraticCuspWeight (p : ℕ) [Fact p.Prime] (j : ℕ) : ℂ :=
  ((quadraticChar (ZMod p) (j : ZMod p) : ℤ) : ℂ)

/-- The character value represented by the cusp-orbit weight. -/
theorem quadraticCuspWeight_eq_character (p : ℕ) [Fact p.Prime] (j : ℕ) :
    quadraticCuspWeight p j =
      ((quadraticChar (ZMod p) (j : ZMod p) : ℤ) : ℂ) := (rfl)

/-- The nontrivial quadratic character has zero total weight on the prime
orbit. -/
theorem quadraticCuspWeight_sum_zero (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) :
    (∑ j ∈ Finset.range p, quadraticCuspWeight p j) = 0 := by
  have hpchar : ringChar (ZMod p) ≠ 2 := by
    rw [ringChar.eq (ZMod p) p]
    omega
  have hne : quadraticChar (ZMod p) ≠ 1 := quadraticChar_ne_one hpchar
  have hsum : (∑ a : ZMod p, quadraticChar (ZMod p) a) = (0 : ℤ) :=
    MulChar.sum_eq_zero_of_ne_one hne
  have hsumC :
      (∑ a : ZMod p, ((quadraticChar (ZMod p) a : ℤ) : ℂ)) = 0 := by
    exact_mod_cast hsum
  rw [Finset.sum_range]
  calc
    (∑ j : Fin p, quadraticCuspWeight p j) =
        ∑ a : ZMod p, ((quadraticChar (ZMod p) a : ℤ) : ℂ) := by
      apply Fintype.sum_equiv (ZMod.finEquiv p).toEquiv
      intro j
      cases p with
      | zero => omega
      | succ q =>
          have hj : (j.val : ZMod (q + 1)) =
              (ZMod.finEquiv (q + 1)).toEquiv j := by
            apply ZMod.val_injective
            simp only [ZMod.val_natCast, ZMod.finEquiv]
            change j.val % (q + 1) = j.val
            exact Nat.mod_eq_of_lt j.isLt
          simp [quadraticCuspWeight, hj]
    _ = 0 := hsumC

/-- At every signed index divisible by the prime, the quadratic-weighted
middle multiplier vanishes. -/
theorem quadraticCuspTransform_of_dvd (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) (r : ℤ) (hr : (p : ℤ) ∣ r) :
    cuspRootFourierTransform p (quadraticCuspWeight p) r = 0 := by
  rw [cuspRootFourierTransform_of_dvd p (by omega) _ r hr]
  exact quadraticCuspWeight_sum_zero p hp

/-- The quadratic-character transform of any function on the finite field.
Its scaling law is independent of the choice of the cusp additive phase. -/
noncomputable def quadraticFiniteTransform (p : ℕ) [Fact p.Prime]
    (ψ : ZMod p → ℂ) (r : ZMod p) : ℂ :=
  ∑ a : ZMod p,
    ((quadraticChar (ZMod p) a : ℤ) : ℂ) * ψ (a * r)

/-- Multiplying the frequency by a nonzero field element permutes the
summation orbit. This is the algebraic part of the quadratic Gauss multiplier. -/
theorem quadraticFiniteTransform_scale (p : ℕ) [Fact p.Prime]
    (ψ : ZMod p → ℂ) (r : ZMod p) (hr : r ≠ 0) :
    quadraticFiniteTransform p ψ 1 =
      ((quadraticChar (ZMod p) r : ℤ) : ℂ) *
        quadraticFiniteTransform p ψ r := by
  let e : ZMod p ≃ ZMod p := {
    toFun := fun a => a * r
    invFun := fun a => a * r⁻¹
    left_inv := by
      intro a
      simp [mul_assoc, hr]
    right_inv := by
      intro a
      simp [mul_assoc, hr]
  }
  have hreindex (f : ZMod p → ℂ) :
      (∑ a : ZMod p, f a) = ∑ a : ZMod p, f (e a) := by
    symm
    exact Fintype.sum_equiv e (fun a => f (e a)) f (fun _ => rfl)
  unfold quadraticFiniteTransform
  simp only [mul_one]
  rw [hreindex]
  simp only [e]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  change ((quadraticChar (ZMod p) (a * r) : ℤ) : ℂ) * ψ (a * r) =
    ((quadraticChar (ZMod p) r : ℤ) : ℂ) *
      (((quadraticChar (ZMod p) a : ℤ) : ℂ) * ψ (a * r))
  rw [map_mul]
  push_cast
  ring

/-- The nonzero-frequency scaling law in the direction used by the
coefficient row. -/
theorem quadraticFiniteTransform_scale_forward (p : ℕ) [Fact p.Prime]
    (ψ : ZMod p → ℂ) (r : ZMod p) (hr : r ≠ 0) :
    quadraticFiniteTransform p ψ r =
      ((quadraticChar (ZMod p) r : ℤ) : ℂ) *
        quadraticFiniteTransform p ψ 1 := by
  have hsquare : ((quadraticChar (ZMod p) r : ℤ) : ℂ) ^ 2 = 1 := by
    exact_mod_cast quadraticChar_sq_one hr
  calc
    quadraticFiniteTransform p ψ r =
        ((quadraticChar (ZMod p) r : ℤ) : ℂ) ^ 2 *
          quadraticFiniteTransform p ψ r := by rw [hsquare, one_mul]
    _ = ((quadraticChar (ZMod p) r : ℤ) : ℂ) *
          quadraticFiniteTransform p ψ 1 := by
      rw [quadraticFiniteTransform_scale p ψ r hr]
      ring

/-- The zero-frequency quadratic transform vanishes because the prime-field
quadratic character is nontrivial. -/
theorem quadraticFiniteTransform_zero (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) (ψ : ZMod p → ℂ) :
    quadraticFiniteTransform p ψ 0 = 0 := by
  have hpchar : ringChar (ZMod p) ≠ 2 := by
    rw [ringChar.eq (ZMod p) p]
    omega
  have hne : quadraticChar (ZMod p) ≠ 1 := quadraticChar_ne_one hpchar
  have hsum : (∑ a : ZMod p, quadraticChar (ZMod p) a) = (0 : ℤ) :=
    MulChar.sum_eq_zero_of_ne_one hne
  have hsumC :
      (∑ a : ZMod p, ((quadraticChar (ZMod p) a : ℤ) : ℂ)) = 0 := by
    exact_mod_cast hsum
  simp only [quadraticFiniteTransform, mul_zero, ← Finset.sum_mul,
    hsumC, zero_mul]

/-- The prime-orbit quadratic character as a complex multiplicative
character, preserving the original integral normalization. -/
noncomputable def quadraticComplexChar (p : ℕ) [Fact p.Prime] :
    MulChar (ZMod p) ℂ :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

/-- The finite cusp transform at frequency one is Mathlib's Gauss sum
with the positive standard additive phase. -/
theorem quadraticFiniteTransform_one_eq_gaussSum (p : ℕ) [Fact p.Prime] :
    quadraticFiniteTransform p (fun a => (ZMod.stdAddChar a : ℂ)) 1 =
      gaussSum (quadraticComplexChar p) (ZMod.stdAddChar) := by
  simp only [quadraticFiniteTransform, mul_one, gaussSum,
    quadraticComplexChar, MulChar.ringHomComp_apply, Int.coe_castRingHom]

/-- The square of the actual prime-orbit Gauss multiplier has the exact
quadratic-character and cardinality normalization. -/
theorem quadraticCuspGauss_square (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    (quadraticFiniteTransform p (fun a => (ZMod.stdAddChar a : ℂ)) 1) ^ 2 =
      ((quadraticChar (ZMod p) (-1) : ℤ) : ℂ) * (p : ℂ) := by
  have hpchar : ringChar (ZMod p) ≠ 2 := by
    rw [ringChar.eq (ZMod p) p]
    omega
  have hne : quadraticComplexChar p ≠ 1 := by
    exact (MulChar.ringHomComp_ne_one_iff
      (R := ZMod p) (f := Int.castRingHom ℂ)
      (by exact_mod_cast (Int.cast_injective : Function.Injective (fun z : ℤ => (z : ℂ))))).mpr
      (quadraticChar_ne_one hpchar)
  have hquad : (quadraticComplexChar p).IsQuadratic :=
    (quadraticChar_isQuadratic (ZMod p)).comp (Int.castRingHom ℂ)
  rw [quadraticFiniteTransform_one_eq_gaussSum]
  simpa only [quadraticComplexChar, MulChar.ringHomComp_apply,
    Int.coe_castRingHom, ZMod.card] using
    (gaussSum_sq hne hquad (ZMod.isPrimitive_stdAddChar p))

/-- The positive-phase quadratic Gauss multiplier is invertible at every
prime in the Hecke range [rolenManuscript, §3, Hecke formula]. -/
theorem quadraticCuspGauss_ne_zero (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    gaussSum (quadraticComplexChar p) (ZMod.stdAddChar) ≠ 0 := by
  have hsq := quadraticCuspGauss_square p hp
  rw [quadraticFiniteTransform_one_eq_gaussSum] at hsq
  have hcharInt : (quadraticChar (ZMod p) (-1) : ℤ) ≠ 0 := by
    intro hz
    have hone : (quadraticChar (ZMod p) (-1) : ℤ) *
        quadraticChar (ZMod p) (-1) = 1 := by
      calc
        _ = quadraticChar (ZMod p) ((-1) * (-1)) :=
          (map_mul (quadraticChar (ZMod p)) (-1) (-1)).symm
        _ = 1 := by simp
    rw [hz] at hone
    norm_num at hone
  have hchar : ((quadraticChar (ZMod p) (-1) : ℤ) : ℂ) ≠ 0 := by
    exact_mod_cast hcharInt
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  intro hzero
  rw [hzero] at hsq
  exact (mul_ne_zero hchar hpC) (by simpa using hsq.symm)

/-- The reciprocal of the actual positive-phase quadratic Gauss multiplier. -/
noncomputable def quadraticCuspGaussNormalizer (p : ℕ) [Fact p.Prime] : ℂ :=
  (gaussSum (quadraticComplexChar p) (ZMod.stdAddChar))⁻¹

/-- The normalizer is the reciprocal of the positive-phase quadratic sum. -/
theorem quadraticCuspGaussNormalizer_eq (p : ℕ) [Fact p.Prime] :
    quadraticCuspGaussNormalizer p =
      (gaussSum (quadraticComplexChar p) ZMod.stdAddChar)⁻¹ :=
  (rfl)

/-- Normalization removes the Gauss factor from the signed cusp transform. -/
theorem quadraticCuspGaussNormalizer_mul (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) :
    quadraticCuspGaussNormalizer p *
      gaussSum (quadraticComplexChar p) (ZMod.stdAddChar) = 1 := by
  exact inv_mul_cancel₀ (quadraticCuspGauss_ne_zero p hp)

/-- Multiplication of a residue moves its cusp root by the corresponding
natural Fourier frequency. This fixes the orientation of the additive phase
before the quadratic Gauss sum is evaluated. -/
theorem cuspRoot_mulResidue (p j r : ℕ) (hp : 0 < p) :
    cuspRoot p (((j : ZMod p) * (r : ZMod p)).val) =
      cuspRoot p j ^ r := by
  have hval : (((j : ZMod p) * (r : ZMod p)).val) = (j * r) % p := by
    rw [← Nat.cast_mul, ZMod.val_natCast]
  calc
    cuspRoot p (((j : ZMod p) * (r : ZMod p)).val) =
        cuspRoot p ((j * r) % p) := by rw [hval]
    _ = cuspRoot p (j * r) := cuspRoot_mod p (j * r) hp
    _ = cuspRoot p j ^ r := by
      rw [cuspRoot_eq_pow p (j * r), cuspRoot_eq_pow p j, pow_mul]

/-- At a natural frequency, the actual cusp-orbit transform is the
finite-field character transform for the cusp additive phase. -/
theorem quadraticCuspTransform_nat (p : ℕ) [Fact p.Prime]
    (r : ℕ) :
    cuspRootFourierTransform p (quadraticCuspWeight p) (r : ℤ) =
      quadraticFiniteTransform p (fun a => cuspRoot p a.val) (r : ZMod p) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  rw [cuspRootFourierTransform_eq_sum]
  unfold quadraticFiniteTransform
  rw [Finset.sum_range]
  apply Fintype.sum_equiv (ZMod.finEquiv p).toEquiv
  intro j
  have hj : (j.val : ZMod p) = (ZMod.finEquiv p).toEquiv j := by
    cases p with
    | zero => omega
    | succ q =>
        apply ZMod.val_injective
        simp only [ZMod.val_natCast, ZMod.finEquiv]
        change j.val % (q + 1) = j.val
        exact Nat.mod_eq_of_lt j.isLt
  rw [← hj]
  simp only [quadraticCuspWeight, zpow_natCast]
  rw [cuspRoot_mulResidue p j.val r hp]

/-- The same finite-field transform computes the cusp multiplier at a
signed index, including the negative indices of the inverse-eta pole. -/
theorem quadraticCuspTransform_signed (p : ℕ) [Fact p.Prime]
    (r : ℤ) :
    cuspRootFourierTransform p (quadraticCuspWeight p) r =
      quadraticFiniteTransform p (fun a => cuspRoot p a.val)
        (((r % (p : ℤ)).toNat : ℕ) : ZMod p) := by
  rw [cuspRootFourierTransform_emod p (Fact.out : p.Prime).pos]
  exact quadraticCuspTransform_nat p _

/-- The signed cusp transform written with the standard additive character
of the prime residue field. -/
theorem quadraticCuspTransform_signed_addChar (p : ℕ) [Fact p.Prime]
    (r : ℤ) :
    cuspRootFourierTransform p (quadraticCuspWeight p) r =
      quadraticFiniteTransform p (fun a => (ZMod.stdAddChar a : ℂ))
        (((r % (p : ℤ)).toNat : ℕ) : ZMod p) := by
  rw [quadraticCuspTransform_signed]
  congr 1
  funext a
  exact cuspRoot_eq_stdAddChar p a

/-- At a nonzero signed frequency, multiplication by the quadratic
character carries the cusp transform to the frequency-one Gauss sum. -/
theorem quadraticCuspTransform_signed_scale (p : ℕ) [Fact p.Prime]
    (r : ℤ)
    (hr : (((r % (p : ℤ)).toNat : ℕ) : ZMod p) ≠ 0) :
    quadraticFiniteTransform p (fun a => cuspRoot p a.val) 1 =
      ((quadraticChar (ZMod p)
        (((r % (p : ℤ)).toNat : ℕ) : ZMod p) : ℤ) : ℂ) *
        cuspRootFourierTransform p (quadraticCuspWeight p) r := by
  rw [quadraticCuspTransform_signed]
  exact quadraticFiniteTransform_scale p _ _ hr

/-- At a nonzero signed frequency, the cusp-orbit multiplier is the
quadratic character of that frequency times the positive-phase Gauss sum. -/
theorem quadraticCuspTransform_signed_gauss (p : ℕ) [Fact p.Prime]
    (r : ℤ)
    (hr : (((r % (p : ℤ)).toNat : ℕ) : ZMod p) ≠ 0) :
    cuspRootFourierTransform p (quadraticCuspWeight p) r =
      ((quadraticChar (ZMod p)
        (((r % (p : ℤ)).toNat : ℕ) : ZMod p) : ℤ) : ℂ) *
        gaussSum (quadraticComplexChar p) (ZMod.stdAddChar) := by
  rw [quadraticCuspTransform_signed_addChar]
  rw [quadraticFiniteTransform_scale_forward p _ _ hr]
  rw [quadraticFiniteTransform_one_eq_gaussSum]

/-- The quadratic cusp transform at every signed index. Its value is zero
when the prime divides the index, including negative pole indices. -/
theorem quadraticCuspTransform_signed_gauss_all (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) (r : ℤ) :
    cuspRootFourierTransform p (quadraticCuspWeight p) r =
      ((quadraticChar (ZMod p)
        (((r % (p : ℤ)).toNat : ℕ) : ZMod p) : ℤ) : ℂ) *
        gaussSum (quadraticComplexChar p) (ZMod.stdAddChar) := by
  let s : ZMod p := (((r % (p : ℤ)).toNat : ℕ) : ZMod p)
  by_cases hs : s = 0
  · rw [quadraticCuspTransform_signed_addChar]
    change quadraticFiniteTransform p (fun a => (ZMod.stdAddChar a : ℂ)) s =
      ((quadraticChar (ZMod p) s : ℤ) : ℂ) *
        gaussSum (quadraticComplexChar p) (ZMod.stdAddChar)
    rw [hs, quadraticFiniteTransform_zero p hp]
    simp
  · exact quadraticCuspTransform_signed_gauss p r hs

/-- After division by the nonzero Gauss factor, the actual signed cusp
multiplier is the quadratic character, including zero frequency. -/
theorem quadraticCuspTransform_signed_normalized (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) (r : ℤ) :
    quadraticCuspGaussNormalizer p *
      cuspRootFourierTransform p (quadraticCuspWeight p) r =
      ((quadraticChar (ZMod p)
        ((((r % (p : ℤ)).toNat : ℕ) : ZMod p)) : ℤ) : ℂ) := by
  rw [quadraticCuspTransform_signed_gauss_all p hp]
  calc
    quadraticCuspGaussNormalizer p *
        (((quadraticChar (ZMod p)
          ((((r % (p : ℤ)).toNat : ℕ) : ZMod p)) : ℤ) : ℂ) *
          gaussSum (quadraticComplexChar p) (ZMod.stdAddChar)) =
      ((quadraticChar (ZMod p)
        ((((r % (p : ℤ)).toNat : ℕ) : ZMod p)) : ℤ) : ℂ) *
        (quadraticCuspGaussNormalizer p *
          gaussSum (quadraticComplexChar p) (ZMod.stdAddChar)) := by ring
    _ = _ := by rw [quadraticCuspGaussNormalizer_mul p hp]; ring

/-- The middle analytic summand has a convergent Fourier row whose
multiplier is the finite-field quadratic transform at the signed index.
This leaves the weak-modular-form transformation as a separate question. -/
theorem InverseEtaFourierForm.hasSum_squareIndexAnalyticMiddleQuadratic
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (hm : m.Coprime 6) (p : ℕ) [Fact p.Prime]
    (τ : UpperHalfPlane) :
    HasSum (fun k : ℕ =>
      ((A (24 * (k : ℤ) - (m : ℤ) ^ 2) : ℂ) *
        Function.Periodic.qParam 1 τ ^ k) *
      quadraticFiniteTransform p (fun a => cuspRoot p a.val)
        (((24 * (k : ℤ) - (m : ℤ) ^ 2) % (p : ℤ)).toNat : ZMod p))
      (Function.Periodic.qParam 1 τ ^ ((m * m) / 24) *
        Function.Periodic.qParam 24 τ *
        squareIndexAnalyticSum row.form p (Fact.out : p.Prime).pos
          (quadraticCuspWeight p) 0 1 0 τ) := by
  simpa only [quadraticCuspTransform_signed] using
    row.hasSum_squareIndexAnalyticMiddleTransform hm p
      (Fact.out : p.Prime).pos (quadraticCuspWeight p) τ

/-- The middle analytic Hecke summand has the precise quadratic-character
Fourier row, including the zero frequencies and negative pole indices. The
remaining scalar and modular transformation belong to the prime Hecke law. -/
theorem InverseEtaFourierForm.hasSum_squareIndexAnalyticMiddleGauss
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (hm : m.Coprime 6) (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (τ : UpperHalfPlane) :
    HasSum (fun k : ℕ =>
      ((A (24 * (k : ℤ) - (m : ℤ) ^ 2) : ℂ) *
        Function.Periodic.qParam 1 τ ^ k) *
      (((quadraticChar (ZMod p)
        ((((24 * (k : ℤ) - (m : ℤ) ^ 2) % (p : ℤ)).toNat : ℕ) : ZMod p) : ℤ) : ℂ) *
        gaussSum (quadraticComplexChar p) (ZMod.stdAddChar)))
      (Function.Periodic.qParam 1 τ ^ ((m * m) / 24) *
        Function.Periodic.qParam 24 τ *
        squareIndexAnalyticSum row.form p (Fact.out : p.Prime).pos
          (quadraticCuspWeight p) 0 1 0 τ) := by
  simpa only [quadraticCuspTransform_signed_gauss_all p hp] using
    row.hasSum_squareIndexAnalyticMiddleTransform hm p
      (Fact.out : p.Prime).pos (quadraticCuspWeight p) τ

/-- The Gauss-normalized middle analytic summand has exactly the signed
quadratic-character Fourier multiplier. Its eta-character and weight factors
remain explicit in the eventual full Hecke operator. -/
theorem InverseEtaFourierForm.hasSum_squareIndexAnalyticMiddleNormalized
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (hm : m.Coprime 6) (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (τ : UpperHalfPlane) :
    HasSum (fun k : ℕ =>
      ((A (24 * (k : ℤ) - (m : ℤ) ^ 2) : ℂ) *
        Function.Periodic.qParam 1 τ ^ k) *
      ((quadraticChar (ZMod p)
        ((((24 * (k : ℤ) - (m : ℤ) ^ 2) % (p : ℤ)).toNat : ℕ) : ZMod p) : ℤ) : ℂ))
      (Function.Periodic.qParam 1 τ ^ ((m * m) / 24) *
        Function.Periodic.qParam 24 τ *
        squareIndexAnalyticSum row.form p (Fact.out : p.Prime).pos
          (quadraticCuspWeight p) 0 (quadraticCuspGaussNormalizer p) 0 τ) := by
  have hs := (row.hasSum_squareIndexAnalyticMiddleGauss hm p hp τ).mul_left
    (quadraticCuspGaussNormalizer p)
  convert hs using 1
  · funext k
    let x : ℂ := (A (24 * (k : ℤ) - (m : ℤ) ^ 2) : ℂ) *
      Function.Periodic.qParam 1 τ ^ k
    let c : ℂ := ((quadraticChar (ZMod p)
      ((((24 * (k : ℤ) - (m : ℤ) ^ 2) % (p : ℤ)).toNat : ℕ) : ZMod p) : ℤ) : ℂ)
    let g : ℂ := gaussSum (quadraticComplexChar p) (ZMod.stdAddChar)
    change x * c = quadraticCuspGaussNormalizer p * (x * (c * g))
    calc
      x * c = x * c * (quadraticCuspGaussNormalizer p * g) := by
        rw [quadraticCuspGaussNormalizer_mul p hp]
        ring
      _ = _ := by ring
  · simp only [squareIndexAnalyticSum_eq, zero_mul, zero_add, add_zero,
      one_mul]
    ring

/-- Reexpress the Gauss-normalized middle Hecke row at the new square pole.
The initial coefficients vanish by the old row's pole support, and the
signed quadratic-character index is preserved by the shift. This includes
primes already dividing `m` [rolenManuscript, §3]. -/
theorem InverseEtaFourierForm.hasSum_squareIndexMiddleTarget
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (hm : m.Coprime 6) (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) (hp6 : p.Coprime 6)
    (τ : UpperHalfPlane) :
    HasSum (fun j : ℕ =>
      ((A (24 * (j : ℤ) - (m * p : ℤ) ^ 2) : ℂ) *
        Function.Periodic.qParam 1 τ ^ j) *
      ((quadraticChar (ZMod p)
        ((((24 * (j : ℤ) - (m * p : ℤ) ^ 2) % (p : ℤ)).toNat : ℕ) : ZMod p) : ℤ) : ℂ))
      (Function.Periodic.qParam 1 τ ^ (((m * p) * (m * p)) / 24) *
        Function.Periodic.qParam 24 τ *
        squareIndexAnalyticSum row.form p (Fact.out : p.Prime).pos
          (quadraticCuspWeight p) 0 (quadraticCuspGaussNormalizer p) 0 τ) := by
  let z := Function.Periodic.qParam 1 τ
  let s := inverseEtaMiddlePoleShift m p
  let a : ℕ → ℂ := fun k =>
    (A (24 * (k : ℤ) - (m : ℤ) ^ 2) : ℂ) *
      ((quadraticChar (ZMod p)
        ((((24 * (k : ℤ) - (m : ℤ) ^ 2) % (p : ℤ)).toNat : ℕ) : ZMod p) : ℤ) : ℂ)
  let E := squareIndexAnalyticSum row.form p (Fact.out : p.Prime).pos
    (quadraticCuspWeight p) 0 (quadraticCuspGaussNormalizer p) 0 τ
  have hsource :
      HasSum (fun k : ℕ => a k * z ^ k)
        (z ^ ((m * m) / 24) * Function.Periodic.qParam 24 τ * E) := by
    convert row.hasSum_squareIndexAnalyticMiddleNormalized hm p hp τ using 1
    funext k
    dsimp [a, z]
    ring
  have hshift := hasSum_shifted_powers s a z
    (z ^ ((m * m) / 24) * Function.Periodic.qParam 24 τ * E) hsource
  convert hshift using 1
  · funext j
    by_cases hj : s ≤ j
    · have hi := inverseEtaMiddleIndex_after_shift m p j hp6 hj
      simp only [if_pos hj]
      dsimp [a, z]
      rw [hi]
      ring
    · have hzero := row.support.middle_zero_before_shift p j hp6
        (Nat.lt_of_not_ge hj)
      simp only [if_neg hj]
      rw [hzero]
      ring
  · dsimp [s, z, E]
    rw [← inverseEtaMiddlePoleShift_exponent m p hm hp6, pow_add]
    ring

/-- The signed quadratic character used by the cusp transform is the
Legendre symbol of the same integer index. -/
theorem legendreSym_eq_quadraticCuspIndex (p : ℕ) [Fact p.Prime]
    (r : ℤ) :
    legendreSym p r =
      quadraticChar (ZMod p)
        ((((r % (p : ℤ)).toNat : ℕ) : ZMod p)) := by
  change quadraticChar (ZMod p) (r : ZMod p) = _
  congr 1
  have hp : 0 < (p : ℤ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hnonneg : 0 ≤ r % (p : ℤ) := Int.emod_nonneg _ (by omega)
  calc
    (r : ZMod p) = ((r % (p : ℤ) : ℤ) : ZMod p) :=
      (ZMod.intCast_mod r p).symm
    _ = (((r % (p : ℤ)).toNat : ℕ) : ZMod p) := by
      rw [← Int.toNat_of_nonneg hnonneg]
      simp

/-- The Gauss-normalized middle cusp summand has exactly the weight `-1/2`
Hecke middle coefficient at the shifted square pole. This includes negative
indices and primes dividing the earlier Hecke index. The modularity of the
full three-term sum is a separate obligation. -/
theorem InverseEtaFourierForm.hasSum_squareIndexMiddleHeckeTarget
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (hm : m.Coprime 6) (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) (hp6 : p.Coprime 6)
    (τ : UpperHalfPlane) :
    HasSum (fun j : ℕ =>
      ((etaHeckeDiagonal p (24 * (j : ℤ) - (m * p : ℤ) ^ 2) /
        (p : ℚ) ^ 2 *
        A (24 * (j : ℤ) - (m * p : ℤ) ^ 2) : ℚ) : ℂ) *
          Function.Periodic.qParam 1 τ ^ j)
      (Function.Periodic.qParam 1 τ ^ (((m * p) * (m * p)) / 24) *
        Function.Periodic.qParam 24 τ *
        ((etaHeckeMiddleScalar p : ℂ) *
          squareIndexAnalyticSum row.form p (Fact.out : p.Prime).pos
            (quadraticCuspWeight p) 0 (quadraticCuspGaussNormalizer p) 0 τ)) := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hcoeff (r : ℤ) :
      (((etaHeckeDiagonal p r / (p : ℚ) ^ 2 * A r : ℚ) : ℂ)) =
        (etaHeckeMiddleScalar p : ℂ) * (A r : ℂ) *
          ((quadraticChar (ZMod p)
            ((((r % (p : ℤ)).toNat : ℕ) : ZMod p)) : ℤ) : ℂ) := by
    rw [etaHeckeDiagonal_div_square p hodd r,
      legendreSym_eq_quadraticCuspIndex p r]
    push_cast
    ring
  have hs := (row.hasSum_squareIndexMiddleTarget hm p hp hp6 τ).mul_left
    (etaHeckeMiddleScalar p : ℂ)
  convert hs using 1
  · funext j
    rw [hcoeff]
    ring
  · ring

/-- The analytic three-term expression with the exact weight `-1/2`
coefficient normalization. Its Fourier row is established below; modular
transformation of this expression is a separate obligation. -/
noncomputable def inverseEtaPrimeAnalyticHeckeStep
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (p : ℕ) [Fact p.Prime] : UpperHalfPlane → ℂ :=
  squareIndexAnalyticSum row.form p (Fact.out : p.Prime).pos
    (quadraticCuspWeight p)
    (((p * p : ℕ) : ℂ)⁻¹)
    ((etaHeckeMiddleScalar p : ℂ) * quadraticCuspGaussNormalizer p)
    (((1 / (p : ℚ) ^ 3 : ℚ) : ℂ))

/-- The three analytic prime Hecke orbits with their explicit coefficient
normalizations. -/
theorem inverseEtaPrimeAnalyticHeckeStep_eq
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (p : ℕ) [Fact p.Prime] (τ : UpperHalfPlane) :
    inverseEtaPrimeAnalyticHeckeStep row p τ =
      ((p : ℂ) ^ 2)⁻¹ *
        (∑ j ∈ Finset.range (p * p),
          row.form (cuspAffinePoint (p * p) j
            (Nat.mul_pos (Fact.out : p.Prime).pos (Fact.out : p.Prime).pos) τ)) +
      ((etaHeckeMiddleScalar p : ℂ) * quadraticCuspGaussNormalizer p) *
        (∑ j ∈ Finset.range p,
          quadraticCuspWeight p j *
            row.form (cuspFractionTranslate p j (Fact.out : p.Prime).pos τ)) +
      ((1 / (p : ℚ) ^ 3 : ℚ) : ℂ) *
        row.form (natDilation (p * p)
          (Nat.mul_pos (Fact.out : p.Prime).pos (Fact.out : p.Prime).pos) τ) := by
  rw [inverseEtaPrimeAnalyticHeckeStep, squareIndexAnalyticSum_eq]
  simp only [Nat.cast_mul, pow_two]

/-- The concrete prime Hecke expression is holomorphic on the upper half-plane. -/
theorem InverseEtaFourierForm.primeAnalyticHeckeStep_holomorphic
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (p : ℕ) [Fact p.Prime] :
    MDiff (inverseEtaPrimeAnalyticHeckeStep row p) := by
  exact row.form.squareIndexAnalyticSum_holomorphic p
    (Fact.out : p.Prime).pos _ _ _ _

/-- The concrete prime Hecke expression has a meromorphic period-24 cusp germ. -/
theorem InverseEtaFourierForm.primeAnalyticHeckeStep_meromorphicCusp
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (p : ℕ) [Fact p.Prime] :
    ∃ H : ℂ → ℂ, MeromorphicAt H 0 ∧
      ∀ τ : UpperHalfPlane,
        H (Function.Periodic.qParam 24 τ) =
          inverseEtaPrimeAnalyticHeckeStep row p τ := by
  exact row.form.has_meromorphic_cusp_squareIndexAnalyticSum p
    (Fact.out : p.Prime).pos _ _ _ _

/-- The translation generator acts with the inverse eta multiplier on the
concrete prime Hecke expression. -/
theorem InverseEtaFourierForm.primeAnalyticHeckeStep_translation
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (p : ℕ) [Fact p.Prime] (hp6 : p.Coprime 6)
    (τ : UpperHalfPlane) :
    inverseEtaPrimeAnalyticHeckeStep row p (upperUnipotent 1 • τ) =
      (Complex.exp (Real.pi * Complex.I / 12))⁻¹ *
        inverseEtaPrimeAnalyticHeckeStep row p τ := by
  exact row.form.squareIndexAnalyticSum_translation p
    (Fact.out : p.Prime).pos hp6 _ _ _ _ τ

/-- The Hecke coefficient row retains its lower square-pole bound. -/
theorem InverseEtaFourierForm.primeAnalyticHeckeStep_support
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (p : ℕ) [Fact p.Prime] :
    SquarePoleSupported (m * p) (heckeMinusHalf p A) :=
  row.support.heckeMinusHalf p (Fact.out : p.Prime).pos

/-- The affine, quadratic Gauss, and dilation rows add to the actual
single-prime weight `-1/2` Hecke coefficient action, including signed indices
and primes already dividing the earlier Hecke index [rolenManuscript, §3]. -/
theorem InverseEtaFourierForm.hasSum_primeAnalyticHeckeStep
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (hm : m.Coprime 6) (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) (hp6 : p.Coprime 6)
    (τ : UpperHalfPlane) :
    HasSum (fun j : ℕ =>
      ((heckeMinusHalf p A (24 * (j : ℤ) - (m * p : ℤ) ^ 2) : ℚ) : ℂ) *
        Function.Periodic.qParam 1 τ ^ j)
      (Function.Periodic.qParam 1 τ ^ (((m * p) * (m * p)) / 24) *
        Function.Periodic.qParam 24 τ *
          inverseEtaPrimeAnalyticHeckeStep row p τ) := by
  have hA := row.hasSum_squareIndexAffineTarget hm p hp6
    (Fact.out : p.Prime).pos τ
  have hM := row.hasSum_squareIndexMiddleHeckeTarget hm p hp hp6 τ
  have hD := (row.hasSum_squareDownDilation hm p
    (Fact.out : p.Prime).pos hp6 τ).mul_left
      (((1 / (p : ℚ) ^ 3 : ℚ) : ℂ))
  have hsum := (hA.add hM).add hD
  convert hsum using 1
  · funext j
    rw [heckeMinusHalf_eq_squareHecke, squareHecke_apply]
    push_cast
    ring
  · simp only [inverseEtaPrimeAnalyticHeckeStep, squareIndexAnalyticSum_eq,
      zero_mul, zero_add, add_zero, one_mul]
    ring

end SptClassification.QSeries
