/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.EtaAutomorphy
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# The odd-denominator Dedekind eta transformation

The general matrix law is a named literature input. Its phase is stated
explicitly so that applications cannot choose an arbitrary multiplier for
each affine Hecke point [apostol1990, Chapter 3, transformation formula for
Dedekind eta].
-/

public section

namespace SptClassification

open UpperHalfPlane

/-- An integral determinant-one matrix with specified entries. Its entries
are exposed so concrete matrices can be identified by computation. -/
@[expose] def etaMatrix (a b c d : ℤ) (hdet : a * d - b * c = 1) :
    Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  ⟨!![a, b; c, d], by
    rw [Matrix.det_fin_two]
    norm_num
    exact hdet⟩

/-- The phase in the odd positive lower-left-entry eta transformation law. -/
noncomputable def etaOddMatrixPhase (a b c d : ℤ) : ℂ :=
  (jacobiSym d c.toNat : ℂ) *
    Complex.exp (Real.pi * Complex.I *
      (((a + d) * c - b * d * (c ^ 2 - 1) - 3 * c : ℤ) : ℂ) / 12)

/-- In the affine inversion matrices, the exponential part of the eta
multiplier is independent of the affine indices modulo its integral period. -/
theorem etaOddMatrixPhase_affine (n j k : ℕ) (q : ℤ) :
    etaOddMatrixPhase (24 * j) (-q) n (-(24 * k)) =
      (jacobiSym (-(24 * (k : ℤ))) n : ℂ) *
        Complex.exp (-Real.pi * Complex.I * (n : ℂ) / 4) := by
  unfold etaOddMatrixPhase
  simp only [Int.toNat_natCast]
  congr 1
  let r : ℤ := (n : ℤ) * ((j : ℤ) - k) - q * k * ((n : ℤ) ^ 2 - 1)
  have harg : Real.pi * Complex.I *
      (((((24 * j : ℤ) + -(24 * k : ℤ)) * (n : ℤ) -
          (-q) * (-(24 * k : ℤ)) * ((n : ℤ) ^ 2 - 1) - 3 * (n : ℤ)) : ℤ) : ℂ) / 12 =
      2 * Real.pi * Complex.I * (r : ℂ) -
        Real.pi * Complex.I * (n : ℂ) / 4 := by
    dsimp [r]
    push_cast
    ring
  rw [harg, Complex.exp_sub]
  have hperiod : Complex.exp (2 * Real.pi * Complex.I * (r : ℂ)) = 1 := by
    convert Complex.exp_int_mul_two_pi_mul_I r using 1 <;> ring
  have hneg : -Real.pi * Complex.I * (n : ℂ) / 4 =
      -(Real.pi * Complex.I * (n : ℂ) / 4) := by ring
  rw [hperiod, one_div, hneg, Complex.exp_neg]

/-- The classical Dedekind eta transformation for a determinant-one matrix
with odd positive lower-left entry, with the principal square root and Jacobi
symbol phase [apostol1990, Chapter 3, transformation formula for Dedekind eta].
This literature theorem is admitted; its exact citation locator remains unverified. -/
theorem eta_odd_matrix_law (a b c d : ℤ)
    (hdet : a * d - b * c = 1) (hc : 0 < c) (hodd : c % 2 = 1)
    (z : UpperHalfPlane) :
    ModularForm.eta (etaMatrix a b c d hdet • z : UpperHalfPlane) =
      etaOddMatrixPhase a b c d * ((c : ℂ) * z + d).sqrt *
        ModularForm.eta z := by
  sorry

end SptClassification
