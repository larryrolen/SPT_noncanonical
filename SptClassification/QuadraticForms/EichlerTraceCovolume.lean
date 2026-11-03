/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.ConditionalSeparationGeometry
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Trace covolume of a rank-four sublattice

In an integral basis of an Eichler order, the Gram matrix of four order
elements is obtained by conjugating the basis Gram matrix by their integral
coordinate matrix. Its covolume is therefore the absolute determinant of the
coordinate matrix times the covolume of the order. This is the lattice-index
step in [rolen2026canonical, Lemma 5.2]. The identification of a particular
endomorphism order and its discriminant is separate geometric input.
-/

public section

namespace SptClassification
namespace ConditionalCM

/-- Four elements with independent integral coordinates have trace covolume at
least `6p` when their ambient rank-four order has trace discriminant
`(6p)²`. The Gram compatibility equation records the change of integral
basis; the theorem proves the ensuing index bound. -/
theorem traceCovolume_ge_of_integral_basis
    {H : Type*} [DivisionRing H]
    (reducedTrace : H → ℝ) (conj : H → H) (v : Fin 4 → H)
    (p : ℕ) (basisGram : Matrix (Fin 4) (Fin 4) ℝ)
    (coordinates : Matrix (Fin 4) (Fin 4) ℤ)
    (hdisc : basisGram.det = (6 * (p : ℝ)) ^ 2)
    (hind : coordinates.det ≠ 0)
    (hgram : (fun i j : Fin 4 => reducedTrace (v i * conj (v j))) =
      (coordinates.map (Int.castRingHom ℝ)) * basisGram *
        (coordinates.map (Int.castRingHom ℝ)).transpose) :
    6 * (p : ℝ) ≤ traceCovolume reducedTrace conj v := by
  have hcast : (coordinates.map (Int.castRingHom ℝ)).det =
      (coordinates.det : ℝ) := by
    exact (RingHom.map_det (Int.castRingHom ℝ) coordinates).symm
  have hdet : (Matrix.det (fun i j : Fin 4 => reducedTrace (v i * conj (v j)))) =
      ((coordinates.det : ℝ) * (6 * (p : ℝ))) ^ 2 := by
    rw [hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
      hcast, hdisc]
    ring
  have hcov : traceCovolume reducedTrace conj v =
      |(coordinates.det : ℝ)| * (6 * (p : ℝ)) := by
    have hp : 0 ≤ (6 : ℝ) * (p : ℝ) :=
      mul_nonneg (by norm_num) (Nat.cast_nonneg p)
    rw [traceCovolume_eq]
    rw [hdet, Real.sqrt_sq_eq_abs, abs_mul, abs_of_nonneg hp]
  have hindex : (1 : ℝ) ≤ |(coordinates.det : ℝ)| := by
    have hindexZ : 1 ≤ |coordinates.det| := by
      rcases lt_trichotomy coordinates.det 0 with hneg | hzero | hpos
      · rw [abs_of_neg hneg]
        omega
      · exact (hind hzero).elim
      · rw [abs_of_nonneg (le_of_lt hpos)]
        omega
    exact_mod_cast hindexZ
  rw [hcov]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hindex
    (mul_nonneg (by norm_num) (Nat.cast_nonneg p))

end ConditionalCM
end SptClassification
