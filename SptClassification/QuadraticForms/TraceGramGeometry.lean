/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.ConditionalSeparationGeometry
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.Orientation

/-!
# The positive trace Gram bound

A real realization of the reduced-trace pairing as the ordinary inner product
on four-dimensional Euclidean space supplies the Hadamard inequality used in
the CM separation argument. The result applies to dependent families as well.
The trace normalization is that of [rolen2026canonical, Lemma 5.2].
-/

public section

open scoped RealInnerProductSpace

namespace SptClassification
namespace ConditionalCM

/-- Gram's determinant is bounded by the product of its diagonal entries in
real Euclidean dimension four. -/
theorem gram_det_le_prod_diagonal (w : Fin 4 → EuclideanSpace ℝ (Fin 4)) :
    (Matrix.gram ℝ w).det ≤ ∏ i : Fin 4, inner ℝ (w i) (w i) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 4) := ⟨by simp⟩
  let b := EuclideanSpace.basisFun (Fin 4) ℝ
  have hdet : (Matrix.gram ℝ w).det = (b.toBasis.det w) ^ 2 := by
    rw [Matrix.gram_eq_conjTranspose_mul b w, Matrix.det_mul,
      Matrix.det_conjTranspose]
    change (b.toBasis.det w) * (b.toBasis.det w) = (b.toBasis.det w) ^ 2
    ring
  have hvol : |b.toBasis.det w| ≤ ∏ i : Fin 4, ‖w i‖ := by
    simpa only [(b.toBasis.orientation).volumeForm_robust' b w] using
      (b.toBasis.orientation).abs_volumeForm_apply_le w
  have hsq : (b.toBasis.det w) ^ 2 ≤ (∏ i : Fin 4, ‖w i‖) ^ 2 := by
    have hnonneg : 0 ≤ ∏ i : Fin 4, ‖w i‖ := by positivity
    nlinarith [abs_nonneg (b.toBasis.det w), sq_abs (b.toBasis.det w)]
  have hprod : (∏ i : Fin 4, inner ℝ (w i) (w i)) =
      (∏ i : Fin 4, ‖w i‖) ^ 2 := by
    simp_rw [real_inner_self_eq_norm_sq]
    exact Finset.prod_pow Finset.univ 2 (fun i : Fin 4 => ‖w i‖)
  rw [hdet, hprod]
  exact hsq

/-- A universal covolume bound derived from an exact positive trace
realization; no determinant bound is included among the hypotheses. -/
theorem trace_covolume_le_of_realization {H : Type*} [DivisionRing H]
    (reducedTrace : H → ℝ) (conj : H → H)
    (rho : H → EuclideanSpace ℝ (Fin 4))
    (hrho : ∀ x y : H, inner ℝ (rho x) (rho y) = reducedTrace (x * conj y))
    (v : Fin 4 → H) :
    traceCovolume reducedTrace conj v ≤
      Real.sqrt (∏ i : Fin 4, reducedTrace (v i * conj (v i))) := by
  have hgram : Matrix.gram ℝ (rho ∘ v) =
      (fun i j : Fin 4 => reducedTrace (v i * conj (v j))) := by
    ext i j
    exact hrho (v i) (v j)
  have hdiag : (∏ i : Fin 4, inner ℝ (rho (v i)) (rho (v i))) =
      ∏ i : Fin 4, reducedTrace (v i * conj (v i)) := by
    simp_rw [hrho]
  rw [traceCovolume_eq]
  rw [← hgram, ← hdiag]
  exact Real.sqrt_le_sqrt (gram_det_le_prod_diagonal (rho ∘ v))

end ConditionalCM
end SptClassification
