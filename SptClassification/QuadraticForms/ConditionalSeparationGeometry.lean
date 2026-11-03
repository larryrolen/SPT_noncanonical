/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.ConditionalSeparationAlgebra

/-!
# Geometric input for conditional CM separation

The fields here are the precise CM and Eichler inputs. They record an
integral preserving order and its faithful rational and real realizations,
the action on a cyclic subgroup of order six, and general covolume laws for
rank-four sublattices. No separation inequality is an input.

We follow [rolen2026canonical], section 4 and Lemma 5.2.
-/

public section

namespace SptClassification
namespace ConditionalCM

/-- Covolume for the reduced-trace pairing `Trd(x * conj(y))`.
The square root is taken after the Gram determinant. -/
noncomputable def traceCovolume {H : Type*} [DivisionRing H]
    (reducedTrace : H → ℝ) (conj : H → H) (v : Fin 4 → H) : ℝ :=
  Real.sqrt (Matrix.det (fun i j : Fin 4 => reducedTrace (v i * conj (v j))))

theorem traceCovolume_eq {H : Type*} [DivisionRing H]
    (reducedTrace : H → ℝ) (conj : H → H) (v : Fin 4 → H) :
    traceCovolume reducedTrace conj v =
      Real.sqrt (Matrix.det (fun i j : Fin 4 => reducedTrace (v i * conj (v j)))) := (rfl)

/-- All algebraic and geometric data produced by one common reduced CM root.
The carrier types may vary with the root, as the elliptic curve varies. -/
structure CommonRootAction (d p : ℕ) where
  O : Type
  D : Type
  H : Type
  [ringO : Ring O]
  [divisionD : DivisionRing D]
  [divisionH : DivisionRing H]
  order : PreservingOrder O D
  intoReal : D →+* H
  intoReal_injective : Function.Injective intoReal
  scalar : ℝ →+* H
  scalar_injective : Function.Injective scalar
  scalar_central : ∀ (r : ℝ) (x : H), scalar r * x = x * scalar r
  alpha : O
  beta : O
  normNumber : ℕ
  normNumber_eq : 4 * normNumber = d + 1
  alpha_quadratic : order.intoDivision alpha * order.intoDivision alpha -
    order.intoDivision alpha + (normNumber : D) = 0
  beta_quadratic : order.intoDivision beta * order.intoDivision beta -
    order.intoDivision beta + (normNumber : D) = 0
  alpha_orientation : order.restriction alpha = 0 ∨ order.restriction alpha = 1
  beta_orientation : order.restriction beta = 3 ∨ order.restriction beta = 4
  ordinary : Prop
  ordinary_commutes : ordinary → ∀ x y : O,
    order.intoDivision x * order.intoDivision y =
      order.intoDivision y * order.intoDivision x
  reducedTrace : H → ℝ
  quaternionConj : H → H
  reducedNorm : H → ℝ
  trace_self : ∀ x : H, reducedTrace (x * quaternionConj x) = 2 * reducedNorm x
  norm_one : reducedNorm 1 = 1
  norm_mul : ∀ x y : H, reducedNorm (x * y) = reducedNorm x * reducedNorm y
  norm_alpha : reducedNorm (intoReal (order.intoDivision alpha)) = (normNumber : ℝ)
  norm_beta : reducedNorm (intoReal (order.intoDivision beta)) = (normNumber : ℝ)
  hadamard : ∀ v : Fin 4 → H,
    traceCovolume reducedTrace quaternionConj v ≤
      Real.sqrt (∏ i : Fin 4, reducedTrace (v i * quaternionConj (v i)))
  eichler_lower : ¬ordinary → ∀ v : Fin 4 → O,
    (∀ c : Fin 4 → ℝ,
      (∑ i : Fin 4, scalar (c i) * intoReal (order.intoDivision (v i))) = 0 →
        ∀ i, c i = 0) →
    6 * (p : ℝ) ≤ traceCovolume reducedTrace quaternionConj
      (fun i => intoReal (order.intoDivision (v i)))

/-- A common reduced CM root forces the reverse of the manuscript's strict
separation bound. This uses the general Eichler lattice bound, not an assumed
inequality attached to the particular root. -/
theorem CommonRootAction.bound {d p : ℕ} (R : CommonRootAction d p)
    (hd : 0 < d) : 24 * (p : ℝ) ≤ ((d : ℝ) + 1) ^ 2 := by
  let _ := R.ringO
  let _ := R.divisionD
  let _ := R.divisionH
  let a : R.H := R.intoReal (R.order.intoDivision R.alpha)
  let b : R.H := R.intoReal (R.order.intoDivision R.beta)
  have hnoncommD := oriented_actions_not_commute R.order R.normNumber R.alpha R.beta
    R.alpha_quadratic R.beta_quadratic R.alpha_orientation R.beta_orientation
  have hnoncomm : a * b ≠ b * a := by
    intro h
    exact hnoncommD (R.intoReal_injective (by simpa [a, b, map_mul] using h))
  have hnotOrd : ¬R.ordinary := by
    intro ho
    exact hnoncommD (R.ordinary_commutes ho R.alpha R.beta)
  have hquad : a * a - a + R.scalar (R.normNumber : ℝ) = 0 := by
    have h := congrArg R.intoReal R.alpha_quadratic
    simpa [a, map_add, map_sub, map_mul] using h
  have hnonscalar := quadratic_action_nonscalar R.scalar R.scalar_injective
    d R.normNumber hd R.normNumber_eq a hquad
  let v : Fin 4 → R.O := ![1, R.alpha, R.beta, R.alpha * R.beta]
  let w : Fin 4 → R.H := fun i => R.intoReal (R.order.intoDivision (v i))
  have hw : w = ![1, a, b, a * b] := by
    funext i
    fin_cases i <;> simp [w, v, a, b, map_mul]
  have hind : ∀ c : Fin 4 → ℝ,
      (∑ i : Fin 4, R.scalar (c i) * w i) = 0 → ∀ i, c i = 0 := by
    intro c hc i
    have hc' : R.scalar (c 0) + R.scalar (c 1) * a +
        R.scalar (c 2) * b + R.scalar (c 3) * (a * b) = 0 := by
      simpa [Fin.sum_univ_four, hw] using hc
    obtain ⟨h0, h1, h2, h3⟩ := four_action_coefficients R.scalar
      R.scalar_injective R.scalar_central a b hnonscalar hnoncomm
      (c 0) (c 1) (c 2) (c 3) hc'
    fin_cases i <;> assumption
  have hlow : 6 * (p : ℝ) ≤ traceCovolume R.reducedTrace R.quaternionConj w :=
    R.eichler_lower hnotOrd v hind
  have hhigh := R.hadamard w
  have hdiag0 : R.reducedTrace (w 0 * R.quaternionConj (w 0)) = 2 := by
    rw [show w 0 = (1 : R.H) by simp [hw], R.trace_self, R.norm_one]
    norm_num
  have hdiag1 : R.reducedTrace (w 1 * R.quaternionConj (w 1)) =
      2 * (R.normNumber : ℝ) := by
    rw [show w 1 = a by simp [hw], R.trace_self, R.norm_alpha]
  have hdiag2 : R.reducedTrace (w 2 * R.quaternionConj (w 2)) =
      2 * (R.normNumber : ℝ) := by
    rw [show w 2 = b by simp [hw], R.trace_self, R.norm_beta]
  have hdiag3 : R.reducedTrace (w 3 * R.quaternionConj (w 3)) =
      2 * ((R.normNumber : ℝ) * (R.normNumber : ℝ)) := by
    rw [show w 3 = a * b by simp [hw], R.trace_self, R.norm_mul,
      R.norm_alpha, R.norm_beta]
  have hprod : (∏ i : Fin 4, R.reducedTrace (w i * R.quaternionConj (w i))) =
      (4 * (R.normNumber : ℝ) ^ 2) ^ 2 := by
    rw [Fin.prod_univ_four, hdiag0, hdiag1, hdiag2, hdiag3]
    ring
  have hn : 0 ≤ (R.normNumber : ℝ) := Nat.cast_nonneg _
  have hcov : traceCovolume R.reducedTrace R.quaternionConj w ≤
      4 * (R.normNumber : ℝ) ^ 2 := by
    rw [hprod] at hhigh
    simpa [Real.sqrt_sq (by positivity : 0 ≤ 4 * (R.normNumber : ℝ) ^ 2)] using hhigh
  have hnEq : 4 * (R.normNumber : ℝ) = (d : ℝ) + 1 := by
    exact_mod_cast R.normNumber_eq
  nlinarith

end ConditionalCM
end SptClassification
