/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.CMUniformization
public import SptClassification.QuadraticForms.LevelSixWeierstrass
public import SptClassification.ModularForms.LevelSixEtaQuotient
import Mathlib.Tactic.FieldSimp

/-!
# The invariant of the eta-parametrized level-six equation

Maier's parameter is `s = 72 / t`, where `t` is the manuscript's eta
quotient. Table 4 gives `j(τ)` in terms of `s`; Table 5 instead gives
`j(6τ)`. We use Table 4 and prove the reciprocal substitution algebraically.
This identifies the unmarked invariant, not the cyclic subgroup.
-/

public section

namespace SptClassification

namespace ComplexUniformization

/-- The level-six covering formula [maier2009, §3.1, Table 2, p.11;
§3.2, Table 4, p.12 of arXiv:math/0611041v4]. Maier writes
`s = 2^3*3^2*η(2τ)*η(6τ)^5/(η(τ)^5*η(3τ)) = 72/t`.
His `j` is the usual invariant (`j(i)=1728`) of the lattice
`ℤ + ℤτ`, hence of our equation `y² = x³ - g₂*x/4 - g₃/4`.
The displayed rational identity is written after clearing its denominator.
All upper-half-plane points are allowed; there is no CM hypothesis.
This is a named literature admission, not a marked-moduli identification. -/
theorem levelSix_covering_invariant (L : PeriodPair) (z : UpperHalfPlane)
    (h₁ : L.ω₁ = 1) (h₂ : L.ω₂ = (z : ℂ)) :
    letI := curve_isElliptic L
    let s := 72 / levelSixEtaQuotient (z : ℂ)
    (curve L).j * (s * (s + 8) ^ 3 * (s + 9) ^ 2) =
      (s + 6) ^ 3 * (s ^ 3 + 18 * s ^ 2 + 84 * s + 24) ^ 3 := by
  sorry

end ComplexUniformization

namespace LevelSixWeierstrass

/-- Reciprocal normalization of the two rational covering formulas. -/
theorem reciprocal_invariant_relation {K : Type*} [Field K] [CharZero K]
    (t j : K) (ht : t ≠ 0)
    (h : let s := 72 / t
      j * (s * (s + 8) ^ 3 * (s + 9) ^ 2) =
        (s + 6) ^ 3 * (s ^ 3 + 18 * s ^ 2 + 84 * s + 24) ^ 3) :
    j * (t ^ 6 * (t + 8) ^ 2 * (t + 9) ^ 3) =
      (t + 12) ^ 3 * (t ^ 3 + 252 * t ^ 2 + 3888 * t + 15552) ^ 3 := by
  have heq :
      j * ((72 / t) * (72 / t + 8) ^ 3 * (72 / t + 9) ^ 2) -
          (72 / t + 6) ^ 3 *
            ((72 / t) ^ 3 + 18 * (72 / t) ^ 2 + 84 * (72 / t) + 24) ^ 3 =
        (2985984 / t ^ 12) *
          (j * (t ^ 6 * (t + 8) ^ 2 * (t + 9) ^ 3) -
            (t + 12) ^ 3 * (t ^ 3 + 252 * t ^ 2 + 3888 * t + 15552) ^ 3) := by
    field_simp
    <;> ring
  have hz : (2985984 / t ^ 12) *
      (j * (t ^ 6 * (t + 8) ^ 2 * (t + 9) ^ 3) -
        (t + 12) ^ 3 * (t ^ 3 + 252 * t ^ 2 + 3888 * t + 15552) ^ 3) = 0 := by
    rw [← heq, h, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left
    (div_ne_zero (by norm_num) (pow_ne_zero _ ht)))

end LevelSixWeierstrass

namespace ComplexUniformization

/-- The actual eta value satisfies the explicit family's invariant equation.
The reciprocal substitution and normalization constants are proved here. -/
theorem levelSixEta_invariant_relation (L : PeriodPair) (z : UpperHalfPlane)
    (h₁ : L.ω₁ = 1) (h₂ : L.ω₂ = (z : ℂ)) :
    letI := curve_isElliptic L
    (curve L).j * (LevelSixWeierstrass.curve (levelSixEtaQuotient z)).Δ =
      (LevelSixWeierstrass.curve (levelSixEtaQuotient z)).c₄ ^ 3 := by
  letI := curve_isElliptic L
  apply (LevelSixWeierstrass.j_relation_iff _ _ (by norm_num)).mpr
  exact LevelSixWeierstrass.reciprocal_invariant_relation _ _
    (levelSixEtaQuotient_ne_zero z) (levelSix_covering_invariant L z h₁ h₂)

end ComplexUniformization

namespace LevelSixForm

/-- Applying the generic covering formula to the actual CM period pair. -/
theorem complexCurve_eta_invariant_relation {D : ℤ} {r : ZMod 12}
    [Fact (D < 0)] (Q : LevelSixForm D r) :
    letI := Q.complexCurve_isElliptic
    Q.complexCurve.j * (LevelSixWeierstrass.curve (levelSixEtaQuotient Q.cmPoint)).Δ =
      (LevelSixWeierstrass.curve (levelSixEtaQuotient Q.cmPoint)).c₄ ^ 3 :=
  ComplexUniformization.levelSixEta_invariant_relation Q.periodPair Q.cmPoint
    Q.periodPair_omega_one Q.periodPair_omega_two

end LevelSixForm
end SptClassification
