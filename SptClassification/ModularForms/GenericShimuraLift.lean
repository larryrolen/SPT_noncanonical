/- Assembled by AxiomProver. -/

module

public import SptClassification.Theta.PrincipalWeilInput
public import SptClassification.ModularForms.IntegralShimuraLambert
public import SptClassification.ModularForms.LevelSixFiniteCuspCharts
public import Mathlib.Analysis.Meromorphic.Order

/-!
# The signature `(2, 1)` weight-four Shimura lift

The lattice is `Theta.Lattice`, with quadratic form `6b²-ac`, discriminant
group `ZMod 12`, and the distinguished vector `weilInputVector`. The theorem
below is a literature interface for the weight-`5/2` to weight-four lift,
independent of a CM discriminant. It records the Fourier normalization only
in a sufficiently high cusp region, and keeps the coefficient-sensitive pole
support visible. [borcherds1998, Section 6, printed p. 23, Theorem 14.3(3),
printed p. 55, and Example 14.4, printed p. 59] [liZemel2018, Theorem 5.1,
PDF p. 14]. Atkin–Lehner covariance is stated for the full Weil input; its
eigenvalues follow from the checked discriminant-group action on `v`.
-/

public section

namespace SptClassification

/-- The divisor-sum row of the level-six signature `(2, 1)` lift of a scalar
weight-`5/2` input multiplied by the distinguished Weil vector. -/
noncomputable def signature21ShimuraRow (c : ℤ → ℤ) (n : ℕ) : ℤ :=
  ∑ m ∈ n.divisors,
    characterTwelve (m : ℤ) * (n / m : ℕ) * c ((m : ℤ) ^ 2)

theorem signature21ShimuraRow_eq (c : ℤ → ℤ) (n : ℕ) :
    signature21ShimuraRow c n =
      ∑ m ∈ n.divisors,
        characterTwelve (m : ℤ) * (n / m : ℕ) * c ((m : ℤ) ^ 2) := (rfl)

/-- Borcherds' meromorphic lift, with Li–Zemel's normalized Fourier row.
The hypotheses express a weakly holomorphic weight-`5/2` Weil input of the
form `f * v`, with its actual Fourier coefficients `c * v`. This interface
records the high-infinity Fourier normalization and interior divisor support.
Theorem 14.3(5) gives expansions at primitive isotropic vectors. Section 6
gives equivariance of the lift under the orthogonal action; the three
determinant-normalized slash equations below specialize this to `f * v`, whose
full Weil vector has the checked Atkin–Lehner signs. Integral descent and
finite cusp clearing require separate arguments. -/
theorem borcherds_signature21_weightFour_lift
    (f : EtaWeaklyHolomorphicForm 2) (c : ℤ → ℤ) (N : ℕ)
    (hFourier : ∀ τ : UpperHalfPlane,
      HasSum (fun m : ℕ =>
        (c (24 * (m : ℤ) - (N : ℤ)) : ℂ) *
          Function.Periodic.qParam 1 τ ^ m)
        (Function.Periodic.qParam 1 τ ^ QSeries.principalIndex N *
          (Function.Periodic.qParam 24 τ)⁻¹ * f τ))
    (hN : N % 24 = 23) (hzero : c 0 = 0) :
    ∃ F : ℂ → ℂ,
      MeromorphicOn F {w | 0 < w.im} ∧
      (∀ (g : CongruenceSubgroup.Gamma0 6) (z : UpperHalfPlane),
        F ((g : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z : UpperHalfPlane) =
          UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ
            (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)) z ^ 4 * F z) ∧
      (∀ (cusp : FiniteLevelSixCusp) (z : UpperHalfPlane),
        cusp.atkinLehnerMatrix.weightFourSlash F z =
          (cusp.atkinSign : ℂ) * F z) ∧
      (∀ z : UpperHalfPlane,
        (-2 : WithTop ℤ) ≤ meromorphicOrderAt F (z : ℂ)) ∧
      (∀ z : UpperHalfPlane, meromorphicOrderAt F (z : ℂ) < 0 →
        ∃ (x : Theta.DualCoordinates) (n : ℤ), n < 0 ∧
          Theta.quadratic x.toSpace = (n : ℚ) / 24 ∧
          c n * Theta.weilInputVector x.discriminantClass ≠ 0 ∧
          (6 * (x.c : ℂ)) * (z : ℂ) ^ 2 + (x.r : ℂ) * z + x.a = 0) ∧
      ∃ Y : ℝ, ∀ z : UpperHalfPlane, Y < z.im →
        HasSum (fun n : ℕ => (signature21ShimuraRow c n : ℂ) *
          Function.Periodic.qParam 1 z ^ n) (F z) := by
  sorry

end SptClassification
