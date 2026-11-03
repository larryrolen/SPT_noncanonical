/- Assembled by AxiomProver. -/

module

public import SptClassification.Theta.NegativeVectorForms
public import SptClassification.Theta.CuspLattice

/-!
# The period coordinate for the Shimura lattice

The isotropic vector `(-6τ², τ, -1)` fixes the normalization used in
[rolenManuscript, lines 344–350]. Pairing it with `(a,r/12,c)` gives
`6cτ²+rτ+a`, and pairing it with the positive middle vector of index `m`
gives `mτ`. These identities concern the finite-dimensional quadratic space;
they do not assert the analytic Fourier expansion of a lift.
-/

public section

namespace SptClassification
namespace Theta

/-- Complexification of a dual-lattice vector. -/
noncomputable def DualCoordinates.toComplex (x : DualCoordinates) : Vector ℂ :=
  ⟨x.a, (x.r : ℂ) / 12, x.c⟩

theorem DualCoordinates.toComplex_eq (x : DualCoordinates) :
    x.toComplex = ⟨x.a, (x.r : ℂ) / 12, x.c⟩ := (rfl)

/-- Complexification of an integral lattice vector. -/
def Lattice.toComplex (x : Lattice) : Vector ℂ := ⟨x.a, x.b, x.c⟩

/-- Coordinatewise complex scaling, used to identify the rational cusp lines. -/
def complexScale (u : ℂ) (x : Vector ℂ) : Vector ℂ :=
  ⟨u * x.a, u * x.b, u * x.c⟩

theorem complexScale_eq (u : ℂ) (x : Vector ℂ) :
    complexScale u x = ⟨u * x.a, u * x.b, u * x.c⟩ := (rfl)

/-- The complex bilinear extension of the lattice pairing. -/
def complexBilinear (x y : Vector ℂ) : ℂ :=
  12 * x.b * y.b - x.a * y.c - y.a * x.c

/-- The complex quadratic extension of the lattice norm. -/
def complexQuadratic (x : Vector ℂ) : ℂ :=
  6 * x.b ^ 2 - x.a * x.c

/-- The normalized isotropic period vector at `τ`. -/
def periodVector (τ : ℂ) : Vector ℂ := ⟨-6 * τ ^ 2, τ, -1⟩

theorem periodVector_eq (τ : ℂ) : periodVector τ = ⟨-6 * τ ^ 2, τ, -1⟩ :=
  (rfl)

theorem periodVector_isotropic (τ : ℂ) :
    complexQuadratic (periodVector τ) = 0 := by
  simp only [complexQuadratic, periodVector]
  ring

theorem periodVector_zero :
    periodVector 0 = complexScale (-1) secondIsotropic.toComplex := by
  ext <;> norm_num [periodVector, complexScale, Lattice.toComplex, secondIsotropic_eq]

theorem periodVector_half :
    periodVector (1 / 2 : ℂ) =
      complexScale (1 / 2) halfCuspIsotropic.toComplex := by
  ext <;> norm_num [periodVector, complexScale, Lattice.toComplex, halfCuspIsotropic_eq]

theorem periodVector_third :
    periodVector (1 / 3 : ℂ) =
      complexScale (1 / 3) thirdCuspIsotropic.toComplex := by
  ext <;> norm_num [periodVector, complexScale, Lattice.toComplex, thirdCuspIsotropic_eq]

theorem periodVector_pair (x : DualCoordinates) (τ : ℂ) :
    complexBilinear x.toComplex (periodVector τ) =
      6 * (x.c : ℂ) * τ ^ 2 + (x.r : ℂ) * τ + x.a := by
  simp only [complexBilinear, DualCoordinates.toComplex, periodVector]
  ring

theorem infinityDualVector_period_pair (m : ℤ) (τ : ℂ) :
    complexBilinear (infinityDualVector m).toComplex (periodVector τ) =
      (m : ℂ) * τ := by
  rw [periodVector_pair]
  simp [infinityDualVector_eq]

theorem DualCoordinates.period_pair_cmPoint (x : DualCoordinates) (d : ℤ)
    (hd : 0 < d) (hc : 0 < x.c)
    (hnorm : quadratic x.toSpace = -(d : ℚ) / 24) :
    letI : Fact (-d < 0) := ⟨by omega⟩
    complexBilinear x.toComplex
      (periodVector ((x.toLevelSixForm d hc hnorm).cmPoint : ℂ)) = 0 := by
  letI : Fact (-d < 0) := ⟨by omega⟩
  rw [periodVector_pair]
  exact x.evaluate_cmPoint d hd hc hnorm

end Theta
end SptClassification
