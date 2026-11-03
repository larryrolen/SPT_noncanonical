/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.RationalEndomorphisms
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Geometric kernels of separable rational endomorphisms

The cardinal below is taken on the actual point-map kernel. A factorization
of prime-to-characteristic multiplication certifies separability, so this
cardinal agrees with isogeny degree in the applications below.
-/

public section

namespace SptClassification.RationalPointMap

variable {F : Type*} [Field F] [DecidableEq F]

/-- The number of geometric points in the kernel; this is not the degree
of an inseparable isogeny. -/
noncomputable def kernelCard (W : WeierstrassCurve F) (f : endomorphismRing W) : ℕ :=
  Nat.card (pointAction W f).ker

/-- A rational left factor through multiplication prime to the characteristic.
On an elliptic curve this certifies that `f` is a separable isogeny. -/
def HasPrimeToCharFactor (p : ℕ) (W : WeierstrassCurve F)
    (f : endomorphismRing W) : Prop :=
  ∃ (m : ℕ) (_ : 0 < m) (_ : ¬p ∣ m) (g : endomorphismRing W), g * f = m

/-- Degree/trace and separable-kernel theorem, in its irreducible quadratic
corollary [silverman2009, Chapter III, §§4,6]. The relation has discriminant
`1-4n < 0`, so the non-scalar endomorphism has degree `n` by its characteristic
polynomial. Also `(1-f)*f=[n]`; as `p ∤ n`, multiplication by `n` is separable,
hence so is `f`, and its geometric kernel has exactly its degree many points.
This is a named general literature interface, not a CM specialization premise.
The section locators are recorded; primary theorem numbers are unverified. -/
theorem kernelCard_eq_of_quadratic [IsAlgClosed F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (W : WeierstrassCurve F) (hW : W.IsElliptic)
    (f : endomorphismRing W) (n : ℕ) (hn : 0 < n) (hpn : ¬p ∣ n)
    (hf : f * f - f + (n : endomorphismRing W) = 0) :
    kernelCard W f = n := by
  sorry

/-- The quadratic relation provides the separability factor itself. -/
theorem hasPrimeToCharFactor_of_quadratic
    (p : ℕ) (W : WeierstrassCurve F) (f : endomorphismRing W)
    (n : ℕ) (hn : 0 < n) (hpn : ¬p ∣ n)
    (hf : f * f - f + (n : endomorphismRing W) = 0) :
    HasPrimeToCharFactor p W f := by
  refine ⟨n, hn, hpn, 1 - f, ?_⟩
  have heq : f * f - f = -(n : endomorphismRing W) := eq_neg_of_add_eq_zero_left hf
  calc
    (1 - f) * f = -(f * f - f) := by rw [sub_mul, one_mul, neg_sub]
    _ = n := by rw [heq, neg_neg]

end SptClassification.RationalPointMap
