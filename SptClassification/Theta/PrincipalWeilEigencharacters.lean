/- Assembled by AxiomProver. -/

module

public import SptClassification.Theta.AtkinLehnerLattice
public import SptClassification.Theta.PrincipalWeilInput
import all SptClassification.Theta.PrincipalWeilInput

/-!
# Atkin–Lehner eigencharacters of the full principal Weil input

The discriminant actions of the determinant-two, determinant-three and
Fricke substitutions act on the entire analytic input by signs `-1`, `-1`
and `1`. These identities supply the input side of the lift covariance in
[borcherds1998, §6, p. 23; Theorem 14.3(3), p. 55], used in
[rolenManuscript, §4]. They hold at every Fourier exponent, not just
the principal part. Covariance of the meromorphic lift is a separate input.
-/

public section

namespace SptClassification.Theta

theorem principalWeilInput_mul_seven (d : ℕ) (τ : UpperHalfPlane)
    (r : ZMod 12) :
    principalWeilInput d τ (7 * r) = -principalWeilInput d τ r := by
  simp only [principalWeilInput_apply, weilInputVectorAs,
    weilInputVector_mul_seven, Int.cast_neg, mul_neg]

theorem principalWeilInput_mul_five (d : ℕ) (τ : UpperHalfPlane)
    (r : ZMod 12) :
    principalWeilInput d τ (5 * r) = -principalWeilInput d τ r := by
  simp only [principalWeilInput_apply, weilInputVectorAs,
    weilInputVector_mul_five, Int.cast_neg, mul_neg]

theorem principalWeilInput_neg (d : ℕ) (τ : UpperHalfPlane)
    (r : ZMod 12) :
    principalWeilInput d τ (-r) = principalWeilInput d τ r := by
  simp only [principalWeilInput_apply, weilInputVectorAs, weilInputVector_neg]

theorem principalWeilCoefficient_mul_seven (d : ℕ) (n : ℤ) (r : ZMod 12) :
    principalWeilCoefficient d n (7 * r) = -principalWeilCoefficient d n r := by
  simp only [principalWeilCoefficient, weilInputVector_mul_seven, mul_neg]

theorem principalWeilCoefficient_mul_five (d : ℕ) (n : ℤ) (r : ZMod 12) :
    principalWeilCoefficient d n (5 * r) = -principalWeilCoefficient d n r := by
  simp only [principalWeilCoefficient, weilInputVector_mul_five, mul_neg]

theorem principalWeilCoefficient_neg (d : ℕ) (n : ℤ) (r : ZMod 12) :
    principalWeilCoefficient d n (-r) = principalWeilCoefficient d n r := by
  simp only [principalWeilCoefficient, weilInputVector_neg]

end SptClassification.Theta
