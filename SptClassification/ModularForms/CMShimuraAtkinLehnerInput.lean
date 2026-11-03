/- Assembled by AxiomProver. -/

module

public import SptClassification.Theta.AtkinLehnerLattice
public import SptClassification.Theta.PrincipalWeilInput

/-!
# Atkin–Lehner signs of the principal part of the Shimura input

The determinant-two and determinant-three lattice substitutions act by `7`
and `5` on the discriminant class; the Fricke substitution acts by negation.
The distinguished Weil vector is respectively odd, odd, and even under these
actions. These negative-coefficient identities are the input calculation used in the
finite-cusp argument of [rolenManuscript, Section 4, lines 350–353]. They
do not assert a transformation law for the analytic Shimura lift.
-/

public section

namespace SptClassification
namespace Theta

/-- The negative principal coefficient is odd under the determinant-two
discriminant action. This is the only negative Fourier row of the input. -/
theorem principalWeilCoefficient_negative_mul_seven (d : ℕ)
    (hd : d % 24 = 23) (n : ℤ) (hn : n < 0) (r : ZMod 12) :
    principalWeilCoefficient d n (7 * r) =
      -principalWeilCoefficient d n r := by
  rw [principalWeilCoefficient_negative d hd n hn,
    principalWeilCoefficient_negative d hd n hn]
  split_ifs <;> simp [weilInputVector_mul_seven]

/-- The actual integral Weil coefficients are odd under the
determinant-three discriminant action. -/
theorem principalWeilCoefficient_negative_mul_five (d : ℕ)
    (hd : d % 24 = 23) (n : ℤ) (hn : n < 0) (r : ZMod 12) :
    principalWeilCoefficient d n (5 * r) =
      -principalWeilCoefficient d n r := by
  rw [principalWeilCoefficient_negative d hd n hn,
    principalWeilCoefficient_negative d hd n hn]
  split_ifs <;> simp [weilInputVector_mul_five]

/-- The Fricke discriminant action fixes the actual integral input. -/
theorem principalWeilCoefficient_negative_neg (d : ℕ)
    (hd : d % 24 = 23) (n : ℤ) (hn : n < 0) (r : ZMod 12) :
    principalWeilCoefficient d n (-r) = principalWeilCoefficient d n r := by
  rw [principalWeilCoefficient_negative d hd n hn,
    principalWeilCoefficient_negative d hd n hn]
  split_ifs <;> simp [weilInputVector_neg]

/-- The constant input coefficient remains zero in each transformed
discriminant class. -/
theorem principalWeilCoefficient_transformed_zero (d : ℕ) (r : ZMod 12) :
    principalWeilCoefficient d 0 (7 * r) = 0 ∧
      principalWeilCoefficient d 0 (5 * r) = 0 ∧
        principalWeilCoefficient d 0 (-r) = 0 := by
  simp only [principalWeilCoefficient_zero, and_self]

end Theta
end SptClassification
