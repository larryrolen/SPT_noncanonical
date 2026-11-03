/- Assembled by AxiomProver. -/

module

public import SptClassification.Theta.NegativeVectorForms
public import SptClassification.Theta.WeilVector

/-!
# Atkin–Lehner substitutions on the Shimura lattice

The determinant-two, determinant-three, and Fricke substitutions are represented
by `[[2,1],[6,4]]`, `[[3,1],[6,3]]`, and `[[0,-1],[6,0]]`. Pullback of
`6cX²+rXY+aY²`, divided by the determinant, preserves the dual lattice and
its norm. The induced discriminant actions multiply the residue by `7`, `5`,
and `-1`. This establishes the finite sign calculation used at the four cusps
in [rolenManuscript, lines 350–353]; analytic cusp holomorphy is separate.
-/

public section

namespace SptClassification
namespace Theta

/-- A determinant-two Atkin–Lehner matrix at level six. -/
def atkinLehnerTwoMatrix : Matrix (Fin 2) (Fin 2) ℤ := !![2, 1; 6, 4]

/-- A determinant-three Atkin–Lehner matrix at level six. -/
def atkinLehnerThreeMatrix : Matrix (Fin 2) (Fin 2) ℤ := !![3, 1; 6, 3]

/-- The determinant-six Fricke matrix. -/
def frickeSixMatrix : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; 6, 0]

theorem atkinLehnerTwoMatrix_det : atkinLehnerTwoMatrix.det = 2 := by
  norm_num [atkinLehnerTwoMatrix, Matrix.det_fin_two]

theorem atkinLehnerThreeMatrix_det : atkinLehnerThreeMatrix.det = 3 := by
  norm_num [atkinLehnerThreeMatrix, Matrix.det_fin_two]

theorem frickeSixMatrix_det : frickeSixMatrix.det = 6 := by
  norm_num [frickeSixMatrix, Matrix.det_fin_two]

/-- Normalized pullback by the determinant-two matrix on dual coordinates. -/
def atkinLehnerTwo (x : DualCoordinates) : DualCoordinates :=
  ⟨8 * x.a + 2 * x.r + 3 * x.c,
    24 * x.a + 7 * x.r + 12 * x.c,
    3 * x.a + x.r + 2 * x.c⟩

theorem atkinLehnerTwo_eq (x : DualCoordinates) :
    atkinLehnerTwo x = ⟨8 * x.a + 2 * x.r + 3 * x.c,
      24 * x.a + 7 * x.r + 12 * x.c,
      3 * x.a + x.r + 2 * x.c⟩ := (rfl)

/-- Normalized pullback by the determinant-three matrix on dual coordinates. -/
def atkinLehnerThree (x : DualCoordinates) : DualCoordinates :=
  ⟨3 * x.a + x.r + 2 * x.c,
    12 * x.a + 5 * x.r + 12 * x.c,
    2 * x.a + x.r + 3 * x.c⟩

theorem atkinLehnerThree_eq (x : DualCoordinates) :
    atkinLehnerThree x = ⟨3 * x.a + x.r + 2 * x.c,
      12 * x.a + 5 * x.r + 12 * x.c,
      2 * x.a + x.r + 3 * x.c⟩ := (rfl)

/-- Normalized pullback by the Fricke matrix on dual coordinates. -/
def frickeSix (x : DualCoordinates) : DualCoordinates := ⟨x.c, -x.r, x.a⟩

theorem frickeSix_eq (x : DualCoordinates) :
    frickeSix x = ⟨x.c, -x.r, x.a⟩ := (rfl)

theorem atkinLehnerTwo_binaryForm (x : DualCoordinates) :
    x.binaryForm.pullback atkinLehnerTwoMatrix =
      (atkinLehnerTwo x).binaryForm.scale 2 := by
  ext <;> norm_num [BinaryQuadraticForm.pullback, BinaryQuadraticForm.scale,
    DualCoordinates.binaryForm_eq, atkinLehnerTwoMatrix, atkinLehnerTwo] <;> ring

theorem atkinLehnerThree_binaryForm (x : DualCoordinates) :
    x.binaryForm.pullback atkinLehnerThreeMatrix =
      (atkinLehnerThree x).binaryForm.scale 3 := by
  ext <;> norm_num [BinaryQuadraticForm.pullback, BinaryQuadraticForm.scale,
    DualCoordinates.binaryForm_eq, atkinLehnerThreeMatrix, atkinLehnerThree] <;> ring

theorem frickeSix_binaryForm (x : DualCoordinates) :
    x.binaryForm.pullback frickeSixMatrix = (frickeSix x).binaryForm.scale 6 := by
  ext <;> norm_num [BinaryQuadraticForm.pullback, BinaryQuadraticForm.scale,
    DualCoordinates.binaryForm_eq, frickeSixMatrix, frickeSix] <;> ring

theorem atkinLehnerTwo_norm (x : DualCoordinates) :
    quadratic (atkinLehnerTwo x).toSpace = quadratic x.toSpace := by
  rw [DualCoordinates.quadratic_eq, DualCoordinates.quadratic_eq]
  simp only [atkinLehnerTwo]
  push_cast
  ring

theorem atkinLehnerThree_norm (x : DualCoordinates) :
    quadratic (atkinLehnerThree x).toSpace = quadratic x.toSpace := by
  rw [DualCoordinates.quadratic_eq, DualCoordinates.quadratic_eq]
  simp only [atkinLehnerThree]
  push_cast
  ring

theorem frickeSix_norm (x : DualCoordinates) :
    quadratic (frickeSix x).toSpace = quadratic x.toSpace := by
  rw [DualCoordinates.quadratic_eq, DualCoordinates.quadratic_eq]
  simp only [frickeSix]
  push_cast
  ring

theorem atkinLehnerTwo_discriminantClass (x : DualCoordinates) :
    (atkinLehnerTwo x).discriminantClass = 7 * x.discriminantClass := by
  norm_num [atkinLehnerTwo, DualCoordinates.discriminantClass]
  simp only [show (24 : ZMod 12) = 0 by decide,
    show (12 : ZMod 12) = 0 by decide, zero_mul, zero_add, add_zero]

theorem atkinLehnerThree_discriminantClass (x : DualCoordinates) :
    (atkinLehnerThree x).discriminantClass = 5 * x.discriminantClass := by
  norm_num [atkinLehnerThree, DualCoordinates.discriminantClass]
  simp only [show (12 : ZMod 12) = 0 by decide, zero_mul, zero_add, add_zero]

theorem frickeSix_discriminantClass (x : DualCoordinates) :
    (frickeSix x).discriminantClass = -x.discriminantClass := by
  simp [frickeSix, DualCoordinates.discriminantClass]

theorem discriminantQuadratic_mul_seven (r : ZMod 12) :
    discriminantQuadratic (7 * r) = discriminantQuadratic r := by
  fin_cases r <;> decide +kernel

theorem discriminantQuadratic_mul_five (r : ZMod 12) :
    discriminantQuadratic (5 * r) = discriminantQuadratic r := by
  fin_cases r <;> decide +kernel

theorem weilInputVector_mul_seven (r : ZMod 12) :
    weilInputVector (7 * r) = -weilInputVector r := by
  fin_cases r <;> decide +kernel

theorem weilInputVector_mul_five (r : ZMod 12) :
    weilInputVector (5 * r) = -weilInputVector r := by
  fin_cases r <;> decide +kernel

/-- The Atkin–Lehner action on the actual dual-lattice quotient. -/
def atkinLehnerTwoDiscriminant (q : DiscriminantGroup) : DiscriminantGroup :=
  discriminantGroupEquiv.symm (7 * discriminantGroupEquiv q)

def atkinLehnerThreeDiscriminant (q : DiscriminantGroup) : DiscriminantGroup :=
  discriminantGroupEquiv.symm (5 * discriminantGroupEquiv q)

def frickeSixDiscriminant (q : DiscriminantGroup) : DiscriminantGroup :=
  discriminantGroupEquiv.symm (-discriminantGroupEquiv q)

theorem atkinLehnerTwoDiscriminant_mk (x : DualCoordinates) :
    atkinLehnerTwoDiscriminant (⟦x⟧ : DiscriminantGroup) =
      (⟦atkinLehnerTwo x⟧ : DiscriminantGroup) := by
  apply discriminantGroupEquiv.injective
  simp only [atkinLehnerTwoDiscriminant, Equiv.apply_symm_apply]
  simp only [discriminantGroupEquiv_mk]
  exact (atkinLehnerTwo_discriminantClass x).symm

theorem atkinLehnerThreeDiscriminant_mk (x : DualCoordinates) :
    atkinLehnerThreeDiscriminant (⟦x⟧ : DiscriminantGroup) =
      (⟦atkinLehnerThree x⟧ : DiscriminantGroup) := by
  apply discriminantGroupEquiv.injective
  simp only [atkinLehnerThreeDiscriminant, Equiv.apply_symm_apply]
  simp only [discriminantGroupEquiv_mk]
  exact (atkinLehnerThree_discriminantClass x).symm

theorem frickeSixDiscriminant_mk (x : DualCoordinates) :
    frickeSixDiscriminant (⟦x⟧ : DiscriminantGroup) =
      (⟦frickeSix x⟧ : DiscriminantGroup) := by
  apply discriminantGroupEquiv.injective
  simp only [frickeSixDiscriminant, Equiv.apply_symm_apply]
  simp only [discriminantGroupEquiv_mk]
  exact (frickeSix_discriminantClass x).symm

theorem discriminantGroupNorm_eq (q : DiscriminantGroup) :
    discriminantGroupNorm q = discriminantQuadratic (discriminantGroupEquiv q) := by
  simpa only [Equiv.symm_apply_apply] using
    (discriminantGroupNorm_formula (discriminantGroupEquiv q))

theorem atkinLehnerTwoDiscriminant_norm (q : DiscriminantGroup) :
    discriminantGroupNorm (atkinLehnerTwoDiscriminant q) =
      discriminantGroupNorm q := by
  simp only [discriminantGroupNorm_eq, atkinLehnerTwoDiscriminant,
    Equiv.apply_symm_apply, discriminantQuadratic_mul_seven]

theorem atkinLehnerThreeDiscriminant_norm (q : DiscriminantGroup) :
    discriminantGroupNorm (atkinLehnerThreeDiscriminant q) =
      discriminantGroupNorm q := by
  simp only [discriminantGroupNorm_eq, atkinLehnerThreeDiscriminant,
    Equiv.apply_symm_apply, discriminantQuadratic_mul_five]

theorem frickeSixDiscriminant_norm (q : DiscriminantGroup) :
    discriminantGroupNorm (frickeSixDiscriminant q) =
      discriminantGroupNorm q := by
  simp only [discriminantGroupNorm_eq, frickeSixDiscriminant,
    Equiv.apply_symm_apply, discriminantQuadratic_neg]

theorem atkinLehnerTwoThree_discriminant (q : DiscriminantGroup) :
    atkinLehnerTwoDiscriminant (atkinLehnerThreeDiscriminant q) =
      frickeSixDiscriminant q := by
  apply discriminantGroupEquiv.injective
  simp only [atkinLehnerTwoDiscriminant, atkinLehnerThreeDiscriminant,
    frickeSixDiscriminant, Equiv.apply_symm_apply]
  change 7 * (5 * discriminantGroupEquiv q) = -discriminantGroupEquiv q
  have h : (7 : ZMod 12) * 5 = -1 := by decide
  rw [← mul_assoc, h, neg_one_mul]

/-- The finite sign induced by the determinant-two substitution. -/
theorem atkinLehnerTwo_input_sign (x : DualCoordinates) :
    weilInputVector (atkinLehnerTwo x).discriminantClass =
      -weilInputVector x.discriminantClass := by
  rw [atkinLehnerTwo_discriminantClass, weilInputVector_mul_seven]

/-- The finite sign induced by the determinant-three substitution. -/
theorem atkinLehnerThree_input_sign (x : DualCoordinates) :
    weilInputVector (atkinLehnerThree x).discriminantClass =
      -weilInputVector x.discriminantClass := by
  rw [atkinLehnerThree_discriminantClass, weilInputVector_mul_five]

/-- The Fricke substitution fixes the finite input vector. -/
theorem frickeSix_input_sign (x : DualCoordinates) :
    weilInputVector (frickeSix x).discriminantClass =
      weilInputVector x.discriminantClass := by
  rw [frickeSix_discriminantClass, weilInputVector_neg]

end Theta
end SptClassification
