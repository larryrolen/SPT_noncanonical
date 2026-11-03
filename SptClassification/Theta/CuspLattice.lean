/- Assembled by AxiomProver. -/

module

public import SptClassification.Theta.DiscriminantForm

/-!
# Cusp data at infinity for the Shimura lattice

The first and third coordinate axes form a hyperbolic plane, and the middle
axis has bilinear norm twelve. Positive dual vectors on the middle axis have
norm `m²/24`, as used at infinity in [rolenManuscript, lines 344–348].
-/

public section

namespace SptClassification
namespace Theta

def firstIsotropic : Lattice := ⟨1, 0, 0⟩
def secondIsotropic : Lattice := ⟨0, 0, 1⟩
def middleGenerator : Lattice := ⟨0, 1, 0⟩

/-- A primitive isotropic representative of the cusp `1/2`. -/
def halfCuspIsotropic : Lattice := ⟨-3, 1, -2⟩

/-- A primitive isotropic representative of the cusp `1/3`. -/
def thirdCuspIsotropic : Lattice := ⟨-2, 1, -3⟩

theorem secondIsotropic_eq : secondIsotropic = ⟨0, 0, 1⟩ := (rfl)
theorem halfCuspIsotropic_eq : halfCuspIsotropic = ⟨-3, 1, -2⟩ := (rfl)
theorem thirdCuspIsotropic_eq : thirdCuspIsotropic = ⟨-2, 1, -3⟩ := (rfl)

theorem firstIsotropic_norm : integralQuadratic firstIsotropic = 0 := by decide
theorem secondIsotropic_norm : integralQuadratic secondIsotropic = 0 := by decide
theorem middleGenerator_norm : integralQuadratic middleGenerator = 6 := by decide
theorem halfCuspIsotropic_norm : integralQuadratic halfCuspIsotropic = 0 := by decide
theorem thirdCuspIsotropic_norm : integralQuadratic thirdCuspIsotropic = 0 := by decide

theorem halfCuspIsotropic_primitive (n : ℤ) (_hn : n ∣ halfCuspIsotropic.a)
    (hm : n ∣ halfCuspIsotropic.b) (_hc : n ∣ halfCuspIsotropic.c) : n ∣ 1 := by
  simpa [halfCuspIsotropic] using hm

theorem thirdCuspIsotropic_primitive (n : ℤ) (_hn : n ∣ thirdCuspIsotropic.a)
    (hm : n ∣ thirdCuspIsotropic.b) (_hc : n ∣ thirdCuspIsotropic.c) : n ∣ 1 := by
  simpa [thirdCuspIsotropic] using hm

theorem isotropic_pairing :
    bilinear firstIsotropic.toSpace secondIsotropic.toSpace = -1 := by
  norm_num [bilinear, firstIsotropic, secondIsotropic, Lattice.toSpace]

theorem middle_pairing :
    bilinear middleGenerator.toSpace middleGenerator.toSpace = 12 := by
  norm_num [bilinear, middleGenerator, Lattice.toSpace]

theorem middle_orthogonal_first :
    bilinear middleGenerator.toSpace firstIsotropic.toSpace = 0 := by
  norm_num [bilinear, middleGenerator, firstIsotropic, Lattice.toSpace]

theorem middle_orthogonal_second :
    bilinear middleGenerator.toSpace secondIsotropic.toSpace = 0 := by
  norm_num [bilinear, middleGenerator, secondIsotropic, Lattice.toSpace]

/-- A positive dual vector at the infinity cusp, indexed by an integer. -/
def infinityDualVector (m : ℤ) : DualCoordinates := ⟨0, m, 0⟩

theorem infinityDualVector_eq (m : ℤ) :
    infinityDualVector m = ⟨0, m, 0⟩ := (rfl)

theorem infinityDualVector_norm (m : ℤ) :
    quadratic (infinityDualVector m).toSpace = (m : ℚ) ^ 2 / 24 := by
  simp [DualCoordinates.quadratic_eq, infinityDualVector]

theorem infinityDualVector_discriminantClass (m : ℤ) :
    (infinityDualVector m).discriminantClass = (m : ZMod 12) := by
  simp [infinityDualVector, DualCoordinates.discriminantClass]

theorem infinityDualVector_norm_pos {m : ℤ} (hm : m ≠ 0) :
    0 < quadratic (infinityDualVector m).toSpace := by
  rw [infinityDualVector_norm]
  positivity

/-- Orthogonality to the first isotropic axis cuts out the cusp plane `c = 0`. -/
theorem orthogonal_first_iff (x : Space) :
    bilinear x firstIsotropic.toSpace = 0 ↔ x.c = 0 := by
  simp [bilinear, firstIsotropic, Lattice.toSpace]

/-- Orthogonality to both isotropic axes leaves exactly the middle line. -/
theorem orthogonal_hyperbolicPlane_iff (x : Space) :
    bilinear x firstIsotropic.toSpace = 0 ∧
      bilinear x secondIsotropic.toSpace = 0 ↔ x.a = 0 ∧ x.c = 0 := by
  simp [bilinear, firstIsotropic, secondIsotropic, Lattice.toSpace, and_comm]

/-- The positive-norm dual vectors perpendicular to both cusp axes are indexed by
their integral middle coordinate. -/
theorem dual_orthogonal_hyperbolicPlane (x : Space) (hx : x ∈ dualLattice)
    (hfirst : bilinear x firstIsotropic.toSpace = 0)
    (hsecond : bilinear x secondIsotropic.toSpace = 0) :
    ∃ m : ℤ, x = (infinityDualVector m).toSpace := by
  obtain ⟨a, m, c, ha, hb, hc⟩ := (inDual_iff x).1 hx
  have hzero := (orthogonal_hyperbolicPlane_iff x).1 ⟨hfirst, hsecond⟩
  have ha0 : a = 0 := by exact_mod_cast ha.symm.trans hzero.1
  have hc0 : c = 0 := by exact_mod_cast hc.symm.trans hzero.2
  refine ⟨m, ?_⟩
  ext <;> simp [infinityDualVector, DualCoordinates.toSpace, ha, hb, hc,
    ha0, hc0]

end Theta
end SptClassification
