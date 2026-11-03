/- Assembled by AxiomProver. -/

module

public import SptClassification.Theta.DiscriminantForm
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices

/-!
# The level-six action on the lattice dual

The substitution matrix `[[p,q],[6k,s]]` has determinant one. Pulling back
`6cX²+rXY+aY²` gives an integral dual vector. Its middle coordinate is
unchanged modulo twelve, so `Γ₀(6)` acts trivially on the discriminant group.
This is the discriminant-kernel assertion in [rolenManuscript, lines 342–344].
-/

public section

namespace SptClassification
namespace Theta

/-- Integral data for a determinant-one matrix in `Γ₀(6)`. -/
structure LevelSixMatrix where
  p : ℤ
  q : ℤ
  k : ℤ
  s : ℤ
  det_one : p * s - 6 * k * q = 1

/-- Pullback of the quadratic attached to a dual vector. -/
def LevelSixMatrix.act (g : LevelSixMatrix) (x : DualCoordinates) : DualCoordinates :=
  ⟨6 * x.c * g.q ^ 2 + x.r * g.q * g.s + x.a * g.s ^ 2,
   12 * x.c * g.p * g.q + x.r * (g.p * g.s + 6 * g.k * g.q) +
     12 * x.a * g.k * g.s,
   x.c * g.p ^ 2 + x.r * g.p * g.k + 6 * x.a * g.k ^ 2⟩

@[simp] theorem LevelSixMatrix.act_a (g : LevelSixMatrix) (x : DualCoordinates) :
    (g.act x).a = 6 * x.c * g.q ^ 2 + x.r * g.q * g.s + x.a * g.s ^ 2 :=
  (rfl)

@[simp] theorem LevelSixMatrix.act_r (g : LevelSixMatrix) (x : DualCoordinates) :
    (g.act x).r = 12 * x.c * g.p * g.q +
      x.r * (g.p * g.s + 6 * g.k * g.q) + 12 * x.a * g.k * g.s :=
  (rfl)

@[simp] theorem LevelSixMatrix.act_c (g : LevelSixMatrix) (x : DualCoordinates) :
    (g.act x).c = x.c * g.p ^ 2 + x.r * g.p * g.k + 6 * x.a * g.k ^ 2 :=
  (rfl)

theorem LevelSixMatrix.act_norm (g : LevelSixMatrix) (x : DualCoordinates) :
    quadratic (g.act x).toSpace = quadratic x.toSpace := by
  have hscale : quadratic (g.act x).toSpace =
      ((g.p * g.s - 6 * g.k * g.q : ℤ) : ℚ) ^ 2 * quadratic x.toSpace := by
    rw [DualCoordinates.quadratic_eq, DualCoordinates.quadratic_eq]
    dsimp only [act]
    push_cast
    ring
  rw [hscale, g.det_one]
  norm_num

theorem LevelSixMatrix.act_discriminantClass (g : LevelSixMatrix)
    (x : DualCoordinates) :
    (g.act x).discriminantClass = x.discriminantClass := by
  have hp : g.p * g.s = 1 + 6 * g.k * g.q := by
    nlinarith only [g.det_one]
  have hd : 12 ∣ (g.act x).r - x.r := by
    refine ⟨x.c * g.p * g.q + x.r * g.k * g.q + x.a * g.k * g.s, ?_⟩
    dsimp only [act]
    rw [hp]
    ring
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 12).2 hd
  simpa only [DualCoordinates.discriminantClass, Int.cast_sub, sub_eq_zero] using hz

/-- Extract the integral level-six matrix data from an actual `Γ₀(6)` element. -/
def LevelSixMatrix.ofGamma
    (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hg : g ∈ CongruenceSubgroup.Gamma0 6) : LevelSixMatrix := by
  have hzero : ((g 1 0 : ℤ) : ZMod 6) = 0 := hg
  have hd : (6 : ℤ) ∣ g 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 6).1 hzero
  let k : ℤ := (g 1 0) / 6
  have hk : g 1 0 = 6 * k := by
    dsimp only [k]
    simpa only [mul_comm] using (Int.ediv_mul_cancel hd).symm
  refine ⟨g 0 0, g 0 1, k, g 1 1, ?_⟩
  have hdet : (g : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := g.property
  rw [Matrix.det_fin_two] at hdet
  rw [hk] at hdet
  nlinarith only [hdet]

/-- The actual congruence subgroup lies in the discriminant kernel. -/
theorem gamma0_acts_trivially_on_discriminant
    (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hg : g ∈ CongruenceSubgroup.Gamma0 6) (x : DualCoordinates) :
    ((LevelSixMatrix.ofGamma g hg).act x).discriminantClass = x.discriminantClass :=
  (LevelSixMatrix.ofGamma g hg).act_discriminantClass x

/-- Pullback by a level-six matrix induces a well-defined map on dual cosets. -/
def LevelSixMatrix.actOnDiscriminantGroup (g : LevelSixMatrix) :
    DiscriminantGroup → DiscriminantGroup :=
  Quotient.lift (fun x : DualCoordinates => (⟦g.act x⟧ : DiscriminantGroup)) (by
    intro x y h
    apply Quotient.sound
    exact (g.act_discriminantClass x).trans (h.trans (g.act_discriminantClass y).symm))

/-- Every level-six matrix acts as the identity on the actual dual quotient. -/
theorem LevelSixMatrix.actOnDiscriminantGroup_eq_id (g : LevelSixMatrix) :
    g.actOnDiscriminantGroup = id := by
  funext q
  induction q using Quotient.inductionOn with
  | h x =>
    apply Quotient.sound
    exact g.act_discriminantClass x

/-- In particular, each element of `Γ₀(6)` lies in the discriminant kernel. -/
theorem gamma0_discriminant_action_eq_id
    (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hg : g ∈ CongruenceSubgroup.Gamma0 6) :
    (LevelSixMatrix.ofGamma g hg).actOnDiscriminantGroup = id :=
  (LevelSixMatrix.ofGamma g hg).actOnDiscriminantGroup_eq_id

end Theta
end SptClassification
