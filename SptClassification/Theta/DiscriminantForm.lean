/- Assembled by AxiomProver. -/

module

public import SptClassification.Theta.Lattice

/-!
# The discriminant form of the Shimura lattice

For the lattice of [rolenManuscript, lines 336–353], the bilinear dual has
coordinates `(a, r / 12, c)` with integral `a`, `r`, and `c`. The residue of
`r` gives its class in `ℤ/12ℤ`; its norm modulo `ℤ` is `r²/24`.
-/

public section

namespace SptClassification
namespace Theta

/-- Integral coordinates for a vector in the bilinear dual. -/
@[ext] structure DualCoordinates where
  a : ℤ
  r : ℤ
  c : ℤ

@[expose]
def DualCoordinates.toSpace (x : DualCoordinates) : Space :=
  ⟨x.a, (x.r : ℚ) / 12, x.c⟩

theorem DualCoordinates.mem (x : DualCoordinates) : x.toSpace ∈ dualLattice := by
  exact (inDual_iff _).2 ⟨x.a, x.r, x.c, rfl, rfl, rfl⟩

theorem dual_has_coordinates (x : Space) (hx : x ∈ dualLattice) :
    ∃ y : DualCoordinates, y.toSpace = x := by
  obtain ⟨a, r, c, ha, hr, hc⟩ := (inDual_iff x).1 hx
  refine ⟨⟨a, r, c⟩, ?_⟩
  ext <;> simp [DualCoordinates.toSpace, ha, hr, hc]

theorem DualCoordinates.quadratic_eq (x : DualCoordinates) :
    quadratic x.toSpace = (x.r : ℚ) ^ 2 / 24 - x.a * x.c := by
  simp only [quadratic, toSpace]
  ring

/-- The discriminant class is the middle dual coordinate modulo twelve. -/
@[expose]
def DualCoordinates.discriminantClass (x : DualCoordinates) : ZMod 12 := x.r

/-- Equality of residue classes is the equivalence relation on the dual lattice. -/
instance dualCoordinatesSetoid : Setoid DualCoordinates where
  r x y := x.discriminantClass = y.discriminantClass
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun hxy hyz => hxy.trans hyz⟩

/-- The residue relation is exactly difference by an integral lattice vector. -/
theorem DualCoordinates.sameCoset_iff (x y : DualCoordinates) :
    x ≈ y ↔ ∃ z : Lattice,
      x.a = y.a + z.a ∧
      (x.r : ℚ) / 12 = (y.r : ℚ) / 12 + z.b ∧
      x.c = y.c + z.c := by
  constructor
  · intro h
    change (x.r : ZMod 12) = y.r at h
    have hz : ((x.r - y.r : ℤ) : ZMod 12) = 0 := by
      simpa only [Int.cast_sub, sub_eq_zero] using h
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 12).1 hz
    refine ⟨⟨x.a - y.a, k, x.c - y.c⟩, by simp, ?_, by simp⟩
    have hkq : (x.r : ℚ) - y.r = 12 * (k : ℚ) := by
      exact_mod_cast (show x.r - y.r = 12 * k by omega)
    linarith only [hkq]
  · rintro ⟨z, _, hb, _⟩
    have hr : x.r - y.r = 12 * z.b := by
      exact_mod_cast (show (x.r : ℚ) - y.r = 12 * z.b by linarith only [hb])
    have hd : 12 ∣ x.r - y.r := ⟨z.b, by simpa only [mul_comm] using hr⟩
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 12).2 hd
    change (x.r : ZMod 12) = y.r
    simpa only [Int.cast_sub, sub_eq_zero] using hz

/-- A value in `ZMod 24` records a rational norm with denominator 24 modulo `ℤ`. -/
@[expose]
def discriminantQuadratic (r : ZMod 12) : ZMod 24 := (r.val : ZMod 24) ^ 2

/-- The associated pairing has rational value `rs/12` modulo integers. -/
def discriminantPairing (r s : ZMod 12) : ZMod 24 :=
  2 * (r.val : ZMod 24) * (s.val : ZMod 24)

/-- The bilinear numerator can be computed using the product in `ZMod 12`. -/
theorem discriminantPairing_eq (r s : ZMod 12) :
    discriminantPairing r s = 2 * (((r * s).val : ℕ) : ZMod 24) := by
  unfold discriminantPairing
  fin_cases r <;> fin_cases s <;> decide +kernel

theorem discriminantQuadratic_zero : discriminantQuadratic 0 = 0 := by decide

theorem discriminantQuadratic_neg (r : ZMod 12) :
    discriminantQuadratic (-r) = discriminantQuadratic r := by
  fin_cases r <;> decide +kernel

theorem discriminantQuadratic_add (r s : ZMod 12) :
    discriminantQuadratic (r + s) =
      discriminantQuadratic r + discriminantQuadratic s + discriminantPairing r s := by
  fin_cases r <;> fin_cases s <;> decide +kernel

theorem discriminantQuadratic_formula (r : ZMod 12) :
    discriminantQuadratic r = ((r.val : ℤ) ^ 2 : ZMod 24) := by
  simp [discriminantQuadratic]

/-- The norm numerator of an arbitrary dual vector, interpreted modulo twenty-four. -/
def DualCoordinates.normResidue (x : DualCoordinates) : ZMod 24 := (x.r ^ 2 : ℤ)

theorem square_residue_eq_of_twelve_dvd (r s : ℤ) (h : 12 ∣ r - s) :
    ((r ^ 2 : ℤ) : ZMod 24) = ((s ^ 2 : ℤ) : ZMod 24) := by
  obtain ⟨k, hk⟩ := h
  have hr : r = s + 12 * k := by omega
  have hd : 24 ∣ r ^ 2 - s ^ 2 := by
    refine ⟨s * k + 6 * k ^ 2, ?_⟩
    rw [hr]
    ring
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 24).2 hd
  simpa only [Int.cast_sub, sub_eq_zero] using hz

/-- The discriminant quadratic value depends only on the dual vector's coset. -/
theorem DualCoordinates.normResidue_sameCoset (x y : DualCoordinates)
    (h : x ≈ y) : x.normResidue = y.normResidue := by
  have hr : (x.r : ZMod 12) = y.r := h
  have hz : ((x.r - y.r : ℤ) : ZMod 12) = 0 := by
    simpa only [Int.cast_sub, sub_eq_zero] using hr
  exact square_residue_eq_of_twelve_dvd x.r y.r
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 12).1 hz)

theorem normResidue_dualRepresentative (r : ZMod 12) :
    (⟨0, r.val, 0⟩ : DualCoordinates).normResidue = discriminantQuadratic r := by
  simp [DualCoordinates.normResidue, discriminantQuadratic]

/-- The genuine quotient of the bilinear dual by the integral lattice. -/
abbrev DiscriminantGroup := Quotient (inferInstance : Setoid DualCoordinates)

/-- The discriminant group is cyclic of order twelve. -/
def discriminantGroupEquiv : DiscriminantGroup ≃ ZMod 12 where
  toFun := Quotient.lift DualCoordinates.discriminantClass
    (fun _ _ h => h)
  invFun := fun r => Quotient.mk _ (⟨0, r.val, 0⟩ : DualCoordinates)
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
      change (⟦(⟨0, (x.discriminantClass).val, 0⟩ : DualCoordinates)⟧ : DiscriminantGroup) =
        (⟦x⟧ : DiscriminantGroup)
      apply Quotient.sound
      simp [DualCoordinates.discriminantClass]
  right_inv := by
    intro r
    simp [DualCoordinates.discriminantClass]

@[simp] theorem discriminantGroupEquiv_mk (x : DualCoordinates) :
    discriminantGroupEquiv (⟦x⟧ : DiscriminantGroup) = x.discriminantClass := (rfl)

/-- The additive structure on the dual-lattice quotient, transported through its
middle-coordinate residue. -/
instance discriminantGroupAddCommGroup : AddCommGroup DiscriminantGroup :=
  discriminantGroupEquiv.addCommGroup

theorem discriminantGroupEquiv_add (x y : DiscriminantGroup) :
    discriminantGroupEquiv (x + y) = discriminantGroupEquiv x + discriminantGroupEquiv y :=
  Equiv.apply_symm_apply _ _

theorem discriminantGroupEquiv_zero : discriminantGroupEquiv (0 : DiscriminantGroup) = 0 :=
  Equiv.apply_symm_apply _ _

theorem discriminantGroupEquiv_neg (x : DiscriminantGroup) :
    discriminantGroupEquiv (-x) = -discriminantGroupEquiv x :=
  Equiv.apply_symm_apply _ _

theorem discriminantGroup_add_mk (x y : DualCoordinates) :
    (⟦x⟧ : DiscriminantGroup) + ⟦y⟧ =
      ⟦⟨x.a + y.a, x.r + y.r, x.c + y.c⟩⟧ := by
  apply discriminantGroupEquiv.injective
  rw [discriminantGroupEquiv_add]
  change (x.r : ZMod 12) + y.r = ((x.r + y.r : ℤ) : ZMod 12)
  exact (Int.cast_add x.r y.r).symm

/-- The quotient quadratic value, encoded in `ZMod 24` as a multiple of `1/24` modulo `ℤ`. -/
def discriminantGroupNorm : DiscriminantGroup → ZMod 24 :=
  Quotient.lift DualCoordinates.normResidue
    (fun x y h => x.normResidue_sameCoset y h)

theorem discriminantGroupNorm_formula (r : ZMod 12) :
    discriminantGroupNorm (discriminantGroupEquiv.symm r) =
      discriminantQuadratic r := by
  exact normResidue_dualRepresentative r

end Theta
end SptClassification
