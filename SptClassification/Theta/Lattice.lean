/- Assembled by AxiomProver. -/

module

public import Mathlib.Tactic

/-!
# The signature (2, 1) lattice used by the Shimura lift

We use the coordinates of [borcherds1998, Theorem 14.3] as normalized in
[rolenManuscript, lines 336–353]. The integral lattice is `ℤ³` with
`Q(a,b,c) = 6b² - ac`. Its associated bilinear form is
`B(x,y) = 12bb' - ac' - a'c`.
-/

public section

namespace SptClassification
namespace Theta

/-- Three coordinates for the rational quadratic space and its integral lattice. -/
@[ext] structure Vector (R : Type*) where
  a : R
  b : R
  c : R

/-- Coordinate identification with the usual threefold product. -/
def vectorProdEquiv (R : Type*) : Vector R ≃ R × R × R where
  toFun x := (x.a, x.b, x.c)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv x := by cases x; rfl
  right_inv p := by cases p with | mk a bc => cases bc; rfl

/-- Coordinatewise addition makes these triples the usual free rank-three additive group. -/
instance vectorAddCommGroup (R : Type*) [AddCommGroup R] : AddCommGroup (Vector R) :=
  (vectorProdEquiv R).addCommGroup

abbrev Lattice := Vector ℤ
abbrev Space := Vector ℚ

/-- The integral lattice included in the rational quadratic space. -/
@[expose]
def Lattice.toSpace (x : Lattice) : Space :=
  ⟨x.a, x.b, x.c⟩

/-- The lattice quadratic form, with its rational extension. -/
@[expose]
def quadratic (x : Space) : ℚ := 6 * x.b ^ 2 - x.a * x.c

/-- The integral quadratic form on `ℤ³`. -/
@[expose]
def integralQuadratic (x : Lattice) : ℤ := 6 * x.b ^ 2 - x.a * x.c

theorem quadratic_toSpace (x : Lattice) :
    quadratic x.toSpace = (integralQuadratic x : ℚ) := by
  simp [quadratic, integralQuadratic, Lattice.toSpace]

/-- The bilinear form polarized from `quadratic`. -/
@[expose]
def bilinear (x y : Space) : ℚ :=
  12 * x.b * y.b - x.a * y.c - y.a * x.c

theorem bilinear_self (x : Space) : bilinear x x = 2 * quadratic x := by
  simp only [bilinear, quadratic]
  ring

theorem bilinear_symm (x y : Space) : bilinear x y = bilinear y x := by
  simp only [bilinear]
  ring

theorem quadratic_add (x y : Space) :
    quadratic (x + y) = quadratic x + quadratic y + bilinear x y := by
  simp only [quadratic, bilinear]
  change 6 * (x.b + y.b) ^ 2 - (x.a + y.a) * (x.c + y.c) = _
  ring

/-- The bilinear dual of the integral lattice as a subset of the rational space. -/
def dualLattice : Set Space :=
  {x | ∀ y : Lattice, ∃ n : ℤ, bilinear x y.toSpace = n}

/-- Coordinates of every vector in the bilinear dual. -/
theorem inDual_iff (x : Space) :
    x ∈ dualLattice ↔ ∃ a r c : ℤ, x.a = a ∧ x.b = r / 12 ∧ x.c = c := by
  constructor
  · intro hx
    obtain ⟨na, ha⟩ := hx ⟨0, 0, 1⟩
    obtain ⟨nr, hr⟩ := hx ⟨0, 1, 0⟩
    obtain ⟨nc, hc⟩ := hx ⟨1, 0, 0⟩
    simp [bilinear, Lattice.toSpace] at ha hr hc
    refine ⟨-na, nr, -nc, ?_, ?_, ?_⟩
    · exact neg_eq_iff_eq_neg.mp ha
    · apply (eq_div_iff (by norm_num : (12 : ℚ) ≠ 0)).2
      simpa only [mul_comm] using hr
    · exact neg_eq_iff_eq_neg.mp hc
  · rintro ⟨a, r, c, ha, hb, hc⟩ y
    refine ⟨r * y.b - a * y.c - y.a * c, ?_⟩
    simp only [bilinear, Lattice.toSpace, ha, hb, hc]
    push_cast
    ring

/-- A chosen lift of a residue to the rational dual. -/
def dualRepresentative (r : ZMod 12) : Space :=
  ⟨0, (r.val : ℚ) / 12, 0⟩

theorem dualRepresentative_mem (r : ZMod 12) :
    dualRepresentative r ∈ dualLattice := by
  refine (inDual_iff _).2 ?_
  exact ⟨0, r.val, 0, rfl, rfl, rfl⟩

theorem quadratic_dualRepresentative (r : ZMod 12) :
    quadratic (dualRepresentative r) = (r.val : ℚ) ^ 2 / 24 := by
  simp [quadratic, dualRepresentative]
  ring

end Theta
end SptClassification
