/- Assembled by AxiomProver. -/

module

public import SptClassification.Theta.LatticeAction
public import SptClassification.QuadraticForms.LevelSixForms
public import SptClassification.QuadraticForms.CMPoint

/-!
# Negative dual vectors and level-six CM forms

The dual vector `(a,r/12,c)` gives `6c X² + r XY + a Y²`. Its
discriminant is twenty-four times its lattice norm. This is the algebraic
correspondence used to locate the lift's poles in [rolenManuscript,
lines 348–350]. Positivity requires `c > 0`; it does not follow merely from
negative norm without choosing the appropriate component.
-/

public section

namespace SptClassification
namespace Theta

/-- The binary quadratic form attached to a dual lattice vector. -/
def DualCoordinates.binaryForm (x : DualCoordinates) : BinaryQuadraticForm :=
  ⟨6 * x.c, x.r, x.a⟩

theorem DualCoordinates.binaryForm_eq (x : DualCoordinates) :
    x.binaryForm = ⟨6 * x.c, x.r, x.a⟩ := (rfl)

theorem DualCoordinates.binaryForm_discriminant (x : DualCoordinates) :
    x.binaryForm.discriminant = x.r ^ 2 - 24 * x.a * x.c := by
  simp only [binaryForm, BinaryQuadraticForm.discriminant]
  ring

theorem LevelSixMatrix.binaryForm_act (g : LevelSixMatrix) (x : DualCoordinates) :
    (g.act x).binaryForm =
      x.binaryForm.pullback !![g.p, g.q; 6 * g.k, g.s] := by
  ext <;> simp [DualCoordinates.binaryForm, LevelSixMatrix.act_a,
    LevelSixMatrix.act_r, LevelSixMatrix.act_c,
    BinaryQuadraticForm.pullback] <;> ring

theorem DualCoordinates.norm_eq_iff_discriminant (x : DualCoordinates) (d : ℤ) :
    quadratic x.toSpace = -(d : ℚ) / 24 ↔ x.binaryForm.discriminant = -d := by
  rw [quadratic_eq, binaryForm_discriminant]
  constructor
  · intro h
    exact_mod_cast (show (x.r : ℚ) ^ 2 - 24 * x.a * x.c = -(d : ℚ) by
      linarith only [h])
  · intro h
    have hq : (x.r : ℚ) ^ 2 - 24 * x.a * x.c = -(d : ℚ) := by exact_mod_cast h
    linarith only [hq]

/-- A positive-component negative vector gives a level-six form. -/
def DualCoordinates.toLevelSixForm (x : DualCoordinates) (d : ℤ)
    (hc : 0 < x.c) (hnorm : quadratic x.toSpace = -(d : ℚ) / 24) :
    LevelSixForm (-d) (x.r : ZMod 12) where
  toBinaryQuadraticForm := x.binaryForm
  a_pos := by dsimp [binaryForm]; omega
  discriminant_eq := (x.norm_eq_iff_discriminant d).1 hnorm
  six_dvd_a := ⟨x.c, by rfl⟩
  b_residue := rfl

theorem DualCoordinates.toLevelSixForm_toBinaryQuadraticForm (x : DualCoordinates) (d : ℤ)
    (hc : 0 < x.c) (hnorm : quadratic x.toSpace = -(d : ℚ) / 24) :
    (x.toLevelSixForm d hc hnorm).toBinaryQuadraticForm = x.binaryForm := (rfl)

/-- The dual vector associated with any level-six form. -/
def ofLevelSixForm {D : ℤ} {r : ZMod 12} (Q : LevelSixForm D r) : DualCoordinates :=
  ⟨Q.c, Q.b, Q.a / 6⟩

theorem binaryForm_ofLevelSixForm {D : ℤ} {r : ZMod 12}
    (Q : LevelSixForm D r) : (ofLevelSixForm Q).binaryForm = Q.toBinaryQuadraticForm := by
  apply BinaryQuadraticForm.ext
  · simp only [DualCoordinates.binaryForm, ofLevelSixForm]
    simpa only [mul_comm] using (Int.ediv_mul_cancel Q.six_dvd_a)
  · rfl
  · rfl

theorem ofLevelSixForm_norm {D : ℤ} {r : ZMod 12}
    (Q : LevelSixForm D r) :
    quadratic (ofLevelSixForm Q).toSpace = (D : ℚ) / 24 := by
  have h : (ofLevelSixForm Q).binaryForm.discriminant = D := by
    rw [binaryForm_ofLevelSixForm]
    exact Q.discriminant_eq
  have hq := ((ofLevelSixForm Q).norm_eq_iff_discriminant (-D)).2 (by simpa using h)
  simpa only [Int.cast_neg, neg_neg] using hq

/-- Recover the vector after forming its positive level-six quadratic. -/
theorem ofLevelSixForm_toLevelSixForm (x : DualCoordinates) (d : ℤ)
    (hc : 0 < x.c) (hnorm : quadratic x.toSpace = -(d : ℚ) / 24) :
    ofLevelSixForm (x.toLevelSixForm d hc hnorm) = x := by
  apply DualCoordinates.ext
  · rfl
  · rfl
  · dsimp [ofLevelSixForm, DualCoordinates.toLevelSixForm,
      DualCoordinates.binaryForm]
    omega

/-- A positive level-six form has a positive third dual-lattice coordinate. -/
theorem ofLevelSixForm_c_pos {D : ℤ} {r : ZMod 12}
    (Q : LevelSixForm D r) : 0 < (ofLevelSixForm Q).c := by
  change 0 < Q.a / 6
  have h : Q.a / 6 * 6 = Q.a := Int.ediv_mul_cancel Q.six_dvd_a
  have ha := Q.a_pos
  omega

/-- The dual vector of a level-six quadratic retains its prescribed residue. -/
theorem ofLevelSixForm_discriminantClass {D : ℤ} {r : ZMod 12}
    (Q : LevelSixForm D r) : (ofLevelSixForm Q).discriminantClass = r :=
  Q.b_residue

/-- Recover the underlying level-six quadratic after passing to its dual vector. -/
theorem toLevelSixForm_ofLevelSixForm {d : ℤ} {r : ZMod 12}
    (Q : LevelSixForm (-d) r) :
    ((ofLevelSixForm Q).toLevelSixForm d
      (ofLevelSixForm_c_pos Q)
      (by simpa only [Int.cast_neg] using ofLevelSixForm_norm Q)).toBinaryQuadraticForm =
        Q.toBinaryQuadraticForm :=
  binaryForm_ofLevelSixForm Q

/-- The form's actual CM point solves the quadratic attached to the vector. -/
theorem DualCoordinates.evaluate_cmPoint (x : DualCoordinates) (d : ℤ)
    (hd : 0 < d) (hc : 0 < x.c)
    (hnorm : quadratic x.toSpace = -(d : ℚ) / 24) :
    letI : Fact (-d < 0) := ⟨by omega⟩
    let z := (x.toLevelSixForm d hc hnorm).cmPoint
    (6 * (x.c : ℂ)) * (z : ℂ) ^ 2 + (x.r : ℂ) * z + x.a = 0 := by
  letI : Fact (-d < 0) := ⟨by omega⟩
  have h := (x.toLevelSixForm d hc hnorm).evaluateOver_cmPoint
  simpa [BinaryQuadraticForm.evaluateOver_one, DualCoordinates.toLevelSixForm,
    DualCoordinates.binaryForm] using h

end Theta
end SptClassification
