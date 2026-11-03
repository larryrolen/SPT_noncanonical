/- Assembled by AxiomProver. -/

module

public import SptClassification.Theta.WeilOperatorRelations

/-!
# Quadratic Gauss transform for the Shimura discriminant form

The quadratic and bilinear values of the twelve-element discriminant group
control the full finite Weil generator relation. We use Mathlib's standard
additive characters on `ZMod 24` and `ZMod 12`, with the normalization of
[rolenManuscript, lines 336–343].
-/

public section

namespace SptClassification
namespace Theta

/-- The quadratic phase `e(r²/24)` on the discriminant group. -/
noncomputable def weilQuadraticPhase (r : ZMod 12) : ℂ :=
  ZMod.stdAddChar (discriminantQuadratic r)

/-- The bilinear phase `e(rs/12)` on the discriminant group. -/
noncomputable def weilPairingPhase (r s : ZMod 12) : ℂ :=
  ZMod.stdAddChar (discriminantPairing r s)

/-- The standard additive characters of orders twelve and twenty-four agree
under doubling of a residue representative. -/
theorem stdAddChar_double (r : ZMod 12) :
    (ZMod.stdAddChar (2 * (r.val : ZMod 24)) : ℂ) = ZMod.stdAddChar r := by
  have hval : (2 * (r.val : ZMod 24)).val = 2 * r.val := by
    have hr := r.val_lt
    rw [show 2 * (r.val : ZMod 24) = ((2 * r.val : ℕ) : ZMod 24) by push_cast; ring]
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt (by omega)
  simp only [ZMod.stdAddChar_apply, ZMod.toCircle_apply, hval]
  congr 1
  push_cast
  ring

/-- The bilinear phase equals Mathlib's order-twelve character. -/
theorem weilPairingPhase_eq (r s : ZMod 12) :
    weilPairingPhase r s = ZMod.stdAddChar (r * s) := by
  rw [weilPairingPhase, discriminantPairing_eq, stdAddChar_double]

/-- The quadratic phase is exactly the diagonal coefficient of the standard
finite Weil translation. -/
theorem weilQuadraticPhase_eq (r : ZMod 12) :
    weilQuadraticPhase r =
      Complex.exp (Real.pi * Complex.I * (discriminantQuadratic r).val / 12) := by
  rw [weilQuadraticPhase, ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  congr 1
  push_cast
  ring

/-- Polarization of the discriminant quadratic phase. -/
theorem weilQuadraticPhase_add (r s : ZMod 12) :
    weilQuadraticPhase (r + s) =
      weilQuadraticPhase r * weilQuadraticPhase s * weilPairingPhase r s := by
  simp only [weilQuadraticPhase, weilPairingPhase, discriminantQuadratic_add]
  rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]

/-- The quadratic phase is invariant under the reflection induced by `S²`. -/
theorem weilQuadraticPhase_neg (r : ZMod 12) :
    weilQuadraticPhase (-r) = weilQuadraticPhase r := by
  simp [weilQuadraticPhase, discriminantQuadratic_neg]

/-- Completing the square against the negative Fourier kernel. -/
theorem weilQuadraticPhase_sub (r s : ZMod 12) :
    weilQuadraticPhase (r - s) =
      weilQuadraticPhase r * weilQuadraticPhase s *
        ZMod.stdAddChar (-(r * s)) := by
  rw [sub_eq_add_neg, weilQuadraticPhase_add, weilQuadraticPhase_neg,
    weilPairingPhase_eq]
  simp only [mul_neg]

/-- The quadratic Gauss numerator with the manuscript's normalization. -/
noncomputable def weilQuadraticGauss : ℂ :=
  ∑ r : ZMod 12, weilQuadraticPhase r

/-- A shift of the quadratic Gauss sum is controlled by its quadratic phase. -/
theorem weilQuadraticGauss_shift (a : ZMod 12) :
    weilQuadraticPhase a *
        (∑ r : ZMod 12,
          weilQuadraticPhase r * ZMod.stdAddChar (-(r * a))) =
      weilQuadraticGauss := by
  calc
    weilQuadraticPhase a *
        (∑ r : ZMod 12,
          weilQuadraticPhase r * ZMod.stdAddChar (-(r * a))) =
        ∑ r : ZMod 12, weilQuadraticPhase (r - a) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r _
          rw [weilQuadraticPhase_sub]
          ring
    _ = ∑ r : ZMod 12, weilQuadraticPhase r := by
      apply Finset.sum_bij (fun r _ => r - a)
      · simp
      · intro r _ s _ h
        simpa only [sub_add_cancel] using congrArg (fun x : ZMod 12 => x + a) h
      · intro s _
        refine ⟨s + a, by simp, ?_⟩
        simp
      · intro r _
        rfl
    _ = weilQuadraticGauss := rfl

/-- The completed-square kernel needed for the cubic relation of the two
standard Weil generators. -/
theorem weilQuadraticGauss_kernel (r s : ZMod 12) :
    weilQuadraticPhase r * weilQuadraticPhase s *
        (∑ t : ZMod 12,
          weilQuadraticPhase t * ZMod.stdAddChar (-(t * (r + s)))) =
      weilQuadraticGauss * ZMod.stdAddChar (-(r * s)) := by
  have hcancel :
      (ZMod.stdAddChar (r * s) : ℂ) * ZMod.stdAddChar (-(r * s)) = 1 := by
    rw [← AddChar.map_add_eq_mul]
    simp
  calc
    weilQuadraticPhase r * weilQuadraticPhase s *
        (∑ t : ZMod 12,
          weilQuadraticPhase t * ZMod.stdAddChar (-(t * (r + s)))) =
      (weilQuadraticPhase (r + s) *
        (∑ t : ZMod 12,
          weilQuadraticPhase t * ZMod.stdAddChar (-(t * (r + s))))) *
          ZMod.stdAddChar (-(r * s)) := by
            rw [weilQuadraticPhase_add, weilPairingPhase_eq]
            calc
              weilQuadraticPhase r * weilQuadraticPhase s *
                  (∑ t : ZMod 12,
                    weilQuadraticPhase t * ZMod.stdAddChar (-(t * (r + s)))) =
                (weilQuadraticPhase r * weilQuadraticPhase s *
                  (∑ t : ZMod 12,
                    weilQuadraticPhase t * ZMod.stdAddChar (-(t * (r + s))))) *
                  (ZMod.stdAddChar (r * s) * ZMod.stdAddChar (-(r * s))) := by
                    rw [hcancel, mul_one]
              _ = _ := by ring
    _ = weilQuadraticGauss * ZMod.stdAddChar (-(r * s)) := by
      rw [weilQuadraticGauss_shift]

end Theta
end SptClassification
