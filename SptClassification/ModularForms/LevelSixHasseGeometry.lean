/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.LevelSixModularSections
public import SptClassification.ModularForms.WeierstrassHasse
public import Mathlib.FieldTheory.Separable
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Ring

/-!
# Hasse geometry of the actual level-six equation

All constructions are independent of the CM discriminant. The finite chart is
the actual integral family, with the invariant differential frame fixed in
`LevelSixModularSections`. The four omitted fibers are multiplicative; at
infinity the frame is changed by the coordinate. Generic Katz/Igusa inputs
are isolated in `WeierstrassHasse`.
-/

public noncomputable section

namespace SptClassification.LevelSixHasseGeometry

open Polynomial WeierstrassHasse LevelSixModularSections

variable {R : Type*} [CommRing R]

/-- Coefficient of the weight `p-1` Hasse section of the actual family. -/
def H (p : ℕ) : R[X] := hasse p (LevelSixWeierstrass.curve (X : R[X]))

/-- Coefficient of `12 D_(p-1) H`, of weight `p+1`. -/
def E (p : ℕ) : R[X] := 12 * serre (p - 1) (H p)

/-- The Hasse section in the graded ring, with weight `p-1`. -/
def hasseSection (p : ℕ) : SectionRing R := sectionOf (p - 1) (H p)

/-- The section `12 D_(p-1) H` in the same graded ring. -/
def serreHasseSection (p : ℕ) : SectionRing R := sectionOf (p - 1 + 2) (E p)

theorem hasseSection_weight (p : ℕ) : IsWeight (p - 1) (hasseSection (R := R) p) :=
  sectionOf_isWeight _ _

theorem serreHasseSection_weight (p : ℕ) :
    IsWeight (p - 1 + 2) (serreHasseSection (R := R) p) := sectionOf_isWeight _ _

/-- The two sections satisfy the Serre identity inside the same graded ring. -/
theorem serreHasseSection_eq (p : ℕ) :
    serreHasseSection (R := R) p = 12 * serreSection (p - 1) (hasseSection p) := by
  simp only [serreHasseSection, hasseSection, serreSection_sectionOf, E]
  change sectionOf (p - 1 + 2) ((C (12 : R)) * serre (p - 1) (H p)) = _
  have h := sectionOf_mul (R := R) 0 (p - 1 + 2) (C 12) (serre (p - 1) (H p))
  have hs : sectionOf 0 (C (12 : R)) = (12 : SectionRing R) := sectionOf_natCast 12
  rw [hs] at h
  simpa only [Nat.zero_add] using h

/-- For positive `p`, the weight is the usual `p+1`. -/
theorem serreHasseSection_weight_succ (p : ℕ) (hp : 0 < p) :
    IsWeight (p + 1) (serreHasseSection (R := R) p) := by
  convert serreHasseSection_weight (R := R) p using 1 <;> omega

/-- Base change of the section coefficient to the actual fiber. -/
theorem eval₂_H {S : Type*} [CommRing S] (φ : R →+* S) (p : ℕ) (t : S) :
    (H p : R[X]).eval₂ φ t = hasse p (LevelSixWeierstrass.curve t) := by
  change (eval₂RingHom φ t) (hasse p (LevelSixWeierstrass.curve X)) = _
  rw [map_hasse]
  congr 1
  ext <;> simp

theorem framedEval_hasseSection {S : Type*} [CommRing S]
    (φ : R →+* S) (p : ℕ) (t w : S) :
    framedEval φ t w (hasseSection p) =
      hasse p (LevelSixWeierstrass.curve t) * w ^ (p - 1) := by
  rw [hasseSection, framedEval_sectionOf, eval₂_H]

/-- The family satisfies the weight bounds at the infinity chart. -/
theorem curve_weightBounds : HasWeightBounds (LevelSixWeierstrass.curve (X : R[X])) := by
  simp only [hasWeightBounds_iff, LevelSixWeierstrass.curve_a₁,
    LevelSixWeierstrass.curve_a₂, LevelSixWeierstrass.curve_a₃,
    LevelSixWeierstrass.curve_a₄, LevelSixWeierstrass.curve_a₆]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> compute_degree <;> omega

/-- The Kodaira–Spencer numerator, including the elliptic `j` fibers. -/
theorem curve_ksNumerator :
    ksNumerator (LevelSixWeierstrass.curve (X : R[X])) =
      2 ^ 16 * 3 ^ 8 * X ^ 5 * (X + 8) * (X + 9) ^ 2 := by
  simp [ksNumerator_eq, WeierstrassCurve.c₄, WeierstrassCurve.c₆,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    derivative_mul, derivative_pow]
  simp only [C_ofNat]
  ring

/-- Exact inverse relation between the coordinate coefficient and the
Kodaira–Spencer coefficient `ksNumerator / (1728 Δ)`. This fixes the sign and
normalization used in [katz1973], Appendix A1.3.17–18. -/
theorem coordinateDerivative_mul_ksNumerator :
    coordinateDerivative * ksNumerator (LevelSixWeierstrass.curve (X : R[X])) =
      1728 * (LevelSixWeierstrass.curve (X : R[X])).Δ := by
  rw [curve_ksNumerator, LevelSixWeierstrass.curve_discriminant]
  rw [coordinateDerivative_eq]
  ring

/-- The infinity fiber in its regular frame is nodal. -/
theorem infinity_discriminant :
    (infinityFiber (LevelSixWeierstrass.curve (X : R[X]))).Δ = 0 := by
  simp [ WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring_nf
  norm_num [coeff_X]

/-- Its weight-four invariant is a unit away from characteristics two and three. -/
theorem infinity_c₄ :
    (infinityFiber (LevelSixWeierstrass.curve (X : R[X]))).c₄ = 144 := by
  simp [ WeierstrassCurve.c₄, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄]
  ring_nf
  norm_num [coeff_X]

variable {K : Type*} [Field K]

/-- Interior parameters of the modular curve. -/
def IsInterior (t : K) : Prop := t ≠ 0 ∧ t ≠ -8 ∧ t ≠ -9

theorem isInterior_iff (t : K) :
    IsInterior t ↔ t ≠ 0 ∧ t ≠ -8 ∧ t ≠ -9 := Iff.rfl

/-- Six invertible implies that every power of two or three is nonzero. -/
theorem two_three_ne_zero (h6 : (6 : K) ≠ 0) : (2 : K) ≠ 0 ∧ (3 : K) ≠ 0 := by
  have h : (2 : K) * 3 ≠ 0 := by norm_num; exact h6
  exact mul_ne_zero_iff.mp h

/-- The polynomial family is transverse to the elliptic moduli stack everywhere
on the interior; this is the hypothesis used by the generic simple-zero theorem. -/
theorem ksNumerator_eval_ne_zero (t : K) (h6 : (6 : K) ≠ 0) (ht : IsInterior t) :
    (ksNumerator (LevelSixWeierstrass.curve (X : K[X]))).eval t ≠ 0 := by
  rw [curve_ksNumerator]
  have h23 := two_three_ne_zero h6
  simpa [add_eq_zero_iff_eq_neg] using
    mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (pow_ne_zero 16 h23.1) (pow_ne_zero 8 h23.2))
      (pow_ne_zero 5 ht.1))
      (show t + 8 ≠ 0 by simpa [add_eq_zero_iff_eq_neg] using ht.2.1))
      (pow_ne_zero 2 (show t + 9 ≠ 0 by simpa [add_eq_zero_iff_eq_neg] using ht.2.2))

/-- Evaluation of Hasse coefficients is base change to the actual fiber. -/
theorem eval_H (p : ℕ) (t : K) :
    (H p : K[X]).eval t = hasse p (LevelSixWeierstrass.curve t) := by
  change (evalRingHom t) (hasse p (LevelSixWeierstrass.curve X)) = _
  rw [map_hasse]
  congr 1
  ext <;> simp

variable (p : ℕ) [Fact p.Prime] [CharP K p]

/-- Hasse has full degree because the infinity cusp is multiplicative. -/
theorem natDegree_H (hp : 3 < p) (h6 : (6 : K) ≠ 0) :
    (H p : K[X]).natDegree = p - 1 := by
  apply le_antisymm (hasse_degree_bound_literature p _ curve_weightBounds (by omega))
  apply le_natDegree_of_ne_zero
  rw [hasse_top_coefficient_literature p _ curve_weightBounds (by omega)]
  apply hasse_ne_zero_of_multiplicative_literature p hp _ infinity_discriminant
  rw [infinity_c₄]
  have h23 := two_three_ne_zero h6
  have h144 : (144 : K) = 2 ^ 4 * 3 ^ 2 := by norm_num
  rw [h144]
  exact mul_ne_zero (pow_ne_zero _ h23.1) (pow_ne_zero _ h23.2)

/-- A zero of H cannot occur at one of the three finite cusps. -/
theorem isInterior_of_H_eq_zero (hp : 3 < p) (h6 : (6 : K) ≠ 0) (t : K)
    (hH : (H p : K[X]).eval t = 0) : IsInterior t := by
  have h23 := two_three_ne_zero h6
  rw [eval_H] at hH
  have hnodal : ∀ s : K, (LevelSixWeierstrass.curve s).Δ = 0 →
      (LevelSixWeierstrass.curve s).c₄ ≠ 0 → hasse p (LevelSixWeierstrass.curve s) ≠ 0 :=
    fun s hΔ hc => hasse_ne_zero_of_multiplicative_literature p hp _ hΔ hc
  refine ⟨?_, ?_, ?_⟩
  all_goals intro ht; subst t
  · exact hnodal 0 (by rw [LevelSixWeierstrass.curve_discriminant]; simp)
      (by rw [LevelSixWeierstrass.curve_c₄_zero]; exact
        mul_ne_zero (pow_ne_zero _ h23.1) (pow_ne_zero _ h23.2)) hH
  · exact hnodal (-8) (by rw [LevelSixWeierstrass.curve_discriminant]; simp)
      (by rw [LevelSixWeierstrass.curve_c₄_neg_eight]; exact
        mul_ne_zero (pow_ne_zero _ h23.1) (pow_ne_zero _ h23.2)) hH
  · exact hnodal (-9) (by rw [LevelSixWeierstrass.curve_discriminant]; simp)
      (by rw [LevelSixWeierstrass.curve_c₄_neg_nine]; exact
        mul_ne_zero (pow_ne_zero _ h23.1) (pow_ne_zero _ h23.2)) hH

variable [IsAlgClosed K]

/-- Igusa's generic simple-zero theorem applied to the actual level-six family. -/
theorem derivative_H_ne_zero (hp : 3 < p) (h6 : (6 : K) ≠ 0) (t : K)
    (hH : (H p : K[X]).eval t = 0) : (derivative (H p : K[X])).eval t ≠ 0 := by
  have ht := isInterior_of_H_eq_zero p hp h6 t hH
  apply hasse_simple_zero_of_transverse_literature p hp _ t _
    (ksNumerator_eval_ne_zero t h6 ht) hH
  simpa [LevelSixWeierstrass.curve_discriminant] using
    (show (LevelSixWeierstrass.curve t).Δ ≠ 0 by
      intro hz
      exact (not_or_intro ht.1 (not_or_intro ht.2.1 ht.2.2))
        ((LevelSixWeierstrass.discriminant_eq_zero_iff t h6).mp hz))

/-- The manuscript's nonvanishing deduction from simple zeros and KS. -/
theorem E_eval_ne_zero (hp : 3 < p) (h6 : (6 : K) ≠ 0) (t : K)
    (hH : (H p : K[X]).eval t = 0) : (E p : K[X]).eval t ≠ 0 := by
  have ht := isInterior_of_H_eq_zero p hp h6 t hH
  have hD := eval_serre_ne_zero_of_simple_zero (p - 1) (H p) t h6
    ht.1 ht.2.1 ht.2.2 hH (derivative_H_ne_zero p hp h6 t hH)
  have h12 : (12 : K) ≠ 0 := by
    have : (12 : K) = 2 * 6 := by norm_num
    rw [this]
    exact mul_ne_zero (two_three_ne_zero h6).1 h6
  simpa [E] using mul_ne_zero h12 hD

/-- Nonvanishing is independent of the chosen nonzero differential frame. -/
theorem framedEval_serreHasseSection_ne_zero (hp : 3 < p) (h6 : (6 : K) ≠ 0)
    (t w : K) (hw : w ≠ 0) (hH : (H p : K[X]).eval t = 0) :
    framedEval (RingHom.id K) t w (serreHasseSection p) ≠ 0 := by
  rw [serreHasseSection, framedEval_sectionOf]
  simpa using mul_ne_zero (E_eval_ne_zero p hp h6 t hH) (pow_ne_zero (p - 1 + 2) hw)

/-- All geometric Hasse zeros are simple. -/
theorem H_separable (hp : 3 < p) (h6 : (6 : K) ≠ 0) :
    (H p : K[X]).Separable := by
  rw [Polynomial.separable_def,
    Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed K K (H p) (derivative (H p))]
  intro t
  by_cases ht : (H p : K[X]).eval t = 0
  · right
    simpa using derivative_H_ne_zero p hp h6 t ht
  · left
    simpa using ht

/-- The geometric supersingular parameter locus, as roots of the actual Hasse
coefficient. Its identification with Frobenius degeneracy is the classical
Hasse coefficient formula, with frame normalization fixed above. -/
@[expose] def supersingularParameters : Set K := (H p : K[X]).rootSet K

noncomputable instance : Fintype (supersingularParameters (K := K) p) := by
  unfold supersingularParameters
  infer_instance

/-- There are exactly `p-1` distinct geometric Hasse zeros. -/
theorem card_supersingularParameters (hp : 3 < p) (h6 : (6 : K) ≠ 0) :
    Fintype.card (supersingularParameters (K := K) p) = p - 1 := by
  have hH : (H p : K[X]) ≠ 0 := by
    intro h
    have hd := natDegree_H p hp h6
    rw [h, natDegree_zero] at hd
    omega
  have hs := H_separable p hp h6
  have hc := (Polynomial.card_rootSet_eq_natDegree_iff_of_splits (K := K) hH
    (by simpa using IsAlgClosed.splits (H p : K[X]))).2 hs
  exact hc.trans (natDegree_H p hp h6)

end SptClassification.LevelSixHasseGeometry
