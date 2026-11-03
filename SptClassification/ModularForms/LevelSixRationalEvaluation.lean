/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.LevelSixRationalSections
public import SptClassification.ModularForms.LevelSixRationalHasseComparison
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
import all SptClassification.ModularForms.LevelSixRationalHasseComparison
import all SptClassification.ModularForms.LevelSixHasseGeometry
import all SptClassification.ModularForms.LevelSixRationalSections
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Evaluation of rational level-six sections away from poles

Evaluation is multiplicative only on functions regular at the chosen point.
The Serre operator preserves this regularity. The twice corrected weight-two
identity in [rolenManuscript, Section 4, equation (hasse)] can therefore be
evaluated at a Hasse zero without a homomorphism on the full rational field.
-/

public noncomputable section

namespace SptClassification.LevelSixRationalEvaluation

open Polynomial LevelSixRationalSections

variable {K : Type*} [Field K]

/-- No pole at the specified finite coordinate. -/
def RegularAt (x : K) (f : RatFunc K) : Prop := f.denom.eval x ≠ 0

/-- Rational evaluation; ring laws below require regularity. -/
def value (x : K) (f : RatFunc K) : K := RatFunc.eval (RingHom.id K) x f

theorem value_polynomial (x : K) (P : K[X]) :
    value x (algebraMap K[X] (RatFunc K) P) = P.eval x := by
  simp [value, RatFunc.eval_algebraMap]

theorem regularAt_polynomial (x : K) (P : K[X]) :
    RegularAt x (algebraMap K[X] (RatFunc K) P) := by
  simp [RegularAt, RatFunc.denom_algebraMap]

theorem eval_ne_zero_of_dvd {x : K} {P Q : K[X]} (h : P ∣ Q)
    (hQ : Q.eval x ≠ 0) : P.eval x ≠ 0 := by
  obtain ⟨R, rfl⟩ := h
  simpa only [eval_mul] using (mul_ne_zero_iff.mp (by simpa using hQ)).1

theorem RegularAt.add {x : K} {f g : RatFunc K}
    (hf : RegularAt x f) (hg : RegularAt x g) : RegularAt x (f + g) := by
  exact eval_ne_zero_of_dvd (RatFunc.denom_add_dvd f g)
    (by simpa only [eval_mul] using mul_ne_zero hf hg)

theorem RegularAt.mul {x : K} {f g : RatFunc K}
    (hf : RegularAt x f) (hg : RegularAt x g) : RegularAt x (f * g) := by
  exact eval_ne_zero_of_dvd (RatFunc.denom_mul_dvd f g)
    (by simpa only [eval_mul] using mul_ne_zero hf hg)

theorem RegularAt.neg {x : K} {f : RatFunc K}
    (hf : RegularAt x f) : RegularAt x (-f) := by
  have h := (regularAt_polynomial x (C (-1))).mul hf
  simpa using h

theorem RegularAt.sub {x : K} {f g : RatFunc K}
    (hf : RegularAt x f) (hg : RegularAt x g) : RegularAt x (f - g) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem regularAt_fraction (x : K) (P Q : K[X]) (hQ : Q.eval x ≠ 0) :
    RegularAt x (algebraMap K[X] (RatFunc K) P /
      algebraMap K[X] (RatFunc K) Q) :=
  eval_ne_zero_of_dvd (RatFunc.denom_div_dvd P Q) hQ

theorem value_add {x : K} {f g : RatFunc K}
    (hf : RegularAt x f) (hg : RegularAt x g) :
    value x (f + g) = value x f + value x g := by
  exact RatFunc.eval_add (RingHom.id K) x hf hg

theorem value_mul {x : K} {f g : RatFunc K}
    (hf : RegularAt x f) (hg : RegularAt x g) :
    value x (f * g) = value x f * value x g := by
  exact RatFunc.eval_mul (RingHom.id K) x hf hg

theorem value_fraction (x : K) (P Q : K[X]) (hQ : Q.eval x ≠ 0) :
    value x (algebraMap K[X] (RatFunc K) P /
      algebraMap K[X] (RatFunc K) Q) = P.eval x / Q.eval x := by
  have hQ' : algebraMap K[X] (RatFunc K) Q ≠ 0 := by
    intro hz
    have h := congrArg (value x) hz
    rw [value_polynomial] at h
    exact hQ (by simpa [value] using h)
  apply (eq_div_iff hQ).2
  rw [← value_polynomial x Q,
    ← value_mul (regularAt_fraction x P Q hQ) (regularAt_polynomial x Q),
    div_mul_cancel₀ _ hQ', value_polynomial]

/-- A rational connection with polynomial coefficients creates no new finite
poles. The denominator of its quotient-rule expression divides a square. -/
theorem RegularAt.serre {x : K} {f : RatFunc K}
    (hf : RegularAt x f) (k : ℕ) : RegularAt x (serre k f) := by
  rw [LevelSixRationalSections.serre, ← map_pow]
  exact (regularAt_fraction x _ _ hf).sub
    (regularAt_fraction x _ _ (by simpa only [eval_pow] using pow_ne_zero 2 hf))

/-- Coefficient of the Hasse-corrected derivative, in the original invariant
frame. `E` is the same polynomial `12 D_(p-1) H` used by Hasse geometry. -/
def correctedCoefficient (p k : ℕ) (f : RatFunc K) : RatFunc K :=
  algebraMap K[X] (RatFunc K) (LevelSixHasseGeometry.H p) * serre k f +
    algebraMap K[X] (RatFunc K) (C ((k : K) / 12) * LevelSixHasseGeometry.E p) * f

theorem correctedCoefficient_eq (p k : ℕ) (f : RatFunc K) :
    correctedCoefficient p k f =
      algebraMap K[X] (RatFunc K) (LevelSixHasseGeometry.H p) * serre k f +
      algebraMap K[X] (RatFunc K) (C ((k : K) / 12) * LevelSixHasseGeometry.E p) * f :=
  (rfl)

theorem RegularAt.correctedCoefficient {x : K} {f : RatFunc K}
    (hf : RegularAt x f) (p k : ℕ) : RegularAt x (correctedCoefficient p k f) := by
  rw [correctedCoefficient_eq]
  exact ((regularAt_polynomial x _).mul (hf.serre k)).add
    ((regularAt_polynomial x _).mul hf)

/-- At a Hasse zero the connection term vanishes, provided the section is
regular there. Regularity of its derivative has already been proved. -/
theorem value_correctedCoefficient {x : K} {f : RatFunc K}
    (hf : RegularAt x f) (p k : ℕ)
    (hH : (LevelSixHasseGeometry.H p : K[X]).eval x = 0) :
    value x (correctedCoefficient p k f) =
      ((k : K) / 12) * (LevelSixHasseGeometry.E p : K[X]).eval x * value x f := by
  rw [correctedCoefficient_eq,
    value_add ((regularAt_polynomial x _).mul (hf.serre k))
      ((regularAt_polynomial x _).mul hf),
    value_mul (regularAt_polynomial x _) (hf.serre k),
    value_mul (regularAt_polynomial x _) hf,
    value_polynomial, value_polynomial, hH]
  simp


/-- The coefficient operator is exactly the actual Hasse correction on a
homogeneous rational section, with the same invariant frame and weight. -/
theorem corrected_sectionOf (p k : ℕ) (hp : 0 < p) (f : RatFunc K) :
    LevelSixRationalHasseComparison.corrected p k (sectionOf k f) =
      sectionOf (k + p + 1) (correctedCoefficient p k f) := by
  rw [LevelSixRationalHasseComparison.corrected,
    LevelSixHasseGeometry.hasseSection, LevelSixHasseGeometry.serreHasseSection,
    ofPolynomial_sectionOf, ofPolynomial_sectionOf, serreSection_sectionOf,
    ← sectionOf_mul]
  have hw : p - 1 + (k + 2) = k + p + 1 := by omega
  have hw' : p - 1 + 2 + k = k + p + 1 := by omega
  simp only [sectionOf, C_mul_monomial, monomial_mul_monomial, hw, hw',
    ← map_add, correctedCoefficient_eq, map_mul, map_div₀, map_natCast,
    map_ofNat, map_C, RatFunc.algebraMap_C]

/-- Extract the genuine coefficient identity from the homogeneous section
identity supplied by the actual Tate/Hasse comparison. -/
theorem coefficient_identity_of_section_identity (p : ℕ) (hp : 0 < p)
    (L J : SectionRing K) (hL : IsWeight 2 L) (hJ : IsWeight 4 J) (d : ℕ)
    (hidentity : LevelSixRationalHasseComparison.corrected p (p + 3)
        (LevelSixRationalHasseComparison.corrected p 2 L) =
      (d : SectionRing K) * (ofPolynomial (LevelSixHasseGeometry.hasseSection p) *
        LevelSixRationalHasseComparison.corrected p 4 J)) :
    correctedCoefficient p (p + 3) (correctedCoefficient p 2 (L.coeff 2)) =
      algebraMap K[X] (RatFunc K) (C (d : K) * LevelSixHasseGeometry.H p) *
        correctedCoefficient p 4 (J.coeff 4) := by
  obtain ⟨l, rfl⟩ := hL
  obtain ⟨j, rfl⟩ := hJ
  simp only [coeff_sectionOf]
  have hw : 2 + p + 1 = p + 3 := by omega
  rw [corrected_sectionOf p 2 hp, hw, corrected_sectionOf p (p + 3) hp,
    corrected_sectionOf p 4 hp, LevelSixHasseGeometry.hasseSection,
    ofPolynomial_sectionOf, ← sectionOf_mul] at hidentity
  have hw' : p - 1 + (4 + p + 1) = p + 3 + p + 1 := by omega
  rw [hw'] at hidentity
  have h := congrArg (fun F : SectionRing K => F.coeff (p + 3 + p + 1)) hidentity
  rw [← C_eq_natCast] at h
  simpa [sectionOf, map_mul, RatFunc.algebraMap_C, mul_assoc] using h

/-- Evaluation of the manuscript's homogeneous identity gives exactly the
factor `E² L / 24`. The outer weight is `p+3`, which becomes `3` in the field.
Both sides are rational functions, and only `L,J` need regularity hypotheses. -/
theorem evaluated_hasse_identity (p : ℕ) [CharP K p]
    (x : K) (h6 : (6 : K) ≠ 0) (L J : RatFunc K) (d : K)
    (hL : RegularAt x L) (hJ : RegularAt x J)
    (hH : (LevelSixHasseGeometry.H p : K[X]).eval x = 0)
    (hidentity : correctedCoefficient p (p + 3) (correctedCoefficient p 2 L) =
      algebraMap K[X] (RatFunc K) (C d * LevelSixHasseGeometry.H p) *
        correctedCoefficient p 4 J) :
    (LevelSixHasseGeometry.E p : K[X]).eval x ^ 2 * value x L / 24 = 0 := by
  have h := congrArg (value x) hidentity
  rw [value_correctedCoefficient (hL.correctedCoefficient p 2) p (p + 3) hH,
    value_correctedCoefficient hL p 2 hH,
    value_mul (regularAt_polynomial x _) (hJ.correctedCoefficient p 4),
    value_polynomial] at h
  simp only [eval_mul, eval_C, hH, mul_zero, zero_mul, Nat.cast_add,
    CharP.cast_eq_zero, Nat.cast_ofNat, zero_add] at h
  have h12 : (12 : K) ≠ 0 := by
    have h2 := (LevelSixHasseGeometry.two_three_ne_zero h6).1
    have heq : (12 : K) = 2 * 6 := by norm_num
    rw [heq]
    exact mul_ne_zero h2 h6
  have h24 : (24 : K) ≠ 0 := by
    have h2 := (LevelSixHasseGeometry.two_three_ne_zero h6).1
    have heq : (24 : K) = 2 * 12 := by norm_num
    rw [heq]
    exact mul_ne_zero h2 h12
  have hfactor (e l : K) : (3 / 12 : K) * e * ((2 / 12 : K) * e * l) =
      e ^ 2 * l / 24 := by
    field_simp
    <;> ring
  rw [hfactor] at h
  exact h

/-- A regular weight-two rational coefficient vanishes at every geometric
Hasse zero where its homogeneous identity holds. The same actual `H` and
`E=12 D H` supply the nonvanishing factor. -/
theorem value_eq_zero_of_hasse_identity (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsAlgClosed K] (hp : 3 < p) (h6 : (6 : K) ≠ 0)
    (x : K) (L J : RatFunc K) (d : K)
    (hL : RegularAt x L) (hJ : RegularAt x J)
    (hH : (LevelSixHasseGeometry.H p : K[X]).eval x = 0)
    (hidentity : correctedCoefficient p (p + 3) (correctedCoefficient p 2 L) =
      algebraMap K[X] (RatFunc K) (C d * LevelSixHasseGeometry.H p) *
        correctedCoefficient p 4 J) : value x L = 0 := by
  have h := evaluated_hasse_identity p x h6 L J d hL hJ hH hidentity
  have h24 : (24 : K) ≠ 0 := by
    have h23 := LevelSixHasseGeometry.two_three_ne_zero h6
    have heq : (24 : K) = 2 ^ 3 * 3 := by norm_num
    rw [heq]
    exact mul_ne_zero (pow_ne_zero _ h23.1) h23.2
  have hnum : (LevelSixHasseGeometry.E p : K[X]).eval x ^ 2 * value x L = 0 :=
    (div_eq_zero_iff).mp h |>.resolve_right h24
  exact (mul_eq_zero.mp hnum).resolve_left
    (pow_ne_zero 2 (LevelSixHasseGeometry.E_eval_ne_zero p hp h6 x hH))

/-- The coefficient of the logarithmic form in the invariant differential
frame, retaining the actual positive Kodaira–Spencer coordinate factor. -/
def logarithmicCoefficient (A B : K[X]) : RatFunc K :=
  algebraMap K[X] (RatFunc K)
    (LevelSixModularSections.coordinateDerivative * (A.derivative * B - A * B.derivative)) /
      algebraMap K[X] (RatFunc K) (A * B)

theorem regularAt_logarithmicCoefficient (x : K) (A B : K[X])
    (ha : A.eval x ≠ 0) (hb : B.eval x ≠ 0) :
    RegularAt x (logarithmicCoefficient A B) :=
  regularAt_fraction x _ _ (by simpa using mul_ne_zero ha hb)

theorem value_logarithmicCoefficient (x : K) (A B : K[X])
    (ha : A.eval x ≠ 0) (hb : B.eval x ≠ 0) :
    value x (logarithmicCoefficient A B) =
      (LevelSixModularSections.coordinateDerivative : K[X]).eval x *
        (A.derivative * B - A * B.derivative).eval x / (A.eval x * B.eval x) := by
  rw [logarithmicCoefficient,
    value_fraction x _ _ (by simpa using mul_ne_zero ha hb)]
  simp only [eval_mul]

/-- Off the rational poles, the homogeneous Hasse identity forces a root of
the Wronskian. No root or logarithmic vanishing is assumed.
[rolenManuscript, Section 4, after equation (hasse)] -/
theorem wronskian_eval_eq_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsAlgClosed K] (hp : 3 < p) (h6 : (6 : K) ≠ 0)
    (x : K) (A B : K[X]) (J : RatFunc K) (d : K)
    (ha : A.eval x ≠ 0) (hb : B.eval x ≠ 0) (hJ : RegularAt x J)
    (hH : (LevelSixHasseGeometry.H p : K[X]).eval x = 0)
    (hidentity : correctedCoefficient p (p + 3)
        (correctedCoefficient p 2 (logarithmicCoefficient A B)) =
      algebraMap K[X] (RatFunc K) (C d * LevelSixHasseGeometry.H p) *
        correctedCoefficient p 4 J) :
    (A.derivative * B - A * B.derivative).eval x = 0 := by
  have h := value_eq_zero_of_hasse_identity p hp h6 x
    (logarithmicCoefficient A B) J d (regularAt_logarithmicCoefficient x A B ha hb)
    hJ hH hidentity
  rw [value_logarithmicCoefficient x A B ha hb] at h
  have hnum := (div_eq_zero_iff.mp h).resolve_right (mul_ne_zero ha hb)
  have hx := LevelSixHasseGeometry.isInterior_of_H_eq_zero p hp h6 x hH
  rw [LevelSixHasseGeometry.isInterior_iff] at hx
  exact (mul_eq_zero.mp hnum).resolve_left
    (LevelSixModularSections.coordinateDerivative_eval_ne_zero x h6 hx.1 hx.2.1 hx.2.2)

/-- Pointwise form of the actual rational-section Hasse identity. Only the
weight coefficients of `L,J` must have nonzero denominators at `x`. -/
theorem value_eq_zero_of_section_identity (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsAlgClosed K] (hp : 3 < p) (h6 : (6 : K) ≠ 0)
    (x : K) (L J : SectionRing K) (hL : IsWeight 2 L) (hJ : IsWeight 4 J) (d : ℕ)
    (hrL : RegularAt x (L.coeff 2)) (hrJ : RegularAt x (J.coeff 4))
    (hH : (LevelSixHasseGeometry.H p : K[X]).eval x = 0)
    (hidentity : LevelSixRationalHasseComparison.corrected p (p + 3)
        (LevelSixRationalHasseComparison.corrected p 2 L) =
      (d : SectionRing K) * (ofPolynomial (LevelSixHasseGeometry.hasseSection p) *
        LevelSixRationalHasseComparison.corrected p 4 J)) : value x (L.coeff 2) = 0 :=
  value_eq_zero_of_hasse_identity p hp h6 x _ _ (d : K) hrL hrJ hH
    (coefficient_identity_of_section_identity p (by omega) L J hL hJ d hidentity)

/-- Direct interface for the final obstruction: the actual homogeneous
identity and a logarithmic coefficient give a Wronskian root away from poles.
The global construction and regularity of `J` remain explicit inputs. -/
theorem wronskian_eval_eq_zero_of_section_identity
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsAlgClosed K]
    (hp : 3 < p) (h6 : (6 : K) ≠ 0) (x : K) (A B : K[X])
    (L J : SectionRing K) (hL : IsWeight 2 L) (hJ : IsWeight 4 J) (d : ℕ)
    (hcoeff : L.coeff 2 = logarithmicCoefficient A B)
    (ha : A.eval x ≠ 0) (hb : B.eval x ≠ 0) (hrJ : RegularAt x (J.coeff 4))
    (hH : (LevelSixHasseGeometry.H p : K[X]).eval x = 0)
    (hidentity : LevelSixRationalHasseComparison.corrected p (p + 3)
        (LevelSixRationalHasseComparison.corrected p 2 L) =
      (d : SectionRing K) * (ofPolynomial (LevelSixHasseGeometry.hasseSection p) *
        LevelSixRationalHasseComparison.corrected p 4 J)) :
    (A.derivative * B - A * B.derivative).eval x = 0 := by
  have hi := coefficient_identity_of_section_identity p (by omega) L J hL hJ d hidentity
  rw [hcoeff] at hi
  exact wronskian_eval_eq_zero p hp h6 x A B (J.coeff 4) (d : K) ha hb hrJ hH hi

end SptClassification.LevelSixRationalEvaluation
