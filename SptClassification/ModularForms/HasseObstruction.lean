/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.HasseObstructionGeometry

/-!
# The conditional Hasse character obstruction

This module proves the deduction in [rolenManuscript, Section 4,
Proposition 4.1] from the actual principal Lambert series, descended CM
models, and explicit lift/good-reduction geometry. It does not assert that
the geometric inputs exist unconditionally.
-/

public section

namespace SptClassification

open Polynomial QSeries

private theorem hasseTheta_eval_at_hasse_zero
    {p : ℕ} [Fact p.Prime] {F K : Type*}
    [CommRing F] [Algebra (ZMod p) F]
    [Field K] [Algebra (ZMod p) K]
    (H E : F) (D : ℕ → F →ₗ[ZMod p] F)
    (φ : F →ₐ[ZMod p] K) (hH : φ H = 0)
    (k : ℕ) (f : F) :
    φ (hasseTheta H E D k f) =
      ((k : K) / 12) * φ E * φ f := by
  have h12 : (algebraMap (ZMod p) K) (12 : ZMod p) = (12 : K) := by
    exact map_natCast (algebraMap (ZMod p) K) 12
  simp [hasseTheta_apply, hH, Algebra.smul_def, h12, mul_assoc]

/-- The Hasse invariant has simple zeros by Katz; the manuscript's identity
`E = 12 D H` transfers this to the Eisenstein value. -/
private theorem eisenstein_ne_zero_of_serre_H_ne_zero
    {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    {F K : Type*} [CommRing F] [Algebra (ZMod p) F]
    [Field K] [Algebra (ZMod p) K] [CharP K p]
    (H E : F) (D : ℕ → F →ₗ[ZMod p] F)
    (hE : E = (12 : ZMod p) • D (p - 1) H)
    (φ : F →ₐ[ZMod p] K)
    (hD : φ (D (p - 1) H) ≠ 0) : φ E ≠ 0 := by
  have h12 : (12 : K) ≠ 0 := by
    intro hz
    have hdiv : p ∣ 12 := (CharP.cast_eq_zero_iff K p 12).mp hz
    have hdiv' : p ∣ 3 * 4 := by simpa only [show 3 * 4 = 12 by decide] using hdiv
    rcases (Fact.out : p.Prime).dvd_mul.mp hdiv' with h3div | h4div
    · have := Nat.le_of_dvd (by decide : 0 < 3) h3div
      omega
    · have := Nat.le_of_dvd (by decide : 0 < 4) h4div
      omega
  have heval : φ E = (12 : K) * φ (D (p - 1) H) := by
    have hmap : (algebraMap (ZMod p) K) (12 : ZMod p) = (12 : K) := by
      exact map_natCast (algebraMap (ZMod p) K) 12
    rw [hE]
    simp [Algebra.smul_def, hmap]
  rw [heval]
  exact mul_ne_zero h12 hD

/-- At a supersingular point away from CM poles, the twice homogenized
Lambert identity makes the logarithmic form vanish. The characteristic is
at least five, so the manuscript's coefficient 1/24 is nonzero. -/
private theorem lambert_zero_at_hasse_point
    {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    {F K : Type*} [CommRing F] [Algebra (ZMod p) F]
    [Field K] [Algebra (ZMod p) K] [CharP K p]
    (H E L J : F) (D : ℕ → F →ₗ[ZMod p] F)
    (φ : F →ₐ[ZMod p] K)
    (hH : φ H = 0) (hE : φ E ≠ 0)
    (d : ℕ)
    (hidentity : hasseTheta H E D (p + 3)
        (hasseTheta H E D 2 L) =
      (d : ZMod p) • (H * hasseTheta H E D 4 J)) :
    φ L = 0 := by
  have h2 : (2 : K) ≠ 0 := by
    intro hz
    have hdiv : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp hz
    exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) hdiv
  have h3 : (3 : K) ≠ 0 := by
    intro hz
    have hdiv : p ∣ 3 := (CharP.cast_eq_zero_iff K p 3).mp hz
    exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) hdiv
  have h12 : (12 : K) ≠ 0 := by
    intro hz
    have hdiv : p ∣ 12 := (CharP.cast_eq_zero_iff K p 12).mp hz
    have hdiv' : p ∣ 3 * 4 := by simpa only [show 3 * 4 = 12 by decide] using hdiv
    rcases (Fact.out : p.Prime).dvd_mul.mp hdiv' with h3div | h4div
    · have := Nat.le_of_dvd (by decide : 0 < 3) h3div
      omega
    · have := Nat.le_of_dvd (by decide : 0 < 4) h4div
      omega
  have hpzero : (p : K) = 0 :=
    (CharP.cast_eq_zero_iff K p p).mpr (dvd_refl p)
  have hp3 : ((p + 3 : ℕ) : K) = 3 := by
    simp
  have hc1 : (((p + 3 : ℕ) : K) / 12) ≠ 0 := by
    rw [hp3]
    exact div_ne_zero h3 h12
  have hc2 : ((2 : K) / 12) ≠ 0 := div_ne_zero h2 h12
  have heval : (((p + 3 : ℕ) : K) / 12) * φ E *
      (((2 : K) / 12) * φ E * φ L) = 0 := by
    have h := congrArg (fun f : F => φ f) hidentity
    rw [hasseTheta_eval_at_hasse_zero H E D φ hH (p + 3),
      hasseTheta_eval_at_hasse_zero H E D φ hH 2] at h
    simpa [hH] using h
  have hinner : ((2 : K) / 12) * φ E * φ L = 0 :=
    (mul_eq_zero.mp heval).resolve_left (mul_ne_zero hc1 hE)
  exact (mul_eq_zero.mp hinner).resolve_left (mul_ne_zero hc2 hE)

/-- A weight-two form with the oriented CM quotient evaluation vanishes at
every supersingular point away from its poles. The root conclusion uses only
the homogeneous identity and the general Hasse geometry. -/
theorem LiftHasseGeometry.logarithmic_root_off_support_of_form
    {p d : ℕ} [Fact p.Prime] [Fact (-(d : ℤ) < 0)]
    {F X : Type*} [CommRing F] [Algebra (ZMod p) F]
    (Icm : ConditionalCM.CMDescentInput d p)
    (I : LiftHasseGeometry p d Icm F X) (L : F)
    (hcomparison : ∀ (x : X) ha hb,
      I.evaluate x ha hb L =
        I.theta_coordinate x *
          (Icm.geometricA.derivative * Icm.geometricB -
            Icm.geometricA * Icm.geometricB.derivative).eval (I.coordinate x) /
          (Icm.geometricA.eval (I.coordinate x) *
            Icm.geometricB.eval (I.coordinate x)))
    (hp : 5 ≤ p)
    (hidentity : hasseTheta I.forms.H I.forms.E I.forms.serre (p + 3)
        (hasseTheta I.forms.H I.forms.E I.forms.serre 2 L) =
      (d : ZMod p) •
        (I.forms.H * hasseTheta I.forms.H I.forms.E I.forms.serre 4 I.forms.J))
    (x : X) (hx : x ∈ I.points)
    (ha : ¬Icm.geometricA.IsRoot (I.coordinate x))
    (hb : ¬Icm.geometricB.IsRoot (I.coordinate x)) :
    (Icm.geometricA.derivative * Icm.geometricB -
      Icm.geometricA * Icm.geometricB.derivative).IsRoot
        (I.coordinate x) := by
  let φ := I.evaluate x ha hb
  have hE : φ I.forms.E ≠ 0 :=
    eisenstein_ne_zero_of_serre_H_ne_zero hp I.forms.H I.forms.E
      I.forms.serre I.forms.E_eq_serre_H φ
      (I.serre_H_ne_zero x hx ha hb)
  have hL : φ L = 0 :=
    lambert_zero_at_hasse_point hp I.forms.H I.forms.E L
      I.forms.J I.forms.serre φ
      (I.hasse_zero x hx ha hb) hE
      d hidentity
  have hden : Icm.geometricA.eval (I.coordinate x) *
      Icm.geometricB.eval (I.coordinate x) ≠ 0 :=
    mul_ne_zero ha hb
  have hratio : I.theta_coordinate x *
      (Icm.geometricA.derivative * Icm.geometricB -
        Icm.geometricA * Icm.geometricB.derivative).eval (I.coordinate x) /
      (Icm.geometricA.eval (I.coordinate x) *
        Icm.geometricB.eval (I.coordinate x)) = 0 := by
    rw [← hcomparison x ha hb]
    exact hL
  have hnum : I.theta_coordinate x *
      (Icm.geometricA.derivative * Icm.geometricB -
        Icm.geometricA * Icm.geometricB.derivative).eval (I.coordinate x) = 0 := by
    by_contra hne
    exact (div_ne_zero hne hden) hratio
  change (Icm.geometricA.derivative * Icm.geometricB -
    Icm.geometricA * Icm.geometricB.derivative).eval (I.coordinate x) = 0
  exact (mul_eq_zero.mp hnum).resolve_left (I.theta_coordinate_ne_zero x)

/-- Specialization to an explicitly supplied logarithmic lift. -/
theorem LiftHasseInput.logarithmic_root_off_support
    {p d : ℕ} [Fact p.Prime] [Fact (-(d : ℤ) < 0)]
    {F X : Type*} [CommRing F] [Algebra (ZMod p) F]
    (Icm : ConditionalCM.CMDescentInput d p)
    (I : LiftHasseInput p d Icm F X)
    (hp : 5 ≤ p)
    (hidentity : hasseTheta I.forms.H I.forms.E I.forms.serre (p + 3)
        (hasseTheta I.forms.H I.forms.E I.forms.serre 2 I.L) =
      (d : ZMod p) •
        (I.forms.H * hasseTheta I.forms.H I.forms.E I.forms.serre 4 I.forms.J))
    (x : X) (hx : x ∈ I.points)
    (ha : ¬Icm.geometricA.IsRoot (I.coordinate x))
    (hb : ¬Icm.geometricB.IsRoot (I.coordinate x)) :
    (Icm.geometricA.derivative * Icm.geometricB -
      Icm.geometricA * Icm.geometricB.derivative).IsRoot
        (I.coordinate x) := by
  exact I.toLiftHasseGeometry.logarithmic_root_off_support_of_form
    Icm I.L I.logarithmic_identity hp hidentity x hx ha hb

/-- The actual reduced CM support and logarithmic numerator cannot cover
all supersingular coordinates under the manuscript's strict class-number
bound. [rolenManuscript, proof of Proposition 4.1] -/
private theorem LiftHasseGeometry.no_homogeneous_identity_of_form
    {p d : ℕ} [Fact p.Prime] [Fact (-(d : ℤ) < 0)]
    {F X : Type*} [CommRing F] [Algebra (ZMod p) F]
    (Icm : ConditionalCM.CMDescentInput d p)
    (I : LiftHasseGeometry p d Icm F X) (L : F)
    (hcomparison : ∀ (x : X) ha hb,
      I.evaluate x ha hb L =
        I.theta_coordinate x *
          (Icm.geometricA.derivative * Icm.geometricB -
            Icm.geometricA * Icm.geometricB.derivative).eval (I.coordinate x) /
          (Icm.geometricA.eval (I.coordinate x) *
            Icm.geometricB.eval (I.coordinate x)))
    (hp : 5 ≤ p) (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) (hcop : ¬p ∣ 6 * d)
    (hsep : (d + 1) ^ 2 < 24 * p)
    (hclass : 8 * formClassNumber (-(d : ℤ)) < p + 1)
    (hidentity : hasseTheta I.forms.H I.forms.E I.forms.serre (p + 3)
        (hasseTheta I.forms.H I.forms.E I.forms.serre 2 L) =
      (d : ZMod p) •
        (I.forms.H * hasseTheta I.forms.H I.forms.E I.forms.serre 4 I.forms.J)) :
    False := by
  classical
  let s : Finset (AlgebraicClosure (ZMod p)) := I.points.map I.coordinate
  have hs_card : s.card = p - 1 := by
    simpa only [s, Finset.card_map] using I.points_card
  have hcover : ∀ y ∈ s, Icm.geometricA.IsRoot y ∨
      Icm.geometricB.IsRoot y ∨
      (Icm.geometricA.derivative * Icm.geometricB -
        Icm.geometricA * Icm.geometricB.derivative).IsRoot y := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
    by_cases ha : Icm.geometricA.IsRoot (I.coordinate x)
    · exact Or.inl ha
    by_cases hb : Icm.geometricB.IsRoot (I.coordinate x)
    · exact Or.inr (Or.inl hb)
    exact Or.inr (Or.inr
      (I.logarithmic_root_off_support_of_form Icm L hcomparison
        hp hidentity x hx ha hb))
  have hD : (-(d : ℤ)) % 4 = 1 := by omega
  have hpositive : 0 < formClassNumber (-(d : ℤ)) :=
    formClassNumber_pos _ hD
  exact no_supersingular_logarithmic_cover p
    (formClassNumber (-(d : ℤ)))
    (Icm.geometric_coprime hd hsq hmod hp hcop hsep)
    Icm.geometricA_monic Icm.geometricB_monic
    (Icm.geometricA_degree hmod) (Icm.geometricB_degree hmod)
    hpositive hclass s hs_card hcover

/-- The supplied-logarithmic-lift instance of the general root-count
contradiction. -/
private theorem LiftHasseInput.no_homogeneous_identity
    {p d : ℕ} [Fact p.Prime] [Fact (-(d : ℤ) < 0)]
    {F X : Type*} [CommRing F] [Algebra (ZMod p) F]
    (Icm : ConditionalCM.CMDescentInput d p)
    (I : LiftHasseInput p d Icm F X)
    (hp : 5 ≤ p) (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) (hcop : ¬p ∣ 6 * d)
    (hsep : (d + 1) ^ 2 < 24 * p)
    (hclass : 8 * formClassNumber (-(d : ℤ)) < p + 1)
    (hidentity : hasseTheta I.forms.H I.forms.E I.forms.serre (p + 3)
        (hasseTheta I.forms.H I.forms.E I.forms.serre 2 I.L) =
      (d : ZMod p) •
        (I.forms.H * hasseTheta I.forms.H I.forms.E I.forms.serre 4 I.forms.J)) :
    False := by
  exact I.toLiftHasseGeometry.no_homogeneous_identity_of_form
    Icm I.L I.logarithmic_identity hp hd hsq hmod hcop hsep hclass hidentity

/-- Conditional character obstruction for the actual `spt` class and the
actual principal-form Lambert series. The constant-term, CM-descent and
lift/Hasse data are explicit inputs; in particular no geometric root or
class exclusion is assumed. [rolenManuscript, Proposition 4.1] -/
theorem conditional_character_obstruction
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (sign : ℤ) (hsign : sign = 1 ∨ sign = -1)
    (d : ℕ) [Fact (-(d : ℤ) < 0)]
    (hd : 0 < d) (hsq : Squarefree d) (hmod : d % 24 = 23)
    (hr : legendreSym p (-(d : ℤ)) = sign)
    (hsep : (d + 1) ^ 2 < 24 * p)
    (hclass : 8 * formClassNumber (-(d : ℤ)) < p + 1)
    (hCT : ConstantTermInputs p)
    (Icm : ConditionalCM.CMDescentInput d p)
    {F X : Type*} [CommRing F] [Algebra (ZMod p) F]
    (I : LiftHasseInput p d Icm F X) :
    ¬∀ j : ℕ, legendreSym p (1 - 24 * (j : ℤ)) = sign →
      ((spt j : ℤ) : ZMod p) = 0 := by
  intro hspt
  have hd22 : 22 ≤ d := by omega
  have hmul : 22 * d ≤ d * d := Nat.mul_le_mul_right d hd22
  have hdlt : d < p := by nlinarith [hmul]
  have hpd : ¬p ∣ d := Nat.not_dvd_of_pos_of_lt hd hdlt
  have hp6 : ¬p ∣ 6 := by
    intro h
    have h23 : p ∣ 2 ∨ p ∣ 3 := by
      apply (Fact.out : p.Prime).dvd_mul.mp
      simpa only [show 2 * 3 = 6 by decide] using h
    rcases h23 with h2 | h3
    · have := Nat.le_of_dvd (by decide : 0 < 2) h2
      omega
    · have := Nat.le_of_dvd (by decide : 0 < 3) h3
      omega
  have hcop : ¬p ∣ 6 * d := by
    intro h
    rcases (Fact.out : p.Prime).dvd_mul.mp h with h6 | hdvd
    · exact hp6 h6
    · exact hpd hdvd
  have hdiff := QSeries.conditional_principal_lambert_differential
    p hp sign hsign d hd hmod hr hspt hCT
  have hidentity := I.forms.homogeneous_lambert_identity_of_forms
    I.L I.forms.J I.L_form I.forms.J_form I.L_qexp I.forms.J_qexp hdiff
  exact I.no_homogeneous_identity Icm hp hd hsq hmod hcop hsep hclass hidentity

/-- The manuscript obstruction from the same oriented CM quotient used by
the formal product. The quotient and good-reduction sections remain explicit
construction data; their logarithmic comparison is proved by
`CMQuotientLiftData.logarithmic_identity`.
[rolenManuscript, proof of Proposition 4.1] -/
theorem conditional_character_obstruction_of_cm_quotient
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (sign : ℤ) (hsign : sign = 1 ∨ sign = -1)
    (d : ℕ) [Fact (-(d : ℤ) < 0)]
    (hd : 0 < d) (hsq : Squarefree d) (hmod : d % 24 = 23)
    (hr : legendreSym p (-(d : ℤ)) = sign)
    (hsep : (d + 1) ^ 2 < 24 * p)
    (hclass : 8 * formClassNumber (-(d : ℤ)) < p + 1)
    (hCT : ConstantTermInputs p)
    (Icm : ConditionalCM.CMDescentInput d p)
    {F X : Type*} [CommRing F] [Algebra (ZMod p) F]
    (I : CMQuotientLiftData p d Icm F X) :
    ¬∀ j : ℕ, legendreSym p (1 - 24 * (j : ℤ)) = sign →
      ((spt j : ℤ) : ZMod p) = 0 := by
  intro hspt
  have hd22 : 22 ≤ d := by omega
  have hmul : 22 * d ≤ d * d := Nat.mul_le_mul_right d hd22
  have hdlt : d < p := by nlinarith [hmul]
  have hpd : ¬p ∣ d := Nat.not_dvd_of_pos_of_lt hd hdlt
  have hcop : ¬p ∣ 6 * d := by
    intro h
    rcases (Fact.out : p.Prime).dvd_mul.mp h with h6 | hdvd
    · exact I.hp6 h6
    · exact hpd hdvd
  have hdiff := QSeries.conditional_principal_lambert_differential
    p hp sign hsign d hd hmod hr hspt hCT
  have hidentity := I.constructed_homogeneous_lambert_identity hdiff
  exact I.geometry.no_homogeneous_identity_of_form Icm
    I.constructedLogarithmicForm I.constructed_logarithmic_identity
    hp hd hsq hmod hcop hsep hclass hidentity

end SptClassification
