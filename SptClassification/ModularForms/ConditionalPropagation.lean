/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.AuxiliaryPrime
public import SptClassification.Arithmetic.SquareClasses
public import SptClassification.QSeries.TwistedFourierSeries
public import SptClassification.ModularForms.EtaAutomorphy
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
public import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Conditional propagation of smallest-parts congruences

The input below separates the general modular progression theorem of
[garthwaiteJameson2021, Proposition 4] from the modular approximation of the
actual smallest-parts series in [rolenManuscript, §2, (2.5)]. The arithmetic
deduction, including the prime-dividing-progression-modulus case, is proved
here. Availability of the analytic inputs is a later task.
-/

public section

namespace SptClassification

open UpperHalfPlane
open scoped MatrixGroups Manifold

/-- The standard theta normalization of the half-integral automorphy factor.
Here `jacobiTheta (2τ) = ∑ n, exp(2πi n²τ)`. On `Γ₀(4)` its quotient
is the usual weight-one-half factor. The exponent `2k+1` fixes the
Nebentypus convention of [garthwaiteJameson2021, §2]. -/
noncomputable def standardProgressionFactor (k : ℕ) (halfIntegral : Bool)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane) : ℂ :=
  if halfIntegral then
    (jacobiTheta (2 * ((γ • τ : UpperHalfPlane) : ℂ)) / jacobiTheta (2 * (τ : ℂ))) ^
      (2 * k + 1)
  else (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ) ^ k

/-- Evaluation of the half-integral factor in the fixed theta normalization. -/
theorem standardProgressionFactor_half (k : ℕ)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane) :
    standardProgressionFactor k true γ τ =
      (jacobiTheta (2 * ((γ • τ : UpperHalfPlane) : ℂ)) /
        jacobiTheta (2 * (τ : ℂ))) ^ (2 * k + 1) := by
  rfl

/-- A rational-coefficient weakly holomorphic modular form with the standard
integral or theta multiplier, together with faithful reduction at `p`.
The fourth power has integral weight and trivial fourth power of its character.
Meromorphy of its integral slash at every cusp expresses finite pole order
without choosing a half-integral slash outside `Γ₀(4)`.
[garthwaiteJameson2021, §2] -/
structure ModularProgressionForm (p : ℕ) where
  level : ℕ
  level_pos : 0 < level
  weightNumerator : ℕ
  halfIntegral : Bool
  level_four : halfIntegral = true → 4 ∣ level
  toFun : UpperHalfPlane → ℂ
  holomorphic : MDiff toFun
  character : CongruenceSubgroup.Gamma0 level → ℂ
  nebentypus : DirichletCharacter ℂ level
  character_eq_nebentypus : ∀ γ,
    character γ = nebentypus
      ((((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ)
        1 1 : ℤ) : ZMod level)
  character_one : character 1 = 1
  character_mul : ∀ γ δ, character (γ * δ) = character γ * character δ
  character_quadratic : ∀ γ, character γ ^ 2 = 1
  map_action : ∀ (γ : CongruenceSubgroup.Gamma0 level) (τ : UpperHalfPlane),
    toFun ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • τ) =
      character γ * standardProgressionFactor weightNumerator halfIntegral γ τ * toFun τ
  meromorphic_cusps : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
    ∃ width : ℕ, 0 < width ∧ ∃ G : ℂ → ℂ, MeromorphicAt G 0 ∧
      ∀ τ : UpperHalfPlane,
        G (Function.Periodic.qParam width τ) =
          toFun (γ • τ) ^ 4 /
            (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ) ^
              (4 * weightNumerator + if halfIntegral then 2 else 0)
  coeff : ℤ → ℚ
  coeffMod : ℤ → ZMod p
  pIntegral : ∀ r, ∃ num den : ℤ, ¬(p : ℤ) ∣ den ∧
    coeff r = (num : ℚ) / den ∧ coeffMod r * (den : ZMod p) = (num : ZMod p)
  lowerBound : ∃ B : ℤ, ∀ r < B, coeff r = 0
  hasSum_qExpansion : ∀ τ : UpperHalfPlane,
    HasSum (fun r : ℤ => (coeff r : ℂ) * (Function.Periodic.qParam 1 τ) ^ r) (toFun τ)

/-- When a rational Fourier coefficient is an integer, the supplied faithful
reduction agrees with the ordinary residue of that integer. -/
theorem ModularProgressionForm.coeffMod_eq_intCast {p : ℕ} [Fact p.Prime]
    (g : ModularProgressionForm p) (r z : ℤ) (hz : g.coeff r = z) :
    g.coeffMod r = (z : ZMod p) := by
  obtain ⟨num, den, hden, hcoeff, hmod⟩ := g.pIntegral r
  have hden0 : den ≠ 0 := by
    intro h
    subst den
    exact hden (dvd_zero _)
  have hdenQ : (den : ℚ) ≠ 0 := by exact_mod_cast hden0
  have hnumQ : (num : ℚ) = (z : ℚ) * den := by
    rw [hz] at hcoeff
    exact (div_eq_iff hdenQ).mp hcoeff.symm
  have hnum : num = z * den := by exact_mod_cast hnumQ
  have hdenMod : (den : ZMod p) ≠ 0 := by
    intro h
    exact hden ((ZMod.intCast_zmod_eq_zero_iff_dvd den p).mp h)
  have hprod : g.coeffMod r * (den : ZMod p) = (z : ZMod p) * den := by
    rw [hmod, hnum]
    push_cast
    ring
  exact mul_right_cancel₀ hdenMod hprod

/-- The generic progression transport law, including `p ∣ M`. This is an
explicit input about every supplied modular coefficient object, not a
special rule for `spt`. It packages the powered slash identity and integral
q-expansion descent of [garthwaiteJameson2021, Proposition 4]. -/
structure ProgressionTransportInput (p : ℕ) where
  transport : ∀ (g : ModularProgressionForm p) (M : ℕ) (_hM : 0 < M)
    (u : ℤ) (a : ℕ), a.Coprime (6 * M * g.level) →
      (∀ r : ℤ, (r : ZMod M) = (u : ZMod M) → g.coeffMod r = 0) →
      ∀ r : ℤ, (r : ZMod M) =
        ((a : ZMod M) ^ 2 * (u : ZMod M)) → g.coeffMod r = 0

/-- The normalized weight-two quasimodular Fourier coefficient
`E₂ = 1 - 24 ∑_{n≥1} σ₁(n) qⁿ` [rolenManuscript, §2]. -/
def eisensteinTwoCoefficient (n : ℕ) : ℚ :=
  if n = 0 then 1 else -24 * (n.divisors.sum fun d => (d : ℚ))

theorem eisensteinTwoCoefficient_apply (n : ℕ) :
    eisensteinTwoCoefficient n =
      if n = 0 then 1 else -24 * (n.divisors.sum fun d => (d : ℚ)) := (rfl)

/-- The integral Fourier row of `E₂`. Keeping this row over `ℤ` makes its
reduction modulo every prime canonical, including primes dividing a later
progression modulus [rolenManuscript, §2, (2.5)]. -/
def eisensteinTwoIntegerCoefficient (n : ℕ) : ℤ :=
  if n = 0 then 1 else -24 * (n.divisors.sum fun d => (d : ℤ))

theorem eisensteinTwoCoefficient_eq_intCast (n : ℕ) :
    eisensteinTwoCoefficient n = (eisensteinTwoIntegerCoefficient n : ℚ) := by
  by_cases hn : n = 0
  · simp [eisensteinTwoCoefficient, eisensteinTwoIntegerCoefficient, hn]
  · simp [eisensteinTwoCoefficient, eisensteinTwoIntegerCoefficient, hn]

/-- The integral formal `E₂` series, with the same normalization as the
analytic expansion in `SptModularApproximation`. -/
noncomputable def eisensteinTwoSeries : PowerSeries ℤ :=
  PowerSeries.mk eisensteinTwoIntegerCoefficient

@[simp] theorem eisensteinTwoSeries_coeff (n : ℕ) :
    eisensteinTwoSeries.coeff n = eisensteinTwoIntegerCoefficient n := by
  simp [eisensteinTwoSeries]

theorem eisensteinTwoSeries_hasSum (q : ℂ) (F : ℂ)
    (h : HasSum (fun n : ℕ => (eisensteinTwoCoefficient n : ℂ) * q ^ n) F) :
    HasSum (fun n : ℕ => (eisensteinTwoSeries.coeff n : ℂ) * q ^ n) F := by
  have hcoeff (n : ℕ) :
      (eisensteinTwoCoefficient n : ℂ) = (eisensteinTwoSeries.coeff n : ℂ) := by
    rw [eisensteinTwoCoefficient_eq_intCast, eisensteinTwoSeries_coeff]
    norm_cast
  simpa only [hcoeff] using h

/-- Algebraic cancellation in the normalized approximation. The three
scalars are the inverses of `12`, `24`, and `288` in the coefficient ring;
their relation is derived rather than supplied. This is the coefficientwise
step in [rolenManuscript, §2, (2.5)]. -/
theorem normalizedSptCancellation {R : Type*} [CommRing R]
    (c12 c24 c288 Eminus Eplus E2 M P thetaP D S F : R)
    (h12 : c12 * 12 = 1) (h24 : c24 * 24 = 1)
    (h288 : c288 * 288 = 1)
    (hminus : Eminus = 1) (hplus : Eplus = E2)
    (hM : M = S + c12 * thetaP)
    (hD : D = thetaP + c24 * (E2 * P))
    (hF : F = Eminus * (M - c12 * D) + c288 * (Eplus * P)) :
    F = S := by
  have hproduct : (c12 * c24) * 288 = 1 := by
    calc
      (c12 * c24) * 288 = (c12 * 12) * (c24 * 24) := by ring
      _ = 1 := by rw [h12, h24]; ring
  have hcoeff : c288 = c12 * c24 := by
    calc
      c288 = c288 * ((c12 * c24) * 288) := by rw [hproduct]; ring
      _ = (c288 * 288) * (c12 * c24) := by ring
      _ = c12 * c24 := by rw [h288]; ring
  rw [hF, hminus, hplus, hM, hD, hcoeff]
  ring

/-- Formal Fourier product of the normalized representative in (2.5), using
the actual twisted rows. Its analytic realization is a separate obligation.
[rolenManuscript, §2, (2.5)] -/
noncomputable def sptNormalizedFourierProduct (p Q : ℕ) [Fact Q.Prime]
    (c12 c24 c288 Eminus Eplus E2 : LaurentSeries (ZMod p)) :
    LaurentSeries (ZMod p) :=
  Eminus *
    ((QSeries.sptTwistedLaurent p Q +
        c12 * QSeries.thetaPartitionTwistedLaurent p Q) -
      c12 * (QSeries.thetaPartitionTwistedLaurent p Q +
        c24 * (E2 * QSeries.partitionTwistedLaurent p Q))) +
    c288 * (Eplus * QSeries.partitionTwistedLaurent p Q)

/-- Convergent twisted mock and partition rows, together with the weight
`-1/2` Serre correction. These analytic data precede the construction of the
normalized modular form in [rolenManuscript, §2, (2.5)]. They include no
modular form of weight `p+1/2`, coefficient reduction or congruence. -/
structure SptTwistedAnalyticData (Q : ℕ) [Fact Q.Prime] where
  eisensteinTwo : UpperHalfPlane → ℂ
  eisensteinTwo_expansion : ∀ τ : UpperHalfPlane,
    HasSum (fun n : ℕ => (eisensteinTwoCoefficient n : ℂ) *
      (Function.Periodic.qParam 1 τ) ^ n) (eisensteinTwo τ)
  twistedM : UpperHalfPlane → ℂ
  twistedP : UpperHalfPlane → ℂ
  thetaTwistedP : UpperHalfPlane → ℂ
  serreDerivativeP : UpperHalfPlane → ℂ
  twistedP_expansion : ∀ τ : UpperHalfPlane,
    HasSum (fun r : ℤ =>
      ((negativeSquareSelector Q r * QSeries.partitionFourier r : ℚ) : ℂ) *
        (Function.Periodic.qParam 1 τ) ^ r) (twistedP τ)
  twistedM_expansion : ∀ τ : UpperHalfPlane,
    HasSum (fun r : ℤ =>
      ((negativeSquareSelector Q r *
        ((QSeries.sptFourier r : ℚ) + r * QSeries.partitionFourier r / 12) : ℚ) : ℂ) *
        (Function.Periodic.qParam 1 τ) ^ r) (twistedM τ)
  thetaTwistedP_expansion : ∀ τ : UpperHalfPlane,
    HasSum (fun r : ℤ =>
      ((r * negativeSquareSelector Q r * QSeries.partitionFourier r : ℚ) : ℂ) *
        (Function.Periodic.qParam 1 τ) ^ r) (thetaTwistedP τ)
  serreDerivativeP_eq : ∀ τ : UpperHalfPlane,
    serreDerivativeP τ = thetaTwistedP τ + eisensteinTwo τ * twistedP τ / 24

/-- Data for the exact normalized approximation
`E_(p-1) (M_Q - D_(-1/2) P_Q / 12) + E_(p+1) P_Q / 288`.
The analytic rows are independent of the prime of reduction. Modularity and
prime-local Fourier coefficients are additional properties of the normalized
representative [rolenManuscript, §2, (2.5)]. -/
structure SptModularApproximation (p Q : ℕ) (hfive : 5 ≤ p) [Fact Q.Prime]
    extends SptTwistedAnalyticData Q where
  form : ModularProgressionForm p
  weight_eq : form.weightNumerator = p
  halfIntegral_eq : form.halfIntegral = true
  level_divides : form.level ∣ 576 * Q ^ 4
  normalized_representative : ∀ τ : UpperHalfPlane,
    form.toFun τ =
      ModularForm.E (k := p - 1) (by omega) τ *
        (twistedM τ - serreDerivativeP τ / 12) +
        ModularForm.E (k := p + 1) (by omega) τ * twistedP τ / 288

/-- The analytic `E₂` in an approximation sums the integral formal row. -/
theorem SptModularApproximation.eisensteinTwoSeries_hasSum {p Q : ℕ}
    {hfive : 5 ≤ p} [Fact Q.Prime]
    (A : SptModularApproximation p Q hfive) (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ => (eisensteinTwoSeries.coeff n : ℂ) *
      Function.Periodic.qParam 1 τ ^ n) (A.eisensteinTwo τ) :=
  SptClassification.eisensteinTwoSeries_hasSum _ _ (A.eisensteinTwo_expansion τ)

/-- The selected smallest-parts function obtained by cancelling the theta
part of the twisted mock form. This is an analytic function, before reduction
of any Fourier coefficient [rolenManuscript, §2, (2.5)]. -/
noncomputable def SptTwistedAnalyticData.twistedS {Q : ℕ}
    [Fact Q.Prime] (A : SptTwistedAnalyticData Q)
    (τ : UpperHalfPlane) : ℂ :=
  A.twistedM τ - A.thetaTwistedP τ / 12

/-- Cancellation of the theta row gives the convergent selected `spt` row.
No congruence or modular-form coefficient identification is used here. -/
theorem SptTwistedAnalyticData.twistedS_expansion {Q : ℕ} [Fact Q.Prime]
    (A : SptTwistedAnalyticData Q) (τ : UpperHalfPlane) :
    HasSum (fun r : ℤ =>
      ((negativeSquareSelector Q r * (QSeries.sptFourier r : ℚ) : ℚ) : ℂ) *
        Function.Periodic.qParam 1 τ ^ r) (A.twistedS τ) := by
  have htheta :=
    (A.thetaTwistedP_expansion τ).const_smul (1 / 12 : ℂ)
  have h := (A.twistedM_expansion τ).sub htheta
  convert h using 1
  · ext r
    push_cast
    ring
  · simp only [SptTwistedAnalyticData.twistedS]
    ring

/-- Selected smallest-parts function of a constructed approximation. -/
noncomputable def SptModularApproximation.twistedS {p Q : ℕ} {hfive : 5 ≤ p}
    [Fact Q.Prime] (A : SptModularApproximation p Q hfive) :
    UpperHalfPlane → ℂ := A.toSptTwistedAnalyticData.twistedS

/-- The selected Fourier row is independent of the modularity construction. -/
theorem SptModularApproximation.twistedS_expansion {p Q : ℕ}
    {hfive : 5 ≤ p} [Fact Q.Prime]
    (A : SptModularApproximation p Q hfive) (τ : UpperHalfPlane) :
    HasSum (fun r : ℤ =>
      ((negativeSquareSelector Q r * (QSeries.sptFourier r : ℚ) : ℚ) : ℂ) *
        Function.Periodic.qParam 1 τ ^ r) (A.twistedS τ) :=
  A.toSptTwistedAnalyticData.twistedS_expansion τ

/-- The normalized analytic function, defined before proving its modularity. -/
noncomputable def SptTwistedAnalyticData.normalizedRepresentative {Q : ℕ}
    [Fact Q.Prime] (A : SptTwistedAnalyticData Q) (p : ℕ) (hp : 5 ≤ p)
    (τ : UpperHalfPlane) : ℂ :=
  ModularForm.E (k := p - 1) (by omega) τ *
    (A.twistedM τ - A.serreDerivativeP τ / 12) +
    ModularForm.E (k := p + 1) (by omega) τ * A.twistedP τ / 288

/-- The defining normalized expression as a public evaluation rule. -/
theorem SptTwistedAnalyticData.normalizedRepresentative_apply {Q : ℕ}
    [Fact Q.Prime] (A : SptTwistedAnalyticData Q) (p : ℕ) (hp : 5 ≤ p)
    (τ : UpperHalfPlane) :
    A.normalizedRepresentative p hp τ =
      ModularForm.E (k := p - 1) (by omega) τ *
        (A.twistedM τ - A.serreDerivativeP τ / 12) +
      ModularForm.E (k := p + 1) (by omega) τ * A.twistedP τ / 288 := by
  rfl

/-- Cancelling the theta term isolates the quasimodular correction. -/
theorem SptTwistedAnalyticData.normalizedRepresentative_eq {Q : ℕ}
    [Fact Q.Prime] (A : SptTwistedAnalyticData Q) (p : ℕ) (hp : 5 ≤ p)
    (τ : UpperHalfPlane) :
    A.normalizedRepresentative p hp τ =
      ModularForm.E (k := p - 1) (by omega) τ *
        (A.twistedS τ - A.eisensteinTwo τ * A.twistedP τ / 288) +
      ModularForm.E (k := p + 1) (by omega) τ * A.twistedP τ / 288 := by
  rw [SptTwistedAnalyticData.normalizedRepresentative, A.serreDerivativeP_eq τ]
  dsimp [SptTwistedAnalyticData.twistedS]
  ring

/-- The analytic normalized representative separates into the selected
smallest-parts function and the `E₂ P_Q` correction. This is the pointwise
identity underlying the coefficient comparison in (2.5). -/
theorem SptModularApproximation.normalized_representative_eq {p Q : ℕ}
    {hfive : 5 ≤ p} [Fact Q.Prime]
    (A : SptModularApproximation p Q hfive) (τ : UpperHalfPlane) :
    A.form.toFun τ =
      ModularForm.E (k := p - 1) (by omega) τ *
        (A.twistedS τ - A.eisensteinTwo τ * A.twistedP τ / 288) +
      ModularForm.E (k := p + 1) (by omega) τ * A.twistedP τ / 288 := by
  rw [A.normalized_representative τ, A.serreDerivativeP_eq τ]
  dsimp [SptModularApproximation.twistedS, SptTwistedAnalyticData.twistedS]
  ring

/-- AP supplies the genuine normalized form for each auxiliary prime. -/
structure SptApproximationInput (p : ℕ) (hfive : 5 ≤ p) where
  forPrime : ∀ Q : ℕ, ∀ hQ : Q.Prime, ¬Q ∣ 6 * p →
    @SptModularApproximation p Q hfive ⟨hQ⟩

/-- The two independent inputs used in the conditional propagation argument:
generic modular progression transport and the actual smallest-parts modular
approximation [garthwaiteJameson2021, Proposition 4],
[rolenManuscript, §2]. Neither field asserts their unconditional existence. -/
structure ProgressionInputs (p : ℕ) (hfive : 5 ≤ p) where
  transport : ProgressionTransportInput p
  approximation : SptApproximationInput p hfive

end SptClassification
