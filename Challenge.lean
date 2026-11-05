module

public import Mathlib

/-!
# Conditional classification of smallest-parts congruences

The hypotheses below are explicit literature and geometric inputs. This
statement does not claim that those inputs have been constructed in Lean.
The smallest-parts function is defined directly from integer partitions.
-/

@[expose] public section

-- Preserve the standard ring operations when importing the complete Mathlib surface.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace SptClassification
/-- The quadratic character on residue classes modulo twelve. -/
@[expose] def characterTwelveResidue (a : ZMod 12) : ℤ :=
  if a = 1 ∨ a = 11 then 1 else if a = 5 ∨ a = 7 then -1 else 0
/-- The integer-periodic quadratic character of conductor twelve. -/
def characterTwelve (a : ℤ) : ℤ := characterTwelveResidue a
end SptClassification

namespace SptClassification
/-- The coefficient multiplier of the quadratic twist selecting negative nonresidues. -/
def negativeSquareSelector (p : ℕ) [Fact p.Prime] (u : ℤ) : ℚ :=
  ((legendreSym p u : ℚ) ^ 2 -
    (legendreSym p (-1) : ℚ) * (legendreSym p u : ℚ)) / 2
end SptClassification

namespace SptClassification
/-- An integral binary quadratic form `a * X² + b * X * Y + c * Y²`. -/
@[ext] structure BinaryQuadraticForm where
  a : ℤ
  b : ℤ
  c : ℤ
  deriving DecidableEq
namespace BinaryQuadraticForm
/-- The discriminant in the binary quadratic form convention. -/
def discriminant (Q : BinaryQuadraticForm) : ℤ := Q.b ^ 2 - 4 * Q.a * Q.c
/-- The nonnegative content; the zero form has content zero. -/
def content (Q : BinaryQuadraticForm) : ℕ := Int.gcd Q.a (Int.gcd Q.b Q.c)
end BinaryQuadraticForm
end SptClassification

namespace SptClassification.BinaryQuadraticForm
/-- Substitution of the linear variables given by a two-by-two matrix. -/
def pullback (Q : BinaryQuadraticForm) (M : Matrix (Fin 2) (Fin 2) ℤ) :
    BinaryQuadraticForm where
  a := Q.a * M 0 0 ^ 2 + Q.b * M 0 0 * M 1 0 + Q.c * M 1 0 ^ 2
  b := 2 * Q.a * M 0 0 * M 0 1 + Q.b * (M 0 0 * M 1 1 + M 0 1 * M 1 0) +
    2 * Q.c * M 1 0 * M 1 1
  c := Q.a * M 0 1 ^ 2 + Q.b * M 0 1 * M 1 1 + Q.c * M 1 1 ^ 2

theorem discriminant_pullback (Q : BinaryQuadraticForm) (M : Matrix (Fin 2) (Fin 2) ℤ) :
    (Q.pullback M).discriminant = M.det ^ 2 * Q.discriminant := by sorry
/-- Left action by substitution with the inverse unimodular matrix. -/
def transform (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) (Q : BinaryQuadraticForm) :
    BinaryQuadraticForm := Q.pullback (↑(g⁻¹) : Matrix (Fin 2) (Fin 2) ℤ)

theorem discriminant_transform (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (Q : BinaryQuadraticForm) : (transform g Q).discriminant = Q.discriminant := by sorry

theorem content_transform (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (Q : BinaryQuadraticForm) : (transform g Q).content = Q.content := by sorry

theorem pullback_a_pos (Q : BinaryQuadraticForm) (ha : 0 < Q.a)
    (hD : Q.discriminant < 0) (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det = 1) :
    0 < (Q.pullback M).a := by sorry
end SptClassification.BinaryQuadraticForm

namespace SptClassification.BinaryQuadraticForm

theorem transform_a_pos (Q : BinaryQuadraticForm) (ha : 0 < Q.a)
    (hD : Q.discriminant < 0) (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    0 < (transform g Q).a := by sorry
end SptClassification.BinaryQuadraticForm

namespace SptClassification
/-- Positive integral forms of fixed discriminant, without a level condition. -/
structure PositiveForm (D : ℤ) extends BinaryQuadraticForm where
  a_pos : 0 < a
  discriminant_eq : toBinaryQuadraticForm.discriminant = D
namespace PositiveForm

def transform {D : ℤ} (hD : D < 0) (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (Q : PositiveForm D) : PositiveForm D where
  toBinaryQuadraticForm := BinaryQuadraticForm.transform g Q.toBinaryQuadraticForm
  a_pos := Q.toBinaryQuadraticForm.transform_a_pos Q.a_pos (Q.discriminant_eq.trans_lt hD) g
  discriminant_eq := (BinaryQuadraticForm.discriminant_transform g Q.toBinaryQuadraticForm).trans
    Q.discriminant_eq

@[simp] theorem transform_one {D : ℤ} (hD : D < 0) (Q : PositiveForm D) :
    transform hD 1 Q = Q := by sorry

theorem transform_mul {D : ℤ} (hD : D < 0) (g h : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (Q : PositiveForm D) : transform hD (g * h) Q = transform hD g (transform hD h Q) := by sorry

instance modularAction {D : ℤ} [Fact (D < 0)] :
    MulAction (Matrix.SpecialLinearGroup (Fin 2) ℤ) (PositiveForm D) where
  smul := transform Fact.out
  one_smul := transform_one Fact.out
  mul_smul := transform_mul Fact.out

@[simp] theorem toBinaryQuadraticForm_smul {D : ℤ} [Fact (D < 0)]
    (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) (Q : PositiveForm D) :
    (g • Q).toBinaryQuadraticForm = BinaryQuadraticForm.transform g Q.toBinaryQuadraticForm := by sorry
end PositiveForm
end SptClassification

namespace SptClassification
/-- Proper classes of positive integral forms of a negative discriminant. -/
def FormClass (D : ℤ) [Fact (D < 0)] :=
  MulAction.orbitRel.Quotient (Matrix.SpecialLinearGroup (Fin 2) ℤ) (PositiveForm D)
namespace FormClass
/-- The content is independent of the chosen proper representative. -/
def content {D : ℤ} [Fact (D < 0)] : FormClass D → ℕ :=
  Quotient.lift (fun Q : PositiveForm D => Q.toBinaryQuadraticForm.content) (by
    intro Q R h
    obtain ⟨g, hg⟩ := h
    rw [← hg, PositiveForm.toBinaryQuadraticForm_smul, BinaryQuadraticForm.content_transform])
end FormClass
/-- Proper primitive classes, expressed as the content-one part of the class space. -/
def PrimitiveFormClass (D : ℤ) [Fact (D < 0)] := {C : FormClass D // C.content = 1}
/-- The proper class number, in its integral binary-form realization. -/
noncomputable def formClassNumber (D : ℤ) [Fact (D < 0)] : ℕ := Nat.card (PrimitiveFormClass D)
end SptClassification

namespace SptClassification

variable (p : ℕ) [Fact p.Prime]
/-- The precise constant-interval estimate used in §5 of [rolenManuscript].
Its availability is an explicit input; the character estimate of
[trevino2012, trevino2017] is not proved here. -/
structure CharacterIntervalInput : Prop where
  bound : ∀ (p : ℕ) [Fact p.Prime], Odd p →
    ∀ (χ : DirichletCharacter ℂ p), χ ≠ 1 →
    ∀ (a : ℤ) (H : ℕ), 1 ≤ H →
    ∀ (c : ℂ), c ≠ 0 →
    (∀ j : ℕ, 1 ≤ j → j ≤ H → χ ((a + (j : ℤ)) : ZMod p) = c) →
    (H : ℝ) ≤ (169 / 50 : ℝ) * (p : ℝ) ^ (1 / 4 : ℝ) * Real.log p
end SptClassification

namespace SptClassification
/-- The number of occurrences of a least part in a partition. -/
def smallestMultiplicity {n : ℕ} (p : Nat.Partition n) : ℕ :=
  p.parts.countP fun a => ∀ b ∈ p.parts, a ≤ b
/-- Andrews' smallest-parts function. -/
noncomputable def spt (n : ℕ) : ℕ :=
  ∑ p : Nat.Partition n, smallestMultiplicity p
/-- The ordinary partition function. -/
noncomputable def partitionCount (n : ℕ) : ℕ :=
  Fintype.card (Nat.Partition n)
end SptClassification

namespace SptClassification
/-- The previously published canonical necessity theorem and Andrews'
three congruences. Its first field concerns only canonical progressions;
it does not assume exclusion of any noncanonical progression. -/
structure CanonicalInputs : Prop where
  canonicalNecessity : ∀ (p b : ℕ), p.Prime → 5 ≤ p → b < p →
    ((24 * b : ℕ) : ZMod p) = 1 →
    (∀ n : ℕ, p ∣ spt (p * n + b)) → p = 5 ∨ p = 7 ∨ p = 13
  andrewsFive : ∀ n : ℕ, 5 ∣ spt (5 * n + 4)
  andrewsSeven : ∀ n : ℕ, 7 ∣ spt (7 * n + 5)
  andrewsThirteen : ∀ n : ℕ, 13 ∣ spt (13 * n + 6)
end SptClassification

namespace SptClassification.QSeries
/-- The downward square-index shift, extended by zero at nonintegral indices. -/
def squareDown {K : Type*} [Zero K] (p : ℕ) (A : ℤ → K) (r : ℤ) : K :=
  if (p : ℤ) ^ 2 ∣ r then A (r / (p : ℤ) ^ 2) else 0
/-- The three-term coefficient action with specified diagonal and downward multipliers. -/
def squareHecke {K : Type*} [Semiring K]
    (p : ℕ) (middle : ℤ → K) (last : K) (A : ℤ → K) (r : ℤ) : K :=
  A ((p : ℤ) ^ 2 * r) + middle r * A r + last * squareDown p A r
end SptClassification.QSeries

namespace SptClassification.QSeries
/-- Place a sequence at the integral indices `24n - 1` and extend it by zero.
The support test is used by modular-form propagation proofs. -/
@[expose] noncomputable def shiftedTwentyFour (a : ℕ → ℤ) (r : ℤ) : ℤ :=
  by
    classical
    exact if h : (∃ n : ℕ, r = 24 * (n : ℤ) - 1) then a (Classical.choose h) else 0
/-- Coefficients of `P = η⁻¹` at exponents `r/24`. -/
noncomputable def partitionFourier (r : ℤ) : ℤ :=
  shiftedTwentyFour (fun n => (partitionCount n : ℤ)) r
/-- Coefficients of the smallest-parts series at exponents `r/24`. -/
@[expose] noncomputable def sptFourier (r : ℤ) : ℤ :=
  shiftedTwentyFour (fun n => (spt n : ℤ)) r
/-- The unscaled coefficients `a(r)` of `f = -12 S - 24 Θ P`. -/
noncomputable def fFourier (r : ℤ) : ℤ :=
  -12 * sptFourier r - r * partitionFourier r
end SptClassification.QSeries

namespace SptClassification
/-- The explicit level-six eta quotient used to evaluate CM points. -/
noncomputable def levelSixEtaQuotient (z : ℂ) : ℂ :=
  ModularForm.eta z ^ 5 * ModularForm.eta (3 * z) /
    (ModularForm.eta (2 * z) * ModularForm.eta (6 * z) ^ 5)
end SptClassification

namespace SptClassification

open UpperHalfPlane

open scoped MatrixGroups Manifold
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
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
/-- Explicit lower bounds used in the two Eisenstein-series parameters. -/
theorem eisensteinWeightMinus_ge_three (p : ℕ) (hfive : 5 ≤ p) : 3 ≤ p - 1 := by sorry
theorem eisensteinWeightPlus_ge_three (p : ℕ) (hfive : 5 ≤ p) : 3 ≤ p + 1 := by sorry
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
      ModularForm.E (k := p - 1) (eisensteinWeightMinus_ge_three p hfive) τ *
        (twistedM τ - serreDerivativeP τ / 12) +
        ModularForm.E (k := p + 1) (eisensteinWeightPlus_ge_three p hfive) τ * twistedP τ / 288
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

namespace SptClassification
namespace GammaZeroSix
end GammaZeroSix
/-- The actual analytic eta quotient is invariant under every element of Γ₀(6). -/
theorem levelSixEtaQuotient_gamma0 (g : CongruenceSubgroup.Gamma0 6) (z : UpperHalfPlane) :
    levelSixEtaQuotient (↑((g : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z : UpperHalfPlane) : ℂ) =
      levelSixEtaQuotient z := by sorry
end SptClassification

namespace SptClassification.QSeries
/-- Compose coefficient Hecke steps, retaining repeated entries. -/
def squareHeckeWord {K : Type*} [Semiring K]
    (middle : ℕ → ℤ → K) (last : ℕ → K) : List ℕ → (ℤ → K) → (ℤ → K)
  | [], A => A
  | p :: ps, A => squareHeckeWord middle last ps (squareHecke p (middle p) (last p) A)
/-- The integral diagonal multiplier before embedding in rational coefficients. -/
def etaHeckeDiagonalInt (p : ℕ) (r : ℤ) : ℤ :=
  jacobiSym 12 p * jacobiSym (-r) p
/-- The integral weight-`3/2` word, whose coefficients supply the integers `c_t`. -/
def heckeThreeHalfWordInt (ps : List ℕ) (A : ℤ → ℤ) : ℤ → ℤ :=
  squareHeckeWord etaHeckeDiagonalInt (fun p => (p : ℤ)) ps A
end SptClassification.QSeries

namespace SptClassification.QSeries
/-- Indices supporting the negative divisor-square principal part. -/
def negativeDivisorSquareIndices (m : ℕ) : Finset ℤ :=
  m.divisors.image (fun t : ℕ => - (t : ℤ) ^ 2)
/-- All indices which can contribute to the constant coefficient of the
product when the other factor has its only negative index at `-d`. -/
def constantTermIndices (m d : ℕ) : Finset ℤ :=
  insert (d : ℤ) (negativeDivisorSquareIndices m)
/-- A finite coefficient convolution at exponent zero. -/
def finiteConstantTerm {K : Type*} [Semiring K]
    (I : Finset ℤ) (A B : ℤ → K) : K :=
  ∑ r ∈ I, A r * B (-r)
end SptClassification.QSeries

namespace SptClassification.QSeries
/-- Integral row reduction, retaining every Fourier coefficient of the rows. -/
noncomputable def principalPartElimination (raw : ℕ → ℤ → ℤ) (n : ℕ) : ℤ → ℤ :=
  Nat.strongRecOn n fun n ih r =>
    raw n r - Finset.sum (Finset.univ : Finset (Finset.range n))
      (fun k => raw n (k : ℤ) * ih k (Finset.mem_range.mp k.property) r)
end SptClassification.QSeries

namespace SptClassification.QSeries

open PowerSeries
/-- The Euler derivative on ordinary formal power series. -/
noncomputable def eulerDerivative {R : Type*} [CommSemiring R]
    (F : PowerSeries R) : PowerSeries R :=
  X * PowerSeries.derivative F
end SptClassification.QSeries

namespace SptClassification.QSeries

open PowerSeries
/-- The Laurent coefficients of `q^(-n) F`, indexed by the possible pole. -/
noncomputable def shiftedPrincipalRow (F : PowerSeries ℤ) (n : ℕ) (k : ℤ) : ℤ :=
  if k ≤ (n : ℤ) then F.coeff (((n : ℤ) - k).toNat) else 0
/-- Coefficients of `η j^n`, provided `U` and `J` are the associated unit series. -/
noncomputable def etaJRow (U J : PowerSeries ℤ) (n : ℕ) : ℤ → ℤ :=
  shiftedPrincipalRow (U * J ^ n) n
/-- Coefficients of `-η (Θ j) j^n`, with the leading pole reindexed by `n`. -/
noncomputable def etaThetaJRow (U J : PowerSeries ℤ) (n : ℕ) : ℤ → ℤ :=
  shiftedPrincipalRow (U * (J - eulerDerivative J) * J ^ n) n
end SptClassification.QSeries

namespace SptClassification.QSeries

open PowerSeries
/-- Integral elimination of the poles of the rows `η j^n`. -/
noncomputable def etaPrincipalBasis (U J : PowerSeries ℤ) (n : ℕ) : ℤ → ℤ :=
  principalPartElimination (etaJRow U J) n
/-- Integral elimination of the poles of the rows `-η (Θ j) j^n`. -/
noncomputable def etaThetaPrincipalBasis (U J : PowerSeries ℤ) (n : ℕ) : ℤ → ℤ :=
  principalPartElimination (etaThetaJRow U J) n
/-- Prescribe the first nonpolar eta coefficient after eliminating all poles. -/
noncomputable def etaPrincipalWithConstant (U J : PowerSeries ℤ)
    (n : ℕ) (c : ℤ) : ℤ → ℤ :=
  fun k => etaPrincipalBasis U J n k + c * etaJRow U J 0 k
end SptClassification.QSeries

namespace SptClassification.QSeries

open PowerSeries
/-- The normalized integral Fourier coefficients of the weight-four Eisenstein series. -/
def eisensteinFourCoefficient (n : ℕ) : ℤ :=
  if n = 0 then 1 else 240 * ∑ d ∈ n.divisors, (d : ℤ) ^ 3
/-- The integral ordinary power series of the normalized weight-four Eisenstein series. -/
noncomputable def eisensteinFourSeries : PowerSeries ℤ :=
  PowerSeries.mk eisensteinFourCoefficient
/-- The unit series `qj` expressed through the ordinary eta reciprocal core. -/
noncomputable def modularJCore (P : PowerSeries ℤ) : PowerSeries ℤ :=
  eisensteinFourSeries ^ 3 * P ^ 24
/-- The ordinary integral core `q^(-1/24)η`, formed from a partition series. -/
noncomputable def etaCoreFromPartition (P : PowerSeries ℤ) : PowerSeries ℤ :=
  P.invOfUnit 1
end SptClassification.QSeries

namespace SptClassification
/-- Weight one for allowed parts and zero for smaller parts. -/
def lowerBoundWeight (m i : ℕ) (_c : ℕ) : ℤ := if m ≤ i then 1 else 0
end SptClassification

namespace SptClassification.QSeries

open PowerSeries
/-- The generating function of partitions all of whose parts are at least `m`. -/
noncomputable def restrictedPartitionSeries (m : ℕ) : PowerSeries ℤ :=
  Nat.Partition.genFun (lowerBoundWeight m)
end SptClassification.QSeries

namespace SptClassification.QSeries

open PowerSeries
/-- The ordinary generating series of the actual partition numbers. -/
noncomputable def partitionSeries : PowerSeries ℤ := restrictedPartitionSeries 1
/-- The integral eta product core, obtained by inverting the partition series. -/
noncomputable def etaIntegralCore : PowerSeries ℤ :=
  etaCoreFromPartition partitionSeries
/-- The integral ordinary core of `qj`. -/
noncomputable def modularJIntegralCore : PowerSeries ℤ :=
  modularJCore partitionSeries
/-- The row-reduced integral coefficients of `-η(Θj)j^n`. -/
noncomputable def integralEtaThetaPrincipalBasis (n : ℕ) : ℤ → ℤ :=
  etaThetaPrincipalBasis etaIntegralCore modularJIntegralCore n
/-- For `d ≡ 23 (mod 24)`, the eta row indexed by `n` has pole `q^(-d/24)`. -/
def principalIndex (d : ℕ) : ℕ := (d + 1) / 24
/-- The integral `H_d` coefficient sequence before identifying its prescribed
constant term with the coefficient of the actual harmonic Maass form. -/
noncomputable def integralHPrincipalPart (d : ℕ) (a : ℤ) : ℤ → ℤ :=
  etaPrincipalWithConstant etaIntegralCore modularJIntegralCore
    (principalIndex d) (-a)
/-- The integral `K_d` coefficient sequence; the derivative rows start one
index later than the eta rows. -/
noncomputable def integralKPrincipalPart (d : ℕ) : ℤ → ℤ :=
  integralEtaThetaPrincipalBasis (principalIndex d - 1)
end SptClassification.QSeries

namespace SptClassification.QSeries
/-- The full integer-indexed H coefficients, with prescribed coefficient `-a` at one. -/
noncomputable def principalHFourier (d : ℕ) (a r : ℤ) : ℤ :=
  if r % 24 = 1 then integralHPrincipalPart d a ((1 - r) / 24) else 0
/-- The full integer-indexed K coefficients, including the derivative pole shift. -/
noncomputable def principalKFourier (d : ℕ) (r : ℤ) : ℤ :=
  if r % 24 = 1 then integralKPrincipalPart d ((1 - r) / 24 - 1) else 0
end SptClassification.QSeries

namespace SptClassification.QSeries
/-- The weight `-1/2` word reduced to the prime field, with zero at
nonintegral downward indices inherited from `squareDown`. -/
def heckeMinusHalfWordMod (l : ℕ) [Fact l.Prime]
    (ps : List ℕ) (A : ℤ → ZMod l) :
    ℤ → ZMod l :=
  squareHeckeWord
    (fun p r => (etaHeckeDiagonalInt p r : ZMod l) / (p : ZMod l) ^ 2)
    (fun p => (1 : ZMod l) / (p : ZMod l) ^ 3) ps A
end SptClassification.QSeries

namespace SptClassification.QSeries
/-- Vanishing of both finite weight-two product constant terms for every
admissible principal part and every positive Hecke index prime to `6 * p`.
The prime-factor list retains multiplicities. The second product uses the
integral normalization `n² (P|Uₙ)` modulo `p`. -/
structure ConstantTermInputs (p : ℕ) [Fact p.Prime] where
  hPairing : ∀ d n : ℕ, d % 24 = 23 → 0 < n → n.Coprime (6 * p) →
    finiteConstantTerm (constantTermIndices n.primeFactorsList.prod d)
      (fun r => (heckeThreeHalfWordInt n.primeFactorsList fFourier r : ZMod p))
      (fun r => (principalHFourier d (fFourier d) r : ZMod p)) = 0
  kPairing : ∀ d n : ℕ, d % 24 = 23 → 0 < n → n.Coprime (6 * p) →
    finiteConstantTerm (constantTermIndices n.primeFactorsList.prod d)
      (fun r => (n.primeFactorsList.prod : ZMod p) ^ 2 *
        heckeMinusHalfWordMod p n.primeFactorsList
          (fun s => (partitionFourier s : ZMod p)) r)
      (fun r => (principalKFourier d r : ZMod p)) = 0
end SptClassification.QSeries

namespace SptClassification.QSeries
/-- The coefficient of the logarithmic Lambert series attached to square coefficients. -/
def logarithmicLambertCoeff {K : Type*} [CommRing K] (h : ℕ → K) (n : ℕ) : K :=
  -∑ m ∈ n.divisors, (characterTwelve (m : ℤ) : K) * (m : K) * h (m ^ 2)
/-- The coefficient of the weight-four Lambert series attached to square coefficients. -/
def shimuraLambertCoeff {K : Type*} [CommRing K] (k : ℕ → K) (n : ℕ) : K :=
  ∑ m ∈ n.divisors, (characterTwelve (m : ℤ) : K) * (n / m : ℕ) * k (m ^ 2)
/-- The formal logarithmic Lambert series, specified by its finite divisor-sum coefficients. -/
def logarithmicLambertSeries {K : Type*} [CommRing K] (h : ℕ → K) : PowerSeries K :=
  PowerSeries.mk (logarithmicLambertCoeff h)
/-- The formal weight-four Lambert series, specified by its finite divisor-sum coefficients. -/
def shimuraLambertSeries {K : Type*} [CommRing K] (k : ℕ → K) : PowerSeries K :=
  PowerSeries.mk (shimuraLambertCoeff k)
end SptClassification.QSeries

namespace SptClassification.QSeries
/-- The logarithmic Lambert series formed from the prescribed `H_d`
square-index coefficients. Its constant coefficient is zero. -/
noncomputable def principalLogarithmicLambertSeries (p d : ℕ) [Fact p.Prime] :
    PowerSeries (ZMod p) :=
  logarithmicLambertSeries
    (fun r => (principalHFourier d (fFourier d) (r : ℤ) : ZMod p))
/-- The weight-four Lambert series formed from the prescribed `K_d`
square-index coefficients. Its constant coefficient is zero. -/
noncomputable def principalShimuraLambertSeries (p d : ℕ) [Fact p.Prime] :
    PowerSeries (ZMod p) :=
  shimuraLambertSeries
    (fun r => (principalKFourier d (r : ℤ) : ZMod p))
end SptClassification.QSeries

namespace SptClassification
/-- All positive integral forms with the prescribed level-six orientation.
No condition on the content is imposed. -/
structure LevelSixForm (D : ℤ) (r : ZMod 12) extends BinaryQuadraticForm where
  a_pos : 0 < a
  discriminant_eq : toBinaryQuadraticForm.discriminant = D
  six_dvd_a : 6 ∣ a
  b_residue : (b : ZMod 12) = r
namespace BinaryQuadraticForm

theorem six_dvd_pullback_a (Q : BinaryQuadraticForm)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hQ : 6 ∣ Q.a) (hM : 6 ∣ M 1 0) :
    6 ∣ (Q.pullback M).a := by sorry

theorem pullback_b_residue (Q : BinaryQuadraticForm)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hQ : 6 ∣ Q.a) (hM : 6 ∣ M 1 0)
    (hdet : M.det = 1) : ((Q.pullback M).b : ZMod 12) = Q.b := by sorry
end BinaryQuadraticForm
namespace LevelSixForm
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- The action with the negative-discriminant hypothesis made explicit. -/
def transform {D : ℤ} {r : ZMod 12} (hD : D < 0)
    (g : CongruenceSubgroup.Gamma0 6) (Q : LevelSixForm D r) : LevelSixForm D r := by
  let M : Matrix.SpecialLinearGroup (Fin 2) ℤ := (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)⁻¹
  have hM : 6 ∣ M 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (M 1 0) 6).mp
    (show (M 1 0 : ZMod 6) = 0 from (g⁻¹).property)
  refine {
    toBinaryQuadraticForm := Q.toBinaryQuadraticForm.pullback (M : Matrix (Fin 2) (Fin 2) ℤ)
    a_pos := Q.toBinaryQuadraticForm.pullback_a_pos Q.a_pos (Q.discriminant_eq.trans_lt hD) _ M.property
    discriminant_eq := ?_
    six_dvd_a := Q.toBinaryQuadraticForm.six_dvd_pullback_a _ Q.six_dvd_a hM
    b_residue := (Q.toBinaryQuadraticForm.pullback_b_residue _ Q.six_dvd_a hM M.property).trans Q.b_residue }
  rw [BinaryQuadraticForm.discriminant_pullback, M.property, one_pow, one_mul]
  exact Q.discriminant_eq

@[simp] theorem transform_one {D : ℤ} {r : ZMod 12} (hD : D < 0)
    (Q : LevelSixForm D r) : transform hD 1 Q = Q := by sorry

theorem transform_mul {D : ℤ} {r : ZMod 12} (hD : D < 0)
    (g h : CongruenceSubgroup.Gamma0 6) (Q : LevelSixForm D r) :
    transform hD (g * h) Q = transform hD g (transform hD h Q) := by sorry

instance gammaZeroAction {D : ℤ} {r : ZMod 12} [Fact (D < 0)] :
    MulAction (CongruenceSubgroup.Gamma0 6) (LevelSixForm D r) where
  smul := transform Fact.out
  one_smul := transform_one Fact.out
  mul_smul := transform_mul Fact.out

theorem content_smul {D : ℤ} {r : ZMod 12} [Fact (D < 0)]
    (g : CongruenceSubgroup.Gamma0 6) (Q : LevelSixForm D r) :
    (g • Q).toBinaryQuadraticForm.content = Q.toBinaryQuadraticForm.content := by sorry
end LevelSixForm
end SptClassification

namespace SptClassification
/-- The `Γ₀(6)`-orbit space of positive forms with fixed negative discriminant
and fixed middle-coefficient residue. -/
def CMClass (D : ℤ) (r : ZMod 12) [Fact (D < 0)] :=
  Quotient (MulAction.orbitRel (CongruenceSubgroup.Gamma0 6) (LevelSixForm D r))
namespace CMClass
/-- The content of a class, independent of the representative. -/
def content {D : ℤ} {r : ZMod 12} [Fact (D < 0)] : CMClass D r → ℕ :=
  Quotient.lift (fun Q : LevelSixForm D r => Q.toBinaryQuadraticForm.content) (by
    intro Q R h
    obtain ⟨g, hg⟩ := h
    rw [← hg, LevelSixForm.content_smul])
end CMClass
/-- Classes whose representatives have content one. -/
def PrimitiveCMClass (D : ℤ) (r : ZMod 12) [Fact (D < 0)] :=
  {C : CMClass D r // CMClass.content C = 1}
namespace LevelSixForm
/-- Forget the level and orientation conditions. -/
def toPositiveForm {D : ℤ} {r : ZMod 12} (Q : LevelSixForm D r) : PositiveForm D where
  toBinaryQuadraticForm := Q.toBinaryQuadraticForm
  a_pos := Q.a_pos
  discriminant_eq := Q.discriminant_eq
end LevelSixForm
namespace CMClass
end CMClass
end SptClassification

namespace SptClassification
namespace PositiveForm
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- The upper-half-plane root, with the positive real square root of `-D`. -/
noncomputable def cmPoint {D : ℤ} [Fact (D < 0)] (Q : PositiveForm D) : UpperHalfPlane :=
  ⟨⟨-(Q.b : ℝ) / (2 * (Q.a : ℝ)), Real.sqrt (-(D : ℝ)) / (2 * (Q.a : ℝ))⟩, by
    apply div_pos
    · apply Real.sqrt_pos.mpr
      exact_mod_cast (neg_pos.mpr (Fact.out : D < 0))
    · exact mul_pos (by norm_num) (by exact_mod_cast Q.a_pos)⟩
end PositiveForm
namespace LevelSixForm
/-- The CM point of an oriented level-six form. -/
noncomputable def cmPoint {D : ℤ} {r : ZMod 12} [Fact (D < 0)]
    (Q : LevelSixForm D r) : UpperHalfPlane := Q.toPositiveForm.cmPoint
end LevelSixForm
end SptClassification

open scoped MatrixGroups
namespace SptClassification
namespace BinaryQuadraticForm
end BinaryQuadraticForm
namespace PositiveForm
end PositiveForm
namespace LevelSixForm

theorem cmPoint_smul {D : ℤ} {r : ZMod 12} [Fact (D < 0)]
    (g : CongruenceSubgroup.Gamma0 6) (Q : LevelSixForm D r) :
    (g • Q).cmPoint = g • Q.cmPoint := by sorry
end LevelSixForm
end SptClassification

namespace SptClassification

instance primitiveCMClassFinite (D : ℤ) (r : ZMod 12) [Fact (D < 0)] :
    Finite (PrimitiveCMClass D r) := by sorry
namespace CMClass
/-- The actual eta-quotient value, independent of the oriented class representative. -/
noncomputable def etaValue {D : ℤ} {r : ZMod 12} [Fact (D < 0)] : CMClass D r → ℂ :=
  Quotient.lift (fun Q : LevelSixForm D r => levelSixEtaQuotient Q.cmPoint) (by
    intro Q R h
    obtain ⟨g, hg⟩ := h
    rw [← hg, LevelSixForm.cmPoint_smul]
    exact levelSixEtaQuotient_gamma0 g R.cmPoint)
end CMClass

open Polynomial
/-- The monic complex polynomial for one oriented primitive CM class space. -/
noncomputable def complexCMPolynomial (D : ℤ) (r : ZMod 12) [Fact (D < 0)] : ℂ[X] := by
  classical
  letI := Fintype.ofFinite (PrimitiveCMClass D r)
  exact ∏ C : PrimitiveCMClass D r, (X - Polynomial.C C.val.etaValue)
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- The complex realization of `A_d`, with the middle-coefficient classes1 and11. -/
noncomputable def cmClassPolynomialA (D : ℤ) [Fact (D < 0)] : ℂ[X] :=
  complexCMPolynomial D 1 * complexCMPolynomial D 11
/-- The complex realization of `B_d`, with the middle-coefficient classes5 and7. -/
noncomputable def cmClassPolynomialB (D : ℤ) [Fact (D < 0)] : ℂ[X] :=
  complexCMPolynomial D 5 * complexCMPolynomial D 7
end SptClassification

namespace SptClassification
namespace ConditionalCM
/-- An integral preserving order, its rational division algebra, and the
action on the cyclic subgroup of order six. -/
structure PreservingOrder (O D : Type*) [Ring O] [DivisionRing D] where
  intoDivision : O →+* D
  intoDivision_injective : Function.Injective intoDivision
  restriction : O →+* ZMod 6
end ConditionalCM
end SptClassification

namespace SptClassification
namespace ConditionalCM
/-- Covolume for the reduced-trace pairing `Trd(x * conj(y))`.
The square root is taken after the Gram determinant. -/
noncomputable def traceCovolume {H : Type*} [DivisionRing H]
    (reducedTrace : H → ℝ) (conj : H → H) (v : Fin 4 → H) : ℝ :=
  Real.sqrt (Matrix.det (fun i j : Fin 4 => reducedTrace (v i * conj (v j))))
/-- All algebraic and geometric data produced by one common reduced CM root.
The carrier types may vary with the root, as the elliptic curve varies. -/
structure CommonRootAction (d p : ℕ) where
  O : Type
  D : Type
  H : Type
  [ringO : Ring O]
  [divisionD : DivisionRing D]
  [divisionH : DivisionRing H]
  order : PreservingOrder O D
  intoReal : D →+* H
  intoReal_injective : Function.Injective intoReal
  scalar : ℝ →+* H
  scalar_injective : Function.Injective scalar
  scalar_central : ∀ (r : ℝ) (x : H), scalar r * x = x * scalar r
  alpha : O
  beta : O
  normNumber : ℕ
  normNumber_eq : 4 * normNumber = d + 1
  alpha_quadratic : order.intoDivision alpha * order.intoDivision alpha -
    order.intoDivision alpha + (normNumber : D) = 0
  beta_quadratic : order.intoDivision beta * order.intoDivision beta -
    order.intoDivision beta + (normNumber : D) = 0
  alpha_orientation : order.restriction alpha = 0 ∨ order.restriction alpha = 1
  beta_orientation : order.restriction beta = 3 ∨ order.restriction beta = 4
  ordinary : Prop
  ordinary_commutes : ordinary → ∀ x y : O,
    order.intoDivision x * order.intoDivision y =
      order.intoDivision y * order.intoDivision x
  reducedTrace : H → ℝ
  quaternionConj : H → H
  reducedNorm : H → ℝ
  trace_self : ∀ x : H, reducedTrace (x * quaternionConj x) = 2 * reducedNorm x
  norm_one : reducedNorm 1 = 1
  norm_mul : ∀ x y : H, reducedNorm (x * y) = reducedNorm x * reducedNorm y
  norm_alpha : reducedNorm (intoReal (order.intoDivision alpha)) = (normNumber : ℝ)
  norm_beta : reducedNorm (intoReal (order.intoDivision beta)) = (normNumber : ℝ)
  hadamard : ∀ v : Fin 4 → H,
    traceCovolume reducedTrace quaternionConj v ≤
      Real.sqrt (∏ i : Fin 4, reducedTrace (v i * quaternionConj (v i)))
  eichler_lower : ¬ordinary → ∀ v : Fin 4 → O,
    (∀ c : Fin 4 → ℝ,
      (∑ i : Fin 4, scalar (c i) * intoReal (order.intoDivision (v i))) = 0 →
        ∀ i, c i = 0) →
    6 * (p : ℝ) ≤ traceCovolume reducedTrace quaternionConj
      (fun i => intoReal (order.intoDivision (v i)))
end ConditionalCM
end SptClassification

namespace SptClassification
namespace ConditionalCM
/-- The manuscript's integral models of its two actual complex class
polynomials, together with the geometric meaning of a common reduced root.
The coefficient maps are specializations of the same localized integral ring. -/
structure CMDescentInput (d p : ℕ) [Fact (-(d : ℤ) < 0)] [Fact p.Prime] where
  modelA : Polynomial (Localization.Away (6 : ℤ))
  modelB : Polynomial (Localization.Away (6 : ℤ))
  modelA_monic : modelA.Monic
  modelB_monic : modelB.Monic
  complexSpecialization : Localization.Away (6 : ℤ) →+* ℂ
  complexA : modelA.map complexSpecialization = cmClassPolynomialA (-(d : ℤ))
  complexB : modelB.map complexSpecialization = cmClassPolynomialB (-(d : ℤ))
  reduction : Localization.Away (6 : ℤ) →+* ZMod p
  commonRoot : ∀ x : AlgebraicClosure (ZMod p),
    (Polynomial.aeval x) (modelA.map reduction) = 0 →
    (Polynomial.aeval x) (modelB.map reduction) = 0 →
    CommonRootAction d p
end ConditionalCM
end SptClassification

namespace SptClassification

open QSeries
/-- Explicit good-reduction and homogeneous lift laws for the actual
principal-form series. `forms k` includes regularity at infinity and the
pole-clearing condition at the CM support, including the derivatives.
Its multiplication and Serre laws keep those conditions available for the
two sides of the homogeneous identity. -/
structure HomogeneousHasseInput (p d : ℕ) [Fact p.Prime]
    (F : Type*) [CommRing F] [Algebra (ZMod p) F] where
  forms : ℕ → Submodule (ZMod p) F
  forms_mul : ∀ {k l : ℕ} {f g : F},
    f ∈ forms k → g ∈ forms l → f * g ∈ forms (k + l)
  serre : ℕ → F →ₗ[ZMod p] F
  forms_serre : ∀ {k : ℕ} {f : F}, f ∈ forms k → serre k f ∈ forms (k + 2)
  qexp : F →ₐ[ZMod p] PowerSeries (ZMod p)
  qexp_injective_same_weight : ∀ {k : ℕ} {f g : F},
    f ∈ forms k → g ∈ forms k → qexp f = qexp g → f = g
  H : F
  E : F
  J : F
  H_form : H ∈ forms (p - 1)
  E_form : E ∈ forms (p + 1)
  J_form : J ∈ forms 4
  H_qexp : qexp H = 1
  J_qexp : qexp J = principalShimuraLambertSeries p d
  E_eq_serre_H : E = (12 : ZMod p) • serre (p - 1) H
  /-- The reduction of the weight-`p+1` Eisenstein series is the correction
  series in the Serre derivative. [rolenManuscript, Section 4] -/
  eisensteinTwo : PowerSeries (ZMod p)
  E_qexp : qexp E = eisensteinTwo
  /-- The ordinary Serre q-expansion law with `Dₖ = Θ-kE₂/12`.
  [rolenManuscript, Section 2 and Section 4] -/
  serre_qexp : ∀ {k : ℕ} {f : F}, f ∈ forms k →
    qexp (serre k f) = eulerDerivative (qexp f) -
      ((k : ZMod p) / 12) • (eisensteinTwo * qexp f)
end SptClassification

namespace SptClassification

open Polynomial
namespace ConditionalCM
/-- The first actual CM model after reduction and extension to the
algebraic closure of the residue field. -/
noncomputable def CMDescentInput.geometricA {d p : ℕ}
    [Fact (-(d : ℤ) < 0)] [Fact p.Prime]
    (C : CMDescentInput d p) :
    Polynomial (AlgebraicClosure (ZMod p)) :=
  (C.modelA.map C.reduction).map
    (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
/-- The second actual CM model under the same specialization. -/
noncomputable def CMDescentInput.geometricB {d p : ℕ}
    [Fact (-(d : ℤ) < 0)] [Fact p.Prime]
    (C : CMDescentInput d p) :
    Polynomial (AlgebraicClosure (ZMod p)) :=
  (C.modelB.map C.reduction).map
    (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
end ConditionalCM
/-- Shared good-reduction Hasse geometry. `X` is the interior of the
good-reduction curve, and coordinate is its injective affine coordinate.
The points are the distinct supersingular points. Algebra evaluation maps
exist off the reduced support of the same CM descent models used by
conditional separation. The theta coordinate is its Kodaira--Spencer
derivative. No logarithmic comparison or Wronskian-root conclusion is an input. -/
structure LiftHasseGeometry (p d : ℕ) [Fact p.Prime]
    [Fact (-(d : ℤ) < 0)]
    (C : ConditionalCM.CMDescentInput d p)
    (F X : Type*) [CommRing F] [Algebra (ZMod p) F] where
  forms : HomogeneousHasseInput p d F
  points : Finset X
  points_card : points.card = p - 1
  coordinate : X ↪ AlgebraicClosure (ZMod p)
  theta_coordinate : X → AlgebraicClosure (ZMod p)
  theta_coordinate_ne_zero : ∀ x : X, theta_coordinate x ≠ 0
  evaluate : ∀ (x : X),
    ¬(C.geometricA).IsRoot (coordinate x) →
    ¬(C.geometricB).IsRoot (coordinate x) →
    F →ₐ[ZMod p] AlgebraicClosure (ZMod p)
  hasse_zero : ∀ (x : X) (_hx : x ∈ points) ha hb,
    evaluate x ha hb forms.H = 0
  /-- Katz's simple-zero property, expressed through the Serre derivative of
  the Hasse invariant at a supersingular point. The manuscript's nonvanishing
  of `E` follows from `E_eq_serre_H` since the characteristic is at least five.
  [katz1973, Sections 2 and 4.3] -/
  serre_H_ne_zero : ∀ (x : X) (_hx : x ∈ points) ha hb,
    evaluate x ha hb (forms.serre (p - 1) forms.H) ≠ 0
/-- The previously used conditional lift: the CM quotient comparison is
kept explicit until it is obtained from the actual quotient construction. -/
structure LiftHasseInput (p d : ℕ) [Fact p.Prime]
    [Fact (-(d : ℤ) < 0)]
    (C : ConditionalCM.CMDescentInput d p)
    (F X : Type*) [CommRing F] [Algebra (ZMod p) F]
    extends LiftHasseGeometry p d C F X where
  L : F
  L_form : L ∈ forms.forms 2
  L_qexp : forms.qexp L = QSeries.principalLogarithmicLambertSeries p d
  logarithmic_identity : ∀ (x : X) ha hb,
    evaluate x ha hb L =
      theta_coordinate x *
        ((C.geometricA).derivative * C.geometricB -
          C.geometricA * (C.geometricB).derivative).eval (coordinate x) /
        ((C.geometricA).eval (coordinate x) *
          (C.geometricB).eval (coordinate x))
end SptClassification

namespace SptClassification

structure CharacterObstructionGeometry (p d : ℕ) [Fact p.Prime]
    [Fact (-(d : ℤ) < 0)] where
  cm : ConditionalCM.CMDescentInput d p
  Form : Type
  formRing : CommRing Form
  formAlgebra : letI : CommRing Form := formRing
    Algebra (ZMod p) Form
  Point : Type
  lift : letI : CommRing Form := formRing
    letI : Algebra (ZMod p) Form := formAlgebra
    LiftHasseInput p d cm Form Point
/-- The geometric input is supplied at every discriminant eligible
for the manuscript's character obstruction. Its data do not depend on
vanishing of any `spt` class. -/
structure CharacterObstructionInputFamily where
  atDiscriminant : ∀ (p d : ℕ) [Fact p.Prime]
    [Fact (-(d : ℤ) < 0)],
    5 ≤ p → 23 ≤ d → d % 24 = 23 → Squarefree d →
    ¬p ∣ 6 * d → (d + 1) ^ 2 < 24 * p →
    8 * formClassNumber (-(d : ℤ)) < p + 1 →
    CharacterObstructionGeometry p d
end SptClassification
namespace SptClassification
/-- A rational number and its residue, with a denominator prime to p. -/
def RationalReduces (p : ℕ) (q : ℚ) (z : ZMod p) : Prop :=
  ∃ num den : ℤ, ¬(p : ℤ) ∣ den ∧
    q = (num : ℚ) / den ∧ z * (den : ZMod p) = (num : ZMod p)
/-- Rational Fourier coefficient of the normalized level-one Eisenstein series. -/
noncomputable def normalizedEisensteinRationalCoefficient (k n : ℕ) : ℚ :=
  if n = 0 then 1 else
    -(2 * k / bernoulli k) * (ArithmeticFunction.sigma (k - 1) n)
/-- The integral Fourier coefficients of E₂. -/
def eisensteinTwoIntegerCoefficient (n : ℕ) : ℤ :=
  if n = 0 then 1 else -24 * (n.divisors.sum fun d => (d : ℤ))
end SptClassification

@[expose] public section
namespace SptClassification.Palomar

/-- The two classical Eisenstein congruences used in the propagation argument.
These are explicit literature hypotheses, not proofs supplied by this package. -/
structure EisensteinCongruenceInputs where
  minus : ∀ {p : ℕ} [Fact p.Prime], 5 ≤ p → ∀ n : ℕ,
    RationalReduces p (normalizedEisensteinRationalCoefficient (p - 1) n)
      (if n = 0 then 1 else 0)
  plus : ∀ {p : ℕ} [Fact p.Prime], 5 ≤ p → ∀ n : ℕ,
    RationalReduces p (normalizedEisensteinRationalCoefficient (p + 1) n)
      (eisensteinTwoIntegerCoefficient n : ZMod p)

/-- Theorem 1.1, conditional on the explicit literature and geometric inputs,
including the two classical Eisenstein congruences. -/
theorem conditional_noncanonical_exclusion
    (eisenstein : EisensteinCongruenceInputs)
    (tv : CharacterIntervalInput)
    (ct : ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → QSeries.ConstantTermInputs p)
    (progression : ∀ (p : ℕ), p.Prime → ∀ hp5 : 5 ≤ p, ProgressionInputs p hp5)
    (geometry : CharacterObstructionInputFamily)
    (p b : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hb : b < p)
    (hspt : ∀ n : ℕ, p ∣ spt (p * n + b)) :
    ((24 * b : ℕ) : ZMod p) = 1 := by
  sorry

/-- Corollary 1.2, with canonical classification and Andrews' congruences
also supplied as the explicit `CanonicalInputs` hypothesis. -/
theorem conditional_simple_congruence_classification
    (eisenstein : EisensteinCongruenceInputs)
    (tv : CharacterIntervalInput)
    (ct : ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → QSeries.ConstantTermInputs p)
    (progression : ∀ (p : ℕ), p.Prime → ∀ hp5 : 5 ≤ p, ProgressionInputs p hp5)
    (geometry : CharacterObstructionInputFamily)
    (canonical : CanonicalInputs)
    (p b : ℕ) (hp : p.Prime) (hb : b < p) :
    (∀ n : ℕ, p ∣ spt (p * n + b)) ↔
      (p = 5 ∧ b = 4) ∨ (p = 7 ∧ b = 5) ∨ (p = 13 ∧ b = 6) := by
  sorry

end SptClassification.Palomar
