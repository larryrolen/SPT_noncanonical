# Assumptions and manuscript coverage

The library has 62 visible theorem admissions, all named literature inputs.
All six manuscript arguments have proofs using these premises. Literature interfaces are accepted
premises for conditional manuscript completion; their `sorry` bodies remain
explicit and their dependency cones remain unconditionally open. There are
no custom axioms. Explicit-parameter conditional exports remain separate
from the original statements.

The classification assembly uses propagation and character obstruction,
plus the corrected Treviño bound, Rolen's canonical necessity theorem, and
Andrews' three congruences. The library root includes actual propagation,
all-prime CM separation and global CM Shimura cusp clearing. The representative’s
holomorphy, transformation and meromorphic cusp laws are proved.

[CMShimuraClearedObstruction](SptClassification/ModularForms/CMShimuraClearedObstruction.lean)
proves the character obstruction from an independently supplied globally
holomorphic cleared form and its exact integral Fourier row. It constructs
the residue specialization, rational Shimura section and Hasse contradiction
without new admissions. The exact Fourier row is proved in
[CMIntegralCuspComparison](SptClassification/ModularForms/CMIntegralCuspComparison.lean)
from the same lift’s high-cusp expansion and equality with the cleared form.
[CMFiniteCuspBounds](SptClassification/ModularForms/CMFiniteCuspBounds.lean)
proves the remaining three cusp bounds for the same principal lift.
[CMGlobalCuspClearing](SptClassification/ModularForms/CMGlobalCuspClearing.lean)
constructs its globally holomorphic clearing. The original
`character_obstruction` composes these constructions with the exact integral
row and Hasse contradiction, without a new admission.

## Named manuscript results

All six statements preserve their approved hypotheses. The coefficient lemma
allows nonsquarefree `d`; CM separation requires positive squarefree `d` and
covers both splitting types using the actual oriented class polynomials.

| Manuscript label | Lean declaration | Proof status |
| --- | --- | --- |
| `thm:main` | [`SptClassification.noncanonical_exclusion`](SptClassification/Classification/NoncanonicalExclusion.lean) | Assembly using admitted results |
| `cor:classification` | [`SptClassification.simple_congruence_classification`](SptClassification/Classification/SimpleCongruences.lean) | Assembly using admitted results |
| `lem:prop` | [`SptClassification.propagation`](SptClassification/ModularForms/CongruencePropagation.lean) | Manuscript proof using literature premises |
| `lem:coeff` | [`SptClassification.QSeries.square_coefficient_relation`](SptClassification/QSeries/SquareCoefficientRelation.lean) | Manuscript proof using literature premises |
| `lem:separation` | [`SptClassification.cm_separation`](SptClassification/QuadraticForms/CMSeparation.lean) | Manuscript proof using literature premises |
| `prop:obstruction` | [`SptClassification.character_obstruction`](SptClassification/ModularForms/CharacterObstruction.lean) | Manuscript proof using literature premises |


The finite rational-translation operator in
[FiniteFourierFilter](SptClassification/ModularForms/FiniteFourierFilter.lean)
has proved coefficient filtering and negative-square shadow cancellation.
The correction may have arbitrary height-dependent amplitudes; its convergence
is an explicit hypothesis. This adds no admission and does not assert the
completion or twisted modular transformation law.

The actual finite-filter/Serre construction in
[TwistedAnalyticFunctions](SptClassification/ModularForms/TwistedAnalyticFunctions.lean)
derives all selected Fourier rows from untwisted expansions.
[IntegralShimuraLambert](SptClassification/ModularForms/IntegralShimuraLambert.lean)
constructs the integral divisor-sum row; existence of the good-reduction modular
lift is constructed in the global cusp and integral comparison modules. [LevelSixWeierstrass](SptClassification/QuadraticForms/LevelSixWeierstrass.lean)
proves the explicit curve discriminant and nonsingularity from the finite-j
relation. The eta coordinate and cyclic-six subgroup are identified using the
named uniformization and level-six literature interfaces below.

[CMLogarithmicLaurentComparison](SptClassification/ModularForms/CMLogarithmicLaurentComparison.lean)
proves that the actual integral CM quotient and its logarithmic derivative
have the rational Laurent expansions used in the Hasse argument. The comparison
persists under any residue-field extension and transports the differential
identity. It adds no admission; existence and regularity of the independent
weight-four Shimura section are supplied by the global clearing construction.

## Named literature premises

[TriangularQExpansionDescent](SptClassification/ModularForms/TriangularQExpansionDescent.lean)
proves coefficient descent for a finite cusp basis with distinct initial
exponents and leading coefficients one. An expansion over a subring forces
each basis coefficient into that subring. This adds no admission; the global
polynomial representation uses the named holomorphic-basis premise below.

[CMAnalyticPoleClearing](SptClassification/ModularForms/CMAnalyticPoleClearing.lean)
proves that the squared actual paired CM polynomial removes all interior
double poles supported on the principal Weil divisors. It constructs a single
analytic extension and proves equality of punctured germs, adding no admission.
The lifting theorem's meromorphy, pole bound and divisor description remain
explicit literature inputs. Cusp regularity and integral descent are supplied
by the subsequent cusp bounds and exact Fourier comparison.
[CMAnalyticTransformation](SptClassification/ModularForms/CMAnalyticTransformation.lean)
proves that this removable extension retains the lift's transformation law,
using invariance of the actual CM factor and uniqueness of punctured limits.
It adds no admission.

[CMAnalyticCuspClearing](SptClassification/ModularForms/CMAnalyticCuspClearing.lean)
proves the analytic infinity-cusp cancellation by `Delta^(8h)` for the actual
paired CM polynomials, preserving the lift's constant term. It uses Mathlib's
polynomial homogenization and explicit analytic normalized cusp functions
`U=q*t` and `V=Delta/q`, both with value one at zero.
[CMActualCuspClearing](SptClassification/ModularForms/CMActualCuspClearing.lean)
supplies these functions using the actual eta quotient and the modular
discriminant, proving analyticity and constant term one without a normalization
assumption. Both modules add no admission; the global cusp and integral
comparisons are proved in the subsequent modules.

[CMFiniteCuspClearing](SptClassification/ModularForms/CMFiniteCuspClearing.lean)
proves analyticity of the actual paired CM polynomial factor at the other
three cusps, with coordinate values `0`, `-9`, and `-8`. It adds no admission;
the lift's slash expansions follow from the named full-input covariance
premise, and their holomorphy is proved by the finite-cusp germ construction.

Citations use the keys in [references.bib](references.bib). The signatures
below are the current Lean statements; referenced definitions in each linked
module fix their objects and normalizations. The Andrews congruences are
verified through their display and attribution in Rolen §1; their primary
Andrews theorem locator remains unverified.

### Hasse geometry and the invariant differential frame

[WeierstrassHasse](SptClassification/ModularForms/WeierstrassHasse.lean)
defines the Hasse invariant by the coefficient of `X^(p-1)` in
`(4X^3+b₂X²+2b₄X+b₆)^((p-1)/2)`. Five generic literature premises are explicit:

- `hasse_degree_bound_literature` and `hasse_top_coefficient_literature`:
  weight homogeneity for a polynomial Weierstrass family satisfying the five
  coefficient degree bounds; [katz1973], §2.0, pp. 97–98, and Appendix A1.4,
  Remark 2, p. 172. These coefficient consequences retain the infinity frame.
- `hasse_variableChange_literature`: covariance in characteristic `p > 3`,
  with Mathlib's inverse-unit convention; the same source locators.
- `hasse_ne_zero_of_multiplicative_literature`: nonvanishing on a nodal
  fiber (`Δ = 0`, `c₄ ≠ 0`), in characteristic `p > 3`; §2.0, pp. 97–98.
- `hasse_simple_zero_of_transverse_literature`: simple Hasse zeros in an
  algebraically closed characteristic-`p > 3` Weierstrass family with nonzero
  discriminant and Kodaira–Spencer numerator at the point; proof of
  Theorem 4.3, p. 149, and Appendix A1.3.17, p. 169. This is the transverse
  pullback of Igusa's theorem, including the elliptic `j` fibers.

The sixth input, `hasse_tate_literature` in
[LevelSixTateSections](SptClassification/ModularForms/LevelSixTateSections.lean),
is the normalized Hasse expansion `1` for the explicit canonical Tate
Weierstrass equation in characteristic `p > 3`; §2.0, pp. 97–98, and
Appendix A1.4, Remark 2, p. 172. The Tate equation and differential are in
Appendix A1.2.3, pp. 160–161.

From these inputs, the actual level-six specialization proves `p-1` distinct
interior Hasse zeros, the nonvanishing of `12 D_(p-1) H` there, and framed
Tate evaluation of Hasse. The exact Kodaira–Spencer and Ramanujan polynomial
identities are proved. The ring of polynomial sections in this construction
is a regular subring on the interior chart; it does not assert that every
such section is holomorphic at the cusps. The eta cusp realization,
Serre Fourier comparison and global integral lift are supplied by the
subsequent constructions.

[LevelSixRationalHasseComparison](SptClassification/ModularForms/LevelSixRationalHasseComparison.lean)
proves the equal-weight Hasse identity from the Laurent differential identity
for independently supplied rational sections of weights two and four. It uses
the actual Hasse section, Serre connection and fixed-weight Tate injectivity.
It adds no admission; the global integral lift and evaluation
away from its poles are constructed in the modules below.

[LevelSixRationalEvaluation](SptClassification/ModularForms/LevelSixRationalEvaluation.lean)
proves the evaluated identity `E²L/24 = 0` using rational functions regular
at the chosen point. [LevelSixRationalObstruction](SptClassification/ModularForms/LevelSixRationalObstruction.lean)
combines it with the actual `p-1` Hasse zeros and the Wronskian degree bound
to contradict the Laurent differential identity. Both add no admission.
The global sections, their expansions and regularity away from CM support
are supplied by the CM clearing and rational comparison constructions.

### The actual mock completion

[MockCompletion](SptClassification/ModularForms/MockCompletion.lean) defines the
Ahlgren–Andersen integral at `24τ`, with vertical ray from `−24 conjugate τ`,
principal complex power and coefficient `sqrt(3i)/(2π)`.
`etaEichlerIntegral_negativeSquare_expansion` admits the convergent expansion
supported on negative squares, with height-dependent amplitudes, from
[ahlgrenAndersen2016, §3, (3.1), PDF p. 9] and the unary-theta eta expansion.
`ahlgrenAndersen_sptCompletion_map_action` in
[MockCompletionTransformation](SptClassification/ModularForms/MockCompletionTransformation.lean)
admits its weight `3/2`, level `576`, character `(12/·)` transformation law,
recorded immediately after (3.2) on the same page and attributed to
[bringmann2008]. These are two explicit literature premises.
The finite-filter identity `fourierFilter_sptCompletion` is proved from the
expansion and the checked negative-square cancellation. The filtered transformation laws and normalized
meromorphy at all cusps are proved. The actual approximation and propagation
are deduced from these laws and the named literature interfaces.

### Rational CM maps and the level-six model

The following thirteen general literature interfaces are included. Linked
Lean statements retain all field, nonsingularity, separability and marking
hypotheses. None admits the actual CM specialization or separation conclusion.

| Declaration | Lean source | Literature locator and limitation |
| --- | --- | --- |
| `latticeMultiplication_isRational` | [CMRationalAction](SptClassification/QuadraticForms/CMRationalAction.lean) | [silverman2009], VI §§3–4; analytic lattice maps are algebraic; section locator |
| `endomorphismRing_isRational`, `surjective_of_isRational` | [RationalEndomorphisms](SptClassification/QuadraticForms/RationalEndomorphisms.lean) | [silverman2009], II §2, III §§2,4; section locators, primary theorem numbers unverified |
| `isRational_comp` | [RationalCurveIsomorphism](SptClassification/QuadraticForms/RationalCurveIsomorphism.lean) | [silverman2009], II §2, III §4; section locators |
| `comp_comm_of_nonzero_prime_torsion` | [OrdinaryRationalEndomorphisms](SptClassification/QuadraticForms/OrdinaryRationalEndomorphisms.lean) | [silverman2009], V §3, III §9; ordinary geometric endomorphism ring, primary theorem numbers unverified |
| `kernelCard_eq_of_quadratic` | [SeparableRationalEndomorphisms](SptClassification/QuadraticForms/SeparableRationalEndomorphisms.lean) | [silverman2009], III §§4,6; degree/trace and separable-kernel corollary, section locators |
| `supersingular_kernel_bound` | [SupersingularKernelBound](SptClassification/QuadraticForms/SupersingularKernelBound.lean) | [rolen2026canonical], Lemma 5.2, PDF p. 8: `6p ≤ 4N(f)N(g)`; prime-to-characteristic factors identify kernel cardinality with degree |
| `torsion_coordinates_isAlgebraic` | [TorsionPointDescent](SptClassification/QuadraticForms/TorsionPointDescent.lean) | Finite-fiber consequence of [silverman2009], III §6, Corollary 6.4; primary locator unverified |
| `latticeCM_j_isIntegral` | [CMSingularModuli](SptClassification/QuadraticForms/CMSingularModuli.lean) | [silverman1994], II Theorem 6.1; primary book not inspected |
| `levelSix_covering_invariant` | [LevelSixEtaInvariant](SptClassification/QuadraticForms/LevelSixEtaInvariant.lean) | [maier2009], arXiv v4, Tables 2 and 4, pp. 11–12; `s=72/t`, usual `j(i)=1728`, denominator cleared |
| `exists_tate_model` | [LevelSixTateModel](SptClassification/QuadraticForms/LevelSixTateModel.lean) | [sutherland2012], §2, Proposition 1 and Table 4; exact order-six marking and characteristic restrictions retained |
| `exists_curveEquiv_of_variableChange`, `exists_variableChange_of_curveEquiv` | [VariableChangeIsomorphism](SptClassification/QuadraticForms/VariableChangeIsomorphism.lean) | [milne2021], II Proposition 1.5, p. 49, and II 2.4(b); affine coordinate formulas fix the actual point maps |

The rational CM transport, common-root extraction, all-prime contradiction,
integral eta model, and Tate-coordinate calculations are proved using these
premises. The marked analytic identification is proved from explicit coefficient
holomorphy and cusp limits. The six classical analytic inputs are named literature premises, documented
below. Compatible specialization under the fixed reduction map is proved using the
named general good-reduction premise below. Equal
`j` invariants alone do not identify the cyclic-six marking.

### Powered projection and its Fourier expansion

[Lean source](SptClassification/ModularForms/PoweredProjection.lean)

`garthwaiteJameson_powered_projection` is [garthwaiteJameson2021,
Proposition 4, PDF p. 4], specialized to `B = 0`. For a weakly holomorphic
form of integral or half-integral weight with the standard theta multiplier
(and `4 ∣ N` in the half-integral case), it transforms the actual finite
progression average raised to `24*M*N`. The exact source level is `N*N_M`,
where `N_M` is `M`, `8*M`, `3*M`, or `24*M` according as `gcd(M,6)` is
1, 2, 3, or 6. The upper-left entry `a` is coprime to 6; the transformed
residue is `a²*u`. It also supplies holomorphy on `Γ₁(N*N_M)` after
multiplication by a sufficiently large power of `Δ = η²⁴`.

`garthwaiteJameson_projection_expansion` is the Fourier identity preceding
(1) in the same paper, §2, PDF p. 4. It identifies that finite average with
the convergent, bounded-below row retaining precisely `r ≡ u (mod M)`,
in the variable `q^(1/M)`. Both theorem bodies remain visible `sorry`.

The specialization to level `24*M*N`, constant scaling, equality for congruent
residue labels, and realization by the actual rational Laurent series are
proved deductions. These interfaces do not assume congruence propagation
or existence of the manuscript's modular approximation.

[`ModularProgressionForm.transport_of_commonDenominator`](SptClassification/ModularForms/PoweredProjectionTransport.lean)
proves transport from these literature inputs when the actual Fourier row
has one denominator prime to `p`, allowing `p ∣ M` and `p ∣ R`.
The rational Laurent cancellation theorem
[`reduction_zero_of_divided_power`](SptClassification/ModularForms/PoweredDenominatorReduction.lean)
has a proof using only the standard three axioms. The actual normalized
approximation has the required denominator by `SptModularApproximation.commonDenominator`.
Consequently [`propagation_of_approximation`](SptClassification/ModularForms/ApproximationPropagation.lean)
needs only the explicitly supplied `SptApproximationInput`, and no independent
transport assumption. `actualSptModularApproximation` constructs that
approximation from the actual completed mock form, twists, Serre derivative
and proved cusp law; the original `propagation` composes these deductions.

The construction in
[`approximationOfModularity`](SptClassification/ModularForms/ApproximationConstruction.lean)
supplies the rational Fourier row, reduction and pole bound from analytic
modularity. The normalized representative's holomorphy and transformation law
are proved from the three constituent forms in
[NormalizedAutomorphy](SptClassification/ModularForms/NormalizedAutomorphy.lean),
and its meromorphic fourth-power cusp expansion is assembled in
[NormalizedCusps](SptClassification/ModularForms/NormalizedCusps.lean).
These add no admissions and
construct the actual twisted analytic constituents in
[ScaledGeneratingDerivative](SptClassification/ModularForms/ScaledGeneratingDerivative.lean).
The function `sptTwistedAnalyticData` uses the partition-defined smallest-parts
series and the inverse eta function, with proved convergent Fourier expansions
and normalized derivative. The classical theta nonvanishing and fourth-power multiplier are named
literature premises, documented below. The two filtered transformation laws are proved from the inputs below.
The actual normalized cusp law is proved in
[ActualNormalizedCusps](SptClassification/ModularForms/ActualNormalizedCusps.lean).

[ActualApproximation](SptClassification/ModularForms/ActualApproximation.lean)
constructs the actual level `576 * Q^4` approximation from those remaining
analytic laws, using the proved character `(12/·)` and negative-half-weight
Serre transformation. `propagation_of_actual_analytic_laws` composes that
construction with `propagation_of_approximation`. The actual
specialization supplies these analytic hypotheses, preserving the
literature boundary in the original `propagation`.

### Classical theta

[ThetaMultiplier](SptClassification/ModularForms/ThetaMultiplier.lean) contains
two named literature admissions, independent of the smallest-parts series:

- `dlmf_jacobiTheta_ne_zero` states nonvanishing for `Im τ > 0`. It is the
  `z = 0` consequence of the exact zero set in [nistDLMF, §20.2(iv)], with
  the `θ₃` normalization in §20.2(i), (20.2.3).
- `koblitz_theta_multiplier_fourth` states that the fourth power of
  `jacobiTheta (2γτ) / jacobiTheta (2τ)` is `(cτ+d)^2` on `Γ₀(4)`.
  The source is [koblitz1993, theorem on p. 148], as reproduced in
  [kunduMuller2025, arXiv v1, §2.5, p. 6]. The secondary display was
  inspected; the primary book was not.

The restriction to levels divisible by four is proved. The positive-weight
statement of Proposition 2.5 has not been applied to negative-weight or harmonic
forms. Its weight-independent matrix/theta calculation is isolated below.

### Actual filtered transformation laws

[ThetaTranslation](SptClassification/ModularForms/ThetaTranslation.lean)
contains `koblitz_theta_rational_translation`, a named literature premise
isolating the matrix and theta calculation in [kunduMuller2025, arXiv v1,
Proposition 2.5 proof, p. 7], using [koblitz1993, p. 148]. For positive `N`
divisible by four and odd nonzero `M`, it intertwines rational translations
under `Γ₀(N M²)`, preserves the lower-right entry modulo `N`, and identifies
the theta quotients. The secondary proof was inspected; the primary Koblitz
book was not. The source uses `−v/M`; the code uses `j = −v`.
`fourierFilter_theta_map_action` proves the transformation for every integer
power of the theta quotient from this calculation and finite Fourier inversion.

[ScaledEtaTransformation](SptClassification/ModularForms/ScaledEtaTransformation.lean)
contains `ahlgrenBringmannLovejoy_eta_twenty_four_map_action`, the transformation
part of `η(24τ) ∈ M_{1/2}(Γ₀(576), (12/·))`, explicitly stated in
[ahlgrenBringmannLovejoy2011, §3, immediately after (3.7), PDF p. 8].
Inversion and the quadratic character identity supply the actual partition law.
[ActualTwistTransformation](SptClassification/ModularForms/ActualTwistTransformation.lean)
then proves both actual filtered laws at level `576 Q⁴` for odd prime `Q`.

[ActualTwistedApproximation](SptClassification/ModularForms/ActualTwistedApproximation.lean)
constructs `actualApproximationOfCuspLaw` and proves
`propagation_of_actual_cusp_law`. The theorem
`sptTwistedAnalyticData_normalizedRepresentative_cusps` supplies their cusp
hypothesis with a positive integral width. Its proof combines actual
partition/spt coefficient bounds, finite Fourier filtering, the normalized
fourth-power transformation, and the generic periodic cusp criterion.
`actualSptModularApproximation` and the original `propagation` compose
these deductions without an additional manuscript admission.

### Partition coefficient growth

[PartitionGrowth](SptClassification/QSeries/PartitionGrowth.lean) contains
`hardyRamanujan_partitionCount_growth`: there are positive real constants
`C, B` such that `partitionCount n ≤ C * exp (B * sqrt n)` for every natural
`n`. This is the coarse consequence of [hardyRamanujan1918, Introduction,
displayed leading asymptotic]. The primary paper was not inspected for this
interface; the exact display locator remains to be checked against the source.
The estimate is a named literature premise, independent of the smallest-parts
congruences. Bounds for `spt` and both actual generating functions, their
transport to cusp strips and the resulting meromorphic cusp law are proved
from it.

### Classical marked lattice coefficients

[ClassicalWeierstrassCoefficients](SptClassification/QuadraticForms/ClassicalWeierstrassCoefficients.lean)
contains six named literature premises: holomorphy of `markedShortA`,
`markedShortX`, `markedShortY`, and their limits at imaginary infinity.
The periods are `(1, τ)` and the marked point is `1/6`, with affine
coordinate `y = wp′/2`. All declarations below are in
`SptClassification.ComplexUniformization`; the limits allow arbitrary
real part of `τ`.

| Named literature premise | Conclusion |
| --- | --- |
| [`analyticOnNhd_markedShortA_literature`](SptClassification/QuadraticForms/ClassicalWeierstrassCoefficients.lean) | `−g₂/4` is analytic on the upper half-plane |
| [`analyticOnNhd_markedShortX_literature`](SptClassification/QuadraticForms/ClassicalWeierstrassCoefficients.lean) | `wp(1/6)` is analytic on the upper half-plane |
| [`analyticOnNhd_markedShortY_literature`](SptClassification/QuadraticForms/ClassicalWeierstrassCoefficients.lean) | `wp′(1/6)/2` is analytic on the upper half-plane |
| [`tendsto_markedShortA_literature`](SptClassification/QuadraticForms/ClassicalWeierstrassCoefficients.lean) | Limit `−π⁴/3` as `Im τ → ∞` |
| [`tendsto_markedShortX_literature`](SptClassification/QuadraticForms/ClassicalWeierstrassCoefficients.lean) | Limit `11π²/3` as `Im τ → ∞` |
| [`tendsto_markedShortY_literature`](SptClassification/QuadraticForms/ClassicalWeierstrassCoefficients.lean) | Limit `−4√3 π³` as `Im τ → ∞` |

The sources are [whittakerWatson1920, §§20.2–20.22, pp. 433–437;
§§21.3, 21.41–21.43, pp. 469–473]: normally convergent lattice series,
theta products and the trigonometric degeneration. The source uses half-periods
`1/2, τ/2` and nome `exp(π i τ)`. These are classical analytic consequences
specialized at the fixed marking; they assert no CM reduction result.
[CMMarkedEtaLiterature](SptClassification/QuadraticForms/CMMarkedEtaLiterature.lean)
proves the actual marked eta identity and rational complex CM action from them.

### `SptClassification.garthwaiteJameson_slash_cyclotomic_integral`

[Lean source](SptClassification/ModularForms/CyclotomicSlash.lean)

[garthwaiteJameson2021, Theorem 5, PDF p. 4], attributed there to
[deligneRapoport1973, Corollaire 3.12] and [radu2012, Corollary 5.3].
The primary Garthwaite–Jameson statement was inspected. It requires positive
integral weight and level, holomorphy on `Γ₁(N)`, and coefficients in `ℤ[ζ_N]`.
It asserts preservation of that ring under `Γ₀(N)` slash. It has no
prime-coprime-level condition. Both rows below are actual width-one analytic
q-expansions, and `HolomorphicGammaOneForm` includes boundedness at every cusp.

```lean
theorem garthwaiteJameson_slash_cyclotomic_integral
    (N k : ℕ) (hN : 0 < N) (hk : 0 < k)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ N)
    (F : UpperHalfPlane → ℂ) (hF : HolomorphicGammaOneForm N k F)
    (γ : CongruenceSubgroup.Gamma0 N) (a b : ℕ → ℂ)
    (ha : HasIntegralWeightQExpansion F a)
    (hb : HasIntegralWeightQExpansion (progressionIntegralSlash k γ F) b)
    (hint : ∀ n, a n ∈ cyclotomicCoefficientRing ζ) :
    ∀ n, b n ∈ cyclotomicCoefficientRing ζ
```

Rational descent and localization using a common denominator are proved.
The normalized representative and its divided vanishing progression have
such a denominator prime to the reduction characteristic. These deductions
do not assume that arbitrary coefficientwise prime-local rows have a common
denominator.

### `SptClassification.corrected_trevino_character_interval_bound`

[Lean source](SptClassification/Arithmetic/EffectiveCharacterDiscriminant.lean)

The corrected explicit constant-character bound of
[trevino2017, Theorem 1, p. 1]. The source applies to every odd prime,
every nonprincipal character, and an interval `(a, a + H]`; its
`3.38 = 169/50` bound has no large-prime qualification. The nonzero
constant hypothesis below is a restriction of the source statement.
This named literature theorem remains an admitted input.

```lean
theorem corrected_trevino_character_interval_bound
    (q : ℕ) [Fact q.Prime] (hq : Odd q)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (a : ℤ) (H : ℕ) (hH : 1 ≤ H)
    (c : ℂ) (hc : c ≠ 0)
    (hconstant : ∀ j : ℕ, 1 ≤ j → j ≤ H →
      χ ((a + (j : ℤ)) : ZMod q) = c) :
    (H : ℝ) ≤ (169 / 50 : ℝ) * (q : ℝ) ^ (1 / 4 : ℝ) * Real.log q
```

### `SptClassification.rolen_canonical_prime_necessity`

[Lean source](SptClassification/Classification/ConditionalCanonical.lean)

Necessity in [rolen2026canonical, Theorem 1.1]. That paper defines
the canonical residue by `24 * b ≡ 1 (mod p)` for primes `p ≥ 5`;
its theorem gives precisely the three primes below. This named
literature theorem remains an admitted input.

```lean
theorem rolen_canonical_prime_necessity
    (p b : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hb : b < p)
    (hcanon : ((24 * b : ℕ) : ZMod p) = 1)
    (hspt : ∀ n : ℕ, p ∣ spt (p * n + b)) :
    p = 5 ∨ p = 7 ∨ p = 13
```

### `SptClassification.andrews_spt_five`

[Lean source](SptClassification/Classification/ConditionalCanonical.lean)

Andrews' congruence at five, displayed in
[rolen2026canonical, §1] with attribution to [andrews2008]. The
primary-paper theorem locator still needs verification.

```lean
theorem andrews_spt_five (n : ℕ) : 5 ∣ spt (5 * n + 4)
```

### `SptClassification.andrews_spt_seven`

[Lean source](SptClassification/Classification/ConditionalCanonical.lean)

Andrews' congruence at seven, displayed in
[rolen2026canonical, §1] with attribution to [andrews2008]. The
primary-paper theorem locator still needs verification.

```lean
theorem andrews_spt_seven (n : ℕ) : 7 ∣ spt (7 * n + 5)
```

### `SptClassification.andrews_spt_thirteen`

[Lean source](SptClassification/Classification/ConditionalCanonical.lean)

Andrews' congruence at thirteen, displayed in
[rolen2026canonical, §1] with attribution to [andrews2008]. The
primary-paper theorem locator still needs verification.

```lean
theorem andrews_spt_thirteen (n : ℕ) : 13 ∣ spt (13 * n + 6)
```

### `SptClassification.rolen_cmBorcherdsProduct_near_infinity`

[Lean source](SptClassification/ModularForms/BorcherdsCMProduct.lean)

Analytic part of [rolen2026canonical, Theorem 4.2, PDF pp. 6–7].
For squarefree `d ≡ 23 (mod 24)`, the product near `q = 0` converges to
`A_d(t)/B_d(t)`, with the coefficient and orientation normalizations of
the manuscript. The source also asserts an integral formal-series identity;
that stronger assertion is not used here.

```lean
theorem rolen_cmBorcherdsProduct_near_infinity (d : ℕ)
    [Fact (-(d : ℤ) < 0)] (hsq : Squarefree d) (hmod : d % 24 = 23) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : UpperHalfPlane,
      ‖Function.Periodic.qParam 1 z‖ < ε →
        Filter.Tendsto
          (fun N : ℕ => cmBorcherdsPartialProduct d N
            (Function.Periodic.qParam 1 z)) Filter.atTop
          (nhds (cmBorcherdsQuotient (-(d : ℤ)) z))
```

### `SptClassification.rolen_cmFormalBorcherdsProduct`

[Lean source](SptClassification/ModularForms/CMFormalProduct.lean)

Formal-series part of [rolen2026canonical, Theorem 4.2, (4.4), PDF
pp. 6–7]. The source states this equality over a ring integral away from six
for squarefree `d ≡ 23 (mod 24)`. Both polynomials here are the actual monic
oriented CM products supplied by its Lemma 4.1, with the same eta coordinate.
Only this exact formal product assertion is admitted.

```lean
theorem rolen_cmFormalBorcherdsProduct (d : ℕ)
    [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) :
    cmFormalBorcherdsQuotient d hd hsq hmod =
      QSeries.integerEulerProduct (R := CMFormalCoefficientRing)
        (cmFormalProductExponent d)
```

### `SptClassification.QSeries.rolen_individualShadowForms`

[Lean source](SptClassification/QSeries/AnalyticConstantTerms.lean)

The individually constructed integral forms `G_t`, with `G₁ = 0`, in
[rolen2026canonical, Proposition 2.2 and Remark 2.3, PDF p. 3]. This leaf
records their actual Fourier realizations and prescribed principal parts;
the subsequent Hecke identities are separate.

```lean
theorem rolen_individualShadowForms : Nonempty IndividualShadowForms
```

### `SptClassification.QSeries.rolen_f_prime_shadow`

[Lean source](SptClassification/QSeries/AnalyticConstantTerms.lean)

The single-prime relation for the mock row `f` in
[rolen2026canonical, Lemma 2.4, equation (2.6), PDF p. 3]. The Hecke
normalization is the three-term weight `3/2` action on indices `r/24`.

```lean
theorem rolen_f_prime_shadow (forms : IndividualShadowForms)
    (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    heckeThreeHalf p (fun r => (fFourier r : ℚ)) -
      (((characterTwelve (p : ℤ) * (1 + (p : ℤ)) : ℤ) : ℚ) •
        (fun r => (fFourier r : ℚ))) =
      (p : ℚ) • forms.rationalRow p
```

### `SptClassification.QSeries.rolen_G_prime_shadow_source`

[Lean source](SptClassification/QSeries/AnalyticConstantTerms.lean)

The single-prime relation [rolen2026canonical, Lemma 2.4, (2.7), PDF p. 3].
Its diagonal is exactly `χ₁₂(p) (m²/p)`, including zero when `p ∣ m`.
`G_(m/p) = 0` when `p ∤ m`, and `G₁ = 0`. The former interface
`rolen_G_prime_shadow` is deduced from this source-normalized identity.

```lean
theorem rolen_G_prime_shadow_source
    (forms : IndividualShadowForms) (p m : ℕ) [Fact p.Prime]
    (hp5 : 5 ≤ p) (hm : 1 < m) (hmc : m.Coprime 6) :
    heckeThreeHalf p (forms.rationalRow m) =
      (p : ℚ) • forms.rationalRow (m * p) +
        ((characterTwelve (p : ℤ) : ℚ) *
          (legendreSym p ((m : ℤ) ^ 2) : ℚ)) • forms.rationalRow m +
        (if p ∣ m then forms.rationalRow (m / p) else 0) -
        ((p : ℚ) * (characterTwelve (m : ℤ) : ℚ)) •
          forms.rationalRow p
```

### `SptClassification.integralCMClassPolynomials_literature`

[Lean source](SptClassification/QuadraticForms/IntegralClassPolynomials.lean)

The monic-descent assertion of [rolen2026canonical, Lemma 4.1, pp. 5–6].
The source's `n` is `d` here: `n > 0` is squarefree and `n ≡ 23 (mod 24)`, so
the discriminant is `-d`. Its products (4.2) and (4.3) use the primitive
`Γ₀(6)` classes with orientations `1,11` and `5,7`, the same CM points and
the eta quotient (4.1). The source gives monic coefficients in `ℤ[1/6]`;
`complexA` and `complexB` express equality with those actual complex products.
Only this exact literature assertion is admitted; the coordinate and reduction
claims in that lemma are separate.

```lean
theorem integralCMClassPolynomials_literature (d : ℕ) [Fact (-(d : ℤ) < 0)]
    (hd : 0 < d) (hsq : Squarefree d) (hmod : d % 24 = 23) :
    Nonempty (IntegralCMClassPolynomials d)
```

The manuscript degree assertion is proved by
[`cmClassPolynomialPair_integral_descent`](SptClassification/QuadraticForms/CMPolynomialDescent.lean):
for positive squarefree `d ≡ 23 (mod 24)`, the two monic models have degree
`2 * formClassNumber (-d)` and specialize to the actual oriented complex
products. Coefficient descent uses the literature premise above; degree comes
from the proved class counts. The models and their reductions are independent
of the descent witness by
[CMIntegralModelUniqueness](SptClassification/QuadraticForms/CMIntegralModelUniqueness.lean).

### `SptClassification.normalizedEisenstein_minus_reduces`

[Lean source](SptClassification/ModularForms/PrimeLocalNormalizedProduct.lean)

Classical `E_(p-1) ≡ 1` congruence, quoted immediately after (2.5) in [rolenManuscript, §2]. The coefficient is rational and reduction is in the prime-local ring.

```lean
theorem normalizedEisenstein_minus_reduces
    {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (n : ℕ) :
    RationalReduces p (normalizedEisensteinRationalCoefficient (p - 1) n)
      (if n = 0 then 1 else 0)
```

### `SptClassification.normalizedEisenstein_plus_reduces`

[Lean source](SptClassification/ModularForms/PrimeLocalNormalizedProduct.lean)

Classical `E_(p+1) ≡ E₂` congruence, quoted immediately after (2.5) in [rolenManuscript, §2], with the integral weight-two normalization.

```lean
theorem normalizedEisenstein_plus_reduces
    {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (n : ℕ) :
    RationalReduces p (normalizedEisensteinRationalCoefficient (p + 1) n)
      (eisensteinTwoIntegerCoefficient n : ZMod p)
```

### `SptClassification.eta_odd_matrix_law`

[Lean source](SptClassification/ModularForms/EtaOddMatrix.lean)

Dedekind eta transformation for positive odd lower-left entry and principal square root. [apostol1990, Chapter 3] is the proposed source; its exact equation locator and full phase applicability remain unverified.

```lean
theorem eta_odd_matrix_law (a b c d : ℤ)
    (hdet : a * d - b * c = 1) (hc : 0 < c) (hodd : c % 2 = 1)
    (z : UpperHalfPlane) :
    ModularForm.eta (etaMatrix a b c d hdet • z : UpperHalfPlane) =
      etaOddMatrixPhase a b c d * ((c : ℂ) * z + d).sqrt *
        ModularForm.eta z
```

### `SptClassification.QSeries.quadraticGaussSum_positivePhase`

[Lean source](SptClassification/QSeries/QuadraticGaussLiterature.lean)

Signed quadratic Gauss evaluation for the positive standard additive character and positive real square root. [berndtEvansWilliams1998, Chapter 1] is the proposed source; the exact theorem locator remains unverified.

```lean
theorem quadraticGaussSum_positivePhase (p : ℕ) [Fact p.Prime]
    (hpOdd : p ≠ 2) :
    gaussSum (quadraticComplexChar p) ZMod.stdAddChar =
      (if p % 4 = 1 then (1 : ℂ) else Complex.I) * (Real.sqrt p : ℂ)
```

## Proved manuscript deduction using literature

### `SptClassification.QSeries.square_coefficient_relation`

[Lean source](SptClassification/QSeries/SquareCoefficientRelation.lean)

The original coefficient lemma for the actual integral principal-form rows.
No squarefreeness hypothesis is imposed on `d`. The normalization is
`H_d = q^(-d/24) - a(d) q^(1/24) + …` and `K_d` has unit principal pole.
[rolenManuscript, label lem:coeff]. The manuscript deduction is proved using the three Rolen shadow
interfaces, `eta_odd_matrix_law`, and `quadraticGaussSum_positivePhase`.
Repeated prime factors in `m` are retained.


```lean
theorem square_coefficient_relation
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (sign : ℤ)
    (hsign : sign = 1 ∨ sign = -1) (d : ℕ) (hdPos : 0 < d)
    (hd : d % 24 = 23) (hr : legendreSym p (-(d : ℤ)) = sign)
    (hspt : ∀ j : ℕ, legendreSym p (1 - 24 * (j : ℤ)) = sign → p ∣ spt j)
    (m : ℕ) (hmPos : 0 < m) (hmCop : m.Coprime (6 * p)) :
    (p : ℤ) ∣ (m : ℤ) ^ 2 * principalHFourier d (fFourier d) ((m : ℤ) ^ 2) +
      (d : ℤ) * principalKFourier d ((m : ℤ) ^ 2)
```

## Manuscript deductions

No manuscript declaration has a direct admission. The integral lift, cusp
clearing and Hasse deductions are proved from the named literature interfaces;
their transitive dependency cones retain those admissions.

### `SptClassification.character_obstruction`

[Lean source](SptClassification/ModularForms/CharacterObstruction.lean)

A squarefree discriminant satisfying the two numerical bounds obstructs
vanishing on its character class. This is the original unconditional target
[rolenManuscript, label prop:obstruction]. Its proof constructs all four cusp
bounds for the same principal Shimura lift, then applies the integral
comparison and Hasse contradiction. It remains conditional on the literature.

```lean
theorem character_obstruction (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (sign : ℤ) (hsign : sign = 1 ∨ sign = -1)
    (d : ℕ) [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) (hr : legendreSym p (-(d : ℤ)) = sign)
    (hsep : (d + 1) ^ 2 < 24 * p)
    (hclass : 8 * formClassNumber (-(d : ℤ)) < p + 1) :
    ¬∀ j : ℕ, legendreSym p (1 - 24 * (j : ℤ)) = sign → p ∣ spt j
```

### `SptClassification.propagation`

[Lean source](SptClassification/ModularForms/CongruencePropagation.lean)

A noncanonical congruence propagates to its whole quadratic-character class.
This is the original unconditional target [rolenManuscript, label lem:prop].
Its modular transformation, cusp and integrality deductions are implemented
using the named literature premises. Its dependency cone remains
unconditionally open.

```lean
theorem propagation (p b : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hb : b < p)
    (hspt : ∀ n : ℕ, p ∣ spt (p * n + b))
    (hnotcanonical : ¬(p : ℤ) ∣ 24 * (b : ℤ) - 1)
    (N : ℕ)
    (hclass : @legendreSym p ⟨hp⟩ (1 - 24 * (N : ℤ)) =
      @legendreSym p ⟨hp⟩ (1 - 24 * (b : ℤ))) :
    p ∣ spt N
```

### `SptClassification.cm_separation`

[Lean source](SptClassification/QuadraticForms/CMSeparation.lean)

The reductions of the actual oriented class polynomials are coprime under
the manuscript bound, for both splitting types. The models come from the
explicit admitted integral-descent theorem, with no geometric hypothesis added
to this original target [rolenManuscript, label lem:separation].

```lean
theorem cm_separation (d p : ℕ) [Fact (-(d : ℤ) < 0)] [Fact p.Prime]
    (hd : 0 < d) (hsq : Squarefree d) (hmod : d % 24 = 23)
    (hcop : ¬p ∣ 6 * d) (hbound : (d + 1) ^ 2 < 24 * p) :
    let models := integralCMClassPolynomials d hd hsq hmod
    let reduction := cmCoefficientReduction p (fun h => hcop (dvd_mul_of_dvd_left h d))
    IsCoprime (models.modelA.map reduction) (models.modelB.map reduction)
```

## Remaining source and construction boundaries

Propagation cites [garthwaiteJameson2021, Proposition 4 and Theorem 5],
[deligneRapoport1973, Corollaire 3.12], and [radu2012, Corollary 5.3].
The Garthwaite–Jameson integral-lattice statement permits the reduction prime
to divide the progression modulus. Its application still requires an actual
holomorphic powered projection with the stated modular transformation law,
rational Fourier expansions and a uniform denominator.
`PoweredProjectionData.slash_integral` in
[ProgressionSlash.lean](SptClassification/ModularForms/ProgressionSlash.lean)
is an explicit assumption of the conditional construction, not an established
literature theorem. The full construction bundle is not admitted as a premise
of a completed manuscript proof.

The inverse-eta Hecke realization and coefficient identification have
manuscript proofs, using the explicitly listed eta and Gauss literature inputs.
The all-prime CM specialization and separation are proved. The global integral
lift and Hasse comparison are constructed from the named literature inputs.
Fourier objects retain support modulo 24 and the prescribed pole bound.
Rolen Lemma 5.2 gives the supersingular noncommuting norm bound; its inert-only
Proposition 5.3 does not establish separation for both splitting types.
The geometric application uses the proved simultaneous specialization preserving
both oriented CM actions. Character obstruction uses the constructed integral
and reduced lifts and logarithmic comparison for the same oriented class
polynomials. No bundle containing that conclusion is admitted.

The CM formal product premise uses the actual monic products with numerator
orientations `1,11` and denominator orientations `5,7`, over `ℤ[1/6]`.
The normalized reversed products have constant coefficient one. It does not
assume the logarithmic derivative, reduced lift or final Hasse obstruction.
Reduction requires a prime not dividing six, and does not divide by coefficient
indices. The analytic and formal product statements remain separate inputs.

### Complex uniformization

[CMUniformization](SptClassification/QuadraticForms/CMUniformization.lean)
contains two classical literature interfaces, both with visible `sorry` bodies:
`ComplexUniformization.curve_isElliptic` and
`ComplexUniformization.exists_uniformization`. For any independent period pair
`L`, they assert nonsingularity of the cubic with `a₄ = -L.g₂/4`,
`a₆ = -L.g₃/4`, and an additive equivalence from the actual complex torus to
its affine point group with coordinates `(℘(z), ℘′(z)/2)` away from the lattice.
The source is [silverman2009, Chapter VI, §§3–4]; exact theorem numbering has
not been checked. Transport of the CM quadratic relation and the order-six
point/subgroup is proved. Algebraicity of arbitrary additive maps, arithmetic
descent and simultaneous good reduction are not included in these premises.

### Negative half-integral Serre derivative

[HalfIntegralSerre](SptClassification/ModularForms/HalfIntegralSerre.lean)
proves the weight −1/2 to 3/2 transformation law using integer-weight Serre
equivariance. It requires a holomorphic nonvanishing theta function with
fourth-power multiplier law, and the transformation of the differentiated
function; that function need not be nonvanishing.
[ActualNormalizedAutomorphy](SptClassification/ModularForms/ActualNormalizedAutomorphy.lean)
applies it to the actual filtered inverse eta function. Theta and filtered
function transformation laws remain explicit inputs; no new literature or
manuscript admission is introduced.

### Specialization of endomorphisms under good reduction

`RationalPointMap.goodReduction_endomorphisms_sections_literature` in
[AlgebraicGoodReduction](SptClassification/QuadraticForms/AlgebraicGoodReduction.lean)
is the coordinate corollary of [milneAV2008, Chapter I, Corollary 16.4(b),
p. 68; Theorem 17.1 and Remark 17.2, p. 70; Theorem 17.3, p. 71].
It specializes geometric endomorphisms of an arbitrary nonsingular integral
Weierstrass model at the specified residue map, preserving the action on
integral sections. Finite coefficient descent and regular-extension Hom descent
precede the Néron extension argument; the source statements were inspected.
This single named literature admission contains no CM or separation conclusion.
The actual oriented actions, common-root construction and original
`cm_separation` are proved from it and the earlier disclosed premises.
Both ordinary and supersingular primes remain covered.

### Actual eta Tate chart and Serre comparison

[LevelSixSerreExpansion](SptClassification/ModularForms/LevelSixSerreExpansion.lean)
and [LevelSixTateComparison](SptClassification/ModularForms/LevelSixTateComparison.lean)
construct the actual eta Laurent parameter and its nonsingular generic curve.
The same differential frame gives the Serre expansion, Hasse expansion one,
and expansion `E₂` for `12 D_(p-1) H`. Three named admissions are used:

- `weierstrass_serre_tate_literature`: [katz1973, Appendix A1.3.17–18,
  p. 169; A1.4, pp. 170–171, especially Corollary A1.4.5]. Its coordinate
  formulation retains invertible six, the exact Kodaira–Spencer and two
  invariant connection identities, nonzero discriminant, and an actual
  variable change to the canonical Tate curve. The primary source was inspected.
- `eta_tate_invariant_literature`: [maier2009, arXiv v4, §3.1 Table 2,
  p. 11; §3.2 Table 4, p. 12], with parameter `72/t`. The primary table was
  inspected. The formal identity is a coefficient consequence over `ℤ[1/6]`
  followed by reduction, retaining the actual eta Euler product. It does not
  assert compatibility of differential frames or torsion markings.
- `split_multiplicative_tate_comparison_literature`: [silverman1994,
  Chapter V, Theorem 3.1], specialized to the formal discrete valuation field
  `K((q))`, with uniqueness of the Tate parameter. The hypotheses retain
  nonzero discriminant, nodal special fiber, unit `c₄`, an explicit splitting
  root `r² c₄(0) = -c₆(0)`, and equality with the canonical Tate invariant.
  The primary book was not directly inspected; the locator has secondary
  support; direct primary-source verification remains outstanding.

The particular eta frame requires `r² = -12` in the coefficient field.
No descent of this choice, marked six-torsion comparison, global integral
lift, or final character obstruction is asserted by these interfaces.
All three visible `sorry` bodies remain open literature premises.

### Even eta differential frame

[LevelSixEtaFrame](SptClassification/ModularForms/LevelSixEtaFrame.lean)
defines the integral expansion of
`b = eta(tau) eta(6 tau)^6 / (eta(2 tau)^2 eta(3 tau)^3)`.
Its one new literature premise, `eta_parameter_derivative_literature`, is
`Theta t = -t(t+8)(t+9)b^2`, with the actual eta coordinate and Euler products.
The source is [maier2009, arXiv v4, equation (6.6), p. 29; Tables 8 and 11,
pp. 26 and 31], after substituting `t=72/t6` and `h6=t*b`. The integral
Laurent identity is specialized to coefficient fields.

The proved `eta_frame_sq` identifies the chosen Tate differential frame
squared with `-b^2/12`; `eta_expansion_even` gives the corresponding
even-weight polynomial section expansion. They require invertible six and
the existing choice `r^2=-12`.
These results fix the normalization used in the global holomorphic-section
and integral comparison for the Shimura lift.


### Generic meromorphic Shimura lift

[GenericShimuraLift](SptClassification/ModularForms/GenericShimuraLift.lean)
contains the named literature input `borcherds_signature21_weightFour_lift`:
the weight-`5/2` eta-multiplier input, multiplied by the distinguished Weil
vector for the quadratic form `6b²-ac`, has a weight-four meromorphic lift
on `Gamma0 6`. Its double poles lie on the negative-coefficient divisors;
its Fourier row is the stated integral divisor sum above some cusp height.
The indexing hypothesis `N % 24 = 23` aligns the input exponents with the
square-index coefficients. The zero coefficient is required to vanish.
The same lift satisfies determinant-normalized Atkin–Lehner covariance
with signs `+1,-1,-1` at zero, one half and one third. This is an
explicit literature premise for the full Weil input, not an inference from
its principal part alone. Sources: [borcherds1998, §6, printed p. 23;
Theorem 14.3(3),(5), printed pp. 55–56; Example 14.4, printed p. 59]
and [liZemel2018, Theorem 5.1, PDF p. 14].

[CMShimuraLift](SptClassification/ModularForms/CMShimuraLift.lean) specializes
this input to the actual principal form and proves interior pole clearing
with the actual oriented CM support. The full-input covariance gives
finite-cusp germs in
[CMShimuraFiniteCuspGerm](SptClassification/ModularForms/CMShimuraFiniteCuspGerm.lean).
The positive-determinant slash comparison and bounds construct global cusp
regularity; the exact Fourier row then supplies integral descent.

### Rational sections and Laurent comparison

[LevelSixRationalSections](SptClassification/ModularForms/LevelSixRationalSections.lean)
retains weights in `K(t)[omega]` and extends the Serre connection by the
quotient rule. [LevelSixTateInjectivity](SptClassification/ModularForms/LevelSixTateInjectivity.lean)
proves fixed-weight injectivity and the Serre/Hasse expansion laws using
the actual eta coordinate and differential frame, with `6 != 0` and
`r² = -12`. These introduce no admissions; the existing Tate and Hasse
literature premises remain in their dependency cones.

[LaurentHasseComparison](SptClassification/ModularForms/LaurentHasseComparison.lean)
proves the homogeneous Hasse identity from independent weight-two and
weight-four sections, fixed-weight injectivity and their Laurent
differential identity. Its generic proof has only the three standard
logical axioms. Rational sections expand into Laurent series; evaluation
at a geometric point still requires a nonvanishing denominator.

[CMShimuraCuspComparison](SptClassification/ModularForms/CMShimuraCuspComparison.lean)
proves that the actual principal lift has an analytic infinity-cusp germ
after multiplication by `(A_d B_d)^2 Delta^(8h)`. Its value at the cusp is
zero, and its high-cusp values agree with the interior pole-cleared extension.
The proof adds no admissions. The finite-cusp bounds and global clearing
complete holomorphy at the other cusps and integral global descent.


### Holomorphic eta basis and logarithmic expansion

[LevelSixHolomorphicBasis](SptClassification/ModularForms/LevelSixHolomorphicBasis.lean)
adds two named literature inputs. `holomorphic_polynomial_representation_literature`
represents every actual even-weight `Gamma0(6)` modular form as `P(t)b^k`,
with `deg P <= k`. All-cusp boundedness is required by the bundled modular form.
This is a consequence of [maier2009, arXiv v4, Corollary 5.5.1, pp. 23–24;
Table 8, p. 26; character calculation, p. 28; Table 11, p. 31] and compact
genus-zero divisor theory, rather than a verbatim theorem of Maier.
`polynomial_qExpansion_literature` identifies its expansion with the explicit
integral eta basis, using the convergent Euler products and Taylor uniqueness.
The subsequent coefficient descent to any complex subring is proved.
These interfaces require global holomorphy; they do not construct the CM lift.

[LevelSixLogarithmicExpansion](SptClassification/ModularForms/LevelSixLogarithmicExpansion.lean)
proves that the actual weight-two rational logarithmic section expands to
`Theta(A(t)/B(t))/(A(t)/B(t))` for nonzero polynomials, invertible six,
and the chosen frame with `r^2 = -12`. It adds no admissions.

[LevelSixRationalEtaClearing](SptClassification/ModularForms/LevelSixRationalEtaClearing.lean)
constructs the weight-four section with coefficient
`144 P / ((AB)^2 Deta^(8h))`, where `Deta=X^6(X+8)^2(X+9)^3`.
It proves its Laurent expansion and regularity at Hasse zeros outside the CM
support. These proofs add no admissions and retain the existing Tate/Hasse
literature dependencies. The numerator must be supplied independently; the
module does not assume the existence of the actual CM lift or its global
cleared numerator. Its discriminant is the Tate-curve discriminant; comparison
with the normalized Euler product is supplied below.


[TateDiscriminantEuler](SptClassification/ModularForms/TateDiscriminantEuler.lean)
uses one named literature premise, `discriminant_euler_literature`:
for a field with invertible six, the canonical Tate equation has discriminant
`q * product (1-q^n)^24`, with differential `dx/(2y+x)` and no extra
`12^6` or analytic period factor. The citation is [silverman1994, Chapter V,
§3, Tate equation and discriminant-product display]. The primary Silverman
display has not been independently inspected. [katz1973, Appendix A1.2.3,
pp. 160–161] confirms the equation and differential, not this product identity.
The module proves coefficient specialization and the exact rational clearing
factor for the integral CM Shimura row. Polynomial degrees are measured before
reduction. It does not admit the existence of a global CM lift.

[LevelSixEtaPolynomialLaurent](SptClassification/ModularForms/LevelSixEtaPolynomialLaurent.lean)
proves the eta-polynomial expansion over coefficient rings and its compatibility
with reduction. [CMShimuraRationalComparison](SptClassification/ModularForms/CMShimuraRationalComparison.lean)
then recovers the actual integral Shimura row as the expansion of the rational
weight-four section, from a globally holomorphic cleared modular form with that
Fourier row. Its `numerator_of_holomorphic_clearing` keeps the global form and
row equality as explicit inputs. These modules add no admissions; the global
analytic construction supplies both inputs in character obstruction.


[LevelSixCuspCriterion](SptClassification/ModularForms/LevelSixCuspCriterion.lean)
uses `maier_cusp_representatives_literature`: every cusp of the real matrix
image of `Gamma0(6)` lies in the group orbit of infinity, zero, one half or
one third. The source is [maier2009, arXiv v4, §2, cusp classification
immediately before (2.1)]: the divisors of six each contribute one orbit
since `gcd(d,6/d)=1`. Boundedness transport along these orbits and construction
of a modular form from four independently supplied cusp bounds are proved.
This premise concerns cusp orbits only. The bounds for the actual CM form
are proved at infinity and in each of the three finite cusp charts.
