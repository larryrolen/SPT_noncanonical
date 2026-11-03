/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.ProgressionSlash
public import SptClassification.ModularForms.PrimeLocalRational
public import Mathlib.RingTheory.RootsOfUnity.Minpoly

/-!
# Cyclotomic q-expansion integrality

The literature input is exactly the integral-coefficient slash principle in
[garthwaiteJameson2021, Theorem 5, PDF p. 4]. Its level need not be prime to
the reduction characteristic. The localization deduction keeps a single
denominator explicit; coefficientwise rationality alone does not supply it.
-/

public section

namespace SptClassification

open UpperHalfPlane
open scoped MatrixGroups

/-- The ring `ℤ[ζ]` inside the complex numbers, for the chosen root of unity. -/
noncomputable def cyclotomicCoefficientRing (ζ : ℂ) : Subalgebra ℤ ℂ :=
  Algebra.adjoin ℤ ({ζ} : Set ℂ)

/-- An actual holomorphic Fourier expansion at infinity, with `q = exp(2πiτ)`.
The width is one, as it is for forms on `Γ₁(N)`. -/
def HasIntegralWeightQExpansion (F : UpperHalfPlane → ℂ) (a : ℕ → ℂ) : Prop :=
  ∀ τ : UpperHalfPlane,
    HasSum (fun n : ℕ => a n * Function.Periodic.qParam 1 τ ^ n) (F τ)

/-- Construct a width-one expansion from its pointwise convergent sums. -/
theorem HasIntegralWeightQExpansion.of_hasSum
    {F : UpperHalfPlane → ℂ} {a : ℕ → ℂ}
    (h : ∀ τ : UpperHalfPlane,
      HasSum (fun n : ℕ => a n * Function.Periodic.qParam 1 τ ^ n) (F τ)) :
    HasIntegralWeightQExpansion F a := h

/-- The integral q-expansion principle of [garthwaiteJameson2021, Theorem 5,
PDF p. 4], attributed there to [deligneRapoport1973, Corollaire 3.12] and
[radu2012, Corollary 5.3]. Both expansions represent the indicated analytic
functions. Positive weight and level, the full `Γ₁(N)` condition, and the
coefficient ring `ℤ[ζ_N]` are retained. This is a named literature admission,
not a prime-local strengthening of the cited statement. -/
theorem garthwaiteJameson_slash_cyclotomic_integral
    (N k : ℕ) (hN : 0 < N) (hk : 0 < k)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ N)
    (F : UpperHalfPlane → ℂ) (hF : HolomorphicGammaOneForm N k F)
    (γ : CongruenceSubgroup.Gamma0 N) (a b : ℕ → ℂ)
    (ha : HasIntegralWeightQExpansion F a)
    (hb : HasIntegralWeightQExpansion (progressionIntegralSlash k γ F) b)
    (hint : ∀ n, a n ∈ cyclotomicCoefficientRing ζ) :
    ∀ n, b n ∈ cyclotomicCoefficientRing ζ := by
  sorry

/-- Multiplying a Fourier expansion by a constant multiplies its coefficients. -/
theorem HasIntegralWeightQExpansion.const_mul
    {F : UpperHalfPlane → ℂ} {a : ℕ → ℂ}
    (h : HasIntegralWeightQExpansion F a) (c : ℂ) :
    HasIntegralWeightQExpansion (fun τ => c * F τ) (fun n => c * a n) := by
  intro τ
  simpa only [mul_assoc] using (h τ).mul_left c

/-- The cyclotomic coefficient ring consists of algebraic integers. -/
theorem cyclotomicCoefficientRing_isIntegral
    {N : ℕ} (hN : 0 < N) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    {x : ℂ} (hx : x ∈ cyclotomicCoefficientRing ζ) : IsIntegral ℤ x := by
  letI : Algebra.IsIntegral ℤ (cyclotomicCoefficientRing ζ) := by
    apply Algebra.IsIntegral.adjoin
    intro y hy
    obtain rfl := Set.mem_singleton_iff.mp hy
    exact hζ.isIntegral hN
  exact (Algebra.IsIntegral.isIntegral (⟨x, hx⟩ : cyclotomicCoefficientRing ζ)).algebraMap

/-- Constant scaling preserves the actual holomorphic modular-form conditions. -/
theorem HolomorphicGammaOneForm.const_mul
    {N k : ℕ} {F : UpperHalfPlane → ℂ}
    (hF : HolomorphicGammaOneForm N k F) (c : ℂ) :
    HolomorphicGammaOneForm N k (fun τ => c * F τ) := by
  refine ⟨mdifferentiable_const.mul hF.holomorphic, ?_, ?_⟩
  · intro γ ha hc hd τ
    simp only [progressionIntegralSlash_const_mul, hF.gammaOne γ ha hc hd]
  · intro γ
    rw [progressionIntegralSlash_const_mul]
    exact (hF.boundedAtCusps γ).const_mul_left c

/-- Rational integrality descends through the faithful complex embedding. -/
theorem rational_eq_integer_of_complex_integral (q : ℚ)
    (hq : IsIntegral ℤ (q : ℂ)) : ∃ z : ℤ, (z : ℚ) = q := by
  have hq' : IsIntegral ℤ q :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ ℚ ℂ)
      (IsScalarTower.toAlgHom ℤ ℚ ℂ).injective).mp hq
  exact IsIntegrallyClosed.isIntegral_iff.mp hq'

/-- After clearing one denominator prime to `p`, complex integrality gives
a faithful prime-local reduction of a rational coefficient. -/
theorem rationalReduces_of_cleared_integral
    (p : ℕ) [Fact p.Prime] (D : ℤ) (hD : ¬(p : ℤ) ∣ D)
    (q : ℚ) (hq : IsIntegral ℤ ((D : ℂ) * (q : ℂ))) :
    ∃ z : ZMod p, RationalReduces p q z := by
  have hD0 : D ≠ 0 := fun h => hD (h ▸ dvd_zero _)
  have hDQ : (D : ℚ) ≠ 0 := by exact_mod_cast hD0
  have hDZ : (D : ZMod p) ≠ 0 := by
    exact fun h => hD ((ZMod.intCast_zmod_eq_zero_iff_dvd D p).mp h)
  obtain ⟨n, hn⟩ := rational_eq_integer_of_complex_integral ((D : ℚ) * q)
    (by simpa only [Rat.cast_mul, Rat.cast_intCast] using hq)
  refine ⟨(n : ZMod p) / D, ?_⟩
  have heq : q = (n : ℚ) / D := by
    apply (eq_div_iff hDQ).mpr
    rw [hn]
    ring
  rw [heq]
  exact RationalReduces.ofFraction p n D hD _ (div_mul_cancel₀ _ hDZ)

/-- The prime-local consequence of the cited integral slash theorem. The
common denominator `D` is an explicit hypothesis to be supplied by the actual
Fourier construction. In particular no assumption `p ∤ N` is used. -/
theorem slash_rational_reduces_of_common_denominator
    (p N k : ℕ) [Fact p.Prime] (hN : 0 < N) (hk : 0 < k)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ N)
    (F : UpperHalfPlane → ℂ) (hF : HolomorphicGammaOneForm N k F)
    (γ : CongruenceSubgroup.Gamma0 N) (a b : ℕ → ℚ)
    (ha : HasIntegralWeightQExpansion F (fun n => (a n : ℂ)))
    (hb : HasIntegralWeightQExpansion (progressionIntegralSlash k γ F)
      (fun n => (b n : ℂ)))
    (D : ℤ) (hD : ¬(p : ℤ) ∣ D)
    (hclear : ∀ n, ∃ z : ℤ, (D : ℚ) * a n = z) :
    ∀ n, ∃ z : ZMod p, RationalReduces p (b n) z := by
  have hs := ha.const_mul (D : ℂ)
  have ht : HasIntegralWeightQExpansion
      (progressionIntegralSlash k γ (fun τ => (D : ℂ) * F τ))
      (fun n => (D : ℂ) * (b n : ℂ)) := by
    simpa only [progressionIntegralSlash_const_mul] using hb.const_mul (D : ℂ)
  have hi : ∀ n, (D : ℂ) * (a n : ℂ) ∈ cyclotomicCoefficientRing ζ := by
    intro n
    obtain ⟨z, hz⟩ := hclear n
    have hzC : (D : ℂ) * (a n : ℂ) = (z : ℂ) := by exact_mod_cast hz
    rw [hzC]
    exact (cyclotomicCoefficientRing ζ).algebraMap_mem z
  have hout := garthwaiteJameson_slash_cyclotomic_integral N k hN hk ζ hζ
    (fun τ => (D : ℂ) * F τ) (hF.const_mul D) γ _ _ hs ht hi
  intro n
  exact rationalReduces_of_cleared_integral p D hD (b n)
    (cyclotomicCoefficientRing_isIntegral hN hζ (hout n))

end SptClassification
