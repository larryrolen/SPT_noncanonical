/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.LevelSixTateSections
public import Mathlib.RingTheory.LaurentSeries
import all SptClassification.ModularForms.LevelSixModularSections
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Serre differentiation in a framed Tate expansion

The target is Laurent series: an interior regular coefficient polynomial may
have a pole at the cusp. The generic comparison below retains the actual
Weierstrass equation, its invariant differential frame, and the polynomial
Kodaira–Spencer and connection identities. Its level-six specialization and
characteristic-p Hasse deduction use the previously constructed sections.
-/

public noncomputable section

namespace SptClassification.LevelSixSerreExpansion

open Polynomial LevelSixModularSections LevelSixHasseGeometry LevelSixTateSections

variable (K : Type*) [Field K]

/-- The canonical inclusion of power series into Laurent series. -/
def tateBase : PowerSeries K →+* LaurentSeries K := HahnSeries.ofPowerSeries ℤ K

/-- Constant coefficients in the Laurent target. -/
def constants : K →+* LaurentSeries K := (tateBase K).comp PowerSeries.C

theorem tateBase_apply (F : PowerSeries K) :
    tateBase K F = HahnSeries.ofPowerSeries ℤ K F := (rfl)

@[simp] theorem constants_apply (a : K) :
    constants K a = HahnSeries.single 0 a := by
  simp [constants, tateBase]

/-- The Euler operator `q d/dq`, including negative exponents. -/
def theta (F : LaurentSeries K) : LaurentSeries K :=
  HahnSeries.single 1 1 * LaurentSeries.derivative K F

/-- The weight-two quasimodular series, with its integral normalization. -/
def eisensteinTwo : LaurentSeries K :=
  tateBase K (1 - 24 * divisorSeries K 1)

@[simp] theorem theta_one : theta K 1 = 0 := by
  ext n
  simp [theta, LaurentSeries.derivative, LaurentSeries.hasseDeriv_coeff,
    HahnSeries.coeff_single_mul]
  intro h
  simp [h]

/-- Framed formal Serre comparison, derived from [katz1973], Appendix
A1.3.17–18 (p.169), A1.4 (pp.170–171), especially the operator
`12 Theta - k P` and Corollary A1.4.5. This is a coordinate formulation,
not a verbatim statement in Katz. The three polynomial identities identify
`v d/dt + k a` with the Gauss–Manin/Serre operator: the first fixes the
Kodaira–Spencer scale and the latter two fix the splitting, with Tate
`c₆ = -E₆`. Nonzero discriminant and invertibility of six are essential.
The actual change to the canonical Tate equation fixes the differential
frame. This theorem makes no assertion that such a change exists. -/
theorem weierstrass_serre_tate_literature
    (h6 : (6 : K) ≠ 0) (W : WeierstrassCurve K[X]) (v a : K[X])
    (hks : v * WeierstrassHasse.ksNumerator W = 1728 * W.Δ)
    (hfour : 3 * (v * derivative W.c₄ + C (4 : K) * a * W.c₄) = W.c₆)
    (hsix : 2 * (v * derivative W.c₆ + C (6 : K) * a * W.c₆) = W.c₄ ^ 2)
    (t : LaurentSeries K) (Cw : WeierstrassCurve.VariableChange (LaurentSeries K))
    (hΔ : W.Δ.eval₂ (constants K) t ≠ 0)
    (hcurve : Cw • W.map (eval₂RingHom (constants K) t) =
      (tateCurve K).map (tateBase K))
    (k : ℕ) (f : K[X]) :
    (v * derivative f + C (k : K) * a * f).eval₂ (constants K) t *
        (↑Cw.u⁻¹ : LaurentSeries K) ^ (k + 2) =
      theta K (f.eval₂ (constants K) t * (↑Cw.u⁻¹ : LaurentSeries K) ^ k) -
        (k : LaurentSeries K) / 12 * eisensteinTwo K *
          (f.eval₂ (constants K) t * (↑Cw.u⁻¹ : LaurentSeries K) ^ k) := by
  sorry

variable {K}

/-- Actual base change of the integral family, used to apply the universal
Weierstrass comparison without changing the modular coordinate. -/
theorem map_curve (t : LaurentSeries K) :
    (LevelSixWeierstrass.curve (X : K[X])).map
        (eval₂RingHom (constants K) t) = LevelSixWeierstrass.curve t := by
  ext <;> simp [WeierstrassCurve.map]

/-- Every actual level-six Tate chart with the canonical power-series base
has the prescribed Serre Fourier expansion. Ellipticity is retained as an
explicit geometric hypothesis, independently of the Fourier conclusion. -/
theorem expansion_serre
    (h6 : (6 : K) ≠ 0) (T : TateRealization (K := K) (S := LaurentSeries K))
    (hbase : T.base = tateBase K)
    (hΔ : (LevelSixWeierstrass.curve (X : K[X])).Δ.eval₂
      (constants K) T.parameter ≠ 0) (k : ℕ) (f : K[X]) :
    T.expansion (sectionOf (k + 2) (serre k f)) =
      theta K (T.expansion (sectionOf k f)) -
        (k : LaurentSeries K) / 12 * eisensteinTwo K *
          T.expansion (sectionOf k f) := by
  have hcurve : T.change • (LevelSixWeierstrass.curve (X : K[X])).map
      (eval₂RingHom (constants K) T.parameter) =
      (tateCurve K).map (tateBase K) := by
    rw [map_curve, T.equation, hbase]
  simpa only [TateRealization.expansion_sectionOf, hbase, constants, serre] using
    weierstrass_serre_tate_literature K h6
      (LevelSixWeierstrass.curve (X : K[X])) coordinateDerivative connection
      coordinateDerivative_mul_ksNumerator
      (by simpa only [serre, Nat.cast_ofNat] using (serre_c₄ (R := K)))
      (by simpa only [serre, Nat.cast_ofNat] using (serre_c₆ (R := K)))
      T.parameter T.change hΔ hcurve k f

/-- The same comparison applies to any homogeneous section. -/
theorem expansion_serreSection
    (h6 : (6 : K) ≠ 0) (T : TateRealization (K := K) (S := LaurentSeries K))
    (hbase : T.base = tateBase K)
    (hΔ : (LevelSixWeierstrass.curve (X : K[X])).Δ.eval₂
      (constants K) T.parameter ≠ 0) (k : ℕ) (F : SectionRing K)
    (hF : IsWeight k F) :
    T.expansion (serreSection k F) = theta K (T.expansion F) -
      (k : LaurentSeries K) / 12 * eisensteinTwo K * T.expansion F := by
  obtain ⟨f, rfl⟩ := hF
  rw [serreSection_sectionOf]
  exact expansion_serre h6 T hbase hΔ k f

/-- The weight-two coordinate section expands to the Euler derivative of
exactly the parameter of the actual Tate chart. -/
theorem expansion_coordinateSection
    (h6 : (6 : K) ≠ 0) (T : TateRealization (K := K) (S := LaurentSeries K))
    (hbase : T.base = tateBase K)
    (hΔ : (LevelSixWeierstrass.curve (X : K[X])).Δ.eval₂
      (constants K) T.parameter ≠ 0) :
    T.expansion coordinateSection = theta K T.parameter := by
  have h := expansion_serre h6 T hbase hΔ 0 (X : K[X])
  simpa [coordinateSection, serre, TateRealization.expansion_sectionOf] using h

/-- In characteristic `p`, the actual section `12 D_(p-1) H` expands to
`E₂`: `H` expands to one and `-(p-1)=1`. This proves the manuscript's
normalization in the very same actual Tate realization as its Hasse section.
It does not identify an independently constructed Eisenstein section. -/
theorem expansion_serreHasse
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 3 < p)
    (h6 : (6 : K) ≠ 0) (T : TateRealization (K := K) (S := LaurentSeries K))
    (hbase : T.base = tateBase K)
    (hΔ : (LevelSixWeierstrass.curve (X : K[X])).Δ.eval₂
      (constants K) T.parameter ≠ 0) :
    T.expansion (serreHasseSection p) = eisensteinTwo K := by
  letI : CharP (LaurentSeries K) p :=
    ((constants K).charP_iff_charP p).mp inferInstance
  have h12 : (12 : LaurentSeries K) ≠ 0 := by
    have h6' : (6 : LaurentSeries K) ≠ 0 := by
      intro h
      apply h6
      apply (constants K).injective
      simpa only [map_ofNat, map_zero] using h
    have h2 : (2 : LaurentSeries K) ≠ 0 := by
      intro h
      apply h6'
      calc (6 : LaurentSeries K) = 2 * 3 := by norm_num
           _ = 0 := by rw [h, zero_mul]
    convert mul_ne_zero h2 h6' using 1 <;> norm_num
  have hpcast : ((p - 1 : ℕ) : LaurentSeries K) = -1 := by
    have h := Nat.cast_sub (R := LaurentSeries K) (by omega : 1 ≤ p)
    simpa [CharP.cast_eq_zero (LaurentSeries K) p] using h
  rw [serreHasseSection_eq, map_mul, map_ofNat,
    expansion_serreSection h6 T hbase hΔ (p - 1) _ (hasseSection_weight p),
    T.expansion_hasse p hp, theta_one, mul_one, hpcast]
  field_simp [h12]
  ring

end SptClassification.LevelSixSerreExpansion
