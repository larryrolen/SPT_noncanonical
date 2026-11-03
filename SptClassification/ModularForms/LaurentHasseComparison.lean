/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.ConditionalLambert
public import SptClassification.ModularForms.LevelSixSerreExpansion
import all SptClassification.ModularForms.LevelSixSerreExpansion

/-!
# Homogeneous Hasse comparison with Laurent expansions

The coordinate and rational modular sections may have poles at infinity.
The expansion therefore takes values in Laurent series. Only injectivity
on each fixed weight is needed to lift the differential identity in
[rolenManuscript, Section 4, equations (differential) and (hasse)].
No evaluation of arbitrary rational functions at a geometric point is used.
-/

public noncomputable section

namespace SptClassification.LaurentHasseComparison

open LevelSixSerreExpansion

/-- The Laurent Euler operator agrees with the power-series Euler operator
on the canonical inclusion, including the vanishing negative coefficients. -/
theorem theta_tateBase {K : Type*} [Field K] (f : PowerSeries K) :
    theta K (tateBase K f) = tateBase K (QSeries.eulerDerivative f) := by
  ext n
  have hcoeff (g : LaurentSeries K) :
      (theta K g).coeff n = (n : K) * g.coeff n := by
    simp [theta, HahnSeries.coeff_single_mul, LaurentSeries.derivative,
      LaurentSeries.hasseDeriv_coeff, zsmul_eq_mul]
  rw [hcoeff]
  change (n : K) * ((f : LaurentSeries K).coeff n) =
    ((QSeries.eulerDerivative f : PowerSeries K) : LaurentSeries K).coeff n
  simp only [PowerSeries.coeff_coe]
  split_ifs with hn
  · simp
  · rw [QSeries.coeff_eulerDerivative]
    have hn' : 0 ≤ n := le_of_not_gt hn
    lift n to ℕ using hn'
    simp

/-- The already proved manuscript power-series differential row has the
same meaning in the Laurent target. -/
theorem differential_tateBase {p d : ℕ} [Fact p.Prime]
    (hdiff : QSeries.eulerDerivative (QSeries.eulerDerivative
      (QSeries.principalLogarithmicLambertSeries p d)) =
        PowerSeries.C (d : ZMod p) *
          QSeries.eulerDerivative (QSeries.principalShimuraLambertSeries p d)) :
    theta (ZMod p) (theta (ZMod p)
      (tateBase (ZMod p) (QSeries.principalLogarithmicLambertSeries p d))) =
      constants (ZMod p) (d : ZMod p) * theta (ZMod p)
        (tateBase (ZMod p) (QSeries.principalShimuraLambertSeries p d)) := by
  rw [theta_tateBase, theta_tateBase, hdiff, map_mul, theta_tateBase]
  rfl

variable {p : ℕ} [Fact p.Prime]
variable {K F : Type*} [Field K] [Algebra (ZMod p) (LaurentSeries K)]
variable [CommRing F] [Algebra (ZMod p) F]

/-- Hasse correction of a weight-indexed connection. Its linearity is not
needed for the homogeneous comparison. -/
def correctedDerivative (H E : F) (D : ℕ → F → F) (k : ℕ) (f : F) : F :=
  H * D k f + ((k : ZMod p) / 12) • (E * f)

theorem correctedDerivative_apply (H E : F) (D : ℕ → F → F) (k : ℕ) (f : F) :
    correctedDerivative (p := p) H E D k f = H * D k f + ((k : ZMod p) / 12) • (E * f) :=
  (rfl)

/-- The Hasse correction cancels the Serre correction also for Laurent
expansions. The Hasse and Eisenstein expansions refer to the same frame. -/
theorem theta_expansion
    (qexp : F →ₐ[ZMod p] LaurentSeries K)
    (H E : F) (D : ℕ → F → F)
    (e₂ : LaurentSeries K) (k : ℕ) (f : F)
    (hH : qexp H = 1) (hE : qexp E = e₂)
    (hD : qexp (D k f) = theta K (qexp f) -
      ((k : ZMod p) / 12) • (e₂ * qexp f)) :
    qexp (correctedDerivative (p := p) H E D k f) = theta K (qexp f) := by
  rw [correctedDerivative_apply, map_add, map_mul, hH, one_mul, hD]
  simp only [Algebra.smul_def, map_mul, AlgHom.commutes, hE]
  exact sub_add_cancel _ _

/-- Weight bookkeeping for the Hasse-corrected derivative, independently
of cusp regularity or the chosen expansion target. -/
theorem theta_mem
    (forms : ℕ → Submodule (ZMod p) F)
    (hmul : ∀ {k l : ℕ} {f g : F},
      f ∈ forms k → g ∈ forms l → f * g ∈ forms (k + l))
    (D : ℕ → F → F)
    (hD : ∀ {k : ℕ} {f : F}, f ∈ forms k → D k f ∈ forms (k + 2))
    (H E : F) (hH : H ∈ forms (p - 1)) (hE : E ∈ forms (p + 1))
    {k : ℕ} {f : F} (hf : f ∈ forms k) :
    correctedDerivative (p := p) H E D k f ∈ forms (k + p + 1) := by
  have hp : 1 ≤ p := (Fact.out : p.Prime).one_le
  have hleft := hmul hH (hD hf)
  have hright := hmul hE hf
  have hweight : p - 1 + (k + 2) = k + p + 1 := by omega
  rw [hweight] at hleft
  have hweight' : p + 1 + k = k + p + 1 := by omega
  rw [hweight'] at hright
  rw [correctedDerivative_apply]
  exact (forms _).add_mem hleft ((forms _).smul_mem _ hright)

/-- The manuscript differential identity becomes an equality of rational
sections of weight `2p+4`. The two sections `L` and `J` are independently
supplied; the hypothesis is only an identity of their Laurent expansions.
The fixed-weight injectivity may be obtained from a transcendental Tate
coordinate, without a power-series map on the full rational section ring. -/
theorem homogeneous_identity
    (forms : ℕ → Submodule (ZMod p) F)
    (hmul : ∀ {k l : ℕ} {f g : F},
      f ∈ forms k → g ∈ forms l → f * g ∈ forms (k + l))
    (D : ℕ → F → F)
    (hD : ∀ {k : ℕ} {f : F}, f ∈ forms k → D k f ∈ forms (k + 2))
    (qexp : F →ₐ[ZMod p] LaurentSeries K)
    (hinj : ∀ {k : ℕ} {f g : F},
      f ∈ forms k → g ∈ forms k → qexp f = qexp g → f = g)
    (H E : F) (hH : H ∈ forms (p - 1)) (hE : E ∈ forms (p + 1))
    (hHq : qexp H = 1)
    (hTheta : ∀ {k : ℕ} {f : F}, f ∈ forms k →
      qexp (correctedDerivative (p := p) H E D k f) = theta K (qexp f))
    (L J : F) (hL : L ∈ forms 2) (hJ : J ∈ forms 4)
    (d : ZMod p)
    (hdiff : theta K (theta K (qexp L)) = d • theta K (qexp J)) :
    correctedDerivative (p := p) H E D (p + 3) (correctedDerivative (p := p) H E D 2 L) =
      d • (H * correctedDerivative (p := p) H E D 4 J) := by
  have hthetaL : correctedDerivative (p := p) H E D 2 L ∈ forms (p + 3) := by
    convert theta_mem forms hmul D hD H E hH hE hL using 1 <;> congr 1 <;> omega
  have hleft : correctedDerivative (p := p) H E D (p + 3) (correctedDerivative (p := p) H E D 2 L) ∈
      forms (2 * p + 4) := by
    convert theta_mem forms hmul D hD H E hH hE hthetaL using 1 <;> congr 1 <;> omega
  have hthetaJ : correctedDerivative (p := p) H E D 4 J ∈ forms (p + 5) := by
    convert theta_mem forms hmul D hD H E hH hE hJ using 1 <;> congr 1 <;> omega
  have hright : d • (H * correctedDerivative (p := p) H E D 4 J) ∈ forms (2 * p + 4) := by
    have h := hmul hH hthetaJ
    have hp : 1 ≤ p := (Fact.out : p.Prime).one_le
    have hw : p - 1 + (p + 5) = 2 * p + 4 := by omega
    rw [hw] at h
    exact (forms _).smul_mem _ h
  apply hinj hleft hright
  rw [hTheta hthetaL, hTheta hL]
  simpa only [Algebra.smul_def, map_mul, AlgHom.commutes, hHq, one_mul,
    hTheta hJ] using hdiff

end SptClassification.LaurentHasseComparison
