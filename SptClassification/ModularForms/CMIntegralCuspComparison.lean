/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.CMActualCuspClearing
public import SptClassification.ModularForms.CMShimuraCuspClearing
public import SptClassification.ModularForms.EtaQuotientExpansionScale
public import SptClassification.ModularForms.HighCuspFourierUniqueness
import all SptClassification.ModularForms.CMFormalProduct
import all SptClassification.ModularForms.CMShimuraCuspClearing
import all SptClassification.ModularForms.CMActualCuspClearing
import all SptClassification.ModularForms.CMAnalyticCuspClearing

/-!
# The integral Fourier row of an independently cleared CM lift

Finite Cauchy products compare the actual CM polynomial homogenizations and
Euler discriminant factor with their integral formal series. Fourier uniqueness
then identifies the row of a globally holomorphic form agreeing with the cleared
lift at the high cusp. [rolenManuscript, Section 4, proof of prop:obstruction]
-/

public noncomputable section

namespace SptClassification

open PowerSeries

/-- Powers of convergent complex formal series have the expected analytic sum. -/
theorem hasSum_complexSeries_pow (P : PowerSeries ℂ) (q a : ℂ) (k : ℕ)
    (hP : HasSum (fun n => P.coeff n * q ^ n) a) :
    HasSum (fun n => (P ^ k).coeff n * q ^ n) (a ^ k) := by
  induction k with
  | zero => simpa using QSeries.hasSum_complexPowerSeries_one q
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact QSeries.hasSum_complexPowerSeries_mul _ _ _ _ _ ih hP

/-- Evaluation of the formal homogeneous polynomial retains the degree before
specialization, so no pole order is lost through coefficient reduction. -/
theorem hasSum_cmPolynomialHomogenization (P : Polynomial CMFormalCoefficientRing)
    (hdeg : (P.map cmCoefficientComplexMap).natDegree = P.natDegree)
    {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n => cmCoefficientComplexMap
      ((cmPolynomialHomogenizationAtCusp P).coeff n) * q ^ n)
      (polynomialCuspHomogenization (P.map cmCoefficientComplexMap)
        levelSixEulerUnit q) := by
  let U := PowerSeries.map (Int.castRingHom ℂ) levelSixFormalEulerUnit
  have hU : HasSum (fun n => U.coeff n * q ^ n) (levelSixEulerUnit q) := by
    simpa [U, levelSixFormalEulerUnit_eq_rescaled] using
      hasSum_levelSixRescaledEulerUnit hq
  have hterm (j : ℕ) :
      HasSum (fun n => ((C (cmCoefficientComplexMap (P.coeff (P.natDegree - j))) *
        X ^ j * U ^ (P.natDegree - j)).coeff n) * q ^ n)
      (cmCoefficientComplexMap (P.coeff (P.natDegree - j)) * q ^ j *
        levelSixEulerUnit q ^ (P.natDegree - j)) := by
    have hc : HasSum (fun n =>
        (C (cmCoefficientComplexMap (P.coeff (P.natDegree - j))) :
          PowerSeries ℂ).coeff n * q ^ n)
        (cmCoefficientComplexMap (P.coeff (P.natDegree - j))) := by
      simpa +contextual [PowerSeries.coeff_C] using
        hasSum_ite_eq (0 : ℕ) (cmCoefficientComplexMap (P.coeff (P.natDegree - j)))
    have hx : HasSum (fun n => (X ^ j : PowerSeries ℂ).coeff n * q ^ n) (q ^ j) := by
      simpa +contextual [PowerSeries.coeff_X_pow] using hasSum_ite_eq j (q ^ j)
    exact QSeries.hasSum_complexPowerSeries_mul _ _ _ _ _
      (QSeries.hasSum_complexPowerSeries_mul _ _ _ _ _ hc hx)
      (hasSum_complexSeries_pow U q _ _ hU)
  have hs := hasSum_sum (s := Finset.range (P.natDegree + 1)) (fun j _ => hterm j)
  have he : polynomialCuspHomogenization (P.map cmCoefficientComplexMap)
      levelSixEulerUnit q =
      ∑ j ∈ Finset.range (P.natDegree + 1),
        cmCoefficientComplexMap (P.coeff (P.natDegree - j)) * q ^ j *
          levelSixEulerUnit q ^ (P.natDegree - j) := by
    rw [polynomialCuspHomogenization_sum, hdeg, ← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≤ P.natDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    simp only [Nat.add_sub_cancel, Polynomial.coeff_map, Nat.sub_sub_self hj']
    ring
  rw [he]
  have hm : PowerSeries.map cmCoefficientComplexMap
      (PowerSeries.map (algebraMap ℤ CMFormalCoefficientRing) levelSixFormalEulerUnit) = U := by
    ext n
    simp [U]
  convert hs using 1
  funext n
  rw [← PowerSeries.coeff_map]
  simp only [cmPolynomialHomogenizationAtCusp, map_sum, map_mul, map_pow,
    PowerSeries.map_C, PowerSeries.map_X, hm, map_sum, Finset.sum_mul]

/-- The formal discriminant unit has exactly the analytic Euler sum `E(q)^24`. -/
theorem hasSum_cmDiscriminantEulerUnit {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n => cmCoefficientComplexMap (cmDiscriminantEulerUnit.coeff n) * q ^ n)
      (etaEulerProduct q ^ 24) := by
  simp only [cmDiscriminantEulerUnit, PowerSeries.coeff_map]
  simpa using
    QSeries.hasSum_coefficientTerm_pow (etaEulerSeries 1) q _ 24
      (hasSum_etaEulerSeries_one hq)

/-- The integral CM clearing unit sums to the actual analytic clearing factor. -/
theorem hasSum_cmShimuraCuspClearingUnit (d : ℕ) [Fact (-(d : ℤ) < 0)]
    (hd : 0 < d) (hsq : Squarefree d) (hmod : d % 24 = 23)
    {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n => cmCoefficientComplexMap
      ((cmShimuraCuspClearingUnit d hd hsq hmod).coeff n) * q ^ n)
      (cmActualCuspClearingFactor (-(d : ℤ)) q) := by
  let M := integralCMClassPolynomials d hd hsq hmod
  have hA := hasSum_cmPolynomialHomogenization M.modelA
    (M.monicA.natDegree_map _) hq
  have hB := hasSum_cmPolynomialHomogenization M.modelB
    (M.monicB.natDegree_map _) hq
  rw [M.complexA] at hA
  rw [M.complexB] at hB
  have hAB := QSeries.hasSum_complexPowerSeries_mul
    (PowerSeries.map cmCoefficientComplexMap (cmPolynomialHomogenizationAtCusp M.modelA))
    (PowerSeries.map cmCoefficientComplexMap (cmPolynomialHomogenizationAtCusp M.modelB))
    q _ _ (by simpa using hA) (by simpa using hB)
  have hAB2 := hasSum_complexSeries_pow _ q _ 2 hAB
  have hD := hasSum_complexSeries_pow
    (PowerSeries.map cmCoefficientComplexMap cmDiscriminantEulerUnit) q _
    (8 * formClassNumber (-(d : ℤ))) (by simpa using hasSum_cmDiscriminantEulerUnit hq)
  simpa [cmShimuraCuspClearingUnit, cmActualCuspClearingFactor,
    cmAnalyticCuspClearingFactor, ← map_mul, ← map_pow, M] using
    QSeries.hasSum_complexPowerSeries_mul _ _ q _ _ hAB2 hD

/-- Multiplication by the actual CM clearing factor produces precisely the
integral cleared Fourier row, with the original Shimura coefficients. -/
theorem hasSum_cmPoleClearedShimuraCuspSeries (d : ℕ) [Fact (-(d : ℤ) < 0)]
    (hd : 0 < d) (hsq : Squarefree d) (hmod : d % 24 = 23)
    {q a : ℂ} (hq : ‖q‖ < 1)
    (hs : HasSum (fun n => ((integralPrincipalShimuraLambertSeries d).coeff n : ℂ) *
      q ^ n) a) :
    HasSum (fun n => cmCoefficientComplexMap
      ((cmPoleClearedShimuraCuspSeries d hd hsq hmod).coeff n) * q ^ n)
      (cmActualCuspClearingFactor (-(d : ℤ)) q * a) := by
  have hU := hasSum_cmShimuraCuspClearingUnit d hd hsq hmod hq
  have hJ : HasSum (fun n =>
      (PowerSeries.map cmCoefficientComplexMap (cmIntegralShimuraCuspSeries d)).coeff n *
        q ^ n) a := by simpa [cmIntegralShimuraCuspSeries] using hs
  simpa [cmPoleClearedShimuraCuspSeries_eq_unit_mul, ← map_mul] using
    QSeries.hasSum_complexPowerSeries_mul
      (PowerSeries.map cmCoefficientComplexMap (cmShimuraCuspClearingUnit d hd hsq hmod))
      _ q _ _ (by simpa using hU) hJ

/-- Translation by one is a strict period at the infinity cusp of level six. -/
theorem one_mem_levelSix_strictPeriods : (1 : ℝ) ∈
    ((CongruenceSubgroup.Gamma0 6).map
      (Matrix.SpecialLinearGroup.mapGL ℝ)).strictPeriods := by
  simp only [Subgroup.mem_strictPeriods_iff, Subgroup.mem_map]
  refine ⟨ModularGroup.T, ?_, ?_⟩
  · change ((0 : ℤ) : ZMod 6) = 0
    norm_num
  · ext i j
    change ((ModularGroup.T i j : ℤ) : ℝ) = _
    fin_cases i <;> fin_cases j <;> norm_num [ModularGroup.T]

/-- A Fourier row known only high in the cusp determines the full analytic
q-expansion of a level-six holomorphic modular form. -/
theorem levelSix_qExpansion_eq_of_highCusp {k : ℤ}
    (F : ModularForm ((CongruenceSubgroup.Gamma0 6).map
      (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (c : PowerSeries ℂ) (Y : ℝ)
    (hs : ∀ z : UpperHalfPlane, Y < z.im →
      HasSum (fun n => c.coeff n * Function.Periodic.qParam 1 z ^ n) (F z)) :
    c = UpperHalfPlane.qExpansion 1 (fun z => F z) := by
  have he := highCusp_fourierRow_unique (fun z => F z) (fun n => c.coeff n)
    (fun n => (UpperHalfPlane.qExpansion 1 (fun z => F z)).coeff n) Y hs
    (fun z _ => ModularForm.hasSum_qExpansion F one_pos one_mem_levelSix_strictPeriods z)
  ext n
  exact congrFun he n

/-- The exact integral CM row of an independently supplied holomorphic clearing.
Both hypotheses concern the same lift `J`; they need hold only above their
respective heights. The clearing uses the actual CM class polynomials, the
normalized discriminant, and the unchanged integral principal Shimura row.
No Fourier coefficient or global-lift existence is admitted here.
[rolenManuscript, Section 4, proof of prop:obstruction] -/
theorem cmPoleClearedShimuraCuspSeries_eq_qExpansion
    (d : ℕ) [Fact (-(d : ℤ) < 0)]
    (hd : 0 < d) (hsq : Squarefree d) (hmod : d % 24 = 23)
    (F : ModularForm ((CongruenceSubgroup.Gamma0 6).map
      (Matrix.SpecialLinearGroup.mapGL ℝ))
      ((96 * formClassNumber (-(d : ℤ)) + 4 : ℕ) : ℤ))
    (J : UpperHalfPlane → ℂ) (YJ YF : ℝ)
    (hJ : ∀ z : UpperHalfPlane, YJ < z.im →
      HasSum (fun n => ((integralPrincipalShimuraLambertSeries d).coeff n : ℂ) *
        Function.Periodic.qParam 1 z ^ n) (J z))
    (hF : ∀ z : UpperHalfPlane, YF < z.im →
      F z = ((cmClassPolynomialA (-(d : ℤ))).eval (levelSixEtaQuotient z) *
        (cmClassPolynomialB (-(d : ℤ))).eval (levelSixEtaQuotient z)) ^ 2 *
          ModularForm.discriminant z ^ (8 * formClassNumber (-(d : ℤ))) * J z) :
    PowerSeries.map cmCoefficientComplexMap
      (cmPoleClearedShimuraCuspSeries d hd hsq hmod) =
        UpperHalfPlane.qExpansion 1 (fun z => F z) := by
  apply levelSix_qExpansion_eq_of_highCusp F _ (max YJ YF)
  intro z hz
  have hJz := hJ z (lt_of_le_of_lt (le_max_left YJ YF) hz)
  have hs := hasSum_cmPoleClearedShimuraCuspSeries d hd hsq hmod
    (Function.Periodic.norm_qParam_lt_one one_pos z.im_pos) hJz
  have hD : -(d : ℤ) % 24 = 1 := by omega
  rw [cmActualCuspClearingFactor_qParam _ hD,
    ← hF z (lt_of_le_of_lt (le_max_right YJ YF) hz)] at hs
  simpa only [PowerSeries.coeff_map] using hs

end SptClassification
