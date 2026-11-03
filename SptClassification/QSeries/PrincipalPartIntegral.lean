/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.PrincipalPartJ
public import SptClassification.Partitions.RestrictedSeries
import Mathlib.Tactic.Linarith

/-!
# Integral principal-part rows from the partition generating series

The ordinary partition series is `q^(1/24)η⁻¹`. Its inverse is the ordinary
core of `η`, and the integral series `E₄³ P²⁴` is the ordinary core of `qj`.
Specializing the row elimination to these series gives integral Laurent
coefficient sequences with exactly the pole required in the manuscript
[rolenManuscript, §3]. Analytic identification and modularity are separate
proof obligations.
-/

public section

namespace SptClassification.QSeries

open PowerSeries

/-- The ordinary generating series of the actual partition numbers. -/
noncomputable def partitionSeries : PowerSeries ℤ := restrictedPartitionSeries 1

@[simp] theorem partitionSeries_coeff (n : ℕ) :
    partitionSeries.coeff n = (partitionCount n : ℤ) := by
  exact coeff_restrictedPartitionSeries_one n

@[simp] theorem partitionSeries_coeff_zero : partitionSeries.coeff 0 = 1 := by
  exact coeff_restrictedPartitionSeries_zero 1

/-- The integral eta product core, obtained by inverting the partition series. -/
noncomputable def etaIntegralCore : PowerSeries ℤ :=
  etaCoreFromPartition partitionSeries

/-- The integral eta core is the inverse of the actual partition series. -/
theorem etaIntegralCore_eq_invOfUnit :
    etaIntegralCore = partitionSeries.invOfUnit 1 := by
  rw [etaIntegralCore, etaCoreFromPartition_eq_invOfUnit]

/-- The integral ordinary core of `qj`. -/
noncomputable def modularJIntegralCore : PowerSeries ℤ :=
  modularJCore partitionSeries

/-- The factors of the integral core of `qj`. -/
theorem modularJIntegralCore_eq :
    modularJIntegralCore = eisensteinFourSeries ^ 3 * partitionSeries ^ 24 := by
  unfold modularJIntegralCore
  exact modularJCore_eq partitionSeries

theorem partitionSeries_mul_etaIntegralCore :
    partitionSeries * etaIntegralCore = 1 :=
  partition_mul_etaCoreFromPartition partitionSeries partitionSeries_coeff_zero

@[simp] theorem etaIntegralCore_coeff_zero : etaIntegralCore.coeff 0 = 1 :=
  etaCoreFromPartition_coeff_zero partitionSeries partitionSeries_coeff_zero

@[simp] theorem modularJIntegralCore_coeff_zero :
    modularJIntegralCore.coeff 0 = 1 :=
  modularJCore_coeff_zero partitionSeries partitionSeries_coeff_zero

/-- The row-reduced integral coefficients of `η j^n`. -/
noncomputable def integralEtaPrincipalBasis (n : ℕ) : ℤ → ℤ :=
  etaPrincipalBasis etaIntegralCore modularJIntegralCore n

/-- The row-reduced integral coefficients of `-η(Θj)j^n`. -/
noncomputable def integralEtaThetaPrincipalBasis (n : ℕ) : ℤ → ℤ :=
  etaThetaPrincipalBasis etaIntegralCore modularJIntegralCore n

theorem integralEtaThetaPrincipalBasis_eq (n : ℕ) :
    integralEtaThetaPrincipalBasis n =
      principalPartElimination (etaThetaJRow etaIntegralCore modularJIntegralCore) n := by
  rw [integralEtaThetaPrincipalBasis, etaThetaPrincipalBasis_eq]

theorem integralEtaPrincipalBasis_pole (n k : ℕ) :
    integralEtaPrincipalBasis n (k : ℤ) = if k = n then 1 else 0 :=
  etaPrincipalBasis_pole etaIntegralCore modularJIntegralCore
    etaIntegralCore_coeff_zero modularJIntegralCore_coeff_zero n k

theorem integralEtaThetaPrincipalBasis_pole (n k : ℕ) :
    integralEtaThetaPrincipalBasis n (k : ℤ) = if k = n then 1 else 0 :=
  etaThetaPrincipalBasis_pole etaIntegralCore modularJIntegralCore
    etaIntegralCore_coeff_zero modularJIntegralCore_coeff_zero n k

/-- For `d ≡ 23 (mod 24)`, the eta row indexed by `n` has pole `q^(-d/24)`. -/
def principalIndex (d : ℕ) : ℕ := (d + 1) / 24

theorem principalIndex_mul (d : ℕ) (hd : d % 24 = 23) :
    24 * principalIndex d = d + 1 := by
  unfold principalIndex
  omega

theorem principalIndex_pos (d : ℕ) (hd : d % 24 = 23) :
    0 < principalIndex d := by
  have := principalIndex_mul d hd
  omega

/-- The integral `H_d` coefficient sequence before identifying its prescribed
constant term with the coefficient of the actual harmonic Maass form. -/
noncomputable def integralHPrincipalPart (d : ℕ) (a : ℤ) : ℤ → ℤ :=
  etaPrincipalWithConstant etaIntegralCore modularJIntegralCore
    (principalIndex d) (-a)

theorem integralHPrincipalPart_eq (d : ℕ) (a r : ℤ) :
    integralHPrincipalPart d a r =
      principalPartElimination (etaJRow etaIntegralCore modularJIntegralCore)
        (principalIndex d) r - a * etaJRow etaIntegralCore modularJIntegralCore 0 r := by
  rw [integralHPrincipalPart, etaPrincipalWithConstant_eq, etaPrincipalBasis_eq]
  ring

/-- The integral `K_d` coefficient sequence; the derivative rows start one
index later than the eta rows. -/
noncomputable def integralKPrincipalPart (d : ℕ) : ℤ → ℤ :=
  integralEtaThetaPrincipalBasis (principalIndex d - 1)

theorem integralKPrincipalPart_eq (d : ℕ) :
    integralKPrincipalPart d =
      principalPartElimination (etaThetaJRow etaIntegralCore modularJIntegralCore)
        (principalIndex d - 1) := by
  rw [integralKPrincipalPart, integralEtaThetaPrincipalBasis_eq]

theorem integralHPrincipalPart_constant (d : ℕ) (hd : d % 24 = 23)
    (a : ℤ) : integralHPrincipalPart d a 0 = -a :=
  etaPrincipalWithConstant_zero etaIntegralCore modularJIntegralCore
    etaIntegralCore_coeff_zero modularJIntegralCore_coeff_zero
    (principalIndex d) (principalIndex_pos d hd) (-a)

theorem integralHPrincipalPart_pole (d : ℕ) (a : ℤ)
    (k : ℕ) (hk : 0 < k) :
    integralHPrincipalPart d a (k : ℤ) =
      if k = principalIndex d then 1 else 0 :=
  etaPrincipalWithConstant_pole etaIntegralCore modularJIntegralCore
    etaIntegralCore_coeff_zero modularJIntegralCore_coeff_zero
    (principalIndex d) (-a) k hk

theorem integralKPrincipalPart_pole (d k : ℕ) :
    integralKPrincipalPart d (k : ℤ) =
      if k = principalIndex d - 1 then 1 else 0 :=
  integralEtaThetaPrincipalBasis_pole (principalIndex d - 1) k

/-- Generic integral row elimination together with the actual partition-series
units and the distinct eta/derivative pole shifts [rolenManuscript, §3].
The row indices refer to exponents `1/24-k` and `1/24-(k+1)` respectively. -/
theorem integralPrincipalPartRows_spec :
    (∀ (U J : PowerSeries ℤ) (n : ℕ) (r : ℤ),
      etaPrincipalBasis U J n r =
        etaJRow U J n r -
          Finset.sum (Finset.univ : Finset (Finset.range n))
            (fun k => etaJRow U J n (k : ℤ) * etaPrincipalBasis U J k r) ∧
      etaThetaPrincipalBasis U J n r =
        etaThetaJRow U J n r -
          Finset.sum (Finset.univ : Finset (Finset.range n))
            (fun k => etaThetaJRow U J n (k : ℤ) * etaThetaPrincipalBasis U J k r)) ∧
    (∀ (U J : PowerSeries ℤ) (hU : U.coeff 0 = 1)
      (hJ : J.coeff 0 = 1) (n k : ℕ),
      etaPrincipalBasis U J n (k : ℤ) = (if k = n then 1 else 0) ∧
      etaThetaPrincipalBasis U J n (k : ℤ) = (if k = n then 1 else 0)) ∧
    etaIntegralCore = etaCoreFromPartition partitionSeries ∧
    modularJIntegralCore = eisensteinFourSeries ^ 3 * partitionSeries ^ 24 ∧
    partitionSeries.coeff 0 = 1 ∧
    etaIntegralCore.coeff 0 = 1 ∧
    modularJIntegralCore.coeff 0 = 1 ∧
    partitionSeries * etaIntegralCore = 1 ∧
    (∀ (d : ℕ) (hd : d % 24 = 23) (a : ℤ),
      integralHPrincipalPart d a 0 = -a ∧
      (∀ (k : ℕ), 0 < k →
        integralHPrincipalPart d a (k : ℤ) =
          if k = principalIndex d then 1 else 0) ∧
      24 * principalIndex d = d + 1) ∧
    (∀ (d k : ℕ), integralKPrincipalPart d (k : ℤ) =
      if k = principalIndex d - 1 then 1 else 0) ∧
    (∀ (d : ℕ), d % 24 = 23 →
      24 * (principalIndex d - 1 + 1) = d + 1) := by
  refine ⟨?_, ?_, rfl, modularJCore_eq partitionSeries, partitionSeries_coeff_zero,
    etaIntegralCore_coeff_zero, modularJIntegralCore_coeff_zero,
    partitionSeries_mul_etaIntegralCore, ?_, ?_, ?_⟩
  · intro U J n r
    exact ⟨etaPrincipalBasis_eq_row_sub U J n r,
      etaThetaPrincipalBasis_eq_row_sub U J n r⟩
  · intro U J hU hJ n k
    exact ⟨etaPrincipalBasis_pole U J hU hJ n k,
      etaThetaPrincipalBasis_pole U J hU hJ n k⟩
  · intro d hd a
    exact ⟨integralHPrincipalPart_constant d hd a,
      fun k hk => integralHPrincipalPart_pole d a k hk,
      principalIndex_mul d hd⟩
  · exact integralKPrincipalPart_pole
  · intro d hd
    have hpos := principalIndex_pos d hd
    have hmul := principalIndex_mul d hd
    omega

end SptClassification.QSeries
