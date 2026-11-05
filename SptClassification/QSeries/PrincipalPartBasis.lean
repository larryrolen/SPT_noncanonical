/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.PrincipalPartRows
public import Mathlib.Algebra.Group.Subgroup.Lattice

/-!
# The two integral principal-part row reductions

For unit series `U` and `J`, the eta rows and derivative rows both have a
unitriangular pole matrix. Their row reductions therefore give an integral
coefficient sequence with precisely one pole. The analytic identification
`U=q^(-1/24)η` and `J=qj`, and the prescribed coefficient `-a(d)`, are
separate prerequisites for the manuscript's forms `H_d` and `K_d`.
-/

@[expose] public section

namespace SptClassification.QSeries

open PowerSeries

/-- Integral elimination of the poles of the rows `η j^n`. -/
noncomputable def etaPrincipalBasis (U J : PowerSeries ℤ) (n : ℕ) : ℤ → ℤ :=
  principalPartElimination (etaJRow U J) n

theorem etaPrincipalBasis_eq (U J : PowerSeries ℤ) (n : ℕ) :
    etaPrincipalBasis U J n = principalPartElimination (etaJRow U J) n := (rfl)

/-- Integral elimination of the poles of the rows `-η (Θ j) j^n`. -/
noncomputable def etaThetaPrincipalBasis (U J : PowerSeries ℤ) (n : ℕ) : ℤ → ℤ :=
  principalPartElimination (etaThetaJRow U J) n

theorem etaThetaPrincipalBasis_eq (U J : PowerSeries ℤ) (n : ℕ) :
    etaThetaPrincipalBasis U J n = principalPartElimination (etaThetaJRow U J) n := (rfl)

/-- The eta row reduction satisfies its integral elimination recurrence. -/
theorem etaPrincipalBasis_eq_row_sub (U J : PowerSeries ℤ) (n : ℕ) (r : ℤ) :
    etaPrincipalBasis U J n r =
      etaJRow U J n r -
        Finset.sum (Finset.univ : Finset (Finset.range n))
          (fun k => etaJRow U J n (k : ℤ) * etaPrincipalBasis U J k r) := by
  simpa only [etaPrincipalBasis] using principalPartElimination_eq (etaJRow U J) n r

/-- The derivative row reduction satisfies its integral elimination recurrence. -/
theorem etaThetaPrincipalBasis_eq_row_sub (U J : PowerSeries ℤ) (n : ℕ) (r : ℤ) :
    etaThetaPrincipalBasis U J n r =
      etaThetaJRow U J n r -
        Finset.sum (Finset.univ : Finset (Finset.range n))
          (fun k => etaThetaJRow U J n (k : ℤ) * etaThetaPrincipalBasis U J k r) := by
  simpa only [etaThetaPrincipalBasis] using
    principalPartElimination_eq (etaThetaJRow U J) n r

theorem etaPrincipalBasis_pole (U J : PowerSeries ℤ)
    (hU : U.coeff 0 = 1) (hJ : J.coeff 0 = 1) (n k : ℕ) :
    etaPrincipalBasis U J n (k : ℤ) = if k = n then 1 else 0 :=
  principalPartElimination_pole (etaJRow U J)
    (etaJRow_leading U J hU hJ) (etaJRow_above U J) n k

theorem etaThetaPrincipalBasis_pole (U J : PowerSeries ℤ)
    (hU : U.coeff 0 = 1) (hJ : J.coeff 0 = 1) (n k : ℕ) :
    etaThetaPrincipalBasis U J n (k : ℤ) = if k = n then 1 else 0 :=
  principalPartElimination_pole (etaThetaJRow U J)
    (etaThetaJRow_leading U J hU hJ) (etaThetaJRow_above U J) n k

/-- The eta basis coefficient sequence is an integral polynomial combination
of the original `η j^i` rows. -/
theorem etaPrincipalBasis_mem_span (U J : PowerSeries ℤ) (n : ℕ) :
    etaPrincipalBasis U J n ∈
      AddSubgroup.closure (Set.range (etaJRow U J)) := by
  exact principalPartElimination_mem (etaJRow U J) _
    (fun i => AddSubgroup.subset_closure (Set.mem_range_self i)) n

/-- The derivative basis is an integral polynomial combination of the
`-η(Θj)j^i` rows. -/
theorem etaThetaPrincipalBasis_mem_span (U J : PowerSeries ℤ) (n : ℕ) :
    etaThetaPrincipalBasis U J n ∈
      AddSubgroup.closure (Set.range (etaThetaJRow U J)) := by
  exact principalPartElimination_mem (etaThetaJRow U J) _
    (fun i => AddSubgroup.subset_closure (Set.mem_range_self i)) n

/-- Prescribe the first nonpolar eta coefficient after eliminating all poles. -/
noncomputable def etaPrincipalWithConstant (U J : PowerSeries ℤ)
    (n : ℕ) (c : ℤ) : ℤ → ℤ :=
  fun k => etaPrincipalBasis U J n k + c * etaJRow U J 0 k

theorem etaPrincipalWithConstant_eq (U J : PowerSeries ℤ)
    (n : ℕ) (c k : ℤ) :
    etaPrincipalWithConstant U J n c k =
      etaPrincipalBasis U J n k + c * etaJRow U J 0 k := (rfl)

/-- Prescribing the first nonpolar coefficient still gives an integral
polynomial combination of eta rows. -/
theorem etaPrincipalWithConstant_mem_span (U J : PowerSeries ℤ)
    (n : ℕ) (c : ℤ) :
    etaPrincipalWithConstant U J n c ∈
      AddSubgroup.closure (Set.range (etaJRow U J)) := by
  have hrow : etaJRow U J 0 ∈
      AddSubgroup.closure (Set.range (etaJRow U J)) :=
    AddSubgroup.subset_closure (Set.mem_range_self 0)
  have heq : etaPrincipalWithConstant U J n c =
      etaPrincipalBasis U J n + c • etaJRow U J 0 := by
    funext k
    simp [etaPrincipalWithConstant, Pi.add_apply]
  rw [heq]
  exact (AddSubgroup.closure (Set.range (etaJRow U J))).add_mem
    (etaPrincipalBasis_mem_span U J n)
    ((AddSubgroup.closure (Set.range (etaJRow U J))).zsmul_mem hrow c)

theorem etaPrincipalWithConstant_zero (U J : PowerSeries ℤ)
    (hU : U.coeff 0 = 1) (hJ : J.coeff 0 = 1)
    (n : ℕ) (hn : 0 < n) (c : ℤ) :
    etaPrincipalWithConstant U J n c 0 = c := by
  have hzero : etaPrincipalBasis U J n 0 = 0 := by
    simpa [(Nat.ne_of_gt hn).symm] using etaPrincipalBasis_pole U J hU hJ n 0
  have heta : etaJRow U J 0 0 = 1 := etaJRow_leading U J hU hJ 0
  simp [etaPrincipalWithConstant, hzero, heta]

theorem etaPrincipalWithConstant_pole (U J : PowerSeries ℤ)
    (hU : U.coeff 0 = 1) (hJ : J.coeff 0 = 1)
    (n : ℕ) (c : ℤ) (k : ℕ) (hk : 0 < k) :
    etaPrincipalWithConstant U J n c (k : ℤ) = if k = n then 1 else 0 := by
  simp [etaPrincipalWithConstant, etaPrincipalBasis_pole U J hU hJ n k,
    etaJRow_above U J 0 k hk]

end SptClassification.QSeries
