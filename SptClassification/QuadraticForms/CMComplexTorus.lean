/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.CMReductionAction
public import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.Ring

/-!
# The actual complex torus of an oriented CM form

The torus is the additive quotient of `ℂ` by `ℤ + ℤτ`, with `τ` the
form's upper-half-plane root. Multiplication by the CM generator descends
to this quotient by the explicit period calculation of
[rolen2026canonical, Proposition 5.3]. Algebraic uniformization and
specialization to an elliptic curve in positive characteristic are separate.
-/

public section

namespace SptClassification.LevelSixForm

variable {D : ℤ} {r : ZMod 12} [Fact (D < 0)] (Q : LevelSixForm D r)

/-- The actual periods of the CM point, in the ordered basis `1, τ`. -/
noncomputable def periodMap : (ℤ × ℤ) →+ ℂ where
  toFun v := (v.1 : ℂ) + (v.2 : ℂ) * Q.cmPoint
  map_zero' := by simp
  map_add' v w := by simp only [Prod.fst_add, Prod.snd_add, Int.cast_add]; ring

theorem periodMap_apply (v : ℤ × ℤ) :
    Q.periodMap v = (v.1 : ℂ) + (v.2 : ℂ) * Q.cmPoint := (rfl)

/-- The rank-two period subgroup, as an actual subgroup of the complex numbers. -/
noncomputable def periodLattice : AddSubgroup ℂ := Q.periodMap.range

theorem mem_periodLattice (z : ℂ) : z ∈ Q.periodLattice ↔
    ∃ m n : ℤ, (m : ℂ) + (n : ℂ) * Q.cmPoint = z := by
  change (∃ v : ℤ × ℤ, Q.periodMap v = z) ↔ _
  simp only [periodMap_apply, Prod.exists]

/-- The complex torus attached to the given form, before algebraic uniformization. -/
abbrev ComplexTorus := ℂ ⧸ Q.periodLattice

/-- Passage from a complex coordinate to its class modulo the periods. -/
noncomputable def torusPoint : ℂ →+ Q.ComplexTorus :=
  QuotientAddGroup.mk' Q.periodLattice

theorem torusPoint_apply (z : ℂ) :
    Q.torusPoint z = QuotientAddGroup.mk' Q.periodLattice z := (rfl)

theorem torusPoint_eq_zero (z : ℂ) : Q.torusPoint z = 0 ↔ z ∈ Q.periodLattice := by
  exact QuotientAddGroup.eq_zero_iff z

/-- Multiplication by the selected complex CM generator is additive. -/
noncomputable def complexGeneratorMap (D : ℤ) : ℂ →+ ℂ where
  toFun z := cmGenerator D * z
  map_zero' := mul_zero _
  map_add' := mul_add _

theorem complexGeneratorMap_apply (z : ℂ) :
    complexGeneratorMap D z = cmGenerator D * z := (rfl)

theorem complexGeneratorMap_preserves (hodd : Q.b % 2 = 1)
    (z : ℂ) (hz : z ∈ Q.periodLattice) :
    complexGeneratorMap D z ∈ Q.periodLattice := by
  obtain ⟨m, n, rfl⟩ := (Q.mem_periodLattice z).mp hz
  apply (Q.mem_periodLattice _).mpr
  refine ⟨((Q.b + 1) / 2) * m - Q.c * n,
    Q.a * m + (((Q.b + 1) / 2) - Q.b) * n, ?_⟩
  exact (Q.cmGenerator_mul_periods hodd m n).symm

/-- The actual CM generator endomorphism on the quotient by the period lattice. -/
noncomputable def torusGenerator (hodd : Q.b % 2 = 1) :
    Q.ComplexTorus →+ Q.ComplexTorus :=
  QuotientAddGroup.map Q.periodLattice Q.periodLattice (complexGeneratorMap D)
    (fun z hz => Q.complexGeneratorMap_preserves hodd z hz)

theorem torusGenerator_point (hodd : Q.b % 2 = 1) (z : ℂ) :
    Q.torusGenerator hodd (Q.torusPoint z) =
      Q.torusPoint (cmGenerator D * z) := (rfl)

theorem torusPoint_surjective : Function.Surjective Q.torusPoint :=
  QuotientAddGroup.mk'_surjective Q.periodLattice

/-- The trace-one quadratic relation holds on the actual complex torus. -/
theorem torusGenerator_quadratic (hodd : Q.b % 2 = 1) (n : ℕ)
    (hn : 4 * (n : ℤ) = 1 - D) (x : Q.ComplexTorus) :
    Q.torusGenerator hodd (Q.torusGenerator hodd x) -
      Q.torusGenerator hodd x + n • x = 0 := by
  obtain ⟨z, rfl⟩ := Q.torusPoint_surjective x
  rw [Q.torusGenerator_point, Q.torusGenerator_point]
  rw [← map_nsmul, ← map_sub, ← map_add]
  have hzero : cmGenerator D * (cmGenerator D * z) -
      cmGenerator D * z + n • z = 0 := by
    rw [nsmul_eq_mul]
    calc
      _ = (cmGenerator D * cmGenerator D - cmGenerator D + (n : ℂ)) * z := by ring
      _ = 0 := by rw [cmGenerator_quadratic D n hn, zero_mul]
  rw [hzero, map_zero]

/-- A real rational point `m/6` lies in the period lattice exactly when its
numerator is divisible by six; positivity of `im τ` excludes the second period. -/
theorem int_div_six_mem_periodLattice (m : ℤ) :
    (m : ℂ) / 6 ∈ Q.periodLattice ↔ 6 ∣ m := by
  rw [Q.mem_periodLattice]
  constructor
  · rintro ⟨k, l, h⟩
    have him : (l : ℝ) * (Q.cmPoint : ℂ).im = 0 := by
      simpa using congrArg Complex.im h
    have hlR : (l : ℝ) = 0 := (mul_eq_zero.mp him).resolve_right
      (ne_of_gt Q.cmPoint.im_pos)
    have hl : l = 0 := by exact_mod_cast hlR
    subst l
    have hk : (k : ℂ) = (m : ℂ) / 6 := by simpa using h
    have hmul : (m : ℂ) = 6 * (k : ℂ) := by
      rw [eq_div_iff (by norm_num : (6 : ℂ) ≠ 0)] at hk
      simpa only [mul_comm] using hk.symm
    refine ⟨k, ?_⟩
    exact_mod_cast hmul
  · rintro ⟨k, rfl⟩
    refine ⟨k, 0, ?_⟩
    push_cast
    ring

/-- The distinguished point whose cyclic subgroup is the level-six structure. -/
noncomputable def torusSixPoint : Q.ComplexTorus := Q.torusPoint (1 / 6)

theorem torusSixPoint_eq : Q.torusSixPoint = Q.torusPoint (1 / 6) := (rfl)

/-- The distinguished point has exact order six, stated without a choice of
an isomorphism of its cyclic subgroup with `ZMod 6`. -/
theorem torusSixPoint_nsmul_eq_zero (n : ℕ) :
    n • Q.torusSixPoint = 0 ↔ 6 ∣ n := by
  rw [Q.torusSixPoint_eq, ← map_nsmul]
  have heq : n • (1 / 6 : ℂ) = (n : ℂ) / 6 := by rw [nsmul_eq_mul]; ring
  rw [heq, Q.torusPoint_eq_zero]
  have hdiv : (6 : ℤ) ∣ (n : ℤ) ↔ (6 : ℕ) ∣ n := by
    exact_mod_cast (Iff.rfl : (6 : ℕ) ∣ n ↔ (6 : ℕ) ∣ n)
  simpa only [Int.cast_natCast] using
    (Q.int_div_six_mem_periodLattice (n : ℤ)).trans hdiv

/-- The cyclic subgroup of the actual complex torus generated by `1/6`. -/
noncomputable def torusLevelSix : AddSubgroup Q.ComplexTorus :=
  AddSubgroup.zmultiples Q.torusSixPoint

/-- The CM generator acts on the distinguished point by the integral scalar
whose residue modulo six is the orientation scalar. -/
theorem torusGenerator_sixPoint (hodd : Q.b % 2 = 1) :
    Q.torusGenerator hodd Q.torusSixPoint =
      ((Q.b + 1) / 2 : ℤ) • Q.torusSixPoint := by
  rw [Q.torusSixPoint_eq, Q.torusGenerator_point, ← map_zsmul]
  obtain ⟨k, hk⟩ := Q.cmGenerator_on_six_torsion hodd
  have hperiod : (k : ℂ) * Q.cmPoint ∈ Q.periodLattice :=
    (Q.mem_periodLattice _).mpr ⟨0, k, by simp⟩
  have hzero := (Q.torusPoint_eq_zero _).mpr hperiod
  have hmul : cmGenerator D * (1 / 6) = cmGenerator D / 6 := by ring
  rw [hmul, hk, map_add, hzero, zero_add]
  congr 1
  rw [zsmul_eq_mul]
  ring

/-- The actual CM action preserves the distinguished level-six subgroup. -/
theorem torusGenerator_preserves_levelSix (hodd : Q.b % 2 = 1)
    (x : Q.ComplexTorus) (hx : x ∈ Q.torusLevelSix) :
    Q.torusGenerator hodd x ∈ Q.torusLevelSix := by
  obtain ⟨m, rfl⟩ := hx
  change ∃ k : ℤ, k • Q.torusSixPoint = _
  refine ⟨m * ((Q.b + 1) / 2), ?_⟩
  rw [map_zsmul, Q.torusGenerator_sixPoint, mul_smul]

end SptClassification.LevelSixForm
