/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.CharacterTwelve
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.Basic.Complex.Basic

/-!
# The conductor-twelve Nebentypus

The residue-table normalization of [ahlgrenAndersen2016, §3] gives a
Dirichlet character and its pullback to any compatible congruence subgroup.
Changing level extends by zero at the new nonunits; on the lower-right
entries of subgroup elements it retains the original integer character.
-/

public section

namespace SptClassification

/-- The integer-valued Dirichlet character defined by the residue table. -/
def characterTwelveDirichletInt : DirichletCharacter ℤ 12 where
  toFun := characterTwelveResidue
  map_one' := by decide +kernel
  map_mul' := characterTwelveResidue_mul
  map_nonunit' := by
    intro a ha
    have h : ¬a.val.Coprime 12 := by
      simpa only [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val] using ha
    fin_cases a <;> revert h <;> decide +kernel

/-- The complex-valued character used in modular transformation formulas. -/
def characterTwelveDirichlet : DirichletCharacter ℂ 12 :=
  characterTwelveDirichletInt.ringHomComp (Int.castRingHom ℂ)

@[simp] theorem characterTwelveDirichlet_apply (a : ℤ) :
    characterTwelveDirichlet (a : ZMod 12) = (characterTwelve a : ℂ) := by
  rw [characterTwelve_eq_residue]
  rfl

theorem characterTwelveDirichlet_isQuadratic :
    characterTwelveDirichlet.IsQuadratic := by
  apply MulChar.IsQuadratic.comp
  intro a
  fin_cases a <;> decide +kernel

/-- Extension of the character to a level divisible by twelve. -/
noncomputable def characterTwelveAtLevel {N : ℕ} (hN : 12 ∣ N) :
    DirichletCharacter ℂ N :=
  characterTwelveDirichlet.changeLevel hN

/-- The associated multiplicative character on `Γ₀(N)`. -/
noncomputable def characterTwelveGamma0 {N : ℕ} (hN : 12 ∣ N) :
    CongruenceSubgroup.Gamma0 N →* ℂ :=
  (characterTwelveAtLevel hN).toMonoidHom.comp (CongruenceSubgroup.Gamma0Map N)

theorem characterTwelveGamma0_eq_nebentypus {N : ℕ} (hN : 12 ∣ N)
    (γ : CongruenceSubgroup.Gamma0 N) :
    characterTwelveGamma0 hN γ = characterTwelveAtLevel hN
      ((((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ)
        1 1 : ℤ) : ZMod N) := (rfl)

theorem characterTwelveGamma0_apply {N : ℕ} (hN : 12 ∣ N)
    (γ : CongruenceSubgroup.Gamma0 N) :
    characterTwelveGamma0 hN γ =
      (characterTwelve (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
        Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) := by
  rw [characterTwelveGamma0_eq_nebentypus]
  change characterTwelveDirichlet.changeLevel hN _ = _
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd']
  · exact characterTwelveDirichlet_apply _
  · apply isCoprime_comm.mp
    apply (ZMod.coe_int_isUnit_iff_isCoprime _ _).mp
    exact (Group.isUnit γ).map (CongruenceSubgroup.Gamma0Map N)

theorem characterTwelveGamma0_sq {N : ℕ} (hN : 12 ∣ N)
    (γ : CongruenceSubgroup.Gamma0 N) :
    characterTwelveGamma0 hN γ ^ 2 = 1 := by
  have h := congrArg (fun χ : DirichletCharacter ℂ N =>
    χ (CongruenceSubgroup.Gamma0Map N γ))
    (show characterTwelveAtLevel hN ^ 2 = 1 by
      unfold characterTwelveAtLevel
      rw [← map_pow, characterTwelveDirichlet_isQuadratic.sq_eq_one, map_one])
  rw [MulChar.pow_apply' _ two_ne_zero, MulChar.one_apply
    ((Group.isUnit γ).map (CongruenceSubgroup.Gamma0Map N))] at h
  exact h

end SptClassification
