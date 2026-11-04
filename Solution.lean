module

public import SptClassification.Classification.ConditionalClassification
import all SptClassification.Classification.ConditionalClassification
public import SptClassification.Classification.ConditionalExclusion
import all SptClassification.Classification.ConditionalExclusion
public import SptClassification.ModularForms.ConditionalPropagationProof
import all SptClassification.ModularForms.ConditionalPropagationProof
public import SptClassification.ModularForms.PrimeLocalNormalizedProduct
import all SptClassification.ModularForms.PrimeLocalNormalizedProduct
public import Lean

namespace PalomarPreparation
open Lean Meta Elab Tactic

/-- Cache proof expansions; only the two named literature lemmas may be replaced. -/
meta structure RewriteState where
  expanded : NameMap Expr := {}
  needsExpansion : NameMap Bool := {}

meta partial def replaceLiterature (minus plus : Expr) (e : Expr) :
    StateT RewriteState MetaM Expr := do
  match e with
  | .const name levels =>
    if name == `SptClassification.normalizedEisenstein_minus_reduces then return minus
    if name == `SptClassification.normalizedEisenstein_plus_reduces then return plus
    let dirty ← match (← get).needsExpansion.find? name with
      | some b => pure b
      | none => do
        let b := (← collectAxioms name).contains `sorryAx
        modify fun s => { s with needsExpansion := s.needsExpansion.insert name b }
        pure b
    if !dirty then return e
    let info ← getConstInfo name
    let value ← match (← get).expanded.find? name with
      | some v => pure v
      | none => do
        let some v := info.value? true
          | throwError "Cannot replace an additional unproved dependency: {name}"
        let v ← replaceLiterature minus plus v
        modify fun s => { s with expanded := s.expanded.insert name v }
        pure v
    return value.instantiateLevelParams info.levelParams levels
  | .app f a => return e.updateApp! (← replaceLiterature minus plus f) (← replaceLiterature minus plus a)
  | .lam _ t b _ => return e.updateLambdaE! (← replaceLiterature minus plus t) (← replaceLiterature minus plus b)
  | .forallE _ t b _ => return e.updateForallE! (← replaceLiterature minus plus t) (← replaceLiterature minus plus b)
  | .letE _ t v b nondep => return e.updateLet! (← replaceLiterature minus plus t) (← replaceLiterature minus plus v) (← replaceLiterature minus plus b) nondep
  | .mdata _ b => return e.updateMData! (← replaceLiterature minus plus b)
  | .proj _ _ b => return e.updateProj! (← replaceLiterature minus plus b)
  | _ => return e

/-- Expand only proof dependencies containing the two literature admissions,
then substitute the explicit hypotheses. Lean checks the resulting proof term. -/
elab "replace_literature_admissions " source:term " using " lo:term "," hi:term : tactic =>
  withMainContext do
    let goal ← getMainGoal
    let expected ← goal.getType
    let original ← elabTerm source (some expected)
    let minusType := (← getConstInfo `SptClassification.normalizedEisenstein_minus_reduces).type
    let plusType := (← getConstInfo `SptClassification.normalizedEisenstein_plus_reduces).type
    let minus ← elabTerm lo (some minusType)
    let plus ← elabTerm hi (some plusType)
    let proof ← (replaceLiterature (← instantiateMVars minus) (← instantiateMVars plus)
      (← instantiateMVars original)).run' {}
    unless ← isDefEq (← inferType proof) expected do
      throwError "The conditional proof does not prove the requested statement"
    goal.assign proof
    replaceMainGoal []
end PalomarPreparation

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
  replace_literature_admissions
    (_root_.SptClassification.conditional_noncanonical_exclusion tv ct progression geometry p b hp hp5 hb hspt)
    using eisenstein.minus, eisenstein.plus

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
  replace_literature_admissions
    (_root_.SptClassification.conditional_simple_congruence_classification tv ct progression geometry canonical p b hp hb)
    using eisenstein.minus, eisenstein.plus

end SptClassification.Palomar
