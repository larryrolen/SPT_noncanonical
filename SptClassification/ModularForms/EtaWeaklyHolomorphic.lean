/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.EtaAutomorphy
public import Mathlib.Analysis.Meromorphic.Basic

/-!
# Weakly holomorphic forms with the Dedekind eta factor

`EtaWeaklyHolomorphicForm k` has weight `k + 1/2` on the full modular group,
with eta's actual automorphy factor. The period-24 cusp coordinate trivializes
the eta monodromy. Holomorphy on the upper half-plane and a meromorphic cusp
germ are required independently of the transformation law
[apostol1990, Chapter 3], [rolenManuscript, §3].
-/

public section

namespace SptClassification

open UpperHalfPlane
open scoped MatrixGroups Manifold

/-- A level-one weakly holomorphic form of weight `k + 1/2` with eta's multiplier. -/
structure EtaWeaklyHolomorphicForm (k : ℕ) where
  /-- The actual analytic function on the upper half-plane. -/
  toFun : UpperHalfPlane → ℂ
  /-- Holomorphy on the upper half-plane. -/
  holomorphic' : MDiff toFun
  /-- Equivariance under the full integral modular group. -/
  map_action' : ∀ (γ : GL (Fin 2) ℝ), γ ∈ 𝒮ℒ → ∀ τ : UpperHalfPlane,
    toFun (γ • τ) = etaAutomorphyFactor γ τ * denom γ τ ^ k * toFun τ
  /-- Meromorphy at the unique level-one cusp, in the period-24 coordinate. -/
  meromorphic_cusp' : ∃ G : ℂ → ℂ, MeromorphicAt G 0 ∧
    ∀ τ : UpperHalfPlane, G (Function.Periodic.qParam 24 τ) = toFun τ

namespace EtaWeaklyHolomorphicForm

instance instFunLike (k : ℕ) : FunLike (EtaWeaklyHolomorphicForm k) UpperHalfPlane ℂ where
  coe := toFun
  coe_injective := by
    intro f g h
    cases f
    cases g
    cases h
    rfl

/-- The underlying function is holomorphic. -/
theorem holomorphic {k : ℕ} (f : EtaWeaklyHolomorphicForm k) : MDiff f :=
  f.holomorphic'

/-- The full modular-group transformation law of an eta weak form. -/
theorem map_action {k : ℕ} (f : EtaWeaklyHolomorphicForm k)
    (γ : GL (Fin 2) ℝ) (hγ : γ ∈ 𝒮ℒ) (τ : UpperHalfPlane) :
    f (γ • τ) = etaAutomorphyFactor γ τ * denom γ τ ^ k * f τ :=
  f.map_action' γ hγ τ

/-- An eta weak form has an actual meromorphic representative at the cusp. -/
theorem has_meromorphic_cusp {k : ℕ} (f : EtaWeaklyHolomorphicForm k) :
    ∃ G : ℂ → ℂ, MeromorphicAt G 0 ∧
      ∀ τ : UpperHalfPlane, G (Function.Periodic.qParam 24 τ) = f τ :=
  f.meromorphic_cusp'

end EtaWeaklyHolomorphicForm
end SptClassification
