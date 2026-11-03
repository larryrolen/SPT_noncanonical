/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.PoweredProjectionTransport

/-!
# Propagation from the normalized modular approximation

The powered-slash argument proves the transport needed by
[rolenManuscript, Lemma 1]. Only construction of the actual normalized
modular approximation remains an explicit input here.
-/

public section

namespace SptClassification

/-- Propagation for the partition-defined smallest-parts function from the
normalized modular approximation, with no separate transport assumption. -/
theorem propagation_of_approximation (p b : ℕ) (hp : p.Prime)
    (hfive : 5 ≤ p) (hb : b < p)
    (hnotcanonical : ((24 * (b : ℤ) - 1 : ℤ) : ZMod p) ≠ 0)
    (hspt : ∀ n : ℕ, p ∣ spt (p * n + b))
    (approximation : SptApproximationInput p hfive)
    (N : ℕ)
    (hclass : @legendreSym p ⟨hp⟩ (1 - 24 * (N : ℤ)) =
      @legendreSym p ⟨hp⟩ (1 - 24 * (b : ℤ))) :
    p ∣ spt N := by
  let : Fact p.Prime := ⟨hp⟩
  apply propagation_of_approximation_transport p b hp hfive hb hnotcanonical hspt
    approximation ?_ N hclass
  intro Q hQ hQavoid
  let : Fact Q.Prime := ⟨hQ⟩
  let A := approximation.forPrime Q hQ hQavoid
  exact A.form.transport_of_commonDenominator A.commonDenominator

end SptClassification
