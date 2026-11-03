/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.CharacterSumsPowerRigidity
public import SptClassification.Arithmetic.CharacterSumsDiagonal

/-!
# Large-order diagonal character correlations

When the order of a character exceeds the tuple length, a rational-power
exception has equal multiplicities at every shift. Consequently its two
products of linear factors agree, and its complete correlation has the same
exact value as a diagonal correlation [trevino2012].
-/

public section

namespace SptClassification

/-- Two finite products obtained from tuples with the same occurrence count
at every value are equal in any commutative monoid. -/
theorem shift_product_eq_of_count_eq {α β ι κ : Type*}
    [DecidableEq α] [DecidableEq ι] [DecidableEq κ] [CommMonoid β]
    (s : Finset ι) (t : Finset κ) (u : ι → α) (v : κ → α)
    (f : α → β)
    (hcount : ∀ a : α, (s.filter (fun i => u i = a)).card =
      (t.filter (fun j => v j = a)).card) :
    (∏ i ∈ s, f (u i)) = ∏ j ∈ t, f (v j) := by
  classical
  have hm : s.val.map u = t.val.map v := by
    apply Multiset.ext.mpr
    intro a
    rw [Multiset.count_map, Multiset.count_map]
    change (s.filter (fun i => a = u i)).card =
      (t.filter (fun j => a = v j)).card
    simpa only [eq_comm] using hcount a
  have hp := congrArg (fun m : Multiset α => (m.map f).prod) hm
  change (s.val.map (f ∘ u)).prod = (t.val.map (f ∘ v)).prod
  simpa [Multiset.map_map, Function.comp_def] using hp

/-- A nonzero rational `n`th-power presentation of two short shifted-factor
products forces equality of their values when both lengths are below `n`.
This is the diagonal case of the large-order moment analysis [trevino2012]. -/
theorem shift_product_eq_of_large_rational_power {F : Type*}
    [Field F] [DecidableEq F] {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (u : ι → F) (v : κ → F)
    (n : ℕ) (hs : s.card < n) (ht : t.card < n)
    (C D : Polynomial F) (hC : C ≠ 0) (hD : D ≠ 0)
    (hpower :
      (∏ i ∈ s, (Polynomial.X + Polynomial.C (u i))) * D ^ n =
        (∏ j ∈ t, (Polynomial.X + Polynomial.C (v j))) * C ^ n)
    (x : F) :
    (∏ i ∈ s, (x + u i)) = ∏ j ∈ t, (x + v j) := by
  apply shift_product_eq_of_count_eq s t u v (fun a => x + a)
  intro a
  exact shift_product_ratio_count_eq_of_large_power
    s t u v a n hs ht C D hC hD hpower

/-- Every large-order rational-power exception contributes precisely `p`
minus the number of distinct shifts. The count includes repeated shifts and
the zero residues omitted by the Dirichlet character [trevino2012]. -/
theorem sum_character_ratio_of_large_rational_power (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) {ι κ : Type*}
    (s : Finset ι) (t : Finset κ)
    (u : ι → ZMod p) (v : κ → ZMod p)
    (n : ℕ) (hs : s.card < n) (ht : t.card < n)
    (C D : Polynomial (ZMod p)) (hC : C ≠ 0) (hD : D ≠ 0)
    (hpower :
      (∏ i ∈ s, (Polynomial.X + Polynomial.C (u i))) * D ^ n =
        (∏ j ∈ t, (Polynomial.X + Polynomial.C (v j))) * C ^ n) :
    (∑ x : ZMod p,
      χ ((∏ i ∈ s, (x + u i)) / (∏ j ∈ t, (x + v j)))) =
      (p : ℂ) - ((s.image (fun i => -u i)).card : ℂ) := by
  classical
  have hprod (x : ZMod p) :
      (∏ j ∈ t, (x + v j)) = ∏ i ∈ s, (x + u i) :=
    (shift_product_eq_of_large_rational_power
      s t u v n hs ht C D hC hD hpower x).symm
  simp_rw [hprod]
  exact sum_character_tuple_self_ratio p χ s u

end SptClassification
