/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.CharacterSumsLargeOrderDiagonal

/-!
# Large-order exceptional pairs in character moments

For exponents larger than both tuple lengths, a quotient of products of
shifted linear factors is a rational perfect power exactly when the two
products agree. This gives an intrinsic algebraic description of the
exceptional terms in a high character moment [trevino2012].
-/

public section

namespace SptClassification

/-- Equality of two shifted-factor polynomials is equivalent to equality of
the multiplicity of every shift. The implication from polynomial equality
uses root multiplicities, so repeated factors are included [trevino2012]. -/
theorem shift_product_eq_iff_count_eq {F : Type*}
    [Field F] [DecidableEq F] {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (u : ι → F) (v : κ → F) :
    (∏ i ∈ s, (Polynomial.X + Polynomial.C (u i))) =
        (∏ j ∈ t, (Polynomial.X + Polynomial.C (v j))) ↔
      ∀ a : F, (s.filter (fun i => u i = a)).card =
        (t.filter (fun j => v j = a)).card := by
  constructor
  · intro hprod a
    have hroot := congrArg (Polynomial.rootMultiplicity (-a)) hprod
    simpa only [rootMultiplicity_shift_product] using hroot
  · intro hcount
    exact shift_product_eq_of_count_eq s t u v
      (fun a => Polynomial.X + Polynomial.C a) hcount

/-- A nonzero rational `n`th-power presentation of two short products of
shifted factors is equivalent to equality of the products when `n` exceeds
both numbers of factors. No reducedness assumption on the presentation is
needed [trevino2012]. -/
theorem shift_product_rational_power_iff_eq_of_large_order {F : Type*}
    [Field F] [DecidableEq F] {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (u : ι → F) (v : κ → F)
    (n : ℕ) (hs : s.card < n) (ht : t.card < n) :
    (∃ C D : Polynomial F, C ≠ 0 ∧ D ≠ 0 ∧
      (∏ i ∈ s, (Polynomial.X + Polynomial.C (u i))) * D ^ n =
        (∏ j ∈ t, (Polynomial.X + Polynomial.C (v j))) * C ^ n) ↔
      (∏ i ∈ s, (Polynomial.X + Polynomial.C (u i))) =
        ∏ j ∈ t, (Polynomial.X + Polynomial.C (v j)) := by
  constructor
  · rintro ⟨C, D, hC, hD, hpower⟩
    apply shift_product_eq_of_count_eq s t u v
      (fun a => Polynomial.X + Polynomial.C a)
    intro a
    exact shift_product_ratio_count_eq_of_large_power
      s t u v a n hs ht C D hC hD hpower
  · intro hprod
    refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
    simpa using hprod

/-- For two `w`-tuples, every rational-power exception with exponent above
`w` is exactly a pair with equal shift polynomials. This form can be used
directly as the exceptional predicate in the finite moment expansion
[trevino2012]. -/
theorem character_tuple_rational_power_iff_eq_of_large_order {F : Type*}
    [Field F] [DecidableEq F] (w n : ℕ) (hn : w < n)
    (u v : Fin w → F) :
    (∃ C D : Polynomial F, C ≠ 0 ∧ D ≠ 0 ∧
      (∏ i : Fin w, (Polynomial.X + Polynomial.C (u i))) * D ^ n =
        (∏ j : Fin w, (Polynomial.X + Polynomial.C (v j))) * C ^ n) ↔
      (∏ i : Fin w, (Polynomial.X + Polynomial.C (u i))) =
        ∏ j : Fin w, (Polynomial.X + Polynomial.C (v j)) := by
  simpa only [Finset.prod_attach_univ] using
    (shift_product_rational_power_iff_eq_of_large_order
      (Finset.univ : Finset (Fin w)) (Finset.univ : Finset (Fin w))
      u v n (by simpa using hn) (by simpa using hn))

/-- Above the tuple length, a rational-power exception is exactly equality
of all shift multiplicities in the numerator and denominator. -/
theorem character_tuple_rational_power_iff_count_eq_of_large_order
    {F : Type*} [Field F] [DecidableEq F]
    (w n : ℕ) (hn : w < n) (u v : Fin w → F) :
    (∃ C D : Polynomial F, C ≠ 0 ∧ D ≠ 0 ∧
      (∏ i : Fin w, (Polynomial.X + Polynomial.C (u i))) * D ^ n =
        (∏ j : Fin w, (Polynomial.X + Polynomial.C (v j))) * C ^ n) ↔
      ∀ a : F,
        ((Finset.univ : Finset (Fin w)).filter (fun i => u i = a)).card =
        ((Finset.univ : Finset (Fin w)).filter (fun j => v j = a)).card := by
  rw [character_tuple_rational_power_iff_eq_of_large_order w n hn u v]
  simpa only [Finset.prod_attach_univ] using
    (shift_product_eq_iff_count_eq
      (Finset.univ : Finset (Fin w)) (Finset.univ : Finset (Fin w)) u v)

end SptClassification
