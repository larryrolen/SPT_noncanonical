/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.CharacterSumsPowerCongruence

/-!
# Large-order rigidity of rational character correlations

The multiplicity congruence for a rational power becomes an equality when
the exponent exceeds the number of factors on each side. Thus a pair of
short tuples with a shift of different multiplicity cannot contribute a
perfect-power exception to a complete character correlation [trevino2012].
-/

public section

namespace SptClassification

/-- A mismatch in the number of occurrences of any shift modulo `n`
obstructs every nonzero rational `n`th-power presentation. This includes
repeated factors on both sides. -/
theorem shift_product_ratio_ne_pow_of_count_mod_ne {F : Type*}
    [Field F] [DecidableEq F] {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (u : ι → F) (v : κ → F)
    (a : F) (n : ℕ) (C D : Polynomial F)
    (hcount : (s.filter (fun i => u i = a)).card % n ≠
      (t.filter (fun j => v j = a)).card % n)
    (hC : C ≠ 0) (hD : D ≠ 0) :
    (∏ i ∈ s, (Polynomial.X + Polynomial.C (u i))) * D ^ n ≠
      (∏ j ∈ t, (Polynomial.X + Polynomial.C (v j))) * C ^ n := by
  intro hpower
  exact hcount (shift_product_ratio_count_mod_eq s t u v a n C D hC hD hpower)

/-- If the power exponent is larger than both tuple lengths, its
root-multiplicity congruence forces the exact occurrence counts of every
shift to agree. -/
theorem shift_product_ratio_count_eq_of_large_power {F : Type*}
    [Field F] [DecidableEq F] {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (u : ι → F) (v : κ → F)
    (a : F) (n : ℕ) (hs : s.card < n) (ht : t.card < n)
    (C D : Polynomial F) (hC : C ≠ 0) (hD : D ≠ 0)
    (hpower :
      (∏ i ∈ s, (Polynomial.X + Polynomial.C (u i))) * D ^ n =
        (∏ j ∈ t, (Polynomial.X + Polynomial.C (v j))) * C ^ n) :
    (s.filter (fun i => u i = a)).card =
      (t.filter (fun j => v j = a)).card := by
  have hleft : (s.filter (fun i => u i = a)).card < n :=
    (Finset.card_filter_le _ _).trans_lt hs
  have hright : (t.filter (fun j => v j = a)).card < n :=
    (Finset.card_filter_le _ _).trans_lt ht
  simpa [Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hright] using
    (shift_product_ratio_count_mod_eq s t u v a n C D hC hD hpower)

/-- For two ordered `w`-tuples, a rational power of exponent above `w`
can occur only when every shift has the same multiplicity in both tuples.
This identifies the large-order exceptional condition in the even moment
expansion [trevino2012]. -/
theorem character_tuple_ratio_count_eq_of_large_power {F : Type*}
    [Field F] [DecidableEq F] (w n : ℕ) (hn : w < n)
    (u v : Fin w → F) (a : F) (C D : Polynomial F)
    (hC : C ≠ 0) (hD : D ≠ 0)
    (hpower :
      (∏ i : Fin w, (Polynomial.X + Polynomial.C (u i))) * D ^ n =
        (∏ j : Fin w, (Polynomial.X + Polynomial.C (v j))) * C ^ n) :
    ((Finset.univ : Finset (Fin w)).filter (fun i => u i = a)).card =
      ((Finset.univ : Finset (Fin w)).filter (fun j => v j = a)).card := by
  apply shift_product_ratio_count_eq_of_large_power
    (Finset.univ : Finset (Fin w)) (Finset.univ : Finset (Fin w))
    u v a n (by simpa using hn) (by simpa using hn) C D hC hD
  exact hpower

end SptClassification
