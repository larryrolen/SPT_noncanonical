/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.CharacterSumsPowerMultiplicity

/-!
# Exceptional tuples in rational character correlations

If a rational product of shifted linear factors is a nontrivial power,
every shift in the numerator and denominator together occurs at least
twice. This is the algebraic reason that perfect-power tuples have small
support in the higher moment method [trevino2012].
-/

public section

namespace SptClassification

/-- Under a nonzero rational power presentation, each numerator shift
occurs again in the numerator or occurs in the denominator. -/
theorem numerator_shift_repeated_of_rational_power
    {F : Type*} [Field F] {ι κ : Type*} [DecidableEq ι]
    (s : Finset ι) (t : Finset κ) (u : ι → F) (v : κ → F)
    (n : ℕ) (hn : 2 ≤ n) (C D : Polynomial F)
    (hC : C ≠ 0) (hD : D ≠ 0)
    (hpower :
      (∏ j ∈ s, (Polynomial.X + Polynomial.C (u j))) * D ^ n =
        (∏ k ∈ t, (Polynomial.X + Polynomial.C (v k))) * C ^ n)
    (i : ι) (hi : i ∈ s) :
    (∃ j ∈ s, j ≠ i ∧ u j = u i) ∨
      (∃ k ∈ t, v k = u i) := by
  classical
  by_contra hnone
  have hunique : ∀ j ∈ s, u j = u i → j = i := by
    intro j hj hji
    by_contra hne
    exact hnone (Or.inl ⟨j, hj, hne, hji⟩)
  have habsent : ∀ k ∈ t, v k ≠ u i := by
    intro k hk hki
    exact hnone (Or.inr ⟨k, hk, hki⟩)
  exact (shift_product_ratio_ne_pow_of_unique_numerator_nonzero
    s t u v i hi hunique habsent n hn C D hC hD) hpower

/-- Under a nonzero rational power presentation, each denominator shift
occurs again in the denominator or occurs in the numerator. -/
theorem denominator_shift_repeated_of_rational_power
    {F : Type*} [Field F] {ι κ : Type*} [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (u : ι → F) (v : κ → F)
    (n : ℕ) (hn : 2 ≤ n) (C D : Polynomial F)
    (hC : C ≠ 0) (hD : D ≠ 0)
    (hpower :
      (∏ i ∈ s, (Polynomial.X + Polynomial.C (u i))) * D ^ n =
        (∏ k ∈ t, (Polynomial.X + Polynomial.C (v k))) * C ^ n)
    (j : κ) (hj : j ∈ t) :
    (∃ k ∈ t, k ≠ j ∧ v k = v j) ∨
      (∃ i ∈ s, u i = v j) := by
  classical
  by_contra hnone
  have hunique : ∀ k ∈ t, v k = v j → k = j := by
    intro k hk hkj
    by_contra hne
    exact hnone (Or.inl ⟨k, hk, hne, hkj⟩)
  have habsent : ∀ i ∈ s, u i ≠ v j := by
    intro i hi hij
    exact hnone (Or.inr ⟨i, hi, hij⟩)
  exact (shift_product_ratio_ne_pow_of_unique_denominator_nonzero
    s t u v j hj hunique habsent n hn C D hC hD) hpower

/-- If each value in a finite tuple occurs at least twice, then twice the
number of distinct values is at most the number of positions. -/
theorem twice_card_image_le_of_repeated {α β : Type*}
    [Fintype α] [DecidableEq β] (f : α → β)
    (hrepeat : ∀ b ∈ (Finset.univ : Finset α).image f,
      ∃ ij : α × α, ij.1 ≠ ij.2 ∧ f ij.1 = b ∧ f ij.2 = b) :
    2 * ((Finset.univ : Finset α).image f).card ≤ Fintype.card α := by
  classical
  let support := (Finset.univ : Finset α).image f
  let pick (b : {b : β // b ∈ support}) : α × α :=
    Classical.choose (hrepeat b.val b.property)
  have hpick (b : {b : β // b ∈ support}) :
      (pick b).1 ≠ (pick b).2 ∧
        f (pick b).1 = b.val ∧ f (pick b).2 = b.val :=
    Classical.choose_spec (hrepeat b.val b.property)
  let occurrence : {b : β // b ∈ support} × Bool → α :=
    fun bb => if bb.2 then (pick bb.1).1 else (pick bb.1).2
  have hvalue (b : {b : β // b ∈ support}) (t : Bool) :
      f (occurrence (b, t)) = b.val := by
    cases t <;> simp [occurrence, (hpick b).2]
  have hinj : Function.Injective occurrence := by
    intro bc de heq
    obtain ⟨b, c⟩ := bc
    obtain ⟨d, e⟩ := de
    have hbd : b = d := Subtype.ext (by
      have h := congrArg f heq
      rw [hvalue b c, hvalue d e] at h
      exact h)
    cases hbd
    have hce : c = e := by
      cases c <;> cases e
      · rfl
      · exact False.elim ((hpick b).1 heq.symm)
      · exact False.elim ((hpick b).1 heq)
      · rfl
    exact congrArg (fun t : Bool => (b, t)) hce
  have hcard := Fintype.card_le_of_injective occurrence hinj
  have hdouble : support.card * 2 ≤ Fintype.card α := by
    simpa only [Fintype.card_prod, Fintype.card_coe, Fintype.card_bool]
      using hcard
  dsimp [support] at hdouble ⊢
  omega

/-- If a rational correlation from two `w`-tuples is a nontrivial perfect
power, their combined shifts use at most `w` distinct residues. This is
the precise small-support condition for the exceptional tuples in an even
character moment [trevino2012]. -/
theorem card_rational_power_shift_support_le
    {F : Type*} [Field F] [DecidableEq F] (w : ℕ)
    (u v : Fin w → F) (n : ℕ) (hn : 2 ≤ n)
    (C D : Polynomial F) (hC : C ≠ 0) (hD : D ≠ 0)
    (hpower :
      (∏ i ∈ (Finset.univ : Finset (Fin w)),
        (Polynomial.X + Polynomial.C (u i))) * D ^ n =
      (∏ j ∈ (Finset.univ : Finset (Fin w)),
        (Polynomial.X + Polynomial.C (v j))) * C ^ n) :
    (((Finset.univ : Finset (Fin w)).image u) ∪
      ((Finset.univ : Finset (Fin w)).image v)).card ≤ w := by
  classical
  let f : Sum (Fin w) (Fin w) → F := Sum.elim u v
  have hrepeated :
      ∀ a ∈ (Finset.univ : Finset (Sum (Fin w) (Fin w))).image f,
        ∃ ij : Sum (Fin w) (Fin w) × Sum (Fin w) (Fin w),
          ij.1 ≠ ij.2 ∧ f ij.1 = a ∧ f ij.2 = a := by
    intro a ha
    obtain ⟨q, _, hqa⟩ := Finset.mem_image.mp ha
    cases q with
    | inl i =>
      have hi := numerator_shift_repeated_of_rational_power
        (Finset.univ : Finset (Fin w)) (Finset.univ : Finset (Fin w))
        u v n hn C D hC hD hpower i (Finset.mem_univ i)
      rcases hi with ⟨j, _, hji, huj⟩ | ⟨j, _, hvj⟩
      · refine ⟨⟨Sum.inl j, Sum.inl i⟩, ?_, ?_, ?_⟩
        · exact fun h => hji (Sum.inl.inj h)
        · simpa [f, huj] using hqa
        · simpa [f] using hqa
      · refine ⟨⟨Sum.inl i, Sum.inr j⟩, ?_, ?_, ?_⟩
        · intro h
          cases h
        · simpa [f] using hqa
        · simpa [f, hvj] using hqa
    | inr j =>
      have hj := denominator_shift_repeated_of_rational_power
        (Finset.univ : Finset (Fin w)) (Finset.univ : Finset (Fin w))
        u v n hn C D hC hD hpower j (Finset.mem_univ j)
      rcases hj with ⟨k, _, hkj, hvk⟩ | ⟨i, _, hui⟩
      · refine ⟨⟨Sum.inr k, Sum.inr j⟩, ?_, ?_, ?_⟩
        · exact fun h => hkj (Sum.inr.inj h)
        · simpa [f, hvk] using hqa
        · simpa [f] using hqa
      · refine ⟨⟨Sum.inr j, Sum.inl i⟩, ?_, ?_, ?_⟩
        · intro h
          cases h
        · simpa [f] using hqa
        · simpa [f, hui] using hqa
  have himage :
      (Finset.univ : Finset (Sum (Fin w) (Fin w))).image f =
      ((Finset.univ : Finset (Fin w)).image u) ∪
        ((Finset.univ : Finset (Fin w)).image v) := by
    ext a
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · rintro ⟨q, hq⟩
      cases q with
      | inl i => exact Or.inl ⟨i, by simpa [f] using hq⟩
      | inr j => exact Or.inr ⟨j, by simpa [f] using hq⟩
    · rintro (⟨i, hi⟩ | ⟨j, hj⟩)
      · exact ⟨Sum.inl i, by simpa [f] using hi⟩
      · exact ⟨Sum.inr j, by simpa [f] using hj⟩
  have hbound := twice_card_image_le_of_repeated f hrepeated
  rw [himage] at hbound
  simp only [Fintype.card_sum, Fintype.card_fin] at hbound
  omega

end SptClassification
