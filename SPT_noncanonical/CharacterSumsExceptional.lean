/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.CharacterSumsRationalZeros

/-!
# Repeated shifts in exceptional character tuples

If every shift occurring in a `2w`-tuple occurs at least twice, then the
tuple has at most `w` distinct shifts. This is the combinatorial condition
forced by a perfect-power rational function: a shift occurring just once
would give a root or pole of multiplicity one [trevino2012].
-/

public section

namespace SptClassification

/-- A tuple of length `2w` with no singleton value uses at most `w` distinct
values. The proof injects two chosen occurrences of each value into the
positions of the tuple. -/
theorem card_tuple_image_le_half_of_repeated {α : Type*} [DecidableEq α]
    (w : ℕ) (u : Fin (2 * w) → α)
    (hrepeat : ∀ a ∈ (Finset.univ : Finset (Fin (2 * w))).image u,
      ∃ ij : Fin (2 * w) × Fin (2 * w),
        ij.1 ≠ ij.2 ∧ u ij.1 = a ∧ u ij.2 = a) :
    ((Finset.univ : Finset (Fin (2 * w))).image u).card ≤ w := by
  classical
  let roots := (Finset.univ : Finset (Fin (2 * w))).image u
  let pick (a : {a : α // a ∈ roots}) :
      Fin (2 * w) × Fin (2 * w) :=
    Classical.choose (hrepeat a.val a.property)
  have hpick (a : {a : α // a ∈ roots}) :
      (pick a).1 ≠ (pick a).2 ∧
        u (pick a).1 = a.val ∧ u (pick a).2 = a.val :=
    Classical.choose_spec (hrepeat a.val a.property)
  let occurrence : {a : α // a ∈ roots} × Bool → Fin (2 * w) :=
    fun ab => if ab.2 then (pick ab.1).1 else (pick ab.1).2
  have hvalue (a : {a : α // a ∈ roots}) (b : Bool) :
      u (occurrence (a, b)) = a.val := by
    cases b <;> simp [occurrence, (hpick a).2]
  have hinj : Function.Injective occurrence := by
    intro ab cd heq
    obtain ⟨a, b⟩ := ab
    obtain ⟨c, d⟩ := cd
    have hac : a = c := Subtype.ext (by
      have h := congrArg u heq
      rw [hvalue a b, hvalue c d] at h
      exact h)
    cases hac
    have hbd : b = d := by
      cases b <;> cases d
      · rfl
      · exact False.elim ((hpick a).1 heq.symm)
      · exact False.elim ((hpick a).1 heq)
      · rfl
    exact congrArg (fun t : Bool => (a, t)) hbd
  have hcard := Fintype.card_le_of_injective occurrence hinj
  have hdouble : roots.card * 2 ≤ 2 * w := by
    simpa only [Fintype.card_prod, Fintype.card_coe, Fintype.card_bool,
      Fintype.card_fin] using hcard
  dsimp [roots] at hdouble ⊢
  omega

end SptClassification
