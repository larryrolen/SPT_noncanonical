/- Assembled by AxiomProver. -/

module

public import SptClassification.Partitions.Evaluation
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.IntervalCases

/-!
# Canonical simple smallest-parts progressions

The independent canonical necessity theorem of [rolen2026canonical,
Theorem 1.1] and the three congruences of [andrews2008] are explicit inputs.
The elementary residue calculation and the exclusions at two and three
are proved for the actual partition-based `spt`.
-/

@[expose] public section

namespace SptClassification

/-- The previously published canonical necessity theorem and Andrews'
three congruences. Its first field concerns only canonical progressions;
it does not assume exclusion of any noncanonical progression. -/
structure CanonicalInputs : Prop where
  canonicalNecessity : ∀ (p b : ℕ), p.Prime → 5 ≤ p → b < p →
    ((24 * b : ℕ) : ZMod p) = 1 →
    (∀ n : ℕ, p ∣ spt (p * n + b)) → p = 5 ∨ p = 7 ∨ p = 13
  andrewsFive : ∀ n : ℕ, 5 ∣ spt (5 * n + 4)
  andrewsSeven : ∀ n : ℕ, 7 ∣ spt (7 * n + 5)
  andrewsThirteen : ∀ n : ℕ, 13 ∣ spt (13 * n + 6)

/-- Necessity in [rolen2026canonical, Theorem 1.1]. That paper defines
the canonical residue by `24 * b ≡ 1 (mod p)` for primes `p ≥ 5`;
its theorem gives precisely the three primes below. This named
literature theorem is used as an admitted premise. -/
theorem rolen_canonical_prime_necessity
    (p b : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hb : b < p)
    (hcanon : ((24 * b : ℕ) : ZMod p) = 1)
    (hspt : ∀ n : ℕ, p ∣ spt (p * n + b)) :
    p = 5 ∨ p = 7 ∨ p = 13 := by
  sorry

/-- Andrews' congruence at five, displayed in
[rolen2026canonical, §1] with attribution to [andrews2008]. The
primary-paper theorem locator still needs verification. -/
theorem andrews_spt_five (n : ℕ) : 5 ∣ spt (5 * n + 4) := by
  sorry

/-- Andrews' congruence at seven, displayed in
[rolen2026canonical, §1] with attribution to [andrews2008]. The
primary-paper theorem locator still needs verification. -/
theorem andrews_spt_seven (n : ℕ) : 7 ∣ spt (7 * n + 5) := by
  sorry

/-- Andrews' congruence at thirteen, displayed in
[rolen2026canonical, §1] with attribution to [andrews2008]. The
primary-paper theorem locator still needs verification. -/
theorem andrews_spt_thirteen (n : ℕ) : 13 ∣ spt (13 * n + 6) := by
  sorry

/-- The four separately identified literature results supplying the
canonical classification. -/
theorem canonicalLiteratureInputs : CanonicalInputs := by
  exact ⟨rolen_canonical_prime_necessity, andrews_spt_five,
    andrews_spt_seven, andrews_spt_thirteen⟩

private theorem canonical_residue_five {b : ℕ} (hb : b < 5)
    (hcanon : ((24 * b : ℕ) : ZMod 5) = 1) : b = 4 := by
  change ((24 * b : ℕ) : ZMod 5) = ((1 : ℕ) : ZMod 5) at hcanon
  rw [ZMod.natCast_eq_natCast_iff] at hcanon
  interval_cases b <;> norm_num [Nat.ModEq] at *

private theorem canonical_residue_seven {b : ℕ} (hb : b < 7)
    (hcanon : ((24 * b : ℕ) : ZMod 7) = 1) : b = 5 := by
  change ((24 * b : ℕ) : ZMod 7) = ((1 : ℕ) : ZMod 7) at hcanon
  rw [ZMod.natCast_eq_natCast_iff] at hcanon
  interval_cases b <;> norm_num [Nat.ModEq] at *

private theorem canonical_residue_thirteen {b : ℕ} (hb : b < 13)
    (hcanon : ((24 * b : ℕ) : ZMod 13) = 1) : b = 6 := by
  change ((24 * b : ℕ) : ZMod 13) = ((1 : ℕ) : ZMod 13) at hcanon
  rw [ZMod.natCast_eq_natCast_iff] at hcanon
  interval_cases b <;> norm_num [Nat.ModEq] at *

/-- The canonical residue is unique at each prime allowed by the independent
canonical necessity input. -/
theorem canonical_progression_cases (inputs : CanonicalInputs)
    (p b : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hb : b < p)
    (hcanon : ((24 * b : ℕ) : ZMod p) = 1)
    (hspt : ∀ n : ℕ, p ∣ spt (p * n + b)) :
    (p = 5 ∧ b = 4) ∨ (p = 7 ∧ b = 5) ∨ (p = 13 ∧ b = 6) := by
  rcases inputs.canonicalNecessity p b hp hp5 hb hcanon hspt with rfl | rfl | rfl
  · exact Or.inl ⟨rfl, canonical_residue_five hb hcanon⟩
  · exact Or.inr (Or.inl ⟨rfl, canonical_residue_seven hb hcanon⟩)
  · exact Or.inr (Or.inr ⟨rfl, canonical_residue_thirteen hb hcanon⟩)

/-- Andrews' three congruences give the converse direction for the actual
smallest-parts function. [andrews2008] -/
theorem canonical_cases_are_congruences (inputs : CanonicalInputs)
    (p b : ℕ)
    (hcases : (p = 5 ∧ b = 4) ∨ (p = 7 ∧ b = 5) ∨ (p = 13 ∧ b = 6)) :
    ∀ n : ℕ, p ∣ spt (p * n + b) := by
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact inputs.andrewsFive
  · exact inputs.andrewsSeven
  · exact inputs.andrewsThirteen

/-- The already checked small `spt` values exclude the two small prime
moduli in the manuscript's classification. -/
theorem no_small_prime_simple_congruence (p b : ℕ)
    (hp : p.Prime) (hb : b < p)
    (hspt : ∀ n : ℕ, p ∣ spt (p * n + b)) : 5 ≤ p := by
  by_contra h
  have hsmall : p = 2 ∨ p = 3 := by
    have hprime := hp.two_le
    have hfour : p ≠ 4 := by
      intro hfour
      subst p
      norm_num at hp
    omega
  rcases hsmall with rfl | rfl
  · exact no_congruence_mod_two hb hspt
  · exact no_congruence_mod_three hb hspt

/-- Assemble the independent canonical necessity and Andrews congruences
with a proved exclusion of noncanonical progressions. The last argument is
discharged by the conditional geometric and arithmetic theorem below, not
packaged among the canonical literature inputs. [rolenManuscript,
Corollary 1] -/
theorem simple_congruence_classification_of_noncanonical_exclusion
    (inputs : CanonicalInputs)
    (hnoncanonical : ∀ (p b : ℕ), p.Prime → 5 ≤ p → b < p →
      (∀ n : ℕ, p ∣ spt (p * n + b)) →
      ((24 * b : ℕ) : ZMod p) = 1)
    (p b : ℕ) (hp : p.Prime) (hb : b < p) :
    (∀ n : ℕ, p ∣ spt (p * n + b)) ↔
      (p = 5 ∧ b = 4) ∨ (p = 7 ∧ b = 5) ∨ (p = 13 ∧ b = 6) := by
  constructor
  · intro hspt
    have hp5 := no_small_prime_simple_congruence p b hp hb hspt
    exact canonical_progression_cases inputs p b hp hp5 hb
      (hnoncanonical p b hp hp5 hb hspt) hspt
  · exact canonical_cases_are_congruences inputs p b

end SptClassification
