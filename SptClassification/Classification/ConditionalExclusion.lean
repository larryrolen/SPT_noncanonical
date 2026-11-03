/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.FiniteRange
public import SptClassification.Arithmetic.EffectiveCharacterDiscriminant
public import SptClassification.ModularForms.ConditionalPropagationProof
public import SptClassification.ModularForms.HasseObstruction

/-!
# Arithmetic witnesses for the conditional noncanonical exclusion

The finite character sieve and the conditional Treviño estimate supply the
two alternatives in the proof of [rolenManuscript, Theorem 1]. A small
prime has an actual nonvanishing smallest-parts coefficient in each nonzero
character class. A large prime has an actual squarefree discriminant with
both numerical bounds required by the geometric obstruction.
-/

public section

namespace SptClassification

/-- A noncanonical simple progression supplies a vanishing nonzero Legendre
class of the actual `spt` sequence. This is the propagation lemma with the
sign and nonzero-character bookkeeping needed for the final theorem.
[rolenManuscript, Lemma 1] -/
theorem noncanonical_progression_character_class
    (p b : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hb : b < p)
    (hspt : ∀ n : ℕ, p ∣ spt (p * n + b))
    (hnotcanonical : ((24 * b : ℕ) : ZMod p) ≠ 1)
    (inputs : ProgressionInputs p hp5) :
    ∃ sign : ℤ, (sign = 1 ∨ sign = -1) ∧
      ∀ N : ℕ, @legendreSym p ⟨hp⟩ (1 - 24 * (N : ℤ)) = sign → p ∣ spt N := by
  let : Fact p.Prime := ⟨hp⟩
  have hnotcanonical' : ((24 * (b : ℤ) - 1 : ℤ) : ZMod p) ≠ 0 := by
    intro hz
    apply hnotcanonical
    calc
      ((24 * b : ℕ) : ZMod p) = ((24 * (b : ℤ) - 1 : ℤ) : ZMod p) + 1 := by
        push_cast
        ring
      _ = 1 := by rw [hz]; ring
  have hbnonzero : ((1 - 24 * (b : ℤ) : ℤ) : ZMod p) ≠ 0 := by
    intro hz
    apply hnotcanonical'
    calc
      ((24 * (b : ℤ) - 1 : ℤ) : ZMod p) =
          -((1 - 24 * (b : ℤ) : ℤ) : ZMod p) := by push_cast; ring
      _ = 0 := by rw [hz]; ring
  refine ⟨legendreSym p (1 - 24 * (b : ℤ)),
    legendreSym.eq_one_or_neg_one p hbnonzero, ?_⟩
  intro N hclass
  exact conditional_propagation p b hp hp5 hb hnotcanonical' hspt inputs N hclass

/-- For every prime at least five and either nonzero character sign, the
finite certificate gives a nonzero coefficient or the interval estimate
gives a fundamental discriminant satisfying both obstruction bounds.
The finite range includes `10^11`. [rolenManuscript, §5] -/
theorem finite_or_effective_class_witness (tv : CharacterIntervalInput)
    (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    {sign : ℤ} (hsign : sign = 1 ∨ sign = -1) :
    (∃ N : ℕ, 1 ≤ N ∧ N ≤ 87 ∧ ¬p ∣ spt N ∧
      @legendreSym p ⟨hp⟩ (1 - 24 * (N : ℤ)) = sign) ∨
    (∃ d : ℕ, ∃ hd : 23 ≤ d,
      letI : Fact (-(d : ℤ) < 0) := ⟨by omega⟩
      d % 24 = 23 ∧ Squarefree d ∧
        (-(d : ℤ)).IsFundamentalDiscr ∧ ¬p ∣ 6 * d ∧
        @legendreSym p ⟨hp⟩ (-(d : ℤ)) = sign ∧
        (d + 1) ^ 2 < 24 * p ∧
        8 * formClassNumber (-(d : ℤ)) < p + 1) := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases hfinite : p ≤ 10 ^ 11
  · exact Or.inl (finite_class_witnesses p hp5 hfinite hsign)
  · exact Or.inr (exists_effective_character_discriminant p tv (by omega) hsign)

/-- The same two alternatives exclude a vanishing character class once the
pointwise geometric obstruction is available. The pointwise hypothesis is
used only by this assembly lemma; the named conditional theorem must obtain
it from the proved CT/CM/lift/Hasse construction. -/
theorem character_class_nonvanishing_of_pointwise_obstruction
    (tv : CharacterIntervalInput)
    (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    {sign : ℤ} (hsign : sign = 1 ∨ sign = -1)
    (hclass : ∀ N : ℕ,
      @legendreSym p ⟨hp⟩ (1 - 24 * (N : ℤ)) = sign → p ∣ spt N)
    (hobstruction : ∀ (d : ℕ) (hd : 23 ≤ d),
      letI : Fact (-(d : ℤ) < 0) := ⟨by omega⟩
      d % 24 = 23 → Squarefree d →
        (-(d : ℤ)).IsFundamentalDiscr → ¬p ∣ 6 * d →
        @legendreSym p ⟨hp⟩ (-(d : ℤ)) = sign →
        (d + 1) ^ 2 < 24 * p →
        8 * formClassNumber (-(d : ℤ)) < p + 1 → False) : False := by
  rcases finite_or_effective_class_witness tv p hp hp5 hsign with hsmall | hlarge
  · obtain ⟨N, _, _, hnonzero, hsignN⟩ := hsmall
    exact hnonzero (hclass N hsignN)
  · obtain ⟨d, hd, hdata⟩ := hlarge
    obtain ⟨hmod, hsq, hfund, hcop, hvalue, hbound, hclassBound⟩ := hdata
    exact hobstruction d hd hmod hsq hfund hcop hvalue hbound hclassBound

/-- The progression transport reduces a noncanonical simple congruence to
one of the two nonzero character classes. A proved obstruction for each
such class therefore forces the canonical residue. This is only an
assembly lemma: the final conditional theorem supplies the obstruction
from the actual lift and Hasse geometry. [rolenManuscript, Section 5] -/
theorem canonical_residue_of_character_class_obstruction
    (p b : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hb : b < p)
    (hspt : ∀ n : ℕ, p ∣ spt (p * n + b))
    (inputs : ProgressionInputs p hp5)
    (hobstruction : ∀ sign : ℤ, (sign = 1 ∨ sign = -1) →
      (∀ N : ℕ,
        @legendreSym p ⟨hp⟩ (1 - 24 * (N : ℤ)) = sign → p ∣ spt N) → False) :
    ((24 * b : ℕ) : ZMod p) = 1 := by
  by_contra hnotcanonical
  obtain ⟨sign, hsign, hclass⟩ :=
    noncanonical_progression_character_class p b hp hp5 hb hspt hnotcanonical inputs
  exact hobstruction sign hsign hclass

/-- CM descent and lift/Hasse data for one admissible discriminant. The
lift is attached to the same descended CM models as the geometric
obstruction; no character-class vanishing assertion is stored here.
[rolenManuscript, Sections 4--5] -/
structure CharacterObstructionGeometry (p d : ℕ) [Fact p.Prime]
    [Fact (-(d : ℤ) < 0)] where
  cm : ConditionalCM.CMDescentInput d p
  Form : Type
  formRing : CommRing Form
  formAlgebra : letI : CommRing Form := formRing
    Algebra (ZMod p) Form
  Point : Type
  lift : letI : CommRing Form := formRing
    letI : Algebra (ZMod p) Form := formAlgebra
    LiftHasseInput p d cm Form Point

/-- The geometric input is supplied at every discriminant eligible
for the manuscript's character obstruction. Its data do not depend on
vanishing of any `spt` class. -/
structure CharacterObstructionInputFamily where
  atDiscriminant : ∀ (p d : ℕ) [Fact p.Prime]
    [Fact (-(d : ℤ) < 0)],
    5 ≤ p → 23 ≤ d → d % 24 = 23 → Squarefree d →
    ¬p ∣ 6 * d → (d + 1) ^ 2 < 24 * p →
    8 * formClassNumber (-(d : ℤ)) < p + 1 →
    CharacterObstructionGeometry p d

/-- Finite certificates or the conditional character-interval estimate
exclude a vanishing nonzero character class by the proved geometric
obstruction. [rolenManuscript, Sections 4--5] -/
theorem character_class_nonvanishing
    (tv : CharacterIntervalInput)
    (ct : ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → QSeries.ConstantTermInputs p)
    (geometry : CharacterObstructionInputFamily)
    (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    {sign : ℤ} (hsign : sign = 1 ∨ sign = -1)
    (hclass : ∀ N : ℕ,
      @legendreSym p ⟨hp⟩ (1 - 24 * (N : ℤ)) = sign → p ∣ spt N) :
    False := by
  let : Fact p.Prime := ⟨hp⟩
  apply character_class_nonvanishing_of_pointwise_obstruction tv p hp hp5
    hsign hclass
  intro d hd hmod hsq _ hcop hvalue hbound hclassBound
  let : Fact (-(d : ℤ) < 0) := ⟨by omega⟩
  let G := geometry.atDiscriminant p d hp5 hd hmod hsq hcop hbound hclassBound
  let : CommRing G.Form := G.formRing
  let : Algebra (ZMod p) G.Form := G.formAlgebra
  have hzero : ∀ j : ℕ,
      legendreSym p (1 - 24 * (j : ℤ)) = sign →
      ((spt j : ℤ) : ZMod p) = 0 := by
    intro j hj
    simpa only [Int.cast_natCast] using
      (ZMod.natCast_eq_zero_iff (spt j) p).mpr (hclass j hj)
  exact conditional_character_obstruction p hp5 sign hsign d (by omega)
    hsq hmod hvalue hbound hclassBound (ct p hp5) G.cm G.lift hzero

/-- A simple `spt` congruence at a prime at least five has the canonical
residue, conditional only on the explicit CT, progression, interval,
CM-descent and lift/Hasse input families. [rolenManuscript, Theorem 1] -/
theorem conditional_noncanonical_exclusion
    (tv : CharacterIntervalInput)
    (ct : ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → QSeries.ConstantTermInputs p)
    (progression : ∀ (p : ℕ), p.Prime → ∀ hp5 : 5 ≤ p, ProgressionInputs p hp5)
    (geometry : CharacterObstructionInputFamily)
    (p b : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hb : b < p)
    (hspt : ∀ n : ℕ, p ∣ spt (p * n + b)) :
    ((24 * b : ℕ) : ZMod p) = 1 := by
  apply canonical_residue_of_character_class_obstruction p b hp hp5 hb hspt
    (progression p hp hp5)
  intro sign hsign hclass
  exact character_class_nonvanishing tv ct geometry p hp hp5 hsign hclass

end SptClassification
