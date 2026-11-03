/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.BlockChecker

/-!
# The block layout of the finite character certificate

The source bound is inclusive. Blocks have width `2^20`, and the last nonempty
block is clipped at `10^11 + 1`. Certified consecutive ranges are joined by a
prefix-extension theorem. Full blocks share a fixed width during computation.
-/

public section

namespace SptClassification.Sieve

/-- The inclusive cutoff in the finite character criterion. -/
def sieveLimit : ℕ := 10 ^ 11

@[simp] theorem sieveLimit_eq : sieveLimit = 10 ^ 11 := (rfl)

/-- A packed block contains this many consecutive integers. -/
@[expose] def sieveBlockWidth : ℕ := 2 ^ 20

/-- The source-range check for one block index. -/
@[expose] def indexedBlockCheck (k : ℕ) : Bool :=
  if k < 95367 then checkBlock sieveBlockWidth (sieveBlockWidth * k)
  else if k = 95367 then checkBlock 452609 (sieveBlockWidth * k)
  else true

/-- The fixed-width dispatcher agrees with the inclusive source interval layout. -/
theorem indexedBlockCheck_eq {k : ℕ} (hk : k ≤ 95367) :
    indexedBlockCheck k =
      checkBlock (checkedBlockLength sieveBlockWidth sieveLimit k) (sieveBlockWidth * k) := by
  unfold indexedBlockCheck
  by_cases hlt : k < 95367
  · have hlength : checkedBlockLength sieveBlockWidth sieveLimit k = sieveBlockWidth := by
      apply checkedBlockLength_eq_width
      change 1048576 * k + 1048576 ≤ 100000000001
      omega
    rw [ite_eq_left hlt, hlength]
  · have heq : k = 95367 := by omega
    subst k
    norm_num [checkedBlockLength_eq_min, sieveBlockWidth, sieveLimit]

theorem last_sieve_block : sieveLimit / sieveBlockWidth = 95367 := by
  decide +kernel

/-- Extend a certified prefix by a consecutive finite range of block certificates. -/
theorem extendCertifiedPrefix (first size : ℕ)
    (hprevious : ∀ k : ℕ, k < first → indexedBlockCheck k = true)
    (hnext : ∀ i : Fin size, indexedBlockCheck (first + i.val) = true) :
    ∀ k : ℕ, k < first + size → indexedBlockCheck k = true := by
  intro k hk
  by_cases hfirst : k < first
  · exact hprevious k hfirst
  · have hi : k - first < size := by omega
    have hindex : first + (k - first) = k := by omega
    simpa only [Fin.val_mk, hindex] using hnext ⟨k - first, hi⟩

/-- Join consecutive verified subranges within one certificate block interval. -/
theorem extendCertifiedSegment (base first size : ℕ)
    (hprevious : ∀ i : ℕ, i < first → indexedBlockCheck (base + i) = true)
    (hnext : ∀ i : Fin size, indexedBlockCheck (base + first + i.val) = true) :
    ∀ i : ℕ, i < first + size → indexedBlockCheck (base + i) = true := by
  intro i hi
  by_cases hfirst : i < first
  · exact hprevious i hfirst
  · have hnext' := hnext ⟨i - first, by omega⟩
    simpa only [Fin.val_mk, show base + first + (i - first) = base + i by omega]
      using hnext'

end SptClassification.Sieve
