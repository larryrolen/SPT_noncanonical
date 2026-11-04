/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 95232 through 95743 -/

public section

namespace SptClassification.Sieve

-- Bound memory by checking small certificate pieces sequentially.
set_option Elab.async false

private theorem checkBlocks_95232_95295_part0 :
    ∀ i : Fin 32, indexedBlockCheck (95232 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_95232_95295_part1 :
    ∀ i : Fin 32, indexedBlockCheck (95264 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_95232_95295 :
    ∀ i : Fin 64, indexedBlockCheck (95232 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (95232 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 95232 0 32 h0 checkBlocks_95232_95295_part0
  have h64 := extendCertifiedSegment 95232 32 32 h32 checkBlocks_95232_95295_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_95296_95359_part0 :
    ∀ i : Fin 32, indexedBlockCheck (95296 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_95296_95359_part1 :
    ∀ i : Fin 32, indexedBlockCheck (95328 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_95296_95359 :
    ∀ i : Fin 64, indexedBlockCheck (95296 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (95296 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 95296 0 32 h0 checkBlocks_95296_95359_part0
  have h64 := extendCertifiedSegment 95296 32 32 h32 checkBlocks_95296_95359_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_95360_95423_part0 :
    ∀ i : Fin 32, indexedBlockCheck (95360 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_95360_95423_part1 :
    ∀ i : Fin 32, indexedBlockCheck (95392 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_95360_95423 :
    ∀ i : Fin 64, indexedBlockCheck (95360 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (95360 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 95360 0 32 h0 checkBlocks_95360_95423_part0
  have h64 := extendCertifiedSegment 95360 32 32 h32 checkBlocks_95360_95423_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_95424_95487_part0 :
    ∀ i : Fin 32, indexedBlockCheck (95424 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_95424_95487_part1 :
    ∀ i : Fin 32, indexedBlockCheck (95456 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_95424_95487 :
    ∀ i : Fin 64, indexedBlockCheck (95424 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (95424 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 95424 0 32 h0 checkBlocks_95424_95487_part0
  have h64 := extendCertifiedSegment 95424 32 32 h32 checkBlocks_95424_95487_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_95488_95551_part0 :
    ∀ i : Fin 32, indexedBlockCheck (95488 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_95488_95551_part1 :
    ∀ i : Fin 32, indexedBlockCheck (95520 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_95488_95551 :
    ∀ i : Fin 64, indexedBlockCheck (95488 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (95488 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 95488 0 32 h0 checkBlocks_95488_95551_part0
  have h64 := extendCertifiedSegment 95488 32 32 h32 checkBlocks_95488_95551_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_95552_95615_part0 :
    ∀ i : Fin 32, indexedBlockCheck (95552 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_95552_95615_part1 :
    ∀ i : Fin 32, indexedBlockCheck (95584 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_95552_95615 :
    ∀ i : Fin 64, indexedBlockCheck (95552 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (95552 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 95552 0 32 h0 checkBlocks_95552_95615_part0
  have h64 := extendCertifiedSegment 95552 32 32 h32 checkBlocks_95552_95615_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_95616_95679_part0 :
    ∀ i : Fin 32, indexedBlockCheck (95616 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_95616_95679_part1 :
    ∀ i : Fin 32, indexedBlockCheck (95648 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_95616_95679 :
    ∀ i : Fin 64, indexedBlockCheck (95616 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (95616 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 95616 0 32 h0 checkBlocks_95616_95679_part0
  have h64 := extendCertifiedSegment 95616 32 32 h32 checkBlocks_95616_95679_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_95680_95743_part0 :
    ∀ i : Fin 32, indexedBlockCheck (95680 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_95680_95743_part1 :
    ∀ i : Fin 32, indexedBlockCheck (95712 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_95680_95743 :
    ∀ i : Fin 64, indexedBlockCheck (95680 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (95680 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 95680 0 32 h0 checkBlocks_95680_95743_part0
  have h64 := extendCertifiedSegment 95680 32 32 h32 checkBlocks_95680_95743_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_95232_95743 :
    ∀ i : Fin 512, indexedBlockCheck (95232 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (95232 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 95232 0 64 h0 checkBlocks_95232_95295
  have h128 := extendCertifiedSegment 95232 64 64 h64 checkBlocks_95296_95359
  have h192 := extendCertifiedSegment 95232 128 64 h128 checkBlocks_95360_95423
  have h256 := extendCertifiedSegment 95232 192 64 h192 checkBlocks_95424_95487
  have h320 := extendCertifiedSegment 95232 256 64 h256 checkBlocks_95488_95551
  have h384 := extendCertifiedSegment 95232 320 64 h320 checkBlocks_95552_95615
  have h448 := extendCertifiedSegment 95232 384 64 h384 checkBlocks_95616_95679
  have h512 := extendCertifiedSegment 95232 448 64 h448 checkBlocks_95680_95743
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [95232, 95744) passes the packed checker. -/
public theorem blocks_in_95232_95744 :
    ∀ i : Fin 512, indexedBlockCheck (95232 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (95232 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 95232 0 512 h0 checkBlocks_95232_95743
  intro i
  exact h512 i.val i.isLt

end SptClassification.Sieve
