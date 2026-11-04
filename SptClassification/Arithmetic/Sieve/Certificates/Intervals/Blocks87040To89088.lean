/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 87040 through 89087 -/

public section

namespace SptClassification.Sieve

private theorem checkBlocks_87040_87103 :
    ∀ i : Fin 64, indexedBlockCheck (87040 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87104_87167 :
    ∀ i : Fin 64, indexedBlockCheck (87104 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87168_87231 :
    ∀ i : Fin 64, indexedBlockCheck (87168 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87232_87295 :
    ∀ i : Fin 64, indexedBlockCheck (87232 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87296_87359 :
    ∀ i : Fin 64, indexedBlockCheck (87296 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87360_87423 :
    ∀ i : Fin 64, indexedBlockCheck (87360 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87424_87487 :
    ∀ i : Fin 64, indexedBlockCheck (87424 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87488_87551 :
    ∀ i : Fin 64, indexedBlockCheck (87488 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87040_87551 :
    ∀ i : Fin 512, indexedBlockCheck (87040 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (87040 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 87040 0 64 h0 checkBlocks_87040_87103
  have h128 := extendCertifiedSegment 87040 64 64 h64 checkBlocks_87104_87167
  have h192 := extendCertifiedSegment 87040 128 64 h128 checkBlocks_87168_87231
  have h256 := extendCertifiedSegment 87040 192 64 h192 checkBlocks_87232_87295
  have h320 := extendCertifiedSegment 87040 256 64 h256 checkBlocks_87296_87359
  have h384 := extendCertifiedSegment 87040 320 64 h320 checkBlocks_87360_87423
  have h448 := extendCertifiedSegment 87040 384 64 h384 checkBlocks_87424_87487
  have h512 := extendCertifiedSegment 87040 448 64 h448 checkBlocks_87488_87551
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_87552_87615 :
    ∀ i : Fin 64, indexedBlockCheck (87552 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87616_87679 :
    ∀ i : Fin 64, indexedBlockCheck (87616 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87680_87743 :
    ∀ i : Fin 64, indexedBlockCheck (87680 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87744_87807 :
    ∀ i : Fin 64, indexedBlockCheck (87744 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87808_87871 :
    ∀ i : Fin 64, indexedBlockCheck (87808 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87872_87935 :
    ∀ i : Fin 64, indexedBlockCheck (87872 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87936_87999 :
    ∀ i : Fin 64, indexedBlockCheck (87936 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88000_88063 :
    ∀ i : Fin 64, indexedBlockCheck (88000 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87552_88063 :
    ∀ i : Fin 512, indexedBlockCheck (87552 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (87552 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 87552 0 64 h0 checkBlocks_87552_87615
  have h128 := extendCertifiedSegment 87552 64 64 h64 checkBlocks_87616_87679
  have h192 := extendCertifiedSegment 87552 128 64 h128 checkBlocks_87680_87743
  have h256 := extendCertifiedSegment 87552 192 64 h192 checkBlocks_87744_87807
  have h320 := extendCertifiedSegment 87552 256 64 h256 checkBlocks_87808_87871
  have h384 := extendCertifiedSegment 87552 320 64 h320 checkBlocks_87872_87935
  have h448 := extendCertifiedSegment 87552 384 64 h384 checkBlocks_87936_87999
  have h512 := extendCertifiedSegment 87552 448 64 h448 checkBlocks_88000_88063
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_88064_88127 :
    ∀ i : Fin 64, indexedBlockCheck (88064 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88128_88191 :
    ∀ i : Fin 64, indexedBlockCheck (88128 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88192_88255 :
    ∀ i : Fin 64, indexedBlockCheck (88192 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88256_88319 :
    ∀ i : Fin 64, indexedBlockCheck (88256 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88320_88383 :
    ∀ i : Fin 64, indexedBlockCheck (88320 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88384_88447 :
    ∀ i : Fin 64, indexedBlockCheck (88384 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88448_88511 :
    ∀ i : Fin 64, indexedBlockCheck (88448 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88512_88575 :
    ∀ i : Fin 64, indexedBlockCheck (88512 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88064_88575 :
    ∀ i : Fin 512, indexedBlockCheck (88064 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (88064 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 88064 0 64 h0 checkBlocks_88064_88127
  have h128 := extendCertifiedSegment 88064 64 64 h64 checkBlocks_88128_88191
  have h192 := extendCertifiedSegment 88064 128 64 h128 checkBlocks_88192_88255
  have h256 := extendCertifiedSegment 88064 192 64 h192 checkBlocks_88256_88319
  have h320 := extendCertifiedSegment 88064 256 64 h256 checkBlocks_88320_88383
  have h384 := extendCertifiedSegment 88064 320 64 h320 checkBlocks_88384_88447
  have h448 := extendCertifiedSegment 88064 384 64 h384 checkBlocks_88448_88511
  have h512 := extendCertifiedSegment 88064 448 64 h448 checkBlocks_88512_88575
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_88576_88639 :
    ∀ i : Fin 64, indexedBlockCheck (88576 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88640_88703 :
    ∀ i : Fin 64, indexedBlockCheck (88640 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88704_88767 :
    ∀ i : Fin 64, indexedBlockCheck (88704 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88768_88831 :
    ∀ i : Fin 64, indexedBlockCheck (88768 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88832_88895 :
    ∀ i : Fin 64, indexedBlockCheck (88832 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88896_88959 :
    ∀ i : Fin 64, indexedBlockCheck (88896 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88960_89023 :
    ∀ i : Fin 64, indexedBlockCheck (88960 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_89024_89087 :
    ∀ i : Fin 64, indexedBlockCheck (89024 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88576_89087 :
    ∀ i : Fin 512, indexedBlockCheck (88576 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (88576 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 88576 0 64 h0 checkBlocks_88576_88639
  have h128 := extendCertifiedSegment 88576 64 64 h64 checkBlocks_88640_88703
  have h192 := extendCertifiedSegment 88576 128 64 h128 checkBlocks_88704_88767
  have h256 := extendCertifiedSegment 88576 192 64 h192 checkBlocks_88768_88831
  have h320 := extendCertifiedSegment 88576 256 64 h256 checkBlocks_88832_88895
  have h384 := extendCertifiedSegment 88576 320 64 h320 checkBlocks_88896_88959
  have h448 := extendCertifiedSegment 88576 384 64 h384 checkBlocks_88960_89023
  have h512 := extendCertifiedSegment 88576 448 64 h448 checkBlocks_89024_89087
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [87040, 89088) passes the packed checker. -/
public theorem blocks_in_87040_89088 :
    ∀ i : Fin 2048, indexedBlockCheck (87040 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (87040 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 87040 0 512 h0 checkBlocks_87040_87551
  have h1024 := extendCertifiedSegment 87040 512 512 h512 checkBlocks_87552_88063
  have h1536 := extendCertifiedSegment 87040 1024 512 h1024 checkBlocks_88064_88575
  have h2048 := extendCertifiedSegment 87040 1536 512 h1536 checkBlocks_88576_89087
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
