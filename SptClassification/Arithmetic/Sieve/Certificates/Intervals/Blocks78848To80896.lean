/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

-- Build-order dependency: keep at most two large certificate modules in flight.
import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks74752To76800

/-! # Certified checker blocks from 78848 through 80895 -/

public section

namespace SptClassification.Sieve

private theorem checkBlocks_78848_78911 :
    ∀ i : Fin 64, indexedBlockCheck (78848 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_78912_78975 :
    ∀ i : Fin 64, indexedBlockCheck (78912 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_78976_79039 :
    ∀ i : Fin 64, indexedBlockCheck (78976 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79040_79103 :
    ∀ i : Fin 64, indexedBlockCheck (79040 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79104_79167 :
    ∀ i : Fin 64, indexedBlockCheck (79104 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79168_79231 :
    ∀ i : Fin 64, indexedBlockCheck (79168 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79232_79295 :
    ∀ i : Fin 64, indexedBlockCheck (79232 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79296_79359 :
    ∀ i : Fin 64, indexedBlockCheck (79296 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_78848_79359 :
    ∀ i : Fin 512, indexedBlockCheck (78848 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (78848 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 78848 0 64 h0 checkBlocks_78848_78911
  have h128 := extendCertifiedSegment 78848 64 64 h64 checkBlocks_78912_78975
  have h192 := extendCertifiedSegment 78848 128 64 h128 checkBlocks_78976_79039
  have h256 := extendCertifiedSegment 78848 192 64 h192 checkBlocks_79040_79103
  have h320 := extendCertifiedSegment 78848 256 64 h256 checkBlocks_79104_79167
  have h384 := extendCertifiedSegment 78848 320 64 h320 checkBlocks_79168_79231
  have h448 := extendCertifiedSegment 78848 384 64 h384 checkBlocks_79232_79295
  have h512 := extendCertifiedSegment 78848 448 64 h448 checkBlocks_79296_79359
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_79360_79423 :
    ∀ i : Fin 64, indexedBlockCheck (79360 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79424_79487 :
    ∀ i : Fin 64, indexedBlockCheck (79424 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79488_79551 :
    ∀ i : Fin 64, indexedBlockCheck (79488 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79552_79615 :
    ∀ i : Fin 64, indexedBlockCheck (79552 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79616_79679 :
    ∀ i : Fin 64, indexedBlockCheck (79616 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79680_79743 :
    ∀ i : Fin 64, indexedBlockCheck (79680 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79744_79807 :
    ∀ i : Fin 64, indexedBlockCheck (79744 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79808_79871 :
    ∀ i : Fin 64, indexedBlockCheck (79808 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79360_79871 :
    ∀ i : Fin 512, indexedBlockCheck (79360 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (79360 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 79360 0 64 h0 checkBlocks_79360_79423
  have h128 := extendCertifiedSegment 79360 64 64 h64 checkBlocks_79424_79487
  have h192 := extendCertifiedSegment 79360 128 64 h128 checkBlocks_79488_79551
  have h256 := extendCertifiedSegment 79360 192 64 h192 checkBlocks_79552_79615
  have h320 := extendCertifiedSegment 79360 256 64 h256 checkBlocks_79616_79679
  have h384 := extendCertifiedSegment 79360 320 64 h320 checkBlocks_79680_79743
  have h448 := extendCertifiedSegment 79360 384 64 h384 checkBlocks_79744_79807
  have h512 := extendCertifiedSegment 79360 448 64 h448 checkBlocks_79808_79871
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_79872_79935 :
    ∀ i : Fin 64, indexedBlockCheck (79872 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79936_79999 :
    ∀ i : Fin 64, indexedBlockCheck (79936 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80000_80063 :
    ∀ i : Fin 64, indexedBlockCheck (80000 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80064_80127 :
    ∀ i : Fin 64, indexedBlockCheck (80064 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80128_80191 :
    ∀ i : Fin 64, indexedBlockCheck (80128 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80192_80255 :
    ∀ i : Fin 64, indexedBlockCheck (80192 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80256_80319 :
    ∀ i : Fin 64, indexedBlockCheck (80256 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80320_80383 :
    ∀ i : Fin 64, indexedBlockCheck (80320 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79872_80383 :
    ∀ i : Fin 512, indexedBlockCheck (79872 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (79872 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 79872 0 64 h0 checkBlocks_79872_79935
  have h128 := extendCertifiedSegment 79872 64 64 h64 checkBlocks_79936_79999
  have h192 := extendCertifiedSegment 79872 128 64 h128 checkBlocks_80000_80063
  have h256 := extendCertifiedSegment 79872 192 64 h192 checkBlocks_80064_80127
  have h320 := extendCertifiedSegment 79872 256 64 h256 checkBlocks_80128_80191
  have h384 := extendCertifiedSegment 79872 320 64 h320 checkBlocks_80192_80255
  have h448 := extendCertifiedSegment 79872 384 64 h384 checkBlocks_80256_80319
  have h512 := extendCertifiedSegment 79872 448 64 h448 checkBlocks_80320_80383
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_80384_80447 :
    ∀ i : Fin 64, indexedBlockCheck (80384 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80448_80511 :
    ∀ i : Fin 64, indexedBlockCheck (80448 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80512_80575 :
    ∀ i : Fin 64, indexedBlockCheck (80512 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80576_80639 :
    ∀ i : Fin 64, indexedBlockCheck (80576 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80640_80703 :
    ∀ i : Fin 64, indexedBlockCheck (80640 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80704_80767 :
    ∀ i : Fin 64, indexedBlockCheck (80704 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80768_80831 :
    ∀ i : Fin 64, indexedBlockCheck (80768 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80832_80895 :
    ∀ i : Fin 64, indexedBlockCheck (80832 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80384_80895 :
    ∀ i : Fin 512, indexedBlockCheck (80384 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (80384 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 80384 0 64 h0 checkBlocks_80384_80447
  have h128 := extendCertifiedSegment 80384 64 64 h64 checkBlocks_80448_80511
  have h192 := extendCertifiedSegment 80384 128 64 h128 checkBlocks_80512_80575
  have h256 := extendCertifiedSegment 80384 192 64 h192 checkBlocks_80576_80639
  have h320 := extendCertifiedSegment 80384 256 64 h256 checkBlocks_80640_80703
  have h384 := extendCertifiedSegment 80384 320 64 h320 checkBlocks_80704_80767
  have h448 := extendCertifiedSegment 80384 384 64 h384 checkBlocks_80768_80831
  have h512 := extendCertifiedSegment 80384 448 64 h448 checkBlocks_80832_80895
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [78848, 80896) passes the packed checker. -/
public theorem blocks_in_78848_80896 :
    ∀ i : Fin 2048, indexedBlockCheck (78848 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (78848 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 78848 0 512 h0 checkBlocks_78848_79359
  have h1024 := extendCertifiedSegment 78848 512 512 h512 checkBlocks_79360_79871
  have h1536 := extendCertifiedSegment 78848 1024 512 h1024 checkBlocks_79872_80383
  have h2048 := extendCertifiedSegment 78848 1536 512 h1536 checkBlocks_80384_80895
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
