/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

-- Build-order dependency: keep at most two large certificate modules in flight.
import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks27648To29696

/-! # Certified checker blocks from 31744 through 33791 -/

public section

namespace SptClassification.Sieve

private theorem checkBlocks_31744_31807 :
    ∀ i : Fin 64, indexedBlockCheck (31744 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_31808_31871 :
    ∀ i : Fin 64, indexedBlockCheck (31808 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_31872_31935 :
    ∀ i : Fin 64, indexedBlockCheck (31872 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_31936_31999 :
    ∀ i : Fin 64, indexedBlockCheck (31936 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32000_32063 :
    ∀ i : Fin 64, indexedBlockCheck (32000 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32064_32127 :
    ∀ i : Fin 64, indexedBlockCheck (32064 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32128_32191 :
    ∀ i : Fin 64, indexedBlockCheck (32128 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32192_32255 :
    ∀ i : Fin 64, indexedBlockCheck (32192 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_31744_32255 :
    ∀ i : Fin 512, indexedBlockCheck (31744 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (31744 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 31744 0 64 h0 checkBlocks_31744_31807
  have h128 := extendCertifiedSegment 31744 64 64 h64 checkBlocks_31808_31871
  have h192 := extendCertifiedSegment 31744 128 64 h128 checkBlocks_31872_31935
  have h256 := extendCertifiedSegment 31744 192 64 h192 checkBlocks_31936_31999
  have h320 := extendCertifiedSegment 31744 256 64 h256 checkBlocks_32000_32063
  have h384 := extendCertifiedSegment 31744 320 64 h320 checkBlocks_32064_32127
  have h448 := extendCertifiedSegment 31744 384 64 h384 checkBlocks_32128_32191
  have h512 := extendCertifiedSegment 31744 448 64 h448 checkBlocks_32192_32255
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_32256_32319 :
    ∀ i : Fin 64, indexedBlockCheck (32256 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32320_32383 :
    ∀ i : Fin 64, indexedBlockCheck (32320 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32384_32447 :
    ∀ i : Fin 64, indexedBlockCheck (32384 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32448_32511 :
    ∀ i : Fin 64, indexedBlockCheck (32448 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32512_32575 :
    ∀ i : Fin 64, indexedBlockCheck (32512 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32576_32639 :
    ∀ i : Fin 64, indexedBlockCheck (32576 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32640_32703 :
    ∀ i : Fin 64, indexedBlockCheck (32640 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32704_32767 :
    ∀ i : Fin 64, indexedBlockCheck (32704 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32256_32767 :
    ∀ i : Fin 512, indexedBlockCheck (32256 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (32256 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 32256 0 64 h0 checkBlocks_32256_32319
  have h128 := extendCertifiedSegment 32256 64 64 h64 checkBlocks_32320_32383
  have h192 := extendCertifiedSegment 32256 128 64 h128 checkBlocks_32384_32447
  have h256 := extendCertifiedSegment 32256 192 64 h192 checkBlocks_32448_32511
  have h320 := extendCertifiedSegment 32256 256 64 h256 checkBlocks_32512_32575
  have h384 := extendCertifiedSegment 32256 320 64 h320 checkBlocks_32576_32639
  have h448 := extendCertifiedSegment 32256 384 64 h384 checkBlocks_32640_32703
  have h512 := extendCertifiedSegment 32256 448 64 h448 checkBlocks_32704_32767
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_32768_32831 :
    ∀ i : Fin 64, indexedBlockCheck (32768 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32832_32895 :
    ∀ i : Fin 64, indexedBlockCheck (32832 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32896_32959 :
    ∀ i : Fin 64, indexedBlockCheck (32896 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32960_33023 :
    ∀ i : Fin 64, indexedBlockCheck (32960 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33024_33087 :
    ∀ i : Fin 64, indexedBlockCheck (33024 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33088_33151 :
    ∀ i : Fin 64, indexedBlockCheck (33088 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33152_33215 :
    ∀ i : Fin 64, indexedBlockCheck (33152 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33216_33279 :
    ∀ i : Fin 64, indexedBlockCheck (33216 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32768_33279 :
    ∀ i : Fin 512, indexedBlockCheck (32768 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (32768 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 32768 0 64 h0 checkBlocks_32768_32831
  have h128 := extendCertifiedSegment 32768 64 64 h64 checkBlocks_32832_32895
  have h192 := extendCertifiedSegment 32768 128 64 h128 checkBlocks_32896_32959
  have h256 := extendCertifiedSegment 32768 192 64 h192 checkBlocks_32960_33023
  have h320 := extendCertifiedSegment 32768 256 64 h256 checkBlocks_33024_33087
  have h384 := extendCertifiedSegment 32768 320 64 h320 checkBlocks_33088_33151
  have h448 := extendCertifiedSegment 32768 384 64 h384 checkBlocks_33152_33215
  have h512 := extendCertifiedSegment 32768 448 64 h448 checkBlocks_33216_33279
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_33280_33343 :
    ∀ i : Fin 64, indexedBlockCheck (33280 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33344_33407 :
    ∀ i : Fin 64, indexedBlockCheck (33344 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33408_33471 :
    ∀ i : Fin 64, indexedBlockCheck (33408 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33472_33535 :
    ∀ i : Fin 64, indexedBlockCheck (33472 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33536_33599 :
    ∀ i : Fin 64, indexedBlockCheck (33536 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33600_33663 :
    ∀ i : Fin 64, indexedBlockCheck (33600 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33664_33727 :
    ∀ i : Fin 64, indexedBlockCheck (33664 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33728_33791 :
    ∀ i : Fin 64, indexedBlockCheck (33728 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33280_33791 :
    ∀ i : Fin 512, indexedBlockCheck (33280 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (33280 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 33280 0 64 h0 checkBlocks_33280_33343
  have h128 := extendCertifiedSegment 33280 64 64 h64 checkBlocks_33344_33407
  have h192 := extendCertifiedSegment 33280 128 64 h128 checkBlocks_33408_33471
  have h256 := extendCertifiedSegment 33280 192 64 h192 checkBlocks_33472_33535
  have h320 := extendCertifiedSegment 33280 256 64 h256 checkBlocks_33536_33599
  have h384 := extendCertifiedSegment 33280 320 64 h320 checkBlocks_33600_33663
  have h448 := extendCertifiedSegment 33280 384 64 h384 checkBlocks_33664_33727
  have h512 := extendCertifiedSegment 33280 448 64 h448 checkBlocks_33728_33791
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [31744, 33792) passes the packed checker. -/
public theorem blocks_in_31744_33792 :
    ∀ i : Fin 2048, indexedBlockCheck (31744 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (31744 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 31744 0 512 h0 checkBlocks_31744_32255
  have h1024 := extendCertifiedSegment 31744 512 512 h512 checkBlocks_32256_32767
  have h1536 := extendCertifiedSegment 31744 1024 512 h1024 checkBlocks_32768_33279
  have h2048 := extendCertifiedSegment 31744 1536 512 h1536 checkBlocks_33280_33791
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
