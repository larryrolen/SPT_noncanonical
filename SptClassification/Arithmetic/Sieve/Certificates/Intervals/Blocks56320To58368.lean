/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

-- Build-order dependency: keep at most two large certificate modules in flight.
import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks52224To54272

/-! # Certified checker blocks from 56320 through 58367 -/

public section

namespace SptClassification.Sieve

private theorem checkBlocks_56320_56383 :
    ∀ i : Fin 64, indexedBlockCheck (56320 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_56384_56447 :
    ∀ i : Fin 64, indexedBlockCheck (56384 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_56448_56511 :
    ∀ i : Fin 64, indexedBlockCheck (56448 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_56512_56575 :
    ∀ i : Fin 64, indexedBlockCheck (56512 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_56576_56639 :
    ∀ i : Fin 64, indexedBlockCheck (56576 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_56640_56703 :
    ∀ i : Fin 64, indexedBlockCheck (56640 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_56704_56767 :
    ∀ i : Fin 64, indexedBlockCheck (56704 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_56768_56831 :
    ∀ i : Fin 64, indexedBlockCheck (56768 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_56320_56831 :
    ∀ i : Fin 512, indexedBlockCheck (56320 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (56320 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 56320 0 64 h0 checkBlocks_56320_56383
  have h128 := extendCertifiedSegment 56320 64 64 h64 checkBlocks_56384_56447
  have h192 := extendCertifiedSegment 56320 128 64 h128 checkBlocks_56448_56511
  have h256 := extendCertifiedSegment 56320 192 64 h192 checkBlocks_56512_56575
  have h320 := extendCertifiedSegment 56320 256 64 h256 checkBlocks_56576_56639
  have h384 := extendCertifiedSegment 56320 320 64 h320 checkBlocks_56640_56703
  have h448 := extendCertifiedSegment 56320 384 64 h384 checkBlocks_56704_56767
  have h512 := extendCertifiedSegment 56320 448 64 h448 checkBlocks_56768_56831
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_56832_56895 :
    ∀ i : Fin 64, indexedBlockCheck (56832 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_56896_56959 :
    ∀ i : Fin 64, indexedBlockCheck (56896 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_56960_57023 :
    ∀ i : Fin 64, indexedBlockCheck (56960 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57024_57087 :
    ∀ i : Fin 64, indexedBlockCheck (57024 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57088_57151 :
    ∀ i : Fin 64, indexedBlockCheck (57088 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57152_57215 :
    ∀ i : Fin 64, indexedBlockCheck (57152 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57216_57279 :
    ∀ i : Fin 64, indexedBlockCheck (57216 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57280_57343 :
    ∀ i : Fin 64, indexedBlockCheck (57280 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_56832_57343 :
    ∀ i : Fin 512, indexedBlockCheck (56832 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (56832 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 56832 0 64 h0 checkBlocks_56832_56895
  have h128 := extendCertifiedSegment 56832 64 64 h64 checkBlocks_56896_56959
  have h192 := extendCertifiedSegment 56832 128 64 h128 checkBlocks_56960_57023
  have h256 := extendCertifiedSegment 56832 192 64 h192 checkBlocks_57024_57087
  have h320 := extendCertifiedSegment 56832 256 64 h256 checkBlocks_57088_57151
  have h384 := extendCertifiedSegment 56832 320 64 h320 checkBlocks_57152_57215
  have h448 := extendCertifiedSegment 56832 384 64 h384 checkBlocks_57216_57279
  have h512 := extendCertifiedSegment 56832 448 64 h448 checkBlocks_57280_57343
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_57344_57407 :
    ∀ i : Fin 64, indexedBlockCheck (57344 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57408_57471 :
    ∀ i : Fin 64, indexedBlockCheck (57408 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57472_57535 :
    ∀ i : Fin 64, indexedBlockCheck (57472 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57536_57599 :
    ∀ i : Fin 64, indexedBlockCheck (57536 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57600_57663 :
    ∀ i : Fin 64, indexedBlockCheck (57600 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57664_57727 :
    ∀ i : Fin 64, indexedBlockCheck (57664 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57728_57791 :
    ∀ i : Fin 64, indexedBlockCheck (57728 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57792_57855 :
    ∀ i : Fin 64, indexedBlockCheck (57792 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57344_57855 :
    ∀ i : Fin 512, indexedBlockCheck (57344 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (57344 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 57344 0 64 h0 checkBlocks_57344_57407
  have h128 := extendCertifiedSegment 57344 64 64 h64 checkBlocks_57408_57471
  have h192 := extendCertifiedSegment 57344 128 64 h128 checkBlocks_57472_57535
  have h256 := extendCertifiedSegment 57344 192 64 h192 checkBlocks_57536_57599
  have h320 := extendCertifiedSegment 57344 256 64 h256 checkBlocks_57600_57663
  have h384 := extendCertifiedSegment 57344 320 64 h320 checkBlocks_57664_57727
  have h448 := extendCertifiedSegment 57344 384 64 h384 checkBlocks_57728_57791
  have h512 := extendCertifiedSegment 57344 448 64 h448 checkBlocks_57792_57855
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_57856_57919 :
    ∀ i : Fin 64, indexedBlockCheck (57856 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57920_57983 :
    ∀ i : Fin 64, indexedBlockCheck (57920 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57984_58047 :
    ∀ i : Fin 64, indexedBlockCheck (57984 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58048_58111 :
    ∀ i : Fin 64, indexedBlockCheck (58048 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58112_58175 :
    ∀ i : Fin 64, indexedBlockCheck (58112 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58176_58239 :
    ∀ i : Fin 64, indexedBlockCheck (58176 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58240_58303 :
    ∀ i : Fin 64, indexedBlockCheck (58240 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58304_58367 :
    ∀ i : Fin 64, indexedBlockCheck (58304 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57856_58367 :
    ∀ i : Fin 512, indexedBlockCheck (57856 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (57856 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 57856 0 64 h0 checkBlocks_57856_57919
  have h128 := extendCertifiedSegment 57856 64 64 h64 checkBlocks_57920_57983
  have h192 := extendCertifiedSegment 57856 128 64 h128 checkBlocks_57984_58047
  have h256 := extendCertifiedSegment 57856 192 64 h192 checkBlocks_58048_58111
  have h320 := extendCertifiedSegment 57856 256 64 h256 checkBlocks_58112_58175
  have h384 := extendCertifiedSegment 57856 320 64 h320 checkBlocks_58176_58239
  have h448 := extendCertifiedSegment 57856 384 64 h384 checkBlocks_58240_58303
  have h512 := extendCertifiedSegment 57856 448 64 h448 checkBlocks_58304_58367
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [56320, 58368) passes the packed checker. -/
public theorem blocks_in_56320_58368 :
    ∀ i : Fin 2048, indexedBlockCheck (56320 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (56320 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 56320 0 512 h0 checkBlocks_56320_56831
  have h1024 := extendCertifiedSegment 56320 512 512 h512 checkBlocks_56832_57343
  have h1536 := extendCertifiedSegment 56320 1024 512 h1024 checkBlocks_57344_57855
  have h2048 := extendCertifiedSegment 56320 1536 512 h1536 checkBlocks_57856_58367
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
