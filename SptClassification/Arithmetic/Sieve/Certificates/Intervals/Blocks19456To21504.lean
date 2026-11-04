/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

-- Build-order dependency: keep at most two large certificate modules in flight.
import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks15360To17408

/-! # Certified checker blocks from 19456 through 21503 -/

public section

namespace SptClassification.Sieve

private theorem checkBlocks_19456_19519 :
    ∀ i : Fin 64, indexedBlockCheck (19456 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19520_19583 :
    ∀ i : Fin 64, indexedBlockCheck (19520 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19584_19647 :
    ∀ i : Fin 64, indexedBlockCheck (19584 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19648_19711 :
    ∀ i : Fin 64, indexedBlockCheck (19648 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19712_19775 :
    ∀ i : Fin 64, indexedBlockCheck (19712 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19776_19839 :
    ∀ i : Fin 64, indexedBlockCheck (19776 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19840_19903 :
    ∀ i : Fin 64, indexedBlockCheck (19840 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19904_19967 :
    ∀ i : Fin 64, indexedBlockCheck (19904 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19456_19967 :
    ∀ i : Fin 512, indexedBlockCheck (19456 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (19456 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 19456 0 64 h0 checkBlocks_19456_19519
  have h128 := extendCertifiedSegment 19456 64 64 h64 checkBlocks_19520_19583
  have h192 := extendCertifiedSegment 19456 128 64 h128 checkBlocks_19584_19647
  have h256 := extendCertifiedSegment 19456 192 64 h192 checkBlocks_19648_19711
  have h320 := extendCertifiedSegment 19456 256 64 h256 checkBlocks_19712_19775
  have h384 := extendCertifiedSegment 19456 320 64 h320 checkBlocks_19776_19839
  have h448 := extendCertifiedSegment 19456 384 64 h384 checkBlocks_19840_19903
  have h512 := extendCertifiedSegment 19456 448 64 h448 checkBlocks_19904_19967
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_19968_20031 :
    ∀ i : Fin 64, indexedBlockCheck (19968 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20032_20095 :
    ∀ i : Fin 64, indexedBlockCheck (20032 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20096_20159 :
    ∀ i : Fin 64, indexedBlockCheck (20096 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20160_20223 :
    ∀ i : Fin 64, indexedBlockCheck (20160 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20224_20287 :
    ∀ i : Fin 64, indexedBlockCheck (20224 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20288_20351 :
    ∀ i : Fin 64, indexedBlockCheck (20288 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20352_20415 :
    ∀ i : Fin 64, indexedBlockCheck (20352 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20416_20479 :
    ∀ i : Fin 64, indexedBlockCheck (20416 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19968_20479 :
    ∀ i : Fin 512, indexedBlockCheck (19968 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (19968 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 19968 0 64 h0 checkBlocks_19968_20031
  have h128 := extendCertifiedSegment 19968 64 64 h64 checkBlocks_20032_20095
  have h192 := extendCertifiedSegment 19968 128 64 h128 checkBlocks_20096_20159
  have h256 := extendCertifiedSegment 19968 192 64 h192 checkBlocks_20160_20223
  have h320 := extendCertifiedSegment 19968 256 64 h256 checkBlocks_20224_20287
  have h384 := extendCertifiedSegment 19968 320 64 h320 checkBlocks_20288_20351
  have h448 := extendCertifiedSegment 19968 384 64 h384 checkBlocks_20352_20415
  have h512 := extendCertifiedSegment 19968 448 64 h448 checkBlocks_20416_20479
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_20480_20543 :
    ∀ i : Fin 64, indexedBlockCheck (20480 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20544_20607 :
    ∀ i : Fin 64, indexedBlockCheck (20544 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20608_20671 :
    ∀ i : Fin 64, indexedBlockCheck (20608 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20672_20735 :
    ∀ i : Fin 64, indexedBlockCheck (20672 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20736_20799 :
    ∀ i : Fin 64, indexedBlockCheck (20736 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20800_20863 :
    ∀ i : Fin 64, indexedBlockCheck (20800 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20864_20927 :
    ∀ i : Fin 64, indexedBlockCheck (20864 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20928_20991 :
    ∀ i : Fin 64, indexedBlockCheck (20928 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20480_20991 :
    ∀ i : Fin 512, indexedBlockCheck (20480 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (20480 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 20480 0 64 h0 checkBlocks_20480_20543
  have h128 := extendCertifiedSegment 20480 64 64 h64 checkBlocks_20544_20607
  have h192 := extendCertifiedSegment 20480 128 64 h128 checkBlocks_20608_20671
  have h256 := extendCertifiedSegment 20480 192 64 h192 checkBlocks_20672_20735
  have h320 := extendCertifiedSegment 20480 256 64 h256 checkBlocks_20736_20799
  have h384 := extendCertifiedSegment 20480 320 64 h320 checkBlocks_20800_20863
  have h448 := extendCertifiedSegment 20480 384 64 h384 checkBlocks_20864_20927
  have h512 := extendCertifiedSegment 20480 448 64 h448 checkBlocks_20928_20991
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_20992_21055 :
    ∀ i : Fin 64, indexedBlockCheck (20992 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_21056_21119 :
    ∀ i : Fin 64, indexedBlockCheck (21056 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_21120_21183 :
    ∀ i : Fin 64, indexedBlockCheck (21120 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_21184_21247 :
    ∀ i : Fin 64, indexedBlockCheck (21184 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_21248_21311 :
    ∀ i : Fin 64, indexedBlockCheck (21248 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_21312_21375 :
    ∀ i : Fin 64, indexedBlockCheck (21312 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_21376_21439 :
    ∀ i : Fin 64, indexedBlockCheck (21376 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_21440_21503 :
    ∀ i : Fin 64, indexedBlockCheck (21440 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20992_21503 :
    ∀ i : Fin 512, indexedBlockCheck (20992 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (20992 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 20992 0 64 h0 checkBlocks_20992_21055
  have h128 := extendCertifiedSegment 20992 64 64 h64 checkBlocks_21056_21119
  have h192 := extendCertifiedSegment 20992 128 64 h128 checkBlocks_21120_21183
  have h256 := extendCertifiedSegment 20992 192 64 h192 checkBlocks_21184_21247
  have h320 := extendCertifiedSegment 20992 256 64 h256 checkBlocks_21248_21311
  have h384 := extendCertifiedSegment 20992 320 64 h320 checkBlocks_21312_21375
  have h448 := extendCertifiedSegment 20992 384 64 h384 checkBlocks_21376_21439
  have h512 := extendCertifiedSegment 20992 448 64 h448 checkBlocks_21440_21503
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [19456, 21504) passes the packed checker. -/
public theorem blocks_in_19456_21504 :
    ∀ i : Fin 2048, indexedBlockCheck (19456 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (19456 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 19456 0 512 h0 checkBlocks_19456_19967
  have h1024 := extendCertifiedSegment 19456 512 512 h512 checkBlocks_19968_20479
  have h1536 := extendCertifiedSegment 19456 1024 512 h1024 checkBlocks_20480_20991
  have h2048 := extendCertifiedSegment 19456 1536 512 h1536 checkBlocks_20992_21503
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
