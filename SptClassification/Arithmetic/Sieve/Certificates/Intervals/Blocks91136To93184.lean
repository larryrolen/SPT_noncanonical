/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

-- Build-order dependency: keep at most two large certificate modules in flight.
import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks87040To89088

/-! # Certified checker blocks from 91136 through 93183 -/

public section

namespace SptClassification.Sieve

private theorem checkBlocks_91136_91199 :
    ∀ i : Fin 64, indexedBlockCheck (91136 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_91200_91263 :
    ∀ i : Fin 64, indexedBlockCheck (91200 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_91264_91327 :
    ∀ i : Fin 64, indexedBlockCheck (91264 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_91328_91391 :
    ∀ i : Fin 64, indexedBlockCheck (91328 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_91392_91455 :
    ∀ i : Fin 64, indexedBlockCheck (91392 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_91456_91519 :
    ∀ i : Fin 64, indexedBlockCheck (91456 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_91520_91583 :
    ∀ i : Fin 64, indexedBlockCheck (91520 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_91584_91647 :
    ∀ i : Fin 64, indexedBlockCheck (91584 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_91136_91647 :
    ∀ i : Fin 512, indexedBlockCheck (91136 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (91136 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 91136 0 64 h0 checkBlocks_91136_91199
  have h128 := extendCertifiedSegment 91136 64 64 h64 checkBlocks_91200_91263
  have h192 := extendCertifiedSegment 91136 128 64 h128 checkBlocks_91264_91327
  have h256 := extendCertifiedSegment 91136 192 64 h192 checkBlocks_91328_91391
  have h320 := extendCertifiedSegment 91136 256 64 h256 checkBlocks_91392_91455
  have h384 := extendCertifiedSegment 91136 320 64 h320 checkBlocks_91456_91519
  have h448 := extendCertifiedSegment 91136 384 64 h384 checkBlocks_91520_91583
  have h512 := extendCertifiedSegment 91136 448 64 h448 checkBlocks_91584_91647
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_91648_91711 :
    ∀ i : Fin 64, indexedBlockCheck (91648 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_91712_91775 :
    ∀ i : Fin 64, indexedBlockCheck (91712 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_91776_91839 :
    ∀ i : Fin 64, indexedBlockCheck (91776 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_91840_91903 :
    ∀ i : Fin 64, indexedBlockCheck (91840 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_91904_91967 :
    ∀ i : Fin 64, indexedBlockCheck (91904 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_91968_92031 :
    ∀ i : Fin 64, indexedBlockCheck (91968 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_92032_92095 :
    ∀ i : Fin 64, indexedBlockCheck (92032 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_92096_92159 :
    ∀ i : Fin 64, indexedBlockCheck (92096 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_91648_92159 :
    ∀ i : Fin 512, indexedBlockCheck (91648 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (91648 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 91648 0 64 h0 checkBlocks_91648_91711
  have h128 := extendCertifiedSegment 91648 64 64 h64 checkBlocks_91712_91775
  have h192 := extendCertifiedSegment 91648 128 64 h128 checkBlocks_91776_91839
  have h256 := extendCertifiedSegment 91648 192 64 h192 checkBlocks_91840_91903
  have h320 := extendCertifiedSegment 91648 256 64 h256 checkBlocks_91904_91967
  have h384 := extendCertifiedSegment 91648 320 64 h320 checkBlocks_91968_92031
  have h448 := extendCertifiedSegment 91648 384 64 h384 checkBlocks_92032_92095
  have h512 := extendCertifiedSegment 91648 448 64 h448 checkBlocks_92096_92159
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_92160_92223 :
    ∀ i : Fin 64, indexedBlockCheck (92160 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_92224_92287 :
    ∀ i : Fin 64, indexedBlockCheck (92224 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_92288_92351 :
    ∀ i : Fin 64, indexedBlockCheck (92288 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_92352_92415 :
    ∀ i : Fin 64, indexedBlockCheck (92352 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_92416_92479 :
    ∀ i : Fin 64, indexedBlockCheck (92416 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_92480_92543 :
    ∀ i : Fin 64, indexedBlockCheck (92480 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_92544_92607 :
    ∀ i : Fin 64, indexedBlockCheck (92544 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_92608_92671 :
    ∀ i : Fin 64, indexedBlockCheck (92608 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_92160_92671 :
    ∀ i : Fin 512, indexedBlockCheck (92160 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (92160 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 92160 0 64 h0 checkBlocks_92160_92223
  have h128 := extendCertifiedSegment 92160 64 64 h64 checkBlocks_92224_92287
  have h192 := extendCertifiedSegment 92160 128 64 h128 checkBlocks_92288_92351
  have h256 := extendCertifiedSegment 92160 192 64 h192 checkBlocks_92352_92415
  have h320 := extendCertifiedSegment 92160 256 64 h256 checkBlocks_92416_92479
  have h384 := extendCertifiedSegment 92160 320 64 h320 checkBlocks_92480_92543
  have h448 := extendCertifiedSegment 92160 384 64 h384 checkBlocks_92544_92607
  have h512 := extendCertifiedSegment 92160 448 64 h448 checkBlocks_92608_92671
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_92672_92735 :
    ∀ i : Fin 64, indexedBlockCheck (92672 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_92736_92799 :
    ∀ i : Fin 64, indexedBlockCheck (92736 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_92800_92863 :
    ∀ i : Fin 64, indexedBlockCheck (92800 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_92864_92927 :
    ∀ i : Fin 64, indexedBlockCheck (92864 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_92928_92991 :
    ∀ i : Fin 64, indexedBlockCheck (92928 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_92992_93055 :
    ∀ i : Fin 64, indexedBlockCheck (92992 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_93056_93119 :
    ∀ i : Fin 64, indexedBlockCheck (93056 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_93120_93183 :
    ∀ i : Fin 64, indexedBlockCheck (93120 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_92672_93183 :
    ∀ i : Fin 512, indexedBlockCheck (92672 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (92672 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 92672 0 64 h0 checkBlocks_92672_92735
  have h128 := extendCertifiedSegment 92672 64 64 h64 checkBlocks_92736_92799
  have h192 := extendCertifiedSegment 92672 128 64 h128 checkBlocks_92800_92863
  have h256 := extendCertifiedSegment 92672 192 64 h192 checkBlocks_92864_92927
  have h320 := extendCertifiedSegment 92672 256 64 h256 checkBlocks_92928_92991
  have h384 := extendCertifiedSegment 92672 320 64 h320 checkBlocks_92992_93055
  have h448 := extendCertifiedSegment 92672 384 64 h384 checkBlocks_93056_93119
  have h512 := extendCertifiedSegment 92672 448 64 h448 checkBlocks_93120_93183
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [91136, 93184) passes the packed checker. -/
public theorem blocks_in_91136_93184 :
    ∀ i : Fin 2048, indexedBlockCheck (91136 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (91136 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 91136 0 512 h0 checkBlocks_91136_91647
  have h1024 := extendCertifiedSegment 91136 512 512 h512 checkBlocks_91648_92159
  have h1536 := extendCertifiedSegment 91136 1024 512 h1024 checkBlocks_92160_92671
  have h2048 := extendCertifiedSegment 91136 1536 512 h1536 checkBlocks_92672_93183
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
