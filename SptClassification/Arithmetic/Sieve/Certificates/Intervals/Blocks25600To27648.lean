/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 25600 through 27647 -/

public section

namespace SptClassification.Sieve

-- Bound memory by checking small certificate pieces sequentially.
set_option Elab.async false

private theorem checkBlocks_25600_25663_part0 :
    ∀ i : Fin 32, indexedBlockCheck (25600 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_25600_25663_part1 :
    ∀ i : Fin 32, indexedBlockCheck (25632 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_25600_25663 :
    ∀ i : Fin 64, indexedBlockCheck (25600 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (25600 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 25600 0 32 h0 checkBlocks_25600_25663_part0
  have h64 := extendCertifiedSegment 25600 32 32 h32 checkBlocks_25600_25663_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_25664_25727_part0 :
    ∀ i : Fin 32, indexedBlockCheck (25664 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_25664_25727_part1 :
    ∀ i : Fin 32, indexedBlockCheck (25696 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_25664_25727 :
    ∀ i : Fin 64, indexedBlockCheck (25664 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (25664 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 25664 0 32 h0 checkBlocks_25664_25727_part0
  have h64 := extendCertifiedSegment 25664 32 32 h32 checkBlocks_25664_25727_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_25728_25791_part0 :
    ∀ i : Fin 32, indexedBlockCheck (25728 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_25728_25791_part1 :
    ∀ i : Fin 32, indexedBlockCheck (25760 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_25728_25791 :
    ∀ i : Fin 64, indexedBlockCheck (25728 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (25728 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 25728 0 32 h0 checkBlocks_25728_25791_part0
  have h64 := extendCertifiedSegment 25728 32 32 h32 checkBlocks_25728_25791_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_25792_25855_part0 :
    ∀ i : Fin 32, indexedBlockCheck (25792 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_25792_25855_part1 :
    ∀ i : Fin 32, indexedBlockCheck (25824 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_25792_25855 :
    ∀ i : Fin 64, indexedBlockCheck (25792 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (25792 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 25792 0 32 h0 checkBlocks_25792_25855_part0
  have h64 := extendCertifiedSegment 25792 32 32 h32 checkBlocks_25792_25855_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_25856_25919_part0 :
    ∀ i : Fin 32, indexedBlockCheck (25856 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_25856_25919_part1 :
    ∀ i : Fin 32, indexedBlockCheck (25888 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_25856_25919 :
    ∀ i : Fin 64, indexedBlockCheck (25856 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (25856 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 25856 0 32 h0 checkBlocks_25856_25919_part0
  have h64 := extendCertifiedSegment 25856 32 32 h32 checkBlocks_25856_25919_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_25920_25983_part0 :
    ∀ i : Fin 32, indexedBlockCheck (25920 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_25920_25983_part1 :
    ∀ i : Fin 32, indexedBlockCheck (25952 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_25920_25983 :
    ∀ i : Fin 64, indexedBlockCheck (25920 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (25920 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 25920 0 32 h0 checkBlocks_25920_25983_part0
  have h64 := extendCertifiedSegment 25920 32 32 h32 checkBlocks_25920_25983_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_25984_26047_part0 :
    ∀ i : Fin 32, indexedBlockCheck (25984 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_25984_26047_part1 :
    ∀ i : Fin 32, indexedBlockCheck (26016 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_25984_26047 :
    ∀ i : Fin 64, indexedBlockCheck (25984 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (25984 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 25984 0 32 h0 checkBlocks_25984_26047_part0
  have h64 := extendCertifiedSegment 25984 32 32 h32 checkBlocks_25984_26047_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_26048_26111_part0 :
    ∀ i : Fin 32, indexedBlockCheck (26048 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26048_26111_part1 :
    ∀ i : Fin 32, indexedBlockCheck (26080 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26048_26111 :
    ∀ i : Fin 64, indexedBlockCheck (26048 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (26048 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 26048 0 32 h0 checkBlocks_26048_26111_part0
  have h64 := extendCertifiedSegment 26048 32 32 h32 checkBlocks_26048_26111_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_25600_26111 :
    ∀ i : Fin 512, indexedBlockCheck (25600 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (25600 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 25600 0 64 h0 checkBlocks_25600_25663
  have h128 := extendCertifiedSegment 25600 64 64 h64 checkBlocks_25664_25727
  have h192 := extendCertifiedSegment 25600 128 64 h128 checkBlocks_25728_25791
  have h256 := extendCertifiedSegment 25600 192 64 h192 checkBlocks_25792_25855
  have h320 := extendCertifiedSegment 25600 256 64 h256 checkBlocks_25856_25919
  have h384 := extendCertifiedSegment 25600 320 64 h320 checkBlocks_25920_25983
  have h448 := extendCertifiedSegment 25600 384 64 h384 checkBlocks_25984_26047
  have h512 := extendCertifiedSegment 25600 448 64 h448 checkBlocks_26048_26111
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_26112_26175_part0 :
    ∀ i : Fin 32, indexedBlockCheck (26112 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26112_26175_part1 :
    ∀ i : Fin 32, indexedBlockCheck (26144 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26112_26175 :
    ∀ i : Fin 64, indexedBlockCheck (26112 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (26112 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 26112 0 32 h0 checkBlocks_26112_26175_part0
  have h64 := extendCertifiedSegment 26112 32 32 h32 checkBlocks_26112_26175_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_26176_26239_part0 :
    ∀ i : Fin 32, indexedBlockCheck (26176 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26176_26239_part1 :
    ∀ i : Fin 32, indexedBlockCheck (26208 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26176_26239 :
    ∀ i : Fin 64, indexedBlockCheck (26176 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (26176 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 26176 0 32 h0 checkBlocks_26176_26239_part0
  have h64 := extendCertifiedSegment 26176 32 32 h32 checkBlocks_26176_26239_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_26240_26303_part0 :
    ∀ i : Fin 32, indexedBlockCheck (26240 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26240_26303_part1 :
    ∀ i : Fin 32, indexedBlockCheck (26272 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26240_26303 :
    ∀ i : Fin 64, indexedBlockCheck (26240 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (26240 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 26240 0 32 h0 checkBlocks_26240_26303_part0
  have h64 := extendCertifiedSegment 26240 32 32 h32 checkBlocks_26240_26303_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_26304_26367_part0 :
    ∀ i : Fin 32, indexedBlockCheck (26304 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26304_26367_part1 :
    ∀ i : Fin 32, indexedBlockCheck (26336 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26304_26367 :
    ∀ i : Fin 64, indexedBlockCheck (26304 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (26304 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 26304 0 32 h0 checkBlocks_26304_26367_part0
  have h64 := extendCertifiedSegment 26304 32 32 h32 checkBlocks_26304_26367_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_26368_26431_part0 :
    ∀ i : Fin 32, indexedBlockCheck (26368 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26368_26431_part1 :
    ∀ i : Fin 32, indexedBlockCheck (26400 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26368_26431 :
    ∀ i : Fin 64, indexedBlockCheck (26368 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (26368 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 26368 0 32 h0 checkBlocks_26368_26431_part0
  have h64 := extendCertifiedSegment 26368 32 32 h32 checkBlocks_26368_26431_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_26432_26495_part0 :
    ∀ i : Fin 32, indexedBlockCheck (26432 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26432_26495_part1 :
    ∀ i : Fin 32, indexedBlockCheck (26464 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26432_26495 :
    ∀ i : Fin 64, indexedBlockCheck (26432 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (26432 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 26432 0 32 h0 checkBlocks_26432_26495_part0
  have h64 := extendCertifiedSegment 26432 32 32 h32 checkBlocks_26432_26495_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_26496_26559_part0 :
    ∀ i : Fin 32, indexedBlockCheck (26496 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26496_26559_part1 :
    ∀ i : Fin 32, indexedBlockCheck (26528 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26496_26559 :
    ∀ i : Fin 64, indexedBlockCheck (26496 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (26496 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 26496 0 32 h0 checkBlocks_26496_26559_part0
  have h64 := extendCertifiedSegment 26496 32 32 h32 checkBlocks_26496_26559_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_26560_26623_part0 :
    ∀ i : Fin 32, indexedBlockCheck (26560 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26560_26623_part1 :
    ∀ i : Fin 32, indexedBlockCheck (26592 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26560_26623 :
    ∀ i : Fin 64, indexedBlockCheck (26560 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (26560 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 26560 0 32 h0 checkBlocks_26560_26623_part0
  have h64 := extendCertifiedSegment 26560 32 32 h32 checkBlocks_26560_26623_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_26112_26623 :
    ∀ i : Fin 512, indexedBlockCheck (26112 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (26112 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 26112 0 64 h0 checkBlocks_26112_26175
  have h128 := extendCertifiedSegment 26112 64 64 h64 checkBlocks_26176_26239
  have h192 := extendCertifiedSegment 26112 128 64 h128 checkBlocks_26240_26303
  have h256 := extendCertifiedSegment 26112 192 64 h192 checkBlocks_26304_26367
  have h320 := extendCertifiedSegment 26112 256 64 h256 checkBlocks_26368_26431
  have h384 := extendCertifiedSegment 26112 320 64 h320 checkBlocks_26432_26495
  have h448 := extendCertifiedSegment 26112 384 64 h384 checkBlocks_26496_26559
  have h512 := extendCertifiedSegment 26112 448 64 h448 checkBlocks_26560_26623
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_26624_26687_part0 :
    ∀ i : Fin 32, indexedBlockCheck (26624 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26624_26687_part1 :
    ∀ i : Fin 32, indexedBlockCheck (26656 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26624_26687 :
    ∀ i : Fin 64, indexedBlockCheck (26624 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (26624 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 26624 0 32 h0 checkBlocks_26624_26687_part0
  have h64 := extendCertifiedSegment 26624 32 32 h32 checkBlocks_26624_26687_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_26688_26751_part0 :
    ∀ i : Fin 32, indexedBlockCheck (26688 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26688_26751_part1 :
    ∀ i : Fin 32, indexedBlockCheck (26720 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26688_26751 :
    ∀ i : Fin 64, indexedBlockCheck (26688 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (26688 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 26688 0 32 h0 checkBlocks_26688_26751_part0
  have h64 := extendCertifiedSegment 26688 32 32 h32 checkBlocks_26688_26751_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_26752_26815_part0 :
    ∀ i : Fin 32, indexedBlockCheck (26752 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26752_26815_part1 :
    ∀ i : Fin 32, indexedBlockCheck (26784 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26752_26815 :
    ∀ i : Fin 64, indexedBlockCheck (26752 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (26752 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 26752 0 32 h0 checkBlocks_26752_26815_part0
  have h64 := extendCertifiedSegment 26752 32 32 h32 checkBlocks_26752_26815_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_26816_26879_part0 :
    ∀ i : Fin 32, indexedBlockCheck (26816 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26816_26879_part1 :
    ∀ i : Fin 32, indexedBlockCheck (26848 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26816_26879 :
    ∀ i : Fin 64, indexedBlockCheck (26816 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (26816 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 26816 0 32 h0 checkBlocks_26816_26879_part0
  have h64 := extendCertifiedSegment 26816 32 32 h32 checkBlocks_26816_26879_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_26880_26943_part0 :
    ∀ i : Fin 32, indexedBlockCheck (26880 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26880_26943_part1 :
    ∀ i : Fin 32, indexedBlockCheck (26912 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26880_26943 :
    ∀ i : Fin 64, indexedBlockCheck (26880 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (26880 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 26880 0 32 h0 checkBlocks_26880_26943_part0
  have h64 := extendCertifiedSegment 26880 32 32 h32 checkBlocks_26880_26943_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_26944_27007_part0 :
    ∀ i : Fin 32, indexedBlockCheck (26944 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26944_27007_part1 :
    ∀ i : Fin 32, indexedBlockCheck (26976 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26944_27007 :
    ∀ i : Fin 64, indexedBlockCheck (26944 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (26944 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 26944 0 32 h0 checkBlocks_26944_27007_part0
  have h64 := extendCertifiedSegment 26944 32 32 h32 checkBlocks_26944_27007_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_27008_27071_part0 :
    ∀ i : Fin 32, indexedBlockCheck (27008 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_27008_27071_part1 :
    ∀ i : Fin 32, indexedBlockCheck (27040 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_27008_27071 :
    ∀ i : Fin 64, indexedBlockCheck (27008 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (27008 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 27008 0 32 h0 checkBlocks_27008_27071_part0
  have h64 := extendCertifiedSegment 27008 32 32 h32 checkBlocks_27008_27071_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_27072_27135_part0 :
    ∀ i : Fin 32, indexedBlockCheck (27072 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_27072_27135_part1 :
    ∀ i : Fin 32, indexedBlockCheck (27104 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_27072_27135 :
    ∀ i : Fin 64, indexedBlockCheck (27072 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (27072 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 27072 0 32 h0 checkBlocks_27072_27135_part0
  have h64 := extendCertifiedSegment 27072 32 32 h32 checkBlocks_27072_27135_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_26624_27135 :
    ∀ i : Fin 512, indexedBlockCheck (26624 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (26624 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 26624 0 64 h0 checkBlocks_26624_26687
  have h128 := extendCertifiedSegment 26624 64 64 h64 checkBlocks_26688_26751
  have h192 := extendCertifiedSegment 26624 128 64 h128 checkBlocks_26752_26815
  have h256 := extendCertifiedSegment 26624 192 64 h192 checkBlocks_26816_26879
  have h320 := extendCertifiedSegment 26624 256 64 h256 checkBlocks_26880_26943
  have h384 := extendCertifiedSegment 26624 320 64 h320 checkBlocks_26944_27007
  have h448 := extendCertifiedSegment 26624 384 64 h384 checkBlocks_27008_27071
  have h512 := extendCertifiedSegment 26624 448 64 h448 checkBlocks_27072_27135
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_27136_27199_part0 :
    ∀ i : Fin 32, indexedBlockCheck (27136 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_27136_27199_part1 :
    ∀ i : Fin 32, indexedBlockCheck (27168 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_27136_27199 :
    ∀ i : Fin 64, indexedBlockCheck (27136 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (27136 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 27136 0 32 h0 checkBlocks_27136_27199_part0
  have h64 := extendCertifiedSegment 27136 32 32 h32 checkBlocks_27136_27199_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_27200_27263_part0 :
    ∀ i : Fin 32, indexedBlockCheck (27200 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_27200_27263_part1 :
    ∀ i : Fin 32, indexedBlockCheck (27232 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_27200_27263 :
    ∀ i : Fin 64, indexedBlockCheck (27200 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (27200 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 27200 0 32 h0 checkBlocks_27200_27263_part0
  have h64 := extendCertifiedSegment 27200 32 32 h32 checkBlocks_27200_27263_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_27264_27327_part0 :
    ∀ i : Fin 32, indexedBlockCheck (27264 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_27264_27327_part1 :
    ∀ i : Fin 32, indexedBlockCheck (27296 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_27264_27327 :
    ∀ i : Fin 64, indexedBlockCheck (27264 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (27264 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 27264 0 32 h0 checkBlocks_27264_27327_part0
  have h64 := extendCertifiedSegment 27264 32 32 h32 checkBlocks_27264_27327_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_27328_27391_part0 :
    ∀ i : Fin 32, indexedBlockCheck (27328 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_27328_27391_part1 :
    ∀ i : Fin 32, indexedBlockCheck (27360 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_27328_27391 :
    ∀ i : Fin 64, indexedBlockCheck (27328 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (27328 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 27328 0 32 h0 checkBlocks_27328_27391_part0
  have h64 := extendCertifiedSegment 27328 32 32 h32 checkBlocks_27328_27391_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_27392_27455_part0 :
    ∀ i : Fin 32, indexedBlockCheck (27392 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_27392_27455_part1 :
    ∀ i : Fin 32, indexedBlockCheck (27424 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_27392_27455 :
    ∀ i : Fin 64, indexedBlockCheck (27392 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (27392 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 27392 0 32 h0 checkBlocks_27392_27455_part0
  have h64 := extendCertifiedSegment 27392 32 32 h32 checkBlocks_27392_27455_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_27456_27519_part0 :
    ∀ i : Fin 32, indexedBlockCheck (27456 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_27456_27519_part1 :
    ∀ i : Fin 32, indexedBlockCheck (27488 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_27456_27519 :
    ∀ i : Fin 64, indexedBlockCheck (27456 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (27456 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 27456 0 32 h0 checkBlocks_27456_27519_part0
  have h64 := extendCertifiedSegment 27456 32 32 h32 checkBlocks_27456_27519_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_27520_27583_part0 :
    ∀ i : Fin 32, indexedBlockCheck (27520 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_27520_27583_part1 :
    ∀ i : Fin 32, indexedBlockCheck (27552 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_27520_27583 :
    ∀ i : Fin 64, indexedBlockCheck (27520 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (27520 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 27520 0 32 h0 checkBlocks_27520_27583_part0
  have h64 := extendCertifiedSegment 27520 32 32 h32 checkBlocks_27520_27583_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_27584_27647_part0 :
    ∀ i : Fin 32, indexedBlockCheck (27584 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_27584_27647_part1 :
    ∀ i : Fin 32, indexedBlockCheck (27616 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_27584_27647 :
    ∀ i : Fin 64, indexedBlockCheck (27584 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (27584 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 27584 0 32 h0 checkBlocks_27584_27647_part0
  have h64 := extendCertifiedSegment 27584 32 32 h32 checkBlocks_27584_27647_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_27136_27647 :
    ∀ i : Fin 512, indexedBlockCheck (27136 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (27136 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 27136 0 64 h0 checkBlocks_27136_27199
  have h128 := extendCertifiedSegment 27136 64 64 h64 checkBlocks_27200_27263
  have h192 := extendCertifiedSegment 27136 128 64 h128 checkBlocks_27264_27327
  have h256 := extendCertifiedSegment 27136 192 64 h192 checkBlocks_27328_27391
  have h320 := extendCertifiedSegment 27136 256 64 h256 checkBlocks_27392_27455
  have h384 := extendCertifiedSegment 27136 320 64 h320 checkBlocks_27456_27519
  have h448 := extendCertifiedSegment 27136 384 64 h384 checkBlocks_27520_27583
  have h512 := extendCertifiedSegment 27136 448 64 h448 checkBlocks_27584_27647
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [25600, 27648) passes the packed checker. -/
public theorem blocks_in_25600_27648 :
    ∀ i : Fin 2048, indexedBlockCheck (25600 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (25600 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 25600 0 512 h0 checkBlocks_25600_26111
  have h1024 := extendCertifiedSegment 25600 512 512 h512 checkBlocks_26112_26623
  have h1536 := extendCertifiedSegment 25600 1024 512 h1024 checkBlocks_26624_27135
  have h2048 := extendCertifiedSegment 25600 1536 512 h1536 checkBlocks_27136_27647
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
