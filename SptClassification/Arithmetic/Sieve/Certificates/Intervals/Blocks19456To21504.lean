/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 19456 through 21503 -/

public section

namespace SptClassification.Sieve

-- Bound memory by checking small certificate pieces sequentially.
set_option Elab.async false

private theorem checkBlocks_19456_19519_part0 :
    ∀ i : Fin 32, indexedBlockCheck (19456 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19456_19519_part1 :
    ∀ i : Fin 32, indexedBlockCheck (19488 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19456_19519 :
    ∀ i : Fin 64, indexedBlockCheck (19456 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (19456 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 19456 0 32 h0 checkBlocks_19456_19519_part0
  have h64 := extendCertifiedSegment 19456 32 32 h32 checkBlocks_19456_19519_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_19520_19583_part0 :
    ∀ i : Fin 32, indexedBlockCheck (19520 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19520_19583_part1 :
    ∀ i : Fin 32, indexedBlockCheck (19552 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19520_19583 :
    ∀ i : Fin 64, indexedBlockCheck (19520 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (19520 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 19520 0 32 h0 checkBlocks_19520_19583_part0
  have h64 := extendCertifiedSegment 19520 32 32 h32 checkBlocks_19520_19583_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_19584_19647_part0 :
    ∀ i : Fin 32, indexedBlockCheck (19584 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19584_19647_part1 :
    ∀ i : Fin 32, indexedBlockCheck (19616 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19584_19647 :
    ∀ i : Fin 64, indexedBlockCheck (19584 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (19584 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 19584 0 32 h0 checkBlocks_19584_19647_part0
  have h64 := extendCertifiedSegment 19584 32 32 h32 checkBlocks_19584_19647_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_19648_19711_part0 :
    ∀ i : Fin 32, indexedBlockCheck (19648 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19648_19711_part1 :
    ∀ i : Fin 32, indexedBlockCheck (19680 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19648_19711 :
    ∀ i : Fin 64, indexedBlockCheck (19648 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (19648 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 19648 0 32 h0 checkBlocks_19648_19711_part0
  have h64 := extendCertifiedSegment 19648 32 32 h32 checkBlocks_19648_19711_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_19712_19775_part0 :
    ∀ i : Fin 32, indexedBlockCheck (19712 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19712_19775_part1 :
    ∀ i : Fin 32, indexedBlockCheck (19744 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19712_19775 :
    ∀ i : Fin 64, indexedBlockCheck (19712 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (19712 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 19712 0 32 h0 checkBlocks_19712_19775_part0
  have h64 := extendCertifiedSegment 19712 32 32 h32 checkBlocks_19712_19775_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_19776_19839_part0 :
    ∀ i : Fin 32, indexedBlockCheck (19776 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19776_19839_part1 :
    ∀ i : Fin 32, indexedBlockCheck (19808 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19776_19839 :
    ∀ i : Fin 64, indexedBlockCheck (19776 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (19776 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 19776 0 32 h0 checkBlocks_19776_19839_part0
  have h64 := extendCertifiedSegment 19776 32 32 h32 checkBlocks_19776_19839_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_19840_19903_part0 :
    ∀ i : Fin 32, indexedBlockCheck (19840 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19840_19903_part1 :
    ∀ i : Fin 32, indexedBlockCheck (19872 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19840_19903 :
    ∀ i : Fin 64, indexedBlockCheck (19840 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (19840 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 19840 0 32 h0 checkBlocks_19840_19903_part0
  have h64 := extendCertifiedSegment 19840 32 32 h32 checkBlocks_19840_19903_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_19904_19967_part0 :
    ∀ i : Fin 32, indexedBlockCheck (19904 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19904_19967_part1 :
    ∀ i : Fin 32, indexedBlockCheck (19936 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19904_19967 :
    ∀ i : Fin 64, indexedBlockCheck (19904 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (19904 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 19904 0 32 h0 checkBlocks_19904_19967_part0
  have h64 := extendCertifiedSegment 19904 32 32 h32 checkBlocks_19904_19967_part1
  intro i
  exact h64 i.val i.isLt

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

private theorem checkBlocks_19968_20031_part0 :
    ∀ i : Fin 32, indexedBlockCheck (19968 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19968_20031_part1 :
    ∀ i : Fin 32, indexedBlockCheck (20000 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19968_20031 :
    ∀ i : Fin 64, indexedBlockCheck (19968 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (19968 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 19968 0 32 h0 checkBlocks_19968_20031_part0
  have h64 := extendCertifiedSegment 19968 32 32 h32 checkBlocks_19968_20031_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_20032_20095_part0 :
    ∀ i : Fin 32, indexedBlockCheck (20032 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20032_20095_part1 :
    ∀ i : Fin 32, indexedBlockCheck (20064 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20032_20095 :
    ∀ i : Fin 64, indexedBlockCheck (20032 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (20032 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 20032 0 32 h0 checkBlocks_20032_20095_part0
  have h64 := extendCertifiedSegment 20032 32 32 h32 checkBlocks_20032_20095_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_20096_20159_part0 :
    ∀ i : Fin 32, indexedBlockCheck (20096 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20096_20159_part1 :
    ∀ i : Fin 32, indexedBlockCheck (20128 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20096_20159 :
    ∀ i : Fin 64, indexedBlockCheck (20096 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (20096 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 20096 0 32 h0 checkBlocks_20096_20159_part0
  have h64 := extendCertifiedSegment 20096 32 32 h32 checkBlocks_20096_20159_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_20160_20223_part0 :
    ∀ i : Fin 32, indexedBlockCheck (20160 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20160_20223_part1 :
    ∀ i : Fin 32, indexedBlockCheck (20192 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20160_20223 :
    ∀ i : Fin 64, indexedBlockCheck (20160 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (20160 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 20160 0 32 h0 checkBlocks_20160_20223_part0
  have h64 := extendCertifiedSegment 20160 32 32 h32 checkBlocks_20160_20223_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_20224_20287_part0 :
    ∀ i : Fin 32, indexedBlockCheck (20224 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20224_20287_part1 :
    ∀ i : Fin 32, indexedBlockCheck (20256 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20224_20287 :
    ∀ i : Fin 64, indexedBlockCheck (20224 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (20224 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 20224 0 32 h0 checkBlocks_20224_20287_part0
  have h64 := extendCertifiedSegment 20224 32 32 h32 checkBlocks_20224_20287_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_20288_20351_part0 :
    ∀ i : Fin 32, indexedBlockCheck (20288 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20288_20351_part1 :
    ∀ i : Fin 32, indexedBlockCheck (20320 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20288_20351 :
    ∀ i : Fin 64, indexedBlockCheck (20288 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (20288 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 20288 0 32 h0 checkBlocks_20288_20351_part0
  have h64 := extendCertifiedSegment 20288 32 32 h32 checkBlocks_20288_20351_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_20352_20415_part0 :
    ∀ i : Fin 32, indexedBlockCheck (20352 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20352_20415_part1 :
    ∀ i : Fin 32, indexedBlockCheck (20384 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20352_20415 :
    ∀ i : Fin 64, indexedBlockCheck (20352 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (20352 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 20352 0 32 h0 checkBlocks_20352_20415_part0
  have h64 := extendCertifiedSegment 20352 32 32 h32 checkBlocks_20352_20415_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_20416_20479_part0 :
    ∀ i : Fin 32, indexedBlockCheck (20416 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20416_20479_part1 :
    ∀ i : Fin 32, indexedBlockCheck (20448 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20416_20479 :
    ∀ i : Fin 64, indexedBlockCheck (20416 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (20416 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 20416 0 32 h0 checkBlocks_20416_20479_part0
  have h64 := extendCertifiedSegment 20416 32 32 h32 checkBlocks_20416_20479_part1
  intro i
  exact h64 i.val i.isLt

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

private theorem checkBlocks_20480_20543_part0 :
    ∀ i : Fin 32, indexedBlockCheck (20480 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20480_20543_part1 :
    ∀ i : Fin 32, indexedBlockCheck (20512 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20480_20543 :
    ∀ i : Fin 64, indexedBlockCheck (20480 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (20480 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 20480 0 32 h0 checkBlocks_20480_20543_part0
  have h64 := extendCertifiedSegment 20480 32 32 h32 checkBlocks_20480_20543_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_20544_20607_part0 :
    ∀ i : Fin 32, indexedBlockCheck (20544 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20544_20607_part1 :
    ∀ i : Fin 32, indexedBlockCheck (20576 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20544_20607 :
    ∀ i : Fin 64, indexedBlockCheck (20544 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (20544 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 20544 0 32 h0 checkBlocks_20544_20607_part0
  have h64 := extendCertifiedSegment 20544 32 32 h32 checkBlocks_20544_20607_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_20608_20671_part0 :
    ∀ i : Fin 32, indexedBlockCheck (20608 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20608_20671_part1 :
    ∀ i : Fin 32, indexedBlockCheck (20640 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20608_20671 :
    ∀ i : Fin 64, indexedBlockCheck (20608 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (20608 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 20608 0 32 h0 checkBlocks_20608_20671_part0
  have h64 := extendCertifiedSegment 20608 32 32 h32 checkBlocks_20608_20671_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_20672_20735_part0 :
    ∀ i : Fin 32, indexedBlockCheck (20672 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20672_20735_part1 :
    ∀ i : Fin 32, indexedBlockCheck (20704 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20672_20735 :
    ∀ i : Fin 64, indexedBlockCheck (20672 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (20672 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 20672 0 32 h0 checkBlocks_20672_20735_part0
  have h64 := extendCertifiedSegment 20672 32 32 h32 checkBlocks_20672_20735_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_20736_20799_part0 :
    ∀ i : Fin 32, indexedBlockCheck (20736 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20736_20799_part1 :
    ∀ i : Fin 32, indexedBlockCheck (20768 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20736_20799 :
    ∀ i : Fin 64, indexedBlockCheck (20736 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (20736 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 20736 0 32 h0 checkBlocks_20736_20799_part0
  have h64 := extendCertifiedSegment 20736 32 32 h32 checkBlocks_20736_20799_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_20800_20863_part0 :
    ∀ i : Fin 32, indexedBlockCheck (20800 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20800_20863_part1 :
    ∀ i : Fin 32, indexedBlockCheck (20832 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20800_20863 :
    ∀ i : Fin 64, indexedBlockCheck (20800 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (20800 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 20800 0 32 h0 checkBlocks_20800_20863_part0
  have h64 := extendCertifiedSegment 20800 32 32 h32 checkBlocks_20800_20863_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_20864_20927_part0 :
    ∀ i : Fin 32, indexedBlockCheck (20864 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20864_20927_part1 :
    ∀ i : Fin 32, indexedBlockCheck (20896 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20864_20927 :
    ∀ i : Fin 64, indexedBlockCheck (20864 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (20864 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 20864 0 32 h0 checkBlocks_20864_20927_part0
  have h64 := extendCertifiedSegment 20864 32 32 h32 checkBlocks_20864_20927_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_20928_20991_part0 :
    ∀ i : Fin 32, indexedBlockCheck (20928 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20928_20991_part1 :
    ∀ i : Fin 32, indexedBlockCheck (20960 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20928_20991 :
    ∀ i : Fin 64, indexedBlockCheck (20928 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (20928 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 20928 0 32 h0 checkBlocks_20928_20991_part0
  have h64 := extendCertifiedSegment 20928 32 32 h32 checkBlocks_20928_20991_part1
  intro i
  exact h64 i.val i.isLt

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

private theorem checkBlocks_20992_21055_part0 :
    ∀ i : Fin 32, indexedBlockCheck (20992 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20992_21055_part1 :
    ∀ i : Fin 32, indexedBlockCheck (21024 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_20992_21055 :
    ∀ i : Fin 64, indexedBlockCheck (20992 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (20992 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 20992 0 32 h0 checkBlocks_20992_21055_part0
  have h64 := extendCertifiedSegment 20992 32 32 h32 checkBlocks_20992_21055_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_21056_21119_part0 :
    ∀ i : Fin 32, indexedBlockCheck (21056 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_21056_21119_part1 :
    ∀ i : Fin 32, indexedBlockCheck (21088 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_21056_21119 :
    ∀ i : Fin 64, indexedBlockCheck (21056 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (21056 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 21056 0 32 h0 checkBlocks_21056_21119_part0
  have h64 := extendCertifiedSegment 21056 32 32 h32 checkBlocks_21056_21119_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_21120_21183_part0 :
    ∀ i : Fin 32, indexedBlockCheck (21120 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_21120_21183_part1 :
    ∀ i : Fin 32, indexedBlockCheck (21152 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_21120_21183 :
    ∀ i : Fin 64, indexedBlockCheck (21120 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (21120 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 21120 0 32 h0 checkBlocks_21120_21183_part0
  have h64 := extendCertifiedSegment 21120 32 32 h32 checkBlocks_21120_21183_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_21184_21247_part0 :
    ∀ i : Fin 32, indexedBlockCheck (21184 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_21184_21247_part1 :
    ∀ i : Fin 32, indexedBlockCheck (21216 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_21184_21247 :
    ∀ i : Fin 64, indexedBlockCheck (21184 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (21184 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 21184 0 32 h0 checkBlocks_21184_21247_part0
  have h64 := extendCertifiedSegment 21184 32 32 h32 checkBlocks_21184_21247_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_21248_21311_part0 :
    ∀ i : Fin 32, indexedBlockCheck (21248 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_21248_21311_part1 :
    ∀ i : Fin 32, indexedBlockCheck (21280 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_21248_21311 :
    ∀ i : Fin 64, indexedBlockCheck (21248 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (21248 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 21248 0 32 h0 checkBlocks_21248_21311_part0
  have h64 := extendCertifiedSegment 21248 32 32 h32 checkBlocks_21248_21311_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_21312_21375_part0 :
    ∀ i : Fin 32, indexedBlockCheck (21312 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_21312_21375_part1 :
    ∀ i : Fin 32, indexedBlockCheck (21344 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_21312_21375 :
    ∀ i : Fin 64, indexedBlockCheck (21312 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (21312 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 21312 0 32 h0 checkBlocks_21312_21375_part0
  have h64 := extendCertifiedSegment 21312 32 32 h32 checkBlocks_21312_21375_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_21376_21439_part0 :
    ∀ i : Fin 32, indexedBlockCheck (21376 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_21376_21439_part1 :
    ∀ i : Fin 32, indexedBlockCheck (21408 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_21376_21439 :
    ∀ i : Fin 64, indexedBlockCheck (21376 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (21376 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 21376 0 32 h0 checkBlocks_21376_21439_part0
  have h64 := extendCertifiedSegment 21376 32 32 h32 checkBlocks_21376_21439_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_21440_21503_part0 :
    ∀ i : Fin 32, indexedBlockCheck (21440 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_21440_21503_part1 :
    ∀ i : Fin 32, indexedBlockCheck (21472 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_21440_21503 :
    ∀ i : Fin 64, indexedBlockCheck (21440 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (21440 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 21440 0 32 h0 checkBlocks_21440_21503_part0
  have h64 := extendCertifiedSegment 21440 32 32 h32 checkBlocks_21440_21503_part1
  intro i
  exact h64 i.val i.isLt

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
