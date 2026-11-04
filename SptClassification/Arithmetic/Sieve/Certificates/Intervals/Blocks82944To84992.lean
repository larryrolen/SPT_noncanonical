/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 82944 through 84991 -/

public section

namespace SptClassification.Sieve

-- Bound memory by checking small certificate pieces sequentially.
set_option Elab.async false

private theorem checkBlocks_82944_83007_part0 :
    ∀ i : Fin 32, indexedBlockCheck (82944 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_82944_83007_part1 :
    ∀ i : Fin 32, indexedBlockCheck (82976 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_82944_83007 :
    ∀ i : Fin 64, indexedBlockCheck (82944 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (82944 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 82944 0 32 h0 checkBlocks_82944_83007_part0
  have h64 := extendCertifiedSegment 82944 32 32 h32 checkBlocks_82944_83007_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_83008_83071_part0 :
    ∀ i : Fin 32, indexedBlockCheck (83008 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83008_83071_part1 :
    ∀ i : Fin 32, indexedBlockCheck (83040 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83008_83071 :
    ∀ i : Fin 64, indexedBlockCheck (83008 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (83008 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 83008 0 32 h0 checkBlocks_83008_83071_part0
  have h64 := extendCertifiedSegment 83008 32 32 h32 checkBlocks_83008_83071_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_83072_83135_part0 :
    ∀ i : Fin 32, indexedBlockCheck (83072 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83072_83135_part1 :
    ∀ i : Fin 32, indexedBlockCheck (83104 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83072_83135 :
    ∀ i : Fin 64, indexedBlockCheck (83072 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (83072 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 83072 0 32 h0 checkBlocks_83072_83135_part0
  have h64 := extendCertifiedSegment 83072 32 32 h32 checkBlocks_83072_83135_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_83136_83199_part0 :
    ∀ i : Fin 32, indexedBlockCheck (83136 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83136_83199_part1 :
    ∀ i : Fin 32, indexedBlockCheck (83168 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83136_83199 :
    ∀ i : Fin 64, indexedBlockCheck (83136 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (83136 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 83136 0 32 h0 checkBlocks_83136_83199_part0
  have h64 := extendCertifiedSegment 83136 32 32 h32 checkBlocks_83136_83199_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_83200_83263_part0 :
    ∀ i : Fin 32, indexedBlockCheck (83200 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83200_83263_part1 :
    ∀ i : Fin 32, indexedBlockCheck (83232 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83200_83263 :
    ∀ i : Fin 64, indexedBlockCheck (83200 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (83200 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 83200 0 32 h0 checkBlocks_83200_83263_part0
  have h64 := extendCertifiedSegment 83200 32 32 h32 checkBlocks_83200_83263_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_83264_83327_part0 :
    ∀ i : Fin 32, indexedBlockCheck (83264 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83264_83327_part1 :
    ∀ i : Fin 32, indexedBlockCheck (83296 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83264_83327 :
    ∀ i : Fin 64, indexedBlockCheck (83264 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (83264 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 83264 0 32 h0 checkBlocks_83264_83327_part0
  have h64 := extendCertifiedSegment 83264 32 32 h32 checkBlocks_83264_83327_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_83328_83391_part0 :
    ∀ i : Fin 32, indexedBlockCheck (83328 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83328_83391_part1 :
    ∀ i : Fin 32, indexedBlockCheck (83360 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83328_83391 :
    ∀ i : Fin 64, indexedBlockCheck (83328 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (83328 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 83328 0 32 h0 checkBlocks_83328_83391_part0
  have h64 := extendCertifiedSegment 83328 32 32 h32 checkBlocks_83328_83391_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_83392_83455_part0 :
    ∀ i : Fin 32, indexedBlockCheck (83392 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83392_83455_part1 :
    ∀ i : Fin 32, indexedBlockCheck (83424 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83392_83455 :
    ∀ i : Fin 64, indexedBlockCheck (83392 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (83392 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 83392 0 32 h0 checkBlocks_83392_83455_part0
  have h64 := extendCertifiedSegment 83392 32 32 h32 checkBlocks_83392_83455_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_82944_83455 :
    ∀ i : Fin 512, indexedBlockCheck (82944 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (82944 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 82944 0 64 h0 checkBlocks_82944_83007
  have h128 := extendCertifiedSegment 82944 64 64 h64 checkBlocks_83008_83071
  have h192 := extendCertifiedSegment 82944 128 64 h128 checkBlocks_83072_83135
  have h256 := extendCertifiedSegment 82944 192 64 h192 checkBlocks_83136_83199
  have h320 := extendCertifiedSegment 82944 256 64 h256 checkBlocks_83200_83263
  have h384 := extendCertifiedSegment 82944 320 64 h320 checkBlocks_83264_83327
  have h448 := extendCertifiedSegment 82944 384 64 h384 checkBlocks_83328_83391
  have h512 := extendCertifiedSegment 82944 448 64 h448 checkBlocks_83392_83455
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_83456_83519_part0 :
    ∀ i : Fin 32, indexedBlockCheck (83456 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83456_83519_part1 :
    ∀ i : Fin 32, indexedBlockCheck (83488 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83456_83519 :
    ∀ i : Fin 64, indexedBlockCheck (83456 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (83456 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 83456 0 32 h0 checkBlocks_83456_83519_part0
  have h64 := extendCertifiedSegment 83456 32 32 h32 checkBlocks_83456_83519_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_83520_83583_part0 :
    ∀ i : Fin 32, indexedBlockCheck (83520 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83520_83583_part1 :
    ∀ i : Fin 32, indexedBlockCheck (83552 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83520_83583 :
    ∀ i : Fin 64, indexedBlockCheck (83520 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (83520 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 83520 0 32 h0 checkBlocks_83520_83583_part0
  have h64 := extendCertifiedSegment 83520 32 32 h32 checkBlocks_83520_83583_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_83584_83647_part0 :
    ∀ i : Fin 32, indexedBlockCheck (83584 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83584_83647_part1 :
    ∀ i : Fin 32, indexedBlockCheck (83616 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83584_83647 :
    ∀ i : Fin 64, indexedBlockCheck (83584 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (83584 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 83584 0 32 h0 checkBlocks_83584_83647_part0
  have h64 := extendCertifiedSegment 83584 32 32 h32 checkBlocks_83584_83647_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_83648_83711_part0 :
    ∀ i : Fin 32, indexedBlockCheck (83648 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83648_83711_part1 :
    ∀ i : Fin 32, indexedBlockCheck (83680 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83648_83711 :
    ∀ i : Fin 64, indexedBlockCheck (83648 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (83648 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 83648 0 32 h0 checkBlocks_83648_83711_part0
  have h64 := extendCertifiedSegment 83648 32 32 h32 checkBlocks_83648_83711_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_83712_83775_part0 :
    ∀ i : Fin 32, indexedBlockCheck (83712 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83712_83775_part1 :
    ∀ i : Fin 32, indexedBlockCheck (83744 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83712_83775 :
    ∀ i : Fin 64, indexedBlockCheck (83712 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (83712 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 83712 0 32 h0 checkBlocks_83712_83775_part0
  have h64 := extendCertifiedSegment 83712 32 32 h32 checkBlocks_83712_83775_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_83776_83839_part0 :
    ∀ i : Fin 32, indexedBlockCheck (83776 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83776_83839_part1 :
    ∀ i : Fin 32, indexedBlockCheck (83808 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83776_83839 :
    ∀ i : Fin 64, indexedBlockCheck (83776 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (83776 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 83776 0 32 h0 checkBlocks_83776_83839_part0
  have h64 := extendCertifiedSegment 83776 32 32 h32 checkBlocks_83776_83839_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_83840_83903_part0 :
    ∀ i : Fin 32, indexedBlockCheck (83840 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83840_83903_part1 :
    ∀ i : Fin 32, indexedBlockCheck (83872 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83840_83903 :
    ∀ i : Fin 64, indexedBlockCheck (83840 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (83840 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 83840 0 32 h0 checkBlocks_83840_83903_part0
  have h64 := extendCertifiedSegment 83840 32 32 h32 checkBlocks_83840_83903_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_83904_83967_part0 :
    ∀ i : Fin 32, indexedBlockCheck (83904 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83904_83967_part1 :
    ∀ i : Fin 32, indexedBlockCheck (83936 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83904_83967 :
    ∀ i : Fin 64, indexedBlockCheck (83904 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (83904 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 83904 0 32 h0 checkBlocks_83904_83967_part0
  have h64 := extendCertifiedSegment 83904 32 32 h32 checkBlocks_83904_83967_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_83456_83967 :
    ∀ i : Fin 512, indexedBlockCheck (83456 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (83456 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 83456 0 64 h0 checkBlocks_83456_83519
  have h128 := extendCertifiedSegment 83456 64 64 h64 checkBlocks_83520_83583
  have h192 := extendCertifiedSegment 83456 128 64 h128 checkBlocks_83584_83647
  have h256 := extendCertifiedSegment 83456 192 64 h192 checkBlocks_83648_83711
  have h320 := extendCertifiedSegment 83456 256 64 h256 checkBlocks_83712_83775
  have h384 := extendCertifiedSegment 83456 320 64 h320 checkBlocks_83776_83839
  have h448 := extendCertifiedSegment 83456 384 64 h384 checkBlocks_83840_83903
  have h512 := extendCertifiedSegment 83456 448 64 h448 checkBlocks_83904_83967
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_83968_84031_part0 :
    ∀ i : Fin 32, indexedBlockCheck (83968 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83968_84031_part1 :
    ∀ i : Fin 32, indexedBlockCheck (84000 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83968_84031 :
    ∀ i : Fin 64, indexedBlockCheck (83968 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (83968 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 83968 0 32 h0 checkBlocks_83968_84031_part0
  have h64 := extendCertifiedSegment 83968 32 32 h32 checkBlocks_83968_84031_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_84032_84095_part0 :
    ∀ i : Fin 32, indexedBlockCheck (84032 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84032_84095_part1 :
    ∀ i : Fin 32, indexedBlockCheck (84064 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84032_84095 :
    ∀ i : Fin 64, indexedBlockCheck (84032 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (84032 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 84032 0 32 h0 checkBlocks_84032_84095_part0
  have h64 := extendCertifiedSegment 84032 32 32 h32 checkBlocks_84032_84095_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_84096_84159_part0 :
    ∀ i : Fin 32, indexedBlockCheck (84096 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84096_84159_part1 :
    ∀ i : Fin 32, indexedBlockCheck (84128 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84096_84159 :
    ∀ i : Fin 64, indexedBlockCheck (84096 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (84096 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 84096 0 32 h0 checkBlocks_84096_84159_part0
  have h64 := extendCertifiedSegment 84096 32 32 h32 checkBlocks_84096_84159_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_84160_84223_part0 :
    ∀ i : Fin 32, indexedBlockCheck (84160 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84160_84223_part1 :
    ∀ i : Fin 32, indexedBlockCheck (84192 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84160_84223 :
    ∀ i : Fin 64, indexedBlockCheck (84160 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (84160 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 84160 0 32 h0 checkBlocks_84160_84223_part0
  have h64 := extendCertifiedSegment 84160 32 32 h32 checkBlocks_84160_84223_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_84224_84287_part0 :
    ∀ i : Fin 32, indexedBlockCheck (84224 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84224_84287_part1 :
    ∀ i : Fin 32, indexedBlockCheck (84256 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84224_84287 :
    ∀ i : Fin 64, indexedBlockCheck (84224 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (84224 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 84224 0 32 h0 checkBlocks_84224_84287_part0
  have h64 := extendCertifiedSegment 84224 32 32 h32 checkBlocks_84224_84287_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_84288_84351_part0 :
    ∀ i : Fin 32, indexedBlockCheck (84288 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84288_84351_part1 :
    ∀ i : Fin 32, indexedBlockCheck (84320 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84288_84351 :
    ∀ i : Fin 64, indexedBlockCheck (84288 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (84288 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 84288 0 32 h0 checkBlocks_84288_84351_part0
  have h64 := extendCertifiedSegment 84288 32 32 h32 checkBlocks_84288_84351_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_84352_84415_part0 :
    ∀ i : Fin 32, indexedBlockCheck (84352 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84352_84415_part1 :
    ∀ i : Fin 32, indexedBlockCheck (84384 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84352_84415 :
    ∀ i : Fin 64, indexedBlockCheck (84352 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (84352 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 84352 0 32 h0 checkBlocks_84352_84415_part0
  have h64 := extendCertifiedSegment 84352 32 32 h32 checkBlocks_84352_84415_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_84416_84479_part0 :
    ∀ i : Fin 32, indexedBlockCheck (84416 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84416_84479_part1 :
    ∀ i : Fin 32, indexedBlockCheck (84448 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84416_84479 :
    ∀ i : Fin 64, indexedBlockCheck (84416 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (84416 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 84416 0 32 h0 checkBlocks_84416_84479_part0
  have h64 := extendCertifiedSegment 84416 32 32 h32 checkBlocks_84416_84479_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_83968_84479 :
    ∀ i : Fin 512, indexedBlockCheck (83968 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (83968 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 83968 0 64 h0 checkBlocks_83968_84031
  have h128 := extendCertifiedSegment 83968 64 64 h64 checkBlocks_84032_84095
  have h192 := extendCertifiedSegment 83968 128 64 h128 checkBlocks_84096_84159
  have h256 := extendCertifiedSegment 83968 192 64 h192 checkBlocks_84160_84223
  have h320 := extendCertifiedSegment 83968 256 64 h256 checkBlocks_84224_84287
  have h384 := extendCertifiedSegment 83968 320 64 h320 checkBlocks_84288_84351
  have h448 := extendCertifiedSegment 83968 384 64 h384 checkBlocks_84352_84415
  have h512 := extendCertifiedSegment 83968 448 64 h448 checkBlocks_84416_84479
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_84480_84543_part0 :
    ∀ i : Fin 32, indexedBlockCheck (84480 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84480_84543_part1 :
    ∀ i : Fin 32, indexedBlockCheck (84512 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84480_84543 :
    ∀ i : Fin 64, indexedBlockCheck (84480 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (84480 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 84480 0 32 h0 checkBlocks_84480_84543_part0
  have h64 := extendCertifiedSegment 84480 32 32 h32 checkBlocks_84480_84543_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_84544_84607_part0 :
    ∀ i : Fin 32, indexedBlockCheck (84544 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84544_84607_part1 :
    ∀ i : Fin 32, indexedBlockCheck (84576 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84544_84607 :
    ∀ i : Fin 64, indexedBlockCheck (84544 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (84544 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 84544 0 32 h0 checkBlocks_84544_84607_part0
  have h64 := extendCertifiedSegment 84544 32 32 h32 checkBlocks_84544_84607_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_84608_84671_part0 :
    ∀ i : Fin 32, indexedBlockCheck (84608 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84608_84671_part1 :
    ∀ i : Fin 32, indexedBlockCheck (84640 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84608_84671 :
    ∀ i : Fin 64, indexedBlockCheck (84608 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (84608 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 84608 0 32 h0 checkBlocks_84608_84671_part0
  have h64 := extendCertifiedSegment 84608 32 32 h32 checkBlocks_84608_84671_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_84672_84735_part0 :
    ∀ i : Fin 32, indexedBlockCheck (84672 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84672_84735_part1 :
    ∀ i : Fin 32, indexedBlockCheck (84704 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84672_84735 :
    ∀ i : Fin 64, indexedBlockCheck (84672 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (84672 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 84672 0 32 h0 checkBlocks_84672_84735_part0
  have h64 := extendCertifiedSegment 84672 32 32 h32 checkBlocks_84672_84735_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_84736_84799_part0 :
    ∀ i : Fin 32, indexedBlockCheck (84736 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84736_84799_part1 :
    ∀ i : Fin 32, indexedBlockCheck (84768 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84736_84799 :
    ∀ i : Fin 64, indexedBlockCheck (84736 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (84736 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 84736 0 32 h0 checkBlocks_84736_84799_part0
  have h64 := extendCertifiedSegment 84736 32 32 h32 checkBlocks_84736_84799_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_84800_84863_part0 :
    ∀ i : Fin 32, indexedBlockCheck (84800 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84800_84863_part1 :
    ∀ i : Fin 32, indexedBlockCheck (84832 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84800_84863 :
    ∀ i : Fin 64, indexedBlockCheck (84800 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (84800 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 84800 0 32 h0 checkBlocks_84800_84863_part0
  have h64 := extendCertifiedSegment 84800 32 32 h32 checkBlocks_84800_84863_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_84864_84927_part0 :
    ∀ i : Fin 32, indexedBlockCheck (84864 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84864_84927_part1 :
    ∀ i : Fin 32, indexedBlockCheck (84896 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84864_84927 :
    ∀ i : Fin 64, indexedBlockCheck (84864 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (84864 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 84864 0 32 h0 checkBlocks_84864_84927_part0
  have h64 := extendCertifiedSegment 84864 32 32 h32 checkBlocks_84864_84927_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_84928_84991_part0 :
    ∀ i : Fin 32, indexedBlockCheck (84928 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84928_84991_part1 :
    ∀ i : Fin 32, indexedBlockCheck (84960 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84928_84991 :
    ∀ i : Fin 64, indexedBlockCheck (84928 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (84928 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 84928 0 32 h0 checkBlocks_84928_84991_part0
  have h64 := extendCertifiedSegment 84928 32 32 h32 checkBlocks_84928_84991_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_84480_84991 :
    ∀ i : Fin 512, indexedBlockCheck (84480 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (84480 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 84480 0 64 h0 checkBlocks_84480_84543
  have h128 := extendCertifiedSegment 84480 64 64 h64 checkBlocks_84544_84607
  have h192 := extendCertifiedSegment 84480 128 64 h128 checkBlocks_84608_84671
  have h256 := extendCertifiedSegment 84480 192 64 h192 checkBlocks_84672_84735
  have h320 := extendCertifiedSegment 84480 256 64 h256 checkBlocks_84736_84799
  have h384 := extendCertifiedSegment 84480 320 64 h320 checkBlocks_84800_84863
  have h448 := extendCertifiedSegment 84480 384 64 h384 checkBlocks_84864_84927
  have h512 := extendCertifiedSegment 84480 448 64 h448 checkBlocks_84928_84991
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [82944, 84992) passes the packed checker. -/
public theorem blocks_in_82944_84992 :
    ∀ i : Fin 2048, indexedBlockCheck (82944 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (82944 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 82944 0 512 h0 checkBlocks_82944_83455
  have h1024 := extendCertifiedSegment 82944 512 512 h512 checkBlocks_83456_83967
  have h1536 := extendCertifiedSegment 82944 1024 512 h1024 checkBlocks_83968_84479
  have h2048 := extendCertifiedSegment 82944 1536 512 h1536 checkBlocks_84480_84991
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
