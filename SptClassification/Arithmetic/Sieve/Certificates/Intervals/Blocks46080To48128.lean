/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 46080 through 48127 -/

public section

namespace SptClassification.Sieve

private theorem checkBlocks_46080_46143 :
    ∀ i : Fin 64, indexedBlockCheck (46080 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46144_46207 :
    ∀ i : Fin 64, indexedBlockCheck (46144 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46208_46271 :
    ∀ i : Fin 64, indexedBlockCheck (46208 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46272_46335 :
    ∀ i : Fin 64, indexedBlockCheck (46272 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46336_46399 :
    ∀ i : Fin 64, indexedBlockCheck (46336 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46400_46463 :
    ∀ i : Fin 64, indexedBlockCheck (46400 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46464_46527 :
    ∀ i : Fin 64, indexedBlockCheck (46464 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46528_46591 :
    ∀ i : Fin 64, indexedBlockCheck (46528 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46080_46591 :
    ∀ i : Fin 512, indexedBlockCheck (46080 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (46080 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 46080 0 64 h0 checkBlocks_46080_46143
  have h128 := extendCertifiedSegment 46080 64 64 h64 checkBlocks_46144_46207
  have h192 := extendCertifiedSegment 46080 128 64 h128 checkBlocks_46208_46271
  have h256 := extendCertifiedSegment 46080 192 64 h192 checkBlocks_46272_46335
  have h320 := extendCertifiedSegment 46080 256 64 h256 checkBlocks_46336_46399
  have h384 := extendCertifiedSegment 46080 320 64 h320 checkBlocks_46400_46463
  have h448 := extendCertifiedSegment 46080 384 64 h384 checkBlocks_46464_46527
  have h512 := extendCertifiedSegment 46080 448 64 h448 checkBlocks_46528_46591
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_46592_46655 :
    ∀ i : Fin 64, indexedBlockCheck (46592 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46656_46719 :
    ∀ i : Fin 64, indexedBlockCheck (46656 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46720_46783 :
    ∀ i : Fin 64, indexedBlockCheck (46720 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46784_46847 :
    ∀ i : Fin 64, indexedBlockCheck (46784 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46848_46911 :
    ∀ i : Fin 64, indexedBlockCheck (46848 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46912_46975 :
    ∀ i : Fin 64, indexedBlockCheck (46912 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46976_47039 :
    ∀ i : Fin 64, indexedBlockCheck (46976 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47040_47103 :
    ∀ i : Fin 64, indexedBlockCheck (47040 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46592_47103 :
    ∀ i : Fin 512, indexedBlockCheck (46592 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (46592 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 46592 0 64 h0 checkBlocks_46592_46655
  have h128 := extendCertifiedSegment 46592 64 64 h64 checkBlocks_46656_46719
  have h192 := extendCertifiedSegment 46592 128 64 h128 checkBlocks_46720_46783
  have h256 := extendCertifiedSegment 46592 192 64 h192 checkBlocks_46784_46847
  have h320 := extendCertifiedSegment 46592 256 64 h256 checkBlocks_46848_46911
  have h384 := extendCertifiedSegment 46592 320 64 h320 checkBlocks_46912_46975
  have h448 := extendCertifiedSegment 46592 384 64 h384 checkBlocks_46976_47039
  have h512 := extendCertifiedSegment 46592 448 64 h448 checkBlocks_47040_47103
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_47104_47167 :
    ∀ i : Fin 64, indexedBlockCheck (47104 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47168_47231 :
    ∀ i : Fin 64, indexedBlockCheck (47168 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47232_47295 :
    ∀ i : Fin 64, indexedBlockCheck (47232 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47296_47359 :
    ∀ i : Fin 64, indexedBlockCheck (47296 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47360_47423 :
    ∀ i : Fin 64, indexedBlockCheck (47360 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47424_47487 :
    ∀ i : Fin 64, indexedBlockCheck (47424 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47488_47551 :
    ∀ i : Fin 64, indexedBlockCheck (47488 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47552_47615 :
    ∀ i : Fin 64, indexedBlockCheck (47552 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47104_47615 :
    ∀ i : Fin 512, indexedBlockCheck (47104 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (47104 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 47104 0 64 h0 checkBlocks_47104_47167
  have h128 := extendCertifiedSegment 47104 64 64 h64 checkBlocks_47168_47231
  have h192 := extendCertifiedSegment 47104 128 64 h128 checkBlocks_47232_47295
  have h256 := extendCertifiedSegment 47104 192 64 h192 checkBlocks_47296_47359
  have h320 := extendCertifiedSegment 47104 256 64 h256 checkBlocks_47360_47423
  have h384 := extendCertifiedSegment 47104 320 64 h320 checkBlocks_47424_47487
  have h448 := extendCertifiedSegment 47104 384 64 h384 checkBlocks_47488_47551
  have h512 := extendCertifiedSegment 47104 448 64 h448 checkBlocks_47552_47615
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_47616_47679 :
    ∀ i : Fin 64, indexedBlockCheck (47616 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47680_47743 :
    ∀ i : Fin 64, indexedBlockCheck (47680 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47744_47807 :
    ∀ i : Fin 64, indexedBlockCheck (47744 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47808_47871 :
    ∀ i : Fin 64, indexedBlockCheck (47808 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47872_47935 :
    ∀ i : Fin 64, indexedBlockCheck (47872 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47936_47999 :
    ∀ i : Fin 64, indexedBlockCheck (47936 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_48000_48063 :
    ∀ i : Fin 64, indexedBlockCheck (48000 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_48064_48127 :
    ∀ i : Fin 64, indexedBlockCheck (48064 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47616_48127 :
    ∀ i : Fin 512, indexedBlockCheck (47616 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (47616 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 47616 0 64 h0 checkBlocks_47616_47679
  have h128 := extendCertifiedSegment 47616 64 64 h64 checkBlocks_47680_47743
  have h192 := extendCertifiedSegment 47616 128 64 h128 checkBlocks_47744_47807
  have h256 := extendCertifiedSegment 47616 192 64 h192 checkBlocks_47808_47871
  have h320 := extendCertifiedSegment 47616 256 64 h256 checkBlocks_47872_47935
  have h384 := extendCertifiedSegment 47616 320 64 h320 checkBlocks_47936_47999
  have h448 := extendCertifiedSegment 47616 384 64 h384 checkBlocks_48000_48063
  have h512 := extendCertifiedSegment 47616 448 64 h448 checkBlocks_48064_48127
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [46080, 48128) passes the packed checker. -/
public theorem blocks_in_46080_48128 :
    ∀ i : Fin 2048, indexedBlockCheck (46080 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (46080 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 46080 0 512 h0 checkBlocks_46080_46591
  have h1024 := extendCertifiedSegment 46080 512 512 h512 checkBlocks_46592_47103
  have h1536 := extendCertifiedSegment 46080 1024 512 h1024 checkBlocks_47104_47615
  have h2048 := extendCertifiedSegment 46080 1536 512 h1536 checkBlocks_47616_48127
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
