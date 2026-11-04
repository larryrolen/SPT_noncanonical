/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 87040 through 89087 -/

public section

namespace SptClassification.Sieve

-- Bound memory by checking small certificate pieces sequentially.
set_option Elab.async false

private theorem checkBlocks_87040_87103_part0 :
    ∀ i : Fin 32, indexedBlockCheck (87040 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87040_87103_part1 :
    ∀ i : Fin 32, indexedBlockCheck (87072 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87040_87103 :
    ∀ i : Fin 64, indexedBlockCheck (87040 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (87040 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 87040 0 32 h0 checkBlocks_87040_87103_part0
  have h64 := extendCertifiedSegment 87040 32 32 h32 checkBlocks_87040_87103_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_87104_87167_part0 :
    ∀ i : Fin 32, indexedBlockCheck (87104 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87104_87167_part1 :
    ∀ i : Fin 32, indexedBlockCheck (87136 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87104_87167 :
    ∀ i : Fin 64, indexedBlockCheck (87104 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (87104 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 87104 0 32 h0 checkBlocks_87104_87167_part0
  have h64 := extendCertifiedSegment 87104 32 32 h32 checkBlocks_87104_87167_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_87168_87231_part0 :
    ∀ i : Fin 32, indexedBlockCheck (87168 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87168_87231_part1 :
    ∀ i : Fin 32, indexedBlockCheck (87200 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87168_87231 :
    ∀ i : Fin 64, indexedBlockCheck (87168 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (87168 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 87168 0 32 h0 checkBlocks_87168_87231_part0
  have h64 := extendCertifiedSegment 87168 32 32 h32 checkBlocks_87168_87231_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_87232_87295_part0 :
    ∀ i : Fin 32, indexedBlockCheck (87232 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87232_87295_part1 :
    ∀ i : Fin 32, indexedBlockCheck (87264 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87232_87295 :
    ∀ i : Fin 64, indexedBlockCheck (87232 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (87232 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 87232 0 32 h0 checkBlocks_87232_87295_part0
  have h64 := extendCertifiedSegment 87232 32 32 h32 checkBlocks_87232_87295_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_87296_87359_part0 :
    ∀ i : Fin 32, indexedBlockCheck (87296 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87296_87359_part1 :
    ∀ i : Fin 32, indexedBlockCheck (87328 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87296_87359 :
    ∀ i : Fin 64, indexedBlockCheck (87296 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (87296 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 87296 0 32 h0 checkBlocks_87296_87359_part0
  have h64 := extendCertifiedSegment 87296 32 32 h32 checkBlocks_87296_87359_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_87360_87423_part0 :
    ∀ i : Fin 32, indexedBlockCheck (87360 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87360_87423_part1 :
    ∀ i : Fin 32, indexedBlockCheck (87392 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87360_87423 :
    ∀ i : Fin 64, indexedBlockCheck (87360 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (87360 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 87360 0 32 h0 checkBlocks_87360_87423_part0
  have h64 := extendCertifiedSegment 87360 32 32 h32 checkBlocks_87360_87423_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_87424_87487_part0 :
    ∀ i : Fin 32, indexedBlockCheck (87424 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87424_87487_part1 :
    ∀ i : Fin 32, indexedBlockCheck (87456 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87424_87487 :
    ∀ i : Fin 64, indexedBlockCheck (87424 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (87424 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 87424 0 32 h0 checkBlocks_87424_87487_part0
  have h64 := extendCertifiedSegment 87424 32 32 h32 checkBlocks_87424_87487_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_87488_87551_part0 :
    ∀ i : Fin 32, indexedBlockCheck (87488 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87488_87551_part1 :
    ∀ i : Fin 32, indexedBlockCheck (87520 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87488_87551 :
    ∀ i : Fin 64, indexedBlockCheck (87488 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (87488 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 87488 0 32 h0 checkBlocks_87488_87551_part0
  have h64 := extendCertifiedSegment 87488 32 32 h32 checkBlocks_87488_87551_part1
  intro i
  exact h64 i.val i.isLt

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

private theorem checkBlocks_87552_87615_part0 :
    ∀ i : Fin 32, indexedBlockCheck (87552 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87552_87615_part1 :
    ∀ i : Fin 32, indexedBlockCheck (87584 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87552_87615 :
    ∀ i : Fin 64, indexedBlockCheck (87552 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (87552 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 87552 0 32 h0 checkBlocks_87552_87615_part0
  have h64 := extendCertifiedSegment 87552 32 32 h32 checkBlocks_87552_87615_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_87616_87679_part0 :
    ∀ i : Fin 32, indexedBlockCheck (87616 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87616_87679_part1 :
    ∀ i : Fin 32, indexedBlockCheck (87648 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87616_87679 :
    ∀ i : Fin 64, indexedBlockCheck (87616 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (87616 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 87616 0 32 h0 checkBlocks_87616_87679_part0
  have h64 := extendCertifiedSegment 87616 32 32 h32 checkBlocks_87616_87679_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_87680_87743_part0 :
    ∀ i : Fin 32, indexedBlockCheck (87680 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87680_87743_part1 :
    ∀ i : Fin 32, indexedBlockCheck (87712 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87680_87743 :
    ∀ i : Fin 64, indexedBlockCheck (87680 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (87680 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 87680 0 32 h0 checkBlocks_87680_87743_part0
  have h64 := extendCertifiedSegment 87680 32 32 h32 checkBlocks_87680_87743_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_87744_87807_part0 :
    ∀ i : Fin 32, indexedBlockCheck (87744 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87744_87807_part1 :
    ∀ i : Fin 32, indexedBlockCheck (87776 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87744_87807 :
    ∀ i : Fin 64, indexedBlockCheck (87744 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (87744 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 87744 0 32 h0 checkBlocks_87744_87807_part0
  have h64 := extendCertifiedSegment 87744 32 32 h32 checkBlocks_87744_87807_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_87808_87871_part0 :
    ∀ i : Fin 32, indexedBlockCheck (87808 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87808_87871_part1 :
    ∀ i : Fin 32, indexedBlockCheck (87840 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87808_87871 :
    ∀ i : Fin 64, indexedBlockCheck (87808 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (87808 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 87808 0 32 h0 checkBlocks_87808_87871_part0
  have h64 := extendCertifiedSegment 87808 32 32 h32 checkBlocks_87808_87871_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_87872_87935_part0 :
    ∀ i : Fin 32, indexedBlockCheck (87872 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87872_87935_part1 :
    ∀ i : Fin 32, indexedBlockCheck (87904 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87872_87935 :
    ∀ i : Fin 64, indexedBlockCheck (87872 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (87872 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 87872 0 32 h0 checkBlocks_87872_87935_part0
  have h64 := extendCertifiedSegment 87872 32 32 h32 checkBlocks_87872_87935_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_87936_87999_part0 :
    ∀ i : Fin 32, indexedBlockCheck (87936 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87936_87999_part1 :
    ∀ i : Fin 32, indexedBlockCheck (87968 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_87936_87999 :
    ∀ i : Fin 64, indexedBlockCheck (87936 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (87936 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 87936 0 32 h0 checkBlocks_87936_87999_part0
  have h64 := extendCertifiedSegment 87936 32 32 h32 checkBlocks_87936_87999_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_88000_88063_part0 :
    ∀ i : Fin 32, indexedBlockCheck (88000 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88000_88063_part1 :
    ∀ i : Fin 32, indexedBlockCheck (88032 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88000_88063 :
    ∀ i : Fin 64, indexedBlockCheck (88000 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (88000 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 88000 0 32 h0 checkBlocks_88000_88063_part0
  have h64 := extendCertifiedSegment 88000 32 32 h32 checkBlocks_88000_88063_part1
  intro i
  exact h64 i.val i.isLt

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

private theorem checkBlocks_88064_88127_part0 :
    ∀ i : Fin 32, indexedBlockCheck (88064 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88064_88127_part1 :
    ∀ i : Fin 32, indexedBlockCheck (88096 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88064_88127 :
    ∀ i : Fin 64, indexedBlockCheck (88064 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (88064 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 88064 0 32 h0 checkBlocks_88064_88127_part0
  have h64 := extendCertifiedSegment 88064 32 32 h32 checkBlocks_88064_88127_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_88128_88191_part0 :
    ∀ i : Fin 32, indexedBlockCheck (88128 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88128_88191_part1 :
    ∀ i : Fin 32, indexedBlockCheck (88160 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88128_88191 :
    ∀ i : Fin 64, indexedBlockCheck (88128 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (88128 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 88128 0 32 h0 checkBlocks_88128_88191_part0
  have h64 := extendCertifiedSegment 88128 32 32 h32 checkBlocks_88128_88191_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_88192_88255_part0 :
    ∀ i : Fin 32, indexedBlockCheck (88192 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88192_88255_part1 :
    ∀ i : Fin 32, indexedBlockCheck (88224 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88192_88255 :
    ∀ i : Fin 64, indexedBlockCheck (88192 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (88192 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 88192 0 32 h0 checkBlocks_88192_88255_part0
  have h64 := extendCertifiedSegment 88192 32 32 h32 checkBlocks_88192_88255_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_88256_88319_part0 :
    ∀ i : Fin 32, indexedBlockCheck (88256 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88256_88319_part1 :
    ∀ i : Fin 32, indexedBlockCheck (88288 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88256_88319 :
    ∀ i : Fin 64, indexedBlockCheck (88256 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (88256 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 88256 0 32 h0 checkBlocks_88256_88319_part0
  have h64 := extendCertifiedSegment 88256 32 32 h32 checkBlocks_88256_88319_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_88320_88383_part0 :
    ∀ i : Fin 32, indexedBlockCheck (88320 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88320_88383_part1 :
    ∀ i : Fin 32, indexedBlockCheck (88352 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88320_88383 :
    ∀ i : Fin 64, indexedBlockCheck (88320 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (88320 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 88320 0 32 h0 checkBlocks_88320_88383_part0
  have h64 := extendCertifiedSegment 88320 32 32 h32 checkBlocks_88320_88383_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_88384_88447_part0 :
    ∀ i : Fin 32, indexedBlockCheck (88384 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88384_88447_part1 :
    ∀ i : Fin 32, indexedBlockCheck (88416 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88384_88447 :
    ∀ i : Fin 64, indexedBlockCheck (88384 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (88384 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 88384 0 32 h0 checkBlocks_88384_88447_part0
  have h64 := extendCertifiedSegment 88384 32 32 h32 checkBlocks_88384_88447_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_88448_88511_part0 :
    ∀ i : Fin 32, indexedBlockCheck (88448 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88448_88511_part1 :
    ∀ i : Fin 32, indexedBlockCheck (88480 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88448_88511 :
    ∀ i : Fin 64, indexedBlockCheck (88448 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (88448 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 88448 0 32 h0 checkBlocks_88448_88511_part0
  have h64 := extendCertifiedSegment 88448 32 32 h32 checkBlocks_88448_88511_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_88512_88575_part0 :
    ∀ i : Fin 32, indexedBlockCheck (88512 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88512_88575_part1 :
    ∀ i : Fin 32, indexedBlockCheck (88544 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88512_88575 :
    ∀ i : Fin 64, indexedBlockCheck (88512 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (88512 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 88512 0 32 h0 checkBlocks_88512_88575_part0
  have h64 := extendCertifiedSegment 88512 32 32 h32 checkBlocks_88512_88575_part1
  intro i
  exact h64 i.val i.isLt

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

private theorem checkBlocks_88576_88639_part0 :
    ∀ i : Fin 32, indexedBlockCheck (88576 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88576_88639_part1 :
    ∀ i : Fin 32, indexedBlockCheck (88608 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88576_88639 :
    ∀ i : Fin 64, indexedBlockCheck (88576 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (88576 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 88576 0 32 h0 checkBlocks_88576_88639_part0
  have h64 := extendCertifiedSegment 88576 32 32 h32 checkBlocks_88576_88639_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_88640_88703_part0 :
    ∀ i : Fin 32, indexedBlockCheck (88640 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88640_88703_part1 :
    ∀ i : Fin 32, indexedBlockCheck (88672 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88640_88703 :
    ∀ i : Fin 64, indexedBlockCheck (88640 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (88640 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 88640 0 32 h0 checkBlocks_88640_88703_part0
  have h64 := extendCertifiedSegment 88640 32 32 h32 checkBlocks_88640_88703_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_88704_88767_part0 :
    ∀ i : Fin 32, indexedBlockCheck (88704 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88704_88767_part1 :
    ∀ i : Fin 32, indexedBlockCheck (88736 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88704_88767 :
    ∀ i : Fin 64, indexedBlockCheck (88704 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (88704 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 88704 0 32 h0 checkBlocks_88704_88767_part0
  have h64 := extendCertifiedSegment 88704 32 32 h32 checkBlocks_88704_88767_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_88768_88831_part0 :
    ∀ i : Fin 32, indexedBlockCheck (88768 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88768_88831_part1 :
    ∀ i : Fin 32, indexedBlockCheck (88800 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88768_88831 :
    ∀ i : Fin 64, indexedBlockCheck (88768 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (88768 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 88768 0 32 h0 checkBlocks_88768_88831_part0
  have h64 := extendCertifiedSegment 88768 32 32 h32 checkBlocks_88768_88831_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_88832_88895_part0 :
    ∀ i : Fin 32, indexedBlockCheck (88832 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88832_88895_part1 :
    ∀ i : Fin 32, indexedBlockCheck (88864 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88832_88895 :
    ∀ i : Fin 64, indexedBlockCheck (88832 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (88832 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 88832 0 32 h0 checkBlocks_88832_88895_part0
  have h64 := extendCertifiedSegment 88832 32 32 h32 checkBlocks_88832_88895_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_88896_88959_part0 :
    ∀ i : Fin 32, indexedBlockCheck (88896 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88896_88959_part1 :
    ∀ i : Fin 32, indexedBlockCheck (88928 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88896_88959 :
    ∀ i : Fin 64, indexedBlockCheck (88896 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (88896 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 88896 0 32 h0 checkBlocks_88896_88959_part0
  have h64 := extendCertifiedSegment 88896 32 32 h32 checkBlocks_88896_88959_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_88960_89023_part0 :
    ∀ i : Fin 32, indexedBlockCheck (88960 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88960_89023_part1 :
    ∀ i : Fin 32, indexedBlockCheck (88992 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_88960_89023 :
    ∀ i : Fin 64, indexedBlockCheck (88960 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (88960 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 88960 0 32 h0 checkBlocks_88960_89023_part0
  have h64 := extendCertifiedSegment 88960 32 32 h32 checkBlocks_88960_89023_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_89024_89087_part0 :
    ∀ i : Fin 32, indexedBlockCheck (89024 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_89024_89087_part1 :
    ∀ i : Fin 32, indexedBlockCheck (89056 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_89024_89087 :
    ∀ i : Fin 64, indexedBlockCheck (89024 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (89024 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 89024 0 32 h0 checkBlocks_89024_89087_part0
  have h64 := extendCertifiedSegment 89024 32 32 h32 checkBlocks_89024_89087_part1
  intro i
  exact h64 i.val i.isLt

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
