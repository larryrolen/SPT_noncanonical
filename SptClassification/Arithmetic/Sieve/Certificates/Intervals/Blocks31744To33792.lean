/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 31744 through 33791 -/

public section

namespace SptClassification.Sieve

-- Bound memory by checking small certificate pieces sequentially.
set_option Elab.async false

private theorem checkBlocks_31744_31807_part0 :
    ∀ i : Fin 32, indexedBlockCheck (31744 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_31744_31807_part1 :
    ∀ i : Fin 32, indexedBlockCheck (31776 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_31744_31807 :
    ∀ i : Fin 64, indexedBlockCheck (31744 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (31744 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 31744 0 32 h0 checkBlocks_31744_31807_part0
  have h64 := extendCertifiedSegment 31744 32 32 h32 checkBlocks_31744_31807_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_31808_31871_part0 :
    ∀ i : Fin 32, indexedBlockCheck (31808 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_31808_31871_part1 :
    ∀ i : Fin 32, indexedBlockCheck (31840 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_31808_31871 :
    ∀ i : Fin 64, indexedBlockCheck (31808 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (31808 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 31808 0 32 h0 checkBlocks_31808_31871_part0
  have h64 := extendCertifiedSegment 31808 32 32 h32 checkBlocks_31808_31871_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_31872_31935_part0 :
    ∀ i : Fin 32, indexedBlockCheck (31872 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_31872_31935_part1 :
    ∀ i : Fin 32, indexedBlockCheck (31904 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_31872_31935 :
    ∀ i : Fin 64, indexedBlockCheck (31872 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (31872 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 31872 0 32 h0 checkBlocks_31872_31935_part0
  have h64 := extendCertifiedSegment 31872 32 32 h32 checkBlocks_31872_31935_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_31936_31999_part0 :
    ∀ i : Fin 32, indexedBlockCheck (31936 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_31936_31999_part1 :
    ∀ i : Fin 32, indexedBlockCheck (31968 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_31936_31999 :
    ∀ i : Fin 64, indexedBlockCheck (31936 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (31936 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 31936 0 32 h0 checkBlocks_31936_31999_part0
  have h64 := extendCertifiedSegment 31936 32 32 h32 checkBlocks_31936_31999_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_32000_32063_part0 :
    ∀ i : Fin 32, indexedBlockCheck (32000 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32000_32063_part1 :
    ∀ i : Fin 32, indexedBlockCheck (32032 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32000_32063 :
    ∀ i : Fin 64, indexedBlockCheck (32000 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (32000 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 32000 0 32 h0 checkBlocks_32000_32063_part0
  have h64 := extendCertifiedSegment 32000 32 32 h32 checkBlocks_32000_32063_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_32064_32127_part0 :
    ∀ i : Fin 32, indexedBlockCheck (32064 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32064_32127_part1 :
    ∀ i : Fin 32, indexedBlockCheck (32096 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32064_32127 :
    ∀ i : Fin 64, indexedBlockCheck (32064 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (32064 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 32064 0 32 h0 checkBlocks_32064_32127_part0
  have h64 := extendCertifiedSegment 32064 32 32 h32 checkBlocks_32064_32127_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_32128_32191_part0 :
    ∀ i : Fin 32, indexedBlockCheck (32128 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32128_32191_part1 :
    ∀ i : Fin 32, indexedBlockCheck (32160 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32128_32191 :
    ∀ i : Fin 64, indexedBlockCheck (32128 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (32128 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 32128 0 32 h0 checkBlocks_32128_32191_part0
  have h64 := extendCertifiedSegment 32128 32 32 h32 checkBlocks_32128_32191_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_32192_32255_part0 :
    ∀ i : Fin 32, indexedBlockCheck (32192 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32192_32255_part1 :
    ∀ i : Fin 32, indexedBlockCheck (32224 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32192_32255 :
    ∀ i : Fin 64, indexedBlockCheck (32192 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (32192 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 32192 0 32 h0 checkBlocks_32192_32255_part0
  have h64 := extendCertifiedSegment 32192 32 32 h32 checkBlocks_32192_32255_part1
  intro i
  exact h64 i.val i.isLt

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

private theorem checkBlocks_32256_32319_part0 :
    ∀ i : Fin 32, indexedBlockCheck (32256 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32256_32319_part1 :
    ∀ i : Fin 32, indexedBlockCheck (32288 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32256_32319 :
    ∀ i : Fin 64, indexedBlockCheck (32256 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (32256 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 32256 0 32 h0 checkBlocks_32256_32319_part0
  have h64 := extendCertifiedSegment 32256 32 32 h32 checkBlocks_32256_32319_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_32320_32383_part0 :
    ∀ i : Fin 32, indexedBlockCheck (32320 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32320_32383_part1 :
    ∀ i : Fin 32, indexedBlockCheck (32352 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32320_32383 :
    ∀ i : Fin 64, indexedBlockCheck (32320 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (32320 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 32320 0 32 h0 checkBlocks_32320_32383_part0
  have h64 := extendCertifiedSegment 32320 32 32 h32 checkBlocks_32320_32383_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_32384_32447_part0 :
    ∀ i : Fin 32, indexedBlockCheck (32384 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32384_32447_part1 :
    ∀ i : Fin 32, indexedBlockCheck (32416 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32384_32447 :
    ∀ i : Fin 64, indexedBlockCheck (32384 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (32384 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 32384 0 32 h0 checkBlocks_32384_32447_part0
  have h64 := extendCertifiedSegment 32384 32 32 h32 checkBlocks_32384_32447_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_32448_32511_part0 :
    ∀ i : Fin 32, indexedBlockCheck (32448 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32448_32511_part1 :
    ∀ i : Fin 32, indexedBlockCheck (32480 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32448_32511 :
    ∀ i : Fin 64, indexedBlockCheck (32448 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (32448 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 32448 0 32 h0 checkBlocks_32448_32511_part0
  have h64 := extendCertifiedSegment 32448 32 32 h32 checkBlocks_32448_32511_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_32512_32575_part0 :
    ∀ i : Fin 32, indexedBlockCheck (32512 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32512_32575_part1 :
    ∀ i : Fin 32, indexedBlockCheck (32544 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32512_32575 :
    ∀ i : Fin 64, indexedBlockCheck (32512 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (32512 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 32512 0 32 h0 checkBlocks_32512_32575_part0
  have h64 := extendCertifiedSegment 32512 32 32 h32 checkBlocks_32512_32575_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_32576_32639_part0 :
    ∀ i : Fin 32, indexedBlockCheck (32576 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32576_32639_part1 :
    ∀ i : Fin 32, indexedBlockCheck (32608 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32576_32639 :
    ∀ i : Fin 64, indexedBlockCheck (32576 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (32576 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 32576 0 32 h0 checkBlocks_32576_32639_part0
  have h64 := extendCertifiedSegment 32576 32 32 h32 checkBlocks_32576_32639_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_32640_32703_part0 :
    ∀ i : Fin 32, indexedBlockCheck (32640 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32640_32703_part1 :
    ∀ i : Fin 32, indexedBlockCheck (32672 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32640_32703 :
    ∀ i : Fin 64, indexedBlockCheck (32640 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (32640 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 32640 0 32 h0 checkBlocks_32640_32703_part0
  have h64 := extendCertifiedSegment 32640 32 32 h32 checkBlocks_32640_32703_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_32704_32767_part0 :
    ∀ i : Fin 32, indexedBlockCheck (32704 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32704_32767_part1 :
    ∀ i : Fin 32, indexedBlockCheck (32736 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32704_32767 :
    ∀ i : Fin 64, indexedBlockCheck (32704 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (32704 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 32704 0 32 h0 checkBlocks_32704_32767_part0
  have h64 := extendCertifiedSegment 32704 32 32 h32 checkBlocks_32704_32767_part1
  intro i
  exact h64 i.val i.isLt

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

private theorem checkBlocks_32768_32831_part0 :
    ∀ i : Fin 32, indexedBlockCheck (32768 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32768_32831_part1 :
    ∀ i : Fin 32, indexedBlockCheck (32800 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32768_32831 :
    ∀ i : Fin 64, indexedBlockCheck (32768 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (32768 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 32768 0 32 h0 checkBlocks_32768_32831_part0
  have h64 := extendCertifiedSegment 32768 32 32 h32 checkBlocks_32768_32831_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_32832_32895_part0 :
    ∀ i : Fin 32, indexedBlockCheck (32832 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32832_32895_part1 :
    ∀ i : Fin 32, indexedBlockCheck (32864 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32832_32895 :
    ∀ i : Fin 64, indexedBlockCheck (32832 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (32832 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 32832 0 32 h0 checkBlocks_32832_32895_part0
  have h64 := extendCertifiedSegment 32832 32 32 h32 checkBlocks_32832_32895_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_32896_32959_part0 :
    ∀ i : Fin 32, indexedBlockCheck (32896 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32896_32959_part1 :
    ∀ i : Fin 32, indexedBlockCheck (32928 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32896_32959 :
    ∀ i : Fin 64, indexedBlockCheck (32896 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (32896 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 32896 0 32 h0 checkBlocks_32896_32959_part0
  have h64 := extendCertifiedSegment 32896 32 32 h32 checkBlocks_32896_32959_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_32960_33023_part0 :
    ∀ i : Fin 32, indexedBlockCheck (32960 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32960_33023_part1 :
    ∀ i : Fin 32, indexedBlockCheck (32992 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_32960_33023 :
    ∀ i : Fin 64, indexedBlockCheck (32960 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (32960 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 32960 0 32 h0 checkBlocks_32960_33023_part0
  have h64 := extendCertifiedSegment 32960 32 32 h32 checkBlocks_32960_33023_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_33024_33087_part0 :
    ∀ i : Fin 32, indexedBlockCheck (33024 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33024_33087_part1 :
    ∀ i : Fin 32, indexedBlockCheck (33056 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33024_33087 :
    ∀ i : Fin 64, indexedBlockCheck (33024 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (33024 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 33024 0 32 h0 checkBlocks_33024_33087_part0
  have h64 := extendCertifiedSegment 33024 32 32 h32 checkBlocks_33024_33087_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_33088_33151_part0 :
    ∀ i : Fin 32, indexedBlockCheck (33088 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33088_33151_part1 :
    ∀ i : Fin 32, indexedBlockCheck (33120 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33088_33151 :
    ∀ i : Fin 64, indexedBlockCheck (33088 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (33088 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 33088 0 32 h0 checkBlocks_33088_33151_part0
  have h64 := extendCertifiedSegment 33088 32 32 h32 checkBlocks_33088_33151_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_33152_33215_part0 :
    ∀ i : Fin 32, indexedBlockCheck (33152 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33152_33215_part1 :
    ∀ i : Fin 32, indexedBlockCheck (33184 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33152_33215 :
    ∀ i : Fin 64, indexedBlockCheck (33152 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (33152 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 33152 0 32 h0 checkBlocks_33152_33215_part0
  have h64 := extendCertifiedSegment 33152 32 32 h32 checkBlocks_33152_33215_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_33216_33279_part0 :
    ∀ i : Fin 32, indexedBlockCheck (33216 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33216_33279_part1 :
    ∀ i : Fin 32, indexedBlockCheck (33248 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33216_33279 :
    ∀ i : Fin 64, indexedBlockCheck (33216 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (33216 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 33216 0 32 h0 checkBlocks_33216_33279_part0
  have h64 := extendCertifiedSegment 33216 32 32 h32 checkBlocks_33216_33279_part1
  intro i
  exact h64 i.val i.isLt

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

private theorem checkBlocks_33280_33343_part0 :
    ∀ i : Fin 32, indexedBlockCheck (33280 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33280_33343_part1 :
    ∀ i : Fin 32, indexedBlockCheck (33312 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33280_33343 :
    ∀ i : Fin 64, indexedBlockCheck (33280 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (33280 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 33280 0 32 h0 checkBlocks_33280_33343_part0
  have h64 := extendCertifiedSegment 33280 32 32 h32 checkBlocks_33280_33343_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_33344_33407_part0 :
    ∀ i : Fin 32, indexedBlockCheck (33344 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33344_33407_part1 :
    ∀ i : Fin 32, indexedBlockCheck (33376 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33344_33407 :
    ∀ i : Fin 64, indexedBlockCheck (33344 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (33344 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 33344 0 32 h0 checkBlocks_33344_33407_part0
  have h64 := extendCertifiedSegment 33344 32 32 h32 checkBlocks_33344_33407_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_33408_33471_part0 :
    ∀ i : Fin 32, indexedBlockCheck (33408 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33408_33471_part1 :
    ∀ i : Fin 32, indexedBlockCheck (33440 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33408_33471 :
    ∀ i : Fin 64, indexedBlockCheck (33408 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (33408 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 33408 0 32 h0 checkBlocks_33408_33471_part0
  have h64 := extendCertifiedSegment 33408 32 32 h32 checkBlocks_33408_33471_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_33472_33535_part0 :
    ∀ i : Fin 32, indexedBlockCheck (33472 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33472_33535_part1 :
    ∀ i : Fin 32, indexedBlockCheck (33504 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33472_33535 :
    ∀ i : Fin 64, indexedBlockCheck (33472 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (33472 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 33472 0 32 h0 checkBlocks_33472_33535_part0
  have h64 := extendCertifiedSegment 33472 32 32 h32 checkBlocks_33472_33535_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_33536_33599_part0 :
    ∀ i : Fin 32, indexedBlockCheck (33536 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33536_33599_part1 :
    ∀ i : Fin 32, indexedBlockCheck (33568 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33536_33599 :
    ∀ i : Fin 64, indexedBlockCheck (33536 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (33536 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 33536 0 32 h0 checkBlocks_33536_33599_part0
  have h64 := extendCertifiedSegment 33536 32 32 h32 checkBlocks_33536_33599_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_33600_33663_part0 :
    ∀ i : Fin 32, indexedBlockCheck (33600 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33600_33663_part1 :
    ∀ i : Fin 32, indexedBlockCheck (33632 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33600_33663 :
    ∀ i : Fin 64, indexedBlockCheck (33600 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (33600 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 33600 0 32 h0 checkBlocks_33600_33663_part0
  have h64 := extendCertifiedSegment 33600 32 32 h32 checkBlocks_33600_33663_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_33664_33727_part0 :
    ∀ i : Fin 32, indexedBlockCheck (33664 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33664_33727_part1 :
    ∀ i : Fin 32, indexedBlockCheck (33696 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33664_33727 :
    ∀ i : Fin 64, indexedBlockCheck (33664 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (33664 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 33664 0 32 h0 checkBlocks_33664_33727_part0
  have h64 := extendCertifiedSegment 33664 32 32 h32 checkBlocks_33664_33727_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_33728_33791_part0 :
    ∀ i : Fin 32, indexedBlockCheck (33728 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33728_33791_part1 :
    ∀ i : Fin 32, indexedBlockCheck (33760 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33728_33791 :
    ∀ i : Fin 64, indexedBlockCheck (33728 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (33728 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 33728 0 32 h0 checkBlocks_33728_33791_part0
  have h64 := extendCertifiedSegment 33728 32 32 h32 checkBlocks_33728_33791_part1
  intro i
  exact h64 i.val i.isLt

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
