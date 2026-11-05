/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 64512 through 66559 -/

public section

namespace SptClassification.Sieve

-- Bound memory by checking small certificate pieces sequentially.
set_option Elab.async false

private theorem checkBlocks_64512_64575_part0 :
    ∀ i : Fin 32, indexedBlockCheck (64512 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_64512_64575_part1 :
    ∀ i : Fin 32, indexedBlockCheck (64544 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_64512_64575 :
    ∀ i : Fin 64, indexedBlockCheck (64512 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (64512 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 64512 0 32 h0 checkBlocks_64512_64575_part0
  have h64 := extendCertifiedSegment 64512 32 32 h32 checkBlocks_64512_64575_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_64576_64639_part0 :
    ∀ i : Fin 32, indexedBlockCheck (64576 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_64576_64639_part1 :
    ∀ i : Fin 32, indexedBlockCheck (64608 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_64576_64639 :
    ∀ i : Fin 64, indexedBlockCheck (64576 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (64576 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 64576 0 32 h0 checkBlocks_64576_64639_part0
  have h64 := extendCertifiedSegment 64576 32 32 h32 checkBlocks_64576_64639_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_64640_64703_part0 :
    ∀ i : Fin 32, indexedBlockCheck (64640 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_64640_64703_part1 :
    ∀ i : Fin 32, indexedBlockCheck (64672 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_64640_64703 :
    ∀ i : Fin 64, indexedBlockCheck (64640 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (64640 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 64640 0 32 h0 checkBlocks_64640_64703_part0
  have h64 := extendCertifiedSegment 64640 32 32 h32 checkBlocks_64640_64703_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_64704_64767_part0 :
    ∀ i : Fin 32, indexedBlockCheck (64704 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_64704_64767_part1 :
    ∀ i : Fin 32, indexedBlockCheck (64736 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_64704_64767 :
    ∀ i : Fin 64, indexedBlockCheck (64704 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (64704 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 64704 0 32 h0 checkBlocks_64704_64767_part0
  have h64 := extendCertifiedSegment 64704 32 32 h32 checkBlocks_64704_64767_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_64768_64831_part0 :
    ∀ i : Fin 32, indexedBlockCheck (64768 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_64768_64831_part1 :
    ∀ i : Fin 32, indexedBlockCheck (64800 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_64768_64831 :
    ∀ i : Fin 64, indexedBlockCheck (64768 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (64768 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 64768 0 32 h0 checkBlocks_64768_64831_part0
  have h64 := extendCertifiedSegment 64768 32 32 h32 checkBlocks_64768_64831_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_64832_64895_part0 :
    ∀ i : Fin 32, indexedBlockCheck (64832 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_64832_64895_part1 :
    ∀ i : Fin 32, indexedBlockCheck (64864 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_64832_64895 :
    ∀ i : Fin 64, indexedBlockCheck (64832 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (64832 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 64832 0 32 h0 checkBlocks_64832_64895_part0
  have h64 := extendCertifiedSegment 64832 32 32 h32 checkBlocks_64832_64895_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_64896_64959_part0 :
    ∀ i : Fin 32, indexedBlockCheck (64896 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_64896_64959_part1 :
    ∀ i : Fin 32, indexedBlockCheck (64928 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_64896_64959 :
    ∀ i : Fin 64, indexedBlockCheck (64896 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (64896 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 64896 0 32 h0 checkBlocks_64896_64959_part0
  have h64 := extendCertifiedSegment 64896 32 32 h32 checkBlocks_64896_64959_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_64960_65023_part0 :
    ∀ i : Fin 32, indexedBlockCheck (64960 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_64960_65023_part1 :
    ∀ i : Fin 32, indexedBlockCheck (64992 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_64960_65023 :
    ∀ i : Fin 64, indexedBlockCheck (64960 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (64960 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 64960 0 32 h0 checkBlocks_64960_65023_part0
  have h64 := extendCertifiedSegment 64960 32 32 h32 checkBlocks_64960_65023_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_64512_65023 :
    ∀ i : Fin 512, indexedBlockCheck (64512 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (64512 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 64512 0 64 h0 checkBlocks_64512_64575
  have h128 := extendCertifiedSegment 64512 64 64 h64 checkBlocks_64576_64639
  have h192 := extendCertifiedSegment 64512 128 64 h128 checkBlocks_64640_64703
  have h256 := extendCertifiedSegment 64512 192 64 h192 checkBlocks_64704_64767
  have h320 := extendCertifiedSegment 64512 256 64 h256 checkBlocks_64768_64831
  have h384 := extendCertifiedSegment 64512 320 64 h320 checkBlocks_64832_64895
  have h448 := extendCertifiedSegment 64512 384 64 h384 checkBlocks_64896_64959
  have h512 := extendCertifiedSegment 64512 448 64 h448 checkBlocks_64960_65023
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_65024_65087_part0 :
    ∀ i : Fin 32, indexedBlockCheck (65024 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_65024_65087_part1 :
    ∀ i : Fin 32, indexedBlockCheck (65056 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_65024_65087 :
    ∀ i : Fin 64, indexedBlockCheck (65024 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (65024 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 65024 0 32 h0 checkBlocks_65024_65087_part0
  have h64 := extendCertifiedSegment 65024 32 32 h32 checkBlocks_65024_65087_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_65088_65151_part0 :
    ∀ i : Fin 32, indexedBlockCheck (65088 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_65088_65151_part1 :
    ∀ i : Fin 32, indexedBlockCheck (65120 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_65088_65151 :
    ∀ i : Fin 64, indexedBlockCheck (65088 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (65088 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 65088 0 32 h0 checkBlocks_65088_65151_part0
  have h64 := extendCertifiedSegment 65088 32 32 h32 checkBlocks_65088_65151_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_65152_65215_part0 :
    ∀ i : Fin 32, indexedBlockCheck (65152 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_65152_65215_part1 :
    ∀ i : Fin 32, indexedBlockCheck (65184 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_65152_65215 :
    ∀ i : Fin 64, indexedBlockCheck (65152 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (65152 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 65152 0 32 h0 checkBlocks_65152_65215_part0
  have h64 := extendCertifiedSegment 65152 32 32 h32 checkBlocks_65152_65215_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_65216_65279_part0 :
    ∀ i : Fin 32, indexedBlockCheck (65216 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_65216_65279_part1 :
    ∀ i : Fin 32, indexedBlockCheck (65248 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_65216_65279 :
    ∀ i : Fin 64, indexedBlockCheck (65216 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (65216 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 65216 0 32 h0 checkBlocks_65216_65279_part0
  have h64 := extendCertifiedSegment 65216 32 32 h32 checkBlocks_65216_65279_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_65280_65343_part0 :
    ∀ i : Fin 32, indexedBlockCheck (65280 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_65280_65343_part1 :
    ∀ i : Fin 32, indexedBlockCheck (65312 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_65280_65343 :
    ∀ i : Fin 64, indexedBlockCheck (65280 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (65280 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 65280 0 32 h0 checkBlocks_65280_65343_part0
  have h64 := extendCertifiedSegment 65280 32 32 h32 checkBlocks_65280_65343_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_65344_65407_part0 :
    ∀ i : Fin 32, indexedBlockCheck (65344 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_65344_65407_part1 :
    ∀ i : Fin 32, indexedBlockCheck (65376 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_65344_65407 :
    ∀ i : Fin 64, indexedBlockCheck (65344 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (65344 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 65344 0 32 h0 checkBlocks_65344_65407_part0
  have h64 := extendCertifiedSegment 65344 32 32 h32 checkBlocks_65344_65407_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_65408_65471_part0 :
    ∀ i : Fin 32, indexedBlockCheck (65408 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_65408_65471_part1 :
    ∀ i : Fin 32, indexedBlockCheck (65440 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_65408_65471 :
    ∀ i : Fin 64, indexedBlockCheck (65408 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (65408 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 65408 0 32 h0 checkBlocks_65408_65471_part0
  have h64 := extendCertifiedSegment 65408 32 32 h32 checkBlocks_65408_65471_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_65472_65535_part0 :
    ∀ i : Fin 32, indexedBlockCheck (65472 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_65472_65535_part1 :
    ∀ i : Fin 32, indexedBlockCheck (65504 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_65472_65535 :
    ∀ i : Fin 64, indexedBlockCheck (65472 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (65472 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 65472 0 32 h0 checkBlocks_65472_65535_part0
  have h64 := extendCertifiedSegment 65472 32 32 h32 checkBlocks_65472_65535_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_65024_65535 :
    ∀ i : Fin 512, indexedBlockCheck (65024 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (65024 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 65024 0 64 h0 checkBlocks_65024_65087
  have h128 := extendCertifiedSegment 65024 64 64 h64 checkBlocks_65088_65151
  have h192 := extendCertifiedSegment 65024 128 64 h128 checkBlocks_65152_65215
  have h256 := extendCertifiedSegment 65024 192 64 h192 checkBlocks_65216_65279
  have h320 := extendCertifiedSegment 65024 256 64 h256 checkBlocks_65280_65343
  have h384 := extendCertifiedSegment 65024 320 64 h320 checkBlocks_65344_65407
  have h448 := extendCertifiedSegment 65024 384 64 h384 checkBlocks_65408_65471
  have h512 := extendCertifiedSegment 65024 448 64 h448 checkBlocks_65472_65535
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_65536_65599_part0 :
    ∀ i : Fin 32, indexedBlockCheck (65536 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_65536_65599_part1 :
    ∀ i : Fin 32, indexedBlockCheck (65568 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_65536_65599 :
    ∀ i : Fin 64, indexedBlockCheck (65536 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (65536 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 65536 0 32 h0 checkBlocks_65536_65599_part0
  have h64 := extendCertifiedSegment 65536 32 32 h32 checkBlocks_65536_65599_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_65600_65663_part0 :
    ∀ i : Fin 32, indexedBlockCheck (65600 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_65600_65663_part1 :
    ∀ i : Fin 32, indexedBlockCheck (65632 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_65600_65663 :
    ∀ i : Fin 64, indexedBlockCheck (65600 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (65600 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 65600 0 32 h0 checkBlocks_65600_65663_part0
  have h64 := extendCertifiedSegment 65600 32 32 h32 checkBlocks_65600_65663_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_65664_65727_part0 :
    ∀ i : Fin 32, indexedBlockCheck (65664 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_65664_65727_part1 :
    ∀ i : Fin 32, indexedBlockCheck (65696 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_65664_65727 :
    ∀ i : Fin 64, indexedBlockCheck (65664 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (65664 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 65664 0 32 h0 checkBlocks_65664_65727_part0
  have h64 := extendCertifiedSegment 65664 32 32 h32 checkBlocks_65664_65727_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_65728_65791_part0 :
    ∀ i : Fin 32, indexedBlockCheck (65728 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_65728_65791_part1 :
    ∀ i : Fin 32, indexedBlockCheck (65760 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_65728_65791 :
    ∀ i : Fin 64, indexedBlockCheck (65728 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (65728 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 65728 0 32 h0 checkBlocks_65728_65791_part0
  have h64 := extendCertifiedSegment 65728 32 32 h32 checkBlocks_65728_65791_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_65792_65855_part0 :
    ∀ i : Fin 32, indexedBlockCheck (65792 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_65792_65855_part1 :
    ∀ i : Fin 32, indexedBlockCheck (65824 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_65792_65855 :
    ∀ i : Fin 64, indexedBlockCheck (65792 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (65792 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 65792 0 32 h0 checkBlocks_65792_65855_part0
  have h64 := extendCertifiedSegment 65792 32 32 h32 checkBlocks_65792_65855_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_65856_65919_part0 :
    ∀ i : Fin 32, indexedBlockCheck (65856 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_65856_65919_part1 :
    ∀ i : Fin 32, indexedBlockCheck (65888 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_65856_65919 :
    ∀ i : Fin 64, indexedBlockCheck (65856 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (65856 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 65856 0 32 h0 checkBlocks_65856_65919_part0
  have h64 := extendCertifiedSegment 65856 32 32 h32 checkBlocks_65856_65919_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_65920_65983_part0 :
    ∀ i : Fin 32, indexedBlockCheck (65920 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_65920_65983_part1 :
    ∀ i : Fin 32, indexedBlockCheck (65952 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_65920_65983 :
    ∀ i : Fin 64, indexedBlockCheck (65920 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (65920 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 65920 0 32 h0 checkBlocks_65920_65983_part0
  have h64 := extendCertifiedSegment 65920 32 32 h32 checkBlocks_65920_65983_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_65984_66047_part0 :
    ∀ i : Fin 32, indexedBlockCheck (65984 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_65984_66047_part1 :
    ∀ i : Fin 32, indexedBlockCheck (66016 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_65984_66047 :
    ∀ i : Fin 64, indexedBlockCheck (65984 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (65984 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 65984 0 32 h0 checkBlocks_65984_66047_part0
  have h64 := extendCertifiedSegment 65984 32 32 h32 checkBlocks_65984_66047_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_65536_66047 :
    ∀ i : Fin 512, indexedBlockCheck (65536 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (65536 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 65536 0 64 h0 checkBlocks_65536_65599
  have h128 := extendCertifiedSegment 65536 64 64 h64 checkBlocks_65600_65663
  have h192 := extendCertifiedSegment 65536 128 64 h128 checkBlocks_65664_65727
  have h256 := extendCertifiedSegment 65536 192 64 h192 checkBlocks_65728_65791
  have h320 := extendCertifiedSegment 65536 256 64 h256 checkBlocks_65792_65855
  have h384 := extendCertifiedSegment 65536 320 64 h320 checkBlocks_65856_65919
  have h448 := extendCertifiedSegment 65536 384 64 h384 checkBlocks_65920_65983
  have h512 := extendCertifiedSegment 65536 448 64 h448 checkBlocks_65984_66047
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_66048_66111_part0 :
    ∀ i : Fin 32, indexedBlockCheck (66048 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_66048_66111_part1 :
    ∀ i : Fin 32, indexedBlockCheck (66080 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_66048_66111 :
    ∀ i : Fin 64, indexedBlockCheck (66048 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (66048 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 66048 0 32 h0 checkBlocks_66048_66111_part0
  have h64 := extendCertifiedSegment 66048 32 32 h32 checkBlocks_66048_66111_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_66112_66175_part0 :
    ∀ i : Fin 32, indexedBlockCheck (66112 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_66112_66175_part1 :
    ∀ i : Fin 32, indexedBlockCheck (66144 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_66112_66175 :
    ∀ i : Fin 64, indexedBlockCheck (66112 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (66112 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 66112 0 32 h0 checkBlocks_66112_66175_part0
  have h64 := extendCertifiedSegment 66112 32 32 h32 checkBlocks_66112_66175_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_66176_66239_part0 :
    ∀ i : Fin 32, indexedBlockCheck (66176 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_66176_66239_part1 :
    ∀ i : Fin 32, indexedBlockCheck (66208 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_66176_66239 :
    ∀ i : Fin 64, indexedBlockCheck (66176 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (66176 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 66176 0 32 h0 checkBlocks_66176_66239_part0
  have h64 := extendCertifiedSegment 66176 32 32 h32 checkBlocks_66176_66239_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_66240_66303_part0 :
    ∀ i : Fin 32, indexedBlockCheck (66240 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_66240_66303_part1 :
    ∀ i : Fin 32, indexedBlockCheck (66272 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_66240_66303 :
    ∀ i : Fin 64, indexedBlockCheck (66240 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (66240 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 66240 0 32 h0 checkBlocks_66240_66303_part0
  have h64 := extendCertifiedSegment 66240 32 32 h32 checkBlocks_66240_66303_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_66304_66367_part0 :
    ∀ i : Fin 32, indexedBlockCheck (66304 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_66304_66367_part1 :
    ∀ i : Fin 32, indexedBlockCheck (66336 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_66304_66367 :
    ∀ i : Fin 64, indexedBlockCheck (66304 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (66304 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 66304 0 32 h0 checkBlocks_66304_66367_part0
  have h64 := extendCertifiedSegment 66304 32 32 h32 checkBlocks_66304_66367_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_66368_66431_part0 :
    ∀ i : Fin 32, indexedBlockCheck (66368 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_66368_66431_part1 :
    ∀ i : Fin 32, indexedBlockCheck (66400 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_66368_66431 :
    ∀ i : Fin 64, indexedBlockCheck (66368 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (66368 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 66368 0 32 h0 checkBlocks_66368_66431_part0
  have h64 := extendCertifiedSegment 66368 32 32 h32 checkBlocks_66368_66431_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_66432_66495_part0 :
    ∀ i : Fin 32, indexedBlockCheck (66432 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_66432_66495_part1 :
    ∀ i : Fin 32, indexedBlockCheck (66464 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_66432_66495 :
    ∀ i : Fin 64, indexedBlockCheck (66432 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (66432 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 66432 0 32 h0 checkBlocks_66432_66495_part0
  have h64 := extendCertifiedSegment 66432 32 32 h32 checkBlocks_66432_66495_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_66496_66559_part0 :
    ∀ i : Fin 32, indexedBlockCheck (66496 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_66496_66559_part1 :
    ∀ i : Fin 32, indexedBlockCheck (66528 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_66496_66559 :
    ∀ i : Fin 64, indexedBlockCheck (66496 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (66496 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 66496 0 32 h0 checkBlocks_66496_66559_part0
  have h64 := extendCertifiedSegment 66496 32 32 h32 checkBlocks_66496_66559_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_66048_66559 :
    ∀ i : Fin 512, indexedBlockCheck (66048 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (66048 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 66048 0 64 h0 checkBlocks_66048_66111
  have h128 := extendCertifiedSegment 66048 64 64 h64 checkBlocks_66112_66175
  have h192 := extendCertifiedSegment 66048 128 64 h128 checkBlocks_66176_66239
  have h256 := extendCertifiedSegment 66048 192 64 h192 checkBlocks_66240_66303
  have h320 := extendCertifiedSegment 66048 256 64 h256 checkBlocks_66304_66367
  have h384 := extendCertifiedSegment 66048 320 64 h320 checkBlocks_66368_66431
  have h448 := extendCertifiedSegment 66048 384 64 h384 checkBlocks_66432_66495
  have h512 := extendCertifiedSegment 66048 448 64 h448 checkBlocks_66496_66559
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [64512, 66560) passes the packed checker. -/
public theorem blocks_in_64512_66560 :
    ∀ i : Fin 2048, indexedBlockCheck (64512 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (64512 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 64512 0 512 h0 checkBlocks_64512_65023
  have h1024 := extendCertifiedSegment 64512 512 512 h512 checkBlocks_65024_65535
  have h1536 := extendCertifiedSegment 64512 1024 512 h1024 checkBlocks_65536_66047
  have h2048 := extendCertifiedSegment 64512 1536 512 h1536 checkBlocks_66048_66559
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
