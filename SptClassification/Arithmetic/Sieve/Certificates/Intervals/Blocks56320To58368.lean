/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 56320 through 58367 -/

public section

namespace SptClassification.Sieve

-- Bound memory by checking small certificate pieces sequentially.
set_option Elab.async false

private theorem checkBlocks_56320_56383_part0 :
    ∀ i : Fin 32, indexedBlockCheck (56320 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_56320_56383_part1 :
    ∀ i : Fin 32, indexedBlockCheck (56352 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_56320_56383 :
    ∀ i : Fin 64, indexedBlockCheck (56320 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (56320 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 56320 0 32 h0 checkBlocks_56320_56383_part0
  have h64 := extendCertifiedSegment 56320 32 32 h32 checkBlocks_56320_56383_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_56384_56447_part0 :
    ∀ i : Fin 32, indexedBlockCheck (56384 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_56384_56447_part1 :
    ∀ i : Fin 32, indexedBlockCheck (56416 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_56384_56447 :
    ∀ i : Fin 64, indexedBlockCheck (56384 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (56384 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 56384 0 32 h0 checkBlocks_56384_56447_part0
  have h64 := extendCertifiedSegment 56384 32 32 h32 checkBlocks_56384_56447_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_56448_56511_part0 :
    ∀ i : Fin 32, indexedBlockCheck (56448 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_56448_56511_part1 :
    ∀ i : Fin 32, indexedBlockCheck (56480 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_56448_56511 :
    ∀ i : Fin 64, indexedBlockCheck (56448 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (56448 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 56448 0 32 h0 checkBlocks_56448_56511_part0
  have h64 := extendCertifiedSegment 56448 32 32 h32 checkBlocks_56448_56511_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_56512_56575_part0 :
    ∀ i : Fin 32, indexedBlockCheck (56512 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_56512_56575_part1 :
    ∀ i : Fin 32, indexedBlockCheck (56544 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_56512_56575 :
    ∀ i : Fin 64, indexedBlockCheck (56512 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (56512 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 56512 0 32 h0 checkBlocks_56512_56575_part0
  have h64 := extendCertifiedSegment 56512 32 32 h32 checkBlocks_56512_56575_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_56576_56639_part0 :
    ∀ i : Fin 32, indexedBlockCheck (56576 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_56576_56639_part1 :
    ∀ i : Fin 32, indexedBlockCheck (56608 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_56576_56639 :
    ∀ i : Fin 64, indexedBlockCheck (56576 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (56576 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 56576 0 32 h0 checkBlocks_56576_56639_part0
  have h64 := extendCertifiedSegment 56576 32 32 h32 checkBlocks_56576_56639_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_56640_56703_part0 :
    ∀ i : Fin 32, indexedBlockCheck (56640 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_56640_56703_part1 :
    ∀ i : Fin 32, indexedBlockCheck (56672 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_56640_56703 :
    ∀ i : Fin 64, indexedBlockCheck (56640 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (56640 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 56640 0 32 h0 checkBlocks_56640_56703_part0
  have h64 := extendCertifiedSegment 56640 32 32 h32 checkBlocks_56640_56703_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_56704_56767_part0 :
    ∀ i : Fin 32, indexedBlockCheck (56704 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_56704_56767_part1 :
    ∀ i : Fin 32, indexedBlockCheck (56736 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_56704_56767 :
    ∀ i : Fin 64, indexedBlockCheck (56704 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (56704 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 56704 0 32 h0 checkBlocks_56704_56767_part0
  have h64 := extendCertifiedSegment 56704 32 32 h32 checkBlocks_56704_56767_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_56768_56831_part0 :
    ∀ i : Fin 32, indexedBlockCheck (56768 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_56768_56831_part1 :
    ∀ i : Fin 32, indexedBlockCheck (56800 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_56768_56831 :
    ∀ i : Fin 64, indexedBlockCheck (56768 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (56768 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 56768 0 32 h0 checkBlocks_56768_56831_part0
  have h64 := extendCertifiedSegment 56768 32 32 h32 checkBlocks_56768_56831_part1
  intro i
  exact h64 i.val i.isLt

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

private theorem checkBlocks_56832_56895_part0 :
    ∀ i : Fin 32, indexedBlockCheck (56832 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_56832_56895_part1 :
    ∀ i : Fin 32, indexedBlockCheck (56864 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_56832_56895 :
    ∀ i : Fin 64, indexedBlockCheck (56832 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (56832 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 56832 0 32 h0 checkBlocks_56832_56895_part0
  have h64 := extendCertifiedSegment 56832 32 32 h32 checkBlocks_56832_56895_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_56896_56959_part0 :
    ∀ i : Fin 32, indexedBlockCheck (56896 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_56896_56959_part1 :
    ∀ i : Fin 32, indexedBlockCheck (56928 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_56896_56959 :
    ∀ i : Fin 64, indexedBlockCheck (56896 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (56896 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 56896 0 32 h0 checkBlocks_56896_56959_part0
  have h64 := extendCertifiedSegment 56896 32 32 h32 checkBlocks_56896_56959_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_56960_57023_part0 :
    ∀ i : Fin 32, indexedBlockCheck (56960 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_56960_57023_part1 :
    ∀ i : Fin 32, indexedBlockCheck (56992 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_56960_57023 :
    ∀ i : Fin 64, indexedBlockCheck (56960 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (56960 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 56960 0 32 h0 checkBlocks_56960_57023_part0
  have h64 := extendCertifiedSegment 56960 32 32 h32 checkBlocks_56960_57023_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_57024_57087_part0 :
    ∀ i : Fin 32, indexedBlockCheck (57024 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57024_57087_part1 :
    ∀ i : Fin 32, indexedBlockCheck (57056 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57024_57087 :
    ∀ i : Fin 64, indexedBlockCheck (57024 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (57024 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 57024 0 32 h0 checkBlocks_57024_57087_part0
  have h64 := extendCertifiedSegment 57024 32 32 h32 checkBlocks_57024_57087_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_57088_57151_part0 :
    ∀ i : Fin 32, indexedBlockCheck (57088 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57088_57151_part1 :
    ∀ i : Fin 32, indexedBlockCheck (57120 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57088_57151 :
    ∀ i : Fin 64, indexedBlockCheck (57088 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (57088 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 57088 0 32 h0 checkBlocks_57088_57151_part0
  have h64 := extendCertifiedSegment 57088 32 32 h32 checkBlocks_57088_57151_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_57152_57215_part0 :
    ∀ i : Fin 32, indexedBlockCheck (57152 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57152_57215_part1 :
    ∀ i : Fin 32, indexedBlockCheck (57184 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57152_57215 :
    ∀ i : Fin 64, indexedBlockCheck (57152 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (57152 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 57152 0 32 h0 checkBlocks_57152_57215_part0
  have h64 := extendCertifiedSegment 57152 32 32 h32 checkBlocks_57152_57215_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_57216_57279_part0 :
    ∀ i : Fin 32, indexedBlockCheck (57216 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57216_57279_part1 :
    ∀ i : Fin 32, indexedBlockCheck (57248 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57216_57279 :
    ∀ i : Fin 64, indexedBlockCheck (57216 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (57216 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 57216 0 32 h0 checkBlocks_57216_57279_part0
  have h64 := extendCertifiedSegment 57216 32 32 h32 checkBlocks_57216_57279_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_57280_57343_part0 :
    ∀ i : Fin 32, indexedBlockCheck (57280 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57280_57343_part1 :
    ∀ i : Fin 32, indexedBlockCheck (57312 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57280_57343 :
    ∀ i : Fin 64, indexedBlockCheck (57280 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (57280 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 57280 0 32 h0 checkBlocks_57280_57343_part0
  have h64 := extendCertifiedSegment 57280 32 32 h32 checkBlocks_57280_57343_part1
  intro i
  exact h64 i.val i.isLt

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

private theorem checkBlocks_57344_57407_part0 :
    ∀ i : Fin 32, indexedBlockCheck (57344 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57344_57407_part1 :
    ∀ i : Fin 32, indexedBlockCheck (57376 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57344_57407 :
    ∀ i : Fin 64, indexedBlockCheck (57344 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (57344 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 57344 0 32 h0 checkBlocks_57344_57407_part0
  have h64 := extendCertifiedSegment 57344 32 32 h32 checkBlocks_57344_57407_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_57408_57471_part0 :
    ∀ i : Fin 32, indexedBlockCheck (57408 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57408_57471_part1 :
    ∀ i : Fin 32, indexedBlockCheck (57440 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57408_57471 :
    ∀ i : Fin 64, indexedBlockCheck (57408 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (57408 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 57408 0 32 h0 checkBlocks_57408_57471_part0
  have h64 := extendCertifiedSegment 57408 32 32 h32 checkBlocks_57408_57471_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_57472_57535_part0 :
    ∀ i : Fin 32, indexedBlockCheck (57472 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57472_57535_part1 :
    ∀ i : Fin 32, indexedBlockCheck (57504 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57472_57535 :
    ∀ i : Fin 64, indexedBlockCheck (57472 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (57472 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 57472 0 32 h0 checkBlocks_57472_57535_part0
  have h64 := extendCertifiedSegment 57472 32 32 h32 checkBlocks_57472_57535_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_57536_57599_part0 :
    ∀ i : Fin 32, indexedBlockCheck (57536 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57536_57599_part1 :
    ∀ i : Fin 32, indexedBlockCheck (57568 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57536_57599 :
    ∀ i : Fin 64, indexedBlockCheck (57536 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (57536 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 57536 0 32 h0 checkBlocks_57536_57599_part0
  have h64 := extendCertifiedSegment 57536 32 32 h32 checkBlocks_57536_57599_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_57600_57663_part0 :
    ∀ i : Fin 32, indexedBlockCheck (57600 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57600_57663_part1 :
    ∀ i : Fin 32, indexedBlockCheck (57632 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57600_57663 :
    ∀ i : Fin 64, indexedBlockCheck (57600 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (57600 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 57600 0 32 h0 checkBlocks_57600_57663_part0
  have h64 := extendCertifiedSegment 57600 32 32 h32 checkBlocks_57600_57663_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_57664_57727_part0 :
    ∀ i : Fin 32, indexedBlockCheck (57664 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57664_57727_part1 :
    ∀ i : Fin 32, indexedBlockCheck (57696 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57664_57727 :
    ∀ i : Fin 64, indexedBlockCheck (57664 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (57664 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 57664 0 32 h0 checkBlocks_57664_57727_part0
  have h64 := extendCertifiedSegment 57664 32 32 h32 checkBlocks_57664_57727_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_57728_57791_part0 :
    ∀ i : Fin 32, indexedBlockCheck (57728 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57728_57791_part1 :
    ∀ i : Fin 32, indexedBlockCheck (57760 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57728_57791 :
    ∀ i : Fin 64, indexedBlockCheck (57728 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (57728 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 57728 0 32 h0 checkBlocks_57728_57791_part0
  have h64 := extendCertifiedSegment 57728 32 32 h32 checkBlocks_57728_57791_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_57792_57855_part0 :
    ∀ i : Fin 32, indexedBlockCheck (57792 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57792_57855_part1 :
    ∀ i : Fin 32, indexedBlockCheck (57824 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57792_57855 :
    ∀ i : Fin 64, indexedBlockCheck (57792 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (57792 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 57792 0 32 h0 checkBlocks_57792_57855_part0
  have h64 := extendCertifiedSegment 57792 32 32 h32 checkBlocks_57792_57855_part1
  intro i
  exact h64 i.val i.isLt

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

private theorem checkBlocks_57856_57919_part0 :
    ∀ i : Fin 32, indexedBlockCheck (57856 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57856_57919_part1 :
    ∀ i : Fin 32, indexedBlockCheck (57888 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57856_57919 :
    ∀ i : Fin 64, indexedBlockCheck (57856 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (57856 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 57856 0 32 h0 checkBlocks_57856_57919_part0
  have h64 := extendCertifiedSegment 57856 32 32 h32 checkBlocks_57856_57919_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_57920_57983_part0 :
    ∀ i : Fin 32, indexedBlockCheck (57920 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57920_57983_part1 :
    ∀ i : Fin 32, indexedBlockCheck (57952 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57920_57983 :
    ∀ i : Fin 64, indexedBlockCheck (57920 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (57920 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 57920 0 32 h0 checkBlocks_57920_57983_part0
  have h64 := extendCertifiedSegment 57920 32 32 h32 checkBlocks_57920_57983_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_57984_58047_part0 :
    ∀ i : Fin 32, indexedBlockCheck (57984 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57984_58047_part1 :
    ∀ i : Fin 32, indexedBlockCheck (58016 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_57984_58047 :
    ∀ i : Fin 64, indexedBlockCheck (57984 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (57984 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 57984 0 32 h0 checkBlocks_57984_58047_part0
  have h64 := extendCertifiedSegment 57984 32 32 h32 checkBlocks_57984_58047_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_58048_58111_part0 :
    ∀ i : Fin 32, indexedBlockCheck (58048 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58048_58111_part1 :
    ∀ i : Fin 32, indexedBlockCheck (58080 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58048_58111 :
    ∀ i : Fin 64, indexedBlockCheck (58048 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (58048 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 58048 0 32 h0 checkBlocks_58048_58111_part0
  have h64 := extendCertifiedSegment 58048 32 32 h32 checkBlocks_58048_58111_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_58112_58175_part0 :
    ∀ i : Fin 32, indexedBlockCheck (58112 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58112_58175_part1 :
    ∀ i : Fin 32, indexedBlockCheck (58144 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58112_58175 :
    ∀ i : Fin 64, indexedBlockCheck (58112 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (58112 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 58112 0 32 h0 checkBlocks_58112_58175_part0
  have h64 := extendCertifiedSegment 58112 32 32 h32 checkBlocks_58112_58175_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_58176_58239_part0 :
    ∀ i : Fin 32, indexedBlockCheck (58176 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58176_58239_part1 :
    ∀ i : Fin 32, indexedBlockCheck (58208 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58176_58239 :
    ∀ i : Fin 64, indexedBlockCheck (58176 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (58176 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 58176 0 32 h0 checkBlocks_58176_58239_part0
  have h64 := extendCertifiedSegment 58176 32 32 h32 checkBlocks_58176_58239_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_58240_58303_part0 :
    ∀ i : Fin 32, indexedBlockCheck (58240 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58240_58303_part1 :
    ∀ i : Fin 32, indexedBlockCheck (58272 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58240_58303 :
    ∀ i : Fin 64, indexedBlockCheck (58240 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (58240 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 58240 0 32 h0 checkBlocks_58240_58303_part0
  have h64 := extendCertifiedSegment 58240 32 32 h32 checkBlocks_58240_58303_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_58304_58367_part0 :
    ∀ i : Fin 32, indexedBlockCheck (58304 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58304_58367_part1 :
    ∀ i : Fin 32, indexedBlockCheck (58336 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58304_58367 :
    ∀ i : Fin 64, indexedBlockCheck (58304 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (58304 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 58304 0 32 h0 checkBlocks_58304_58367_part0
  have h64 := extendCertifiedSegment 58304 32 32 h32 checkBlocks_58304_58367_part1
  intro i
  exact h64 i.val i.isLt

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
