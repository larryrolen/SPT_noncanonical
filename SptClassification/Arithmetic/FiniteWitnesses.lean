/- Assembled by AxiomProver. -/

module

public import SptClassification.Partitions.Evaluation
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic.NormNum.LegendreSymbol

/-!
# Small witnesses for an explicit finite set of moduli

Each row records a modulus and two indices whose smallest-parts values are
nonzero modulo it and whose discriminants have opposite quadratic characters.
The entries are checked against the actual combinatorial `spt` function.

Identifying this list with the prime divisors of the larger coefficient product
is a separate assertion.
-/

public section

namespace SptClassification

/-- Rows `(modulus, positive-character index, negative-character index)`. -/
@[expose] def smallWitnessCertificate : List (ℕ × ℕ × ℕ) :=
  [(5,5,1), (7,2,1), (11,4,1), (13,1,2), (17,2,1), (19,3,1), (23,6,2),
   (29,1,2), (31,1,2), (37,2,1), (41,1,2), (47,1,3), (53,2,1), (67,4,1),
   (71,1,4), (89,2,1), (137,5,1), (167,1,2), (191,2,1), (239,1,3), (263,2,1),
   (281,5,1), (311,1,2), (359,3,1), (383,2,1), (431,2,1), (433,4,1), (479,2,1),
   (491,1,3), (503,3,1), (599,1,2), (601,1,3), (617,2,1), (647,1,4), (673,1,2),
   (719,1,7), (743,4,1), (839,3,1), (863,1,3), (887,1,2), (911,2,1), (983,3,1),
   (1031,3,1), (1103,3,1), (1151,1,2), (1223,1,4), (1319,1,3), (1367,2,1),
   (1439,1,2), (1487,6,1), (1511,1,4), (1523,3,1), (1531,1,5), (1543,1,2),
   (1559,1,3), (1583,2,1), (1607,2,1), (1823,1,5), (1847,2,1), (1871,1,2),
   (2039,2,1), (2063,1,4), (2087,5,1), (2399,2,1), (2633,2,1), (3331,4,1),
   (3929,2,1), (8167,1,4), (8263,1,2), (9187,4,1), (11171,1,4), (11813,2,1),
   (22777,3,1), (27809,1,4), (127207,2,1), (128413,1,4), (133439,1,4),
   (343667,1,5), (645803,1,2), (682729,2,1), (4404161,1,2), (10859551,1,2),
   (66079291,2,1), (258555197,8,1)]

theorem smallWitnessCertificate_length : smallWitnessCertificate.length = 84 := by
  decide +kernel

theorem smallWitnessCertificate_moduli_nodup :
    (smallWitnessCertificate.map Prod.fst).Nodup := by
  decide +kernel

/-- Every row has the stated two nonzero smallest-parts witnesses. -/
theorem smallWitnessCertificate_valid :
    ∀ t ∈ smallWitnessCertificate,
      (1 ≤ t.2.1 ∧ t.2.1 ≤ 8 ∧ ¬t.1 ∣ spt t.2.1 ∧
        jacobiSym (1 - 24 * (t.2.1 : ℤ)) t.1 = 1) ∧
      (1 ≤ t.2.2 ∧ t.2.2 ≤ 8 ∧ ¬t.1 ∣ spt t.2.2 ∧
        jacobiSym (1 - 24 * (t.2.2 : ℤ)) t.1 = -1) := by
  norm_num [smallWitnessCertificate]

/-- For a prime modulus in the certificate, either Legendre class has a small witness. -/
theorem exists_small_witness_of_certificate (l : ℕ) [Fact l.Prime]
    {a b : ℕ} (hrow : (l, a, b) ∈ smallWitnessCertificate)
    {sign : ℤ} (hsign : sign = 1 ∨ sign = -1) :
    ∃ N : ℕ, 1 ≤ N ∧ N ≤ 8 ∧ ¬l ∣ spt N ∧ legendreSym l (1 - 24 * (N : ℤ)) = sign := by
  obtain ⟨ha, hb⟩ := smallWitnessCertificate_valid (l, a, b) hrow
  rcases hsign with rfl | rfl
  · refine ⟨a, ha.1, ha.2.1, ha.2.2.1, ?_⟩
    simpa only [jacobiSym.legendreSym.to_jacobiSym] using ha.2.2.2
  · refine ⟨b, hb.1, hb.2.1, hb.2.2.1, ?_⟩
    simpa only [jacobiSym.legendreSym.to_jacobiSym] using hb.2.2.2

end SptClassification
