/- Assembled by AxiomProver. -/

module

public import SptClassification.Partitions.RestrictedSeries

/-!
# Bounded tables for restricted partition coefficients

Rows are constructed from the largest allowed part downwards. Each new row
convolves the preceding row with the finite geometric progression of the new
part. The table is finite data; its recurrence certificate is checked separately
before applying `restrictedPartitionTable_sound`.
-/

public section

namespace SptClassification.QSeries

/-- Construct successive restricted-partition rows through degree `B`.
Row zero is the terminal row for parts greater than `B`; row `k+1` adds part `B-k`. -/
@[expose] def partitionTailRows (B : ℕ) : ℕ → List (List ℤ)
  | 0 => [(List.range (B + 1)).map fun n => if n = 0 then (1 : ℤ) else 0]
  | k + 1 =>
    let rows := partitionTailRows B k
    let previous := (rows[k]?).getD []
    let m := B - k
    let row := (List.range (B + 1)).map fun n =>
      (List.range (n / m + 1)).foldl
        (fun total r => total + (previous[n - r * m]?).getD 0) 0
    rows ++ [row]

/-- Read the row with least allowed part `m` from the bounded table. -/
@[expose] def partitionTailCandidate (B m n : ℕ) : ℤ :=
  (((partitionTailRows B B)[B + 1 - m]?).getD [])[n]?.getD 0

/-- The terminal row of the coefficient certificate through degree 87. -/
theorem partitionTailCertificate_boundary : ∀ n : Fin 88,
    partitionTailCandidate 87 88 n.val = if n.val = 0 then 1 else 0 := by
  decide +kernel

/-- Every include/exclude equation of the finite coefficient certificate is kernel checked. -/
theorem partitionTailCertificate_recurrence : ∀ m : Fin 87, ∀ n : Fin 88,
    partitionTailCandidate 87 (m.val + 1) n.val =
      partitionTailCandidate 87 (m.val + 2) n.val +
        if m.val + 1 ≤ n.val then partitionTailCandidate 87 (m.val + 1) (n.val - (m.val + 1))
        else 0 := by
  decide +kernel

/-- The checked finite table gives actual restricted partition coefficients. -/
theorem partitionTailCertificate_correct {m n : ℕ}
    (hm : 1 ≤ m) (hmb : m ≤ 88) (hn : n ≤ 87) :
    partitionTailCandidate 87 m n = (restrictedPartitionSeries m).coeff n := by
  apply restrictedPartitionTable_sound 87 (partitionTailCandidate 87) ?_ ?_ hn hm hmb
  · intro n hn
    exact partitionTailCertificate_boundary ⟨n, by omega⟩
  · intro m hm hmB n hn
    have h := partitionTailCertificate_recurrence ⟨m - 1, by omega⟩ ⟨n, by omega⟩
    simpa only [Fin.val_mk, show m - 1 + 1 = m by omega,
      show m - 1 + 2 = m + 1 by omega] using h

/-- The first row computes the ordinary partition function through degree 87. -/
theorem partitionCount_eq_tailCertificate {n : ℕ} (hn : n ≤ 87) :
    (partitionCount n : ℤ) = partitionTailCandidate 87 1 n := by
  rw [partitionTailCertificate_correct (by decide) (by decide) hn,
    coeff_restrictedPartitionSeries_one]

end SptClassification.QSeries
