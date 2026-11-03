/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.HeckeReduction

/-!
# Finite coefficient pairings at exponent zero

The constant coefficient of a product with one negative index `-d` on one
side and divisor-square negative indices on the other has a finite algebraic
expression. The analytic assertion that a weight-two product has zero
constant coefficient is separate. The coefficient formulas below implement
the algebra in [rolenManuscript], Section 3, equations `eq:ct1` and `eq:ct2`.
-/

public section

namespace SptClassification.QSeries

/-- Indices supporting the negative divisor-square principal part. -/
def negativeDivisorSquareIndices (m : ℕ) : Finset ℤ :=
  m.divisors.image (fun t : ℕ => - (t : ℤ) ^ 2)

/-- Membership in the negative divisor-square index set. -/
theorem mem_negativeDivisorSquareIndices {m : ℕ} {r : ℤ} :
    r ∈ negativeDivisorSquareIndices m ↔
      ∃ t ∈ m.divisors, r = - (t : ℤ) ^ 2 := by
  rw [negativeDivisorSquareIndices, Finset.mem_image]
  constructor
  · rintro ⟨t, ht, htr⟩
    exact ⟨t, ht, htr.symm⟩
  · rintro ⟨t, ht, hrt⟩
    exact ⟨t, ht, hrt.symm⟩

/-- All indices which can contribute to the constant coefficient of the
product when the other factor has its only negative index at `-d`. -/
def constantTermIndices (m d : ℕ) : Finset ℤ :=
  insert (d : ℤ) (negativeDivisorSquareIndices m)

/-- The explicit finite index set for the constant-term pairing. -/
theorem constantTermIndices_eq (m d : ℕ) :
    constantTermIndices m d =
      insert (d : ℤ) (negativeDivisorSquareIndices m) := (rfl)

/-- A finite coefficient convolution at exponent zero. -/
def finiteConstantTerm {K : Type*} [Semiring K]
    (I : Finset ℤ) (A B : ℤ → K) : K :=
  ∑ r ∈ I, A r * B (-r)

/-- Evaluate the finite coefficient convolution at exponent zero. -/
theorem finiteConstantTerm_apply {K : Type*} [Semiring K]
    (I : Finset ℤ) (A B : ℤ → K) :
    finiteConstantTerm I A B = ∑ r ∈ I, A r * B (-r) := (rfl)

/-- The index `d` is disjoint from the negative divisor-square indices. -/
theorem pos_not_mem_negativeDivisorSquareIndices {m d : ℕ} (hd : 0 < d) :
    (d : ℤ) ∉ negativeDivisorSquareIndices m := by
  intro hmem
  obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hmem
  have hdz : (0 : ℤ) < d := by exact_mod_cast hd
  have ht0 : (0 : ℤ) ≤ (t : ℤ) ^ 2 := sq_nonneg _
  nlinarith

/-- The finite constant-term convolution separates into the positive index
`d` and the distinct negative divisor squares. -/
theorem finiteConstantTerm_divisorSquares {K : Type*} [CommSemiring K]
    {m d : ℕ} (hd : 0 < d) (A B : ℤ → K) :
    finiteConstantTerm (constantTermIndices m d) A B =
      A d * B (-(d : ℤ)) +
        ∑ t ∈ m.divisors, A (- (t : ℤ) ^ 2) * B ((t : ℤ) ^ 2) := by
  have hinj : Set.InjOn (fun t : ℕ => - (t : ℤ) ^ 2) m.divisors := by
    intro s _ t _ hst
    have hs : (0 : ℤ) ≤ s := Int.natCast_nonneg s
    have ht : (0 : ℤ) ≤ t := Int.natCast_nonneg t
    have hcast : (s : ℤ) = t := by nlinarith
    exact_mod_cast hcast
  simp only [finiteConstantTerm, constantTermIndices]
  rw [Finset.sum_insert (pos_not_mem_negativeDivisorSquareIndices hd)]
  unfold negativeDivisorSquareIndices
  rw [Finset.sum_image hinj]
  simp only [neg_neg]

/-- Outside the selected finite set, the product coefficient vanishes if
the first factor has divisor-square negative support and the second has only
the negative index `-d`. The zero-index product is stated explicitly. -/
theorem coefficientProduct_zero_outside
    {K : Type*} [CommSemiring K] {m d : ℕ} (hm : 0 < m) (A B : ℤ → K)
    (hA : ∀ r : ℤ, r < 0 → A r ≠ 0 →
      ∃ t : ℕ, 0 < t ∧ t ∣ m ∧ r = - (t : ℤ) ^ 2)
    (hB : ∀ r : ℤ, r < 0 → B r ≠ 0 → r = -(d : ℤ))
    (hzero : A 0 * B 0 = 0)
    (r : ℤ) (hr : r ∉ constantTermIndices m d) :
    A r * B (-r) = 0 := by
  by_cases hneg : r < 0
  · by_cases hAz : A r = 0
    · simp [hAz]
    obtain ⟨t, _, htdiv, hindex⟩ := hA r hneg hAz
    have hmem : r ∈ constantTermIndices m d := by
      apply Finset.mem_insert_of_mem
      apply Finset.mem_image.mpr
      exact ⟨t, Nat.mem_divisors.mpr ⟨htdiv, by omega⟩, hindex.symm⟩
    exact False.elim (hr hmem)
  by_cases hzeroIndex : r = 0
  · subst r
    simpa using hzero
  have hpos : 0 < r := by omega
  by_cases hBz : B (-r) = 0
  · simp [hBz]
  have hindex := hB (-r) (by omega) hBz
  have heq : r = (d : ℤ) := by omega
  exact False.elim (hr (by simp [constantTermIndices, heq]))

/-- The first manuscript pairing's coefficient algebra. To obtain its
zero-constant-term identity one supplies the analytic vanishing theorem. -/
theorem heckeThreeHalf_finiteConstantTerm (ps : List ℕ)
    (_hps : ∀ p ∈ ps, p.Prime) {d : ℕ} (hd : 0 < d)
    (H : ℤ → ℚ) (hH : H (-(d : ℤ)) = 1) :
    finiteConstantTerm (constantTermIndices ps.prod d)
      (heckeThreeHalfWord ps (fun r => (fFourier r : ℚ))) H =
      heckeThreeHalfWord ps (fun r => (fFourier r : ℚ)) d +
        ∑ t ∈ ps.prod.divisors,
          (heckePrincipalCoefficient ps t : ℚ) * H ((t : ℤ) ^ 2) := by
  rw [finiteConstantTerm_divisorSquares hd, hH, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  rw [← heckeThreeHalfWordInt_cast]
  rw [heckePrincipalCoefficient_apply]

/-- The second manuscript pairing's coefficient algebra, with the exact
`c_t/t²` normalization for a repeated-prime word. -/
theorem heckeMinusHalf_finiteConstantTerm (ps : List ℕ)
    (hps : ∀ p ∈ ps, p.Prime) {d : ℕ} (hd : 0 < d)
    (K : ℤ → ℚ) (hK : K (-(d : ℤ)) = 1) :
    finiteConstantTerm (constantTermIndices ps.prod d)
      (fun r => (ps.prod : ℚ) ^ 2 *
        heckeMinusHalfWord ps (fun s => (partitionFourier s : ℚ)) r) K =
      (ps.prod : ℚ) ^ 2 *
        heckeMinusHalfWord ps (fun s => (partitionFourier s : ℚ)) d +
        ∑ t ∈ ps.prod.divisors,
          ((heckePrincipalCoefficient ps t : ℚ) / (t : ℚ) ^ 2) *
            K ((t : ℤ) ^ 2) := by
  have hm : 0 < ps.prod := by
    induction ps with
    | nil => simp
    | cons p ps ih =>
      have hp := hps p (by simp)
      have ht : ∀ q ∈ ps, q.Prime := fun q hq => hps q (by simp [hq])
      simpa only [List.prod_cons] using Nat.mul_pos hp.pos (ih ht)
  rw [finiteConstantTerm_divisorSquares hd, hK, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  have htpos : 0 < t := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp ht).1 hm
  rw [heckePrincipal_partition_coefficient ps hps htpos]

/-- The first coefficient identity once the weight-two product's constant
coefficient has been shown to vanish. -/
theorem heckeThreeHalf_coefficient_of_constantTerm_zero (ps : List ℕ)
    (hps : ∀ p ∈ ps, p.Prime) {d : ℕ} (hd : 0 < d)
    (H : ℤ → ℚ) (hH : H (-(d : ℤ)) = 1)
    (hCT : finiteConstantTerm (constantTermIndices ps.prod d)
      (heckeThreeHalfWord ps (fun r => (fFourier r : ℚ))) H = 0) :
    heckeThreeHalfWord ps (fun r => (fFourier r : ℚ)) d =
      -∑ t ∈ ps.prod.divisors,
        (heckePrincipalCoefficient ps t : ℚ) * H ((t : ℤ) ^ 2) := by
  rw [heckeThreeHalf_finiteConstantTerm ps hps hd H hH] at hCT
  exact eq_neg_of_add_eq_zero_left hCT

/-- The second coefficient identity under the corresponding analytic
constant-term vanishing premise. -/
theorem heckeMinusHalf_coefficient_of_constantTerm_zero (ps : List ℕ)
    (hps : ∀ p ∈ ps, p.Prime) {d : ℕ} (hd : 0 < d)
    (K : ℤ → ℚ) (hK : K (-(d : ℤ)) = 1)
    (hCT : finiteConstantTerm (constantTermIndices ps.prod d)
      (fun r => (ps.prod : ℚ) ^ 2 *
        heckeMinusHalfWord ps (fun s => (partitionFourier s : ℚ)) r) K = 0) :
    (ps.prod : ℚ) ^ 2 *
      heckeMinusHalfWord ps (fun s => (partitionFourier s : ℚ)) d =
      -∑ t ∈ ps.prod.divisors,
        ((heckePrincipalCoefficient ps t : ℚ) / (t : ℚ) ^ 2) *
          K ((t : ℤ) ^ 2) := by
  rw [heckeMinusHalf_finiteConstantTerm ps hps hd K hK] at hCT
  exact eq_neg_of_add_eq_zero_left hCT

end SptClassification.QSeries
