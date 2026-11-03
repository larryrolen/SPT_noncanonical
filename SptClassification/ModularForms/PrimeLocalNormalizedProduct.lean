/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.PrimeLocalRational

/-!
# Prime-local reduction of the normalized spt representative

The two classical Eisenstein congruences quoted immediately after (2.5) in
[rolenManuscript, §2] are isolated as coefficient-level literature inputs.
All subsequent finite-product and cancellation steps concern the particular
normalized representative in that equation.
-/

public section

namespace SptClassification

/-- The normalized weight `p-1` Eisenstein coefficient is `1` at zero and
vanishes modulo `p` at every positive index. This is the classical
`E_(p-1) ≡ 1` congruence used in [rolenManuscript, §2, after (2.5)]. -/
theorem normalizedEisenstein_minus_reduces
    {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (n : ℕ) :
    RationalReduces p (normalizedEisensteinRationalCoefficient (p - 1) n)
      (if n = 0 then 1 else 0) := by
  sorry

/-- The normalized weight `p+1` Eisenstein coefficient reduces to the
integral weight-two coefficient. This is the classical
`E_(p+1) ≡ E₂` congruence used in [rolenManuscript, §2, after (2.5)]. -/
theorem normalizedEisenstein_plus_reduces
    {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (n : ℕ) :
    RationalReduces p (normalizedEisensteinRationalCoefficient (p + 1) n)
      (eisensteinTwoIntegerCoefficient n : ZMod p) := by
  sorry

private theorem prime_not_dvd_288 {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) :
    ¬(p : ℤ) ∣ (288 : ℤ) := by
  intro h
  have hn : p ∣ 288 := by exact_mod_cast h
  have hfactor : (288 : ℕ) = 2 ^ 5 * 3 ^ 2 := by norm_num
  rw [hfactor] at hn
  rcases (Fact.out : p.Prime).dvd_mul.mp hn with htwo | hthree
  · have h2 : p ∣ 2 := (Fact.out : p.Prime).dvd_of_dvd_pow htwo
    have hbound := Nat.le_of_dvd (by omega : 0 < 2) h2
    omega
  · have h3 : p ∣ 3 := (Fact.out : p.Prime).dvd_of_dvd_pow hthree
    have hbound := Nat.le_of_dvd (by omega : 0 < 3) h3
    omega

/-- The scalar `1/288` is prime-local for all primes at least five. -/
theorem one_div_288_reduces {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) :
    RationalReduces p (1 / 288 : ℚ) ((288 : ZMod p)⁻¹) := by
  have h288 : (288 : ZMod p) ≠ 0 := by
    intro h
    have hcast : ((288 : ℤ) : ZMod p) = 0 := by exact_mod_cast h
    exact prime_not_dvd_288 hp
      ((ZMod.intCast_zmod_eq_zero_iff_dvd 288 p).mp hcast)
  convert RationalReduces.ofFraction p 1 288 (prime_not_dvd_288 hp)
    ((288 : ZMod p)⁻¹) (by simp [h288]) using 1 <;> norm_num

/-- The selected smallest-parts coefficient has its evident integral
prime-local residue. -/
theorem twistedSmallestPartsRationalRow_reduces
    {p Q : ℕ} [Fact p.Prime] [Fact Q.Prime] (r : ℤ) :
    RationalReduces p (twistedSmallestPartsRationalRow Q r)
      ((QSeries.sptTwistedLaurent p Q).coeff r) := by
  rw [QSeries.sptTwistedLaurent_coeff]
  by_cases h : legendreSym Q (-r) = -1
  · simp only [twistedSmallestPartsRationalRow_eq, negativeSquareSelector_eq, h,
      ↓ite_true, one_mul]
    exact RationalReduces.intCast p (QSeries.sptFourier r)
  · simp only [twistedSmallestPartsRationalRow_eq, negativeSquareSelector_eq, h,
      ↓ite_false, zero_mul]
    simpa using RationalReduces.intCast p 0

/-- The selected inverse-eta coefficient has its evident integral
prime-local residue. -/
theorem twistedPartitionRationalRow_reduces
    {p Q : ℕ} [Fact p.Prime] [Fact Q.Prime] (r : ℤ) :
    RationalReduces p (twistedPartitionRationalRow Q r)
      ((QSeries.partitionTwistedLaurent p Q).coeff r) := by
  rw [QSeries.partitionTwistedLaurent_coeff]
  by_cases h : legendreSym Q (-r) = -1
  · simp only [twistedPartitionRationalRow_eq, negativeSquareSelector_eq, h,
      ↓ite_true, one_mul]
    exact RationalReduces.intCast p (QSeries.partitionFourier r)
  · simp only [twistedPartitionRationalRow_eq, negativeSquareSelector_eq, h,
      ↓ite_false, zero_mul]
    simpa using RationalReduces.intCast p 0

/-- Extend an ordinary residue power-series row by zero to negative indices. -/
def nonnegativeModularRow (p : ℕ) (a : ℕ → ZMod p) (r : ℤ) : ZMod p :=
  if r < 0 then 0 else a r.toNat

theorem nonnegativeRationalRow_reduces
    {p : ℕ} [Fact p.Prime] (A : PowerSeries ℚ) (a : ℕ → ZMod p)
    (h : ∀ n, RationalReduces p (A.coeff n) (a n)) (r : ℤ) :
    RationalReduces p (nonnegativeRationalRow A r)
      (nonnegativeModularRow p a r) := by
  by_cases hr : r < 0
  · rw [nonnegativeRationalRow_zero_below A r hr]
    simp only [nonnegativeModularRow, if_pos hr]
    simpa using RationalReduces.intCast p 0
  · have hnat : (r.toNat : ℤ) = r := Int.toNat_of_nonneg (by omega)
    rw [nonnegativeModularRow, if_neg hr]
    have hrow : nonnegativeRationalRow A r = A.coeff r.toNat := by
      conv_lhs => rw [← hnat]
      exact nonnegativeRationalRow_natCast A r.toNat
    rw [hrow]
    exact h r.toNat

/-- The constant-one residue row used for `E_(p-1)`. -/
def unitModularRow (p : ℕ) : ℤ → ZMod p :=
  nonnegativeModularRow p (fun n => if n = 0 then 1 else 0)

/-- The integral `E₂` row reduced in `ZMod p`. -/
def eisensteinTwoModularRow (p : ℕ) : ℤ → ZMod p :=
  nonnegativeModularRow p (fun n => (eisensteinTwoIntegerCoefficient n : ZMod p))

theorem normalizedEisenstein_minus_row_reduces
    {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (r : ℤ) :
    RationalReduces p
      (nonnegativeRationalRow (normalizedEisensteinRationalSeries (p - 1)) r)
      (unitModularRow p r) := by
  exact nonnegativeRationalRow_reduces _ _
    (by intro n; simpa only [normalizedEisensteinRationalSeries_coeff] using
      normalizedEisenstein_minus_reduces hp n) r

theorem normalizedEisenstein_plus_row_reduces
    {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (r : ℤ) :
    RationalReduces p
      (nonnegativeRationalRow (normalizedEisensteinRationalSeries (p + 1)) r)
      (eisensteinTwoModularRow p r) := by
  exact nonnegativeRationalRow_reduces _ _
    (by intro n; simpa only [normalizedEisensteinRationalSeries_coeff] using
      normalizedEisenstein_plus_reduces hp n) r

theorem eisensteinTwoRationalRow_reduces
    {p : ℕ} [Fact p.Prime] (r : ℤ) :
    RationalReduces p (nonnegativeRationalRow eisensteinTwoRationalSeries r)
      (eisensteinTwoModularRow p r) := by
  exact nonnegativeRationalRow_reduces _ _ (by
    intro n
    rw [eisensteinTwoRationalSeries_coeff, eisensteinTwoCoefficient_eq_intCast]
    exact RationalReduces.intCast p _) r

private theorem poleCleared_unitModularRow (p : ℕ) :
    poleClearedModularRow p (unitModularRow p) 0 = 1 := by
  apply PowerSeries.ext
  intro n
  simp only [poleClearedModularRow_coeff]
  simp [unitModularRow, nonnegativeModularRow]

theorem modularLaurentProductRow_unit_left (p : ℕ)
    (b : ℤ → ZMod p) (N : ℕ)
    (hb : ∀ r, r < -(N : ℤ) → b r = 0) (r : ℤ) :
    modularLaurentProductRow p (unitModularRow p) b 0 N r = b r := by
  by_cases hr : r < -(N : ℤ)
  · rw [modularLaurentProductRow_zero_below p (unitModularRow p) b 0 N r
      (by simpa using hr), hb r hr]
  · rw [modularLaurentProductRow_eq_coeff p (unitModularRow p) b 0 N r
      (by simpa using hr)]
    simp only [Nat.zero_add,
      poleCleared_unitModularRow, one_mul, poleClearedModularRow_coeff]
    congr 1
    omega

/-- The residue row of the inner factor of (2.5). -/
noncomputable def normalizedInnerModularRow (p Q : ℕ)
    [Fact Q.Prime] (r : ℤ) : ZMod p :=
  (QSeries.sptTwistedLaurent p Q).coeff r -
    modularLaurentProductRow p (eisensteinTwoModularRow p)
      (fun k => (QSeries.partitionTwistedLaurent p Q).coeff k) 0 1 r *
      (288 : ZMod p)⁻¹

theorem normalizedInnerRationalRow_reduces
    {p Q : ℕ} [Fact p.Prime] [Fact Q.Prime] (hp : 5 ≤ p) (r : ℤ) :
    RationalReduces p (normalizedInnerRationalRow Q r)
      (normalizedInnerModularRow p Q r) := by
  have hproduct := rationalLaurentProductRow_reduces
    (nonnegativeRationalRow eisensteinTwoRationalSeries)
    (twistedPartitionRationalRow Q)
    (eisensteinTwoModularRow p)
    (fun k => (QSeries.partitionTwistedLaurent p Q).coeff k)
    0 1 eisensteinTwoRationalRow_reduces
    twistedPartitionRationalRow_reduces r
  have hscaled := hproduct.mul (one_div_288_reduces hp)
  simpa only [normalizedInnerRationalRow_eq, normalizedInnerModularRow,
    div_eq_mul_inv, one_mul] using
    (twistedSmallestPartsRationalRow_reduces (p := p) (Q := Q) r).sub hscaled

theorem normalizedRepresentativeRationalRow_reduces
    {p Q : ℕ} [Fact p.Prime] [Fact Q.Prime] (hp : 5 ≤ p) (r : ℤ) :
    RationalReduces p (normalizedRepresentativeRationalRow p Q r)
      (modularLaurentProductRow p (unitModularRow p)
          (normalizedInnerModularRow p Q) 0 1 r +
        modularLaurentProductRow p (eisensteinTwoModularRow p)
          (fun k => (QSeries.partitionTwistedLaurent p Q).coeff k) 0 1 r *
          (288 : ZMod p)⁻¹) := by
  have hfirst := rationalLaurentProductRow_reduces
    (nonnegativeRationalRow (normalizedEisensteinRationalSeries (p - 1)))
    (normalizedInnerRationalRow Q)
    (unitModularRow p) (normalizedInnerModularRow p Q)
    0 1 (normalizedEisenstein_minus_row_reduces hp)
    (normalizedInnerRationalRow_reduces hp) r
  have hsecond := rationalLaurentProductRow_reduces
    (nonnegativeRationalRow (normalizedEisensteinRationalSeries (p + 1)))
    (twistedPartitionRationalRow Q)
    (eisensteinTwoModularRow p)
    (fun k => (QSeries.partitionTwistedLaurent p Q).coeff k)
    0 1 (normalizedEisenstein_plus_row_reduces hp)
    twistedPartitionRationalRow_reduces r
  have hscaled := hsecond.mul (one_div_288_reduces hp)
  simpa only [normalizedRepresentativeRationalRow_eq, div_eq_mul_inv, one_mul] using
    hfirst.add hscaled

theorem normalizedInnerModularRow_zero_below
    (p Q : ℕ) [Fact Q.Prime] (r : ℤ) (hr : r < -1) :
    normalizedInnerModularRow p Q r = 0 := by
  have hs : (QSeries.sptTwistedLaurent p Q).coeff r = 0 := by
    rw [QSeries.sptTwistedLaurent_coeff]
    simp [QSeries.sptFourier_eq_zero_of_lt hr]
  have hg : modularLaurentProductRow p (eisensteinTwoModularRow p)
      (fun k => (QSeries.partitionTwistedLaurent p Q).coeff k) 0 1 r = 0 :=
    modularLaurentProductRow_zero_below p _ _ 0 1 r (by omega)
  simp only [normalizedInnerModularRow, hs, hg, zero_mul, sub_zero]

/-- The two weight-two correction products cancel after reduction; the
normalized form has precisely the quadratically selected spt residue row. -/
theorem normalizedRepresentativeRationalRow_reduces_twistedS
    {p Q : ℕ} [Fact p.Prime] [Fact Q.Prime] (hp : 5 ≤ p) (r : ℤ) :
    RationalReduces p (normalizedRepresentativeRationalRow p Q r)
      ((QSeries.sptTwistedLaurent p Q).coeff r) := by
  have h := normalizedRepresentativeRationalRow_reduces (Q := Q) hp r
  have hunit := modularLaurentProductRow_unit_left p
    (normalizedInnerModularRow p Q) 1
    (normalizedInnerModularRow_zero_below p Q) r
  rw [hunit] at h
  convert h using 1
  simp only [normalizedInnerModularRow]
  ring

/-- Prime-local reduction of the analytically identified normalized form,
with no coefficient-comparison premise in the approximation. -/
theorem SptModularApproximation.form_coeffMod_eq_twistedS
    {p Q : ℕ} {hfive : 5 ≤ p} [Fact p.Prime] [Fact Q.Prime]
    (A : SptModularApproximation p Q hfive) (r : ℤ) :
    A.form.coeffMod r = (QSeries.sptTwistedLaurent p Q).coeff r := by
  exact A.coeffMod_eq_of_normalizedRow_reduces r _
    (normalizedRepresentativeRationalRow_reduces_twistedS hfive r)

end SptClassification
