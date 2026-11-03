/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.EtaHecke
public import SptClassification.QSeries.FourierCoefficients

/-!
# Support below an inverse-eta Fourier pole

The coefficient action of a square-index Hecke operator reads some input
indices below the first index visible in a convergent Fourier row. The
Fourier coefficient function must vanish there for the analytic reindexing
to represent that operator [rolenManuscript, §3].
-/

public section

namespace SptClassification.QSeries

/-- A coefficient row has no terms below its pole at `-m²/24`. -/
def SquarePoleSupported (m : ℕ) (A : ℤ → ℚ) : Prop :=
  ∀ r : ℤ, r < -(m : ℤ) ^ 2 → A r = 0

/-- A row supported at the square pole vanishes at every earlier index. -/
theorem SquarePoleSupported.apply
    {m : ℕ} {A : ℤ → ℚ} (hA : SquarePoleSupported m A)
    (r : ℤ) (hr : r < -(m : ℤ) ^ 2) : A r = 0 :=
  hA r hr

/-- The ordinary partition row starts at `q^(-1/24)`. -/
theorem squarePoleSupported_partitionFourier :
    SquarePoleSupported 1 (fun r => (partitionFourier r : ℚ)) := by
  intro r hr
  have hlt : r < -1 := by simpa [SquarePoleSupported] using hr
  simp [partitionFourier_eq_zero_of_lt hlt]

/-- A prime Hecke step raises the possible pole from `m²` to `(mp)²`.
This is a coefficient support fact, independent of modularity. -/
theorem SquarePoleSupported.heckeMinusHalf
    {m : ℕ} {A : ℤ → ℚ} (hA : SquarePoleSupported m A)
    (p : ℕ) (hp : 0 < p) :
    SquarePoleSupported (m * p) (heckeMinusHalf p A) := by
  intro r hr
  let q : ℤ := (p : ℤ) ^ 2
  let M : ℤ := (m : ℤ) ^ 2
  have hq : 0 < q := by
    dsimp [q]
    exact pow_pos (by exact_mod_cast hp) _
  have hq1 : 1 ≤ q := by omega
  have hM : 0 ≤ M := sq_nonneg _
  have hbound : r < -(M * q) := by
    simpa only [q, M, Nat.cast_mul, mul_pow] using hr
  have hr0 : r < 0 := by nlinarith [mul_nonneg hM (le_of_lt hq)]
  have hrM : r < -M := by
    nlinarith [mul_nonneg hM (sub_nonneg.mpr hq1)]
  have hfirst : A (q * r) = 0 := by
    apply hA
    have hmul : q * r ≤ r := by
      nlinarith [mul_nonpos_of_nonneg_of_nonpos
        (sub_nonneg.mpr hq1) (le_of_lt hr0)]
    omega
  have hmiddle : A r = 0 := hA r hrM
  have hdown : squareDown p A r = 0 := by
    rw [squareDown_apply]
    by_cases hd : q ∣ r
    · rw [if_pos (by simpa only [q] using hd)]
      apply hA
      have hdiv : (r / q) * q = r := Int.ediv_mul_cancel hd
      have hlt : (r / q) * q < (-M) * q := by
        rw [hdiv]
        simpa only [neg_mul] using hbound
      by_contra hn
      have hge : -M ≤ r / q := le_of_not_gt hn
      have hprod := mul_nonneg (sub_nonneg.mpr hge) (le_of_lt hq)
      nlinarith
    · rw [if_neg (by simpa only [q] using hd)]
  dsimp [q] at hfirst
  rw [heckeMinusHalf_eq_squareHecke, squareHecke_apply,
    hfirst, hmiddle, hdown]
  ring

/-- A finite Hecke word, including repeated prime factors, has no terms below
the square of the product of its indices. -/
theorem SquarePoleSupported.heckeMinusHalfWord
    {m : ℕ} {A : ℤ → ℚ} (hA : SquarePoleSupported m A)
    (ps : List ℕ) (hps : ∀ p ∈ ps, 0 < p) :
    SquarePoleSupported (m * ps.prod) (heckeMinusHalfWord ps A) := by
  induction ps generalizing m A with
  | nil =>
      simpa only [List.prod_nil, mul_one, heckeMinusHalfWord_nil] using hA
  | cons p ps ih =>
      have hp : 0 < p := hps p (by simp)
      have htail : ∀ q ∈ ps, 0 < q :=
        fun q hq => hps q (by simp [hq])
      simpa only [List.prod_cons, mul_assoc, heckeMinusHalfWord_cons] using
        ih (hA.heckeMinusHalf p hp) htail

end SptClassification.QSeries
