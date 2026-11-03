/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.FourierCoefficients
public import SptClassification.QSeries.EtaHecke
import Mathlib.Tactic.NormNum

/-!
# Negative-square principal parts of Hecke words

Repeated prime factors are retained in the word of square-index operators.
All principal-part statements concern the actual coefficient functions at
exponents `r/24`. We follow [rolenManuscript], Section 3.
-/

public section

namespace SptClassification.QSeries

/-- A square divisible by a prime square has a root divisible by that prime. -/
private theorem square_index_preimage {p t : ℕ} (hp : p.Prime) (r : ℤ)
    (h : (p : ℤ) ^ 2 * r = - (t : ℤ) ^ 2) :
    ∃ u : ℕ, t = p * u ∧ r = - (u : ℤ) ^ 2 := by
  have hdivZ : (p : ℤ) ^ 2 ∣ (t : ℤ) ^ 2 := by
    refine ⟨-r, ?_⟩
    nlinarith [h]
  have hdivN : p ^ 2 ∣ t ^ 2 := by exact_mod_cast hdivZ
  have hpdiv : p ∣ t := hp.dvd_of_dvd_pow (by
    exact (dvd_trans (dvd_pow_self p (by omega)) hdivN))
  obtain ⟨u, hu⟩ := hpdiv
  refine ⟨u, hu, ?_⟩
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [hu] at h
  push_cast at h
  nlinarith [sq_pos_of_ne_zero hp0]

/-- One prime Hecke step keeps the negative support inside the divisor squares. -/
theorem negativeSquareSupported_squareHecke {K : Type*} [Semiring K]
    {p m : ℕ} (hp : p.Prime) {A : ℤ → K}
    (hA : ∀ r : ℤ, r < 0 → A r ≠ 0 →
      ∃ t : ℕ, 0 < t ∧ t ∣ m ∧ r = - (t : ℤ) ^ 2)
    (middle : ℤ → K) (last : K) :
    ∀ r : ℤ, r < 0 → squareHecke p middle last A r ≠ 0 →
      ∃ t : ℕ, 0 < t ∧ t ∣ p * m ∧ r = - (t : ℤ) ^ 2 := by
  intro r hr hne
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hp2 : (0 : ℤ) < (p : ℤ) ^ 2 := sq_pos_of_pos hp0
  by_cases hup : A ((p : ℤ) ^ 2 * r) = 0
  · by_cases hmid : A r = 0
    · by_cases hdiv : (p : ℤ) ^ 2 ∣ r
      · have hqneg : r / (p : ℤ) ^ 2 < 0 := by
          have heq := Int.ediv_mul_cancel hdiv
          nlinarith
        by_cases hq : A (r / (p : ℤ) ^ 2) = 0
        · simp [squareHecke_apply, squareDown_apply, hup, hmid, hdiv, hq] at hne
        obtain ⟨t, htpos, htdiv, htindex⟩ := hA _ hqneg hq
        obtain ⟨v, hv⟩ := htdiv
        refine ⟨p * t, Nat.mul_pos hp.pos htpos, ⟨v, by rw [hv]; ring⟩, ?_⟩
        have heq := Int.ediv_mul_cancel hdiv
        rw [htindex] at heq
        calc
          r = - (t : ℤ) ^ 2 * (p : ℤ) ^ 2 := heq.symm
          _ = - ((p * t : ℕ) : ℤ) ^ 2 := by push_cast; ring
      · simp [squareHecke_apply, squareDown_apply, hup, hmid, hdiv] at hne
    · obtain ⟨t, htpos, htdiv, htindex⟩ := hA r hr hmid
      obtain ⟨v, hv⟩ := htdiv
      refine ⟨t, htpos, ⟨p * v, by rw [hv]; ring⟩, htindex⟩
  · obtain ⟨t, htpos, htdiv, htindex⟩ := hA _ (by nlinarith) hup
    obtain ⟨u, hu, hindex⟩ := square_index_preimage hp r htindex
    obtain ⟨v, hv⟩ := htdiv
    have hupos : 0 < u := by
      rw [hu] at htpos
      by_contra h
      have : u = 0 := by omega
      simp [this] at htpos
    refine ⟨u, hupos, ⟨p * p * v, ?_⟩, hindex⟩
    rw [hv, hu]
    ring

/-- Divisor-square support bounds the order of a negative pole. -/
theorem negativeSquareSupported_eq_zero_below {K : Type*} [Zero K]
    {m : ℕ} (hm : 0 < m) {A : ℤ → K}
    (hA : ∀ r : ℤ, r < 0 → A r ≠ 0 →
      ∃ t : ℕ, 0 < t ∧ t ∣ m ∧ r = - (t : ℤ) ^ 2)
    {r : ℤ} (hr : r < - (m : ℤ) ^ 2) : A r = 0 := by
  by_contra hne
  obtain ⟨t, _, htdiv, htindex⟩ := hA r (by nlinarith) hne
  have hle : t ≤ m := Nat.le_of_dvd hm htdiv
  rw [htindex] at hr
  have hleZ : (t : ℤ) ≤ m := by exact_mod_cast hle
  have ht0 : (0 : ℤ) ≤ t := Int.natCast_nonneg t
  nlinarith

/-- At a new largest negative square, only the downward Hecke term survives. -/
theorem squareHecke_leading_coefficient {K : Type*} [Semiring K]
    {p m : ℕ} (hp : p.Prime) (hm : 0 < m) {A : ℤ → K}
    (hA : ∀ r : ℤ, r < 0 → A r ≠ 0 →
      ∃ t : ℕ, 0 < t ∧ t ∣ m ∧ r = - (t : ℤ) ^ 2)
    (middle : ℤ → K) (last : K) :
    squareHecke p middle last A (- ((p * m : ℕ) : ℤ) ^ 2) =
      last * A (- (m : ℤ) ^ 2) := by
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hp2 : (0 : ℤ) < (p : ℤ) ^ 2 := sq_pos_of_pos hp0
  have hp2gt : (1 : ℤ) < (p : ℤ) ^ 2 := by
    have hptwo : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
    nlinarith
  have hpm : m < p * m := by
    simpa using Nat.mul_lt_mul_of_pos_right hp.one_lt hm
  have hbelow : - ((p * m : ℕ) : ℤ) ^ 2 < - (m : ℤ) ^ 2 := by
    have hpmZ : (m : ℤ) < (p * m : ℕ) := by exact_mod_cast hpm
    have hmZ : (0 : ℤ) ≤ m := Int.natCast_nonneg m
    nlinarith
  have hupbelow : (p : ℤ) ^ 2 * - ((p * m : ℕ) : ℤ) ^ 2 <
      - (m : ℤ) ^ 2 := by
    have hneg : - ((p * m : ℕ) : ℤ) ^ 2 < 0 := by nlinarith [hbelow]
    have : (p : ℤ) ^ 2 * - ((p * m : ℕ) : ℤ) ^ 2 <
        - ((p * m : ℕ) : ℤ) ^ 2 := by nlinarith
    omega
  have hup := negativeSquareSupported_eq_zero_below hm hA hupbelow
  have hmid := negativeSquareSupported_eq_zero_below hm hA hbelow
  have hdiv : (p : ℤ) ^ 2 ∣ - ((p * m : ℕ) : ℤ) ^ 2 := by
    refine ⟨- (m : ℤ) ^ 2, ?_⟩
    push_cast
    ring
  have hquot : - ((p * m : ℕ) : ℤ) ^ 2 / (p : ℤ) ^ 2 =
      - (m : ℤ) ^ 2 := by
    have htarget : - ((p * m : ℕ) : ℤ) ^ 2 =
        - (m : ℤ) ^ 2 * (p : ℤ) ^ 2 := by push_cast; ring
    apply mul_right_cancel₀ (ne_of_gt hp2)
    calc
      (- ((p * m : ℕ) : ℤ) ^ 2 / (p : ℤ) ^ 2) * (p : ℤ) ^ 2 =
          - ((p * m : ℕ) : ℤ) ^ 2 := Int.ediv_mul_cancel hdiv
      _ = - (m : ℤ) ^ 2 * (p : ℤ) ^ 2 := htarget
  rw [squareHecke_apply, squareDown_apply]
  simp only [Nat.cast_mul] at hup hmid hdiv hquot ⊢
  simp only [mul_neg] at hup
  simp [hup, hmid, hdiv, hquot]

/-- Compose coefficient Hecke steps, retaining repeated entries. -/
def squareHeckeWord {K : Type*} [Semiring K]
    (middle : ℕ → ℤ → K) (last : ℕ → K) : List ℕ → (ℤ → K) → (ℤ → K)
  | [], A => A
  | p :: ps, A => squareHeckeWord middle last ps (squareHecke p (middle p) (last p) A)

/-- An empty square-index word leaves the coefficient row unchanged. -/
theorem squareHeckeWord_nil {K : Type*} [Semiring K]
    (middle : ℕ → ℤ → K) (last : ℕ → K) (A : ℤ → K) :
    squareHeckeWord middle last [] A = A := (rfl)

/-- A square-index word applies its head operator first. -/
theorem squareHeckeWord_cons {K : Type*} [Semiring K]
    (middle : ℕ → ℤ → K) (last : ℕ → K) (p : ℕ) (ps : List ℕ) (A : ℤ → K) :
    squareHeckeWord middle last (p :: ps) A =
      squareHeckeWord middle last ps (squareHecke p (middle p) (last p) A) := (rfl)

theorem squareHeckeWord_support {K : Type*} [Semiring K]
    (middle : ℕ → ℤ → K) (last : ℕ → K) (ps : List ℕ)
    (hps : ∀ p ∈ ps, p.Prime) {m : ℕ} {A : ℤ → K}
    (hA : ∀ r : ℤ, r < 0 → A r ≠ 0 →
      ∃ t : ℕ, 0 < t ∧ t ∣ m ∧ r = - (t : ℤ) ^ 2) :
    ∀ r : ℤ, r < 0 → squareHeckeWord middle last ps A r ≠ 0 →
      ∃ t : ℕ, 0 < t ∧ t ∣ ps.prod * m ∧ r = - (t : ℤ) ^ 2 := by
  induction ps generalizing m A with
  | nil => simpa [squareHeckeWord] using hA
  | cons p ps ih =>
    have hp : p.Prime := hps p (by simp)
    have ht : ∀ q ∈ ps, q.Prime := fun q hq => hps q (by simp [hq])
    have hstep := negativeSquareSupported_squareHecke hp hA (middle p) (last p)
    simpa only [squareHeckeWord, List.prod_cons, mul_assoc, mul_comm, mul_left_comm]
      using ih ht hstep

theorem squareHeckeWord_leading {K : Type*} [CommSemiring K]
    (middle : ℕ → ℤ → K) (last : ℕ → K) (ps : List ℕ)
    (hps : ∀ p ∈ ps, p.Prime) {m : ℕ} (hm : 0 < m) {A : ℤ → K}
    (hA : ∀ r : ℤ, r < 0 → A r ≠ 0 →
      ∃ t : ℕ, 0 < t ∧ t ∣ m ∧ r = - (t : ℤ) ^ 2) :
    squareHeckeWord middle last ps A (- ((ps.prod * m : ℕ) : ℤ) ^ 2) =
      (ps.map last).prod * A (- (m : ℤ) ^ 2) := by
  induction ps generalizing m A with
  | nil => simp [squareHeckeWord]
  | cons p ps ih =>
    have hp : p.Prime := hps p (by simp)
    have ht : ∀ q ∈ ps, q.Prime := fun q hq => hps q (by simp [hq])
    have hstep := negativeSquareSupported_squareHecke hp hA (middle p) (last p)
    have htop := squareHecke_leading_coefficient hp hm hA (middle p) (last p)
    have hrec := ih ht (Nat.mul_pos hp.pos hm) hstep
    simp only [squareHeckeWord, List.prod_cons, List.map_cons, List.prod_cons] at hrec ⊢
    convert hrec using 1 <;> try { congr 2 <;> omega }
    all_goals try { ring }
    rw [htop]
    ring

/-- The integral diagonal multiplier before embedding in rational coefficients. -/
def etaHeckeDiagonalInt (p : ℕ) (r : ℤ) : ℤ :=
  jacobiSym 12 p * jacobiSym (-r) p

/-- The integral diagonal multiplier is the product of its Jacobi symbols. -/
theorem etaHeckeDiagonalInt_apply (p : ℕ) (r : ℤ) :
    etaHeckeDiagonalInt p r = jacobiSym 12 p * jacobiSym (-r) p := (rfl)

/-- The integral weight-`3/2` word, whose coefficients supply the integers `c_t`. -/
def heckeThreeHalfWordInt (ps : List ℕ) (A : ℤ → ℤ) : ℤ → ℤ :=
  squareHeckeWord etaHeckeDiagonalInt (fun p => (p : ℤ)) ps A

/-- The integral weight `3/2` word uses the square-index coefficient action. -/
theorem heckeThreeHalfWordInt_eq_squareHeckeWord (ps : List ℕ) (A : ℤ → ℤ) :
    heckeThreeHalfWordInt ps A =
      squareHeckeWord etaHeckeDiagonalInt (fun p => (p : ℤ)) ps A := (rfl)

theorem heckeThreeHalfWord_eq_squareHeckeWord (ps : List ℕ) (A : ℤ → ℚ) :
    heckeThreeHalfWord ps A =
      squareHeckeWord etaHeckeDiagonal (fun p => (p : ℚ)) ps A := by
  induction ps generalizing A with
  | nil => simp only [heckeThreeHalfWord_nil, squareHeckeWord]
  | cons p ps ih =>
    simpa only [heckeThreeHalfWord_cons, squareHeckeWord,
      heckeThreeHalf_eq_squareHecke] using
      ih (heckeThreeHalf p A)

/-- A coefficient word commutes with a change of coefficient ring. -/
theorem squareHeckeWord_map {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (middle : ℕ → ℤ → R) (last : ℕ → R)
    (ps : List ℕ) (A : ℤ → R) (r : ℤ) :
    f (squareHeckeWord middle last ps A r) =
      squareHeckeWord (fun p s => f (middle p s)) (fun p => f (last p)) ps
        (fun s => f (A s)) r := by
  induction ps generalizing A with
  | nil => rfl
  | cons p ps ih =>
    simp only [squareHeckeWord]
    rw [ih]
    congr 1
    funext s
    exact squareHecke_map f p (middle p) (last p) A s

theorem heckeThreeHalfWordInt_cast (ps : List ℕ) (A : ℤ → ℤ) (r : ℤ) :
    (heckeThreeHalfWordInt ps A r : ℚ) =
      heckeThreeHalfWord ps (fun s => (A s : ℚ)) r := by
  rw [heckeThreeHalfWordInt, heckeThreeHalfWord_eq_squareHeckeWord]
  have hmiddle : (fun p s => (Int.castRingHom ℚ) (etaHeckeDiagonalInt p s)) =
      etaHeckeDiagonal := by
    funext p s
    simp [etaHeckeDiagonalInt_apply, etaHeckeDiagonal_apply]
  have hlast : (fun p : ℕ => (Int.castRingHom ℚ) (p : ℤ)) =
      (fun p : ℕ => (p : ℚ)) := by funext p; simp
  have hmap := squareHeckeWord_map (Int.castRingHom ℚ) etaHeckeDiagonalInt
    (fun p => (p : ℤ)) ps A r
  change ((squareHeckeWord etaHeckeDiagonalInt (fun p => (p : ℤ)) ps A r : ℤ) : ℚ) =
    squareHeckeWord (fun p s => (Int.castRingHom ℚ) (etaHeckeDiagonalInt p s))
      (fun p => (Int.castRingHom ℚ) (p : ℤ)) ps (fun s => (A s : ℚ)) r at hmap
  simpa only [hmiddle, hlast] using hmap

theorem fFourier_negativeSquareSupported :
    ∀ r : ℤ, r < 0 → fFourier r ≠ 0 →
      ∃ t : ℕ, 0 < t ∧ t ∣ 1 ∧ r = - (t : ℤ) ^ 2 := by
  intro r hr hne
  by_cases h : r = -1
  · subst r
    exact ⟨1, by decide, dvd_refl _, by norm_num⟩
  · have hlt : r < -1 := by omega
    exact False.elim (hne (fFourier_eq_zero_of_lt hlt))

theorem partitionFourier_negativeSquareSupported :
    ∀ r : ℤ, r < 0 → partitionFourier r ≠ 0 →
      ∃ t : ℕ, 0 < t ∧ t ∣ 1 ∧ r = - (t : ℤ) ^ 2 := by
  intro r hr hne
  by_cases h : r = -1
  · subst r
    exact ⟨1, by decide, dvd_refl _, by norm_num⟩
  · have hlt : r < -1 := by omega
    exact False.elim (hne (partitionFourier_eq_zero_of_lt hlt))

/-- The integral coefficient attached to the negative square `-t²` after a word. -/
noncomputable def heckePrincipalCoefficient (ps : List ℕ) (t : ℕ) : ℤ :=
  heckeThreeHalfWordInt ps fFourier (- (t : ℤ) ^ 2)

/-- The negative-square coefficient represented by `heckePrincipalCoefficient`. -/
theorem heckePrincipalCoefficient_apply (ps : List ℕ) (t : ℕ) :
    heckePrincipalCoefficient ps t =
      heckeThreeHalfWordInt ps fFourier (- (t : ℤ) ^ 2) := (rfl)

/-- Every negative coefficient of the composed `f` series lies on a divisor square. -/
theorem heckePrincipalCoefficient_support (ps : List ℕ)
    (hps : ∀ p ∈ ps, p.Prime) :
    ∀ r : ℤ, r < 0 → heckeThreeHalfWordInt ps fFourier r ≠ 0 →
      ∃ t : ℕ, 0 < t ∧ t ∣ ps.prod ∧ r = - (t : ℤ) ^ 2 := by
  simpa only [heckeThreeHalfWordInt, mul_one] using
    (squareHeckeWord_support etaHeckeDiagonalInt (fun p => (p : ℤ)) ps hps
      fFourier_negativeSquareSupported)

/-- The largest negative-square coefficient is the product of all primes,
including repeated factors. -/
theorem heckePrincipalCoefficient_top (ps : List ℕ)
    (hps : ∀ p ∈ ps, p.Prime) :
    heckePrincipalCoefficient ps ps.prod = (ps.prod : ℤ) := by
  have htop := squareHeckeWord_leading etaHeckeDiagonalInt (fun p => (p : ℤ))
    ps hps (by decide : 0 < (1 : ℕ)) fFourier_negativeSquareSupported
  have hprod : (ps.map fun p : ℕ => (p : ℤ)).prod = (ps.prod : ℤ) := by
    simp
  have hbase : fFourier (- ((1 : ℕ) : ℤ) ^ 2) = 1 := by norm_num
  simpa only [heckePrincipalCoefficient, heckeThreeHalfWordInt, mul_one,
    hprod, hbase] using htop

/-- A Hecke step at a positive index depends only on negative input indices
when the output index is negative. -/
theorem squareHecke_eq_on_negative {K : Type*} [Semiring K]
    {p : ℕ} (hp : 0 < p) (middle : ℤ → K) (last : K)
    {A B : ℤ → K} (hAB : ∀ r : ℤ, r < 0 → A r = B r)
    {r : ℤ} (hr : r < 0) :
    squareHecke p middle last A r = squareHecke p middle last B r := by
  have hp2 : (0 : ℤ) < (p : ℤ) ^ 2 := by
    have hpZ : (0 : ℤ) < p := by exact_mod_cast hp
    exact sq_pos_of_pos hpZ
  have hup : (p : ℤ) ^ 2 * r < 0 := mul_neg_of_pos_of_neg hp2 hr
  have hdown : squareDown p A r = squareDown p B r := by
    simp only [squareDown_apply]
    split_ifs with hdiv
    · have hqneg : r / (p : ℤ) ^ 2 < 0 := by
        by_contra hnonneg
        have hmul : 0 ≤ r / (p : ℤ) ^ 2 * (p : ℤ) ^ 2 :=
          mul_nonneg (le_of_not_gt hnonneg) (le_of_lt hp2)
        rw [Int.ediv_mul_cancel hdiv] at hmul
        omega
      exact hAB _ hqneg
    · rfl
  simp only [squareHecke_apply, hAB _ hup, hAB _ hr, hdown]

theorem heckeThreeHalfWord_eq_on_negative (ps : List ℕ)
    (hps : ∀ p ∈ ps, 0 < p) {A B : ℤ → ℚ}
    (hAB : ∀ r : ℤ, r < 0 → A r = B r)
    {r : ℤ} (hr : r < 0) :
    heckeThreeHalfWord ps A r = heckeThreeHalfWord ps B r := by
  induction ps generalizing A B with
  | nil => simpa only [heckeThreeHalfWord_nil] using hAB r hr
  | cons p ps ih =>
    have hp : 0 < p := hps p (by simp)
    have ht : ∀ q ∈ ps, 0 < q := fun q hq => hps q (by simp [hq])
    simpa only [heckeThreeHalfWord_cons, heckeThreeHalf_eq_squareHecke] using
      ih ht (fun s hs => squareHecke_eq_on_negative hp
        (etaHeckeDiagonal p) (p : ℚ) hAB hs)

/-- On all negative indices, `f` is the Euler derivative of `P`. -/
theorem fFourier_eq_negative_derivative {r : ℤ} (hr : r < 0) :
    (fFourier r : ℚ) =
      -24 * thetaCoefficients (fun s => (partitionFourier s : ℚ)) r := by
  rw [fFourier_negative hr]
  simp only [thetaCoefficients_apply, Int.cast_mul, Int.cast_neg]
  ring

/-- The exact derivative relation at every negative index after a repeated-prime word. -/
theorem heckePrincipal_derivative (ps : List ℕ)
    (hps : ∀ p ∈ ps, p.Prime) {r : ℤ} (hr : r < 0) :
    (heckeThreeHalfWordInt ps fFourier r : ℚ) =
      - (r : ℚ) * (ps.prod : ℚ) ^ 2 *
        heckeMinusHalfWord ps (fun s => (partitionFourier s : ℚ)) r := by
  have hpos : ∀ p ∈ ps, 0 < p := fun p hp => (hps p hp).pos
  have hnonzero : ∀ p ∈ ps, p ≠ 0 := fun p hp => (hps p hp).ne_zero
  rw [heckeThreeHalfWordInt_cast]
  have hcongr := heckeThreeHalfWord_eq_on_negative ps hpos
    (fun s hs => fFourier_eq_negative_derivative hs) hr
  rw [hcongr, heckeThreeHalfWord_smul,
    heckeThreeHalfWord_theta ps hnonzero]
  simp only [thetaCoefficients_apply]
  ring

/-- The coefficient of `m²(P|U_m)` at `-t²` is `c_t/t²`. -/
theorem heckePrincipal_partition_coefficient (ps : List ℕ)
    (hps : ∀ p ∈ ps, p.Prime) {t : ℕ} (ht : 0 < t) :
    (ps.prod : ℚ) ^ 2 *
      heckeMinusHalfWord ps (fun s => (partitionFourier s : ℚ))
        (- (t : ℤ) ^ 2) =
      (heckePrincipalCoefficient ps t : ℚ) / (t : ℚ) ^ 2 := by
  have htq : (t : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ht)
  have hneg : - (t : ℤ) ^ 2 < 0 := by
    have htZ : (0 : ℤ) < t := by exact_mod_cast ht
    nlinarith
  have h := heckePrincipal_derivative ps hps hneg
  change (heckePrincipalCoefficient ps t : ℚ) =
    - ((- (t : ℤ) ^ 2 : ℤ) : ℚ) * (ps.prod : ℚ) ^ 2 *
      heckeMinusHalfWord ps (fun s => (partitionFourier s : ℚ)) (- (t : ℤ) ^ 2) at h
  have hcoeff : (heckePrincipalCoefficient ps t : ℚ) =
      (t : ℚ) ^ 2 * (ps.prod : ℚ) ^ 2 *
        heckeMinusHalfWord ps (fun s => (partitionFourier s : ℚ)) (- (t : ℤ) ^ 2) := by
    simpa only [Int.cast_neg, Int.cast_pow, Int.cast_natCast, neg_neg] using h
  apply (eq_div_iff (pow_ne_zero 2 htq)).mpr
  linear_combination -hcoeff

/-- Keep exactly the negative-index coefficients of a Fourier sequence. -/
def negativePrincipalPart {K : Type*} [Zero K] (A : ℤ → K) (r : ℤ) : K :=
  if r < 0 then A r else 0

/-- The finite divisor-square expansion of a negative principal part. -/
def divisorSquarePrincipalPart {K : Type*} [AddCommMonoid K]
    (m : ℕ) (c : ℕ → K) (r : ℤ) : K :=
  if r < 0 then
    ∑ t ∈ m.divisors, if r = - (t : ℤ) ^ 2 then c t else 0
  else 0

private theorem neg_square_injective {s t : ℕ}
    (h : - (s : ℤ) ^ 2 = - (t : ℤ) ^ 2) : s = t := by
  have hs : (0 : ℤ) ≤ s := Int.natCast_nonneg s
  have ht : (0 : ℤ) ≤ t := Int.natCast_nonneg t
  have hst : (s : ℤ) = t := by nlinarith
  exact_mod_cast hst

/-- Divisor-square support is equivalent to the finite principal-part sum. -/
theorem negativePrincipalPart_eq_divisorSquare {K : Type*} [AddCommMonoid K]
    {m : ℕ} (hm : 0 < m)
    {A : ℤ → K}
    (hA : ∀ r : ℤ, r < 0 → A r ≠ 0 →
      ∃ t : ℕ, 0 < t ∧ t ∣ m ∧ r = - (t : ℤ) ^ 2) (r : ℤ) :
    negativePrincipalPart A r =
      divisorSquarePrincipalPart m (fun t => A (- (t : ℤ) ^ 2)) r := by
  by_cases hr : r < 0
  · simp only [negativePrincipalPart, divisorSquarePrincipalPart, ite_eq_left hr]
    by_cases ha : A r = 0
    · rw [ha]
      symm
      apply Finset.sum_eq_zero
      intro t ht
      by_cases hindex : r = - (t : ℤ) ^ 2
      · simp only [ite_eq_left hindex]
        simpa only [← hindex] using ha
      · simp [hindex]
    · obtain ⟨t₀, htpos, htdiv, hindex⟩ := hA r hr ha
      have htmem : t₀ ∈ m.divisors := Nat.mem_divisors.mpr ⟨htdiv, by omega⟩
      have hsum : (∑ t ∈ m.divisors,
          if - (t₀ : ℤ) ^ 2 = - (t : ℤ) ^ 2 then A (- (t : ℤ) ^ 2) else 0) =
          A (- (t₀ : ℤ) ^ 2) := by
        calc
          _ = ∑ t ∈ m.divisors, if t = t₀ then A (- (t₀ : ℤ) ^ 2) else 0 := by
            apply Finset.sum_congr rfl
            intro t ht
            by_cases heq : t = t₀
            · subst t
              simp
            · have hneq : - (t₀ : ℤ) ^ 2 ≠ - (t : ℤ) ^ 2 := by
                intro hsq
                exact heq (neg_square_injective hsq).symm
              simp [heq, hneq]
          _ = A (- (t₀ : ℤ) ^ 2) := by simp [htmem]
      rw [hindex]
      exact hsum.symm
  · simp [negativePrincipalPart, divisorSquarePrincipalPart, hr]

/-- The manuscript's finite principal-part identity for `f|U_m`. -/
theorem heckeThreeHalfWord_principalPart (ps : List ℕ)
    (hps : ∀ p ∈ ps, p.Prime) :
    negativePrincipalPart (heckeThreeHalfWordInt ps fFourier) =
      divisorSquarePrincipalPart ps.prod (heckePrincipalCoefficient ps) := by
  funext r
  have hpos : 0 < ps.prod := by
    induction ps with
    | nil => simp
    | cons p ps ih =>
      have hp : p.Prime := hps p (by simp)
      have ht : ∀ q ∈ ps, q.Prime := fun q hq => hps q (by simp [hq])
      simp only [List.prod_cons]
      exact Nat.mul_pos hp.pos (ih ht)
  change negativePrincipalPart (heckeThreeHalfWordInt ps fFourier) r =
    divisorSquarePrincipalPart ps.prod
      (fun t => heckeThreeHalfWordInt ps fFourier (- (t : ℤ) ^ 2)) r
  exact negativePrincipalPart_eq_divisorSquare hpos
    (heckePrincipalCoefficient_support ps hps) r

private theorem primeWord_prod_pos (ps : List ℕ)
    (hps : ∀ p ∈ ps, p.Prime) : 0 < ps.prod := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    have hp : p.Prime := hps p (by simp)
    have ht : ∀ q ∈ ps, q.Prime := fun q hq => hps q (by simp [hq])
    simp only [List.prod_cons]
    exact Nat.mul_pos hp.pos (ih ht)

theorem heckeMinusHalfWord_scaled_support (ps : List ℕ)
    (hps : ∀ p ∈ ps, p.Prime) :
    ∀ r : ℤ, r < 0 →
      (ps.prod : ℚ) ^ 2 *
        heckeMinusHalfWord ps (fun s => (partitionFourier s : ℚ)) r ≠ 0 →
      ∃ t : ℕ, 0 < t ∧ t ∣ ps.prod ∧ r = - (t : ℤ) ^ 2 := by
  intro r hr hne
  have hrel := heckePrincipal_derivative ps hps hr
  have hrq : - (r : ℚ) ≠ 0 := by
    have hr0 : r ≠ 0 := ne_of_lt hr
    exact neg_ne_zero.mpr (Int.cast_ne_zero.mpr hr0)
  have hFne : heckeThreeHalfWordInt ps fFourier r ≠ 0 := by
    intro hz
    have hzero : - (r : ℚ) * ((ps.prod : ℚ) ^ 2 *
        heckeMinusHalfWord ps (fun s => (partitionFourier s : ℚ)) r) = 0 := by
      rw [← mul_assoc, ← hrel]
      simp [hz]
    exact hne ((mul_eq_zero.mp hzero).resolve_left hrq)
  exact heckePrincipalCoefficient_support ps hps r hr hFne

/-- The manuscript's finite principal-part identity for `m²(P|U_m)`.
The rational coefficient at `-t²` is exactly the integer `c_t` divided by `t²`. -/
theorem heckeMinusHalfWord_principalPart (ps : List ℕ)
    (hps : ∀ p ∈ ps, p.Prime) :
    negativePrincipalPart (fun r => (ps.prod : ℚ) ^ 2 *
      heckeMinusHalfWord ps (fun s => (partitionFourier s : ℚ)) r) =
      divisorSquarePrincipalPart ps.prod
        (fun t => (heckePrincipalCoefficient ps t : ℚ) / (t : ℚ) ^ 2) := by
  funext r
  have hpos := primeWord_prod_pos ps hps
  calc
    negativePrincipalPart (fun r => (ps.prod : ℚ) ^ 2 *
        heckeMinusHalfWord ps (fun s => (partitionFourier s : ℚ)) r) r =
        divisorSquarePrincipalPart ps.prod
          (fun t => (ps.prod : ℚ) ^ 2 *
            heckeMinusHalfWord ps (fun s => (partitionFourier s : ℚ))
              (- (t : ℤ) ^ 2)) r :=
      negativePrincipalPart_eq_divisorSquare hpos
        (heckeMinusHalfWord_scaled_support ps hps) r
    _ = divisorSquarePrincipalPart ps.prod
          (fun t => (heckePrincipalCoefficient ps t : ℚ) / (t : ℚ) ^ 2) r := by
      unfold divisorSquarePrincipalPart
      by_cases hr : r < 0
      · simp only [ite_eq_left hr]
        apply Finset.sum_congr rfl
        intro t ht
        have htpos : 0 < t := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp ht).1 hpos
        by_cases hindex : r = - (t : ℤ) ^ 2
        · simp only [ite_eq_left hindex]
          exact heckePrincipal_partition_coefficient ps hps htpos
        · simp [hindex]
      · simp [hr]

/-- The same integral principal part, now viewed in the actual rational
weight-`3/2` coefficient operator. -/
theorem heckeThreeHalfWord_principalPart_rat (ps : List ℕ)
    (hps : ∀ p ∈ ps, p.Prime) :
    negativePrincipalPart (heckeThreeHalfWord ps (fun r => (fFourier r : ℚ))) =
      divisorSquarePrincipalPart ps.prod
        (fun t => (heckePrincipalCoefficient ps t : ℚ)) := by
  funext r
  have hInt := congrFun (heckeThreeHalfWord_principalPart ps hps) r
  calc
    negativePrincipalPart (heckeThreeHalfWord ps (fun r => (fFourier r : ℚ))) r =
        ((negativePrincipalPart (heckeThreeHalfWordInt ps fFourier) r : ℤ) : ℚ) := by
      by_cases hr : r < 0
      · simp only [negativePrincipalPart, ite_eq_left hr]
        exact (heckeThreeHalfWordInt_cast ps fFourier r).symm
      · simp [negativePrincipalPart, hr]
    _ = ((divisorSquarePrincipalPart ps.prod (heckePrincipalCoefficient ps) r : ℤ) : ℚ) := by
      exact congrArg (fun x : ℤ => (x : ℚ)) hInt
    _ = divisorSquarePrincipalPart ps.prod
          (fun t => (heckePrincipalCoefficient ps t : ℚ)) r := by
      by_cases hr : r < 0
      · simp only [divisorSquarePrincipalPart, ite_eq_left hr, Int.cast_sum]
        apply Finset.sum_congr rfl
        intro t ht
        split_ifs <;> simp
      · simp [divisorSquarePrincipalPart, hr]

/-- Triangular principal parts for a prime word with product `m`, as in the
manuscript. The coprimality hypothesis records the domain of its Hecke operators. -/
theorem hecke_principal_parts (ps : List ℕ)
    (hps : ∀ p ∈ ps, p.Prime) (_hcop : ps.prod.Coprime 6) :
    ∃ c : ℕ → ℤ,
      c ps.prod = (ps.prod : ℤ) ∧
      negativePrincipalPart (heckeThreeHalfWord ps (fun r => (fFourier r : ℚ))) =
        divisorSquarePrincipalPart ps.prod (fun t => (c t : ℚ)) ∧
      negativePrincipalPart (fun r => (ps.prod : ℚ) ^ 2 *
        heckeMinusHalfWord ps (fun s => (partitionFourier s : ℚ)) r) =
        divisorSquarePrincipalPart ps.prod (fun t => (c t : ℚ) / (t : ℚ) ^ 2) := by
  exact ⟨heckePrincipalCoefficient ps,
    heckePrincipalCoefficient_top ps hps,
    heckeThreeHalfWord_principalPart_rat ps hps,
    heckeMinusHalfWord_principalPart ps hps⟩

/-- The weight `3/2` Hecke composition indexed by a positive integer,
using its prime factors with multiplicity. -/
def heckeThreeHalfIndex (m : ℕ) (A : ℤ → ℚ) : ℤ → ℚ :=
  heckeThreeHalfWord m.primeFactorsList A

/-- The corresponding weight `-1/2` Hecke composition. -/
def heckeMinusHalfIndex (m : ℕ) (A : ℤ → ℚ) : ℤ → ℚ :=
  heckeMinusHalfWord m.primeFactorsList A

/-- The two adjacent half-integral-weight coefficient operators used in the
manuscript's Hecke composition. -/
structure EtaHeckeCompositions where
  threeHalf : (ℤ → ℚ) → ℤ → ℚ
  minusHalf : (ℤ → ℚ) → ℤ → ℚ

/-- Both weight normalizations of `U_m`, retaining the full prime-factor
list, including repeated prime factors. -/
def etaHeckeCompositions (m : ℕ) : EtaHeckeCompositions where
  threeHalf := heckeThreeHalfIndex m
  minusHalf := heckeMinusHalfIndex m

/-- The manuscript's principal-part system for every positive index
coprime to six, with the standard prime factorization supplying the word. -/
theorem hecke_principal_parts_index (m : ℕ) (hm : 0 < m)
    (hcop : m.Coprime 6) :
    ∃ c : ℕ → ℤ,
      c m = (m : ℤ) ∧
      negativePrincipalPart (heckeThreeHalfIndex m (fun r => (fFourier r : ℚ))) =
        divisorSquarePrincipalPart m (fun t => (c t : ℚ)) ∧
      negativePrincipalPart (fun r => (m : ℚ) ^ 2 *
        heckeMinusHalfIndex m (fun s => (partitionFourier s : ℚ)) r) =
        divisorSquarePrincipalPart m (fun t => (c t : ℚ) / (t : ℚ) ^ 2) := by
  have hprod : m.primeFactorsList.prod = m :=
    Nat.prod_primeFactorsList (Nat.ne_of_gt hm)
  have hps : ∀ p ∈ m.primeFactorsList, p.Prime :=
    fun p hp => Nat.prime_of_mem_primeFactorsList hp
  have hcopword : m.primeFactorsList.prod.Coprime 6 := by
    simpa only [hprod] using hcop
  have hword := hecke_principal_parts m.primeFactorsList hps hcopword
  simpa only [heckeThreeHalfIndex, heckeMinusHalfIndex, hprod] using hword

/-- The indexed derivative law for the actual partition Fourier row. Prime
factors occur with multiplicity, and `thetaCoefficients` uses the exponent
`r/24` [rolenManuscript, §3]. -/
theorem hecke_partition_derivative_index (m : ℕ) (hm : 0 < m)
    (_hcop : m.Coprime 6) :
    heckeThreeHalfIndex m
        (thetaCoefficients (fun r => (partitionFourier r : ℚ))) =
      fun r => (m : ℚ) ^ 2 *
        thetaCoefficients
          (heckeMinusHalfIndex m (fun s => (partitionFourier s : ℚ))) r := by
  have hprod : m.primeFactorsList.prod = m :=
    Nat.prod_primeFactorsList (Nat.ne_of_gt hm)
  have hps : ∀ p ∈ m.primeFactorsList, p ≠ 0 := by
    intro p hp
    exact (Nat.prime_of_mem_primeFactorsList hp).ne_zero
  have hword := heckeThreeHalfWord_theta m.primeFactorsList hps
    (fun r => (partitionFourier r : ℚ))
  simpa only [heckeThreeHalfIndex, heckeMinusHalfIndex, hprod] using hword

end SptClassification.QSeries
