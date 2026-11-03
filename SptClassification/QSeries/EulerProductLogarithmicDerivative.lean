/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.EulerDerivative
public import SptClassification.QSeries.LambertCoefficients
public import Mathlib.RingTheory.PowerSeries.Inverse
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# Formal Euler products with integral exponents

An exponent in the normalized CM product can be negative. The corresponding
factor uses the inverse of `1 - X ^ m` in the formal power-series ring. The
coefficient of degree `n` in the infinite product is represented by its finite
stage through `m = n`; later factors start in higher degree. This is the
integral-exponent product in [rolen2026canonical, Theorem 4.2, (4.4)].
-/

public section

namespace SptClassification.QSeries

open PowerSeries

/-- A formal Euler factor raised to an arbitrary integer exponent. For
positive `m`, the inverse used here has constant coefficient one. -/
noncomputable def integerEulerFactor {R : Type*} [CommRing R]
    (m : ℕ) (e : ℤ) : PowerSeries R :=
  (1 - X ^ m : PowerSeries R) ^ e.toNat *
    ((1 - X ^ m : PowerSeries R).invOfUnit 1) ^ (-e).toNat

/-- The finite Euler product through factor `m = N`. -/
noncomputable def integerEulerPartialProduct {R : Type*} [CommRing R]
    (e : ℕ → ℤ) (N : ℕ) : PowerSeries R :=
  ∏ j ∈ Finset.range N, integerEulerFactor (j + 1) (e (j + 1))

/-- The coefficientwise formal product. Factors with `m > n` contribute
only to terms beyond degree `n`. -/
noncomputable def integerEulerProduct {R : Type*} [CommRing R]
    (e : ℕ → ℤ) : PowerSeries R :=
  PowerSeries.mk fun n => (integerEulerPartialProduct e n).coeff n

private theorem coeff_mul_of_coeff_eq_through {R : Type*} [CommRing R]
    (F G H : PowerSeries R) (n : ℕ)
    (h : ∀ k ≤ n, F.coeff k = G.coeff k) :
    (F * H).coeff n = (G * H).coeff n := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have hi : ij.1 ≤ n := by
    have := Finset.mem_antidiagonal.mp hij
    omega
  rw [h ij.1 hi]

private theorem coeff_mul_of_coeff_eq_below {R : Type*} [CommRing R]
    (F G H K : PowerSeries R) (m n : ℕ) (hn : n < m)
    (hFG : ∀ k < m, F.coeff k = G.coeff k)
    (hHK : ∀ k < m, H.coeff k = K.coeff k) :
    (F * H).coeff n = (G * K).coeff n := by
  calc
    (F * H).coeff n = (G * H).coeff n :=
      coeff_mul_of_coeff_eq_through F G H n (fun k hk => hFG k (by omega))
    _ = (H * G).coeff n := by rw [mul_comm]
    _ = (K * G).coeff n :=
      coeff_mul_of_coeff_eq_through H K G n (fun k hk => hHK k (by omega))
    _ = (G * K).coeff n := by rw [mul_comm]

private theorem one_sub_X_pow_coeff_below {R : Type*} [CommRing R]
    (m k : ℕ) (hk : k < m) :
    ((1 - X ^ m : PowerSeries R).coeff k) = (1 : PowerSeries R).coeff k := by
  simp [map_sub, PowerSeries.coeff_X_pow, ne_of_lt hk]

private theorem inverse_one_sub_X_pow_coeff_below {R : Type*} [CommRing R]
    (m k : ℕ) (hm : 0 < m) (hk : k < m) :
    ((1 - X ^ m : PowerSeries R).invOfUnit 1).coeff k =
      (1 : PowerSeries R).coeff k := by
  have hc : constantCoeff (1 - X ^ m : PowerSeries R) = 1 := by
    simp [hm.ne']
  have hmul : (1 - X ^ m : PowerSeries R) *
      (1 - X ^ m : PowerSeries R).invOfUnit 1 = 1 :=
    PowerSeries.mul_invOfUnit _ _ hc
  have heq := coeff_mul_of_coeff_eq_through
    (1 - X ^ m : PowerSeries R) 1
    ((1 - X ^ m : PowerSeries R).invOfUnit 1) k
    (fun j hj => one_sub_X_pow_coeff_below m j (by omega))
  simpa [hmul] using heq.symm

private theorem pow_coeff_below_of_coeff_below {R : Type*} [CommRing R]
    (F : PowerSeries R) (m : ℕ)
    (hF : ∀ k < m, F.coeff k = (1 : PowerSeries R).coeff k)
    (r : ℕ) (k : ℕ) (hk : k < m) :
    (F ^ r).coeff k = (1 : PowerSeries R).coeff k := by
  induction r generalizing k with
  | zero => simp
  | succ r ih =>
    rw [pow_succ]
    calc
      (F ^ r * F).coeff k =
          ((1 : PowerSeries R) * (1 : PowerSeries R)).coeff k :=
        coeff_mul_of_coeff_eq_below (F ^ r) 1 F 1 m k hk
          (fun j hj => ih j hj) hF
      _ = (1 : PowerSeries R).coeff k := by simp

/-- An Euler factor indexed by `m` changes no coefficient below degree `m`,
regardless of the sign of its exponent. -/
theorem integerEulerFactor_coeff_below {R : Type*} [CommRing R]
    (m k : ℕ) (e : ℤ) (hm : 0 < m) (hk : k < m) :
    (integerEulerFactor (R := R) m e).coeff k =
      (1 : PowerSeries R).coeff k := by
  unfold integerEulerFactor
  calc
    ((1 - X ^ m : PowerSeries R) ^ e.toNat *
        ((1 - X ^ m : PowerSeries R).invOfUnit 1) ^ (-e).toNat).coeff k =
        ((1 : PowerSeries R) * 1).coeff k :=
      coeff_mul_of_coeff_eq_below _ _ _ _ m k hk
        (fun j hj => pow_coeff_below_of_coeff_below _ m
          (fun i hi => one_sub_X_pow_coeff_below m i hi) _ j hj)
        (fun j hj => pow_coeff_below_of_coeff_below _ m
          (fun i hi => inverse_one_sub_X_pow_coeff_below m i hm hi) _ j hj)
    _ = (1 : PowerSeries R).coeff k := by simp

private theorem integerEulerPartialProduct_succ {R : Type*} [CommRing R]
    (e : ℕ → ℤ) (N : ℕ) :
    integerEulerPartialProduct (R := R) e (N + 1) =
      integerEulerPartialProduct e N * integerEulerFactor (N + 1) (e (N + 1)) := by
  simp [integerEulerPartialProduct, Finset.prod_range_succ]

/-- Once a finite product includes all factors through degree `n`, its
coefficient of degree `n` is stable. -/
theorem integerEulerPartialProduct_coeff_stable {R : Type*} [CommRing R]
    (e : ℕ → ℤ) (n N : ℕ) (hN : n ≤ N) :
    (integerEulerPartialProduct (R := R) e N).coeff n =
      (integerEulerPartialProduct e n).coeff n := by
  induction N, hN using Nat.le_induction with
  | base => rfl
  | succ N hN ih =>
    rw [integerEulerPartialProduct_succ]
    have hnew : (integerEulerFactor (R := R) (N + 1) (e (N + 1)) *
        integerEulerPartialProduct e N).coeff n =
        ((1 : PowerSeries R) * integerEulerPartialProduct e N).coeff n :=
      coeff_mul_of_coeff_eq_through _ _ _ n (fun k hk =>
        integerEulerFactor_coeff_below (N + 1) k (e (N + 1))
          (by omega) (by omega))
    rw [mul_comm (integerEulerPartialProduct e N), hnew, one_mul]
    exact ih

@[simp] theorem coeff_integerEulerProduct {R : Type*} [CommRing R]
    (e : ℕ → ℤ) (n N : ℕ) (hN : n ≤ N) :
    (integerEulerProduct (R := R) e).coeff n =
      (integerEulerPartialProduct e N).coeff n := by
  simp only [integerEulerProduct, PowerSeries.coeff_mk]
  exact (integerEulerPartialProduct_coeff_stable e n N hN).symm

/-- The Euler derivative obeys the product rule in any commutative coefficient
ring; no division by an integer is involved. -/
theorem eulerDerivative_mul {R : Type*} [CommRing R]
    (F G : PowerSeries R) :
    eulerDerivative (F * G) = eulerDerivative F * G + F * eulerDerivative G := by
  ext n
  simp only [coeff_eulerDerivative, map_add,
    PowerSeries.coeff_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ij hij
  have hsum : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
  rw [← hsum, Nat.cast_add]
  ring

theorem eulerDerivative_add {R : Type*} [CommRing R]
    (F G : PowerSeries R) :
    eulerDerivative (F + G) = eulerDerivative F + eulerDerivative G := by
  ext n
  simp [coeff_eulerDerivative, mul_add]

theorem eulerDerivative_neg {R : Type*} [CommRing R]
    (F : PowerSeries R) : eulerDerivative (-F) = -eulerDerivative F := by
  ext n
  simp [coeff_eulerDerivative]

theorem eulerDerivative_sub {R : Type*} [CommRing R]
    (F G : PowerSeries R) :
    eulerDerivative (F - G) = eulerDerivative F - eulerDerivative G := by
  simpa [sub_eq_add_neg, eulerDerivative_add, eulerDerivative_neg]

/-- The Euler derivative commutes with coefficient change, including
reduction modulo a prime. -/
theorem eulerDerivative_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (F : PowerSeries R) :
    eulerDerivative (PowerSeries.map f F) =
      PowerSeries.map f (eulerDerivative F) := by
  ext n
  simp only [coeff_eulerDerivative, PowerSeries.coeff_map, map_mul, map_natCast]

/-- A normalized power-series unit keeps its inverse after changing the
coefficient ring. This includes reduction to positive characteristic. -/
theorem map_invOfUnit_one {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (F : PowerSeries R) (hF : constantCoeff F = 1) :
    PowerSeries.map f (F.invOfUnit 1) =
      (PowerSeries.map f F).invOfUnit 1 := by
  have hmap : constantCoeff (PowerSeries.map f F) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply] at hF ⊢
    simpa only [PowerSeries.coeff_map, hF, map_one]
  have hleft : PowerSeries.map f F * PowerSeries.map f (F.invOfUnit 1) = 1 := by
    rw [← map_mul, PowerSeries.mul_invOfUnit F 1 hF, map_one]
  have hright : (PowerSeries.map f F).invOfUnit 1 * PowerSeries.map f F = 1 := by
    rw [mul_comm]
    exact PowerSeries.mul_invOfUnit _ _ hmap
  calc
    PowerSeries.map f (F.invOfUnit 1) =
        1 * PowerSeries.map f (F.invOfUnit 1) := (one_mul _).symm
    _ = ((PowerSeries.map f F).invOfUnit 1 * PowerSeries.map f F) *
          PowerSeries.map f (F.invOfUnit 1) := by
        rw [hright]
    _ = (PowerSeries.map f F).invOfUnit 1 *
          (PowerSeries.map f F * PowerSeries.map f (F.invOfUnit 1)) := by ring
    _ = (PowerSeries.map f F).invOfUnit 1 := by rw [hleft, mul_one]

/-- Changing coefficients preserves an Euler factor with any integer
exponent. The inverse used for a negative exponent remains the inverse of
the reduced constant-one factor. -/
theorem map_integerEulerFactor {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (m : ℕ) (e : ℤ) (hm : 0 < m) :
    PowerSeries.map f (integerEulerFactor (R := R) m e) =
      integerEulerFactor (R := S) m e := by
  have hc : constantCoeff (1 - X ^ m : PowerSeries R) = 1 := by
    simp [hm.ne']
  unfold integerEulerFactor
  rw [map_mul, map_pow, map_pow,
    map_invOfUnit_one f (1 - X ^ m) hc]
  simp only [map_sub, map_one, map_pow, PowerSeries.map_X]

/-- The finite integral-exponent product commutes with coefficient change. -/
theorem map_integerEulerPartialProduct {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (e : ℕ → ℤ) (N : ℕ) :
    PowerSeries.map f (integerEulerPartialProduct (R := R) e N) =
      integerEulerPartialProduct (R := S) e N := by
  simp only [integerEulerPartialProduct, map_prod]
  apply Finset.prod_congr rfl
  intro j _
  exact map_integerEulerFactor f (j + 1) (e (j + 1)) (Nat.succ_pos j)

/-- The stabilized infinite product commutes with every change of
coefficient ring, including reduction at primes away from six. -/
theorem map_integerEulerProduct {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (e : ℕ → ℤ) :
    PowerSeries.map f (integerEulerProduct (R := R) e) =
      integerEulerProduct (R := S) e := by
  ext n
  simp only [PowerSeries.coeff_map, integerEulerProduct, PowerSeries.coeff_mk]
  rw [← PowerSeries.coeff_map, map_integerEulerPartialProduct]

/-- Logarithmic Euler differentiation commutes with coefficient change for
normalized units. -/
theorem eulerLogarithmicDerivative_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (F : PowerSeries R) (hF : constantCoeff F = 1) :
    eulerDerivative (PowerSeries.map f F) *
        (PowerSeries.map f F).invOfUnit 1 =
      PowerSeries.map f (eulerDerivative F * F.invOfUnit 1) := by
  rw [eulerDerivative_map, ← map_invOfUnit_one f F hF, map_mul]

@[simp] theorem eulerDerivative_one {R : Type*} [CommRing R] :
    eulerDerivative (1 : PowerSeries R) = 0 := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp
  · simp [coeff_eulerDerivative, hn]

theorem eulerDerivative_X_pow {R : Type*} [CommRing R] (m : ℕ) :
    eulerDerivative ((X : PowerSeries R) ^ m) = C (m : R) * X ^ m := by
  ext n
  by_cases hn : n = m
  · subst n
    simp [coeff_eulerDerivative, PowerSeries.coeff_C_mul]
  · simp [coeff_eulerDerivative, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_X_pow, hn]

private theorem eulerDerivative_pow_of_log {R : Type*} [CommRing R]
    (F L : PowerSeries R) (hF : eulerDerivative F = F * L) (r : ℕ) :
    eulerDerivative (F ^ r) = F ^ r * (C (r : R) * L) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, eulerDerivative_mul, ih, hF]
    simp only [Nat.cast_add, Nat.cast_one, map_add, map_one]
    ring

/-- The finite logarithmic term contributed by a factor of exponent `e`.
Its coefficient of positive degree `n` is `-m e` exactly when `m ∣ n`. -/
noncomputable def integerEulerLogTerm {R : Type*} [CommRing R]
    (m : ℕ) (e : ℤ) : PowerSeries R :=
  -(C (e : R) * C (m : R) * X ^ m *
    (1 - X ^ m : PowerSeries R).invOfUnit 1)

private theorem dvd_sub_iff_dvd {m n : ℕ} (hm : m ≤ n) :
    m ∣ n - m ↔ m ∣ n := by
  have hsum : m + (n - m) = n := by omega
  constructor
  · intro h
    rw [← hsum]
    exact dvd_add (dvd_refl m) h
  · intro h
    exact Nat.dvd_sub h (dvd_refl m)

/-- The inverse of `1-X^m` has coefficient one exactly at multiples of `m`.
The proof uses its defining inverse relation and strong induction on degree. -/
theorem coeff_inv_one_sub_X_pow {R : Type*} [CommRing R]
    (m n : ℕ) (hm : 0 < m) :
    ((1 - X ^ m : PowerSeries R).invOfUnit 1).coeff n =
      if m ∣ n then 1 else 0 := by
  let B : PowerSeries R := (1 - X ^ m : PowerSeries R).invOfUnit 1
  have hc : constantCoeff (1 - X ^ m : PowerSeries R) = 1 := by
    simp [hm.ne']
  have hmul : (1 - X ^ m : PowerSeries R) * B = 1 :=
    PowerSeries.mul_invOfUnit _ _ hc
  change B.coeff n = if m ∣ n then 1 else 0
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have h := congrArg (PowerSeries.coeff n) hmul
    rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul'] at h
    by_cases hn : n = 0
    · subst n
      simpa [show ¬m ≤ 0 by omega] using h
    have hrec : B.coeff n = if m ≤ n then B.coeff (n - m) else 0 :=
      sub_eq_zero.mp (by simpa [hn] using h)
    by_cases hle : m ≤ n
    · calc
        B.coeff n = B.coeff (n - m) := by simpa [hle] using hrec
        _ = if m ∣ n - m then 1 else 0 := ih (n - m) (by omega)
        _ = if m ∣ n then 1 else 0 := by simp only [dvd_sub_iff_dvd hle]
    · have hnot : ¬m ∣ n := by
        intro hdiv
        exact hle (Nat.le_of_dvd (by omega) hdiv)
      simpa [hle, hnot] using hrec

/-- A single factor contributes `-m e` at each positive multiple of `m`.
This calculation is valid in every commutative coefficient ring. -/
theorem coeff_integerEulerLogTerm {R : Type*} [CommRing R]
    (m n : ℕ) (e : ℤ) (hm : 0 < m) (hn : 0 < n) :
    (integerEulerLogTerm (R := R) m e).coeff n =
      if m ∣ n then -((m : R) * (e : R)) else 0 := by
  let B : PowerSeries R := (1 - X ^ m : PowerSeries R).invOfUnit 1
  have hshape :
      C (e : R) * C (m : R) * X ^ m * B =
        C ((e : R) * (m : R)) * (X ^ m * B) := by
    rw [map_mul]
    ring
  change (-(C (e : R) * C (m : R) * X ^ m * B)).coeff n = _
  rw [hshape, map_neg, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  by_cases hle : m ≤ n
  · rw [if_pos hle, coeff_inv_one_sub_X_pow m (n - m) hm]
    by_cases hd : m ∣ n
    · have hd' : m ∣ n - m := (dvd_sub_iff_dvd hle).2 hd
      simp [hd, hd'] <;> ring
    · have hd' : ¬m ∣ n - m := fun h => hd ((dvd_sub_iff_dvd hle).1 h)
      simp [hd, hd']
  · have hd : ¬m ∣ n := by
      intro hdiv
      exact hle (Nat.le_of_dvd hn hdiv)
    simp [hle, hd]

@[simp] theorem integerEulerLogTerm_coeff_zero {R : Type*} [CommRing R]
    (m : ℕ) (e : ℤ) (hm : 0 < m) :
    (integerEulerLogTerm (R := R) m e).coeff 0 = 0 := by
  simp [integerEulerLogTerm, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul', show ¬m ≤ 0 by omega, zero_pow hm.ne']

/-- The logarithmic derivative of one integral-exponent factor, proved by
the ordinary product rule and the inverse relation. -/
theorem eulerDerivative_integerEulerFactor {R : Type*} [CommRing R]
    (m : ℕ) (e : ℤ) (hm : 0 < m) :
    eulerDerivative (integerEulerFactor (R := R) m e) =
      integerEulerFactor m e * integerEulerLogTerm m e := by
  let A : PowerSeries R := 1 - X ^ m
  let B : PowerSeries R := A.invOfUnit 1
  let V : PowerSeries R := C (m : R) * X ^ m * B
  have hc : constantCoeff A = 1 := by simp [A, hm.ne']
  have hAB : A * B = 1 := PowerSeries.mul_invOfUnit A 1 hc
  have hAV : A * V = C (m : R) * X ^ m := by
    calc
      A * V = (C (m : R) * X ^ m) * (A * B) := by dsimp [V]; ring
      _ = C (m : R) * X ^ m := by rw [hAB, mul_one]
  have hA : eulerDerivative A = A * (-V) := by
    calc
      eulerDerivative A = -(C (m : R) * X ^ m) := by
        simp [A, eulerDerivative_sub, eulerDerivative_X_pow]
      _ = A * (-V) := by rw [mul_neg, hAV]
  have hB : eulerDerivative B = B * V := by
    have hzero : eulerDerivative A * B + A * eulerDerivative B = 0 := by
      rw [← eulerDerivative_mul, hAB, eulerDerivative_one]
    have hfirst : eulerDerivative A * B = -V := by
      calc
        eulerDerivative A * B = (A * (-V)) * B := by rw [hA]
        _ = -(A * B) * V := by ring
        _ = -V := by rw [hAB, neg_one_mul]
    have hpart : A * eulerDerivative B = V := by
      have hzero' : -V + A * eulerDerivative B = 0 := by
        rw [hfirst] at hzero
        exact hzero
      calc
        A * eulerDerivative B = (-V + A * eulerDerivative B) + V := by ring
        _ = V := by rw [hzero', zero_add]
    calc
      eulerDerivative B = (A * B) * eulerDerivative B := by rw [hAB, one_mul]
      _ = B * (A * eulerDerivative B) := by ring
      _ = B * V := by rw [hpart]
  have he : (e.toNat : R) - ((-e).toNat : R) = (e : R) := by
    have hez : (e.toNat : ℤ) - ((-e).toNat : ℤ) = e := by omega
    have he' := congrArg (fun z : ℤ => (z : R)) hez
    simpa only [Int.cast_sub, Int.cast_natCast] using he'
  rw [integerEulerFactor]
  rw [eulerDerivative_mul,
    eulerDerivative_pow_of_log A (-V) hA,
    eulerDerivative_pow_of_log B V hB]
  dsimp [integerEulerLogTerm, V, B, A]
  -- The two natural exponents differ by the original integer exponent.
  have hC : C (e.toNat : R) - C ((-e).toNat : R) = C (e : R) := by
    rw [← map_sub, he]
  -- `ring` uses the common factor and the equality of the two exponent casts.
  calc
    _ = (A ^ e.toNat * B ^ (-e).toNat) *
        (-(C (e.toNat : R) - C ((-e).toNat : R)) * V) := by ring
    _ = _ := by rw [hC]; dsimp [integerEulerLogTerm, V, B, A]; ring

/-- The finite product has the sum of its factor logarithmic derivatives.
This identity is valid for negative exponents as well as positive ones. -/
theorem eulerDerivative_integerEulerPartialProduct {R : Type*} [CommRing R]
    (e : ℕ → ℤ) (N : ℕ) :
    eulerDerivative (integerEulerPartialProduct (R := R) e N) =
      integerEulerPartialProduct e N *
        ∑ j ∈ Finset.range N, integerEulerLogTerm (j + 1) (e (j + 1)) := by
  induction N with
  | zero => simp [integerEulerPartialProduct]
  | succ N ih =>
    rw [integerEulerPartialProduct_succ, eulerDerivative_mul, ih,
      eulerDerivative_integerEulerFactor (N + 1) (e (N + 1)) (Nat.succ_pos N),
      Finset.sum_range_succ]
    ring

/-- Every finite stage has constant coefficient one. -/
theorem integerEulerPartialProduct_constantCoeff {R : Type*} [CommRing R]
    (e : ℕ → ℤ) (N : ℕ) :
    constantCoeff (integerEulerPartialProduct (R := R) e N) = 1 := by
  induction N with
  | zero => simp [integerEulerPartialProduct]
  | succ N ih =>
    rw [integerEulerPartialProduct_succ, map_mul, ih]
    have hfactor := integerEulerFactor_coeff_below (R := R)
      (N + 1) 0 (e (N + 1)) (Nat.succ_pos N) (Nat.succ_pos N)
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply] at hfactor
    simpa using hfactor

/-- The empty degree-zero stage gives the normalized constant term. -/
theorem integerEulerProduct_coeff_zero {R : Type*} [CommRing R]
    (e : ℕ → ℤ) : (integerEulerProduct (R := R) e).coeff 0 = 1 := by
  simp [integerEulerProduct, integerEulerPartialProduct]

/-- The formal logarithmic derivative, assembled degree by degree from the
finitely many Euler factors that can affect that degree. -/
noncomputable def integerEulerLogarithmicSeries {R : Type*} [CommRing R]
    (e : ℕ → ℤ) : PowerSeries R :=
  PowerSeries.mk fun n =>
    (∑ j ∈ Finset.range n, integerEulerLogTerm (R := R) (j + 1) (e (j + 1))).coeff n

private theorem integerEulerLogTerm_coeff_below {R : Type*} [CommRing R]
    (m k : ℕ) (e : ℤ) (hm : 0 < m) (hk : k < m) :
    (integerEulerLogTerm (R := R) m e).coeff k = 0 := by
  by_cases hk0 : k = 0
  · subst k
    exact integerEulerLogTerm_coeff_zero m e hm
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hnot : ¬m ∣ k := by
      intro hdiv
      exact (Nat.not_le_of_gt hk) (Nat.le_of_dvd hkpos hdiv)
    rw [coeff_integerEulerLogTerm m k e hm hkpos]
    simp [hnot]

/-- Adding Euler factors of index greater than `n` does not change degree
`n` of their logarithmic derivative. -/
theorem coeff_integerEulerLogarithmicSeries {R : Type*} [CommRing R]
    (e : ℕ → ℤ) (n N : ℕ) (hN : n ≤ N) :
    (integerEulerLogarithmicSeries (R := R) e).coeff n =
      (∑ j ∈ Finset.range N,
        integerEulerLogTerm (R := R) (j + 1) (e (j + 1))).coeff n := by
  simp only [integerEulerLogarithmicSeries, PowerSeries.coeff_mk]
  induction N, hN using Nat.le_induction with
  | base => rfl
  | succ N hN ih =>
    rw [Finset.sum_range_succ, map_add,
      integerEulerLogTerm_coeff_below (N + 1) n (e (N + 1))
        (Nat.succ_pos N) (by omega), add_zero]
    exact ih

/-- The formal Euler product satisfies its logarithmic derivative identity
over any commutative ring, including rings of positive characteristic. -/
theorem eulerDerivative_integerEulerProduct {R : Type*} [CommRing R]
    (e : ℕ → ℤ) :
    eulerDerivative (integerEulerProduct (R := R) e) =
      integerEulerProduct e * integerEulerLogarithmicSeries e := by
  ext n
  have hprod : ∀ k < n + 1,
      (integerEulerProduct (R := R) e).coeff k =
        (integerEulerPartialProduct e n).coeff k := by
    intro k hk
    exact coeff_integerEulerProduct e k n (by omega)
  have hlog : ∀ k < n + 1,
      (integerEulerLogarithmicSeries (R := R) e).coeff k =
        (∑ j ∈ Finset.range n,
          integerEulerLogTerm (R := R) (j + 1) (e (j + 1))).coeff k := by
    intro k hk
    exact coeff_integerEulerLogarithmicSeries e k n (by omega)
  calc
    (eulerDerivative (integerEulerProduct e)).coeff n =
        (eulerDerivative (integerEulerPartialProduct e n)).coeff n := by
      simp only [coeff_eulerDerivative, hprod n (by omega)]
    _ = (integerEulerPartialProduct (R := R) e n *
        ∑ j ∈ Finset.range n,
          integerEulerLogTerm (R := R) (j + 1) (e (j + 1))).coeff n := by
      rw [eulerDerivative_integerEulerPartialProduct]
    _ = (integerEulerProduct (R := R) e * integerEulerLogarithmicSeries e).coeff n :=
      (coeff_mul_of_coeff_eq_below _ _ _ _ (n + 1) n (by omega)
        hprod hlog).symm
  rfl

/-- The normalized product is a unit, so the preceding identity is the
literal logarithmic quotient `Theta(P)/P`. -/
theorem eulerDerivative_integerEulerProduct_mul_inv {R : Type*} [CommRing R]
    (e : ℕ → ℤ) :
    eulerDerivative (integerEulerProduct (R := R) e) *
        (integerEulerProduct e).invOfUnit 1 =
      integerEulerLogarithmicSeries e := by
  have hc : constantCoeff (integerEulerProduct (R := R) e) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact integerEulerProduct_coeff_zero e
  have hunit : integerEulerProduct (R := R) e *
      (integerEulerProduct e).invOfUnit 1 = 1 :=
    PowerSeries.mul_invOfUnit _ _ hc
  rw [eulerDerivative_integerEulerProduct]
  calc
    integerEulerProduct (R := R) e * integerEulerLogarithmicSeries e *
        (integerEulerProduct e).invOfUnit 1 =
        (integerEulerProduct e * (integerEulerProduct e).invOfUnit 1) *
          integerEulerLogarithmicSeries e := by ring
    _ = integerEulerLogarithmicSeries e := by rw [hunit, one_mul]

private theorem sum_range_succ_of_dvd_eq_sum_divisors {R : Type*} [AddCommMonoid R]
    (f : ℕ → R) (n : ℕ) (hn : 0 < n) :
    (∑ j ∈ Finset.range n, if j + 1 ∣ n then f (j + 1) else 0) =
      ∑ m ∈ n.divisors, f m := by
  classical
  have hfilter :
      (∑ j ∈ Finset.range n, if j + 1 ∣ n then f (j + 1) else 0) =
        ∑ j ∈ (Finset.range n).filter (fun j => j + 1 ∣ n), f (j + 1) := by
    rw [Finset.sum_filter]
  rw [hfilter]
  apply Finset.sum_bij (fun j _ => j + 1)
  · intro j hj
    exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hj).2, by omega⟩
  · intro i j hi hj hij
    omega
  · intro m hm
    have hdiv : m ∣ n := (Nat.mem_divisors.mp hm).1
    have hpos : 0 < m := Nat.pos_of_dvd_of_pos hdiv hn
    have hle : m ≤ n := Nat.le_of_dvd hn hdiv
    refine ⟨m - 1, ?_, by omega⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), by simpa [Nat.sub_add_cancel hpos] using hdiv⟩
  · intro j hj
    rfl

/-- The coefficient of the formal logarithmic derivative is the usual finite
divisor sum, including the vanishing constant coefficient. -/
theorem coeff_integerEulerLogarithmicSeries_divisors {R : Type*} [CommRing R]
    (e : ℕ → ℤ) (n : ℕ) :
    (integerEulerLogarithmicSeries (R := R) e).coeff n =
      -∑ m ∈ n.divisors, (m : R) * (e m : R) := by
  by_cases hn : n = 0
  · subst n
    simp [integerEulerLogarithmicSeries]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  simp only [integerEulerLogarithmicSeries, PowerSeries.coeff_mk, map_sum]
  calc
    (∑ j ∈ Finset.range n,
        (integerEulerLogTerm (R := R) (j + 1) (e (j + 1))).coeff n) =
        ∑ j ∈ Finset.range n,
          if j + 1 ∣ n then -((j + 1 : R) * (e (j + 1) : R)) else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using
        coeff_integerEulerLogTerm (R := R) (j + 1) n (e (j + 1))
          (Nat.succ_pos j) hnpos
    _ = ∑ m ∈ n.divisors, -((m : R) * (e m : R)) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (sum_range_succ_of_dvd_eq_sum_divisors
          (fun m => -((m : R) * (e m : R))) n hnpos)
    _ = -∑ m ∈ n.divisors, (m : R) * (e m : R) := by
      rw [Finset.sum_neg_distrib]

/-- The coefficient formula for the logarithmic derivative of the infinite
integral-exponent product. It includes degree zero, where the divisor sum is
empty and the coefficient vanishes. -/
theorem coeff_eulerDerivative_integerEulerProduct_mul_inv {R : Type*}
    [CommRing R] (e : ℕ → ℤ) (n : ℕ) :
    (eulerDerivative (integerEulerProduct (R := R) e) *
      (integerEulerProduct e).invOfUnit 1).coeff n =
        -∑ m ∈ n.divisors, (m : R) * (e m : R) := by
  rw [eulerDerivative_integerEulerProduct_mul_inv,
    coeff_integerEulerLogarithmicSeries_divisors]

/-- For exponents supplied by the character and integral principal form,
the product's logarithmic derivative is the existing Lambert series. -/
theorem integerEulerLogarithmicSeries_eq_lambert {R : Type*} [CommRing R]
    (h : ℕ → ℤ) :
    integerEulerLogarithmicSeries (R := R)
        (fun m => characterTwelve (m : ℤ) * h (m ^ 2)) =
      logarithmicLambertSeries (fun r => (h r : R)) := by
  ext n
  rw [coeff_integerEulerLogarithmicSeries_divisors]
  rw [coeff_logarithmicLambertSeries, logarithmicLambertCoeff_eq_divisors]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Int.cast_mul]
  ring

/-- Integral Lambert coefficients commute with every change of coefficient
ring. In particular, reduction modulo a prime does not divide by the index. -/
theorem map_integral_logarithmicLambertSeries {R S : Type*}
    [CommRing R] [CommRing S] (f : R →+* S) (h : ℕ → ℤ) :
    PowerSeries.map f
        (logarithmicLambertSeries (fun r => (h r : R))) =
      logarithmicLambertSeries (fun r => (h r : S)) := by
  ext n
  simp only [PowerSeries.coeff_map, coeff_logarithmicLambertSeries,
    logarithmicLambertCoeff_eq_divisors, map_neg, map_sum,
    map_mul, map_natCast, map_intCast]

end SptClassification.QSeries
