/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.HeckePrincipalParts

/-!
# Reduction of Hecke words on a quadratic-character class

The smallest-parts congruence makes the coefficients of `f` agree with those
of `-24 Θ P` on one character class, including the negative indices. Every
prime in a Hecke word coprime to the modulus preserves that class. This is the
coefficient algebra needed before the analytic constant-term argument in
[rolenManuscript], Section 3.
-/

public section

namespace SptClassification.QSeries

/-- Coefficientwise congruence on a character class survives a word of
square-index Hecke operators, with repeated primes kept in the word. -/
theorem squareHeckeWord_congr_on_class {K : Type*} [Semiring K]
    (l : ℕ) [Fact l.Prime] (middle : ℕ → ℤ → K) (last : ℕ → K)
    (ps : List ℕ) (hps : ∀ p ∈ ps, ((p : ℤ) : ZMod l) ≠ 0)
    {A B : ℤ → K} {sign : ℤ}
    (hAB : ∀ r : ℤ, legendreSym l (-r) = sign → A r = B r)
    {r : ℤ} (hr : legendreSym l (-r) = sign) :
    squareHeckeWord middle last ps A r = squareHeckeWord middle last ps B r := by
  induction ps generalizing A B with
  | nil => simpa only [squareHeckeWord_nil] using hAB r hr
  | cons p ps ih =>
    have hp : ((p : ℤ) : ZMod l) ≠ 0 := hps p (by simp)
    have ht : ∀ q ∈ ps, ((q : ℤ) : ZMod l) ≠ 0 :=
      fun q hq => hps q (by simp [hq])
    simpa only [squareHeckeWord_cons] using
      ih ht (fun s hs => squareHecke_congr_on_class l hp
        (middle p) (last p) hAB hs)

/-- The source's congruence for `spt` implies vanishing of every Fourier
coefficient of `S` in the chosen class, including indices outside its support. -/
theorem sptFourier_mod_zero_on_class (l : ℕ) [Fact l.Prime] (sign : ℤ)
    (hspt : ∀ n : ℕ, legendreSym l (1 - 24 * (n : ℤ)) = sign →
      ((spt n : ℤ) : ZMod l) = 0)
    (r : ℤ) (hr : legendreSym l (-r) = sign) :
    (sptFourier r : ZMod l) = 0 := by
  classical
  by_cases h : ∃ n : ℕ, r = 24 * (n : ℤ) - 1
  · obtain ⟨n, hn⟩ := h
    subst r
    rw [sptFourier_at]
    apply hspt n
    convert hr using 1 <;> ring
  · simp [sptFourier, shiftedTwentyFour, h]

/-- On the congruence class, the integral coefficients of `f` agree with
those of `-24 Θ P`, expressed without rational denominators. -/
theorem fFourier_mod_on_class (l : ℕ) [Fact l.Prime] (sign : ℤ)
    (hspt : ∀ n : ℕ, legendreSym l (1 - 24 * (n : ℤ)) = sign →
      ((spt n : ℤ) : ZMod l) = 0)
    (r : ℤ) (hr : legendreSym l (-r) = sign) :
    (fFourier r : ZMod l) =
      ((-r * partitionFourier r : ℤ) : ZMod l) := by
  have hs := sptFourier_mod_zero_on_class l sign hspt r hr
  have h := congrArg (fun x : ℤ => (x : ZMod l)) (fFourier_add_twelve_spt r)
  push_cast at h ⊢
  rw [hs] at h
  linear_combination h

/-- Integral Hecke words commute with reduction modulo a prime. -/
theorem heckeThreeHalfWordInt_mod (l : ℕ) (ps : List ℕ)
    (A : ℤ → ℤ) (r : ℤ) :
    (heckeThreeHalfWordInt ps A r : ZMod l) =
      squareHeckeWord
        (fun p s => (etaHeckeDiagonalInt p s : ZMod l))
        (fun p => (p : ZMod l)) ps (fun s => (A s : ZMod l)) r := by
  have hmap := squareHeckeWord_map (Int.castRingHom (ZMod l))
    etaHeckeDiagonalInt (fun p => (p : ℤ)) ps A r
  have hcast (x : ℤ) : (Int.castRingHom (ZMod l)) x = (x : ZMod l) := rfl
  rw [heckeThreeHalfWordInt_eq_squareHeckeWord]
  simpa only [hcast, Int.cast_natCast] using hmap

/-- The complete repeated-prime word preserves the source congruence on
the chosen class. No modularity claim is used in this coefficient identity. -/
theorem heckeThreeHalfWordInt_mod_on_class (l : ℕ) [Fact l.Prime]
    (sign : ℤ) (ps : List ℕ)
    (hps : ∀ p ∈ ps, ((p : ℤ) : ZMod l) ≠ 0)
    (hspt : ∀ n : ℕ, legendreSym l (1 - 24 * (n : ℤ)) = sign →
      ((spt n : ℤ) : ZMod l) = 0)
    (r : ℤ) (hr : legendreSym l (-r) = sign) :
    (heckeThreeHalfWordInt ps fFourier r : ZMod l) =
      squareHeckeWord
        (fun p s => (etaHeckeDiagonalInt p s : ZMod l))
        (fun p => (p : ZMod l)) ps
        (fun s => ((-s * partitionFourier s : ℤ) : ZMod l)) r := by
  rw [heckeThreeHalfWordInt_mod]
  exact squareHeckeWord_congr_on_class l
    (fun p s => (etaHeckeDiagonalInt p s : ZMod l))
    (fun p => (p : ZMod l)) ps hps
    (fun s hs => fFourier_mod_on_class l sign hspt s hs) hr

/-- An integral coefficient sequence representing `-r m²(P|U_m)(r)`.
The Hecke word is retained, so repeated prime factors receive their actual
successive coefficient action. -/
noncomputable def scaledPartitionHecke (ps : List ℕ) (r : ℤ) : ℤ :=
  heckeThreeHalfWordInt ps (fun s => -s * partitionFourier s) r

/-- The integral lift uses the same repeated-prime Hecke word as the partition row. -/
theorem scaledPartitionHecke_apply (ps : List ℕ) (r : ℤ) :
    scaledPartitionHecke ps r =
      heckeThreeHalfWordInt ps (fun s => -s * partitionFourier s) r := (rfl)

/-- The integral lift agrees over `ℚ` with the weight `-1/2` Hecke word
and its derivative factor. This identity holds at positive as well as
negative indices. -/
theorem scaledPartitionHecke_eq (ps : List ℕ)
    (hps : ∀ p ∈ ps, p.Prime) (r : ℤ) :
    (scaledPartitionHecke ps r : ℚ) =
      -(r : ℚ) * (ps.prod : ℚ) ^ 2 *
        heckeMinusHalfWord ps (fun s => (partitionFourier s : ℚ)) r := by
  have hnonzero : ∀ p ∈ ps, p ≠ 0 :=
    fun p hp => (hps p hp).ne_zero
  have hinput : (fun s : ℤ => ((-s * partitionFourier s : ℤ) : ℚ)) =
      fun s => -24 * thetaCoefficients (fun u => (partitionFourier u : ℚ)) s := by
    funext s
    simp only [thetaCoefficients_apply, Int.cast_mul, Int.cast_neg]
    ring
  rw [scaledPartitionHecke_apply, heckeThreeHalfWordInt_cast, hinput,
    heckeThreeHalfWord_smul, heckeThreeHalfWord_theta ps hnonzero]
  simp only [thetaCoefficients_apply]
  ring

/-- On the source character class, the integral `f` Hecke coefficients
reduce to the integral lift of `-r m²(P|U_m)(r)`. -/
theorem fHecke_mod_eq_scaledPartitionHecke (l : ℕ) [Fact l.Prime]
    (sign : ℤ) (ps : List ℕ)
    (hps : ∀ p ∈ ps, ((p : ℤ) : ZMod l) ≠ 0)
    (hspt : ∀ n : ℕ, legendreSym l (1 - 24 * (n : ℤ)) = sign →
      ((spt n : ℤ) : ZMod l) = 0)
    (r : ℤ) (hr : legendreSym l (-r) = sign) :
    (heckeThreeHalfWordInt ps fFourier r : ZMod l) =
      (scaledPartitionHecke ps r : ZMod l) := by
  rw [heckeThreeHalfWordInt_mod_on_class l sign ps hps hspt r hr]
  exact (heckeThreeHalfWordInt_mod l ps
    (fun s => -s * partitionFourier s) r).symm

end SptClassification.QSeries
