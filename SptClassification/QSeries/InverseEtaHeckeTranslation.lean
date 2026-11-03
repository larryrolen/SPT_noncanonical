/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.AnalyticConstantTerms
public import SptClassification.ModularForms.MeromorphicCuspTranslations
public import SptClassification.ModularForms.EtaTranslation

/-!
# Fourier rows under fractional translations

The character-weighted translation summand of a square-index Hecke operator
acts on each convergent inverse-eta Fourier row by a finite root-of-unity
sum. This analytic identity keeps the pole-clearing factor at each translated
point, so it does not presume the remaining modular Hecke law
[rolenManuscript, §3].
-/

public section

namespace SptClassification.QSeries

open SptClassification

/-- Translation by `24j/n` multiplies the period-one nome by its explicit
phase. -/
theorem qParam_one_fractionTranslate (n j : ℕ) (hn : 0 < n)
    (τ : UpperHalfPlane) :
    Function.Periodic.qParam 1 (cuspFractionTranslate n j hn τ) =
      Function.Periodic.qParam 1 τ *
        Function.Periodic.qParam 1 ((24 * (j : ℂ)) / n) := by
  rw [cuspFractionTranslate_coe, qParam_add_eq_mul]

/-- The period-one phase is the twenty-fourth power of the period-24
phase. -/
theorem qParam_one_fractionPhase (n j : ℕ) (hn : 0 < n) :
    Function.Periodic.qParam 1 ((24 * (j : ℂ)) / n) =
      cuspRoot n j ^ 24 := by
  have h := qParam_twentyFour_fractionTranslate n j hn (0 : ℂ)
  simp only [zero_add] at h
  calc
    Function.Periodic.qParam 1 ((24 * (j : ℂ)) / n) =
        Function.Periodic.qParam 24 ((24 * (j : ℂ)) / n) ^ 24 :=
      (qParam_twentyFour_pow _).symm
    _ = (cuspRoot n j * Function.Periodic.qParam 24 0) ^ 24 :=
      congrArg (· ^ 24) h
    _ = cuspRoot n j ^ 24 := by simp [Function.Periodic.qParam]

/-- For an index prime to six, translation rotates the full pole-clearing
factor by the square-index phase. -/
theorem inverseEtaPoleFactor_fractionTranslate
    (m n j : ℕ) (hn : 0 < n) (hm : m.Coprime 6)
    (τ : UpperHalfPlane) :
    Function.Periodic.qParam 1 (cuspFractionTranslate n j hn τ) ^
        ((m * m) / 24) *
      Function.Periodic.qParam 24 (cuspFractionTranslate n j hn τ) =
    cuspRoot n j ^ (m * m) *
      (Function.Periodic.qParam 1 τ ^ ((m * m) / 24) *
        Function.Periodic.qParam 24 τ) := by
  have hindex : 24 * ((m * m) / 24) + 1 = m * m := by
    have hmod := squareIndex_mod_twentyFour_of_coprime_six m hm
    omega
  rw [qParam_one_fractionTranslate, qParam_one_fractionPhase n j hn,
    cuspFractionTranslate_coe,
    qParam_twentyFour_fractionTranslate n j hn]
  rw [mul_pow, ← pow_mul]
  have hp : cuspRoot n j ^ (24 * ((m * m) / 24)) * cuspRoot n j =
      cuspRoot n j ^ (m * m) := by
    rw [← pow_succ]
    congr 1
  calc
    Function.Periodic.qParam 1 τ ^ ((m * m) / 24) *
        cuspRoot n j ^ (24 * ((m * m) / 24)) *
        (cuspRoot n j * Function.Periodic.qParam 24 τ) =
      (cuspRoot n j ^ (24 * ((m * m) / 24)) * cuspRoot n j) *
        (Function.Periodic.qParam 1 τ ^ ((m * m) / 24) *
          Function.Periodic.qParam 24 τ) := by ring
    _ = _ := by rw [hp]

/-- The finite weighted translation sum of a realized row is itself a
convergent row. Its coefficient multiplier is the exact finite phase sum;
identifying that sum with the Hecke quadratic character is a separate Gauss
sum calculation. -/
theorem InverseEtaFourierForm.hasSum_weightedFractionTranslations
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (n : ℕ) (hn : 0 < n) (w : ℕ → ℂ) (τ : UpperHalfPlane) :
    HasSum (fun k : ℕ =>
      ((A (24 * (k : ℤ) - (m : ℤ) ^ 2) : ℂ) *
        Function.Periodic.qParam 1 τ ^ k) *
      ∑ j ∈ Finset.range n, w j *
        Function.Periodic.qParam 1 ((24 * (j : ℂ)) / n) ^ k)
      (∑ j ∈ Finset.range n, w j *
        (Function.Periodic.qParam 1 (cuspFractionTranslate n j hn τ) ^
            ((m * m) / 24) *
          Function.Periodic.qParam 24 (cuspFractionTranslate n j hn τ) *
          row.form (cuspFractionTranslate n j hn τ))) := by
  have hs := hasSum_sum (s := Finset.range n) (fun j _ =>
    (row.hasSum (cuspFractionTranslate n j hn τ)).mul_left (w j))
  have hterm (j k : ℕ) :
      w j * ((A (24 * (k : ℤ) - (m : ℤ) ^ 2) : ℂ) *
        Function.Periodic.qParam 1 (cuspFractionTranslate n j hn τ) ^ k) =
      ((A (24 * (k : ℤ) - (m : ℤ) ^ 2) : ℂ) *
        Function.Periodic.qParam 1 τ ^ k) *
        (w j * Function.Periodic.qParam 1 ((24 * (j : ℂ)) / n) ^ k) := by
    rw [qParam_one_fractionTranslate, mul_pow]
    ring
  convert hs using 1
  funext k
  rw [Finset.mul_sum]
  exact (Finset.sum_congr rfl fun j _ => hterm j k).symm

/-- Restore the pole phase in a weighted sum of translated inverse-eta
forms. The exponent `24k - m²` is represented by a quotient of two
nonzero root powers, so no choice of an integer root exponent is needed.
This is the Fourier part of the translation summand in the prime Hecke
operator [rolenManuscript, §3]. -/
theorem InverseEtaFourierForm.hasSum_weightedForms
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (hm : m.Coprime 6) (n : ℕ) (hn : 0 < n)
    (w : ℕ → ℂ) (τ : UpperHalfPlane) :
    HasSum (fun k : ℕ =>
      ((A (24 * (k : ℤ) - (m : ℤ) ^ 2) : ℂ) *
        Function.Periodic.qParam 1 τ ^ k) *
      ∑ j ∈ Finset.range n,
        w j * (cuspRoot n j ^ (24 * k) / cuspRoot n j ^ (m * m)))
      (Function.Periodic.qParam 1 τ ^ ((m * m) / 24) *
        Function.Periodic.qParam 24 τ *
        ∑ j ∈ Finset.range n, w j * row.form (cuspFractionTranslate n j hn τ)) := by
  have hs := row.hasSum_weightedFractionTranslations n hn
    (fun j => w j / cuspRoot n j ^ (m * m)) τ
  convert hs using 1
  · funext k
    congr 1
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [qParam_one_fractionPhase n j hn, pow_mul]
    ring
  · let base := Function.Periodic.qParam 1 τ ^ ((m * m) / 24) *
      Function.Periodic.qParam 24 τ
    change base * ∑ j ∈ Finset.range n,
        w j * row.form (cuspFractionTranslate n j hn τ) = _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    have hz : cuspRoot n j ^ (m * m) ≠ 0 := by
      rw [cuspRoot_eq]
      exact pow_ne_zero _ (Complex.exp_ne_zero _)
    rw [inverseEtaPoleFactor_fractionTranslate m n j hn hm τ]
    dsimp [base]
    field_simp

/-- An affine point is a fractional translate of the zero affine point.
This identifies the first Hecke summand with the finite translation row at
the finer cusp parameter. -/
theorem cuspFractionTranslate_affineBase (n j : ℕ) (hn : 0 < n)
    (τ : UpperHalfPlane) :
    cuspFractionTranslate n j hn (cuspAffinePoint n 0 hn τ) =
      cuspAffinePoint n j hn τ := by
  apply UpperHalfPlane.ext
  rw [cuspFractionTranslate_coe, cuspAffinePoint_coe,
    cuspAffinePoint_coe]
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp only [Nat.cast_zero, mul_zero, add_zero]
  field_simp

/-- The affine root average has a convergent Fourier row in the finer
period. Its multiplier is the finite root sum at exponent `24k - m²`;
evaluation of that sum is the separate coefficient-selection step in the
square-index Hecke formula [rolenManuscript, §3]. -/
theorem InverseEtaFourierForm.hasSum_affineRootAverage
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (hm : m.Coprime 6) (n : ℕ) (hn : 0 < n)
    (τ : UpperHalfPlane) :
    HasSum (fun k : ℕ =>
      ((A (24 * (k : ℤ) - (m : ℤ) ^ 2) : ℂ) *
        Function.Periodic.qParam 1 (cuspAffinePoint n 0 hn τ) ^ k) *
      ∑ j ∈ Finset.range n,
        cuspRoot n j ^ (24 * k) / cuspRoot n j ^ (m * m))
      (Function.Periodic.qParam 1 (cuspAffinePoint n 0 hn τ) ^
          ((m * m) / 24) *
        Function.Periodic.qParam 24 (cuspAffinePoint n 0 hn τ) *
        ∑ j ∈ Finset.range n, row.form (cuspAffinePoint n j hn τ)) := by
  simpa only [one_mul, cuspFractionTranslate_affineBase] using
    row.hasSum_weightedForms hm n hn (fun _ => (1 : ℂ))
      (cuspAffinePoint n 0 hn τ)

/-- Dilation raises both nomes to the dilation index. This is the Fourier
row of the third analytic Hecke summand before sparse coefficient reindexing
[rolenManuscript, §3]. -/
theorem InverseEtaFourierForm.hasSum_dilation
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (n : ℕ) (hn : 0 < n) (τ : UpperHalfPlane) :
    HasSum (fun k : ℕ =>
      (A (24 * (k : ℤ) - (m : ℤ) ^ 2) : ℂ) *
        Function.Periodic.qParam 1 τ ^ (n * k))
      (Function.Periodic.qParam 1 τ ^ (n * ((m * m) / 24)) *
        Function.Periodic.qParam 24 τ ^ n *
        row.form (natDilation n hn τ)) := by
  have h1 : Function.Periodic.qParam 1 (natDilation n hn τ) =
      Function.Periodic.qParam 1 τ ^ n := by
    rw [natDilation_coe]
    unfold Function.Periodic.qParam
    rw [← Complex.exp_nat_mul]
    congr 1
    norm_num
    ring
  have h24 : Function.Periodic.qParam 24 (natDilation n hn τ) =
      Function.Periodic.qParam 24 τ ^ n := by
    rw [natDilation_coe]
    exact qParam_twentyFour_nat_mul n τ
  simpa only [h1, h24, pow_mul] using row.hasSum (natDilation n hn τ)

/-- Dilation inserts zero coefficients away from multiples of its index.
The coefficient at `n * k` is the original inverse-eta row at `k`; this
keeps the pole shift `m²` inside the coefficient index. -/
def inverseEtaSparseDilationRow (m n : ℕ) (A : ℤ → ℚ) (k : ℕ) : ℚ :=
  if n ∣ k then A (24 * ((k / n : ℕ) : ℤ) - (m : ℤ) ^ 2) else 0

/-- Sparse reindexing of the convergent row after dilation. This includes
the pole coefficient, and requires only positivity of the dilation index. -/
theorem InverseEtaFourierForm.hasSum_sparseDilation
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (n : ℕ) (hn : 0 < n) (τ : UpperHalfPlane) :
    HasSum (fun k : ℕ =>
      (inverseEtaSparseDilationRow m n A k : ℂ) *
        Function.Periodic.qParam 1 τ ^ k)
      (Function.Periodic.qParam 1 τ ^ (n * ((m * m) / 24)) *
        Function.Periodic.qParam 24 τ ^ n *
        row.form (natDilation n hn τ)) := by
  have hi : Function.Injective (fun k : ℕ => n * k) := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_left hn hab
  have hz : ∀ k, k ∉ Set.range (fun j : ℕ => n * j) →
      (inverseEtaSparseDilationRow m n A k : ℂ) *
        Function.Periodic.qParam 1 τ ^ k = 0 := by
    intro k hk
    have hndiv : ¬ n ∣ k := by
      rintro ⟨j, rfl⟩
      exact hk ⟨j, rfl⟩
    simp [inverseEtaSparseDilationRow, hndiv]
  apply (hi.hasSum_iff hz).mp
  have hterm (k : ℕ) :
      (inverseEtaSparseDilationRow m n A (n * k) : ℂ) *
          Function.Periodic.qParam 1 τ ^ (n * k) =
        (A (24 * (k : ℤ) - (m : ℤ) ^ 2) : ℂ) *
          Function.Periodic.qParam 1 τ ^ (n * k) := by
    have hdiv : n * k / n = k := by
      rw [mul_comm n k]
      exact Nat.mul_div_cancel _ hn
    simp [inverseEtaSparseDilationRow, hdiv]
  simpa only [Function.comp_def, hterm] using row.hasSum_dilation n hn τ

/-- The sparse Fourier row of an `n²` dilation is exactly the downward
square-index Hecke coefficient at the new pole index. Coprimality with six
allows cancellation of the factor `24` in the divisibility test. -/
theorem inverseEtaSparseDilationRow_eq_squareDown
    (m n k : ℕ) (hn : 0 < n) (hc : n.Coprime 6) (A : ℤ → ℚ) :
    inverseEtaSparseDilationRow m (n * n) A k =
      squareDown n A (24 * (k : ℤ) - (m * n : ℤ) ^ 2) := by
  have hc2 : n.Coprime 2 :=
    Nat.Coprime.of_dvd_right (by decide : 2 ∣ 6) hc
  have hc4 : n.Coprime 4 := by
    convert hc2.pow_right 2 using 1
  have hc24 : n.Coprime 24 := by
    convert hc.mul_right hc4 using 1
  have hcSq : (n * n).Coprime 24 := by
    simpa only [pow_two] using hc24.pow_left 2
  have hden : (n : ℤ) ^ 2 = ((n * n : ℕ) : ℤ) := by push_cast; ring
  have hsq : (m * n : ℤ) ^ 2 = ((n * n : ℕ) : ℤ) * (m : ℤ) ^ 2 := by
    push_cast
    ring
  have hdiv : ((n * n : ℕ) : ℤ) ∣ 24 * (k : ℤ) - (m * n : ℤ) ^ 2 ↔
      n * n ∣ k := by
    rw [hsq]
    constructor
    · intro h
      have hd : ((n * n : ℕ) : ℤ) ∣ 24 * (k : ℤ) := by
        convert dvd_add h (dvd_mul_right ((n * n : ℕ) : ℤ) ((m : ℤ) ^ 2))
          using 1 <;> ring
      have hdNat : n * n ∣ 24 * k := by exact_mod_cast hd
      exact hcSq.dvd_mul_left.mp hdNat
    · intro h
      have hdNat : n * n ∣ 24 * k := dvd_mul_of_dvd_right h 24
      have hd : ((n * n : ℕ) : ℤ) ∣ 24 * (k : ℤ) := by
        exact_mod_cast hdNat
      exact dvd_sub hd (dvd_mul_right _ _)
  rw [inverseEtaSparseDilationRow, squareDown_apply, hden]
  by_cases hk : n * n ∣ k
  · rw [if_pos hk, if_pos (hdiv.mpr hk)]
    obtain ⟨q, hq⟩ := hk
    have hnSq : 0 < n * n := Nat.mul_pos hn hn
    have hquotNat : k / (n * n) = q := by
      rw [hq, mul_comm]
      exact Nat.mul_div_cancel _ hnSq
    have hquotInt :
        (24 * (k : ℤ) - (m * n : ℤ) ^ 2) / ((n * n : ℕ) : ℤ) =
          24 * (q : ℤ) - (m : ℤ) ^ 2 := by
      have hnonzero : ((n * n : ℕ) : ℤ) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt hnSq
      apply mul_right_cancel₀ hnonzero
      rw [Int.ediv_mul_cancel (hdiv.mpr ⟨q, hq⟩)]
      rw [hq, hsq]
      push_cast
      ring
    rw [hquotNat, hquotInt]
  · rw [if_neg hk, if_neg (mt hdiv.mp hk)]

/-- Finite Fourier transform of a weight on the fractional cusp orbit. The
index is an integer because inverse-eta Fourier rows include a negative pole
index. -/
noncomputable def cuspRootFourierTransform (n : ℕ) (w : ℕ → ℂ) (r : ℤ) : ℂ :=
  ∑ j ∈ Finset.range n, w j * cuspRoot n j ^ r

/-- The defining finite sum of the signed cusp-orbit transform. -/
theorem cuspRootFourierTransform_eq_sum (n : ℕ) (w : ℕ → ℂ) (r : ℤ) :
    cuspRootFourierTransform n w r =
      ∑ j ∈ Finset.range n, w j * cuspRoot n j ^ r := (rfl)

/-- The quotient of root powers in a translated inverse-eta row is the
phase at its signed Fourier index. -/
theorem cuspRoot_pow_div_pow_eq_zpow (n j a b : ℕ) :
    cuspRoot n j ^ a / cuspRoot n j ^ b =
      cuspRoot n j ^ ((a : ℤ) - b) := by
  have hz : cuspRoot n j ≠ 0 := by
    rw [cuspRoot_eq]
    exact Complex.exp_ne_zero _
  rw [zpow_sub₀ hz]
  simp only [zpow_natCast]

/-- The middle Hecke multiplier is the finite Fourier transform evaluated
at the actual signed coefficient index `24k - m²`. -/
theorem cuspRoot_middleMultiplier_eq_fourierTransform
    (n m k : ℕ) (w : ℕ → ℂ) :
    (∑ j ∈ Finset.range n,
      w j * (cuspRoot n j ^ (24 * k) / cuspRoot n j ^ (m * m))) =
      cuspRootFourierTransform n w (24 * (k : ℤ) - (m : ℤ) ^ 2) := by
  unfold cuspRootFourierTransform
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [cuspRoot_pow_div_pow_eq_zpow]
  congr 1
  push_cast
  ring_nf

/-- The finite character-weighted translation summand in the analytic
square-index expression has the exact convergent Fourier row with its
unevaluated Gauss multiplier [rolenManuscript, §3, Hecke formula]. -/
theorem InverseEtaFourierForm.hasSum_squareIndexAnalyticMiddlePart
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (hm : m.Coprime 6) (n : ℕ) (hn : 0 < n)
    (w : ℕ → ℂ) (τ : UpperHalfPlane) :
    HasSum (fun k : ℕ =>
      ((A (24 * (k : ℤ) - (m : ℤ) ^ 2) : ℂ) *
        Function.Periodic.qParam 1 τ ^ k) *
      ∑ j ∈ Finset.range n,
        w j * (cuspRoot n j ^ (24 * k) / cuspRoot n j ^ (m * m)))
      (Function.Periodic.qParam 1 τ ^ ((m * m) / 24) *
        Function.Periodic.qParam 24 τ *
        squareIndexAnalyticSum row.form n hn w 0 1 0 τ) := by
  simpa only [squareIndexAnalyticSum_eq, zero_mul, zero_add, add_zero,
    one_mul] using row.hasSum_weightedForms hm n hn w τ

/-- The middle analytic Hecke summand has the signed-index finite Fourier
transform as its coefficient multiplier. Its quadratic Gauss value remains
to be established for each prime. -/
theorem InverseEtaFourierForm.hasSum_squareIndexAnalyticMiddleTransform
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (hm : m.Coprime 6) (n : ℕ) (hn : 0 < n)
    (w : ℕ → ℂ) (τ : UpperHalfPlane) :
    HasSum (fun k : ℕ =>
      ((A (24 * (k : ℤ) - (m : ℤ) ^ 2) : ℂ) *
        Function.Periodic.qParam 1 τ ^ k) *
      cuspRootFourierTransform n w (24 * (k : ℤ) - (m : ℤ) ^ 2))
      (Function.Periodic.qParam 1 τ ^ ((m * m) / 24) *
        Function.Periodic.qParam 24 τ *
        squareIndexAnalyticSum row.form n hn w 0 1 0 τ) := by
  convert row.hasSum_squareIndexAnalyticMiddlePart hm n hn w τ using 1
  funext k
  rw [cuspRoot_middleMultiplier_eq_fourierTransform]

/-- The dilation summand in the analytic square-index expression has the
sparse coefficient row at multiples of `n²`. The remaining change from its
pole-clearing factor to the target `(mn)²` factor is separate. -/
theorem InverseEtaFourierForm.hasSum_squareIndexAnalyticDilationPart
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (n : ℕ) (hn : 0 < n) (τ : UpperHalfPlane) :
    HasSum (fun k : ℕ =>
      (inverseEtaSparseDilationRow m (n * n) A k : ℂ) *
        Function.Periodic.qParam 1 τ ^ k)
      (Function.Periodic.qParam 1 τ ^ ((n * n) * ((m * m) / 24)) *
        Function.Periodic.qParam 24 τ ^ (n * n) *
        squareIndexAnalyticSum row.form n hn (fun _ => 0) 0 0 1 τ) := by
  simpa only [squareIndexAnalyticSum_eq, zero_mul, zero_add, add_zero,
    one_mul] using row.hasSum_sparseDilation (n * n)
      (Nat.mul_pos hn hn) τ

/-- When both square indices are one modulo twenty-four, the pole factor
of the `n²` dilation is exactly the pole factor for index `mn`. This is
the normalization required to read the dilation summand as a row of the
next Hecke word. -/
theorem inverseEtaSquareDilationPoleFactor
    (m n : ℕ) (hm : m.Coprime 6) (hn : n.Coprime 6)
    (τ : UpperHalfPlane) :
    Function.Periodic.qParam 1 τ ^
        ((n * n) * ((m * m) / 24)) *
      Function.Periodic.qParam 24 τ ^ (n * n) =
    Function.Periodic.qParam 1 τ ^
        (((m * n) * (m * n)) / 24) *
      Function.Periodic.qParam 24 τ := by
  let a := (m * m) / 24
  let b := (n * n) / 24
  have hma : m * m = 24 * a + 1 := by
    have hmod := squareIndex_mod_twentyFour_of_coprime_six m hm
    dsimp [a]
    omega
  have hnb : n * n = 24 * b + 1 := by
    have hmod := squareIndex_mod_twentyFour_of_coprime_six n hn
    dsimp [b]
    omega
  have hproduct : (m * n) * (m * n) =
      24 * ((n * n) * a + b) + 1 := by
    calc
      (m * n) * (m * n) = (m * m) * (n * n) := by ring
      _ = (24 * a + 1) * (n * n) := by rw [hma]
      _ = 24 * ((n * n) * a + b) + 1 := by rw [hnb]; ring
  have hquot : ((m * n) * (m * n)) / 24 = (n * n) * a + b := by
    omega
  have hq24 : Function.Periodic.qParam 24 τ ^ (n * n) =
      Function.Periodic.qParam 1 τ ^ b *
        Function.Periodic.qParam 24 τ := by
    rw [hnb, pow_add, pow_mul, pow_one, qParam_twentyFour_pow]
  calc
    Function.Periodic.qParam 1 τ ^ ((n * n) * ((m * m) / 24)) *
        Function.Periodic.qParam 24 τ ^ (n * n) =
      Function.Periodic.qParam 1 τ ^ ((n * n) * a) *
        (Function.Periodic.qParam 1 τ ^ b *
          Function.Periodic.qParam 24 τ) := by rw [hq24]
    _ = Function.Periodic.qParam 1 τ ^ ((n * n) * a + b) *
          Function.Periodic.qParam 24 τ := by rw [pow_add]; ring
    _ = _ := by rw [hquot]

/-- The sparse dilation row has the target pole normalization for Hecke
index `mn`, including repeated prime factors. -/
theorem InverseEtaFourierForm.hasSum_normalizedSquareDilation
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (hm : m.Coprime 6) (n : ℕ) (hn : 0 < n) (hc : n.Coprime 6)
    (τ : UpperHalfPlane) :
    HasSum (fun k : ℕ =>
      (inverseEtaSparseDilationRow m (n * n) A k : ℂ) *
        Function.Periodic.qParam 1 τ ^ k)
      (Function.Periodic.qParam 1 τ ^
          (((m * n) * (m * n)) / 24) *
        Function.Periodic.qParam 24 τ *
        row.form (natDilation (n * n) (Nat.mul_pos hn hn) τ)) := by
  simpa only [inverseEtaSquareDilationPoleFactor m n hm hc τ] using
    row.hasSum_sparseDilation (n * n) (Nat.mul_pos hn hn) τ

/-- The normalized dilation summand realizes the downward coefficient of
the `n²` Hecke step at every Fourier index. The pole index is `(mn)²`, and
the coefficient identity holds for arbitrary indices `n` prime to six. -/
theorem InverseEtaFourierForm.hasSum_squareDownDilation
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (hm : m.Coprime 6) (n : ℕ) (hn : 0 < n) (hc : n.Coprime 6)
    (τ : UpperHalfPlane) :
    HasSum (fun k : ℕ =>
      (((squareDown n A (24 * (k : ℤ) - (m * n : ℤ) ^ 2) : ℚ) : ℂ)) *
        Function.Periodic.qParam 1 τ ^ k)
      (Function.Periodic.qParam 1 τ ^
          (((m * n) * (m * n)) / 24) *
        Function.Periodic.qParam 24 τ *
        row.form (natDilation (n * n) (Nat.mul_pos hn hn) τ)) := by
  convert row.hasSum_normalizedSquareDilation hm n hn hc τ using 1
  funext k
  rw [inverseEtaSparseDilationRow_eq_squareDown m n k hn hc A]

private theorem geometricSum_shift (z : ℂ) (n : ℕ) :
    z * (∑ j ∈ Finset.range n, z ^ j) + 1 =
      (∑ j ∈ Finset.range n, z ^ j) + z ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ]
    calc
      z * ((∑ j ∈ Finset.range n, z ^ j) + z ^ n) + 1 =
          (z * (∑ j ∈ Finset.range n, z ^ j) + 1) + z ^ (n + 1) := by
        rw [pow_succ]
        ring
      _ = ((∑ j ∈ Finset.range n, z ^ j) + z ^ n) + z ^ (n + 1) := by
        rw [ih]

private theorem geometricSum_eq_zero (z : ℂ) (n : ℕ)
    (hz : z ≠ 1) (hzn : z ^ n = 1) :
    ∑ j ∈ Finset.range n, z ^ j = 0 := by
  let S := ∑ j ∈ Finset.range n, z ^ j
  have hshift := geometricSum_shift z n
  rw [hzn] at hshift
  have heq : z * S = S := add_right_cancel hshift
  have hzero : (z - 1) * S = 0 := by
    calc
      (z - 1) * S = z * S - S := by ring
      _ = 0 := sub_eq_zero.mpr heq
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hz)

/-- The cusp root at `j` is the `j`th power of the basic root. -/
theorem cuspRoot_eq_pow (n j : ℕ) :
    cuspRoot n j = cuspRoot n 1 ^ j := by
  rw [cuspRoot_eq, cuspRoot_eq, ← Complex.exp_nat_mul]
  congr 1
  ring

/-- The basic cusp root has order dividing `n`. -/
theorem cuspRoot_one_pow (n : ℕ) (hn : 0 < n) :
    cuspRoot n 1 ^ n = 1 := by
  rw [cuspRoot_eq, ← Complex.exp_nat_mul]
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have heq : (n : ℂ) * (2 * Real.pi * Complex.I * (1 : ℂ) / n) =
      2 * Real.pi * Complex.I := by
    field_simp
  simp only [Nat.cast_one] at *
  rw [heq, Complex.exp_two_pi_mul_I]

/-- Every root in the translation orbit has order dividing its length. -/
theorem cuspRoot_pow_order (n j : ℕ) (hn : 0 < n) :
    cuspRoot n j ^ n = 1 := by
  rw [cuspRoot_eq_pow, ← pow_mul, mul_comm j n, pow_mul,
    cuspRoot_one_pow n hn, one_pow]

/-- A cusp root depends only on its residue in the translation orbit. -/
theorem cuspRoot_mod (n j : ℕ) (hn : 0 < n) :
    cuspRoot n (j % n) = cuspRoot n j := by
  calc
    cuspRoot n (j % n) = cuspRoot n 1 ^ (j % n) := cuspRoot_eq_pow n _
    _ =
        cuspRoot n 1 ^ (j % n + n * (j / n)) := by
      rw [pow_add, pow_mul, cuspRoot_one_pow n hn, one_pow, mul_one]
    _ = cuspRoot n 1 ^ j := by rw [Nat.mod_add_div]
    _ = cuspRoot n j := (cuspRoot_eq_pow n j).symm

/-- The signed-index Fourier transform is periodic in its index. This
includes the negative pole indices of inverse-eta rows. -/
theorem cuspRootFourierTransform_add_period
    (n : ℕ) (hn : 0 < n) (w : ℕ → ℂ) (r : ℤ) :
    cuspRootFourierTransform n w (r + n) =
      cuspRootFourierTransform n w r := by
  unfold cuspRootFourierTransform
  apply Finset.sum_congr rfl
  intro j _
  have hz : cuspRoot n j ≠ 0 := by
    rw [cuspRoot_eq]
    exact Complex.exp_ne_zero _
  rw [zpow_add₀ hz, zpow_natCast, cuspRoot_pow_order n j hn, mul_one]

/-- At an index divisible by the orbit length, every signed cusp phase is
one. -/
theorem cuspRoot_zpow_eq_one_of_dvd
    (n j : ℕ) (hn : 0 < n) (r : ℤ) (hr : (n : ℤ) ∣ r) :
    cuspRoot n j ^ r = 1 := by
  obtain ⟨t, rfl⟩ := hr
  rw [zpow_mul, zpow_natCast, cuspRoot_pow_order n j hn, one_zpow]

/-- A signed cusp phase can be evaluated at its nonnegative residue. -/
theorem cuspRoot_zpow_emod (n j : ℕ) (hn : 0 < n) (r : ℤ) :
    cuspRoot n j ^ r = cuspRoot n j ^ (r % n).toNat := by
  have hz : cuspRoot n j ≠ 0 := by
    rw [cuspRoot_eq]
    exact Complex.exp_ne_zero _
  have hnonneg : 0 ≤ r % (n : ℤ) := Int.emod_nonneg _ (by omega)
  have heq : r = ((r % (n : ℤ)).toNat : ℤ) + (n : ℤ) * (r / n) := by
    rw [Int.toNat_of_nonneg hnonneg]
    exact (Int.emod_add_mul_ediv r n).symm
  have horder : cuspRoot n j ^ (n : ℤ) = 1 := by
    rw [zpow_natCast, cuspRoot_pow_order n j hn]
  calc
    cuspRoot n j ^ r =
        cuspRoot n j ^ (((r % (n : ℤ)).toNat : ℤ) +
          (n : ℤ) * (r / n)) := congrArg _ heq
    _ = cuspRoot n j ^ (r % n).toNat := by
      rw [zpow_add₀ hz, zpow_mul, horder, one_zpow,
        mul_one, zpow_natCast]

/-- A signed cusp-orbit Fourier index may be replaced by its nonnegative
residue. -/
theorem cuspRootFourierTransform_emod
    (n : ℕ) (hn : 0 < n) (w : ℕ → ℂ) (r : ℤ) :
    cuspRootFourierTransform n w r =
      cuspRootFourierTransform n w ((r % (n : ℤ)).toNat : ℤ) := by
  unfold cuspRootFourierTransform
  apply Finset.sum_congr rfl
  intro j _
  rw [cuspRoot_zpow_emod n j hn r, zpow_natCast]

/-- The weighted transform at a multiple of its modulus is the total
weight. In particular, the quadratic-character transform vanishes there
once its zero-sum property is supplied. -/
theorem cuspRootFourierTransform_of_dvd
    (n : ℕ) (hn : 0 < n) (w : ℕ → ℂ) (r : ℤ)
    (hr : (n : ℤ) ∣ r) :
    cuspRootFourierTransform n w r = ∑ j ∈ Finset.range n, w j := by
  unfold cuspRootFourierTransform
  apply Finset.sum_congr rfl
  intro j _
  rw [cuspRoot_zpow_eq_one_of_dvd n j hn r hr, mul_one]

/-- The finite affine multiplier is either the size of the root orbit or
zero. The criterion is stated as equality of the basic phase to one; the
arithmetic identification with divisibility of `24k - m²` is separate. -/
theorem cuspRoot_phaseSum (n a b : ℕ) (hn : 0 < n) :
    (∑ j ∈ Finset.range n,
      cuspRoot n j ^ a / cuspRoot n j ^ b) =
      if cuspRoot n 1 ^ a / cuspRoot n 1 ^ b = 1 then (n : ℂ) else 0 := by
  let ζ := cuspRoot n 1
  let z := ζ ^ a / ζ ^ b
  have hterm (j : ℕ) :
      cuspRoot n j ^ a / cuspRoot n j ^ b = z ^ j := by
    rw [cuspRoot_eq_pow]
    dsimp [z, ζ]
    rw [div_pow]
    congr 1 <;> simp only [← pow_mul, mul_comm j]
  have hzpow : z ^ n = 1 := by
    have hζ : ζ ^ n = 1 := cuspRoot_one_pow n hn
    have ha : (ζ ^ a) ^ n = 1 := by
      rw [← pow_mul, mul_comm a n, pow_mul, hζ, one_pow]
    have hb : (ζ ^ b) ^ n = 1 := by
      rw [← pow_mul, mul_comm b n, pow_mul, hζ, one_pow]
    simp only [z, div_pow, ha, hb, div_self (one_ne_zero : (1 : ℂ) ≠ 0)]
  have hsum : (∑ j ∈ Finset.range n,
      cuspRoot n j ^ a / cuspRoot n j ^ b) =
      ∑ j ∈ Finset.range n, z ^ j :=
    Finset.sum_congr rfl (fun j _ => hterm j)
  rw [hsum]
  change (∑ j ∈ Finset.range n, z ^ j) = if z = 1 then (n : ℂ) else 0
  by_cases hz : z = 1
  · rw [if_pos hz, hz]
    simp
  · rw [if_neg hz, geometricSum_eq_zero z n hz hzpow]

/-- The basic phase is one precisely when the root-average index divides
the difference of the two exponents. This identifies the arithmetic selector
behind the first square-index Hecke summand [rolenManuscript, §3]. -/
theorem cuspRoot_phase_eq_one_iff_dvd
    (n a b : ℕ) (hn : 0 < n) :
    cuspRoot n 1 ^ a / cuspRoot n 1 ^ b = 1 ↔
      (n : ℤ) ∣ (a : ℤ) - b := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  let scale : ℂ := 2 * Real.pi * Complex.I
  have hs : scale ≠ 0 := by
    dsimp [scale]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  have hphase :
      cuspRoot n 1 ^ a / cuspRoot n 1 ^ b =
        Complex.exp (((((a : ℤ) - b : ℤ) : ℂ) / n) * scale) := by
    rw [cuspRoot_eq, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
      ← Complex.exp_sub]
    congr 1
    dsimp [scale]
    push_cast
    field_simp
  rw [hphase]
  constructor
  · intro h
    obtain ⟨t, ht⟩ := Complex.exp_eq_one_iff.mp h
    have hq : ((((a : ℤ) - b : ℤ) : ℂ) / n) = (t : ℂ) := by
      exact mul_right_cancel₀ hs ht
    have hc : ((((a : ℤ) - b : ℤ) : ℂ)) = (n : ℂ) * t := by
      apply (div_eq_iff hn0).mp at hq
      calc
        _ = (t : ℂ) * n := hq
        _ = (n : ℂ) * t := by ring
    refine ⟨t, ?_⟩
    exact_mod_cast hc
  · rintro ⟨t, ht⟩
    apply Complex.exp_eq_one_iff.mpr
    refine ⟨t, ?_⟩
    have hc : ((((a : ℤ) - b : ℤ) : ℂ)) = (n : ℂ) * t := by
      exact_mod_cast ht
    rw [hc]
    dsimp [scale]
    field_simp

/-- An unweighted finite root average is the exact divisibility selector. -/
theorem cuspRoot_phaseSum_dvd (n a b : ℕ) (hn : 0 < n) :
    (∑ j ∈ Finset.range n,
      cuspRoot n j ^ a / cuspRoot n j ^ b) =
      if (n : ℤ) ∣ (a : ℤ) - b then (n : ℂ) else 0 := by
  rw [cuspRoot_phaseSum n a b hn]
  simp only [cuspRoot_phase_eq_one_iff_dvd n a b hn]

/-- The basic cusp root at a signed Fourier index is one exactly when that
index is divisible by the orbit length. This includes the negative pole
indices of an inverse-eta row. -/
theorem cuspRoot_one_zpow_eq_one_iff_dvd
    (n : ℕ) (hn : 0 < n) (r : ℤ) :
    cuspRoot n 1 ^ r = 1 ↔ (n : ℤ) ∣ r := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  let scale : ℂ := 2 * Real.pi * Complex.I
  have hs : scale ≠ 0 := by
    dsimp [scale]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  have hphase : cuspRoot n 1 ^ r =
      Complex.exp (((r : ℂ) / n) * scale) := by
    rw [cuspRoot_eq, ← Complex.exp_int_mul]
    congr 1
    dsimp [scale]
    push_cast
    field_simp
  rw [hphase]
  constructor
  · intro h
    obtain ⟨t, ht⟩ := Complex.exp_eq_one_iff.mp h
    have hq : ((r : ℂ) / n) = (t : ℂ) := mul_right_cancel₀ hs ht
    have hc : (r : ℂ) = (n : ℂ) * t := by
      apply (div_eq_iff hn0).mp at hq
      calc
        _ = (t : ℂ) * n := hq
        _ = (n : ℂ) * t := by ring
    exact ⟨t, by exact_mod_cast hc⟩
  · rintro ⟨t, ht⟩
    apply Complex.exp_eq_one_iff.mpr
    refine ⟨t, ?_⟩
    have hc : (r : ℂ) = (n : ℂ) * t := by exact_mod_cast ht
    rw [hc]
    dsimp [scale]
    field_simp

/-- Signed root orthogonality for the full cusp orbit. -/
theorem cuspRoot_signedPhaseSum_dvd
    (n : ℕ) (hn : 0 < n) (r : ℤ) :
    (∑ j ∈ Finset.range n, cuspRoot n j ^ r) =
      if (n : ℤ) ∣ r then (n : ℂ) else 0 := by
  let z := cuspRoot n 1 ^ r
  have hterm (j : ℕ) : cuspRoot n j ^ r = z ^ j := by
    rw [cuspRoot_eq, ← Complex.exp_int_mul]
    dsimp [z]
    rw [cuspRoot_eq, ← Complex.exp_int_mul, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hzpow : z ^ n = 1 := by
    dsimp [z]
    rw [cuspRoot_eq, ← Complex.exp_int_mul, ← Complex.exp_nat_mul]
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    have heq : (n : ℂ) * ((r : ℂ) *
        (2 * Real.pi * Complex.I * (1 : ℂ) / n)) =
        (r : ℂ) * (2 * Real.pi * Complex.I) := by field_simp
    simp only [Nat.cast_one] at *
    rw [heq, Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]
  have hsum : (∑ j ∈ Finset.range n, cuspRoot n j ^ r) =
      ∑ j ∈ Finset.range n, z ^ j :=
    Finset.sum_congr rfl (fun j _ => hterm j)
  rw [hsum]
  change (∑ j ∈ Finset.range n, z ^ j) =
    if (n : ℤ) ∣ r then (n : ℂ) else 0
  by_cases hd : (n : ℤ) ∣ r
  · have hz : z = 1 := (cuspRoot_one_zpow_eq_one_iff_dvd n hn r).mpr hd
    rw [if_pos hd, hz]
    simp
  · have hz : z ≠ 1 := mt (cuspRoot_one_zpow_eq_one_iff_dvd n hn r).mp hd
    rw [if_neg hd, geometricSum_eq_zero z n hz hzpow]

/-- The Fourier transform of the constant weight is the signed divisibility
selector, including at the negative inverse-eta pole index. -/
theorem cuspRootFourierTransform_one
    (n : ℕ) (hn : 0 < n) (r : ℤ) :
    cuspRootFourierTransform n (fun _ => 1) r =
      if (n : ℤ) ∣ r then (n : ℂ) else 0 := by
  simpa only [cuspRootFourierTransform, one_mul] using
    cuspRoot_signedPhaseSum_dvd n hn r

/-- The affine square-index multiplier selects precisely the Fourier
indices divisible by the averaging index. -/
theorem cuspRoot_squarePhaseSum_dvd (n m k : ℕ) (hn : 0 < n) :
    (∑ j ∈ Finset.range n,
      cuspRoot n j ^ (24 * k) / cuspRoot n j ^ (m * m)) =
      if (n : ℤ) ∣ 24 * (k : ℤ) - (m : ℤ) ^ 2 then (n : ℂ) else 0 := by
  calc
    (∑ j ∈ Finset.range n,
        cuspRoot n j ^ (24 * k) / cuspRoot n j ^ (m * m)) =
      cuspRootFourierTransform n (fun _ => 1)
        (24 * (k : ℤ) - (m : ℤ) ^ 2) := by
      simpa only [one_mul] using
        cuspRoot_middleMultiplier_eq_fourierTransform n m k (fun _ => 1)
    _ = _ := cuspRootFourierTransform_one n hn _

/-- The affine average of a realized inverse-eta row has the exact
divisibility-selected Fourier coefficients. -/
theorem InverseEtaFourierForm.hasSum_affineRootAverage_selected
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (hm : m.Coprime 6) (n : ℕ) (hn : 0 < n)
    (τ : UpperHalfPlane) :
    HasSum (fun k : ℕ =>
      ((A (24 * (k : ℤ) - (m : ℤ) ^ 2) : ℂ) *
        Function.Periodic.qParam 1 (cuspAffinePoint n 0 hn τ) ^ k) *
      if (n : ℤ) ∣ 24 * (k : ℤ) - (m : ℤ) ^ 2 then (n : ℂ) else 0)
      (Function.Periodic.qParam 1 (cuspAffinePoint n 0 hn τ) ^
          ((m * m) / 24) *
        Function.Periodic.qParam 24 (cuspAffinePoint n 0 hn τ) *
        ∑ j ∈ Finset.range n, row.form (cuspAffinePoint n j hn τ)) := by
  convert row.hasSum_affineRootAverage hm n hn τ using 1
  funext k
  rw [cuspRoot_squarePhaseSum_dvd n m k hn]

/-- Dividing the affine average by its `n²` translates removes the size of
the root orbit. This is the normalized first summand of the square-index
Hecke expression: it retains exactly the rows whose Fourier index is
divisible by `n²` [rolenManuscript, §3, Hecke formula]. -/
theorem InverseEtaFourierForm.hasSum_normalizedSquareIndexAffinePart
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (hm : m.Coprime 6) (n : ℕ) (hn : 0 < n)
    (τ : UpperHalfPlane) :
    HasSum (fun k : ℕ =>
      if ((n * n : ℕ) : ℤ) ∣ 24 * (k : ℤ) - (m : ℤ) ^ 2 then
        (A (24 * (k : ℤ) - (m : ℤ) ^ 2) : ℂ) *
          Function.Periodic.qParam 1
            (cuspAffinePoint (n * n) 0 (Nat.mul_pos hn hn) τ) ^ k
      else 0)
      (Function.Periodic.qParam 1
          (cuspAffinePoint (n * n) 0 (Nat.mul_pos hn hn) τ) ^
            ((m * m) / 24) *
        Function.Periodic.qParam 24
          (cuspAffinePoint (n * n) 0 (Nat.mul_pos hn hn) τ) *
        (((n * n : ℕ) : ℂ)⁻¹ *
          ∑ j ∈ Finset.range (n * n),
            row.form (cuspAffinePoint (n * n) j
              (Nat.mul_pos hn hn) τ))) := by
  have hnn : ((n * n : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.mul_pos hn hn)
  have hs :=
    (row.hasSum_affineRootAverage_selected hm (n * n)
      (Nat.mul_pos hn hn) τ).mul_left (((n * n : ℕ) : ℂ)⁻¹)
  convert hs using 1
  · funext k
    by_cases hdiv : ((n * n : ℕ) : ℤ) ∣
        24 * (k : ℤ) - (m : ℤ) ^ 2
    · simp only [if_pos hdiv]
      field_simp
    · simp only [if_neg hdiv, mul_zero, zero_mul]
  · ring

/-- The normalized affine summand in the analytic square-index expression
has the selected Fourier row above. The two other summands are set to zero
here; their coefficients require the quadratic Gauss sum and the dilation
calculation [rolenManuscript, §3, Hecke formula]. -/
theorem InverseEtaFourierForm.hasSum_squareIndexAnalyticAffinePart
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (hm : m.Coprime 6) (n : ℕ) (hn : 0 < n)
    (τ : UpperHalfPlane) :
    HasSum (fun k : ℕ =>
      if ((n * n : ℕ) : ℤ) ∣ 24 * (k : ℤ) - (m : ℤ) ^ 2 then
        (A (24 * (k : ℤ) - (m : ℤ) ^ 2) : ℂ) *
          Function.Periodic.qParam 1
            (cuspAffinePoint (n * n) 0 (Nat.mul_pos hn hn) τ) ^ k
      else 0)
      (Function.Periodic.qParam 1
          (cuspAffinePoint (n * n) 0 (Nat.mul_pos hn hn) τ) ^
            ((m * m) / 24) *
        Function.Periodic.qParam 24
          (cuspAffinePoint (n * n) 0 (Nat.mul_pos hn hn) τ) *
        squareIndexAnalyticSum row.form n hn (fun _ => 0)
          (((n * n : ℕ) : ℂ)⁻¹) 0 0 τ) := by
  simpa only [squareIndexAnalyticSum_eq, zero_mul, add_zero] using
    row.hasSum_normalizedSquareIndexAffinePart hm n hn τ

/-- The shift between the old `m²` pole and the target `(mp)²` pole
in the affine Hecke row. It is integral because `p² ≡ 1 (mod 24)`. -/
def inverseEtaAffinePoleShift (m p : ℕ) : ℕ :=
  m * m * (2 * ((p * p) / 24) + 24 * ((p * p) / 24) ^ 2)

/-- The pole shift is exactly `(m²p⁴ - m²)/24`. -/
theorem inverseEtaAffinePoleShift_spec (m p : ℕ) (hp : p.Coprime 6) :
    24 * inverseEtaAffinePoleShift m p + m * m =
      (m * m) * (p * p) * (p * p) := by
  let b := (p * p) / 24
  have hpmod := squareIndex_mod_twentyFour_of_coprime_six p hp
  have hpdecomp : p * p = 24 * b + 1 := by
    dsimp [b]
    omega
  dsimp [inverseEtaAffinePoleShift]
  change 24 * (m * m * (2 * b + 24 * b ^ 2)) + m * m =
    m * m * (p * p) * (p * p)
  rw [hpdecomp]
  ring

/-- The old signed Fourier index selected by the affine average differs
from the new `(mp)²` index by precisely the pole shift. -/
theorem inverseEtaAffineIndex_add_pole (m p j : ℕ) (hp : p.Coprime 6) :
    (p : ℤ) ^ 2 * (24 * (j : ℤ) - (m * p : ℤ) ^ 2) + (m : ℤ) ^ 2 =
      24 * ((p * p * j : ℕ) : ℤ) -
        24 * (inverseEtaAffinePoleShift m p : ℤ) := by
  have hs := inverseEtaAffinePoleShift_spec m p hp
  have hs' : 24 * (inverseEtaAffinePoleShift m p : ℤ) +
      (m : ℤ) * m = (m : ℤ) * m * ((p : ℤ) * p) * ((p : ℤ) * p) := by
    exact_mod_cast hs
  push_cast
  nlinarith [hs']

/-- If the target row asks for a coefficient before the old pole, the
affine Hecke coefficient is zero. This is the missing finite-prefix case
in reindexing the selected affine average. -/
theorem SquarePoleSupported.affine_zero_before_shift
    {m : ℕ} {A : ℤ → ℚ} (hA : SquarePoleSupported m A)
    (p j : ℕ) (hp : p.Coprime 6)
    (hj : p * p * j < inverseEtaAffinePoleShift m p) :
    A ((p : ℤ) ^ 2 * (24 * (j : ℤ) - (m * p : ℤ) ^ 2)) = 0 := by
  apply hA.apply
  have hi := inverseEtaAffineIndex_add_pole m p j hp
  have hj' : ((p * p * j : ℕ) : ℤ) <
      (inverseEtaAffinePoleShift m p : ℤ) := by exact_mod_cast hj
  omega

/-- At and after the shift, the target affine coefficient is the old
Fourier row at the corresponding nonnegative index. -/
theorem inverseEtaAffineIndex_after_shift
    (m p j : ℕ) (hp : p.Coprime 6)
    (hj : inverseEtaAffinePoleShift m p ≤ p * p * j) :
    (p : ℤ) ^ 2 * (24 * (j : ℤ) - (m * p : ℤ) ^ 2) =
      24 * (((p * p * j - inverseEtaAffinePoleShift m p : ℕ) : ℤ)) -
        (m : ℤ) ^ 2 := by
  have hi := inverseEtaAffineIndex_add_pole m p j hp
  have hsub : ((p * p * j - inverseEtaAffinePoleShift m p : ℕ) : ℤ) =
      ((p * p * j : ℕ) : ℤ) -
        (inverseEtaAffinePoleShift m p : ℤ) := by
    exact Nat.cast_sub hj
  rw [hsub]
  omega

/-- The affine root average selects exactly the old row positions that
become nonnegative positions after the pole shift. This also covers the
case where `p` divides the old pole index `m`. -/
theorem inverseEtaAffineSelected_iff_shift_dvd
    (m p k : ℕ) (hp : p.Coprime 6) :
    (((p * p : ℕ) : ℤ) ∣ 24 * (k : ℤ) - (m : ℤ) ^ 2) ↔
      p * p ∣ k + inverseEtaAffinePoleShift m p := by
  have hp2 : p.Coprime 2 :=
    Nat.Coprime.of_dvd_right (by decide : 2 ∣ 6) hp
  have hp4 : p.Coprime 4 := by
    convert hp2.pow_right 2 using 1
  have hp24 : p.Coprime 24 := by
    convert hp.mul_right hp4 using 1
  have hpSq : (p * p).Coprime 24 := by
    simpa only [pow_two] using hp24.pow_left 2
  have hs := inverseEtaAffinePoleShift_spec m p hp
  have hsZ : 24 * (inverseEtaAffinePoleShift m p : ℤ) +
      (m : ℤ) * m = (m : ℤ) * m * ((p : ℤ) * p) * ((p : ℤ) * p) := by
    exact_mod_cast hs
  have hrel : 24 * (k : ℤ) - (m : ℤ) ^ 2 +
      (m : ℤ) ^ 2 * (p : ℤ) ^ 4 =
      24 * ((k + inverseEtaAffinePoleShift m p : ℕ) : ℤ) := by
    push_cast
    nlinarith [hsZ]
  have hmultiple : ((p * p : ℕ) : ℤ) ∣
      (m : ℤ) ^ 2 * (p : ℤ) ^ 4 := by
    refine ⟨(m : ℤ) ^ 2 * (p : ℤ) ^ 2, ?_⟩
    push_cast
    ring
  constructor
  · intro h
    have hd : ((p * p : ℕ) : ℤ) ∣
        24 * ((k + inverseEtaAffinePoleShift m p : ℕ) : ℤ) := by
      rw [← hrel]
      exact dvd_add h hmultiple
    have hdNat : p * p ∣ 24 * (k + inverseEtaAffinePoleShift m p) := by
      exact_mod_cast hd
    exact hpSq.dvd_mul_left.mp hdNat
  · intro h
    have hdNat : p * p ∣ 24 * (k + inverseEtaAffinePoleShift m p) :=
      dvd_mul_of_dvd_right h 24
    have hd : ((p * p : ℕ) : ℤ) ∣
        24 * ((k + inverseEtaAffinePoleShift m p : ℕ) : ℤ) := by
      exact_mod_cast hdNat
    have hsub := dvd_sub hd hmultiple
    convert hsub using 1 <;> nlinarith [hrel]

/-- A coefficient retained by the affine root average has one target
Fourier index after the pole shift. The index identity uses the full
square-index relation and allows `p ∣ m` [rolenManuscript, §3]. -/
theorem inverseEtaAffineSelected_unique_index
    (m p k : ℕ) (hp : p.Coprime 6) (hp0 : 0 < p)
    (hselected : (((p * p : ℕ) : ℤ) ∣
      24 * (k : ℤ) - (m : ℤ) ^ 2)) :
    ∃! j : ℕ, p * p * j = k + inverseEtaAffinePoleShift m p ∧
      (p : ℤ) ^ 2 * (24 * (j : ℤ) - (m * p : ℤ) ^ 2) =
        24 * (k : ℤ) - (m : ℤ) ^ 2 := by
  obtain ⟨j, hj⟩ :=
    (inverseEtaAffineSelected_iff_shift_dvd m p k hp).mp hselected
  have hindex :
      (p : ℤ) ^ 2 * (24 * (j : ℤ) - (m * p : ℤ) ^ 2) =
        24 * (k : ℤ) - (m : ℤ) ^ 2 := by
    have hshift := inverseEtaAffineIndex_add_pole m p j hp
    rw [← hj] at hshift
    push_cast at hshift
    omega
  refine ⟨j, ⟨hj.symm, hindex⟩, ?_⟩
  intro j' hj'
  apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hp0 hp0)
  calc
    p * p * j' = k + inverseEtaAffinePoleShift m p := hj'.1
    _ = p * p * j := hj

/-- Shift a convergent selected row to its divisible indices. The initial
indices before the shift are zero, and the remaining indices are reindexed
by division. The factor `z ^ s` records the change of pole normalization. -/
theorem hasSum_shifted_dvd (d s : ℕ) (hd : 0 < d)
    (a : ℕ → ℂ) (z L : ℂ)
    (hs : HasSum (fun k : ℕ =>
      if d ∣ k + s then a k * z ^ k else 0) L) :
    HasSum (fun j : ℕ =>
      if s ≤ d * j then a (d * j - s) * z ^ (d * j) else 0)
      (z ^ s * L) := by
  let g : ℕ → ℂ := fun t =>
    if s ≤ t then if d ∣ t then a (t - s) * z ^ t else 0 else 0
  have hshiftInjective : Function.Injective (fun k : ℕ => s + k) := by
    intro x y hxy
    exact Nat.add_left_cancel hxy
  have hshiftZero : ∀ t, t ∉ Set.range (fun k : ℕ => s + k) → g t = 0 := by
    intro t ht
    have hlt : ¬ s ≤ t := by
      intro hle
      apply ht
      refine ⟨t - s, ?_⟩
      change s + (t - s) = t
      exact Nat.add_sub_of_le hle
    simp [g, hlt]
  have hshifted : HasSum g (z ^ s * L) := by
    apply (hshiftInjective.hasSum_iff hshiftZero).mp
    have hterm (k : ℕ) :
        g (s + k) =
          z ^ s * (if d ∣ k + s then a k * z ^ k else 0) := by
      have hle : s ≤ s + k := Nat.le_add_right s k
      have hsub : s + k - s = k := by omega
      dsimp [g]
      rw [if_pos hle, hsub]
      by_cases hdiv : d ∣ k + s
      · rw [if_pos (by simpa [add_comm] using hdiv), if_pos hdiv, pow_add]
        ring
      · rw [if_neg (by simpa [add_comm] using hdiv), if_neg hdiv]
        ring
    simpa only [Function.comp_def, hterm] using hs.mul_left (z ^ s)
  have hmulInjective : Function.Injective (fun j : ℕ => d * j) := by
    intro x y hxy
    exact Nat.eq_of_mul_eq_mul_left hd hxy
  have hmulZero : ∀ t, t ∉ Set.range (fun j : ℕ => d * j) → g t = 0 := by
    intro t ht
    have hndiv : ¬ d ∣ t := by
      rintro ⟨j, hj⟩
      exact ht ⟨j, hj.symm⟩
    by_cases hle : s ≤ t
    · simp [g, hle, hndiv]
    · simp [g, hle]
  have hreindexed := (hmulInjective.hasSum_iff hmulZero).mpr hshifted
  convert hreindexed using 1
  funext j
  by_cases hle : s ≤ d * j
  · simp [g, hle, show d ∣ d * j from ⟨j, rfl⟩]
  · simp [g, hle]

/-- The middle cusp row's pole changes by `m²(p²-1)/24` under a
prime square-index Hecke step. -/
def inverseEtaMiddlePoleShift (m p : ℕ) : ℕ :=
  m * m * ((p * p) / 24)

/-- The middle-row pole shift is exact, also when `p ∣ m`. -/
theorem inverseEtaMiddlePoleShift_spec (m p : ℕ) (hp : p.Coprime 6) :
    24 * inverseEtaMiddlePoleShift m p + m * m =
      (m * p) * (m * p) := by
  let c := (p * p) / 24
  have hpc : p * p = 24 * c + 1 := by
    have hmod := squareIndex_mod_twentyFour_of_coprime_six p hp
    dsimp [c]
    omega
  dsimp [inverseEtaMiddlePoleShift]
  change 24 * (m * m * c) + m * m = (m * p) * (m * p)
  calc
    _ = m * m * (24 * c + 1) := by ring
    _ = m * m * (p * p) := by rw [hpc]
    _ = _ := by ring

/-- The middle row's shifted pole-clearing exponent is the exponent
of the target `(mp)²` Fourier normalization. -/
theorem inverseEtaMiddlePoleShift_exponent (m p : ℕ)
    (hm : m.Coprime 6) (hp : p.Coprime 6) :
    (m * m) / 24 + inverseEtaMiddlePoleShift m p =
      ((m * p) * (m * p)) / 24 := by
  have hma : m * m = 24 * ((m * m) / 24) + 1 := by
    have hmod := squareIndex_mod_twentyFour_of_coprime_six m hm
    omega
  have hs := inverseEtaMiddlePoleShift_spec m p hp
  omega

/-- Shifting the old middle row keeps its signed Fourier index. -/
theorem inverseEtaMiddleIndex_after_shift (m p j : ℕ)
    (hp : p.Coprime 6)
    (hj : inverseEtaMiddlePoleShift m p ≤ j) :
    24 * (j - inverseEtaMiddlePoleShift m p : ℕ) - (m : ℤ) ^ 2 =
      24 * (j : ℤ) - (m * p : ℤ) ^ 2 := by
  have hs := inverseEtaMiddlePoleShift_spec m p hp
  have hsZ : 24 * (inverseEtaMiddlePoleShift m p : ℤ) +
      (m : ℤ) * m = (m * p : ℤ) * (m * p : ℤ) := by
    exact_mod_cast hs
  rw [Nat.cast_sub hj]
  push_cast
  nlinarith [hsZ]

/-- Before the middle-row pole shift, the target coefficient is below
the source row's square pole. -/
theorem SquarePoleSupported.middle_zero_before_shift
    {m : ℕ} {A : ℤ → ℚ} (hA : SquarePoleSupported m A)
    (p j : ℕ) (hp : p.Coprime 6)
    (hj : j < inverseEtaMiddlePoleShift m p) :
    A (24 * (j : ℤ) - (m * p : ℤ) ^ 2) = 0 := by
  apply hA.apply
  have hs := inverseEtaMiddlePoleShift_spec m p hp
  have hsZ : 24 * (inverseEtaMiddlePoleShift m p : ℤ) +
      (m : ℤ) * m = (m * p : ℤ) * (m * p : ℤ) := by
    exact_mod_cast hs
  have hjZ : (j : ℤ) < inverseEtaMiddlePoleShift m p := by
    exact_mod_cast hj
  nlinarith [hsZ]

/-- The affine coefficient, including its initial zero range, is the old
inverse-eta row reindexed by the shift. -/
theorem SquarePoleSupported.affine_coefficient_reindex
    {m : ℕ} {A : ℤ → ℚ} (hA : SquarePoleSupported m A)
    (p j : ℕ) (hp : p.Coprime 6) :
    A ((p : ℤ) ^ 2 * (24 * (j : ℤ) - (m * p : ℤ) ^ 2)) =
      if inverseEtaAffinePoleShift m p ≤ p * p * j then
        A (24 * (((p * p * j - inverseEtaAffinePoleShift m p : ℕ) : ℤ)) -
          (m : ℤ) ^ 2)
      else 0 := by
  split_ifs with hj
  · rw [inverseEtaAffineIndex_after_shift m p j hp hj]
  · exact hA.affine_zero_before_shift p j hp (Nat.lt_of_not_ge hj)

/-- Reindex the convergent affine row at the selected square indices.
The pole support removes the terms before the shifted row begins, so the
result has the full target coefficient at every nonnegative index. -/
theorem SquarePoleSupported.hasSum_affine_selected_reindex
    {m : ℕ} {A : ℤ → ℚ} (hA : SquarePoleSupported m A)
    (p : ℕ) (hp : p.Coprime 6) (hp0 : 0 < p)
    (z L : ℂ)
    (hs : HasSum (fun k : ℕ =>
      if (((p * p : ℕ) : ℤ) ∣ 24 * (k : ℤ) - (m : ℤ) ^ 2) then
        (A (24 * (k : ℤ) - (m : ℤ) ^ 2) : ℂ) * z ^ k
      else 0) L) :
    HasSum (fun j : ℕ =>
      (A ((p : ℤ) ^ 2 * (24 * (j : ℤ) - (m * p : ℤ) ^ 2)) : ℂ) *
        z ^ (p * p * j))
      (z ^ inverseEtaAffinePoleShift m p * L) := by
  have hsShift : HasSum (fun k : ℕ =>
      if p * p ∣ k + inverseEtaAffinePoleShift m p then
        (A (24 * (k : ℤ) - (m : ℤ) ^ 2) : ℂ) * z ^ k
      else 0) L := by
    convert hs using 1
    funext k
    exact if_congr
      (inverseEtaAffineSelected_iff_shift_dvd m p k hp).symm
      rfl rfl
  have hreindexed := hasSum_shifted_dvd (p * p)
    (inverseEtaAffinePoleShift m p) (Nat.mul_pos hp0 hp0)
    (fun k => (A (24 * (k : ℤ) - (m : ℤ) ^ 2) : ℂ)) z L hsShift
  convert hreindexed using 1
  funext j
  rw [hA.affine_coefficient_reindex p j hp]
  split_ifs <;> simp

/-- The nome at the zero affine translate is a chosen `n`th root of the
original nome. -/
theorem qParam_one_affineZero_pow (n : ℕ) (hn : 0 < n)
    (τ : UpperHalfPlane) :
    Function.Periodic.qParam 1 (cuspAffinePoint n 0 hn τ) ^ n =
      Function.Periodic.qParam 1 τ := by
  rw [cuspAffinePoint_coe]
  simp only [Nat.cast_zero, mul_zero, add_zero]
  unfold Function.Periodic.qParam
  rw [← Complex.exp_nat_mul]
  congr 1
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  norm_num
  field_simp

/-- The affine pole factor descends when the two square-index exponents
match after scaling by the affine denominator. -/
theorem qParam_affineZero_poleFactor (n a b : ℕ) (hn : 0 < n)
    (hab : 24 * a + 1 = n * (24 * b + 1))
    (τ : UpperHalfPlane) :
    Function.Periodic.qParam 1 (cuspAffinePoint n 0 hn τ) ^ a *
      Function.Periodic.qParam 24 (cuspAffinePoint n 0 hn τ) =
    Function.Periodic.qParam 1 τ ^ b *
      Function.Periodic.qParam 24 τ := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hab' : (24 : ℂ) * a + 1 = (n : ℂ) * ((24 : ℂ) * b + 1) := by
    exact_mod_cast hab
  have hratio : ((a : ℂ) + 1 / 24) / n = (b : ℂ) + 1 / 24 := by
    apply (div_eq_iff hn').mpr
    linear_combination hab' / 24
  rw [cuspAffinePoint_coe]
  simp only [Nat.cast_zero, mul_zero, add_zero]
  unfold Function.Periodic.qParam
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  calc
    (a : ℂ) * (2 * Real.pi * Complex.I * ((τ : ℂ) / n) / 1) +
        2 * Real.pi * Complex.I * ((τ : ℂ) / n) / 24 =
      (2 * Real.pi * Complex.I * (τ : ℂ)) *
        (((a : ℂ) + 1 / 24) / n) := by ring
    _ = (2 * Real.pi * Complex.I * (τ : ℂ)) *
        ((b : ℂ) + 1 / 24) := by rw [hratio]
    _ = (b : ℂ) * (2 * Real.pi * Complex.I * (τ : ℂ) / 1) +
        2 * Real.pi * Complex.I * (τ : ℂ) / 24 := by ring

/-- The affine pole shift changes the old `m²` normalization into the
target `(mp)²` normalization. The fourth power of `p` in the shift is
essential, including when `p` divides `m`. -/
theorem inverseEtaAffinePoleFactor
    (m p : ℕ) (hm : m.Coprime 6) (hp : p.Coprime 6)
    (hp0 : 0 < p) (τ : UpperHalfPlane) :
    Function.Periodic.qParam 1
        (cuspAffinePoint (p * p) 0 (Nat.mul_pos hp0 hp0) τ) ^
          inverseEtaAffinePoleShift m p *
      (Function.Periodic.qParam 1
          (cuspAffinePoint (p * p) 0 (Nat.mul_pos hp0 hp0) τ) ^
            ((m * m) / 24) *
        Function.Periodic.qParam 24
          (cuspAffinePoint (p * p) 0 (Nat.mul_pos hp0 hp0) τ)) =
    Function.Periodic.qParam 1 τ ^ (((m * p) * (m * p)) / 24) *
      Function.Periodic.qParam 24 τ := by
  let a := (m * m) / 24
  let b := ((m * p) * (m * p)) / 24
  let c := (p * p) / 24
  let s := inverseEtaAffinePoleShift m p
  have hma : m * m = 24 * a + 1 := by
    have hmod := squareIndex_mod_twentyFour_of_coprime_six m hm
    dsimp [a]
    omega
  have hpc : p * p = 24 * c + 1 := by
    have hmod := squareIndex_mod_twentyFour_of_coprime_six p hp
    dsimp [c]
    omega
  have hproduct : (m * p) * (m * p) =
      24 * (a + c + 24 * a * c) + 1 := by
    calc
      (m * p) * (m * p) = (m * m) * (p * p) := by ring
      _ = (24 * a + 1) * (24 * c + 1) := by rw [hma, hpc]
      _ = 24 * (a + c + 24 * a * c) + 1 := by ring
  have hmb : (m * p) * (m * p) = 24 * b + 1 := by
    dsimp [b]
    omega
  have hs := inverseEtaAffinePoleShift_spec m p hp
  have hrel : 24 * (s + a) + 1 = (p * p) * (24 * b + 1) := by
    calc
      24 * (s + a) + 1 = 24 * s + m * m := by rw [hma]; ring
      _ = (m * m) * (p * p) * (p * p) := hs
      _ = (p * p) * ((m * p) * (m * p)) := by ring
      _ = (p * p) * (24 * b + 1) := by rw [hmb]
  let z := Function.Periodic.qParam 1
    (cuspAffinePoint (p * p) 0 (Nat.mul_pos hp0 hp0) τ)
  let w := Function.Periodic.qParam 24
    (cuspAffinePoint (p * p) 0 (Nat.mul_pos hp0 hp0) τ)
  change z ^ s * (z ^ a * w) =
    Function.Periodic.qParam 1 τ ^ b * Function.Periodic.qParam 24 τ
  calc
    z ^ s * (z ^ a * w) = z ^ (s + a) * w := by rw [pow_add]; ring
    _ = Function.Periodic.qParam 1 τ ^ b *
        Function.Periodic.qParam 24 τ :=
      qParam_affineZero_poleFactor (p * p) (s + a) b
        (Nat.mul_pos hp0 hp0) hrel τ

/-- The normalized affine Hecke average has the target square-index
Fourier coefficients, with its remaining pole-clearing factor shown
explicitly. -/
theorem InverseEtaFourierForm.hasSum_squareIndexAffineReindexed
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (hm : m.Coprime 6) (p : ℕ) (hp : p.Coprime 6)
    (hp0 : 0 < p) (τ : UpperHalfPlane) :
    HasSum (fun j : ℕ =>
      (A ((p : ℤ) ^ 2 * (24 * (j : ℤ) - (m * p : ℤ) ^ 2)) : ℂ) *
        Function.Periodic.qParam 1 τ ^ j)
      (Function.Periodic.qParam 1
          (cuspAffinePoint (p * p) 0 (Nat.mul_pos hp0 hp0) τ) ^
            inverseEtaAffinePoleShift m p *
        (Function.Periodic.qParam 1
            (cuspAffinePoint (p * p) 0 (Nat.mul_pos hp0 hp0) τ) ^
              ((m * m) / 24) *
          Function.Periodic.qParam 24
            (cuspAffinePoint (p * p) 0 (Nat.mul_pos hp0 hp0) τ) *
          (((p * p : ℕ) : ℂ)⁻¹ *
            ∑ j ∈ Finset.range (p * p),
              row.form (cuspAffinePoint (p * p) j
                (Nat.mul_pos hp0 hp0) τ)))) := by
  have hs := row.support.hasSum_affine_selected_reindex p hp hp0
    (Function.Periodic.qParam 1
      (cuspAffinePoint (p * p) 0 (Nat.mul_pos hp0 hp0) τ)) _
    (row.hasSum_normalizedSquareIndexAffinePart hm p hp0 τ)
  convert hs using 1
  funext j
  rw [pow_mul, qParam_one_affineZero_pow (p * p) (Nat.mul_pos hp0 hp0) τ]

/-- The affine term of the prime square-index Hecke sum has its Fourier row
at the new `(mp)²` pole. This includes the case `p ∣ m` and leaves the
analytic Hecke normalization visible in the finite average. -/
theorem InverseEtaFourierForm.hasSum_squareIndexAffineTarget
    {m : ℕ} {A : ℤ → ℚ} (row : InverseEtaFourierForm m A)
    (hm : m.Coprime 6) (p : ℕ) (hp : p.Coprime 6)
    (hp0 : 0 < p) (τ : UpperHalfPlane) :
    HasSum (fun j : ℕ =>
      (A ((p : ℤ) ^ 2 * (24 * (j : ℤ) - (m * p : ℤ) ^ 2)) : ℂ) *
        Function.Periodic.qParam 1 τ ^ j)
      (Function.Periodic.qParam 1 τ ^ (((m * p) * (m * p)) / 24) *
        Function.Periodic.qParam 24 τ *
        (((p * p : ℕ) : ℂ)⁻¹ *
          ∑ j ∈ Finset.range (p * p),
            row.form (cuspAffinePoint (p * p) j
              (Nat.mul_pos hp0 hp0) τ))) := by
  have hs := row.hasSum_squareIndexAffineReindexed hm p hp hp0 τ
  convert hs using 1
  let E : ℂ := ((p * p : ℕ) : ℂ)⁻¹ *
    ∑ j ∈ Finset.range (p * p),
      row.form (cuspAffinePoint (p * p) j (Nat.mul_pos hp0 hp0) τ)
  have hfactor := congrArg (fun z : ℂ => z * E)
    (inverseEtaAffinePoleFactor m p hm hp hp0 τ)
  simpa only [mul_assoc] using hfactor.symm

end SptClassification.QSeries
