/- Assembled by AxiomProver. -/

module

public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod

/-!
# Laurent series for projected modular progressions

The Fourier variable here is `X = q^(1/M)`.  Coefficients at indices outside
the selected congruence class are zero [rolenManuscript, §2].
-/

public section

namespace SptClassification.QSeries

/-- The actual coefficient row of the projection to `r ≡ u (mod M)` in the
variable `X = q^(1/M)` [rolenManuscript, §2]. -/
def progressionRow {R : Type*} [Zero R] (f : ℤ → R) (M : ℕ) (u : ℤ) (r : ℤ) : R :=
  if (r : ZMod M) = (u : ZMod M) then f r else 0

/-- A projection depends only on the selected residue class. -/
theorem progressionRow_congr {R : Type*} [Zero R]
    (f : ℤ → R) (M : ℕ) (u v : ℤ)
    (huv : (u : ZMod M) = (v : ZMod M)) :
    progressionRow f M u = progressionRow f M v := by
  funext r
  simp only [progressionRow, huv]

theorem progressionRow_eq_of {R : Type*} [Zero R]
    (f : ℤ → R) (M : ℕ) (u r : ℤ)
    (hr : (r : ZMod M) = (u : ZMod M)) :
    progressionRow f M u r = f r := by simp [progressionRow, hr]

theorem progressionRow_eq_zero_of {R : Type*} [Zero R]
    (f : ℤ → R) (M : ℕ) (u r : ℤ)
    (hr : (r : ZMod M) ≠ (u : ZMod M)) :
    progressionRow f M u r = 0 := by simp [progressionRow, hr]

theorem progressionRow_zero_below {R : Type*} [Zero R]
    (f : ℤ → R) (M : ℕ) (u : ℤ)
    (hbelow : ∃ B : ℤ, ∀ r < B, f r = 0) :
    ∃ B : ℤ, ∀ r < B, progressionRow f M u r = 0 := by
  obtain ⟨B, hB⟩ := hbelow
  refine ⟨B, ?_⟩
  intro r hr
  simp [progressionRow, hB r hr]

/-- A bounded-below rational or integral Fourier row is a Laurent series,
without restricting whether the characteristic divides `M`. -/
def progressionLaurent {R : Type*} [Zero R]
    (f : ℤ → R) (M : ℕ) (u : ℤ)
    (hbelow : ∃ B : ℤ, ∀ r < B, f r = 0) : LaurentSeries R :=
  HahnSeries.ofSuppBddBelow (progressionRow f M u) (by
    obtain ⟨B, hB⟩ := progressionRow_zero_below f M u hbelow
    refine ⟨B, ?_⟩
    intro r hr
    have hnot : ¬r < B := by
      intro hlt
      have hz := hB r hlt
      simp only [Function.mem_support] at hr
      exact hr hz
    exact le_of_not_gt hnot)

theorem progressionLaurent_coeff {R : Type*} [Zero R]
    (f : ℤ → R) (M : ℕ) (u : ℤ)
    (hbelow : ∃ B : ℤ, ∀ r < B, f r = 0) (r : ℤ) :
    (progressionLaurent f M u hbelow).coeff r = progressionRow f M u r := by
  rfl

/-- Vanishing of the full masked Fourier row gives the zero Laurent series. -/
theorem progressionLaurent_eq_zero_of_coeff {R : Type*} [AddMonoid R]
    (f : ℤ → R) (M : ℕ) (u : ℤ)
    (hbelow : ∃ B : ℤ, ∀ r < B, f r = 0)
    (hzero : ∀ r : ℤ, (r : ZMod M) = (u : ZMod M) → f r = 0) :
    progressionLaurent f M u hbelow = 0 := by
  apply HahnSeries.ext
  funext r
  simp only [progressionLaurent_coeff, progressionRow]
  split_ifs with hr
  · simp [hzero r hr]
  · simp

/-- The Laurent-series formulation retains every coefficient of the projected
progression, including negative Fourier indices. -/
theorem progressionLaurent_coeff_eq_zero_of_eq_zero {R : Type*} [AddMonoid R]
    (f : ℤ → R) (M : ℕ) (u : ℤ)
    (hbelow : ∃ B : ℤ, ∀ r < B, f r = 0)
    (hzero : progressionLaurent f M u hbelow = 0)
    (r : ℤ) (hr : (r : ZMod M) = (u : ZMod M)) : f r = 0 := by
  have hcoeff := congrArg (fun s : LaurentSeries R => s.coeff r) hzero
  simpa [progressionLaurent_coeff, progressionRow, hr] using hcoeff

/-- Coefficientwise reduction of a Laurent series is coefficientwise reduction
of its full Fourier row. -/
theorem laurent_map_coeff {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (F : LaurentSeries R) (r : ℤ) :
    (F.map φ).coeff r = φ (F.coeff r) := by
  rfl

/-- Coefficientwise reduction commutes with taking the masked row. -/
theorem progressionLaurent_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (f : ℤ → R) (M : ℕ) (u : ℤ)
    (hbelow : ∃ B : ℤ, ∀ r < B, f r = 0) :
    (progressionLaurent f M u hbelow).map φ =
      progressionLaurent (fun r => φ (f r)) M u
        (by obtain ⟨B, hB⟩ := hbelow
            exact ⟨B, fun r hr => by simp [hB r hr]⟩) := by
  apply HahnSeries.ext
  funext r
  simp only [laurent_map_coeff, progressionLaurent_coeff, progressionRow]
  split_ifs <;> simp

/-- Coefficientwise maps preserve powers of Laurent series. -/
theorem laurent_map_pow {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (F : LaurentSeries R) (n : ℕ) :
    (F ^ n).map φ = (F.map φ) ^ n := by
  induction n with
  | zero =>
      change (1 : LaurentSeries R).map φ.toMonoidWithZeroHom = 1
      exact HahnSeries.map_one φ.toMonoidWithZeroHom
  | succ n ih =>
      simp only [pow_succ]
      change (F ^ n * F).map φ.toNonUnitalRingHom =
        (F.map φ) ^ n * F.map φ
      rw [HahnSeries.map_mul φ.toNonUnitalRingHom]
      change (F ^ n).map φ * F.map φ =
        (F.map φ) ^ n * F.map φ
      rw [ih]

/-- Coefficientwise maps commute with Laurent multiplication. -/
theorem laurent_map_mul {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (F G : LaurentSeries R) :
    (F * G).map φ = F.map φ * G.map φ := by
  change (F * G).map φ.toNonUnitalRingHom = F.map φ * G.map φ
  exact HahnSeries.map_mul φ.toNonUnitalRingHom

/-- Scalar multiplication by a coefficient maps to scalar multiplication by
its image. -/
theorem laurent_map_smul {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (a : R) (F : LaurentSeries R) :
    (a • F).map φ = φ a • F.map φ := by
  apply HahnSeries.ext
  funext r
  change φ (a * F.coeff r) = φ a * φ (F.coeff r)
  exact map_mul φ a (F.coeff r)

/-- Coefficientwise vanishing modulo a prime gives divisibility of the entire
bounded-below Laurent row.  The kernel description is the usual local-ring
fact `ker (A → 𝔽ₚ) = pA`; no condition on the Fourier modulus occurs. -/
theorem laurent_divisible_of_reduction_zero {A : Type*} [CommRing A]
    (p : ℕ) (red : A →+* ZMod p)
    (hker : ∀ x : A, red x = 0 → ∃ y : A, x = (p : A) * y)
    (f : ℤ → A) (hbelow : ∃ B : ℤ, ∀ r < B, f r = 0)
    (hzero : ∀ r, red (f r) = 0) :
    ∃ G : LaurentSeries A,
      HahnSeries.ofSuppBddBelow f (by
        obtain ⟨B, hB⟩ := hbelow
        refine ⟨B, ?_⟩
        intro r hr
        exact le_of_not_gt (fun hlt => hr (by simpa only [Function.mem_support] using hB r hlt))) =
        (p : A) • G := by
  classical
  let g : ℤ → A := fun r =>
    if hf : f r = 0 then 0 else Classical.choose (hker (f r) (hzero r))
  have hg : ∀ r, f r = (p : A) * g r := by
    intro r
    by_cases hf : f r = 0
    · simp [g, hf]
    · simpa [g, hf] using (Classical.choose_spec (hker (f r) (hzero r)))
  have hgBelow : ∃ B : ℤ, ∀ r < B, g r = 0 := by
    obtain ⟨B, hB⟩ := hbelow
    exact ⟨B, fun r hr => by simp [g, hB r hr]⟩
  let G : LaurentSeries A := HahnSeries.ofSuppBddBelow g (by
    obtain ⟨B, hB⟩ := hgBelow
    refine ⟨B, ?_⟩
    intro r hr
    exact le_of_not_gt (fun hlt => hr (by simpa only [Function.mem_support] using hB r hlt)))
  refine ⟨G, ?_⟩
  apply HahnSeries.ext
  funext r
  change f r = (p : A) * g r
  exact hg r

/-- After a projected row vanishes modulo `p`, dividing its `R`th power by
`p^R` remains an integral Laurent row.  A discriminant factor can be inserted
without changing this conclusion. -/
def laurentOfRow {A : Type*} [Zero A]
    (f : ℤ → A) (hbelow : ∃ B : ℤ, ∀ r < B, f r = 0) : LaurentSeries A :=
  HahnSeries.ofSuppBddBelow f (by
    obtain ⟨B, hB⟩ := hbelow
    refine ⟨B, ?_⟩
    intro r hr
    exact le_of_not_gt (fun hlt => hr (by
      simpa only [Function.mem_support] using hB r hlt)))

theorem laurentOfRow_coeff {A : Type*} [Zero A]
    (f : ℤ → A) (hbelow : ∃ B : ℤ, ∀ r < B, f r = 0) (r : ℤ) :
    (laurentOfRow f hbelow).coeff r = f r := by rfl

theorem laurentOfRow_progressionLaurent {A : Type*} [Zero A]
    (f : ℤ → A) (M : ℕ) (u : ℤ)
    (hbelow : ∃ B : ℤ, ∀ r < B, f r = 0)
    (hrowBelow : ∃ B : ℤ, ∀ r < B, progressionRow f M u r = 0) :
    laurentOfRow (progressionRow f M u) hrowBelow =
      progressionLaurent f M u hbelow := by
  apply HahnSeries.ext
  funext r
  rw [laurentOfRow_coeff, progressionLaurent_coeff]

theorem scaled_power_integral_of_reduction_zero {A : Type*} [CommRing A]
    (p R s : ℕ) (red : A →+* ZMod p)
    (hker : ∀ x : A, red x = 0 → ∃ y : A, x = (p : A) * y)
    (f : ℤ → A) (hbelow : ∃ B : ℤ, ∀ r < B, f r = 0)
    (hzero : ∀ r, red (f r) = 0) (δ : LaurentSeries A) :
    ∃ G : LaurentSeries A,
      δ ^ s * (laurentOfRow f hbelow) ^ R = (p : A) ^ R • G := by
  obtain ⟨T, hT⟩ := laurent_divisible_of_reduction_zero p red hker f hbelow hzero
  refine ⟨δ ^ s * T ^ R, ?_⟩
  change δ ^ s * (HahnSeries.ofSuppBddBelow f _) ^ R = _
  rw [hT]
  rw [← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul]
  simp only [map_pow]
  ring

/-- The formal last step of the powered-slash argument. The right side is the
integral rational descent of the transformed, divided Fourier row. Reduction
kills `p^R`; the discriminant factor and the Laurent domain cancel the rest.
No coprimality between `p` and `R` is used [garthwaiteJameson2021, §2]. -/
theorem laurent_reduction_zero_of_scaled_power {A : Type*} [CommRing A]
    (p R s : ℕ) [Fact p.Prime] (red : A →+* ZMod p)
    (hredp : red (p : A) = 0)
    (δ F H : LaurentSeries A) (hδ : δ.map red ≠ 0) (hR : 0 < R)
    (heq : δ ^ s * F ^ R = (p : A) ^ R • H) :
    F.map red = 0 := by
  have hrhs : (((p : A) ^ R • H).map red : LaurentSeries (ZMod p)) = 0 := by
    apply HahnSeries.ext
    funext r
    change red ((p : A) ^ R * H.coeff r) = 0
    have hRne : R ≠ 0 := by omega
    simp [map_mul, map_pow, hredp, hRne]
  have hmap := congrArg (fun x : LaurentSeries A => x.map red) heq
  have hmul : (δ ^ s * F ^ R).map red =
      (δ ^ s).map red * (F ^ R).map red := by
    change (δ ^ s * F ^ R).map red.toNonUnitalRingHom =
      (δ ^ s).map red * (F ^ R).map red
    exact HahnSeries.map_mul red.toNonUnitalRingHom
  have hzero : (δ.map red) ^ s * (F.map red) ^ R = 0 := by
    calc
      (δ.map red) ^ s * (F.map red) ^ R =
          (δ ^ s).map red * (F ^ R).map red := by
            rw [laurent_map_pow, laurent_map_pow]
      _ = (δ ^ s * F ^ R).map red := hmul.symm
      _ = 0 := hmap.trans hrhs
  have hpower : (F.map red) ^ R = 0 :=
    (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero s hδ)
  by_contra hF
  exact (pow_ne_zero R hF) hpower

/-- A rational Fourier coefficient which is integral in a finite cyclotomic
coefficient ring lies in the integrally closed ring of rational coefficients.
The characteristic-zero field records the faithful comparison of the two
coefficient embeddings [deligneRapoport1973, Corollaire 3.12]. -/
theorem rational_coefficient_of_cyclotomic_integral
    (A : Subring ℚ) [IsFractionRing A ℚ] [IsIntegrallyClosed A]
    {C K : Type*} [CommRing C] [Field K]
    [Algebra A C] [Algebra A K] [Algebra ℚ K] [Algebra C K]
    [IsScalarTower A ℚ K] [IsScalarTower A C K]
    (q : ℚ) (c : C) (hc : IsIntegral A c)
    (heq : algebraMap ℚ K q = algebraMap C K c) :
    ∃ a : A, (a : ℚ) = q := by
  have hqK : IsIntegral A ((algebraMap ℚ K) q) := by
    rw [heq]
    exact hc.algebraMap
  have hq : IsIntegral A q := by
    exact (isIntegral_algHom_iff
      (IsScalarTower.toAlgHom A ℚ K)
      (IsScalarTower.toAlgHom A ℚ K).injective).mp hqK
  obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff).mp hq
  exact ⟨a, ha⟩

/-- Reassemble a bounded-below rational row whose coefficients lie in a
specified rational subring.  The full negative-index support is retained. -/
theorem laurent_of_rational_coefficients (A : Subring ℚ)
    (F : LaurentSeries ℚ)
    (hcoeff : ∀ r : ℤ, F.coeff r ∈ A)
    (hbelow : ∃ B : ℤ, ∀ r < B, F.coeff r = 0) :
    ∃ G : LaurentSeries A, G.map (Subring.subtype A) = F := by
  let g : ℤ → A := fun r => ⟨F.coeff r, hcoeff r⟩
  have hgBelow : ∃ B : ℤ, ∀ r < B, g r = 0 := by
    obtain ⟨B, hB⟩ := hbelow
    exact ⟨B, fun r hr => Subtype.ext (hB r hr)⟩
  let G : LaurentSeries A := HahnSeries.ofSuppBddBelow g (by
    obtain ⟨B, hB⟩ := hgBelow
    refine ⟨B, ?_⟩
    intro r hr
    exact le_of_not_gt (fun hlt => hr (by simpa only [Function.mem_support] using hB r hlt)))
  refine ⟨G, ?_⟩
  apply HahnSeries.ext
  funext r
  rfl

/-- Descent of the transformed powered Fourier row from a cyclotomic integral
coefficient ring to the rational local ring, followed by reduction and Laurent
domain cancellation.  The supplied equality is the exact Fourier identity
coming from the powered slash and the weight-twelve transformation of `Δ`;
the cyclotomic integrality statement comes from the applicable slash lattice
law [garthwaiteJameson2021, Proposition 4 and Theorem 5],
[deligneRapoport1973, Corollaire 3.12]. -/
theorem reduction_zero_of_cyclotomic_powered_row
    (p R s : ℕ) [Fact p.Prime]
    (A : Subring ℚ) [IsFractionRing A ℚ] [IsIntegrallyClosed A]
    {C K : Type*} [CommRing C] [Field K]
    [Algebra A C] [Algebra A K] [Algebra ℚ K] [Algebra C K]
    [IsScalarTower A ℚ K] [IsScalarTower A C K]
    (red : A →+* ZMod p) (hredp : red (p : A) = 0)
    (δ F : LaurentSeries A) (hδ : δ.map red ≠ 0)
    (H : LaurentSeries ℚ)
    (hbelow : ∃ B : ℤ, ∀ r < B, H.coeff r = 0)
    (hscaled : (p : ℚ) ^ R • H =
      (δ.map (Subring.subtype A)) ^ s * (F.map (Subring.subtype A)) ^ R)
    (hintegral : ∀ r : ℤ, ∃ c : C, IsIntegral A c ∧
      algebraMap ℚ K (H.coeff r) = algebraMap C K c)
    (hR : 0 < R) : F.map red = 0 := by
  have hcoeff : ∀ r : ℤ, H.coeff r ∈ A := by
    intro r
    obtain ⟨c, hc, heq⟩ := hintegral r
    obtain ⟨a, ha⟩ := rational_coefficient_of_cyclotomic_integral A
      (H.coeff r) c hc heq
    exact ha ▸ a.property
  obtain ⟨H₀, hH₀⟩ := laurent_of_rational_coefficients A H hcoeff hbelow
  have hscaledA : δ ^ s * F ^ R = (p : A) ^ R • H₀ := by
    apply HahnSeries.ext
    funext r
    apply Subtype.ext
    have hcoef := congrArg (fun X : LaurentSeries ℚ => X.coeff r) hscaled
    simp only [HahnSeries.coeff_smul] at hcoef
    have hδF : (δ ^ s * F ^ R).map (Subring.subtype A) =
        (δ.map (Subring.subtype A)) ^ s *
          (F.map (Subring.subtype A)) ^ R := by
      calc
        (δ ^ s * F ^ R).map (Subring.subtype A) =
            (δ ^ s).map (Subring.subtype A) *
              (F ^ R).map (Subring.subtype A) := by
                change (δ ^ s * F ^ R).map (Subring.subtype A).toNonUnitalRingHom = _
                exact HahnSeries.map_mul (Subring.subtype A).toNonUnitalRingHom
        _ = _ := by rw [laurent_map_pow, laurent_map_pow]
    have hleft := congrArg (fun X : LaurentSeries ℚ => X.coeff r) hδF
    have hright := congrArg (fun X : LaurentSeries ℚ => X.coeff r) hH₀
    suffices hcast : (((δ ^ s * F ^ R).coeff r : A) : ℚ) =
        (((p : A) ^ R : A) : ℚ) * (H₀.coeff r : ℚ) by
      simpa only [HahnSeries.coeff_smul, smul_eq_mul, Subring.coe_mul] using hcast
    calc
      (((δ ^ s * F ^ R).coeff r : A) : ℚ) =
          ((δ.map (Subring.subtype A)) ^ s *
            (F.map (Subring.subtype A)) ^ R).coeff r := by
              simpa [laurent_map_coeff] using hleft
      _ = (p : ℚ) ^ R * H.coeff r := hcoef.symm
      _ = (((p : A) ^ R : A) : ℚ) * (H₀.coeff r : ℚ) := by
        rw [← hright]
        simp only [laurent_map_coeff]
        simp
  exact laurent_reduction_zero_of_scaled_power p R s red hredp δ F H₀ hδ hR hscaledA

/-- A nonzero discriminant factor cancels from a powered progression in the
reduced Laurent domain. In particular the proof permits `p ∣ R`. -/
theorem laurent_eq_zero_of_delta_power_zero (p R s : ℕ) [Fact p.Prime]
    (δ F : LaurentSeries (ZMod p)) (hδ : δ ≠ 0) (_hR : 0 < R)
    (hzero : δ ^ s * F ^ R = 0) : F = 0 := by
  have hpow : F ^ R = 0 :=
    (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero s hδ)
  by_contra hF
  exact (pow_ne_zero R hF) hpow

/-- The reduced Laurent ring is a domain, so a powered projected row can
vanish only if the original row vanishes.  This also covers `p ∣ R`. -/
theorem laurent_eq_zero_of_pow_eq_zero (p R : ℕ) [Fact p.Prime]
    (F : LaurentSeries (ZMod p)) (_hR : 0 < R) (hpow : F ^ R = 0) : F = 0 := by
  by_contra hF
  exact (pow_ne_zero R hF) hpow

end SptClassification.QSeries
