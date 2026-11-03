/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.ConditionalPropagationProof
public import SptClassification.QSeries.ProgressionLaurent

/-!
# Powered slash and local integrality for modular progressions

The analytic hypotheses here follow the powered projection identity and the
integrality theorem cited in [garthwaiteJameson2021, Proposition 4 and Theorem 5],
[deligneRapoport1973, Corollaire 3.12], and [radu2012, Corollary 5.3].
-/

public section

namespace SptClassification

open scoped MatrixGroups Manifold
open UpperHalfPlane Filter

/-- The powered projection level is positive, including when its modulus is
divisible by the reduction prime [garthwaiteJameson2021, Proposition 4]. -/
theorem progressionPower_pos (M N₀ : ℕ) (hM : 0 < M) (hN₀ : 0 < N₀) :
    0 < 24 * M * N₀ := by positivity

/-- The matrix used in the powered-slash argument exists for every allowable
upper-left entry. Its lower-left entry is a multiple of the powered level. -/
theorem exists_progression_gamma (M N₀ a : ℕ)
    (_hM : 0 < M) (_hN₀ : 0 < N₀)
    (ha : a.Coprime (6 * M * N₀)) :
    ∃ γ : CongruenceSubgroup.Gamma0 (24 * M * N₀),
      (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ)
        0 0) = a := by
  have ha6 : a.Coprime 6 :=
    Nat.Coprime.of_dvd_right (by exact ⟨M * N₀, by ring⟩) ha
  have haM : a.Coprime M :=
    Nat.Coprime.of_dvd_right (by exact ⟨6 * N₀, by ring⟩) ha
  have haN₀ : a.Coprime N₀ :=
    Nat.Coprime.of_dvd_right (by exact ⟨6 * M, by ring⟩) ha
  have ha2 : a.Coprime 2 :=
    Nat.Coprime.of_dvd_right (by decide : 2 ∣ 6) ha6
  have ha4 : a.Coprime 4 := by
    convert ha2.pow_right 2 using 1
  have ha24 : a.Coprime 24 := by
    convert ha6.mul_right ha4 using 1
  have haR : a.Coprime (24 * M * N₀) :=
    (ha24.mul_right haM).mul_right haN₀
  obtain ⟨d, k, hbezout⟩ := haR.isCoprime
  let A : Matrix (Fin 2) (Fin 2) ℤ := !![(a : ℤ), -k; (24 * M * N₀ : ℤ), d]
  have hdet : A.det = 1 := by
    rw [Matrix.det_fin_two]
    dsimp [A]
    push_cast at hbezout
    linear_combination hbezout
  let γ : Matrix.SpecialLinearGroup (Fin 2) ℤ := ⟨A, hdet⟩
  have hgamma : γ ∈ CongruenceSubgroup.Gamma0 (24 * M * N₀) := by
    change ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod (24 * M * N₀)) = 0
    change ((24 * M * N₀ : ℤ) : ZMod (24 * M * N₀)) = 0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (by exact ⟨1, by push_cast; ring⟩)
  refine ⟨⟨γ, hgamma⟩, ?_⟩
  rfl

/-- The integral weight of the powered projection.  If the original weight is
`k + 1/2`, the `R`th power has weight `R k + R/2`.  The factor `24` in `R`
ensures that this is integral [garthwaiteJameson2021, Proposition 4]. -/
def progressionPowerWeight {p : ℕ} (g : ModularProgressionForm p) (M : ℕ) : ℕ :=
  let R := 24 * M * g.level
  R * g.weightNumerator + if g.halfIntegral then R / 2 else 0

/-- The ordinary integral-weight slash is a pointwise operation on functions.
Its value need not have a rational Fourier expansion of any fixed width. -/
noncomputable def progressionIntegralSlash (k : ℕ)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (F : UpperHalfPlane → ℂ) : UpperHalfPlane → ℂ :=
  fun τ => F (γ • τ) /
    (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ) ^ k

/-- Pointwise evaluation of the ordinary integral-weight slash. -/
theorem progressionIntegralSlash_apply (k : ℕ)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (F : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    progressionIntegralSlash k γ F τ = F (γ • τ) /
      (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ) ^ k := (rfl)

/-- The integral-weight slash commutes with constant scaling. -/
theorem progressionIntegralSlash_const_mul (k : ℕ)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (F : UpperHalfPlane → ℂ) (c : ℂ) :
    progressionIntegralSlash k γ (fun τ => c * F τ) =
      fun τ => c * progressionIntegralSlash k γ F τ := by
  funext τ
  exact mul_div_assoc c (F (γ • τ)) _

/-- The concrete analytic category for the cited integral-lattice principle:
holomorphic weight-`k` forms on `Γ₁(N)` whose weight-`k` slash is bounded at
every rational cusp. The three matrix congruences spell out `Γ₁(N)`; no
q-expansion of an arbitrary slash image is postulated. -/
structure HolomorphicGammaOneForm (N k : ℕ)
    (F : UpperHalfPlane → ℂ) : Prop where
  holomorphic : MDiff F
  gammaOne : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
    ((((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod N) = 1) →
    ((((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N) = 0) →
    ((((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N) = 1) →
    ∀ τ, progressionIntegralSlash k γ F τ = F τ
  boundedAtCusps : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
    IsBoundedAtImInfty (progressionIntegralSlash k γ F)

/-- A rational Fourier algebra of meromorphic functions in `X = q^(1/M)`.
Only the projected forms and Delta are represented here. The applicable
integral-lattice theorem below relates two represented functions by a
pointwise slash equality at their actual weight
[garthwaiteJameson2021, Proposition 4 and Theorem 5]. -/
structure PoweredProjectionData (p : ℕ) (A : Subring ℚ)
    (C K : Type*) [CommRing C] [Field K]
    [Algebra A C] [Algebra A K] [Algebra ℚ K] [Algebra C K]
    [IsScalarTower A ℚ K] [IsScalarTower A C K]
    (red : A →+* ZMod p) (g : ModularProgressionForm p)
    (M : ℕ) (hM : 0 < M) where
  Analytic : Type
  [ring : CommRing Analytic]
  [rational : Algebra ℚ Analytic]
  toFun : Analytic →+* (UpperHalfPlane → ℂ)
  toFun_smul : ∀ (c : ℚ) (f : Analytic) (τ : UpperHalfPlane),
    toFun (c • f) τ = (c : ℂ) * toFun f τ
  qExpansion : Analytic →+* LaurentSeries ℚ
  qExpansion_smul : ∀ (c : ℚ) (f : Analytic),
    qExpansion (c • f) = c • qExpansion f
  qExpansion_hasSum : ∀ (f : Analytic) (τ : UpperHalfPlane),
    HasSum (fun r : ℤ => ((qExpansion f).coeff r : ℂ) *
      (Function.Periodic.qParam M τ) ^ r) (toFun f τ)
  qExpansion_below : ∀ f : Analytic,
    ∃ B : ℤ, ∀ r < B, (qExpansion f).coeff r = 0
  coeffLift : ℤ → A
  coeffLift_eq : ∀ r, (coeffLift r : ℚ) = g.coeff r
  coeffLift_red : ∀ r, red (coeffLift r) = g.coeffMod r
  coeffLift_below : ∃ B : ℤ, ∀ r < B, coeffLift r = 0
  projection : ℤ → Analytic
  projection_qExpansion : ∀ u,
    qExpansion (projection u) =
      (QSeries.progressionLaurent coeffLift M u coeffLift_below).map
        (Subring.subtype A)
  delta : Analytic
  delta_toFun : ∀ τ, toFun delta τ = ModularForm.eta τ ^ 24
  deltaIntegral : LaurentSeries A
  delta_qExpansion : qExpansion delta = deltaIntegral.map (Subring.subtype A)
  delta_leading : deltaIntegral.coeff (M : ℤ) = 1
  delta_slash : ∀ γ τ,
    progressionIntegralSlash 12 γ (toFun delta) τ = toFun delta τ
  powered_slash : ∀ (u : ℤ) (a : ℕ) (_ha6 : a.Coprime 6)
    (γ : CongruenceSubgroup.Gamma0 (24 * M * g.level)),
    (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ)
      0 0) = a →
    ∀ τ, progressionIntegralSlash (progressionPowerWeight g M) γ
      (toFun (projection u ^ (24 * M * g.level))) τ =
      toFun (projection ((a : ℤ) ^ 2 * u) ^ (24 * M * g.level)) τ
  global_pole_clearing : ∀ u, ∃ s : ℕ,
    HolomorphicGammaOneForm (24 * M * g.level)
      (12 * s + progressionPowerWeight g M)
      (toFun (((p : ℚ) ^ (24 * M * g.level))⁻¹ •
        (delta ^ s * projection u ^ (24 * M * g.level))))
  slash_integral : ∀ k (γ : CongruenceSubgroup.Gamma0 (24 * M * g.level))
    (f h : Analytic),
    HolomorphicGammaOneForm (24 * M * g.level) k (toFun f) →
    (∀ τ, progressionIntegralSlash k γ (toFun f) τ = toFun h τ) →
    (∃ F : LaurentSeries A, qExpansion f = F.map (Subring.subtype A)) →
    ∀ r : ℤ, ∃ c : C, IsIntegral A c ∧
      algebraMap ℚ K ((qExpansion h).coeff r) =
        algebraMap C K c

attribute [instance] PoweredProjectionData.ring PoweredProjectionData.rational

namespace PoweredProjectionData

variable {p : ℕ} {A : Subring ℚ} {C K : Type*}
variable [Fact p.Prime]
variable [CommRing C] [Field K]
variable [Algebra A C] [Algebra A K] [Algebra ℚ K] [Algebra C K]
variable [IsScalarTower A ℚ K] [IsScalarTower A C K]
variable {red : A →+* ZMod p} {g : ModularProgressionForm p}
variable {M : ℕ} {hM : 0 < M}

/-- The normalized discriminant remains nonzero after reduction, because its
coefficient at `X^M` is one. -/
theorem delta_reduction_ne_zero (I : PoweredProjectionData p A C K red g M hM) :
    I.deltaIntegral.map red ≠ 0 := by
  intro hz
  have hcoeff := congrArg (fun F : LaurentSeries (ZMod p) => F.coeff (M : ℤ)) hz
  simp only [QSeries.laurent_map_coeff, I.delta_leading, map_one] at hcoeff
  exact one_ne_zero hcoeff

/-- Vanishing of the actual projected row makes the pole-cleared, divided
power integral at the original cusp. This uses neither `p ∤ M` nor `p ∤ R`. -/
theorem source_divided_qExpansion_integral
    (I : PoweredProjectionData p A C K red g M hM)
    (hker : ∀ x : A, red x = 0 → ∃ y : A, x = (p : A) * y)
    (u : ℤ) (s : ℕ)
    (hzero : ∀ r : ℤ, (r : ZMod M) = (u : ZMod M) → g.coeffMod r = 0) :
    ∃ T : LaurentSeries A,
      I.qExpansion (((p : ℚ) ^ (24 * M * g.level))⁻¹ •
        (I.delta ^ s * I.projection u ^ (24 * M * g.level))) =
        T.map (Subring.subtype A) := by
  let R := 24 * M * g.level
  let row : ℤ → A := QSeries.progressionRow I.coeffLift M u
  have hbelow : ∃ B : ℤ, ∀ r < B, row r = 0 :=
    QSeries.progressionRow_zero_below I.coeffLift M u I.coeffLift_below
  let F : LaurentSeries A := QSeries.laurentOfRow row hbelow
  have hF : F = QSeries.progressionLaurent I.coeffLift M u I.coeffLift_below := by
    exact QSeries.laurentOfRow_progressionLaurent I.coeffLift M u
      I.coeffLift_below hbelow
  have hrow : ∀ r, red (row r) = 0 := by
    intro r
    by_cases hr : (r : ZMod M) = (u : ZMod M)
    · rw [show row r = I.coeffLift r from
        QSeries.progressionRow_eq_of I.coeffLift M u r hr]
      rw [I.coeffLift_red]
      exact hzero r hr
    · rw [show row r = 0 from
        QSeries.progressionRow_eq_zero_of I.coeffLift M u r hr, map_zero]
  obtain ⟨T, hscaled⟩ := QSeries.scaled_power_integral_of_reduction_zero
    p R s red hker row hbelow hrow I.deltaIntegral
  change I.deltaIntegral ^ s * F ^ R = (p : A) ^ R • T at hscaled
  have hqsource : I.qExpansion (I.delta ^ s * I.projection u ^ R) =
      (I.deltaIntegral ^ s * F ^ R).map (Subring.subtype A) := by
    calc
      I.qExpansion (I.delta ^ s * I.projection u ^ R) =
          (I.qExpansion I.delta) ^ s * (I.qExpansion (I.projection u)) ^ R := by
            simp
      _ = (I.deltaIntegral.map (Subring.subtype A)) ^ s *
            (F.map (Subring.subtype A)) ^ R := by
            rw [I.delta_qExpansion, I.projection_qExpansion, ← hF]
      _ = (I.deltaIntegral ^ s * F ^ R).map (Subring.subtype A) := by
            rw [QSeries.laurent_map_mul, QSeries.laurent_map_pow,
              QSeries.laurent_map_pow]
  have hpQ : (p : ℚ) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpRQ : (p : ℚ) ^ R ≠ 0 := pow_ne_zero R hpQ
  refine ⟨T, ?_⟩
  rw [I.qExpansion_smul, hqsource, hscaled, QSeries.laurent_map_smul]
  have hcast : (Subring.subtype A) ((p : A) ^ R) = (p : ℚ) ^ R := by
    simp
  rw [hcast, smul_smul, inv_mul_cancel₀ hpRQ, one_smul]

/-- Apply the holomorphic slash-lattice theorem to the actual pole-cleared
projected form. Rational descent is performed separately
[deligneRapoport1973, Corollaire 3.12], [radu2012, Corollary 5.3]. -/
theorem transformed_divided_qExpansion_integral
    (I : PoweredProjectionData p A C K red g M hM)
    (hker : ∀ x : A, red x = 0 → ∃ y : A, x = (p : A) * y)
    (u : ℤ) (a : ℕ) (ha : a.Coprime (6 * M * g.level))
    (hzero : ∀ r : ℤ, (r : ZMod M) = (u : ZMod M) → g.coeffMod r = 0) :
    ∃ s : ℕ, ∃ H : LaurentSeries ℚ,
      (∃ B : ℤ, ∀ r < B, H.coeff r = 0) ∧
      (∀ r : ℤ, ∃ c : C, IsIntegral A c ∧
        algebraMap ℚ K (H.coeff r) = algebraMap C K c) ∧
      (p : ℚ) ^ (24 * M * g.level) • H =
        (I.deltaIntegral.map (Subring.subtype A)) ^ s *
          ((QSeries.progressionLaurent I.coeffLift M
            ((a : ℤ) ^ 2 * u) I.coeffLift_below).map
              (Subring.subtype A)) ^ (24 * M * g.level) := by
  let R := 24 * M * g.level
  let w := progressionPowerWeight g M
  let v : ℤ := (a : ℤ) ^ 2 * u
  obtain ⟨γ, hγ⟩ := exists_progression_gamma M g.level a hM g.level_pos ha
  obtain ⟨s, hs⟩ := I.global_pole_clearing u
  let f : I.Analytic := ((p : ℚ) ^ R)⁻¹ • (I.delta ^ s * I.projection u ^ R)
  let h : I.Analytic := ((p : ℚ) ^ R)⁻¹ • (I.delta ^ s * I.projection v ^ R)
  let H : LaurentSeries ℚ := I.qExpansion h
  obtain ⟨T, hT⟩ := I.source_divided_qExpansion_integral hker u s hzero
  have hsource : I.qExpansion f = T.map (Subring.subtype A) := hT
  have ha6 : a.Coprime 6 :=
    Nat.Coprime.of_dvd_right (by exact ⟨M * g.level, by ring⟩) ha
  have hdeltaSlash (τ : UpperHalfPlane) :
      progressionIntegralSlash (12 * s) γ (I.toFun (I.delta ^ s)) τ =
        I.toFun (I.delta ^ s) τ := by
    calc
      _ = (progressionIntegralSlash 12 γ (I.toFun I.delta) τ) ^ s := by
        simp [progressionIntegralSlash, pow_mul, div_pow]
      _ = I.toFun (I.delta ^ s) τ := by
        rw [I.delta_slash]
        simp
  have hprojectionSlash (τ : UpperHalfPlane) :
      progressionIntegralSlash w γ (I.toFun (I.projection u ^ R)) τ =
        I.toFun (I.projection v ^ R) τ :=
    I.powered_slash u a ha6 γ hγ τ
  have hslash (τ : UpperHalfPlane) :
      progressionIntegralSlash (12 * s + w) γ (I.toFun f) τ = I.toFun h τ := by
    have hf (z : UpperHalfPlane) : I.toFun f z =
        (((p : ℚ) ^ R)⁻¹ : ℂ) *
          (I.toFun (I.delta ^ s) z * I.toFun (I.projection u ^ R) z) := by
      simp [f, I.toFun_smul]
    have hh (z : UpperHalfPlane) : I.toFun h z =
        (((p : ℚ) ^ R)⁻¹ : ℂ) *
          (I.toFun (I.delta ^ s) z * I.toFun (I.projection v ^ R) z) := by
      simp [h, I.toFun_smul]
    calc
      _ = (((p : ℚ) ^ R)⁻¹ : ℂ) *
          (progressionIntegralSlash (12 * s) γ (I.toFun (I.delta ^ s)) τ *
            progressionIntegralSlash w γ (I.toFun (I.projection u ^ R)) τ) := by
        simp only [progressionIntegralSlash, hf, pow_add, div_eq_mul_inv, mul_inv_rev]
        ring
      _ = I.toFun h τ := by
        rw [hdeltaSlash, hprojectionSlash, hh]
  have hintegral : ∀ r : ℤ, ∃ c : C, IsIntegral A c ∧
      algebraMap ℚ K (H.coeff r) = algebraMap C K c :=
    I.slash_integral (12 * s + w) γ f h hs hslash ⟨T, hsource⟩
  have htarget : I.qExpansion (I.delta ^ s * I.projection v ^ R) =
      (I.deltaIntegral.map (Subring.subtype A)) ^ s *
        ((QSeries.progressionLaurent I.coeffLift M v
          I.coeffLift_below).map (Subring.subtype A)) ^ R := by
    simp [I.delta_qExpansion, I.projection_qExpansion]
  have hpQ : (p : ℚ) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpRQ : (p : ℚ) ^ R ≠ 0 := pow_ne_zero R hpQ
  refine ⟨s, H, I.qExpansion_below _, hintegral, ?_⟩
  change (p : ℚ) ^ R • I.qExpansion h = _
  rw [show I.qExpansion h =
    ((p : ℚ) ^ R)⁻¹ • I.qExpansion (I.delta ^ s * I.projection v ^ R)
      from I.qExpansion_smul _ _, htarget, smul_smul,
    mul_inv_cancel₀ hpRQ, one_smul]

/-- Powered slash, the applicable cusp-integrality law, rational descent, and
Laurent-domain cancellation transport the actual reduced Fourier coefficients.
This statement includes the cases `p ∣ M` and `p ∣ 24 M N₀`
[garthwaiteJameson2021, Proposition 4 and Theorem 5]. -/
theorem transport_of_powered_slash [IsFractionRing A ℚ] [IsIntegrallyClosed A]
    (I : PoweredProjectionData p A C K red g M hM)
    (hker : ∀ x : A, red x = 0 → ∃ y : A, x = (p : A) * y)
    (hredp : red (p : A) = 0)
    (u : ℤ) (a : ℕ) (ha : a.Coprime (6 * M * g.level))
    (hzero : ∀ r : ℤ, (r : ZMod M) = (u : ZMod M) → g.coeffMod r = 0) :
    ∀ r : ℤ, (r : ZMod M) =
      ((a : ZMod M) ^ 2 * (u : ZMod M)) → g.coeffMod r = 0 := by
  obtain ⟨s, H, hbelow, hintegral, hscaled⟩ :=
    I.transformed_divided_qExpansion_integral hker u a ha hzero
  let R := 24 * M * g.level
  let v : ℤ := (a : ℤ) ^ 2 * u
  let F : LaurentSeries A :=
    QSeries.progressionLaurent I.coeffLift M v I.coeffLift_below
  have hδ : I.deltaIntegral.map red ≠ 0 := I.delta_reduction_ne_zero
  have hR : 0 < R := progressionPower_pos M g.level hM g.level_pos
  have hFzero : F.map red = 0 := by
    exact QSeries.reduction_zero_of_cyclotomic_powered_row
      p R s A red hredp I.deltaIntegral F hδ H hbelow hscaled hintegral hR
  intro r hr
  have hrv : (r : ZMod M) = (v : ZMod M) := by
    simpa only [v, Int.cast_mul, Int.cast_pow, Int.cast_natCast] using hr
  have hc := congrArg (fun X : LaurentSeries (ZMod p) => X.coeff r) hFzero
  have hczero : red (I.coeffLift r) = 0 := by
    simpa only [F, QSeries.laurent_map_coeff,
      QSeries.progressionLaurent_coeff,
      QSeries.progressionRow_eq_of I.coeffLift M v r hrv,
      HahnSeries.coeff_zero] using hc
  exact (I.coeffLift_red r).symm.trans hczero

end PoweredProjectionData

/-- Uniform powered-projection and slash-integrality data for the actual
modular coefficient objects.  The rational subring `A` is the chosen
`p`-integral coefficient ring; `C` is the coefficient ring in which the cited
slash-integrality theorem holds, and `K` faithfully compares its coefficients
with rational Fourier coefficients.  The kernel condition specifies reduction
modulo `p`.  Every analytic and cusp law is supplied for each actual form and
every positive progression modulus, including moduli divisible by `p`
[garthwaiteJameson2021, Proposition 4 and Theorem 5],
[deligneRapoport1973, Corollaire 3.12], [radu2012, Corollary 5.3]. -/
structure PoweredProgressionInputs (p : ℕ)
    (A : Subring ℚ) (C K : Type*)
    [CommRing C] [Field K]
    [Algebra A C] [Algebra A K] [Algebra ℚ K] [Algebra C K]
    [IsScalarTower A ℚ K] [IsScalarTower A C K] where
  reduction : A →+* ZMod p
  reduction_kernel : ∀ x : A, reduction x = 0 → ∃ y : A, x = (p : A) * y
  reduction_p : reduction (p : A) = 0
  forForm : ∀ (g : ModularProgressionForm p) (M : ℕ) (hM : 0 < M),
    PoweredProjectionData p A C K reduction g M hM

namespace PoweredProgressionInputs

variable {p : ℕ} {A : Subring ℚ} {C K : Type*}
variable [Fact p.Prime] [CommRing C] [Field K]
variable [Algebra A C] [Algebra A K] [Algebra ℚ K] [Algebra C K]
variable [IsScalarTower A ℚ K] [IsScalarTower A C K]
variable [IsFractionRing A ℚ] [IsIntegrallyClosed A]

/-- The cited analytic data and local-ring laws imply the generic progression
transport used by the manuscript.  In particular the conclusion is derived
for every `ModularProgressionForm`, rather than supplied as an input. -/
theorem toProgressionTransportInput (I : PoweredProgressionInputs p A C K) :
    ProgressionTransportInput p := by
  constructor
  intro g M hM u a ha hzero
  exact (I.forForm g M hM).transport_of_powered_slash
    I.reduction_kernel I.reduction_p u a ha hzero

end PoweredProgressionInputs

/-- The conditional propagation lemma with its generic transport derived
from powered slash and the applicable integral q-expansion law.  The actual
smallest-parts approximation input is unchanged [rolenManuscript, §2]. -/
theorem conditional_propagation_of_powered_slash
    (p b : ℕ) (hp : p.Prime) (hfive : 5 ≤ p) (hb : b < p)
    (hnotcanonical : ((24 * (b : ℤ) - 1 : ℤ) : ZMod p) ≠ 0)
    (hspt : ∀ n : ℕ, p ∣ spt (p * n + b))
    (A : Subring ℚ) (C K : Type*)
    [CommRing C] [Field K]
    [Algebra A C] [Algebra A K] [Algebra ℚ K] [Algebra C K]
    [IsScalarTower A ℚ K] [IsScalarTower A C K]
    [IsFractionRing A ℚ] [IsIntegrallyClosed A]
    (powered : PoweredProgressionInputs p A C K)
    (approximation : SptApproximationInput p hfive)
    (N : ℕ)
    (hclass : @legendreSym p ⟨hp⟩ (1 - 24 * (N : ℤ)) =
      @legendreSym p ⟨hp⟩ (1 - 24 * (b : ℤ))) :
    p ∣ spt N := by
  let : Fact p.Prime := ⟨hp⟩
  exact conditional_propagation p b hp hfive hb hnotcanonical hspt
    ⟨powered.toProgressionTransportInput, approximation⟩ N hclass

end SptClassification
