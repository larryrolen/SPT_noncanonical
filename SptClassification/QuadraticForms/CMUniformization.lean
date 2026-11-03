/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.CMComplexTorus
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# The complex elliptic curve of an oriented CM form

The cubic uses mathlib's actual lattice invariants, with coordinates
`x = ℘(z)` and `y = ℘'(z)/2`. Classical complex uniformization is a named
literature premise [silverman2009, Chapter VI, §§3–4]. The CM action and
level-six subgroup are transported from the explicitly constructed torus.
These are endomorphisms of the complex point group; algebraicity of the
endomorphisms, descent and good reduction are separate inputs.
-/

public section

namespace SptClassification.ComplexUniformization

/-- The short Weierstrass equation with the standard lattice invariants.
The factor `1/4` corresponds to the coordinate `y = ℘'/2`. -/
noncomputable def curve (L : PeriodPair) : WeierstrassCurve ℂ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -L.g₂ / 4
  a₆ := -L.g₃ / 4

theorem curve_a₁ (L : PeriodPair) : (curve L).a₁ = 0 := (rfl)

theorem curve_a₂ (L : PeriodPair) : (curve L).a₂ = 0 := (rfl)

theorem curve_a₃ (L : PeriodPair) : (curve L).a₃ = 0 := (rfl)

theorem curve_a₄ (L : PeriodPair) : (curve L).a₄ = -L.g₂ / 4 := (rfl)

/-- Classical nonsingularity of the lattice cubic
[silverman2009, Chapter VI, §3, Weierstrass functions]. This is an
explicit literature admission, for any real-linearly independent periods. -/
theorem curve_isElliptic (L : PeriodPair) : (curve L).IsElliptic := by
  sorry

/-- Classical complex uniformization [silverman2009, Chapter VI, §§3–4,
Weierstrass functions and analytic maps]. The affine normalization is
`(℘, ℘'/2)`, not `(℘, ℘')`, for the cubic defined above. This interface
asserts the point-group equivalence and its coordinates, not algebraicity
of arbitrary additive maps. It is an explicit literature admission. -/
theorem exists_uniformization (L : PeriodPair) :
    ∃ e : (ℂ ⧸ L.lattice.toAddSubgroup) ≃+ (curve L).toAffine.Point,
      ∀ z : ℂ, z ∉ L.lattice →
        ∃ h : (curve L).toAffine.Nonsingular
            (L.weierstrassP z) (L.derivWeierstrassP z / 2),
          e (QuotientAddGroup.mk' L.lattice.toAddSubgroup z) =
            .some (L.weierstrassP z) (L.derivWeierstrassP z / 2) h := by
  sorry

/-- The chosen classical uniformization, with its coordinate specification
retained by `uniformization_coordinates`. -/
noncomputable def uniformization (L : PeriodPair) :
    (ℂ ⧸ L.lattice.toAddSubgroup) ≃+ (curve L).toAffine.Point :=
  (exists_uniformization L).choose

theorem uniformization_coordinates (L : PeriodPair) (z : ℂ)
    (hz : z ∉ L.lattice) :
    ∃ h : (curve L).toAffine.Nonsingular
        (L.weierstrassP z) (L.derivWeierstrassP z / 2),
      uniformization L (QuotientAddGroup.mk' L.lattice.toAddSubgroup z) =
        .some (L.weierstrassP z) (L.derivWeierstrassP z / 2) h :=
  (exists_uniformization L).choose_spec z hz

end ComplexUniformization

namespace LevelSixForm

variable {D : ℤ} {r : ZMod 12} [Fact (D < 0)] (Q : LevelSixForm D r)

/-- The independent periods `1, τ` of the actual oriented form. -/
noncomputable def periodPair : PeriodPair where
  ω₁ := 1
  ω₂ := Q.cmPoint
  indep := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have him : b * (Q.cmPoint : ℂ).im = 0 := by
      simpa using congrArg Complex.im hab
    have hb : b = 0 := (mul_eq_zero.mp him).resolve_right
      (ne_of_gt Q.cmPoint.im_pos)
    subst b
    have ha : a = 0 := by simpa using congrArg Complex.re hab
    exact ⟨ha, rfl⟩

theorem periodPair_omega_one : Q.periodPair.ω₁ = 1 := (rfl)

theorem periodPair_omega_two : Q.periodPair.ω₂ = (Q.cmPoint : ℂ) := (rfl)

theorem periodPair_lattice : Q.periodPair.lattice.toAddSubgroup = Q.periodLattice := by
  ext z
  change z ∈ Q.periodPair.lattice ↔ _
  rw [PeriodPair.mem_lattice, Q.mem_periodLattice]
  simp [periodPair]

/-- The explicit complex Weierstrass cubic attached to the form. -/
noncomputable abbrev complexCurve : WeierstrassCurve ℂ :=
  ComplexUniformization.curve Q.periodPair

/-- The lattice cubic is elliptic, using classical complex uniformization. -/
theorem complexCurve_isElliptic : Q.complexCurve.IsElliptic :=
  ComplexUniformization.curve_isElliptic Q.periodPair

/-- Identifying the two definitions of the period lattice, without changing
its complex coordinate. -/
noncomputable def periodQuotientEquiv :
    Q.ComplexTorus ≃+ (ℂ ⧸ Q.periodPair.lattice.toAddSubgroup) :=
  { toFun := QuotientAddGroup.map Q.periodLattice Q.periodPair.lattice.toAddSubgroup
      (AddMonoidHom.id ℂ) (fun z hz => by
        change z ∈ Q.periodPair.lattice.toAddSubgroup
        simpa only [Q.periodPair_lattice] using hz)
    invFun := QuotientAddGroup.map Q.periodPair.lattice.toAddSubgroup Q.periodLattice
      (AddMonoidHom.id ℂ) (fun z hz => by
        change z ∈ Q.periodLattice
        simpa only [Q.periodPair_lattice] using hz)
    left_inv := by
      intro x
      obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective Q.periodLattice x
      rfl
    right_inv := by
      intro x
      obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective
        Q.periodPair.lattice.toAddSubgroup x
      rfl
    map_add' := map_add _ }

theorem periodQuotientEquiv_point (z : ℂ) :
    Q.periodQuotientEquiv (Q.torusPoint z) =
      QuotientAddGroup.mk' Q.periodPair.lattice.toAddSubgroup z := by
  rw [Q.torusPoint_apply]
  rfl

/-- The actual CM torus uniformizes the explicit complex cubic. -/
noncomputable def curveUniformization :
    Q.ComplexTorus ≃+ Q.complexCurve.toAffine.Point :=
  Q.periodQuotientEquiv.trans (ComplexUniformization.uniformization Q.periodPair)

/-- Uniformization uses the same complex coordinate on both lattice quotients. -/
theorem curveUniformization_torusPoint (z : ℂ) :
    Q.curveUniformization (Q.torusPoint z) =
      ComplexUniformization.uniformization Q.periodPair
        (QuotientAddGroup.mk' Q.periodPair.lattice.toAddSubgroup z) := by
  change ComplexUniformization.uniformization Q.periodPair
    (Q.periodQuotientEquiv (Q.torusPoint z)) = _
  rw [Q.periodQuotientEquiv_point]

/-- The chosen map retains the standard analytic coordinate formula. -/
theorem curveUniformization_coordinates (z : ℂ) (hz : z ∉ Q.periodLattice) :
    ∃ h : Q.complexCurve.toAffine.Nonsingular
        (Q.periodPair.weierstrassP z) (Q.periodPair.derivWeierstrassP z / 2),
      Q.curveUniformization (Q.torusPoint z) =
        .some (Q.periodPair.weierstrassP z) (Q.periodPair.derivWeierstrassP z / 2) h := by
  have hz' : z ∉ Q.periodPair.lattice := by
    change z ∉ Q.periodPair.lattice.toAddSubgroup
    simpa only [Q.periodPair_lattice] using hz
  change ∃ h : (ComplexUniformization.curve Q.periodPair).toAffine.Nonsingular
      (Q.periodPair.weierstrassP z) (Q.periodPair.derivWeierstrassP z / 2),
    ComplexUniformization.uniformization Q.periodPair
      (Q.periodQuotientEquiv (Q.torusPoint z)) = .some _ _ h
  rw [Q.periodQuotientEquiv_point]
  exact ComplexUniformization.uniformization_coordinates Q.periodPair z hz'

/-- The CM generator acting on the complex points of the explicit cubic.
Algebraicity of this additive endomorphism is not asserted here. -/
noncomputable def curveGenerator (hodd : Q.b % 2 = 1) :
    Q.complexCurve.toAffine.Point →+ Q.complexCurve.toAffine.Point :=
  Q.curveUniformization.toAddMonoidHom.comp
    ((Q.torusGenerator hodd).comp Q.curveUniformization.symm.toAddMonoidHom)

theorem curveGenerator_uniformization (hodd : Q.b % 2 = 1) (x : Q.ComplexTorus) :
    Q.curveGenerator hodd (Q.curveUniformization x) =
      Q.curveUniformization (Q.torusGenerator hodd x) := by
  simp [curveGenerator]

/-- The manuscript's trace-one quadratic relation on the complex curve. -/
theorem curveGenerator_quadratic (hodd : Q.b % 2 = 1) (n : ℕ)
    (hn : 4 * (n : ℤ) = 1 - D) (x : Q.complexCurve.toAffine.Point) :
    Q.curveGenerator hodd (Q.curveGenerator hodd x) -
      Q.curveGenerator hodd x + n • x = 0 := by
  obtain ⟨y, rfl⟩ := Q.curveUniformization.surjective x
  rw [Q.curveGenerator_uniformization, Q.curveGenerator_uniformization]
  rw [← map_nsmul, ← map_sub, ← map_add, Q.torusGenerator_quadratic hodd n hn, map_zero]

/-- The distinguished point of exact order six on the explicit complex curve. -/
noncomputable def curveSixPoint : Q.complexCurve.toAffine.Point :=
  Q.curveUniformization Q.torusSixPoint

theorem curveSixPoint_eq :
    Q.curveSixPoint = Q.curveUniformization Q.torusSixPoint := (rfl)

theorem curveSixPoint_nsmul_eq_zero (n : ℕ) :
    n • Q.curveSixPoint = 0 ↔ 6 ∣ n := by
  change n • Q.curveUniformization Q.torusSixPoint = 0 ↔ _
  rw [← map_nsmul, map_eq_zero_iff Q.curveUniformization Q.curveUniformization.injective]
  exact Q.torusSixPoint_nsmul_eq_zero n

/-- The level-six subgroup on the complex elliptic curve. -/
noncomputable def curveLevelSix : AddSubgroup Q.complexCurve.toAffine.Point :=
  AddSubgroup.zmultiples Q.curveSixPoint

theorem curveLevelSix_eq :
    Q.curveLevelSix = AddSubgroup.zmultiples Q.curveSixPoint := (rfl)

/-- The orientation scalar is unchanged by uniformization. -/
theorem curveGenerator_sixPoint (hodd : Q.b % 2 = 1) :
    Q.curveGenerator hodd Q.curveSixPoint =
      ((Q.b + 1) / 2 : ℤ) • Q.curveSixPoint := by
  change Q.curveGenerator hodd (Q.curveUniformization Q.torusSixPoint) = _
  rw [Q.curveGenerator_uniformization, Q.torusGenerator_sixPoint, map_zsmul]
  rfl

/-- The CM action preserves the actual cyclic subgroup on the complex cubic. -/
theorem curveGenerator_preserves_levelSix (hodd : Q.b % 2 = 1)
    (x : Q.complexCurve.toAffine.Point) (hx : x ∈ Q.curveLevelSix) :
    Q.curveGenerator hodd x ∈ Q.curveLevelSix := by
  obtain ⟨m, rfl⟩ := hx
  change ∃ k : ℤ, k • Q.curveSixPoint = _
  refine ⟨m * ((Q.b + 1) / 2), ?_⟩
  rw [map_zsmul, Q.curveGenerator_sixPoint, mul_smul]

end LevelSixForm
end SptClassification
