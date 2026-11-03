/- Assembled by AxiomProver. -/

module

public import SptClassification.Theta.MetaplecticCubicRelation
public import SptClassification.Theta.MetaplecticProjection
public import Mathlib.Topology.Algebra.Field

/-!
# Continuous square-root pairs and the standard generators

For a fixed integral modular matrix, two continuous square roots of its
automorphy denominator differ by one global sign on the connected upper
half-plane. The chosen inversion and translation lifts generate both signs
over each matrix. This identifies their concrete group with the regular
metaplectic pairs used in [rolenManuscript, lines 339–343]. It does not
descend the full finite Weil operator from generator words.
-/

public section

namespace SptClassification
namespace Theta

/-- The eta function is continuous on the upper half-plane. -/
theorem eta_continuous_on_upperHalfPlane :
    Continuous (fun z : UpperHalfPlane => ModularForm.eta (z : ℂ)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  exact (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet z.im_pos).continuousAt.comp
    UpperHalfPlane.continuous_coe.continuousAt

/-- A standard-generator word acts continuously on the upper half-plane. -/
theorem etaWeilWordAction_continuous (w : List EtaWeilStep) :
    Continuous (etaWeilWordAction w) := by
  induction w with
  | nil =>
      have hfun : etaWeilWordAction [] =
          (fun z : UpperHalfPlane => z) := funext etaWeilWordAction_nil
      rw [hfun]
      exact continuous_id
  | cons g w ih =>
      have hg : Continuous g.act := by
        cases g with
        | inversion =>
            have hneg : Continuous (fun z : UpperHalfPlane => -(z : ℂ)) :=
              UpperHalfPlane.continuous_coe.neg
            have hinv : Continuous (fun z : UpperHalfPlane => (-(z : ℂ))⁻¹) := by
              rw [continuous_iff_continuousAt]
              intro z
              exact hneg.continuousAt.inv₀ (neg_ne_zero.mpr z.ne_zero)
            apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
            simpa only [Function.comp_def, EtaWeilStep.act_inversion,
              UpperHalfPlane.modular_S_smul] using hinv
        | translation n =>
            have hact : (EtaWeilStep.translation n).act =
                (fun z : UpperHalfPlane => (n : ℝ) +ᵥ z) :=
              funext (EtaWeilStep.act_translation n)
            rw [hact]
            apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
            convert (continuous_const.add UpperHalfPlane.continuous_coe :
              Continuous ((fun _ : UpperHalfPlane => ((n : ℝ) : ℂ)) +
                UpperHalfPlane.coe)) using 1
            funext z
            simp [UpperHalfPlane.coe_vadd]
      have hcons : etaWeilWordAction (g :: w) =
          g.act ∘ etaWeilWordAction w :=
        funext (etaWeilWordAction_cons g w)
      rw [hcons]
      exact hg.comp ih

/-- The square-root factor of every standard-generator word is continuous.
Eta nonvanishing gives a uniform quotient formula, including the inversion
step where the principal complex square root occurs. -/
theorem etaWeilWordFactor_continuous (w : List EtaWeilStep) :
    Continuous (etaWeilWordFactor w) := by
  have hratio (z : UpperHalfPlane) :
      etaWeilWordFactor w z =
        ModularForm.eta (etaWeilWordAction w z : ℂ) /
          (etaWeilWordPhase w * ModularForm.eta (z : ℂ)) := by
    apply (eq_div_iff (mul_ne_zero (etaWeilWordPhase_ne_zero w)
      (ModularForm.eta_ne_zero z.im_pos))).mpr
    calc
      etaWeilWordFactor w z *
          (etaWeilWordPhase w * ModularForm.eta (z : ℂ)) =
        etaWeilWordPhase w * etaWeilWordFactor w z *
          ModularForm.eta (z : ℂ) := by ring
      _ = ModularForm.eta (etaWeilWordAction w z : ℂ) :=
        (eta_action_generator_word w z).symm
  have hfun : etaWeilWordFactor w = fun z =>
      ModularForm.eta (etaWeilWordAction w z : ℂ) /
        (etaWeilWordPhase w * ModularForm.eta (z : ℂ)) :=
    funext hratio
  rw [hfun]
  exact (eta_continuous_on_upperHalfPlane.comp
    (etaWeilWordAction_continuous w)).div
      (continuous_const.mul eta_continuous_on_upperHalfPlane)
      (fun z => mul_ne_zero (etaWeilWordPhase_ne_zero w)
        (ModularForm.eta_ne_zero z.im_pos))

/-- Continuous square-root factors over the same matrix agree everywhere
once they agree at one point. -/
theorem MetaplecticPair.eq_of_continuous_factor_and_value
    (g h : MetaplecticPair)
    (hg : Continuous g.factor) (hh : Continuous h.factor)
    (hmatrix : g.matrix = h.matrix)
    (hvalue : g.factor UpperHalfPlane.I = h.factor UpperHalfPlane.I) :
    g = h := by
  apply MetaplecticPair.ext g h hmatrix
  funext z
  have hsquare : Set.EqOn (g.factor ^ 2) (h.factor ^ 2) Set.univ := by
    intro x _
    simp only [Pi.pow_apply]
    rw [g.factor_sq, h.factor_sq, hmatrix]
  exact (isPreconnected_univ.eq_of_sq_eq hg.continuousOn hh.continuousOn
    hsquare (fun {x} _ => h.factor_ne_zero x)
    (Set.mem_univ UpperHalfPlane.I) hvalue)
    (Set.mem_univ z)

/-- Every concrete generated pair has a continuous square-root factor. -/
theorem generatedPair_factor_continuous (g : etaWeilGeneratedPairs) :
    Continuous g.val.factor := by
  have hw : Continuous
      (etaWeilWordFactor (generatedPairWord g)) :=
    etaWeilWordFactor_continuous _
  have hfun : (etaWeilWordMetaplecticPair (generatedPairWord g)).factor =
      etaWeilWordFactor (generatedPairWord g) :=
    funext (etaWeilWordMetaplecticPair_factor _)
  rw [← hfun] at hw
  rw [generatedPairWord_eq] at hw
  exact hw

/-- A continuous square-root pair is generated by the chosen inversion and
integral translation lifts. The matrix projection supplies a word; uniqueness
of a continuous square root leaves only the central sign, represented by four
inversion lifts. -/
theorem MetaplecticPair.mem_generated_of_continuous_factor
    (g : MetaplecticPair) (hg : Continuous g.factor) :
    g ∈ etaWeilGeneratedPairs := by
  obtain ⟨h, hh⟩ := generatedPairMatrixHom_surjective g.matrix
  have hmatrix : g.matrix = h.val.matrix := by
    simpa only [generatedPairMatrixHom_apply] using hh.symm
  have hmem : h.val ∈ etaWeilGeneratedPairs :=
    (mem_etaWeilGeneratedSubgroup_iff h.val).mp h.property
  have hcontinuous : Continuous h.val.factor :=
    generatedPair_factor_continuous ⟨h.val, hmem⟩
  have hsquare : g.factor UpperHalfPlane.I ^ 2 =
      h.val.factor UpperHalfPlane.I ^ 2 := by
    rw [g.factor_sq, h.val.factor_sq, hmatrix]
  have hprod : (g.factor UpperHalfPlane.I - h.val.factor UpperHalfPlane.I) *
      (g.factor UpperHalfPlane.I + h.val.factor UpperHalfPlane.I) = 0 := by
    calc
      _ = g.factor UpperHalfPlane.I ^ 2 -
          h.val.factor UpperHalfPlane.I ^ 2 := by ring
      _ = 0 := sub_eq_zero.mpr hsquare
  rcases mul_eq_zero.mp hprod with hplus | hminus
  · have hvalue : g.factor UpperHalfPlane.I = h.val.factor UpperHalfPlane.I :=
      sub_eq_zero.mp hplus
    have heq : g = h.val :=
      MetaplecticPair.eq_of_continuous_factor_and_value
        g h.val hg hcontinuous hmatrix hvalue
    rw [heq]
    exact hmem
  · have hvalue : g.factor UpperHalfPlane.I =
        -h.val.factor UpperHalfPlane.I :=
      add_eq_zero_iff_eq_neg.mp hminus
    have hsign : MetaplecticPair.centralSign ∈ etaWeilGeneratedPairs := by
      rw [← etaWeilInversionFour_pair_eq_centralSign]
      exact etaWeilWordMetaplecticPair_mem_generated _
    have hcomp : MetaplecticPair.centralSign * h.val ∈
        etaWeilGeneratedPairs :=
      etaWeilGeneratedPairs.mul_mem hsign hmem
    have hcomp_continuous :
        Continuous (MetaplecticPair.centralSign * h.val).factor := by
      have hfactor : (MetaplecticPair.centralSign * h.val).factor =
          (fun z : UpperHalfPlane => (-1 : ℂ) * h.val.factor z) := by
        funext z
        simp only [MetaplecticPair.mul_factor, MetaplecticPair.centralSign_factor]
      rw [hfactor]
      exact continuous_const.mul hcontinuous
    have hcomp_matrix :
        g.matrix = (MetaplecticPair.centralSign * h.val).matrix := by
      simpa only [MetaplecticPair.mul_matrix,
        MetaplecticPair.centralSign_matrix, one_mul] using hmatrix
    have hcomp_value :
        g.factor UpperHalfPlane.I =
          (MetaplecticPair.centralSign * h.val).factor UpperHalfPlane.I := by
      simpa only [MetaplecticPair.mul_factor,
        MetaplecticPair.centralSign_factor, neg_one_mul] using hvalue
    have heq : g = MetaplecticPair.centralSign * h.val :=
      MetaplecticPair.eq_of_continuous_factor_and_value g _ hg
        hcomp_continuous hcomp_matrix hcomp_value
    rw [heq]
    exact hcomp

/-- The word-generated subgroup is exactly the continuous part of the
algebraic metaplectic pair group. -/
theorem MetaplecticPair.mem_generated_iff_continuous_factor
    (g : MetaplecticPair) :
    g ∈ etaWeilGeneratedSubgroup ↔ Continuous g.factor := by
  constructor
  · intro hg
    exact generatedPair_factor_continuous
      ⟨g, (mem_etaWeilGeneratedSubgroup_iff g).mp hg⟩
  · intro hg
    exact (mem_etaWeilGeneratedSubgroup_iff g).mpr
      (g.mem_generated_of_continuous_factor hg)

end Theta
end SptClassification
