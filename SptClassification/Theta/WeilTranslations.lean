/- Assembled by AxiomProver. -/

module

public import SptClassification.Theta.EtaWeilAutomorphyWords

/-!
# Integral translations in the finite Weil formulas

The diagonal formula for a translation by an integer is an additive action on
the full discriminant-group coefficient space. The corresponding eta phase
and automorphy datum obey the same composition law. These identities are
support for the metaplectic calculation in [rolenManuscript, lines 339–343].
-/

public section

namespace SptClassification
namespace Theta

/-- The finite diagonal operators for integral translations compose
according to addition of their translation parameters. -/
theorem finiteWeilTranslation_add (m n : ℤ) (f : ZMod 12 → ℂ) :
    finiteWeilTranslation (m + n) f =
      finiteWeilTranslation m (finiteWeilTranslation n f) := by
  funext r
  simp only [finiteWeilTranslation_apply, Int.cast_add]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 1
  ring_nf

theorem finiteWeilTranslation_zero (f : ZMod 12 → ℂ) :
    finiteWeilTranslation 0 f = f := by
  funext r
  simp [finiteWeilTranslation_apply]

/-- Translation by `-n` is the inverse of translation by `n` on every
coefficient vector. -/
theorem finiteWeilTranslation_neg (n : ℤ) (f : ZMod 12 → ℂ) :
    finiteWeilTranslation n (finiteWeilTranslation (-n) f) = f := by
  rw [← finiteWeilTranslation_add, add_neg_cancel, finiteWeilTranslation_zero]

theorem etaWeilTranslationPhase_add (m n : ℤ) :
    (EtaWeilStep.translation (m + n)).phase =
      (EtaWeilStep.translation m).phase *
        (EtaWeilStep.translation n).phase := by
  simp only [EtaWeilStep.phase_translation, Int.cast_add, ← Complex.exp_add]
  congr 1
  ring

/-- The automorphy datum of one integral translation. -/
def EtaWeilAutomorphyWords.translation (n : ℤ) :
    EtaWeilAutomorphyWords :=
  Quotient.mk etaWeilAutomorphySetoid [.translation n]

theorem EtaWeilAutomorphyWords.translation_eq_mk (n : ℤ) :
    translation n = Quotient.mk etaWeilAutomorphySetoid [.translation n] :=
  (rfl)

theorem EtaWeilAutomorphyWords.translation_add (m n : ℤ) :
    (translation m).compose (translation n) = translation (m + n) := by
  change EtaWeilAutomorphyWords.compose
      (Quotient.mk etaWeilAutomorphySetoid [.translation m])
      (Quotient.mk etaWeilAutomorphySetoid [.translation n]) =
      Quotient.mk etaWeilAutomorphySetoid [.translation (m + n)]
  rw [EtaWeilAutomorphyWords.compose_mk]
  apply Quotient.sound
  apply (etaWeilAutomorphySetoid_rel_iff _ _).2
  intro z
  constructor
  · simp only [List.singleton_append, etaWeilWordAction_cons,
      etaWeilWordAction_nil, EtaWeilStep.act_translation]
    rw [← add_vadd]
    norm_cast
  · simp only [List.singleton_append, etaWeilWordFactor_cons,
      etaWeilWordFactor_nil, EtaWeilStep.factor_translation, one_mul, mul_one]

theorem EtaWeilAutomorphyWords.translation_zero :
    translation 0 = identity := by
  change Quotient.mk etaWeilAutomorphySetoid [.translation 0] = identity
  rw [EtaWeilAutomorphyWords.identity_eq_mk]
  apply Quotient.sound
  apply (etaWeilAutomorphySetoid_rel_iff _ _).2
  intro z
  constructor
  · simp only [etaWeilWordAction_cons, etaWeilWordAction_nil,
      EtaWeilStep.act_translation, Int.cast_zero, zero_vadd]
  · simp only [etaWeilWordFactor_cons, etaWeilWordFactor_nil,
      EtaWeilStep.factor_translation, one_mul]

/-- The translation automorphy data have two-sided inverses. -/
theorem EtaWeilAutomorphyWords.translation_inverse (n : ℤ) :
    (translation n).compose (translation (-n)) = identity ∧
      (translation (-n)).compose (translation n) = identity := by
  constructor
  · rw [translation_add, add_neg_cancel, translation_zero]
  · rw [translation_add, neg_add_cancel, translation_zero]

end Theta
end SptClassification
