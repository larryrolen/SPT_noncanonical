/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.ConditionalLambert
public import SptClassification.QuadraticForms.ConditionalSeparation
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Homogeneous Hasse and Serre data for the character obstruction

The algebra below represents meromorphic level-six forms regular at infinity.
Its `forms k` submodule contains the weight-`k` forms whose denominators and
derivatives have the required integral pole clearing at good reduction. The
q-expansion principle is asserted only on one such fixed-weight submodule.
The Shimura Lambert series specifies an independent weight-four lift. The
weight-two logarithmic form is constructed from the oriented CM quotient.
These are explicit good-reduction inputs, not existence assertions. See
[rolenManuscript, Section 4, equations (differential) and (hasse)] and
[katz1973, Sections 2 and 4.3].
-/

@[expose] public section

namespace SptClassification

open QSeries

/-- The homogeneous Serre correction with the manuscript normalization. -/
def hasseTheta {p : ℕ} [Fact p.Prime] {F : Type*}
    [CommRing F] [Algebra (ZMod p) F]
    (H E : F) (D : ℕ → F →ₗ[ZMod p] F) (k : ℕ) (f : F) : F :=
  H * D k f + ((k : ZMod p) / 12) • (E * f)

/-- The defining Serre correction, available to downstream modules without
unfolding the public operator. -/
theorem hasseTheta_apply {p : ℕ} [Fact p.Prime] {F : Type*}
    [CommRing F] [Algebra (ZMod p) F]
    (H E : F) (D : ℕ → F →ₗ[ZMod p] F) (k : ℕ) (f : F) :
    hasseTheta H E D k f = H * D k f + ((k : ZMod p) / 12) • (E * f) := by
  rfl

/-- Explicit good-reduction and homogeneous lift laws for the actual
principal-form series. `forms k` includes regularity at infinity and the
pole-clearing condition at the CM support, including the derivatives.
Its multiplication and Serre laws keep those conditions available for the
two sides of the homogeneous identity. -/
structure HomogeneousHasseInput (p d : ℕ) [Fact p.Prime]
    (F : Type*) [CommRing F] [Algebra (ZMod p) F] where
  forms : ℕ → Submodule (ZMod p) F
  forms_mul : ∀ {k l : ℕ} {f g : F},
    f ∈ forms k → g ∈ forms l → f * g ∈ forms (k + l)
  serre : ℕ → F →ₗ[ZMod p] F
  forms_serre : ∀ {k : ℕ} {f : F}, f ∈ forms k → serre k f ∈ forms (k + 2)
  qexp : F →ₐ[ZMod p] PowerSeries (ZMod p)
  qexp_injective_same_weight : ∀ {k : ℕ} {f g : F},
    f ∈ forms k → g ∈ forms k → qexp f = qexp g → f = g
  H : F
  E : F
  J : F
  H_form : H ∈ forms (p - 1)
  E_form : E ∈ forms (p + 1)
  J_form : J ∈ forms 4
  H_qexp : qexp H = 1
  J_qexp : qexp J = principalShimuraLambertSeries p d
  E_eq_serre_H : E = (12 : ZMod p) • serre (p - 1) H
  /-- The reduction of the weight-`p+1` Eisenstein series is the correction
  series in the Serre derivative. [rolenManuscript, Section 4] -/
  eisensteinTwo : PowerSeries (ZMod p)
  E_qexp : qexp E = eisensteinTwo
  /-- The ordinary Serre q-expansion law with `Dₖ = Θ-kE₂/12`.
  [rolenManuscript, Section 2 and Section 4] -/
  serre_qexp : ∀ {k : ℕ} {f : F}, f ∈ forms k →
    qexp (serre k f) = eulerDerivative (qexp f) -
      ((k : ZMod p) / 12) • (eisensteinTwo * qexp f)

/-- The Hasse correction cancels the Serre correction at the cusp. This is
the q-expansion calculation in [rolenManuscript, Section 4] rather than
an independent geometric premise. -/
theorem HomogeneousHasseInput.theta_qexp {p d : ℕ} [Fact p.Prime]
    {F : Type*} [CommRing F] [Algebra (ZMod p) F]
    (I : HomogeneousHasseInput p d F) {k : ℕ} {f : F}
    (hf : f ∈ I.forms k) :
    I.qexp (hasseTheta I.H I.E I.serre k f) =
      eulerDerivative (I.qexp f) := by
  rw [hasseTheta_apply, map_add, map_mul, I.H_qexp, one_mul,
    I.serre_qexp hf, map_smul, map_mul, I.E_qexp]
  simp only [Algebra.smul_def]
  ring

/-- Fixed-weight q-expansion injectivity extends from holomorphic forms to
meromorphic forms after clearing the poles of both forms by one nonzero
factor. The common factor may depend on the pair, but its product with each
form must have the same holomorphic weight. This is the algebraic deduction
used with the holomorphic q-expansion principle and the manuscript's CM pole
clearing. [katz1973, Section 2] [rolenManuscript, proof of Proposition 4.1] -/
theorem qexp_injective_of_common_pole_clearing
    {R F : Type*} [CommRing R] [CommRing F] [NoZeroDivisors F]
    (qexp : F →+* PowerSeries R)
    (holomorphic meromorphic : ℕ → Set F)
    (hholomorphic : ∀ (w : ℕ) {f g : F},
      f ∈ holomorphic w → g ∈ holomorphic w →
      qexp f = qexp g → f = g)
    (hclear : ∀ (k : ℕ) {f g : F},
      f ∈ meromorphic k → g ∈ meromorphic k →
      ∃ (c : F) (w : ℕ), c ≠ 0 ∧
        c * f ∈ holomorphic w ∧ c * g ∈ holomorphic w)
    (k : ℕ) {f g : F}
    (hf : f ∈ meromorphic k) (hg : g ∈ meromorphic k)
    (heq : qexp f = qexp g) : f = g := by
  obtain ⟨c, w, hc, hcf, hcg⟩ := hclear k hf hg
  have hq : qexp (c * f) = qexp (c * g) := by
    rw [map_mul, map_mul, heq]
  exact mul_left_cancel₀ hc (hholomorphic w hcf hcg hq)

/-- An integral q-expansion detects membership in a lattice once reduction
modulo the uniformizer is injective on that lattice. `hmodq` is the precise
divisibility consequence of the special-fiber q-expansion principle: a lattice
section whose expansion is divisible by `π` is itself divisible by `π` in the
lattice. The generic section must already have a bounded denominator in the
lattice; this lemma does not assert that its poles have been cleared globally.
[katz1973, Section 2] -/
theorem integral_lattice_of_integral_qexp
    {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W]
    (π : R) (M : Submodule R V) (S : Submodule R W)
    (qexp : V →ₗ[R] W)
    (hπ : ∀ u v : V, π • u = π • v → u = v)
    (hmodq : ∀ m : V, m ∈ M →
      (∃ s ∈ S, qexp m = π • s) →
      ∃ m' ∈ M, m = π • m')
    (x : V) (hdenom : ∃ n : ℕ, (π ^ n) • x ∈ M)
    (hq : qexp x ∈ S) : x ∈ M := by
  obtain ⟨n, hn⟩ := hdenom
  induction n with
  | zero => simpa using hn
  | succ n ih =>
      have hqdiv : ∃ s ∈ S, qexp ((π ^ (n + 1)) • x) = π • s := by
        refine ⟨(π ^ n) • qexp x, S.smul_mem _ hq, ?_⟩
        calc
          qexp ((π ^ (n + 1)) • x) = ((π ^ n) * π) • qexp x := by
            rw [map_smul, pow_succ]
          _ = (π * (π ^ n)) • qexp x := by rw [mul_comm]
          _ = π • ((π ^ n) • qexp x) := mul_smul _ _ _
      obtain ⟨m', hm', heq⟩ := hmodq _ hn hqdiv
      have hprev : (π ^ n) • x ∈ M := by
        have hpow : (π ^ (n + 1)) • x = π • ((π ^ n) • x) := by
          calc
            (π ^ (n + 1)) • x = ((π ^ n) * π) • x := by rw [pow_succ]
            _ = (π * (π ^ n)) • x := by rw [mul_comm]
            _ = π • ((π ^ n) • x) := mul_smul _ _ _
        have hcancel : π • ((π ^ n) • x) = π • m' := by
          rw [← hpow]
          exact heq
        exact (hπ _ _ hcancel) ▸ hm'
      exact ih hprev

/-- The Serre correction is homogeneous and satisfies the supplied
good-reduction/pole-clearing conditions. -/
theorem HomogeneousHasseInput.theta_form {p d : ℕ} [Fact p.Prime]
    {F : Type*} [CommRing F] [Algebra (ZMod p) F]
    (I : HomogeneousHasseInput p d F) {k : ℕ} {f : F}
    (hf : f ∈ I.forms k) :
    hasseTheta I.H I.E I.serre k f ∈ I.forms (k + p + 1) := by
  have hleft : I.H * I.serre k f ∈ I.forms (k + p + 1) := by
    have h := I.forms_mul I.H_form (I.forms_serre hf)
    have heq : p - 1 + (k + 2) = k + p + 1 := by
      have hp : 1 ≤ p := (Fact.out : p.Prime).one_le
      omega
    simpa only [heq] using h
  have hright : I.E * f ∈ I.forms (k + p + 1) := by
    have h := I.forms_mul I.E_form hf
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  exact (I.forms (k + p + 1)).add_mem hleft
    ((I.forms (k + p + 1)).smul_mem _ hright)

/-- The Lambert differential identity lifts for independently constructed
weight-two and weight-four forms with the prescribed expansions. The
fixed-weight q-expansion principle compares both sides in weight `2p+4`.
[rolenManuscript, Section 4, equation (hasse)] -/
theorem HomogeneousHasseInput.homogeneous_lambert_identity_of_forms
    {p d : ℕ} [Fact p.Prime]
    {F : Type*} [CommRing F] [Algebra (ZMod p) F]
    (I : HomogeneousHasseInput p d F)
    (L J : F) (hL : L ∈ I.forms 2) (hJ : J ∈ I.forms 4)
    (hLq : I.qexp L = principalLogarithmicLambertSeries p d)
    (hJq : I.qexp J = principalShimuraLambertSeries p d)
    (hdiff : eulerDerivative (eulerDerivative
      (principalLogarithmicLambertSeries p d)) =
        PowerSeries.C (d : ZMod p) *
          eulerDerivative (principalShimuraLambertSeries p d)) :
    hasseTheta I.H I.E I.serre (p + 3)
        (hasseTheta I.H I.E I.serre 2 L) =
      (d : ZMod p) • (I.H * hasseTheta I.H I.E I.serre 4 J) := by
  have hthetaL : hasseTheta I.H I.E I.serre 2 L ∈ I.forms (p + 3) := by
    have h := I.theta_form hL
    have heq : 2 + p + 1 = p + 3 := by omega
    simpa only [heq] using h
  have hleft : hasseTheta I.H I.E I.serre (p + 3)
      (hasseTheta I.H I.E I.serre 2 L) ∈ I.forms (2 * p + 4) := by
    have h := I.theta_form hthetaL
    have heq : (p + 3) + p + 1 = 2 * p + 4 := by omega
    simpa only [heq] using h
  have hthetaJ : hasseTheta I.H I.E I.serre 4 J ∈ I.forms (p + 5) := by
    have h := I.theta_form hJ
    have heq : 4 + p + 1 = p + 5 := by omega
    simpa only [heq] using h
  have hright : (d : ZMod p) •
      (I.H * hasseTheta I.H I.E I.serre 4 J) ∈ I.forms (2 * p + 4) := by
    have hmul := I.forms_mul I.H_form hthetaJ
    have heq : p - 1 + (p + 5) = 2 * p + 4 := by
      have hp : 1 ≤ p := (Fact.out : p.Prime).one_le
      omega
    rw [heq] at hmul
    exact (I.forms (2 * p + 4)).smul_mem _ hmul
  apply I.qexp_injective_same_weight hleft hright
  rw [I.theta_qexp hthetaL, I.theta_qexp hL,
    map_smul, map_mul, I.H_qexp, one_mul, I.theta_qexp hJ,
    hLq, hJq]
  have hC : (algebraMap (ZMod p) (PowerSeries (ZMod p))) (d : ZMod p) =
      PowerSeries.C (d : ZMod p) := by rfl
  simpa only [Algebra.smul_def, hC] using hdiff

end SptClassification
