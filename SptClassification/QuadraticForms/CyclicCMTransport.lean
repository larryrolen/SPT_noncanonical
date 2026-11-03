/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.OrientedEndomorphisms
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Algebra.Group.Hom.End
import Mathlib.Tactic.Ring

/-!
# Orientation scalars on cyclic subgroups

An isomorphism of elliptic pairs identifies cyclic subgroups, not chosen
points. Scalar action on a generator therefore has to be transported to
any point of the image subgroup. These elementary deductions support
[rolenManuscript, Lemma `lem:separation`]; they do not supply algebraic
CM specialization or an identification of reduced elliptic pairs.
-/

public section

namespace SptClassification

/-- Scalar action on a generator determines the action on its cyclic subgroup. -/
theorem scalar_action_on_zmultiples
    {G : Type*} [AddCommGroup G] (f : G →+ G) (P : G) (m : ℤ)
    (hf : f P = m • P) (x : G) (hx : x ∈ AddSubgroup.zmultiples P) :
    f x = m • x := by
  obtain ⟨k, rfl⟩ := hx
  rw [map_zsmul, hf, smul_comm]

/-- An equivariant map transports the scalar to every point of the image
cyclic subgroup. No matching of chosen generators is required. -/
theorem scalar_action_on_cyclic_image
    {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (f : G →+ G) (g : H →+ H) (e : G →+ H) (P : G) (m : ℤ)
    (hf : f P = m • P)
    (he : ∀ x ∈ AddSubgroup.zmultiples P, g (e x) = e (f x))
    (y : H) (hy : y ∈ (AddSubgroup.zmultiples P).map e) :
    g y = m • y := by
  obtain ⟨x, hx, rfl⟩ := hy
  rw [he x hx, scalar_action_on_zmultiples f P m hf x hx, map_zsmul]

/-- A pair isomorphism preserves orientation scalars even when it changes
which generator is chosen for the level subgroup. -/
theorem scalar_action_of_cyclic_pair_equiv
    {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (f : G →+ G) (g : H →+ H) (e : G ≃+ H) (P : G) (Q : H) (m : ℤ)
    (hf : f P = m • P)
    (he : ∀ x ∈ AddSubgroup.zmultiples P, g (e x) = e (f x))
    (hpair : (AddSubgroup.zmultiples P).map e.toAddMonoidHom =
      AddSubgroup.zmultiples Q) :
    g Q = m • Q := by
  apply scalar_action_on_cyclic_image f g e.toAddMonoidHom P m hf he Q
  rw [hpair]
  exact ⟨1, one_zsmul Q⟩

/-- The orientation contradiction can be detected on one point of exact
order six. The ring is the algebraic endomorphism ring in applications;
its action on points is a ring map, with no faithfulness assumption needed. -/
theorem oriented_point_actions_not_commute
    {O G : Type*} [Ring O] [NoZeroDivisors O] [AddCommGroup G]
    (act : O →+* AddMonoid.End G) (a b c : O) (P : G)
    (horder : addOrderOf P = 6)
    (ha : a * a - a + c = 0) (hb : b * b - b + c = 0)
    (m n : ℤ) (ham : act a P = m • P) (hbn : act b P = n • P)
    (hm : m % 6 = 0 ∨ m % 6 = 1)
    (hn : n % 6 = 3 ∨ n % 6 = 4) : a * b ≠ b * a := by
  intro hcomm
  rcases commuting_quadratic_eq_or_eq_one_sub a b c ha hb hcomm with h | h
  · have heq : n • P = m • P := by rw [← hbn, ← ham, h]
    have hmod := zsmul_eq_zsmul_iff_modEq.mp heq
    rw [horder] at hmod
    change n % 6 = m % 6 at hmod
    omega
  · have heq : n • P = (1 - m) • P := by
      rw [← hbn, h, map_sub, map_one]
      change P - act a P = (1 - m) • P
      rw [ham, sub_zsmul, one_zsmul]
      simp only [sub_eq_add_neg]
    have hmod := zsmul_eq_zsmul_iff_modEq.mp heq
    rw [horder] at hmod
    change n % 6 = (1 - m) % 6 at hmod
    omega


/-- Two equivariant images identifying the same cyclic subgroup give the
orientation contradiction, even with different source generators. In good
reduction applications the source groups may be finite prime-to-p torsion;
no reduction map on all complex points is assumed. -/
theorem oriented_cyclic_images_not_commute
    {O G H₁ H₂ : Type*} [Ring O] [NoZeroDivisors O]
    [AddCommGroup G] [AddCommGroup H₁] [AddCommGroup H₂]
    (act : O →+* AddMonoid.End G) (a b c : O) (P : G)
    (horder : addOrderOf P = 6)
    (ha : a * a - a + c = 0) (hb : b * b - b + c = 0)
    (f₁ : H₁ →+ H₁) (f₂ : H₂ →+ H₂) (P₁ : H₁) (P₂ : H₂)
    (e₁ : H₁ →+ G) (e₂ : H₂ →+ G) (m n : ℤ)
    (hf₁ : f₁ P₁ = m • P₁) (hf₂ : f₂ P₂ = n • P₂)
    (he₁ : ∀ x ∈ AddSubgroup.zmultiples P₁, act a (e₁ x) = e₁ (f₁ x))
    (he₂ : ∀ x ∈ AddSubgroup.zmultiples P₂, act b (e₂ x) = e₂ (f₂ x))
    (hpair₁ : (AddSubgroup.zmultiples P₁).map e₁ = AddSubgroup.zmultiples P)
    (hpair₂ : (AddSubgroup.zmultiples P₂).map e₂ = AddSubgroup.zmultiples P)
    (hm : m % 6 = 0 ∨ m % 6 = 1)
    (hn : n % 6 = 3 ∨ n % 6 = 4) : a * b ≠ b * a := by
  have hP : P ∈ AddSubgroup.zmultiples P := ⟨1, one_zsmul P⟩
  have ham : act a P = m • P :=
    scalar_action_on_cyclic_image f₁ (act a) e₁ P₁ m hf₁ he₁ P
      (hpair₁.symm ▸ hP)
  have hbn : act b P = n • P :=
    scalar_action_on_cyclic_image f₂ (act b) e₂ P₂ n hf₂ he₂ P
      (hpair₂.symm ▸ hP)
  exact oriented_point_actions_not_commute act a b c P horder ha hb m n ham hbn hm hn

/-- All-prime manuscript bound from genuine endomorphisms acting on a common
point of order six. Ordinary commutativity rules out the ordinary branch;
[rolen2026canonical, Lemma 5.2] supplies the supersingular degree estimate.
Construction and specialization of the algebraic actions remain separate. -/
theorem oriented_point_actions_force_prime_bound
    {O G : Type*} [Ring O] [NoZeroDivisors O] [AddCommGroup G]
    (act : O →+* AddMonoid.End G) (a b : O) (P : G)
    (horder : addOrderOf P = 6) (d p N : ℕ) (hN : 4 * N = d + 1)
    (ha : a * a - a + (N : O) = 0) (hb : b * b - b + (N : O) = 0)
    (m n : ℤ) (ham : act a P = m • P) (hbn : act b P = n • P)
    (hm : m % 6 = 0 ∨ m % 6 = 1)
    (hn : n % 6 = 3 ∨ n % 6 = 4)
    (ordinary : Prop) (hordinary : ordinary → a * b = b * a)
    (hsupersingular : ¬ordinary → a * b ≠ b * a → 6 * p ≤ 4 * N * N) :
    24 * p ≤ (d + 1) ^ 2 := by
  have hnoncomm := oriented_point_actions_not_commute act a b (N : O) P
    horder ha hb m n ham hbn hm hn
  have hdegree := hsupersingular (fun h => hnoncomm (hordinary h)) hnoncomm
  calc
    24 * p = 4 * (6 * p) := by ring
    _ ≤ 4 * (4 * N * N) := Nat.mul_le_mul_left 4 hdegree
    _ = (d + 1) ^ 2 := by rw [← hN]; ring

end SptClassification
