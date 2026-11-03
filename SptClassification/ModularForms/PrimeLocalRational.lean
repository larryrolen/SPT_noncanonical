/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.AnalyticNormalizedProduct
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Rational coefficients with a specified prime-local reduction

A rational number has a reduction modulo a prime when it has a denominator
prime to that prime. Keeping the rational coefficient and its residue in one
relation lets finite Fourier convolutions be reduced without assigning a
nonexistent map from all of `ℚ` to `ZMod p`.
-/

public section

namespace SptClassification

/-- A rational coefficient and its faithful reduction at a prime. -/
def RationalReduces (p : ℕ) (q : ℚ) (z : ZMod p) : Prop :=
  ∃ num den : ℤ, ¬(p : ℤ) ∣ den ∧
    q = (num : ℚ) / den ∧ z * (den : ZMod p) = (num : ZMod p)

/-- Recover both the denominator and its residue equation for a concrete
modular-form coefficient record. -/
theorem RationalReduces.witnesses {p : ℕ} {q : ℚ} {z : ZMod p}
    (h : RationalReduces p q z) :
    ∃ num den : ℤ, ¬(p : ℤ) ∣ den ∧
      q = (num : ℚ) / den ∧ z * (den : ZMod p) = (num : ZMod p) := h

/-- Forget the specified residue, retaining a denominator prime to `p`. -/
theorem RationalReduces.exists_denominator {p : ℕ} {q : ℚ} {z : ZMod p}
    (h : RationalReduces p q z) :
    ∃ num den : ℤ, ¬(p : ℤ) ∣ den ∧ q = (num : ℚ) / den := by
  obtain ⟨num, den, hd, hq, _⟩ := h
  exact ⟨num, den, hd, hq⟩

/-- Supply a denominator prime to `p` and the corresponding residue
identity to construct a prime-local rational reduction. -/
theorem RationalReduces.ofFraction (p : ℕ) (num den : ℤ)
    (hden : ¬(p : ℤ) ∣ den) (z : ZMod p)
    (hz : z * (den : ZMod p) = (num : ZMod p)) :
    RationalReduces p ((num : ℚ) / den) z := by
  exact ⟨num, den, hden, rfl, hz⟩

theorem RationalReduces.intCast (p : ℕ) [Fact p.Prime] (n : ℤ) :
    RationalReduces p (n : ℚ) (n : ZMod p) := by
  refine ⟨n, 1, ?_, by norm_num, ?_⟩
  · intro h
    have hp : p ∣ 1 := by exact_mod_cast h
    have : p = 1 := Nat.dvd_one.mp hp
    exact (Fact.out : p.Prime).ne_one this
  · simp

theorem RationalReduces.neg {p : ℕ} {q : ℚ} {z : ZMod p}
    (h : RationalReduces p q z) : RationalReduces p (-q) (-z) := by
  obtain ⟨num, den, hd, hq, hz⟩ := h
  refine ⟨-num, den, hd, ?_, ?_⟩
  · rw [hq]
    push_cast
    ring
  · push_cast
    rw [← hz]
    ring

private theorem rationalReduces_den_ne_zero {p : ℕ} [Fact p.Prime]
    {den : ℤ} (hden : ¬(p : ℤ) ∣ den) : den ≠ 0 := by
  intro h
  subst den
  exact hden (dvd_zero _)

private theorem rationalReduces_den_mod_ne_zero {p : ℕ} [Fact p.Prime]
    {den : ℤ} (hden : ¬(p : ℤ) ∣ den) : (den : ZMod p) ≠ 0 := by
  intro h
  exact hden ((ZMod.intCast_zmod_eq_zero_iff_dvd den p).mp h)

/-- Reduction is compatible with a finite sum of prime-local rationals. -/
theorem RationalReduces.add {p : ℕ} [Fact p.Prime]
    {q₁ q₂ : ℚ} {z₁ z₂ : ZMod p}
    (h₁ : RationalReduces p q₁ z₁)
    (h₂ : RationalReduces p q₂ z₂) :
    RationalReduces p (q₁ + q₂) (z₁ + z₂) := by
  obtain ⟨n₁, d₁, hd₁, hq₁, hz₁⟩ := h₁
  obtain ⟨n₂, d₂, hd₂, hq₂, hz₂⟩ := h₂
  have hd₁q : (d₁ : ℚ) ≠ 0 := by exact_mod_cast rationalReduces_den_ne_zero hd₁
  have hd₂q : (d₂ : ℚ) ≠ 0 := by exact_mod_cast rationalReduces_den_ne_zero hd₂
  have hdprod : ¬(p : ℤ) ∣ d₁ * d₂ := by
    intro h
    have hz : (d₁ : ZMod p) * d₂ = 0 := by
      rw [← Int.cast_mul]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (d₁ * d₂) p).mpr h
    exact (mul_ne_zero (rationalReduces_den_mod_ne_zero hd₁)
      (rationalReduces_den_mod_ne_zero hd₂)) hz
  refine ⟨n₁ * d₂ + n₂ * d₁, d₁ * d₂, hdprod, ?_, ?_⟩
  · rw [hq₁, hq₂]
    push_cast
    field_simp
  · push_cast
    calc
      (z₁ + z₂) * ((d₁ : ZMod p) * d₂) =
          (z₁ * d₁) * d₂ + (z₂ * d₂) * d₁ := by ring
      _ = (n₁ : ZMod p) * d₂ + (n₂ : ZMod p) * d₁ := by rw [hz₁, hz₂]

/-- Reduction is compatible with multiplication. -/
theorem RationalReduces.mul {p : ℕ} [Fact p.Prime]
    {q₁ q₂ : ℚ} {z₁ z₂ : ZMod p}
    (h₁ : RationalReduces p q₁ z₁)
    (h₂ : RationalReduces p q₂ z₂) :
    RationalReduces p (q₁ * q₂) (z₁ * z₂) := by
  obtain ⟨n₁, d₁, hd₁, hq₁, hz₁⟩ := h₁
  obtain ⟨n₂, d₂, hd₂, hq₂, hz₂⟩ := h₂
  have hd₁q : (d₁ : ℚ) ≠ 0 := by exact_mod_cast rationalReduces_den_ne_zero hd₁
  have hd₂q : (d₂ : ℚ) ≠ 0 := by exact_mod_cast rationalReduces_den_ne_zero hd₂
  have hdprod : ¬(p : ℤ) ∣ d₁ * d₂ := by
    intro h
    have hz : (d₁ : ZMod p) * d₂ = 0 := by
      rw [← Int.cast_mul]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (d₁ * d₂) p).mpr h
    exact (mul_ne_zero (rationalReduces_den_mod_ne_zero hd₁)
      (rationalReduces_den_mod_ne_zero hd₂)) hz
  refine ⟨n₁ * n₂, d₁ * d₂, hdprod, ?_, ?_⟩
  · rw [hq₁, hq₂]
    push_cast
    field_simp
  · push_cast
    calc
      (z₁ * z₂) * ((d₁ : ZMod p) * d₂) =
          (z₁ * d₁) * (z₂ * d₂) := by ring
      _ = (n₁ : ZMod p) * n₂ := by rw [hz₁, hz₂]

theorem RationalReduces.sub {p : ℕ} [Fact p.Prime]
    {q₁ q₂ : ℚ} {z₁ z₂ : ZMod p}
    (h₁ : RationalReduces p q₁ z₁)
    (h₂ : RationalReduces p q₂ z₂) :
    RationalReduces p (q₁ - q₂) (z₁ - z₂) := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg

theorem RationalReduces.finset_sum {p : ℕ} [Fact p.Prime]
    {α : Type*} (s : Finset α) (q : α → ℚ) (z : α → ZMod p)
    (h : ∀ a ∈ s, RationalReduces p (q a) (z a)) :
    RationalReduces p (∑ a ∈ s, q a) (∑ a ∈ s, z a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using RationalReduces.intCast p 0
  | @insert a s ha ih =>
      simpa only [Finset.sum_insert ha] using (h a (Finset.mem_insert_self a s)).add
        (ih (by intro b hb; exact h b (Finset.mem_insert_of_mem hb)))

/-- A rational number has at most one residue at a specified prime. -/
theorem RationalReduces.unique {p : ℕ} [Fact p.Prime]
    {q : ℚ} {z₁ z₂ : ZMod p}
    (h₁ : RationalReduces p q z₁)
    (h₂ : RationalReduces p q z₂) : z₁ = z₂ := by
  obtain ⟨n₁, d₁, hd₁, hq₁, hz₁⟩ := h₁
  obtain ⟨n₂, d₂, hd₂, hq₂, hz₂⟩ := h₂
  have hd₁q : (d₁ : ℚ) ≠ 0 := by exact_mod_cast rationalReduces_den_ne_zero hd₁
  have hd₂q : (d₂ : ℚ) ≠ 0 := by exact_mod_cast rationalReduces_den_ne_zero hd₂
  have hcross : n₁ * d₂ = n₂ * d₁ := by
    have hq : (n₁ : ℚ) / d₁ = (n₂ : ℚ) / d₂ := hq₁.symm.trans hq₂
    have hc : (n₁ : ℚ) * d₂ = (n₂ : ℚ) * d₁ :=
      (div_eq_div_iff hd₁q hd₂q).mp hq
    exact_mod_cast hc
  have hcrossMod : (n₁ : ZMod p) * d₂ = (n₂ : ZMod p) * d₁ := by
    have h := congrArg (fun n : ℤ => (n : ZMod p)) hcross
    simpa only [Int.cast_mul] using h
  have heq : z₁ * ((d₁ : ZMod p) * d₂) = z₂ * ((d₁ : ZMod p) * d₂) := by
    calc
      z₁ * ((d₁ : ZMod p) * d₂) = (n₁ : ZMod p) * d₂ := by rw [← mul_assoc, hz₁]
      _ = (n₂ : ZMod p) * d₁ := hcrossMod
      _ = z₂ * ((d₁ : ZMod p) * d₂) := by rw [← hz₂]; ring
  exact mul_right_cancel₀
    (mul_ne_zero (rationalReduces_den_mod_ne_zero hd₁)
      (rationalReduces_den_mod_ne_zero hd₂)) heq

/-- Clear a finite pole in a row of residue coefficients. -/
noncomputable def poleClearedModularRow (p : ℕ)
    (a : ℤ → ZMod p) (M : ℕ) : PowerSeries (ZMod p) :=
  PowerSeries.mk (fun n => a ((n : ℤ) - M))

@[simp] theorem poleClearedModularRow_coeff (p : ℕ)
    (a : ℤ → ZMod p) (M n : ℕ) :
    (poleClearedModularRow p a M).coeff n = a ((n : ℤ) - M) := by
  simp [poleClearedModularRow]

/-- The finite Cauchy coefficient of two pole-cleared reduced Laurent rows.
The cutoff and index shift are identical to `rationalLaurentProductRow`. -/
noncomputable def modularLaurentProductRow (p : ℕ)
    (a b : ℤ → ZMod p) (M N : ℕ) (r : ℤ) : ZMod p :=
  if r < -((M + N : ℕ) : ℤ) then 0 else
    ((poleClearedModularRow p a M * poleClearedModularRow p b N).coeff
      (r + (M + N : ℕ)).toNat)

theorem modularLaurentProductRow_zero_below (p : ℕ)
    (a b : ℤ → ZMod p) (M N : ℕ) (r : ℤ)
    (hr : r < -((M + N : ℕ) : ℤ)) :
    modularLaurentProductRow p a b M N r = 0 := by
  simp only [modularLaurentProductRow, if_pos hr]

theorem modularLaurentProductRow_eq_coeff (p : ℕ)
    (a b : ℤ → ZMod p) (M N : ℕ) (r : ℤ)
    (hr : ¬ r < -((M + N : ℕ) : ℤ)) :
    modularLaurentProductRow p a b M N r =
      (poleClearedModularRow p a M * poleClearedModularRow p b N).coeff
        (r + (M + N : ℕ)).toNat := by
  simp only [modularLaurentProductRow, if_neg hr]

/-- Prime-local coefficient reduction commutes with the actual finite
Laurent Cauchy product, with no restriction on the pole orders. -/
theorem rationalLaurentProductRow_reduces
    {p : ℕ} [Fact p.Prime]
    (a b : ℤ → ℚ) (aMod bMod : ℤ → ZMod p) (M N : ℕ)
    (ha : ∀ r, RationalReduces p (a r) (aMod r))
    (hb : ∀ r, RationalReduces p (b r) (bMod r)) (r : ℤ) :
    RationalReduces p (rationalLaurentProductRow a b M N r)
      (modularLaurentProductRow p aMod bMod M N r) := by
  by_cases hr : r < -((M + N : ℕ) : ℤ)
  · rw [rationalLaurentProductRow_zero_below a b M N r hr]
    have hmod : modularLaurentProductRow p aMod bMod M N r = 0 := by
      simp only [modularLaurentProductRow, if_pos hr]
    rw [hmod]
    simpa using RationalReduces.intCast p 0
  · simp only [modularLaurentProductRow, if_neg hr,
      rationalLaurentProductRow_eq_sum a b M N r hr, PowerSeries.coeff_mul,
      poleClearedModularRow_coeff]
    apply RationalReduces.finset_sum
    intro ij hij
    exact (ha _).mul (hb _)

/-- The analytic Fourier comparison can be combined with a genuinely
prime-local reduction of its rational coefficient. -/
theorem SptModularApproximation.coeffMod_eq_of_normalizedRow_reduces
    {p Q : ℕ} {hfive : 5 ≤ p} [Fact p.Prime] [Fact Q.Prime]
    (A : SptModularApproximation p Q hfive) (r : ℤ) (z : ZMod p)
    (h : RationalReduces p (normalizedRepresentativeRationalRow p Q r) z) :
    A.form.coeffMod r = z := by
  have hform : RationalReduces p (A.form.coeff r) (A.form.coeffMod r) :=
    A.form.pIntegral r
  rw [A.form_coeff_eq_normalizedRepresentative_all r] at hform
  exact RationalReduces.unique hform h

end SptClassification
