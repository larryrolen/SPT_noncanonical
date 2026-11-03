/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.EtaHecke

/-!
# Shadow cancellation through repeated Hecke operators

The single-prime shadow identity of [rolen2026canonical, Lemma 2.4] can be
iterated only after the weakly holomorphic correction space is known to be
stable under each Hecke operator. This file proves the coefficient-level
induction, including repeated primes. Analytic modularity and Hecke stability
are separate inputs.
-/

public section

namespace SptClassification.QSeries

/-- The eigenvalue obtained by iterating the single-prime shadow relation of
[rolen2026canonical, Lemma 2.4], with repeated prime factors retained. -/
def heckeShadowEigenvalue (n : ℕ) : ℤ :=
  (n.primeFactorsList.map fun (q : ℕ) =>
    characterTwelve (q : ℤ) * (1 + (q : ℤ))).prod

/-- The empty factor list has shadow eigenvalue one. -/
theorem heckeShadowEigenvalue_one : heckeShadowEigenvalue 1 = 1 := by
  simp [heckeShadowEigenvalue]

/-- The function-space scalar action agrees with pointwise multiplication
in the Hecke-word identity. -/
theorem heckeThreeHalfWord_smul_fun (ps : List ℕ) (c : ℚ) (A : ℤ → ℚ) :
    heckeThreeHalfWord ps (c • A) = c • heckeThreeHalfWord ps A := by
  funext r
  change heckeThreeHalfWord ps (fun r => c * A r) r =
    c * heckeThreeHalfWord ps A r
  exact congrFun (heckeThreeHalfWord_smul ps c A) r

/-- The one-prime operator is linear for the function-space scalar action. -/
theorem heckeThreeHalf_smul_fun (p : ℕ) (c : ℚ) (A : ℤ → ℚ) :
    heckeThreeHalf p (c • A) = c • heckeThreeHalf p A := by
  funext r
  change heckeThreeHalf p (fun r => c * A r) r =
    c * heckeThreeHalf p A r
  exact congrFun (heckeThreeHalf_smul p c A) r

/-- Every prime in the factor list of an integer coprime to six is at least
five, including when the list contains repeated factors. -/
theorem primeFactorsList_prime_five (n : ℕ) (hn : 0 < n)
    (hc : n.Coprime 6) :
    ∀ p ∈ n.primeFactorsList, p.Prime ∧ 5 ≤ p := by
  intro p hp
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactorsList hp
  have hpDiv : p ∣ n := by
    rw [← Nat.prod_primeFactorsList (Nat.ne_of_gt hn)]
    exact List.dvd_prod hp
  have hpCop : p.Coprime 6 := Nat.Coprime.of_dvd_left hpDiv hc
  have hpTwo : p ≠ 2 := by
    intro h
    subst p
    norm_num at hpCop
  have hpThree : p ≠ 3 := by
    intro h
    subst p
    norm_num at hpCop
  have hpFour : p ≠ 4 := by
    intro h
    subst p
    exact (by decide : ¬ Nat.Prime 4) hpPrime
  exact ⟨hpPrime, by have := hpPrime.two_le; omega⟩

/-- The weight `3/2` coefficient action is additive. -/
theorem heckeThreeHalf_add (p : ℕ) (A B : ℤ → ℚ) :
    heckeThreeHalf p (A + B) = heckeThreeHalf p A + heckeThreeHalf p B := by
  funext r
  simp only [heckeThreeHalf_eq_squareHecke, squareHecke_apply,
    Pi.add_apply, squareDown_apply]
  split_ifs <;> ring

/-- The weight `3/2` coefficient action commutes with subtraction. -/
theorem heckeThreeHalf_sub (p : ℕ) (A B : ℤ → ℚ) :
    heckeThreeHalf p (A - B) = heckeThreeHalf p A - heckeThreeHalf p B := by
  funext r
  simp only [heckeThreeHalf_eq_squareHecke, squareHecke_apply,
    Pi.sub_apply, squareDown_apply]
  split_ifs <;> ring

/-- The coefficient Hecke operator sends the zero row to zero. -/
theorem heckeThreeHalf_zero (p : ℕ) :
    heckeThreeHalf p (0 : ℤ → ℚ) = 0 := by
  funext r
  simp only [heckeThreeHalf_eq_squareHecke, squareHecke_apply,
    Pi.zero_apply, zero_mul, add_zero, squareDown_apply]
  split_ifs <;> simp

/-- A Hecke word remains additive, including when a prime is repeated. -/
theorem heckeThreeHalfWord_add (ps : List ℕ) (A B : ℤ → ℚ) :
    heckeThreeHalfWord ps (A + B) =
      heckeThreeHalfWord ps A + heckeThreeHalfWord ps B := by
  induction ps generalizing A B with
  | nil => simp only [heckeThreeHalfWord_nil]
  | cons p ps ih =>
    simpa only [heckeThreeHalfWord_cons, heckeThreeHalf_add] using
      ih (heckeThreeHalf p A) (heckeThreeHalf p B)

/-- A Hecke word commutes with subtraction. -/
theorem heckeThreeHalfWord_sub (ps : List ℕ) (A B : ℤ → ℚ) :
    heckeThreeHalfWord ps (A - B) =
      heckeThreeHalfWord ps A - heckeThreeHalfWord ps B := by
  induction ps generalizing A B with
  | nil => simp only [heckeThreeHalfWord_nil]
  | cons p ps ih =>
    simpa only [heckeThreeHalfWord_cons, heckeThreeHalf_sub] using
      ih (heckeThreeHalf p A) (heckeThreeHalf p B)

/-- A Hecke word preserves a coefficient submodule when each letter does. -/
theorem heckeThreeHalfWord_mem {W : Submodule ℚ (ℤ → ℚ)}
    {ps : List ℕ} (hstable : ∀ p ∈ ps, ∀ A ∈ W, heckeThreeHalf p A ∈ W)
    {A : ℤ → ℚ} (hA : A ∈ W) : heckeThreeHalfWord ps A ∈ W := by
  induction ps generalizing A with
  | nil => simpa only [heckeThreeHalfWord_nil] using hA
  | cons p ps ih =>
    rw [heckeThreeHalfWord_cons]
    apply ih (A := heckeThreeHalf p A)
    · intro q hq B hB
      exact hstable q (by simp [hq]) B hB
    · exact hstable p (by simp) A hA

/-- Single-prime shadow cancellation propagates through an arbitrary Hecke
word. The input `W` is the coefficient space of holomorphic corrections;
its Hecke stability is a distinct analytic claim. -/
theorem heckeThreeHalfWord_shadow_mem
    (W : Submodule ℚ (ℤ → ℚ)) (F : ℤ → ℚ) (eigenvalue : ℕ → ℚ)
    (ps : List ℕ)
    (hsingle : ∀ p ∈ ps,
      heckeThreeHalf p F - eigenvalue p • F ∈ W)
    (hstable : ∀ p ∈ ps, ∀ A ∈ W, heckeThreeHalf p A ∈ W) :
    heckeThreeHalfWord ps F - (ps.map eigenvalue).prod • F ∈ W := by
  induction ps with
  | nil =>
    simpa only [heckeThreeHalfWord_nil, List.map_nil, List.prod_nil,
      one_smul, sub_self] using W.zero_mem
  | cons p ps ih =>
    have hsinglep : heckeThreeHalf p F - eigenvalue p • F ∈ W :=
      hsingle p (by simp)
    have htail : heckeThreeHalfWord ps F - (ps.map eigenvalue).prod • F ∈ W := by
      apply ih
      · intro q hq
        exact hsingle q (by simp [hq])
      · intro q hq A hA
        exact hstable q (by simp [hq]) A hA
    have hstableTail :
        heckeThreeHalfWord ps (heckeThreeHalf p F - eigenvalue p • F) ∈ W := by
      apply heckeThreeHalfWord_mem ?_ hsinglep
      intro q hq A hA
      exact hstable q (by simp [hq]) A hA
    have heq :
        heckeThreeHalfWord (p :: ps) F -
            ((p :: ps).map eigenvalue).prod • F =
          heckeThreeHalfWord ps (heckeThreeHalf p F - eigenvalue p • F) +
            eigenvalue p •
              (heckeThreeHalfWord ps F - (ps.map eigenvalue).prod • F) := by
      simp only [heckeThreeHalfWord_cons, List.map_cons, List.prod_cons,
        heckeThreeHalfWord_sub]
      rw [heckeThreeHalfWord_smul_fun]
      ext r
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [heq]
    exact W.add_mem hstableTail (W.smul_mem _ htail)

/-- The correction in the repeated-prime Hecke relation lies in `W` when the
single-prime corrections do and `W` is stable under the relevant operators.
This is the coefficient-level induction needed after
[rolen2026canonical, Lemma 2.4]; identifying `W` with analytic weakly
holomorphic forms remains a separate modular-form argument. -/
theorem heckeThreeHalfWord_shadow_mem_primeFactors
    (W : Submodule ℚ (ℤ → ℚ)) (F : ℤ → ℚ) (n : ℕ)
    (hsingle : ∀ q ∈ n.primeFactorsList,
      heckeThreeHalf q F -
        (((characterTwelve (q : ℤ) * (1 + (q : ℤ)) : ℤ) : ℚ) • F) ∈ W)
    (hstable : ∀ q ∈ n.primeFactorsList, ∀ A ∈ W, heckeThreeHalf q A ∈ W) :
    heckeThreeHalfWord n.primeFactorsList F -
      (heckeShadowEigenvalue n : ℚ) • F ∈ W := by
  have hcast (ps : List ℕ) :
      (ps.map fun (q : ℕ) =>
        ((characterTwelve (q : ℤ) * (1 + (q : ℤ)) : ℤ) : ℚ)).prod =
        ((ps.map fun (q : ℕ) => characterTwelve (q : ℤ) * (1 + (q : ℤ))).prod : ℚ) := by
    induction ps with
    | nil => simp
    | cons q ps ih =>
      simp only [List.map_cons, List.prod_cons]
      conv_rhs => rw [Int.cast_mul]
      rw [← ih]
  change heckeThreeHalfWord n.primeFactorsList F -
    (((n.primeFactorsList.map fun (q : ℕ) =>
      characterTwelve (q : ℤ) * (1 + (q : ℤ))).prod : ℤ) : ℚ) • F ∈ W
  rw [← hcast]
  simpa only [List.map_map, Function.comp_def] using
    heckeThreeHalfWord_shadow_mem W F
    (fun q => ((characterTwelve (q : ℤ) * (1 + (q : ℤ)) : ℤ) : ℚ))
    n.primeFactorsList hsingle hstable

/-- The coefficient space generated by the integral weak forms `G_m` of
[rolen2026canonical, Proposition 2.2]. Indices outside the proposition's
domain are assigned zero, including `G₁` as in Remark 2.3. -/
def shadowCorrectionSpan (G : ℕ → ℤ → ℚ) : Submodule ℚ (ℤ → ℚ) :=
  Submodule.span ℚ (Set.range G)

/-- Corrections whose pole indices divide `n`. This smaller space retains the
principal-part bound required for the constant-term pairing. -/
def shadowDivisorSpan (G : ℕ → ℤ → ℚ) (n : ℕ) :
    Submodule ℚ (ℤ → ℚ) :=
  Submodule.span ℚ {A | ∃ t : ℕ, t ∣ n ∧ A = G t}

/-- The generators of the divisor-bounded correction space. -/
theorem shadowDivisorSpan_eq (G : ℕ → ℤ → ℚ) (n : ℕ) :
    shadowDivisorSpan G n =
      Submodule.span ℚ {A | ∃ t : ℕ, t ∣ n ∧ A = G t} := (rfl)

/-- A correction row belongs to the divisor span at each multiple of its
index. -/
theorem mem_shadowDivisorSpan (G : ℕ → ℤ → ℚ) {t n : ℕ}
    (ht : t ∣ n) : G t ∈ shadowDivisorSpan G n :=
  Submodule.subset_span ⟨t, ht, rfl⟩

/-- The exact one-prime identities of [rolen2026canonical, Lemma 2.4,
equations (2.6) and (2.7)], expressed for complete rational Fourier rows.
The zero extension permits the recursion to mention `G_(m/p)` uniformly.
These identities concern one prime at a time; repeated primes are treated
by `PrimeShadowRelations.word_mem` below. -/
structure PrimeShadowRelations (F : ℤ → ℚ) (G : ℕ → ℤ → ℚ) where
  zero_outside : ∀ m, ¬ (1 < m ∧ m.Coprime 6) → G m = 0
  f_prime : ∀ p, p.Prime → 5 ≤ p →
    heckeThreeHalf p F -
      (((characterTwelve (p : ℤ) * (1 + (p : ℤ)) : ℤ) : ℚ) • F) =
      (p : ℚ) • G p
  G_prime : ∀ p, p.Prime → 5 ≤ p → ∀ m, 1 < m → m.Coprime 6 →
    heckeThreeHalf p (G m) =
      (p : ℚ) • G (m * p) +
        etaHeckeDiagonal p (-((m : ℤ) ^ 2)) • G m +
        (if p ∣ m then G (m / p) else 0) -
        ((p : ℚ) * (characterTwelve (m : ℤ) : ℚ)) • G p

namespace PrimeShadowRelations

variable {F : ℤ → ℚ} {G : ℕ → ℤ → ℚ}

/-- A Hecke step at `p` enlarges divisor support by at most a factor of `p`.
This uses each term of the cited one-prime relation, including `G_(m/p)`
when `p` divides `m`. -/
theorem stable_divisor (data : PrimeShadowRelations F G) (p n : ℕ)
    (hp : p.Prime) (hp5 : 5 ≤ p) (A : ℤ → ℚ)
    (hA : A ∈ shadowDivisorSpan G n) :
    heckeThreeHalf p A ∈ shadowDivisorSpan G (n * p) := by
  let W := shadowDivisorSpan G (n * p)
  have hG {t : ℕ} (ht : t ∣ n * p) : G t ∈ W :=
    mem_shadowDivisorSpan G ht
  induction hA using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    by_cases hvalid : 1 < m ∧ m.Coprime 6
    · rw [data.G_prime p hp hp5 m hvalid.1 hvalid.2]
      have hmp : m * p ∣ n * p := by
        obtain ⟨k, rfl⟩ := hm
        exact ⟨k, by ring⟩
      have hm' : m ∣ n * p := dvd_mul_of_dvd_left hm p
      have hp' : p ∣ n * p := by
        exact ⟨n, by ring⟩
      apply W.sub_mem
      · apply W.add_mem
        · exact W.add_mem (W.smul_mem _ (hG hmp))
            (W.smul_mem _ (hG hm'))
        · split_ifs with hpm
          · have hmquot : m = (m / p) * p := (Nat.div_mul_cancel hpm).symm
            have hquot : m / p ∣ n * p :=
              dvd_trans ⟨p, hmquot⟩ hm'
            exact hG hquot
          · exact W.zero_mem
      · exact W.smul_mem _ (hG hp')
    · rw [data.zero_outside m hvalid]
      rw [heckeThreeHalf_zero]
      exact W.zero_mem
  | zero =>
    rw [heckeThreeHalf_zero]
    exact W.zero_mem
  | add x y hx hy ihx ihy =>
    rw [heckeThreeHalf_add]
    exact W.add_mem ihx ihy
  | smul c x hx ih =>
    change heckeThreeHalf p (fun r => c * x r) ∈ W
    rw [heckeThreeHalf_smul]
    exact W.smul_mem c ih

/-- One prime updates a shadow-cancelled row while preserving the precise
divisor bound on its correction. -/
theorem step_mem_divisor (data : PrimeShadowRelations F G) (p n : ℕ)
    (hp : p.Prime) (hp5 : 5 ≤ p) (A : ℤ → ℚ) (c : ℚ)
    (hA : A - c • F ∈ shadowDivisorSpan G n) :
    heckeThreeHalf p A -
      (c * ((characterTwelve (p : ℤ) * (1 + (p : ℤ)) : ℤ) : ℚ)) • F ∈
      shadowDivisorSpan G (n * p) := by
  let e : ℚ := ((characterTwelve (p : ℤ) * (1 + (p : ℤ)) : ℤ) : ℚ)
  have hstable := data.stable_divisor p n hp hp5 _ hA
  have hprime : heckeThreeHalf p F - e • F ∈
      shadowDivisorSpan G (n * p) := by
    rw [data.f_prime p hp hp5]
    exact (shadowDivisorSpan G (n * p)).smul_mem _
      (mem_shadowDivisorSpan G (show p ∣ n * p by exact ⟨n, by ring⟩))
  have heq : heckeThreeHalf p A - (c * e) • F =
      heckeThreeHalf p (A - c • F) + c • (heckeThreeHalf p F - e • F) := by
    rw [heckeThreeHalf_sub]
    rw [heckeThreeHalf_smul_fun]
    ext r
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [heq]
  exact (shadowDivisorSpan G (n * p)).add_mem hstable
    ((shadowDivisorSpan G (n * p)).smul_mem _ hprime)

/-- Iterating the one-prime identities keeps every correction index among
the divisors of the product, including for repeated primes. -/
theorem word_mem_divisor_aux (data : PrimeShadowRelations F G)
    (ps : List ℕ) (n : ℕ) (A : ℤ → ℚ) (c : ℚ)
    (hA : A - c • F ∈ shadowDivisorSpan G n)
    (hps : ∀ p ∈ ps, p.Prime ∧ 5 ≤ p) :
    heckeThreeHalfWord ps A -
      (c * (ps.map fun (p : ℕ) =>
        ((characterTwelve (p : ℤ) * (1 + (p : ℤ)) : ℤ) : ℚ)).prod) • F ∈
      shadowDivisorSpan G (n * ps.prod) := by
  induction ps generalizing n A c with
  | nil => simpa [heckeThreeHalfWord_nil] using hA
  | cons p ps ih =>
    have hp := hps p (by simp)
    have htail : ∀ q ∈ ps, q.Prime ∧ 5 ≤ q :=
      fun q hq => hps q (by simp [hq])
    have hstep := data.step_mem_divisor p n hp.1 hp.2 A c hA
    have hrec := ih (n * p) (heckeThreeHalf p A)
      (c * ((characterTwelve (p : ℤ) * (1 + (p : ℤ)) : ℤ) : ℚ))
      hstep htail
    simpa [heckeThreeHalfWord_cons, List.map_map, mul_assoc] using hrec

/-- The actual Hecke word of `F` differs from its scalar shadow eigenpart by
a finite combination of rows `G_t` with `t` dividing the word product.
[rolen2026canonical, Lemma 2.4]; the finite-word induction is proved here. -/
theorem word_mem_divisor (data : PrimeShadowRelations F G) (ps : List ℕ)
    (hps : ∀ p ∈ ps, p.Prime ∧ 5 ≤ p) :
    heckeThreeHalfWord ps F -
      ((ps.map fun (p : ℕ) =>
        ((characterTwelve (p : ℤ) * (1 + (p : ℤ)) : ℤ) : ℚ)).prod) • F ∈
      shadowDivisorSpan G ps.prod := by
  have hzero : F - (1 : ℚ) • F ∈ shadowDivisorSpan G 1 := by simp
  simpa using data.word_mem_divisor_aux ps 1 F 1 hzero hps

/-- The divisor bound for the canonical factor list of a positive integer
coprime to six. In particular this applies when a prime occurs several times.
The only analytic ingredients are the one-prime relations stored in `data`.
[rolen2026canonical, Lemma 2.4; rolenManuscript, §3] -/
theorem word_mem_divisor_primeFactors (data : PrimeShadowRelations F G)
    (n : ℕ) (hn : 0 < n) (hc : n.Coprime 6) :
    heckeThreeHalfWord n.primeFactorsList F -
      (heckeShadowEigenvalue n : ℚ) • F ∈ shadowDivisorSpan G n := by
  have hprod : n.primeFactorsList.prod = n :=
    Nat.prod_primeFactorsList (Nat.ne_of_gt hn)
  have hps := primeFactorsList_prime_five n hn hc
  have hcast (ps : List ℕ) :
      (ps.map fun (p : ℕ) =>
        ((characterTwelve (p : ℤ) * (1 + (p : ℤ)) : ℤ) : ℚ)).prod =
        ((ps.map fun (p : ℕ) => characterTwelve (p : ℤ) * (1 + (p : ℤ))).prod : ℚ) := by
    induction ps with
    | nil => simp
    | cons p ps ih =>
      simp only [List.map_cons, List.prod_cons]
      conv_rhs => rw [Int.cast_mul]
      rw [← ih]
  simpa only [hprod, heckeShadowEigenvalue, hcast] using
    data.word_mem_divisor n.primeFactorsList hps

/-- A single Hecke step preserves the span of the actual `G_m` rows.
The `m = 1` and non-coprime generators vanish by the zero extension; for
`m > 1` this is precisely the four-term identity (2.7). -/
theorem stable (data : PrimeShadowRelations F G) (p : ℕ)
    (hp : p.Prime) (hp5 : 5 ≤ p) (A : ℤ → ℚ)
    (hA : A ∈ shadowCorrectionSpan G) :
    heckeThreeHalf p A ∈ shadowCorrectionSpan G := by
  let W := shadowCorrectionSpan G
  have hG (m : ℕ) : G m ∈ W :=
    Submodule.subset_span ⟨m, rfl⟩
  induction hA using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    by_cases hm : 1 < m ∧ m.Coprime 6
    · rw [data.G_prime p hp hp5 m hm.1 hm.2]
      apply W.sub_mem
      · apply W.add_mem
        · exact W.add_mem (W.smul_mem _ (hG (m * p)))
            (W.smul_mem _ (hG m))
        · split_ifs
          · exact hG (m / p)
          · exact W.zero_mem
      · exact W.smul_mem _ (hG p)
    · rw [data.zero_outside m hm]
      rw [heckeThreeHalf_zero]
      exact W.zero_mem
  | zero =>
    rw [heckeThreeHalf_zero]
    exact W.zero_mem
  | add x y hx hy ihx ihy =>
    rw [heckeThreeHalf_add]
    exact W.add_mem ihx ihy
  | smul c x hx ih =>
    have hsmul := heckeThreeHalf_smul p c x
    change heckeThreeHalf p (fun r => c * x r) ∈ W
    rw [hsmul]
    exact W.smul_mem c ih

/-- Iteration of the cited one-prime identities through any finite prime
word, including the empty word and repeated prime factors. The conclusion is
membership in a span of actual correction rows, rather than a new analytic
modularity assumption [rolen2026canonical, Lemma 2.4]. -/
theorem word_mem (data : PrimeShadowRelations F G) (ps : List ℕ)
    (hps : ∀ p ∈ ps, p.Prime ∧ 5 ≤ p) :
    heckeThreeHalfWord ps F -
      ((ps.map fun (p : ℕ) =>
        ((characterTwelve (p : ℤ) * (1 + (p : ℤ)) : ℤ) : ℚ)).prod) • F ∈
      shadowCorrectionSpan G := by
  have hword := heckeThreeHalfWord_shadow_mem
    (shadowCorrectionSpan G) F
    (fun p => ((characterTwelve (p : ℤ) * (1 + (p : ℤ)) : ℤ) : ℚ)) ps
    (by
      intro p hp
      rw [data.f_prime p (hps p hp).1 (hps p hp).2]
      exact (shadowCorrectionSpan G).smul_mem _
        (Submodule.subset_span ⟨p, rfl⟩))
    (by
      intro p hp A hA
      exact data.stable p (hps p hp).1 (hps p hp).2 A hA)
  simpa only [List.map_map, Function.comp_def] using hword

end PrimeShadowRelations

end SptClassification.QSeries
