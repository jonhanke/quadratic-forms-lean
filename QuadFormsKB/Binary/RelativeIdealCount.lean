import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Binary.RelativeQuadratic

/-!
# Ideals of $\mathcal O_E$ with given relative norm

Let $E/F$ be an extension of number fields of degree $2$, $\chi = \chi_{E/F}$ its splitting character (`relChar`) and
$N_{E/F}$ the relative ideal norm (Mathlib's `Ideal.relNorm (𝓞 F)`). For an ideal $\mathfrak m$ of $\mathcal O_F$ let
$$c(\mathfrak m) = \#\{\mathfrak A \subseteq \mathcal O_E : N_{E/F}\mathfrak A = \mathfrak m\}\qquad(\texttt{relNormCount}).$$
**`relNormCount_prod`:** for distinct nonzero primes $\mathfrak p_0, \dots, \mathfrak p_{k-1}$ of $F$ (a `Finset` $s$) and exponents
$a_{\mathfrak p} \ge 0$,
$$c\Big(\prod_{\mathfrak p \in s}\mathfrak p^{a_\mathfrak p}\Big) = \prod_{\mathfrak p \in s}\ \sum_{j=0}^{a_\mathfrak p}\chi(\mathfrak p)^j
  = \sum_{\mathfrak d \mid \mathfrak m}\chi(\mathfrak d)$$
(the second form, with $\chi$ extended multiplicatively to ideals, is `relNormCount_prod_eq_sum`: the divisors
$\mathfrak d = \prod\mathfrak p^{j_\mathfrak p}$, $0 \le j_\mathfrak p \le a_\mathfrak p$). This is the input over $F$ for the representation counts.

**The proof is local, one prime at a time** (`relNormCount_pow_mul`): for $\mathfrak p \nmid \mathfrak n$,
$c(\mathfrak p^a\mathfrak n) = S_a(\chi(\mathfrak p))\,c(\mathfrak n)$ with $S_a(x) = \sum_{j \le a}x^j$ (`geomSum`), by induction on $a$, using only:
* if $\mathfrak p \mid N_{E/F}\mathfrak A$ then some prime $\mathfrak P \mid \mathfrak p$ divides $\mathfrak A$ (`exists_dvd_of_dvd_relNorm`);
* multiplication by $\mathfrak P$ is a bijection from $\{N\mathfrak A' = \mathfrak m'\}$ onto $\{\mathfrak P \mid \mathfrak A,\ N\mathfrak A = N\mathfrak P\cdot\mathfrak m'\}$
  (`image_mul_relNormSet`);
* the splitting law (`splitting`): ramified, $c(\mathfrak p^{a+1}\mathfrak n) = c(\mathfrak p^a\mathfrak n)$; inert,
  $c(\mathfrak p\mathfrak n) = 0$ and $c(\mathfrak p^{a+2}\mathfrak n) = c(\mathfrak p^a\mathfrak n)$; split $\mathfrak p = \mathfrak P_0\mathfrak P_1$, by
  inclusion–exclusion over "$\mathfrak P_0 \mid \mathfrak A$", "$\mathfrak P_1 \mid \mathfrak A$",
  $c(\mathfrak p^{a+2}\mathfrak n) = 2c(\mathfrak p^{a+1}\mathfrak n) - c(\mathfrak p^a\mathfrak n)$ and $c(\mathfrak p\mathfrak n) = 2c(\mathfrak n)$.

Dyadic primes need no special treatment.

Sources: Neukirch, *Algebraic Number Theory*, Ch. I §8 and Ch. VII §5 [unverified locators]; Zagier, *Zetafunktionen
und quadratische Körper*, §11 (the case $F = \mathbb{Q}$) [unverified locator].
-/

open NumberField IsDedekindDomain QuadFormsKB.NFEuler

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Binary.Rel

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]

/-! ### Relative norms of ideals -/

variable (E) in
/-- The ideals of $\mathcal O_E$ of relative norm $\mathfrak m$: $\{\mathfrak A : N_{E/F}\mathfrak A = \mathfrak m\}$. -/
def relNormSet (𝔪 : Ideal (𝓞 F)) : Set (Ideal (𝓞 E)) := {𝔄 | Ideal.relNorm (𝓞 F) 𝔄 = 𝔪}

variable (E) in
/-- **The number of ideals of $\mathcal O_E$ of relative norm $\mathfrak m$:**
$c(\mathfrak m) = \#\{\mathfrak A \subseteq \mathcal O_E : N_{E/F}\mathfrak A = \mathfrak m\}$ (`Nat.card`; finite for $\mathfrak m \ne 0$,
`finite_relNormSet`). -/
def relNormCount (𝔪 : Ideal (𝓞 F)) : ℕ := Nat.card {𝔄 : Ideal (𝓞 E) // Ideal.relNorm (𝓞 F) 𝔄 = 𝔪}

theorem relNormCount_eq_ncard (𝔪 : Ideal (𝓞 F)) : relNormCount E 𝔪 = (relNormSet E 𝔪).ncard := by
  rw [relNormCount, ← Nat.card_coe_set_eq]; rfl

theorem finite_relNormSet {𝔪 : Ideal (𝓞 F)} : (relNormSet E 𝔪).Finite := by
  refine (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 E) (Ideal.absNorm 𝔪)).subset fun 𝔄 h𝔄 => ?_
  simp only [relNormSet, Set.mem_ofPred_eq] at h𝔄 ⊢
  rw [← h𝔄, Ideal.absNorm_relNorm]

/-- $N_{E/F}\mathfrak P = \mathfrak p^{f(\mathfrak P\mid\mathfrak p)}$ for a prime $\mathfrak P$ of $\mathcal O_E$ over $\mathfrak p$. -/
theorem relNorm_primesOver (𝔭 : HeightOneSpectrum (𝓞 F)) (P : 𝔭.asIdeal.primesOver (𝓞 E)) :
    Ideal.relNorm (𝓞 F) P.1 = 𝔭.asIdeal ^ P.1.inertiaDeg (𝓞 F) := by
  have := P.2.1
  have := P.2.2
  have := 𝔭.isMaximal
  have : P.1.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P.1 𝔭.asIdeal
  exact Ideal.relNorm_eq_pow_of_isMaximal P.1 𝔭.asIdeal

theorem primesOver_ne_bot (𝔭 : HeightOneSpectrum (𝓞 F)) (P : 𝔭.asIdeal.primesOver (𝓞 E)) : P.1 ≠ ⊥ := by
  have := P.2.2
  exact Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P.1

/-- **A prime dividing the norm comes from a prime factor:** if $\mathfrak p \mid N_{E/F}\mathfrak A$ then some prime $\mathfrak P$ of
$\mathcal O_E$ over $\mathfrak p$ divides $\mathfrak A$. (Induction on the prime factorization of $\mathfrak A$; for a prime $\mathfrak Q$,
$N\mathfrak Q = \mathfrak q^f$ with $\mathfrak q = \mathfrak Q \cap \mathcal O_F$, so $\mathfrak p \mid N\mathfrak Q$ forces $\mathfrak p = \mathfrak q$.) -/
theorem exists_dvd_of_dvd_relNorm (𝔭 : HeightOneSpectrum (𝓞 F)) (𝔄 : Ideal (𝓞 E))
    (h : 𝔭.asIdeal ∣ Ideal.relNorm (𝓞 F) 𝔄) : ∃ P : 𝔭.asIdeal.primesOver (𝓞 E), P.1 ∣ 𝔄 := by
  have h𝔭 : Prime 𝔭.asIdeal := Ideal.prime_of_isPrime 𝔭.ne_bot 𝔭.isPrime
  have := 𝔭.isMaximal
  induction 𝔄 using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
    obtain ⟨Q, hQm, hQ⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) 𝔭.asIdeal
    exact ⟨⟨Q, hQm.isPrime, hQ⟩, dvd_zero _⟩
  | h₂ x hx =>
    rw [Ideal.isUnit_iff.mp hx, Ideal.relNorm_top] at h
    exact absurd (Ideal.dvd_iff_le.mp h) (fun hle => 𝔭.isPrime.ne_top (top_le_iff.mp hle))
  | h₃ a Q ha hQ ih =>
    rw [map_mul] at h
    rcases h𝔭.dvd_or_dvd h with h1 | h1
    · have hQp : Q.IsPrime := Ideal.isPrime_of_prime hQ
      have hQ0 : Q ≠ ⊥ := hQ.ne_zero
      set q : Ideal (𝓞 F) := Q.under (𝓞 F)
      have : Q.IsMaximal := hQp.isMaximal hQ0
      have hqm : q.IsMaximal := Ideal.IsMaximal.under (𝓞 F) Q
      have : Q.LiesOver q := ⟨rfl⟩
      rw [Ideal.relNorm_eq_pow_of_isMaximal Q q] at h1
      have h2 : 𝔭.asIdeal ∣ q := h𝔭.dvd_of_dvd_pow h1
      have h3 : q = 𝔭.asIdeal :=
        hqm.eq_of_le 𝔭.isPrime.ne_top (Ideal.dvd_iff_le.mp h2)
      exact ⟨⟨Q, hQp, ⟨h3.symm⟩⟩, dvd_mul_right _ _⟩
    · obtain ⟨P, hP⟩ := ih h1
      exact ⟨P, dvd_mul_of_dvd_right hP _⟩

/-- **Multiplication by a nonzero ideal $\mathfrak Q$** maps $\{N\mathfrak A' = \mathfrak m'\}$ bijectively onto
$\{\mathfrak A : \mathfrak Q \mid \mathfrak A,\ N\mathfrak A = N\mathfrak Q\cdot\mathfrak m'\}$. -/
theorem image_mul_relNormSet {Q : Ideal (𝓞 E)} (hQ : Q ≠ ⊥) (𝔪' : Ideal (𝓞 F)) :
    (Q * ·) '' relNormSet E 𝔪' = {𝔄 ∈ relNormSet E (Ideal.relNorm (𝓞 F) Q * 𝔪') | Q ∣ 𝔄} := by
  ext 𝔄
  simp only [relNormSet, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨𝔄', h𝔄', rfl⟩
    exact ⟨by rw [map_mul, h𝔄'], dvd_mul_right _ _⟩
  · rintro ⟨hN, 𝔄', rfl⟩
    refine ⟨𝔄', ?_, rfl⟩
    rw [map_mul] at hN
    have hQN : Ideal.relNorm (𝓞 F) Q ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.relNorm_eq_bot_iff]; exact hQ
    exact mul_left_cancel₀ hQN hN

theorem injective_mul {Q : Ideal (𝓞 E)} (hQ : Q ≠ ⊥) : Function.Injective (Q * ·) :=
  fun _ _ h => mul_left_cancel₀ (by rwa [Ne, Ideal.zero_eq_bot]) h

/-- $\#\{\mathfrak A : \mathfrak Q \mid \mathfrak A,\ N\mathfrak A = N\mathfrak Q\cdot\mathfrak m'\} = c(\mathfrak m')$. -/
theorem ncard_dvd_relNormSet {Q : Ideal (𝓞 E)} (hQ : Q ≠ ⊥) (𝔪' : Ideal (𝓞 F)) :
    {𝔄 ∈ relNormSet E (Ideal.relNorm (𝓞 F) Q * 𝔪') | Q ∣ 𝔄}.ncard = relNormCount E 𝔪' := by
  rw [← image_mul_relNormSet hQ, Set.ncard_image_of_injective _ (injective_mul hQ), relNormCount_eq_ncard]

/-! ### The local recursion -/

/-- $S_a(x) = \sum_{j=0}^{a}x^j$. -/
def geomSum (x : ℤ) (a : ℕ) : ℤ := ∑ j ∈ Finset.range (a + 1), x ^ j

theorem geomSum_zero (x : ℤ) : geomSum x 0 = 1 := by simp [geomSum]

theorem geomSum_succ (x : ℤ) (a : ℕ) : geomSum x (a + 1) = 1 + x * geomSum x a := by
  rw [geomSum, geomSum, Finset.sum_range_succ', Finset.mul_sum, pow_zero, add_comm]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

/-- $\mathfrak p^{a}\mathfrak n$ with $\mathfrak p$-exponent shifted: $N\mathfrak Q\cdot\mathfrak p^{a}\mathfrak n$ for $N\mathfrak Q = \mathfrak p^f$. -/
theorem pow_mul_eq (𝔭 : Ideal (𝓞 F)) (𝔫 : Ideal (𝓞 F)) (f a : ℕ) :
    𝔭 ^ (f + a) * 𝔫 = 𝔭 ^ f * (𝔭 ^ a * 𝔫) := by rw [pow_add, mul_assoc]

/-- If $\mathfrak p \nmid \mathfrak n$ then $\mathfrak p^{b} \nmid \mathfrak p^{a}\mathfrak n$ for $b > a$. -/
theorem not_pow_dvd (𝔭 : HeightOneSpectrum (𝓞 F)) {𝔫 : Ideal (𝓞 F)} (h𝔫 : ¬ 𝔭.asIdeal ∣ 𝔫) {a b : ℕ}
    (hab : a < b) : ¬ 𝔭.asIdeal ^ b ∣ 𝔭.asIdeal ^ a * 𝔫 := by
  intro h
  have h0 : 𝔭.asIdeal ^ a ≠ 0 := pow_ne_zero _ (by rw [Ne, Ideal.zero_eq_bot]; exact 𝔭.ne_bot)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hab
  have h' : 𝔭.asIdeal ^ a * (𝔭.asIdeal ^ (k + 1)) ∣ 𝔭.asIdeal ^ a * 𝔫 := by
    rwa [← pow_add, ← add_assoc]
  have := (mul_dvd_mul_iff_left h0).mp h'
  exact h𝔫 (dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero k)) this)

/-- **The local recursion at $\mathfrak p$** (every prime, dyadic and ramified included): for $\mathfrak p \nmid \mathfrak n$ and
$a \ge 0$,
$$c(\mathfrak p^a\mathfrak n) = S_a(\chi(\mathfrak p))\,c(\mathfrak n),\qquad S_a(x) = \sum_{j=0}^a x^j,$$
i.e. $(a+1)\,c(\mathfrak n)$ if $\mathfrak p$ splits, $c(\mathfrak n)$ or $0$ ($a$ even or odd) if $\mathfrak p$ is inert, $c(\mathfrak n)$ if $\mathfrak p$
ramifies. -/
@[kb "neukirch1999" "Ch. I §8 [unverified]"]
theorem relNormCount_pow_mul (hdeg : Module.finrank F E = 2) (𝔭 : HeightOneSpectrum (𝓞 F))
    {𝔫 : Ideal (𝓞 F)} (h𝔫 : ¬ 𝔭.asIdeal ∣ 𝔫) (a : ℕ) :
    (relNormCount E (𝔭.asIdeal ^ a * 𝔫) : ℤ) = geomSum (relChar E 𝔭) a * relNormCount E 𝔫 := by
  classical
  set p := 𝔭.asIdeal
  set C : ℕ → ℤ := fun a => (relNormCount E (p ^ a * 𝔫) : ℤ) with hC
  have hC0 : C 0 = relNormCount E 𝔫 := by simp [C]
  -- every 𝔄 of norm p^(a+1) 𝔫 is divisible by a prime over p
  have hcover : ∀ a, ∀ 𝔄 ∈ relNormSet E (p ^ (a + 1) * 𝔫), ∃ P : p.primesOver (𝓞 E), P.1 ∣ 𝔄 := by
    intro a 𝔄 h𝔄
    refine exists_dvd_of_dvd_relNorm 𝔭 𝔄 ?_
    rw [show Ideal.relNorm (𝓞 F) 𝔄 = p ^ (a + 1) * 𝔫 from h𝔄, pow_succ, mul_comm (p ^ a) p, mul_assoc]
    exact dvd_mul_right _ _
  -- the count of multiples of a prime P over p
  have hmult : ∀ (P : p.primesOver (𝓞 E)) (a : ℕ),
      {𝔄 ∈ relNormSet E (p ^ (P.1.inertiaDeg (𝓞 F) + a) * 𝔫) | P.1 ∣ 𝔄}.ncard = C a := by
    intro P a
    rw [pow_mul_eq, ← relNorm_primesOver 𝔭 P, ncard_dvd_relNormSet (primesOver_ne_bot 𝔭 P)]
  -- no multiples of an ideal of norm p^b in norm p^a 𝔫 when b > a
  have hnone : ∀ (Q : Ideal (𝓞 E)) (a b : ℕ), Ideal.relNorm (𝓞 F) Q = p ^ b → a < b →
      {𝔄 ∈ relNormSet E (p ^ a * 𝔫) | Q ∣ 𝔄} = ∅ := by
    intro Q a b hQ hab
    ext 𝔄
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, relNormSet]
    intro hN hdvd
    have := map_dvd (Ideal.relNorm (𝓞 F)) hdvd
    rw [hQ, hN] at this
    exact not_pow_dvd 𝔭 h𝔫 hab this
  have key : ∀ a, C a = geomSum (relChar E 𝔭) a * C 0 := by
    rcases splitting hdeg 𝔭 with ⟨hχ, P₀, P₁, h01, hx, -, hf0, -, hf1⟩ | ⟨hχ, P₀, hx, -, hf0⟩ |
        ⟨hχ, P₀, hx, -, hf0⟩
    · -- split
      have hP0 : P₀.1 ≠ ⊥ := primesOver_ne_bot 𝔭 P₀
      have hP1 : P₁.1 ≠ ⊥ := primesOver_ne_bot 𝔭 P₁
      have hcop : P₀.1 ⊔ P₁.1 = ⊤ := by
        have := P₀.2.1; have := P₁.2.1
        exact Ideal.IsMaximal.coprime_of_ne (P₀.2.1.isMaximal hP0) (P₁.2.1.isMaximal hP1)
          (fun h => h01 (Subtype.ext h))
      have hboth : ∀ 𝔄 : Ideal (𝓞 E), P₀.1 ∣ 𝔄 ∧ P₁.1 ∣ 𝔄 ↔ P₀.1 * P₁.1 ∣ 𝔄 := by
        intro 𝔄
        rw [Ideal.dvd_iff_le, Ideal.dvd_iff_le, Ideal.dvd_iff_le, Ideal.mul_eq_inf_of_coprime hcop, le_inf_iff]
      have hN01 : Ideal.relNorm (𝓞 F) (P₀.1 * P₁.1) = p ^ 2 := by
        rw [map_mul, relNorm_primesOver 𝔭 P₀, relNorm_primesOver 𝔭 P₁, hf0, hf1, ← pow_add]
      have hP01 : P₀.1 * P₁.1 ≠ ⊥ := by
        rw [Ne, ← Ideal.zero_eq_bot]; exact mul_ne_zero (by rwa [Ideal.zero_eq_bot]) (by rwa [Ideal.zero_eq_bot])
      -- inclusion–exclusion at level a + 1
      have hstep : ∀ a, C (a + 1) + {𝔄 ∈ relNormSet E (p ^ (a + 1) * 𝔫) | P₀.1 * P₁.1 ∣ 𝔄}.ncard = 2 * C a := by
        intro a
        have hX : relNormSet E (p ^ (a + 1) * 𝔫) = {𝔄 ∈ relNormSet E (p ^ (a + 1) * 𝔫) | P₀.1 ∣ 𝔄} ∪
            {𝔄 ∈ relNormSet E (p ^ (a + 1) * 𝔫) | P₁.1 ∣ 𝔄} := by
          ext 𝔄
          simp only [Set.mem_union, Set.mem_ofPred_eq]
          constructor
          · intro h
            obtain ⟨P, hP⟩ := hcover a 𝔄 h
            rcases hx P with rfl | rfl
            · exact Or.inl ⟨h, hP⟩
            · exact Or.inr ⟨h, hP⟩
          · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
        have hI : {𝔄 ∈ relNormSet E (p ^ (a + 1) * 𝔫) | P₀.1 ∣ 𝔄} ∩
            {𝔄 ∈ relNormSet E (p ^ (a + 1) * 𝔫) | P₁.1 ∣ 𝔄} =
            {𝔄 ∈ relNormSet E (p ^ (a + 1) * 𝔫) | P₀.1 * P₁.1 ∣ 𝔄} := by
          ext 𝔄
          simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, ← hboth]
          tauto
        have hie := Set.ncard_union_add_ncard_inter {𝔄 ∈ relNormSet E (p ^ (a + 1) * 𝔫) | P₀.1 ∣ 𝔄}
          {𝔄 ∈ relNormSet E (p ^ (a + 1) * 𝔫) | P₁.1 ∣ 𝔄}
          (finite_relNormSet.subset fun _ h => h.1) (finite_relNormSet.subset fun _ h => h.1)
        rw [← hX, hI] at hie
        have h0 := hmult P₀ a
        have h1 := hmult P₁ a
        rw [hf0, add_comm 1 a] at h0
        rw [hf1, add_comm 1 a] at h1
        have hXc : C (a + 1) = ((relNormSet E (p ^ (a + 1) * 𝔫)).ncard : ℤ) := by
          simp only [C, relNormCount_eq_ncard]
        have hie' := congrArg (Nat.cast : ℕ → ℤ) hie
        push_cast at hie'
        rw [hXc]
        linarith
      have hC1 : C 1 = 2 * C 0 := by
        have := hstep 0
        rw [hnone _ 1 2 hN01 (by norm_num), Set.ncard_empty, Nat.cast_zero, add_zero] at this
        simpa using this
      have hC2 : ∀ a, C (a + 2) = 2 * C (a + 1) - C a := by
        intro a
        have h := hstep (a + 1)
        have hm : {𝔄 ∈ relNormSet E (p ^ (a + 1 + 1) * 𝔫) | P₀.1 * P₁.1 ∣ 𝔄}.ncard = C a := by
          rw [show a + 1 + 1 = 2 + a by ring, pow_mul_eq, ← hN01, ncard_dvd_relNormSet hP01]
        rw [hm] at h
        linarith
      rw [hχ]
      intro a
      induction a using Nat.strong_induction_on with
      | _ a ih =>
        match a, ih with
        | 0, _ => simp [geomSum_zero]
        | 1, _ => rw [hC1]; simp [geomSum]
        | a + 2, ih =>
          rw [hC2, ih (a + 1) (by omega), ih a (by omega)]
          simp only [geomSum, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
          push_cast; ring
    · -- inert
      have hall : ∀ a, relNormSet E (p ^ (a + 1) * 𝔫) = {𝔄 ∈ relNormSet E (p ^ (a + 1) * 𝔫) | P₀.1 ∣ 𝔄} := by
        intro a
        ext 𝔄
        simp only [Set.mem_ofPred_eq]
        constructor
        · intro h
          obtain ⟨P, hP⟩ := hcover a 𝔄 h
          rw [hx P] at hP
          exact ⟨h, hP⟩
        · exact fun h => h.1
      have hC1 : C 1 = 0 := by
        simp only [C, relNormCount_eq_ncard]
        rw [show (1 : ℕ) = 0 + 1 from rfl, hall 0, hnone P₀.1 1 2 (by rw [relNorm_primesOver 𝔭 P₀, hf0])
          (by norm_num)]
        simp
      have hC2 : ∀ a, C (a + 2) = C a := by
        intro a
        have := hmult P₀ a
        rw [hf0, add_comm 2 a] at this
        simp only [C, relNormCount_eq_ncard]
        rw [show a + 2 = (a + 1) + 1 from rfl, hall (a + 1), show a + 1 + 1 = a + 2 from rfl, this]
        simp [C, relNormCount_eq_ncard]
      rw [hχ]
      intro a
      induction a using Nat.strong_induction_on with
      | _ a ih =>
        match a, ih with
        | 0, _ => simp [geomSum_zero]
        | 1, _ => rw [hC1]; simp [geomSum]
        | a + 2, ih =>
          rw [hC2, ih a (by omega), geomSum_succ, geomSum_succ]
          ring
    · -- ramified
      have hall : ∀ a, relNormSet E (p ^ (a + 1) * 𝔫) = {𝔄 ∈ relNormSet E (p ^ (a + 1) * 𝔫) | P₀.1 ∣ 𝔄} := by
        intro a
        ext 𝔄
        simp only [Set.mem_ofPred_eq]
        constructor
        · intro h
          obtain ⟨P, hP⟩ := hcover a 𝔄 h
          rw [hx P] at hP
          exact ⟨h, hP⟩
        · exact fun h => h.1
      have hC1 : ∀ a, C (a + 1) = C a := by
        intro a
        have := hmult P₀ a
        rw [hf0, add_comm 1 a] at this
        simp only [C, relNormCount_eq_ncard]
        rw [hall a, this]
        simp [C, relNormCount_eq_ncard]
      have hg : ∀ a, geomSum 0 a = 1 := by
        intro a; cases a with
        | zero => exact geomSum_zero 0
        | succ a => rw [geomSum_succ]; ring
      rw [hχ]
      intro a
      rw [hg, one_mul]
      induction a with
      | zero => rfl
      | succ a ih => rw [hC1, ih]
  have := key a
  rw [hC0] at this
  exact this

/-- **Ideal counts by relative norm** (the input over $F$ for the representation counts): for a finite set $s$ of nonzero primes of $F$ and
exponents $a_\mathfrak p$,
$$\#\Big\{\mathfrak A \subseteq \mathcal O_E : N_{E/F}\mathfrak A = \prod_{\mathfrak p \in s}\mathfrak p^{a_\mathfrak p}\Big\}
  = \prod_{\mathfrak p \in s}\ \sum_{j=0}^{a_\mathfrak p}\chi_{E/F}(\mathfrak p)^j .$$
*Proof:* `relNormCount_pow_mul` one prime at a time, starting from $c(\mathcal O_F) = 1$. -/
@[kb "neukirch1999" "Ch. I §8 [unverified]"]
theorem relNormCount_prod (hdeg : Module.finrank F E = 2) (s : Finset (HeightOneSpectrum (𝓞 F)))
    (a : HeightOneSpectrum (𝓞 F) → ℕ) :
    (relNormCount E (∏ 𝔭 ∈ s, 𝔭.asIdeal ^ a 𝔭) : ℤ) = ∏ 𝔭 ∈ s, geomSum (relChar E 𝔭) (a 𝔭) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.prod_empty, relNormCount]
    have : {𝔄 : Ideal (𝓞 E) // Ideal.relNorm (𝓞 F) 𝔄 = 1} ≃ Unit :=
      { toFun := fun _ => ()
        invFun := fun _ => ⟨⊤, by rw [Ideal.relNorm_top, Ideal.one_eq_top]⟩
        left_inv := by
          rintro ⟨𝔄, h𝔄⟩
          apply Subtype.ext
          simp only
          by_contra hne
          obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal 𝔄 (Ne.symm hne)
          have hM0 : M ≠ ⊥ := by
            intro h; rw [h, le_bot_iff] at hle
            rw [hle, Ideal.one_eq_top] at h𝔄
            exact absurd ((Ideal.relNorm_eq_bot_iff).mpr rfl) (by rw [h𝔄]; exact top_ne_bot)
          set q : Ideal (𝓞 F) := M.under (𝓞 F)
          have : q.IsMaximal := Ideal.IsMaximal.under (𝓞 F) M
          have : M.LiesOver q := ⟨rfl⟩
          have hd := map_dvd (Ideal.relNorm (𝓞 F)) (Ideal.dvd_iff_le.mpr hle)
          rw [h𝔄, Ideal.relNorm_eq_pow_of_isMaximal M q] at hd
          have hq1 : q ^ M.inertiaDeg (𝓞 F) = ⊤ := by
            rw [← Ideal.one_eq_top]; exact isUnit_iff_dvd_one.mpr hd |>.eq_one
          have hfpos : 0 < M.inertiaDeg (𝓞 F) := Ideal.inertiaDeg_pos M (𝓞 F)
          have : q ^ M.inertiaDeg (𝓞 F) ≤ q := Ideal.pow_le_self hfpos.ne'
          rw [hq1, top_le_iff] at this
          exact (‹q.IsMaximal›.ne_top) this
        right_inv := fun _ => rfl }
    rw [Nat.card_congr this]; simp
  | insert 𝔭 s h𝔭 ih =>
    rw [Finset.prod_insert h𝔭, Finset.prod_insert h𝔭, relNormCount_pow_mul hdeg 𝔭 _ (a 𝔭), ih]
    intro hdvd
    have hp : Prime 𝔭.asIdeal := Ideal.prime_of_isPrime 𝔭.ne_bot 𝔭.isPrime
    obtain ⟨𝔮, h𝔮, hd⟩ := (hp.dvd_finsetProd_iff _).mp hdvd
    have hd' := hp.dvd_of_dvd_pow hd
    have := 𝔮.isMaximal
    have h𝔮eq : 𝔮.asIdeal = 𝔭.asIdeal :=
      (this.eq_of_le 𝔭.isPrime.ne_top (Ideal.dvd_iff_le.mp hd'))
    exact h𝔭 (by rw [← HeightOneSpectrum.ext h𝔮eq]; exact h𝔮)

open Classical in
/-- **The divisor-sum form:** $c(\mathfrak m) = \sum_{\mathfrak d \mid \mathfrak m}\chi_{E/F}(\mathfrak d)$ for
$\mathfrak m = \prod_{\mathfrak p \in s}\mathfrak p^{a_\mathfrak p}$, the divisors being $\mathfrak d = \prod_{\mathfrak p}\mathfrak p^{j_\mathfrak p}$ with
$0 \le j_\mathfrak p \le a_\mathfrak p$ (indexed by `Finset.pi`) and $\chi(\mathfrak d) = \prod_\mathfrak p\chi(\mathfrak p)^{j_\mathfrak p}$. -/
@[kb "neukirch1999" "Ch. I §8 [unverified]"]
theorem relNormCount_prod_eq_sum (hdeg : Module.finrank F E = 2) (s : Finset (HeightOneSpectrum (𝓞 F)))
    (a : HeightOneSpectrum (𝓞 F) → ℕ) :
    (relNormCount E (∏ 𝔭 ∈ s, 𝔭.asIdeal ^ a 𝔭) : ℤ) =
      ∑ j ∈ s.pi (fun 𝔭 => Finset.range (a 𝔭 + 1)), ∏ 𝔭 ∈ s.attach, relChar E 𝔭.1 ^ j 𝔭.1 𝔭.2 := by
  classical
  rw [relNormCount_prod hdeg]
  simp only [geomSum]
  rw [Finset.prod_sum]

/-- **Ideal counts by relative norm, for every nonzero $\mathfrak m$:**
$$c(\mathfrak m) = \prod_{\mathfrak p}\ \sum_{j=0}^{v_\mathfrak p(\mathfrak m)}\chi_{E/F}(\mathfrak p)^j$$
(a finite product, `finprod`; $v_\mathfrak p(\mathfrak m)$ = the multiplicity of $\mathfrak p$ in the prime factorization of $\mathfrak m$,
`Multiset.count` in `normalizedFactors`). -/
@[kb "neukirch1999" "Ch. I §8 [unverified]"]
theorem relNormCount_eq_finprod (hdeg : Module.finrank F E = 2) {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) :
    (relNormCount E 𝔪 : ℤ) = ∏ᶠ 𝔭 : HeightOneSpectrum (𝓞 F),
      geomSum (relChar E 𝔭) (Multiset.count 𝔭.asIdeal (UniqueFactorizationMonoid.normalizedFactors 𝔪)) := by
  classical
  have h𝔪0 : 𝔪 ≠ 0 := by rwa [Ne, Ideal.zero_eq_bot]
  set s := (Ideal.finite_factors h𝔪0).toFinset
  have hcount : ∀ 𝔭 : HeightOneSpectrum (𝓞 F), 𝔭 ∉ s →
      Multiset.count 𝔭.asIdeal (UniqueFactorizationMonoid.normalizedFactors 𝔪) = 0 := by
    intro 𝔭 h𝔭
    rw [Multiset.count_eq_zero]
    intro hmem
    exact h𝔭 ((Ideal.finite_factors h𝔪0).mem_toFinset.mpr
      (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hmem))
  have hm : 𝔪 = ∏ 𝔭 ∈ s, 𝔭.asIdeal ^ Multiset.count 𝔭.asIdeal (UniqueFactorizationMonoid.normalizedFactors 𝔪) := by
    conv_lhs => rw [← Ideal.finprod_heightOneSpectrum_factorization h𝔪0]
    rw [finprod_eq_prod_of_mulSupport_subset (s := s)]
    · exact Finset.prod_congr rfl fun 𝔭 _ => HeightOneSpectrum.maxPowDividing_eq_pow_multiset_count _ h𝔪0
    · intro 𝔭 h𝔭
      by_contra hs
      apply h𝔭
      show 𝔭.maxPowDividing 𝔪 = 1
      rw [HeightOneSpectrum.maxPowDividing_eq_pow_multiset_count _ h𝔪0, hcount 𝔭 hs, pow_zero]
  rw [finprod_eq_prod_of_mulSupport_subset (s := s)]
  · conv_lhs => rw [hm]
    exact relNormCount_prod hdeg s _
  · intro 𝔭 h𝔭
    by_contra hs
    apply h𝔭
    simp only [hcount 𝔭 hs, geomSum_zero]

end QuadFormsKB.Binary.Rel
