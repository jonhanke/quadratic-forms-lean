import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Analysis.NFEulerProduct

/-!
# Splitting of primes in a relative quadratic extension $E/F$

Let $F$ be a number field and $E/F$ an extension of degree $2$ (`Module.finrank F E = 2`); no Galois, CM or
discriminant hypothesis is needed in this file. For a nonzero prime $\mathfrak p$ of $\mathcal O_F$ write
$\mathfrak P \mid \mathfrak p$ for the primes of $\mathcal O_E$ over $\mathfrak p$ (Mathlib's `Ideal.primesOver`, a finite type), with
ramification index $e(\mathfrak P \mid \mathfrak p)$ and inertia degree $f(\mathfrak P \mid \mathfrak p)$.

**The splitting character** (`relChar`) is defined intrinsically, by the splitting of $\mathfrak p$:
$$\chi_{E/F}(\mathfrak p) = \#\{\mathfrak P \mid \mathfrak p : f(\mathfrak P \mid \mathfrak p) = 1\} - 1 \in \{1, -1, 0\}$$
(the analogue of the "number of roots of $f_D \bmod p$, minus one"). **The splitting law** (`splitting`) follows from the
fundamental identity $\sum_{\mathfrak P \mid \mathfrak p} e(\mathfrak P\mid\mathfrak p)f(\mathfrak P\mid\mathfrak p) = [E:F] = 2$ (Mathlib's
`Ideal.sum_ramification_inertia_eq_finrank`) and nothing else, so it holds at **every** prime, dyadic and ramified
primes included, with no Dedekind–Kummer hypothesis ($\mathcal O_E$ need not be monogenic over $\mathcal O_F$):

* $\chi(\mathfrak p) = 1$: $\mathfrak p$ **splits**, $\mathfrak p\mathcal O_E = \mathfrak P_0\mathfrak P_1$ with $\mathfrak P_0 \ne \mathfrak P_1$, $e = f = 1$;
* $\chi(\mathfrak p) = -1$: $\mathfrak p$ is **inert**, one prime, $e = 1$, $f = 2$;
* $\chi(\mathfrak p) = 0$: $\mathfrak p$ **ramifies**, one prime, $e = 2$, $f = 1$.

With $N\mathfrak P = N\mathfrak p^{f(\mathfrak P\mid\mathfrak p)}$ (`absNorm_eq_pow_inertiaDeg`) this gives **the local factor identity**
(`localFactor_eq`)
$$\prod_{\mathfrak P \mid \mathfrak p}(1 - N\mathfrak P^{-s})^{-1} = (1 - N\mathfrak p^{-s})^{-1}(1 - \chi(\mathfrak p)N\mathfrak p^{-s})^{-1}.$$

The identification of $\chi$ with the quadratic Hilbert-symbol character $\mathfrak p \mapsto (-\delta, \pi_\mathfrak p)_\mathfrak p$ of
$E = F(\sqrt{-\delta})$ at unramified $\mathfrak p$ is *not* needed for anything below (the Euler product and the class
number formula only use the splitting law), and is not formalized here; `QTwist.exists_local_cover` gives the
split case "$-\delta \in F_\mathfrak p^{\times 2} \Rightarrow \mathfrak p$ splits" for $\mathfrak p \nmid 2\delta$.

Sources: Neukirch, *Algebraic Number Theory*, Ch. I, Prop. 8.2 ($\sum e_if_i = n$) and Prop. 8.5 [unverified
locators]; Marcus, *Number Fields*, Ch. 3, Thm. 21 ($\sum e_if_i = n$).
-/

open NumberField IsDedekindDomain QuadFormsKB.NFEuler

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Binary.Rel

/-! ### A counting lemma: $\sum e_i f_i = 2$ -/

/-- **The three shapes of $\sum_i e_if_i = 2$** with all $e_i, f_i \ge 1$: two indices with $e = f = 1$, or one index with
$(e, f) = (1, 2)$, or one index with $(e, f) = (2, 1)$. -/
theorem shape_of_sum_eq_two {α : Type*} [Fintype α] (e f : α → ℕ) (he : ∀ a, 0 < e a) (hf : ∀ a, 0 < f a)
    (h : ∑ a, e a * f a = 2) :
    (∃ a b, a ≠ b ∧ (∀ x, x = a ∨ x = b) ∧ e a = 1 ∧ f a = 1 ∧ e b = 1 ∧ f b = 1) ∨
    (∃ a, (∀ x, x = a) ∧ e a = 1 ∧ f a = 2) ∨
    (∃ a, (∀ x, x = a) ∧ e a = 2 ∧ f a = 1) := by
  classical
  have hpos : ∀ a, 1 ≤ e a * f a := fun a => Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (he a).ne' (hf a).ne')
  have hcard : Fintype.card α ≤ 2 := by
    have := Finset.card_nsmul_le_sum (Finset.univ : Finset α) (fun a => e a * f a) 1 (fun a _ => hpos a)
    rw [smul_eq_mul, mul_one, h] at this
    exact this
  have hne : Fintype.card α ≠ 0 := by
    intro h0
    rw [Fintype.card_eq_zero_iff] at h0
    rw [Finset.univ_eq_empty, Finset.sum_empty] at h
    exact absurd h (by norm_num)
  rcases (by omega : Fintype.card α = 1 ∨ Fintype.card α = 2) with hc | hc
  · obtain ⟨a, ha⟩ := Fintype.card_eq_one_iff.mp hc
    have hs : ∑ x, e x * f x = e a * f a := by
      rw [Fintype.sum_eq_single a (fun x hx => absurd (ha x) hx)]
    rw [hs] at h
    have hea : e a ∣ 2 := ⟨f a, h.symm⟩
    rcases (Nat.dvd_prime Nat.prime_two).mp hea with h1 | h2
    · right; left
      exact ⟨a, ha, h1, by rw [h1, one_mul] at h; exact h⟩
    · right; right
      exact ⟨a, ha, h2, by rw [h2] at h; omega⟩
  · obtain ⟨a, b, hab, hall⟩ := Finset.card_eq_two.mp (show (Finset.univ : Finset α).card = 2 from hc)
    have hx : ∀ x, x = a ∨ x = b := by
      intro x
      have : x ∈ ({a, b} : Finset α) := by rw [← hall]; exact Finset.mem_univ x
      simpa using this
    have hs : ∑ x, e x * f x = e a * f a + e b * f b := by
      have : (Finset.univ : Finset α) = {a, b} := by
        ext x; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]; exact hx x
      rw [this, Finset.sum_pair hab]
    rw [hs] at h
    have ha1 : e a * f a = 1 := by have := hpos a; have := hpos b; omega
    have hb1 : e b * f b = 1 := by have := hpos a; have := hpos b; omega
    left
    exact ⟨a, b, hab, hx, (mul_eq_one.mp ha1).1, (mul_eq_one.mp ha1).2,
      (mul_eq_one.mp hb1).1, (mul_eq_one.mp hb1).2⟩

variable {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E] [Algebra F E]

/-! ### Primes of $E$ over a prime of $F$ -/

/-- **The relative splitting character** $\chi_{E/F}$ on the nonzero primes of $\mathcal O_F$:
$$\chi_{E/F}(\mathfrak p) = \#\{\mathfrak P \mid \mathfrak p : f(\mathfrak P \mid \mathfrak p) = 1\} - 1,$$
$\mathfrak P$ running over the primes of $\mathcal O_E$ over $\mathfrak p$ (`Ideal.primesOver`) and $f$ the inertia degree
(`Ideal.inertiaDeg`). For $[E:F] = 2$ it takes the values $1, -1, 0$ exactly when $\mathfrak p$ splits, is inert, ramifies
(`splitting`). -/
def relChar (𝔭 : HeightOneSpectrum (𝓞 F)) : ℤ :=
  ((Finset.univ : Finset (𝔭.asIdeal.primesOver (𝓞 E))).filter
    (fun P => P.1.inertiaDeg (𝓞 F) = 1)).card - 1

variable {E}

/-- $N\mathfrak P = N\mathfrak p^{f(\mathfrak P \mid \mathfrak p)}$ for a prime $\mathfrak P$ of $\mathcal O_E$ over $\mathfrak p$. -/
theorem absNorm_eq_pow_inertiaDeg (𝔭 : HeightOneSpectrum (𝓞 F)) (P : 𝔭.asIdeal.primesOver (𝓞 E)) :
    Ideal.absNorm P.1 = normP 𝔭 ^ P.1.inertiaDeg (𝓞 F) := by
  have := P.2.1
  have := P.2.2
  exact (Ideal.absNorm_pow_inertiaDeg 𝔭.asIdeal P.1).symm

/-- **The fundamental identity for $[E:F] = 2$:** $\sum_{\mathfrak P \mid \mathfrak p} e(\mathfrak P\mid\mathfrak p)\,f(\mathfrak P\mid\mathfrak p) = 2$. -/
theorem sum_ramificationIdx_mul_inertiaDeg (hdeg : Module.finrank F E = 2) (𝔭 : HeightOneSpectrum (𝓞 F)) :
    ∑ P : 𝔭.asIdeal.primesOver (𝓞 E), P.1.ramificationIdx (𝓞 F) * P.1.inertiaDeg (𝓞 F) = 2 := by
  rw [Ideal.sum_ramification_inertia_eq_finrank, ← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E, hdeg]

/-- **The splitting law in a quadratic extension** (every prime $\mathfrak p$ of $F$, dyadic and ramified primes included):
exactly one of
* $\chi_{E/F}(\mathfrak p) = 1$ and $\mathfrak p$ **splits**: two distinct primes $\mathfrak P_0, \mathfrak P_1$ over $\mathfrak p$, each with
  $e = f = 1$;
* $\chi_{E/F}(\mathfrak p) = -1$ and $\mathfrak p$ is **inert**: one prime over $\mathfrak p$, with $e = 1$, $f = 2$;
* $\chi_{E/F}(\mathfrak p) = 0$ and $\mathfrak p$ **ramifies**: one prime over $\mathfrak p$, with $e = 2$, $f = 1$.

*Proof:* $\sum e_if_i = [E:F] = 2$ (`sum_ramificationIdx_mul_inertiaDeg`) with $e_i, f_i \ge 1$ (`shape_of_sum_eq_two`). -/
@[kb "neukirch1999" "Ch. I, Prop. 8.2 [unverified]"]
theorem splitting (hdeg : Module.finrank F E = 2) (𝔭 : HeightOneSpectrum (𝓞 F)) :
    (relChar E 𝔭 = 1 ∧ ∃ P₀ P₁ : 𝔭.asIdeal.primesOver (𝓞 E), P₀ ≠ P₁ ∧ (∀ P, P = P₀ ∨ P = P₁) ∧
      P₀.1.ramificationIdx (𝓞 F) = 1 ∧ P₀.1.inertiaDeg (𝓞 F) = 1 ∧
      P₁.1.ramificationIdx (𝓞 F) = 1 ∧ P₁.1.inertiaDeg (𝓞 F) = 1) ∨
    (relChar E 𝔭 = -1 ∧ ∃ P₀ : 𝔭.asIdeal.primesOver (𝓞 E), (∀ P, P = P₀) ∧
      P₀.1.ramificationIdx (𝓞 F) = 1 ∧ P₀.1.inertiaDeg (𝓞 F) = 2) ∨
    (relChar E 𝔭 = 0 ∧ ∃ P₀ : 𝔭.asIdeal.primesOver (𝓞 E), (∀ P, P = P₀) ∧
      P₀.1.ramificationIdx (𝓞 F) = 2 ∧ P₀.1.inertiaDeg (𝓞 F) = 1) := by
  classical
  have he : ∀ P : 𝔭.asIdeal.primesOver (𝓞 E), 0 < P.1.ramificationIdx (𝓞 F) := by
    intro P; have := P.2.1; exact Ideal.ramificationIdx_pos (𝓞 F) P.1
  have hf : ∀ P : 𝔭.asIdeal.primesOver (𝓞 E), 0 < P.1.inertiaDeg (𝓞 F) := by
    intro P; have := P.2.1; exact Ideal.inertiaDeg_pos P.1 (𝓞 F)
  rcases shape_of_sum_eq_two _ _ he hf (sum_ramificationIdx_mul_inertiaDeg hdeg 𝔭) with
    ⟨a, b, hab, hx, hea, hfa, heb, hfb⟩ | ⟨a, hx, hea, hfa⟩ | ⟨a, hx, hea, hfa⟩
  · left
    refine ⟨?_, a, b, hab, hx, hea, hfa, heb, hfb⟩
    have : (Finset.univ.filter fun P : 𝔭.asIdeal.primesOver (𝓞 E) => P.1.inertiaDeg (𝓞 F) = 1) = {a, b} := by
      ext P
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro _; exact hx P
      · rintro (rfl | rfl) <;> assumption
    rw [relChar, this, Finset.card_pair hab]; norm_num
  · right; left
    refine ⟨?_, a, hx, hea, hfa⟩
    have : (Finset.univ.filter fun P : 𝔭.asIdeal.primesOver (𝓞 E) => P.1.inertiaDeg (𝓞 F) = 1) = ∅ := by
      ext P
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rw [hx P, hfa]; norm_num
    rw [relChar, this, Finset.card_empty]; norm_num
  · right; right
    refine ⟨?_, a, hx, hea, hfa⟩
    have : (Finset.univ.filter fun P : 𝔭.asIdeal.primesOver (𝓞 E) => P.1.inertiaDeg (𝓞 F) = 1) = {a} := by
      ext P
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro _; exact hx P
      · rintro rfl; exact hfa
    rw [relChar, this, Finset.card_singleton]; norm_num

/-- $\chi_{E/F}(\mathfrak p) \in \{1, -1, 0\}$. -/
theorem relChar_mem (hdeg : Module.finrank F E = 2) (𝔭 : HeightOneSpectrum (𝓞 F)) :
    relChar E 𝔭 = 1 ∨ relChar E 𝔭 = -1 ∨ relChar E 𝔭 = 0 := by
  rcases splitting hdeg 𝔭 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]

theorem abs_relChar_le_one (hdeg : Module.finrank F E = 2) (𝔭 : HeightOneSpectrum (𝓞 F)) :
    |(relChar E 𝔭 : ℝ)| ≤ 1 := by
  rcases relChar_mem hdeg 𝔭 with h | h | h <;> simp [h]

/-- **The fibre product over the primes of $E$ above $\mathfrak p$**, for any function $h$ of the norm, with $q = N\mathfrak p$:
$\prod_{\mathfrak P \mid \mathfrak p} h(N\mathfrak P)$ is $h(q)^2$ if $\chi(\mathfrak p) = 1$, $h(q^2)$ if $\chi(\mathfrak p) = -1$, $h(q)$ if
$\chi(\mathfrak p) = 0$. -/
theorem prod_fiber {M : Type*} [CommMonoid M] (hdeg : Module.finrank F E = 2) (𝔭 : HeightOneSpectrum (𝓞 F))
    (h : ℕ → M) :
    (relChar E 𝔭 = 1 ∧ ∏ P : 𝔭.asIdeal.primesOver (𝓞 E), h (Ideal.absNorm P.1) = h (normP 𝔭) * h (normP 𝔭)) ∨
    (relChar E 𝔭 = -1 ∧ ∏ P : 𝔭.asIdeal.primesOver (𝓞 E), h (Ideal.absNorm P.1) = h (normP 𝔭 ^ 2)) ∨
    (relChar E 𝔭 = 0 ∧ ∏ P : 𝔭.asIdeal.primesOver (𝓞 E), h (Ideal.absNorm P.1) = h (normP 𝔭)) := by
  classical
  simp_rw [absNorm_eq_pow_inertiaDeg 𝔭]
  rcases splitting hdeg 𝔭 with ⟨hχ, a, b, hab, hx, -, hfa, -, hfb⟩ | ⟨hχ, a, hx, -, hfa⟩ | ⟨hχ, a, hx, -, hfa⟩
  · left
    refine ⟨hχ, ?_⟩
    have : (Finset.univ : Finset (𝔭.asIdeal.primesOver (𝓞 E))) = {a, b} := by
      ext P; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]; exact hx P
    rw [this, Finset.prod_pair hab, hfa, hfb, pow_one]
  · right; left
    refine ⟨hχ, ?_⟩
    rw [Fintype.prod_eq_single a (fun P hP => absurd (hx P) hP), hfa]
  · right; right
    refine ⟨hχ, ?_⟩
    rw [Fintype.prod_eq_single a (fun P hP => absurd (hx P) hP), hfa, pow_one]

/-- **The local factor identity** (the Euler factor at $\mathfrak p$, every prime including the dyadic and ramified ones):
$$\prod_{\mathfrak P \mid \mathfrak p}(1 - N\mathfrak P^{-s})^{-1} = (1 - N\mathfrak p^{-s})^{-1}\,(1 - \chi_{E/F}(\mathfrak p)\,N\mathfrak p^{-s})^{-1}$$
for every real $s$. -/
@[kb "neukirch1999" "Ch. VII §5 [unverified]"]
theorem localFactor_eq (hdeg : Module.finrank F E = 2) (𝔭 : HeightOneSpectrum (𝓞 F)) (s : ℝ) :
    ∏ P : 𝔭.asIdeal.primesOver (𝓞 E), (1 - (Ideal.absNorm P.1 : ℝ) ^ (-s))⁻¹ =
      (1 - (normP 𝔭 : ℝ) ^ (-s))⁻¹ * (1 - (relChar E 𝔭 : ℝ) * (normP 𝔭 : ℝ) ^ (-s))⁻¹ := by
  rcases prod_fiber hdeg 𝔭 (fun n => (1 - (n : ℝ) ^ (-s))⁻¹) with
    ⟨hχ, hprod⟩ | ⟨hχ, hprod⟩ | ⟨hχ, hprod⟩ <;> rw [hprod, hχ]
  · simp
  · have : (((normP 𝔭 ^ 2 : ℕ) : ℝ)) ^ (-s) = ((normP 𝔭 : ℝ) ^ (-s)) ^ 2 := by
      push_cast; rw [Real.rpow_pow_comm (Nat.cast_nonneg _)]
    simp only [this, ← mul_inv]; congr 1; push_cast; ring
  · simp

end QuadFormsKB.Binary.Rel
