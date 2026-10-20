/-
# Quadratic twists have no pole at $s = 1$: the $\zeta_E/\zeta_F$ argument

**Layer:** global analytic number theory over a number field $F$; the only analytic inputs are Mathlib's residue formula
for Dedekind zeta functions (for $F$ and for a quadratic extension $E$) and the Euler product (`NFEuler.hasProd_dedekindZeta`).

Weil (1982, §4.5, p. 106): "only the one corresponding to $\lambda = 1$ gives a residue for $s = 0$". For a nontrivial
quadratic character $\lambda$, attached to $E = F(\sqrt a)$, Weil appeals to Hecke's theory. We use instead the factorization
$\zeta_E = \zeta_F\cdot L(\cdot,\chi)$ **as an inequality of Euler products**, which is purely local at each prime:

* at a prime $\mathfrak p$ with $\chi(\mathfrak p) = 1$ we are given that $a$ is a square in $F_\mathfrak p$, so $\mathfrak p$ splits in $E$
  into two primes of norm $N\mathfrak p$ (`SqLG.exists_two_primes_of_isSquare`): the factor of $\zeta_F L$ is $(1 - N\mathfrak p^{-\sigma})^{-2}$,
  the product of the two factors of $\zeta_E$;
* at a prime with $\chi(\mathfrak p) = -1$ the factor of $\zeta_F L$ is $(1 - N\mathfrak p^{-2\sigma})^{-1}$, and any prime $\mathfrak P \mid \mathfrak p$ of
  $E$ has $N\mathfrak P \le N\mathfrak p^2$ (`absNorm_le_sq_of_comap`), so $(1 - N\mathfrak P^{-\sigma})^{-1} \ge (1 - N\mathfrak p^{-2\sigma})^{-1}$.

Hence $\zeta_F^{(B)}(\sigma)L^{(B)}(\sigma,\chi) \le \zeta_E(\sigma)$ outside a finite set $B$ (`prod_le_dedekindZetaR`), and
$$s\,L(1+s,\chi) \le C\,\frac{s\,\zeta_E(1+s)}{\zeta_F(1+s)} \to \rho_E\cdot 0 = 0\qquad(s \to 0^+)$$
(**`tendsto_mul_LFunction_zero`**). No analytic continuation of Hecke $L$-functions and no class field theory is used.
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Tamagawa.SquareClassParam
import QuadFormsKB.Tamagawa.ZetaResidue

open NumberField IsDedekindDomain Filter Topology
open QuadFormsKB.NFEuler

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QTwist

variable {F : Type} [Field F] [NumberField F]

/-- **Residue degree at most $2$:** a prime $\mathfrak P$ of a quadratic extension $L$ over $\mathfrak p$ has
$N\mathfrak P = N\mathfrak p^{f} \le N\mathfrak p^2$ ($ef \le \sum e_if_i = 2$, `Ideal.sum_ramification_inertia`). -/
theorem absNorm_le_sq_of_comap {L : Type} [Field L] [NumberField L] [Algebra F L]
    (hdeg : Module.finrank F L = 2) (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 L))
    (hP : P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 L)) = v.asIdeal) :
    Ideal.absNorm P.asIdeal ≤ Ideal.absNorm v.asIdeal ^ 2 := by
  haveI : P.asIdeal.LiesOver v.asIdeal := ⟨by rw [Ideal.under_def, hP]⟩
  haveI := v.isMaximal
  haveI := P.isMaximal
  have hnorm : Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal ^ P.asIdeal.inertiaDeg (𝓞 F) := by
    rw [← Ideal.absNorm_relNorm (𝓞 F) (𝓞 L), Ideal.relNorm_eq_pow_of_isMaximal P.asIdeal v.asIdeal, map_pow]
  have hsum := Ideal.sum_ramification_inertia (p := v.asIdeal) (𝓞 L) F L v.ne_bot
  rw [hdeg] at hsum
  have hmemP : P.asIdeal ∈ IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 L) :=
    (IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot _).2 ⟨inferInstance, inferInstance⟩
  have hle : v.asIdeal.ramificationIdx' P.asIdeal * v.asIdeal.inertiaDeg' P.asIdeal ≤ 2 := by
    rw [← hsum]
    exact Finset.single_le_sum (f := fun X => v.asIdeal.ramificationIdx' X * v.asIdeal.inertiaDeg' X)
      (fun _ _ => Nat.zero_le _) hmemP
  have hmap : Ideal.map (algebraMap (𝓞 F) (𝓞 L)) v.asIdeal ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]
    exact v.ne_bot
  have heP := Ideal.IsDedekindDomain.ramificationIdx_ne_zero hmap P.isPrime
    (Ideal.map_le_iff_le_comap.2 hP.ge)
  have hf : P.asIdeal.inertiaDeg (𝓞 F) ≤ 2 := by
    have := Nat.one_le_iff_ne_zero.2 heP
    have h' : v.asIdeal.inertiaDeg' P.asIdeal ≤ 2 := by nlinarith
    rw [Ideal.inertiaDeg_eq_inertiaDeg'] at h'
    exact h'
  rw [hnorm]
  have h1 : 1 ≤ Ideal.absNorm v.asIdeal := le_trans one_le_two (two_le_normP v)
  exact Nat.pow_le_pow_right h1 hf

lemma rpow_neg_le_half (p : HeightOneSpectrum (𝓞 F)) {σ : ℝ} (hσ : 1 ≤ σ) : (normP p : ℝ) ^ (-σ) ≤ 1 / 2 :=
  rpow_neg_normP_le_half p hσ

lemma one_sub_pos (p : HeightOneSpectrum (𝓞 F)) {σ : ℝ} (hσ : 1 ≤ σ) {c : ℝ} (hc : |c| ≤ 1) :
    0 < 1 - c * (normP p : ℝ) ^ (-σ) := by
  have h1 := rpow_neg_le_half p hσ
  have h0 := rpow_neg_normP_pos p σ
  have : |c * (normP p : ℝ) ^ (-σ)| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos h0]; nlinarith [abs_nonneg c]
  have := (abs_le.mp this).2
  linarith

variable {L : Type} [Field L] [NumberField L] [Algebra F L]

/-- **The local comparison** at a prime $\mathfrak p \nmid 2a$ with $\chi(\mathfrak p) = \pm1$ (and $\chi(\mathfrak p) = 1 \Rightarrow a \in F_\mathfrak p^{\times2}$):
there is a finite set $C$ of primes of $L = F(\sqrt a)$ over $\mathfrak p$ with
$(1-N\mathfrak p^{-\sigma})^{-1}(1-\chi(\mathfrak p)N\mathfrak p^{-\sigma})^{-1} \le \prod_{\mathfrak P\in C}(1-N\mathfrak P^{-\sigma})^{-1}$. -/
theorem exists_local_cover (a : 𝓞 F) (hd : ¬ IsSquare (a : F)) (s : L) (hs : s ^ 2 = algebraMap F L (a : F))
    (hspan : ∀ y : L, ∃ b₀ b₁ : F, y = algebraMap F L b₀ + algebraMap F L b₁ * s)
    (p : HeightOneSpectrum (𝓞 F)) (h2a : 2 * a ∉ p.asIdeal) (c : ℝ) (hc : c = 1 ∨ c = -1)
    (hsplit : c = 1 → IsSquare (algebraMap F (p.adicCompletion F) (a : F))) {σ : ℝ} (hσ : 1 < σ) :
    ∃ C : Finset (HeightOneSpectrum (𝓞 L)),
      (∀ P ∈ C, P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 L)) = p.asIdeal) ∧
      (1 - (normP p : ℝ) ^ (-σ))⁻¹ * (1 - c * (normP p : ℝ) ^ (-σ))⁻¹ ≤
        ∏ P ∈ C, (1 - (normP P : ℝ) ^ (-σ))⁻¹ := by
  classical
  obtain ⟨hQ, -, -, -⟩ := HN.quadData (a : F) hd s hs hspan
  have hdeg : Module.finrank F L = 2 := hQ.finrank_eq_two
  rcases hc with rfl | rfl
  · obtain ⟨P, Q, hPQ, hP, hQ', hnP, hnQ⟩ := SqLG.exists_two_primes_of_isSquare a hd s hs hspan p h2a (hsplit rfl)
    refine ⟨{P, Q}, ?_, ?_⟩
    · intro R hR
      simp only [Finset.mem_insert, Finset.mem_singleton] at hR
      rcases hR with rfl | rfl <;> assumption
    · rw [Finset.prod_pair hPQ]
      simp only [normP, hnP, hnQ, one_mul]
      rfl
  · obtain ⟨w, hw⟩ := HN.exists_over (L := L) p
    have hP : w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 L)) = p.asIdeal := by rw [← hw]; rfl
    refine ⟨{w}, fun P hP' => by rw [Finset.mem_singleton.mp hP']; exact hP, ?_⟩
    rw [Finset.prod_singleton]
    have hN : (normP w : ℝ) ≤ (normP p : ℝ) ^ 2 := by
      exact_mod_cast absNorm_le_sq_of_comap hdeg p w hP
    have hp0 : (0 : ℝ) < normP p := by have := two_le_normP p; positivity
    have hw0 : (0 : ℝ) < normP w := by have := two_le_normP w; positivity
    have hle : ((normP p : ℝ) ^ 2) ^ (-σ) ≤ (normP w : ℝ) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos hw0 hN (by linarith)
    have hsq : ((normP p : ℝ) ^ 2) ^ (-σ) = ((normP p : ℝ) ^ (-σ)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
      ring_nf
    have hx := rpow_neg_le_half p hσ.le
    have hx0 := rpow_neg_normP_pos p σ
    have hy := rpow_neg_le_half w hσ.le
    rw [← mul_inv, inv_le_inv₀ (by nlinarith) (by linarith)]
    nlinarith

/-- **$\zeta_F^{(B)}L^{(B)}(\sigma,\chi) \le \zeta_L(\sigma)$ on finite sets of primes** (the Euler-product form of $\zeta_L = \zeta_FL(\cdot,\chi)$,
as an inequality). -/
theorem prod_le_dedekindZetaR (a : 𝓞 F) (hd : ¬ IsSquare (a : F)) (s : L) (hs : s ^ 2 = algebraMap F L (a : F))
    (hspan : ∀ y : L, ∃ b₀ b₁ : F, y = algebraMap F L b₀ + algebraMap F L b₁ * s)
    (B : Finset (HeightOneSpectrum (𝓞 F))) (hB : ∀ p ∉ B, 2 * a ∉ p.asIdeal)
    (χ : HeightOneSpectrum (𝓞 F) → ℝ) (hχ : ∀ p ∉ B, χ p = 1 ∨ χ p = -1)
    (hsplit : ∀ p ∉ B, χ p = 1 → IsSquare (algebraMap F (p.adicCompletion F) (a : F))) {σ : ℝ} (hσ : 1 < σ)
    (A : Finset (HeightOneSpectrum (𝓞 F))) (hA : ∀ p ∈ A, p ∉ B) :
    ∏ p ∈ A, ((1 - (normP p : ℝ) ^ (-σ))⁻¹ * (1 - χ p * (normP p : ℝ) ^ (-σ))⁻¹) ≤ dedekindZetaR L σ := by
  classical
  have hex : ∀ p ∈ A, ∃ C : Finset (HeightOneSpectrum (𝓞 L)),
      (∀ P ∈ C, P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 L)) = p.asIdeal) ∧
      (1 - (normP p : ℝ) ^ (-σ))⁻¹ * (1 - χ p * (normP p : ℝ) ^ (-σ))⁻¹ ≤
        ∏ P ∈ C, (1 - (normP P : ℝ) ^ (-σ))⁻¹ := fun p hp =>
    exists_local_cover a hd s hs hspan p (hB p (hA p hp)) (χ p) (hχ p (hA p hp)) (hsplit p (hA p hp)) hσ
  choose! C hC1 hC2 using hex
  have hdisj : (A : Set (HeightOneSpectrum (𝓞 F))).PairwiseDisjoint C := by
    intro p hp p' hp' hpp'
    rw [Function.onFun, Finset.disjoint_left]
    intro P hP hP'
    apply hpp'
    exact HeightOneSpectrum.ext ((hC1 p hp P hP).symm.trans (hC1 p' hp' P hP'))
  have hg1 : ∀ P : HeightOneSpectrum (𝓞 L), 1 ≤ (1 - (normP P : ℝ) ^ (-σ))⁻¹ := by
    intro P
    have := rpow_neg_le_half P hσ.le
    have := rpow_neg_normP_pos P σ
    rw [one_le_inv₀ (by linarith)]; linarith
  calc ∏ p ∈ A, ((1 - (normP p : ℝ) ^ (-σ))⁻¹ * (1 - χ p * (normP p : ℝ) ^ (-σ))⁻¹)
      ≤ ∏ p ∈ A, ∏ P ∈ C p, (1 - (normP P : ℝ) ^ (-σ))⁻¹ := by
        refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => hC2 p hp)
        have h1 := one_sub_pos p hσ.le (c := 1) (by norm_num)
        have h2 := one_sub_pos p hσ.le (c := χ p) (by
          rcases hχ p (hA p hp) with h | h <;> rw [h] <;> norm_num)
        rw [one_mul] at h1
        positivity
    _ = ∏ P ∈ A.biUnion C, (1 - (normP P : ℝ) ^ (-σ))⁻¹ := (Finset.prod_biUnion hdisj).symm
    _ ≤ dedekindZetaR L σ := prod_le_of_hasProd (hasProd_dedekindZeta hσ) hg1 _

lemma finite_mem_asIdeal {c : 𝓞 F} (hc : c ≠ 0) : {v : HeightOneSpectrum (𝓞 F) | c ∈ v.asIdeal}.Finite := by
  have hne : Ideal.span {c} ≠ 0 := by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hc
  refine (Ideal.finite_factors hne).subset fun v hv => ?_
  simp only [Set.mem_ofPred_eq] at hv ⊢
  exact Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hv)

lemma abs_lfac_sub_one_le (p : HeightOneSpectrum (𝓞 F)) {σ : ℝ} (hσ : 1 ≤ σ) {c : ℝ} (hc : |c| ≤ 1) :
    |(1 - c * (normP p : ℝ) ^ (-σ))⁻¹ - 1| ≤ 2 * (normP p : ℝ) ^ (-σ) := by
  have hpos := one_sub_pos p hσ hc
  have h1 := rpow_neg_le_half p hσ
  have h0 := rpow_neg_normP_pos p σ
  have hD : 1 / 2 ≤ 1 - c * (normP p : ℝ) ^ (-σ) := by
    have : |c * (normP p : ℝ) ^ (-σ)| ≤ 1 / 2 := by
      rw [abs_mul, abs_of_pos h0]; nlinarith [abs_nonneg c]
    linarith [(abs_le.mp this).2]
  have e : (1 - c * (normP p : ℝ) ^ (-σ))⁻¹ - 1 = c * (normP p : ℝ) ^ (-σ) / (1 - c * (normP p : ℝ) ^ (-σ)) := by
    field_simp; ring
  rw [e, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  have : |c * (normP p : ℝ) ^ (-σ)| ≤ (normP p : ℝ) ^ (-σ) := by
    rw [abs_mul, abs_of_pos h0]; nlinarith [abs_nonneg c]
  nlinarith

/-- **A nontrivial quadratic twist has no pole at $s = 1$** (Weil 1982, §4.5, p. 106: "only the one corresponding to $\lambda = 1$
gives a residue"; here via $\zeta_E/\zeta_F$, without Hecke $L$-functions). Let $a \in \mathcal O_F$ be a non-square, $S$ a finite
set of primes, and $\chi$ with $\chi = 0$ on $S$, $\chi = \pm1$ off $S$, and $\chi(\mathfrak p) = 1 \Rightarrow a \in F_\mathfrak p^{\times2}$. Then
$$s\prod_\mathfrak p\big(1 - \chi(\mathfrak p)N\mathfrak p^{-1-s}\big)^{-1} \longrightarrow 0\qquad(s \to 0^+).$$
*Proof:* $\zeta_F^{(B)}L(\sigma,\chi)^{(B)} \le \zeta_E(\sigma)$, $E = F(\sqrt a)$ (`prod_le_dedekindZetaR`), so
$s L(1+s,\chi) \le 4^{|B|}\,s\zeta_E(1+s)/\zeta_F(1+s) \to 4^{|B|}\rho_E\cdot 0$. -/
@[kb "weil1982" "§4.5, p. 106 (only λ = 1 gives a residue at s = 0)"]
theorem tendsto_mul_LFunction_zero (S : Finset (HeightOneSpectrum (𝓞 F))) (a : 𝓞 F) (hd : ¬ IsSquare (a : F))
    (χ : HeightOneSpectrum (𝓞 F) → ℝ) (hχS : ∀ p ∈ S, χ p = 0) (hχ : ∀ p ∉ S, χ p = 1 ∨ χ p = -1)
    (hsplit : ∀ p ∉ S, χ p = 1 → IsSquare (algebraMap F (p.adicCompletion F) (a : F))) :
    Tendsto (fun s : ℝ => s * ∏' p, (1 - χ p * (normP p : ℝ) ^ (-(1 + s)))⁻¹) (𝓝[>] 0) (𝓝 0) := by
  classical
  obtain ⟨L, _, _, _, s₀, hs₀, hspan⟩ := QuadFormsKB.Lam.exists_quadExt (a : F) hd
  have ha0 : a ≠ 0 := by rintro rfl; exact hd ⟨0, by simp⟩
  have h2a0 : (2 * a : 𝓞 F) ≠ 0 := mul_ne_zero two_ne_zero ha0
  set B : Finset (HeightOneSpectrum (𝓞 F)) := S ∪ (finite_mem_asIdeal h2a0).toFinset
  have hB : ∀ p ∉ B, 2 * a ∉ p.asIdeal := fun p hp h => hp (Finset.mem_union_right _
    ((finite_mem_asIdeal h2a0).mem_toFinset.mpr h))
  have hBS : ∀ p ∉ B, p ∉ S := fun p hp h => hp (Finset.mem_union_left _ h)
  have hχabs : ∀ p, |χ p| ≤ 1 := by
    intro p
    by_cases hp : p ∈ S
    · rw [hχS p hp]; simp
    · rcases hχ p hp with h | h <;> rw [h] <;> simp
  -- the key bound for σ > 1
  have key : ∀ σ : ℝ, 1 < σ → ∏' p, (1 - χ p * (normP p : ℝ) ^ (-σ))⁻¹ ≤
      4 ^ B.card * dedekindZetaR L σ * (dedekindZetaR F σ)⁻¹ := by
    intro σ hσ
    set f : HeightOneSpectrum (𝓞 F) → ℝ := fun p => (1 - χ p * (normP p : ℝ) ^ (-σ))⁻¹
    have hfpos : ∀ p, 0 < f p := fun p => inv_pos.mpr (one_sub_pos p hσ.le (hχabs p))
    have hfle : ∀ p, f p ≤ 2 := by
      intro p
      have h := abs_lfac_sub_one_le p hσ.le (hχabs p)
      have := rpow_neg_le_half p hσ.le
      have := (abs_le.mp h).2
      simp only [f]; linarith
    have hfm : Multipliable f :=
      multipliable_of_abs_sub_one_le f (C := 2) hσ
        (Filter.Eventually.of_forall (f := Filter.cofinite) fun p => abs_lfac_sub_one_le p hσ.le (hχabs p))
    set h : HeightOneSpectrum (𝓞 F) → ℝ := fun p =>
      (1 - (normP p : ℝ) ^ (-σ))⁻¹ * (if p ∈ B then 1 - (normP p : ℝ) ^ (-σ) else 1)
    have hhprod : HasProd h (dedekindZetaR F σ * ∏ p ∈ B, (1 - (normP p : ℝ) ^ (-σ))) := by
      refine (hasProd_dedekindZeta hσ).mul ?_
      have : HasProd (fun p : HeightOneSpectrum (𝓞 F) => if p ∈ B then 1 - (normP p : ℝ) ^ (-σ) else 1)
          (∏ p ∈ B, if p ∈ B then 1 - (normP p : ℝ) ^ (-σ) else 1) :=
        hasProd_prod_of_ne_finset_one (fun p hp => by simp [hp])
      convert this using 1
      exact (Finset.prod_congr rfl fun p hp => by simp [hp]).symm
    have hk := hfm.hasProd.mul hhprod
    -- partial products of k are bounded by 2^|B| ζ_L(σ)
    have hpart : ∀ A : Finset (HeightOneSpectrum (𝓞 F)), ∏ p ∈ A, (f p * h p) ≤ 2 ^ B.card * dedekindZetaR L σ := by
      intro A
      rw [← Finset.prod_filter_mul_prod_filter_not A (· ∈ B)]
      have hzL : 0 < dedekindZetaR L σ := lt_of_lt_of_le one_pos (one_le_dedekindZetaR hσ)
      have h1 : ∏ p ∈ A.filter (· ∈ B), (f p * h p) ≤ 2 ^ B.card := by
        calc ∏ p ∈ A.filter (· ∈ B), (f p * h p) = ∏ p ∈ A.filter (· ∈ B), f p := by
              refine Finset.prod_congr rfl fun p hp => ?_
              have hpB : p ∈ B := (Finset.mem_filter.mp hp).2
              have : 1 - (normP p : ℝ) ^ (-σ) ≠ 0 := (one_sub_pos p hσ.le (c := 1) (by norm_num)).ne' |>.symm.symm |>
                fun h' => by simpa using h'
              simp only [h, hpB, if_true, inv_mul_cancel₀ this, mul_one]
          _ ≤ ∏ p ∈ A.filter (· ∈ B), (2 : ℝ) := Finset.prod_le_prod₀ (fun p _ => (hfpos p).le) fun p _ => hfle p
          _ = 2 ^ (A.filter (· ∈ B)).card := by rw [Finset.prod_const]
          _ ≤ 2 ^ B.card := pow_le_pow_right₀ (by norm_num) (Finset.card_le_card fun p hp =>
              (Finset.mem_filter.mp hp).2)
      have h2 : ∏ p ∈ A.filter (· ∉ B), (f p * h p) ≤ dedekindZetaR L σ := by
        calc ∏ p ∈ A.filter (· ∉ B), (f p * h p) =
            ∏ p ∈ A.filter (· ∉ B), ((1 - (normP p : ℝ) ^ (-σ))⁻¹ * (1 - χ p * (normP p : ℝ) ^ (-σ))⁻¹) := by
              refine Finset.prod_congr rfl fun p hp => ?_
              have hpB : p ∉ B := (Finset.mem_filter.mp hp).2
              simp only [f, h, hpB, if_false, mul_one]; ring
          _ ≤ dedekindZetaR L σ := prod_le_dedekindZetaR a hd s₀ hs₀ hspan B hB χ
              (fun p hp => hχ p (hBS p hp)) (fun p hp => hsplit p (hBS p hp)) hσ _
              (fun p hp => (Finset.mem_filter.mp hp).2)
      have h2' : 0 ≤ ∏ p ∈ A.filter (· ∉ B), (f p * h p) := by
        refine Finset.prod_nonneg fun p hp => mul_nonneg (hfpos p).le ?_
        have hpB : p ∉ B := (Finset.mem_filter.mp hp).2
        simp only [h, hpB, if_false, mul_one]
        exact (inv_pos.mpr (by simpa using one_sub_pos p hσ.le (c := 1) (by norm_num))).le
      calc _ ≤ (2 : ℝ) ^ B.card * dedekindZetaR L σ :=
            mul_le_mul h1 h2 h2' (by positivity)
        _ = _ := rfl
    have hlim : (∏' p, f p) * (dedekindZetaR F σ * ∏ p ∈ B, (1 - (normP p : ℝ) ^ (-σ))) ≤
        2 ^ B.card * dedekindZetaR L σ :=
      le_of_tendsto' hk fun A => by simpa [Finset.prod_mul_distrib] using hpart A
    have hBprod : (1 / 2) ^ B.card ≤ ∏ p ∈ B, (1 - (normP p : ℝ) ^ (-σ)) := by
      rw [← Finset.prod_const]
      refine Finset.prod_le_prod₀ (fun _ _ => by norm_num) fun p _ => ?_
      have := rpow_neg_le_half p hσ.le; linarith
    have hzF : 1 ≤ dedekindZetaR F σ := one_le_dedekindZetaR hσ
    have hfnn : 0 ≤ ∏' p, f p := tprod_nonneg fun p => (hfpos p).le
    have hpos : 0 < dedekindZetaR F σ * (1 / 2) ^ B.card := by positivity
    have hmain : (∏' p, f p) * dedekindZetaR F σ * (1 / 2) ^ B.card ≤ 2 ^ B.card * dedekindZetaR L σ := by
      calc (∏' p, f p) * dedekindZetaR F σ * (1 / 2) ^ B.card
          = (∏' p, f p) * (dedekindZetaR F σ * (1 / 2) ^ B.card) := by ring
        _ ≤ (∏' p, f p) * (dedekindZetaR F σ * ∏ p ∈ B, (1 - (normP p : ℝ) ^ (-σ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hBprod (by linarith)) hfnn
        _ ≤ _ := hlim
    have h2n : (2 : ℝ) ^ B.card * (1 / 2) ^ B.card = 1 := by rw [← mul_pow]; norm_num
    have hzF0 : (dedekindZetaR F σ) ≠ 0 := by linarith
    calc ∏' p, f p = ((∏' p, f p) * dedekindZetaR F σ * (1 / 2) ^ B.card) * (2 ^ B.card * (dedekindZetaR F σ)⁻¹) := by
          field_simp
          rw [mul_assoc, mul_comm ((1 / 2 : ℝ) ^ B.card), h2n, mul_one]
      _ ≤ (2 ^ B.card * dedekindZetaR L σ) * (2 ^ B.card * (dedekindZetaR F σ)⁻¹) :=
          mul_le_mul_of_nonneg_right hmain (by positivity)
      _ = 4 ^ B.card * dedekindZetaR L σ * (dedekindZetaR F σ)⁻¹ := by
          rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]; ring
  -- limits
  have hL := GlobalZeta.tendsto_mul_dedekindZetaR_one_add (F := L)
  have hF := GlobalZeta.tendsto_mul_dedekindZetaR_one_add (F := F)
  have hinvF : Tendsto (fun s : ℝ => (dedekindZetaR F (1 + s))⁻¹) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => s * (s * dedekindZetaR F (1 + s))⁻¹) (𝓝[>] 0)
        (𝓝 (0 * (dedekindZeta_residue F)⁻¹)) :=
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).mul (hF.inv₀ (dedekindZeta_residue_pos F).ne')
    rw [zero_mul] at h1
    refine h1.congr' (eventually_nhdsWithin_of_forall fun s hs => ?_)
    have hs0 : (s : ℝ) ≠ 0 := (Set.mem_Ioi.mp hs).ne'
    have hz : dedekindZetaR F (1 + s) ≠ 0 := by
      have := one_le_dedekindZetaR (F := F) (show 1 < 1 + s by linarith [Set.mem_Ioi.mp hs]); linarith
    field_simp
  have hupper : Tendsto (fun s : ℝ => 4 ^ B.card * (s * dedekindZetaR L (1 + s)) * (dedekindZetaR F (1 + s))⁻¹)
      (𝓝[>] 0) (𝓝 0) := by
    have := (tendsto_const_nhds (x := (4 : ℝ) ^ B.card)).mul hL |>.mul hinvF
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact mul_nonneg (Set.mem_Ioi.mp hs).le (tprod_nonneg fun p =>
      (inv_pos.mpr (one_sub_pos p (by linarith [Set.mem_Ioi.mp hs]) (hχabs p))).le)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : (0 : ℝ) < s := hs
    have := key (1 + s) (by linarith)
    calc s * ∏' p, (1 - χ p * (normP p : ℝ) ^ (-(1 + s)))⁻¹
        ≤ s * (4 ^ B.card * dedekindZetaR L (1 + s) * (dedekindZetaR F (1 + s))⁻¹) :=
          mul_le_mul_of_nonneg_left this hs'.le
      _ = _ := by ring

end QuadFormsKB.QTwist
