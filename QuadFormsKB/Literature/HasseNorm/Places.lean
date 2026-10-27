/-
# Hasse norm theorem, step 3 (cont.): places of a quadratic extension and the count $2^{s'-1}$

For $L/F$ quadratic with nontrivial automorphism $\sigma$:

* `two_primes_of_isSquare`: if $L = F(s)$, $s^2 = a$, and $a$ is a square in $F_v$ ($v$ finite, any
  residue characteristic), then $v$ splits (two primes above), by a valuation argument with
  $z = s - c$, $c \approx \sqrt a$ in $F_v$;
* `ramificationIdx_eq_one`: primes not dividing $2a$ are unramified;
* `ef_of_two`, `ef_of_unique`: $e$, $f$ when there are two primes / one prime above $\mathfrak p$;
* `card_overS_add`, `card_infinitePlace_add`: $|S_L| + \#\{\text{non-split in } S\} = 2|S|$, and likewise for the
  infinite places;
* `index_normsF_eq`: $2\,[F_S^\times : N L_{S_L}^\times] = 2^{s'}$ with $s'$ the number of non-split places in
  $S \cup \{\infty\}$ (when $S$ contains the ramified primes and $\mathrm{Cl}_S(F) = 1$).

See `Herbrand.lean` for the overall plan. Locators are from memory and still `[unverified]`.
-/
import QuadFormsKB.Literature.HasseNorm.FirstInequality

open Module NumberField IsDedekindDomain WithZero
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.HN

variable {F L : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
  [Algebra.IsQuadraticExtension F L] (σ : L ≃ₐ[F] L)

/-- The valuation of $F_v$ restricted to $F$ is the $v$-adic valuation. -/
lemma valued_algebraMap (v : HeightOneSpectrum (𝓞 F)) (y : F) :
    Valued.v (algebraMap F (v.adicCompletion F) y) = v.valuation F y := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion (𝓞 F)]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v y

/-- **A local square splits:** if $a = s^2$ ($s \in L$, $\sigma s = -s$, $a \ne 0$) is a square in $F_v$, then
there are two distinct primes of $L$ above $v$. -/
@[kb "neukirch1999" "Ch. II, Prop. 8.2 (decomposition of primes) [unverified]"]
theorem two_primes_of_isSquare (s : L) (a : F) (hs : s ^ 2 = algebraMap F L a)
    (hσs : σ s = -s) (ha : ¬ IsSquare a) (v : HeightOneSpectrum (𝓞 F))
    (hsq : IsSquare (algebraMap F (v.adicCompletion F) a)) :
    ∃ w w' : HeightOneSpectrum (𝓞 L), w ≠ w' ∧ under (F := F) w = v ∧ under (F := F) w' = v := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨w, hw⟩ := exists_over (L := L) v
  have huniq : ∀ w' : HeightOneSpectrum (𝓞 L), under (F := F) w' = v → w' = w := by
    intro w' hw'
    by_contra hne
    exact hcon w w' (Ne.symm hne) hw hw'
  have hfix : comapEquiv (σO σ) w = w := huniq _ (by rw [under_comapEquiv, hw])
  have ha0 : a ≠ 0 := by rintro rfl; exact ha ⟨0, by simp⟩
  have : CharZero (v.adicCompletion F) :=
    charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  set Fv := v.adicCompletion F
  obtain ⟨α, hα⟩ := hsq
  have hα0 : α ≠ 0 := by
    rintro rfl
    simp only [mul_zero] at hα
    exact ha0 ((map_eq_zero_iff _ (algebraMap F Fv).injective).mp hα)
  have h2α : (2 : Fv) * α ≠ 0 := mul_ne_zero two_ne_zero hα0
  set γ := Valued.v ((2 : Fv) * α) with hγ
  have hγ0 : γ ≠ 0 := (Valuation.ne_zero_iff _).mpr h2α
  obtain ⟨c, hc⟩ : ∃ c : F, Valued.v (algebraMap F Fv c - α) < γ := by
    have hn : {z : Fv | Valued.v (z - α) < γ} ∈ nhds α := by
      have h0 : {u : Fv | Valued.v u < 1} ∈ nhds (0 : Fv) := Valued.mem_nhds.mpr ⟨1, by simp⟩
      have hcont : Continuous fun z : Fv => (z - α) / (2 * α) :=
        (continuous_sub_right α).div_const _
      have h1 := hcont.continuousAt (x := α) (by simpa using h0)
      refine Filter.mem_of_superset h1 ?_
      intro z hz
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, map_div₀] at hz
      rw [div_lt_one₀ (zero_lt_iff.mpr hγ0)] at hz
      exact hz
    obtain ⟨_, h1, ⟨c, rfl⟩⟩ := mem_closure_iff_nhds.mp
      (HeightOneSpectrum.denseRange_algebraMap F v α) _ hn
    exact ⟨c, h1⟩
  have hcα : Valued.v (algebraMap F Fv c + α) = γ := by
    have : algebraMap F Fv c + α = 2 * α + (algebraMap F Fv c - α) := by ring
    rw [this, Valuation.map_add_eq_of_lt_left _ hc]
  have hloc : Valued.v (algebraMap F Fv (c ^ 2 - a)) < Valued.v (algebraMap F Fv (4 * a)) := by
    have e1 : algebraMap F Fv (c ^ 2 - a) = (algebraMap F Fv c - α) * (algebraMap F Fv c + α) := by
      rw [map_sub, map_pow, hα]; ring
    have e2 : algebraMap F Fv (4 * a) = (2 * α) * (2 * α) := by
      rw [map_mul, hα, map_ofNat]; ring
    rw [e1, e2, map_mul, map_mul, hcα, ← hγ]
    exact mul_lt_mul_of_pos_right hc (zero_lt_iff.mpr hγ0)
  rw [valued_algebraMap, valued_algebraMap] at hloc
  -- in L
  set W := w.valuation L
  set e := w.asIdeal.ramificationIdx (𝓞 F)
  have he : e ≠ 0 := ramificationIdx_ne_zero (F := F) w
  set z : L := s - algebraMap F L c with hz
  have hσz : σ z = -s - algebraMap F L c := by rw [hz, map_sub, hσs, σ.commutes]
  have hWσz : W (σ z) = W z := by
    rw [valuation_galois, hfix]
  have hprod : z * σ z = algebraMap F L (c ^ 2 - a) := by
    rw [hσz, hz, map_sub, map_pow, ← hs]; ring
  have hWz : W z ^ 2 = (under (F := F) w).valuation F (c ^ 2 - a) ^ e := by
    calc W z ^ 2 = W z * W (σ z) := by rw [hWσz, pow_two]
      _ = W (z * σ z) := (map_mul _ _ _).symm
      _ = _ := by rw [hprod, valuation_algebraMap]
  have h2s : 2 * s = z - σ z := by rw [hσz, hz]; ring
  have hW2s : W (2 * s) ^ 2 = (under (F := F) w).valuation F (4 * a) ^ e := by
    rw [← map_pow, mul_pow, hs, show (2 : L) ^ 2 = algebraMap F L 4 by rw [map_ofNat]; norm_num, ← map_mul,
      valuation_algebraMap]
  have hle : W (2 * s) ≤ W z := by
    rw [h2s]
    refine (Valuation.map_sub _ _ _).trans ?_
    rw [hWσz, max_self]
  have hlt : (under (F := F) w).valuation F (c ^ 2 - a) ^ e <
      (under (F := F) w).valuation F (4 * a) ^ e := by
    rw [hw]
    exact pow_lt_pow_left₀ hloc zero_le he
  have := pow_le_pow_left₀ zero_le hle 2
  rw [hWz, hW2s] at this
  exact absurd this (not_le.mpr hlt)


/-- The two ramification-index APIs agree. -/
lemma ramificationIdx'_eq (w : HeightOneSpectrum (𝓞 L)) :
    (under (F := F) w).asIdeal.ramificationIdx' w.asIdeal = w.asIdeal.ramificationIdx (𝓞 F) :=
  Ideal.ramificationIdx'_eq_ramificationIdx _ _ (under (F := F) w).ne_bot

/-- `w` lies in the finset of primes over the prime below it. -/
lemma mem_primesOverFinset (w : HeightOneSpectrum (𝓞 L)) :
    w.asIdeal ∈ IsDedekindDomain.primesOverFinset (under (F := F) w).asIdeal (𝓞 L) :=
  (IsDedekindDomain.mem_primesOverFinset_iff (under (F := F) w).ne_bot (𝓞 L)).2
    ⟨w.isPrime, inferInstance⟩

/-- $\sum_{\mathfrak P \mid \mathfrak p} e f = [L:F] = 2$. -/
lemma sum_ef (p : HeightOneSpectrum (𝓞 F)) :
    ∑ P ∈ IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 L),
      p.asIdeal.ramificationIdx' P * p.asIdeal.inertiaDeg' P = 2 := by
  have := p.isMaximal
  rw [Ideal.sum_ramification_inertia (p := p.asIdeal) (𝓞 L) F L p.ne_bot,
    Algebra.IsQuadraticExtension.finrank_eq_two]

/-- $e \ge 1$. -/
lemma e_pos (w : HeightOneSpectrum (𝓞 L)) :
    0 < (under (F := F) w).asIdeal.ramificationIdx' w.asIdeal := by
  rw [ramificationIdx'_eq]; exact Nat.pos_of_ne_zero (ramificationIdx_ne_zero (F := F) w)

/-- $f \ge 1$. -/
lemma f_pos (w : HeightOneSpectrum (𝓞 L)) :
    0 < (under (F := F) w).asIdeal.inertiaDeg' w.asIdeal := by
  have := (under (F := F) w).isMaximal
  exact Ideal.inertiaDeg'_pos _ _

/-- **Two primes over `p`:** both have $e = f = 1$. -/
lemma ef_of_two (w w' : HeightOneSpectrum (𝓞 L)) (hne : w ≠ w') (h : under (F := F) w = under w') :
    (under (F := F) w).asIdeal.ramificationIdx' w.asIdeal = 1 ∧
      (under (F := F) w).asIdeal.inertiaDeg' w.asIdeal = 1 := by
  classical
  set p := under (F := F) w with hp
  have hm := mem_primesOverFinset (F := F) w
  have hm' := mem_primesOverFinset (F := F) w'
  rw [← h] at hm'
  have hne' : w.asIdeal ≠ w'.asIdeal := fun h => hne (HeightOneSpectrum.ext h)
  have hsum := sum_ef (L := L) p
  have hle : p.asIdeal.ramificationIdx' w.asIdeal * p.asIdeal.inertiaDeg' w.asIdeal +
      p.asIdeal.ramificationIdx' w'.asIdeal * p.asIdeal.inertiaDeg' w'.asIdeal ≤ 2 := by
    rw [← hsum, ← Finset.sum_pair (f := fun X => p.asIdeal.ramificationIdx' X * p.asIdeal.inertiaDeg' X) hne']
    exact Finset.sum_le_sum_of_subset (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption)
  have h1 := e_pos (F := F) w
  have h2 := f_pos (F := F) w
  have h3 := e_pos (F := F) w'
  have h4 := f_pos (F := F) w'
  rw [← h] at h3 h4
  constructor <;> nlinarith

/-- **Only one prime over `p`:** then $e f = 2$. -/
lemma ef_of_unique (w : HeightOneSpectrum (𝓞 L))
    (huniq : ∀ w' : HeightOneSpectrum (𝓞 L), under (F := F) w' = under w → w' = w) :
    (under (F := F) w).asIdeal.ramificationIdx' w.asIdeal *
      (under (F := F) w).asIdeal.inertiaDeg' w.asIdeal = 2 := by
  classical
  set p := under (F := F) w with hp
  have hsum := sum_ef (L := L) p
  have hsingle : IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 L) = {w.asIdeal} := by
    ext P
    simp only [Finset.mem_singleton]
    constructor
    · intro hP
      rw [IsDedekindDomain.mem_primesOverFinset_iff p.ne_bot (𝓞 L)] at hP
      obtain ⟨hPp, hPl⟩ := hP
      have hP0 : P ≠ ⊥ := by
        intro h0; apply p.ne_bot
        rw [hPl.over, h0, Ideal.under_def, Ideal.comap_bot_of_injective _
          (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 L))]
      have := huniq ⟨P, hPp, hP0⟩ (by ext1; exact hPl.over.symm)
      exact congrArg HeightOneSpectrum.asIdeal this
    · rintro rfl; exact mem_primesOverFinset (F := F) w
  rw [hsingle, Finset.sum_singleton] at hsum
  exact hsum


/-- **Residue degree one gives surjective residues:** if $f(w \mid \mathfrak p) = 1$, every $y \in \mathcal O_L$ is
congruent mod $w$ to an element of $\mathcal O_F$. -/
lemma exists_residue_of_f_eq_one (w : HeightOneSpectrum (𝓞 L))
    (hf : (under (F := F) w).asIdeal.inertiaDeg' w.asIdeal = 1) (y : 𝓞 L) :
    ∃ c : 𝓞 F, y - algebraMap (𝓞 F) (𝓞 L) c ∈ w.asIdeal := by
  have := (under (F := F) w).isMaximal
  have := w.isMaximal
  letI := Ideal.Quotient.field (under (F := F) w).asIdeal
  rw [Ideal.inertiaDeg'_algebraMap] at hf
  have hbot := Subalgebra.bot_eq_top_of_finrank_eq_one hf
  have hy : Ideal.Quotient.mk w.asIdeal y ∈ (⊥ : Subalgebra ((𝓞 F) ⧸ (under (F := F) w).asIdeal)
      ((𝓞 L) ⧸ w.asIdeal)) := by rw [hbot]; exact Algebra.mem_top
  obtain ⟨c', hc'⟩ := Algebra.mem_bot.mp hy
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c'
  refine ⟨c, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hc']
  rw [Ideal.Quotient.algebraMap_mk_of_liesOver, sub_self]

/-- **Unramified outside $2a$:** for $L = F(s)$, $s^2 = a$, a prime $w$ of $L$ whose prime $\mathfrak p$ below has
$\mathfrak p \nmid 2$ and $v_{\mathfrak p}(a) = 0$ is unramified: $e(w \mid \mathfrak p) = 1$.

*Proof.* Otherwise $e = 2$, $f = 1$, $w$ is the only prime over $\mathfrak p$, so $\sigma w = w$. As $f = 1$ and
$w(s) = 1$, some $c \in F$ has $w(s - c) < 1$; applying $\sigma$, $w(-s - c) < 1$, so $w(2s) < 1$, while
$w(2s) = \mathfrak p(2)^e \cdot w(s) = 1$. -/
@[kb "neukirch1999" "Ch. I, Prop. 8.3 / Ch. III, Cor. 2.12 [unverified]"]
theorem ramificationIdx_eq_one (s : L) (a : F) (hs : s ^ 2 = algebraMap F L a)
    (hσs : σ s = -s) (w : HeightOneSpectrum (𝓞 L))
    (h2 : (under (F := F) w).valuation F 2 = 1) (ha : (under (F := F) w).valuation F a = 1) :
    w.asIdeal.ramificationIdx (𝓞 F) = 1 := by
  classical
  by_contra he
  have he' : (under (F := F) w).asIdeal.ramificationIdx' w.asIdeal ≠ 1 := by
    rw [ramificationIdx'_eq]; exact he
  have huniq : ∀ w' : HeightOneSpectrum (𝓞 L), under (F := F) w' = under w → w' = w := by
    intro w' hw'
    by_contra hne
    exact he' (ef_of_two (F := F) w w' (Ne.symm hne) hw'.symm).1
  have hef := ef_of_unique (F := F) w huniq
  have he1 := e_pos (F := F) w
  have hf1 := f_pos (F := F) w
  have hf : (under (F := F) w).asIdeal.inertiaDeg' w.asIdeal = 1 := by
    rcases Nat.lt_or_ge ((under (F := F) w).asIdeal.inertiaDeg' w.asIdeal) 2 with h | h
    · omega
    · exfalso
      have : (under (F := F) w).asIdeal.ramificationIdx' w.asIdeal ≥ 2 := by omega
      nlinarith
  have hfix : comapEquiv (σO σ) w = w := huniq _ (under_comapEquiv σ w)
  set W := w.valuation L
  set e := w.asIdeal.ramificationIdx (𝓞 F)
  have hWs : W s = 1 := by
    have : W s ^ 2 = 1 := by
      rw [← map_pow, hs, valuation_algebraMap, ha, one_pow]
    exact eq_one_of_pow_eq_one two_ne_zero this
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer w s hWs.le
  obtain ⟨c₁, hc₁⟩ := exists_residue_of_f_eq_one (F := F) w hf n
  obtain ⟨c₂, hc₂⟩ := exists_residue_of_f_eq_one (F := F) w hf d
  have hd : (d : 𝓞 L) ∉ w.asIdeal := d.2
  have hc₂p : algebraMap (𝓞 F) (𝓞 L) c₂ ∉ w.asIdeal := by
    intro h; apply hd
    have := w.asIdeal.add_mem hc₂ h
    simpa using this
  set C₁ : F := algebraMap (𝓞 F) F c₁
  set C₂ : F := algebraMap (𝓞 F) F c₂
  have hcoe : ∀ c : 𝓞 F, algebraMap (𝓞 L) L (algebraMap (𝓞 F) (𝓞 L) c) =
      algebraMap F L (algebraMap (𝓞 F) F c) := fun c => rfl
  have hC₂ : C₂ ≠ 0 := by
    intro h0; apply hc₂p
    have : c₂ = 0 := (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mp h0
    rw [this, map_zero]; exact zero_mem _
  have hdL : algebraMap (𝓞 L) L d ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 L) L)]
    intro h0; exact hd (h0 ▸ zero_mem _)
  set c : F := C₁ / C₂
  have hnum : W (algebraMap (𝓞 L) L (n * algebraMap (𝓞 F) (𝓞 L) c₂ - d * algebraMap (𝓞 F) (𝓞 L) c₁)) < 1 := by
    rw [HeightOneSpectrum.valuation_lt_one_iff_mem]
    have : n * algebraMap (𝓞 F) (𝓞 L) c₂ - d * algebraMap (𝓞 F) (𝓞 L) c₁ =
        (n - algebraMap (𝓞 F) (𝓞 L) c₁) * algebraMap (𝓞 F) (𝓞 L) c₂ -
          (d - algebraMap (𝓞 F) (𝓞 L) c₂) * algebraMap (𝓞 F) (𝓞 L) c₁ := by ring
    rw [this]
    exact sub_mem (w.asIdeal.mul_mem_right _ hc₁) (w.asIdeal.mul_mem_right _ hc₂)
  have hden : W (algebraMap (𝓞 L) L (d * algebraMap (𝓞 F) (𝓞 L) c₂)) = 1 := by
    rw [HeightOneSpectrum.valuation_eq_one_iff_notMem]
    exact fun h => (w.isPrime.mem_or_mem h).elim hd hc₂p
  have hsc : s - algebraMap F L c =
      algebraMap (𝓞 L) L (n * algebraMap (𝓞 F) (𝓞 L) c₂ - d * algebraMap (𝓞 F) (𝓞 L) c₁) /
        algebraMap (𝓞 L) L (d * algebraMap (𝓞 F) (𝓞 L) c₂) := by
    have hC₂L : algebraMap F L C₂ ≠ 0 := by simpa using hC₂
    rw [map_sub, map_mul, map_mul, map_mul, hcoe, hcoe, ← hnd]
    simp only [c, C₁, C₂, map_div₀] at hC₂L ⊢
    field_simp
  have hlt : W (s - algebraMap F L c) < 1 := by
    rw [hsc, map_div₀, hden, div_one]; exact hnum
  have hσsc : σ (s - algebraMap F L c) = -s - algebraMap F L c := by
    rw [map_sub, hσs, σ.commutes]
  have hlt' : W (-s - algebraMap F L c) < 1 := by
    rw [← hσsc, valuation_galois, hfix]; exact hlt
  have h2s : W (2 * s) < 1 := by
    have : 2 * s = (s - algebraMap F L c) - (-s - algebraMap F L c) := by ring
    rw [this]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hlt hlt')
  have h2s' : W (2 * s) = 1 := by
    rw [map_mul, hWs, mul_one, show (2 : L) = algebraMap F L 2 by rw [map_ofNat],
      valuation_algebraMap, h2, one_pow]
  rw [h2s'] at h2s
  exact lt_irrefl _ h2s


/-- `p` splits in `L`: two distinct primes of `L` lie over it. -/
def SplitsFin (p : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∃ w w' : HeightOneSpectrum (𝓞 L), w ≠ w' ∧ under (F := F) w = p ∧ under (F := F) w' = p

open scoped Classical in
/-- **Counting primes over `S`:** $|S_L| + \#\{p \in S \text{ not split}\} = 2|S|$. -/
theorem card_overS_add (hσ : σ ≠ 1) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    (overS (L := L) S).card + (S.filter fun p => ¬ SplitsFin (L := L) p).card = 2 * S.card := by
  classical
  have hfib := Finset.card_eq_sum_card_fiberwise (s := overS (L := L) S) (t := S) (f := under (F := F))
    (fun w hw => mem_overS.mp hw)
  have hone : ∀ p ∈ S, ((overS (L := L) S).filter fun w => under (F := F) w = p).card =
      if SplitsFin (L := L) p then 2 else 1 := by
    intro p hp
    obtain ⟨w, hw⟩ := exists_over (L := L) p
    have hwS : w ∈ overS (L := L) S := mem_overS.mpr (hw ▸ hp)
    have hsub : ((overS (L := L) S).filter fun w' => under (F := F) w' = p) ⊆
        {w, comapEquiv (σO σ) w} := by
      intro w' hw'
      simp only [Finset.mem_filter] at hw'
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact over_eq_or σ hσ w w' (hw.trans hw'.2.symm)
    split_ifs with hsplit
    · obtain ⟨w₁, w₂, hne, h₁, h₂⟩ := hsplit
      apply le_antisymm
      · exact (Finset.card_le_card hsub).trans (Finset.card_le_two)
      · rw [← Finset.card_pair hne]
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        simp only [Finset.mem_filter]
        rcases hx with rfl | rfl
        · exact ⟨mem_overS.mpr (h₁ ▸ hp), h₁⟩
        · exact ⟨mem_overS.mpr (h₂ ▸ hp), h₂⟩
    · rw [Finset.card_eq_one]
      refine ⟨w, ?_⟩
      ext x
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨_, hx⟩
        by_contra hxw
        exact hsplit ⟨x, w, hxw, hx, hw⟩
      · rintro rfl; exact ⟨hwS, hw⟩
  rw [hfib, Finset.sum_congr rfl hone, Finset.sum_ite, Finset.sum_const, Finset.sum_const,
    smul_eq_mul, smul_eq_mul, mul_one]
  have := Finset.card_filter_add_card_filter_not (s := S) (fun p => SplitsFin (L := L) p)
  omega


/-- The infinite place `v` of `F` splits in `L`: two distinct places of `L` lie over it. -/
def SplitsInf (v : InfinitePlace F) : Prop :=
  ∃ w w' : InfinitePlace L, w ≠ w' ∧ w.comap (algebraMap F L) = v ∧ w'.comap (algebraMap F L) = v

/-- Infinite places over the same place of `F` are equal or `σ`-conjugate. -/
lemma inf_over_eq_or (hσ : σ ≠ 1) (w w' : InfinitePlace L)
    (h : w.comap (algebraMap F L) = w'.comap (algebraMap F L)) : w' = w ∨ w' = σ • w := by
  classical
  obtain ⟨τ, hτ⟩ := InfinitePlace.exists_smul_eq_of_comap_eq h
  have hτ2 : τ = 1 ∨ τ = σ := by
    by_contra hc
    push Not at hc
    have hcard : Nat.card (L ≃ₐ[F] L) = 2 := by
      rw [IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two]
    have h3 : ({1, σ, τ} : Finset (L ≃ₐ[F] L)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair hc.2.symm]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hσ.symm, hc.1.symm⟩
    have := Finset.card_le_univ ({1, σ, τ} : Finset (L ≃ₐ[F] L))
    rw [h3, Fintype.card_eq_nat_card, hcard] at this
    omega
  rcases hτ2 with rfl | rfl
  · left; rw [← hτ, one_smul]
  · right; exact hτ.symm

open scoped Classical in
/-- **Counting infinite places:** $r_\infty(L) + \#\{v \text{ not split}\} = 2\,r_\infty(F)$. -/
theorem card_infinitePlace_add (hσ : σ ≠ 1) :
    Fintype.card (InfinitePlace L) +
      (Finset.univ.filter fun v : InfinitePlace F => ¬ SplitsInf (L := L) v).card =
      2 * Fintype.card (InfinitePlace F) := by
  classical
  have hfib := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (InfinitePlace L)))
    (t := (Finset.univ : Finset (InfinitePlace F))) (f := fun w => w.comap (algebraMap F L))
    (fun _ _ => Finset.mem_univ _)
  have hone : ∀ v ∈ (Finset.univ : Finset (InfinitePlace F)),
      ((Finset.univ : Finset (InfinitePlace L)).filter fun w => w.comap (algebraMap F L) = v).card =
      if SplitsInf (L := L) v then 2 else 1 := by
    intro v _
    obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (k := F) (K := L) v
    simp only at hw
    have hsub : ((Finset.univ : Finset (InfinitePlace L)).filter
        fun w' => w'.comap (algebraMap F L) = v) ⊆ {w, σ • w} := by
      intro w' hw'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw'
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact inf_over_eq_or σ hσ w w' (hw.trans hw'.symm)
    split_ifs with hsplit
    · obtain ⟨w₁, w₂, hne, h₁, h₂⟩ := hsplit
      apply le_antisymm
      · exact (Finset.card_le_card hsub).trans (Finset.card_le_two)
      · rw [← Finset.card_pair hne]
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hx with rfl | rfl
        · exact h₁
        · exact h₂
    · rw [Finset.card_eq_one]
      refine ⟨w, ?_⟩
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hx
        by_contra hxw
        exact hsplit ⟨x, w, hxw, hx, hw⟩
      · rintro rfl; exact hw
  rw [Finset.card_univ] at hfib
  rw [hfib, Finset.sum_congr rfl hone, Finset.sum_ite, Finset.sum_const, Finset.sum_const,
    smul_eq_mul, smul_eq_mul, mul_one]
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (InfinitePlace F)))
    (fun v => SplitsInf (L := L) v)
  rw [Finset.card_univ] at this
  omega


open scoped Classical in
/-- **The global norm index of `S`-units, $= 2^{s'-1}$** (Milne VII §3 + Lemma 4.5 in $S$-unit form): if $S$
contains the ramified primes and $\mathrm{Cl}_S(F) = 1$ (`hS`), then
$$2\,[F_S^\times : N L_{S_L}^\times] = 2^{s'},\qquad s' = \#\{v \mid \infty \text{ not split}\} + \#\{\mathfrak p \in S \text{ not split}\}.$$ -/
@[kb "milne2020cft" "Ch. VII §3–4 (first inequality, S-unit form) [unverified]"]
theorem index_normsF_eq (hσ : σ ≠ 1) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ p : HeightOneSpectrum (𝓞 F), p ∉ S → ∃ c : 𝓞 F, c ∈ p.asIdeal ∧ c ∉ p.asIdeal ^ 2 ∧
        ∀ q : HeightOneSpectrum (𝓞 F), q ∉ S → q ≠ p → c ∉ q.asIdeal)
    (hram : ∀ w : HeightOneSpectrum (𝓞 L), under (F := F) w ∉ S →
        w.asIdeal.ramificationIdx (𝓞 F) = 1) :
    (normsF σ S).index * 2 =
      2 ^ ((Finset.univ.filter fun v : InfinitePlace F => ¬ SplitsInf (L := L) v).card +
        (S.filter fun p => ¬ SplitsFin (L := L) p).card) := by
  have h := index_normsF_mul σ hσ S (herbrandM1_eq_one σ hσ S hS hram)
  have hI := card_infinitePlace_add σ hσ
  have hF := card_overS_add σ hσ S
  have hL1 : 1 ≤ Fintype.card (InfinitePlace L) := Fintype.card_pos
  have hF1 : 1 ≤ Fintype.card (InfinitePlace F) := Fintype.card_pos
  simp only [Units.rank] at h
  set A := Fintype.card (InfinitePlace L) - 1 + (overS (L := L) S).card
  set n := (Finset.univ.filter fun v : InfinitePlace F => ¬ SplitsInf (L := L) v).card +
        (S.filter fun p => ¬ SplitsFin (L := L) p).card
  have hexp : 2 * (Fintype.card (InfinitePlace F) - 1 + S.card) + 1 = A + n := by omega
  have hpos : 0 < 2 ^ A := pow_pos two_pos A
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc (normsF σ S).index * 2 * 2 ^ A = (normsF σ S).index * 2 ^ A * 2 := by ring
    _ = 2 ^ (2 * (Fintype.card (InfinitePlace F) - 1 + S.card)) * 2 := by rw [h]
    _ = 2 ^ (A + n) := by rw [← hexp, pow_succ]
    _ = 2 ^ n * 2 ^ A := by rw [pow_add, mul_comm]

end QuadFormsKB.HN

end
