/-
# Hasse norm theorem, step 5a: good primes for the choice of $T$

* `quadData`: $F(\sqrt a)$ is a quadratic extension with an automorphism $\sigma \ne 1$, $\sigma s = -s$;
* `not_isSquare_in_quadExt`: $x \notin F^{\times2} \cup aF^{\times2}$ is not a square in $F(\sqrt a)$;
* `isSquare_of_pow_card_eq`: in $\mathbb F_{q^2}$ ($q$ odd) every element of $\mathbb F_q$ is a square;
* `exists_good_prime`: if $x \in \mathcal O_F$ is neither a square nor $a$ times a square, then outside any
  finite set there is a prime $t \nmid 2ax$ at which $a$ is a square and $x$ is not. This replaces the
  "Frobenius elements generate" input of Milne VII, Lemma 6.2; its analytic content is Dedekind's
  density argument `SqLG.not_almost_all_split` (over $F(\sqrt a)$).

Locators are from memory and still `[unverified]`.
-/
import QuadFormsKB.Literature.HasseNorm.Infinite
import QuadFormsKB.Literature.LocalGlobal.SquaresLocalGlobal

open Module NumberField IsDedekindDomain WithZero
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.HN

/-- **$F(\sqrt a)$ is quadratic with an automorphism $s \mapsto -s$:** for $a$ not a square and $L = F + Fs$,
$s^2 = a$: $[L:F] = 2$ and some $\sigma \ne 1$ has $\sigma s = -s$. -/
theorem quadData {F L : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
    (a : F) (hd : ¬ IsSquare a) (s : L) (hs : s ^ 2 = algebraMap F L a)
    (hspan : ∀ y : L, ∃ b₀ b₁ : F, y = algebraMap F L b₀ + algebraMap F L b₁ * s) :
    ∃ _ : Algebra.IsQuadraticExtension F L, ∃ σ : L ≃ₐ[F] L, σ ≠ 1 ∧ σ s = -s := by
  classical
  have htop : Submodule.span F ((({1, s} : Finset L)) : Set L) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨b₀, b₁, rfl⟩ := hspan y
    have h1 : (algebraMap F L b₀) = b₀ • (1 : L) := by rw [Algebra.smul_def, mul_one]
    have h2 : (algebraMap F L b₁) * s = b₁ • s := by rw [Algebra.smul_def]
    rw [h1, h2]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hfin : FiniteDimensional F L := ⟨⟨{1, s}, htop⟩⟩
  have hle : Module.finrank F L ≤ 2 := by
    rw [← finrank_top, ← htop]
    exact (finrank_span_finset_le_card ({1, s} : Finset L)).trans (Finset.card_le_two)
  have hne : Module.finrank F L ≠ 1 := by
    intro h1
    have := Subalgebra.bot_eq_top_of_finrank_eq_one h1
    have hs' : s ∈ (⊥ : Subalgebra F L) := this ▸ Algebra.mem_top
    obtain ⟨c, hc⟩ := Algebra.mem_bot.mp hs'
    apply hd
    refine ⟨c, ?_⟩
    apply (algebraMap F L).injective
    rw [map_mul, hc, ← hs, sq]
  have hpos : 0 < Module.finrank F L := Module.finrank_pos
  have h2 : Module.finrank F L = 2 := by omega
  have hQ : Algebra.IsQuadraticExtension F L := ⟨h2⟩
  refine ⟨hQ, ?_⟩
  have hcard : Nat.card (L ≃ₐ[F] L) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, h2]
  obtain ⟨σ, hσ⟩ : ∃ σ : L ≃ₐ[F] L, σ ≠ 1 := by
    by_contra hc
    push Not at hc
    have : Nat.card (L ≃ₐ[F] L) ≤ 1 := by
      rw [Finite.card_le_one_iff_subsingleton]
      exact ⟨fun x y => (hc x).trans (hc y).symm⟩
    omega
  refine ⟨σ, hσ, ?_⟩
  have hsq : (σ s - s) * (σ s + s) = 0 := by
    have : (σ s) ^ 2 = s ^ 2 := by rw [← map_pow, hs, σ.commutes]
    linear_combination this
  rcases mul_eq_zero.mp hsq with h | h
  · exfalso; apply hσ
    ext y
    obtain ⟨b₀, b₁, rfl⟩ := hspan y
    rw [sub_eq_zero] at h
    simp [h]
  · linear_combination h

/-- An element of $F$ that is neither a square nor $a$ times a square is not a square in $F(\\sqrt a)$. -/
lemma not_isSquare_in_quadExt {F L : Type*} [Field F] [Field L] [Algebra F L] [CharZero F]
    (a : F) (s : L) (hs : s ^ 2 = algebraMap F L a)
    (hspan : ∀ y : L, ∃ b₀ b₁ : F, y = algebraMap F L b₀ + algebraMap F L b₁ * s)
    (hli : ∀ b₀ b₁ : F, algebraMap F L b₀ + algebraMap F L b₁ * s = 0 → b₀ = 0 ∧ b₁ = 0)
    (x : F) (hx : ¬ IsSquare x) (hax : ¬ IsSquare (a * x)) : ¬ IsSquare (algebraMap F L x) := by
  rintro ⟨y, hy⟩
  obtain ⟨b₀, b₁, rfl⟩ := hspan y
  have key : algebraMap F L (b₀ ^ 2 + a * b₁ ^ 2 - x) + algebraMap F L (2 * b₀ * b₁) * s = 0 := by
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat]
    rw [hy]
    linear_combination (-(algebraMap F L b₁) ^ 2) * hs
  obtain ⟨h1, h2⟩ := hli _ _ key
  rcases mul_eq_zero.mp h2 with h | h
  · rcases mul_eq_zero.mp h with h | h
    · norm_num at h
    · subst h
      apply hax
      refine ⟨a * b₁, ?_⟩
      linear_combination -a * h1
  · subst h
    apply hx
    exact ⟨b₀, by linear_combination -h1⟩


/-- **In a quadratic extension of finite fields of odd characteristic, every element of the base is a
square:** if $|k| = q^2$, $q$ odd, and $y^q = y$, then $y$ is a square in $k$. -/
lemma isSquare_of_pow_card_eq {k : Type*} [Field k] [Fintype k] (q : ℕ) (hq : Odd q)
    (hk : Fintype.card k = q ^ 2) (y : k) (hy : y ^ q = y) : IsSquare y := by
  by_cases hy0 : y = 0
  · exact ⟨0, by simp [hy0]⟩
  have hchar : ringChar k ≠ 2 := by
    intro h
    have := FiniteField.even_card_iff_char_two.mp h
    rw [hk] at this
    have hodd : (q ^ 2) % 2 = 1 := Nat.odd_iff.mp hq.pow
    omega
  rw [FiniteField.isSquare_iff hchar hy0, hk]
  obtain ⟨m, rfl⟩ := hq
  have hq1 : y ^ (2 * m) = 1 := by
    have : y ^ (2 * m + 1) = y ^ (2 * m) * y := pow_succ _ _
    rw [hy] at this
    exact (mul_eq_right₀ hy0).mp this.symm
  have hdiv : (2 * m + 1) ^ 2 / 2 = (2 * m) * (m + 1) := by
    have : (2 * m + 1) ^ 2 = 2 * ((2 * m) * (m + 1)) + 1 := by ring
    omega
  rw [hdiv, pow_mul, hq1, one_pow]


/-- Linear independence of $1, s$ when $s^2 = a$ is not a square. -/
lemma li_of_sq {F L : Type*} [Field F] [Field L] [Algebra F L] (a : F) (hd : ¬ IsSquare a) (s : L)
    (hs : s ^ 2 = algebraMap F L a) (b₀ b₁ : F) (h : algebraMap F L b₀ + algebraMap F L b₁ * s = 0) :
    b₀ = 0 ∧ b₁ = 0 := by
  by_cases h1 : b₁ = 0
  · subst h1; simp at h; exact ⟨h, rfl⟩
  · exfalso; apply hd
    refine ⟨-b₀ / b₁, ?_⟩
    apply (algebraMap F L).injective
    have h1' : algebraMap F L b₁ ≠ 0 := by simpa using h1
    have hs' : s = algebraMap F L (-b₀ / b₁) := by
      rw [map_div₀, map_neg]
      field_simp
      linear_combination h
    rw [← hs, hs', map_mul, sq]

/-- **Good primes for the choice of $T$** (Milne VII, Lemma 6.2 for $n = 2$): if $x \in \mathcal O_F$ is neither a
square nor $a$ times a square, then outside any finite set $B$ there is a prime $t \nmid 2ax$ at which
$a$ is a square and $x$ is not.

*Proof.* $x$ is not a square in $L = F(\sqrt a)$; by `SqLG.not_almost_all_split` (Dirichlet density over
$L$) some prime $P$ of $L$ off the bad set does not split in $L(\sqrt x)$. For $t$ below $P$: if $a$ is not a
square at $t$ then $f(P \mid t) = 2$ (a residue of $\sqrt a$ would give a square root of $a$ mod $t$, hence in
$F_t$), and every element of $\mathcal O_F/t$ is a square in $\mathcal O_L/P$ (`isSquare_of_pow_card_eq`), so $P$
would split; so $a$ is a square at $t$, and then $x$ cannot be one (else $P$ splits again). -/
@[kb "milne2020cft" "Ch. VII, Lemma 6.2 (n = 2) [unverified]"]
theorem exists_good_prime {F L : Type} [Field F] [NumberField F] [Field L] [NumberField L]
    [Algebra F L] (a : 𝓞 F) (hd : ¬ IsSquare (a : F)) (s : L) (hs : s ^ 2 = algebraMap F L a)
    (hspan : ∀ y : L, ∃ b₀ b₁ : F, y = algebraMap F L b₀ + algebraMap F L b₁ * s)
    (x : 𝓞 F) (hx : ¬ IsSquare (x : F)) (hax : ¬ IsSquare ((a : F) * x))
    (B : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ t : HeightOneSpectrum (𝓞 F), t ∉ B ∧ (2 * a * x) ∉ t.asIdeal ∧
      IsSquare (algebraMap F (t.adicCompletion F) a) ∧
      ¬ IsSquare (algebraMap F (t.adicCompletion F) x) := by
  classical
  obtain ⟨hQ, σ, hσ, hσs⟩ := quadData (a : F) hd s hs hspan
  have hxL : ¬ IsSquare (algebraMap F L (x : F)) :=
    not_isSquare_in_quadExt (a : F) s hs hspan (li_of_sq (a : F) hd s hs) (x : F) hx hax
  set xL : 𝓞 L := algebraMap (𝓞 F) (𝓞 L) x with hxLdef
  have hxLcoe : (xL : L) = algebraMap F L (x : F) := rfl
  have hxL' : ¬ IsSquare (xL : L) := by rw [hxLcoe]; exact hxL
  obtain ⟨L', _, _, _, s', hs', hspan'⟩ := QuadFormsKB.Lam.exists_quadExt (F := L) (xL : L) hxL'
  obtain ⟨hQ', -⟩ := quadData (xL : L) hxL' s' hs' hspan'
  have hdeg : Module.finrank L L' = 2 := Algebra.IsQuadraticExtension.finrank_eq_two L L'
  have h2ax0 : (2 * a * x : 𝓞 F) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) ?_
    · rintro rfl; exact hd ⟨0, by simp⟩
    · rintro rfl; exact hx ⟨0, by simp⟩
  have hbad : {p : HeightOneSpectrum (𝓞 F) | (2 * a * x) ∈ p.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {2 * a * x}) (by simpa using h2ax0)).subset ?_
    intro p hp
    rw [Set.mem_ofPred_eq, Ideal.dvd_span_singleton]; exact hp
  set B' := B ∪ hbad.toFinset
  by_contra hgoal
  push Not at hgoal
  apply SqLG.not_almost_all_split (F := L) (L := L') (xL : L) hxL' s' hs' hspan' (overS (L := L) B')
  intro P hP
  set t := under (F := F) P with htdef
  have htB' : t ∉ B' := by simpa [mem_overS] using hP
  have htB : t ∉ B := fun h => htB' (Finset.mem_union_left _ h)
  have ht2ax : (2 * a * x) ∉ t.asIdeal := fun h =>
    htB' (Finset.mem_union_right _ (by simpa using h))
  have hmemP : ∀ c : 𝓞 F, algebraMap (𝓞 F) (𝓞 L) c ∈ P.asIdeal ↔ c ∈ t.asIdeal := by
    intro c; rw [htdef, under_asIdeal, Ideal.mem_comap]
  have h2x : (2 * x : 𝓞 F) ∉ t.asIdeal := by
    intro h; apply ht2ax
    have : 2 * a * x = a * (2 * x) := by ring
    rw [this]; exact t.asIdeal.mul_mem_left _ h
  have hPx : (2 * xL) ∉ P.asIdeal := by
    rw [hxLdef, show (2 : 𝓞 L) = algebraMap (𝓞 F) (𝓞 L) 2 from (map_ofNat _ 2).symm, ← map_mul,
      hmemP]
    exact h2x
  -- the key: x is a square mod P
  have hsqP : ∃ r : 𝓞 L, xL - r ^ 2 ∈ P.asIdeal := by
    by_cases haSq : IsSquare (algebraMap F (t.adicCompletion F) (a : F))
    · have hxSq := hgoal t htB ht2ax haSq
      obtain ⟨r, hr⟩ := SqLG.exists_sq_mod_of_isSquare x t h2x hxSq
      refine ⟨algebraMap (𝓞 F) (𝓞 L) r, ?_⟩
      rw [hxLdef, ← map_pow, ← map_sub, hmemP]; exact hr
    · have hat : (a : 𝓞 F) ∉ t.asIdeal := by
        intro h; apply ht2ax
        have : 2 * a * x = a * (2 * x) := by ring
        rw [this]; exact t.asIdeal.mul_mem_right _ h
      have h2t : (2 : 𝓞 F) ∉ t.asIdeal := by
        intro h; apply ht2ax
        exact t.asIdeal.mul_mem_right _ (t.asIdeal.mul_mem_right _ h)
      have hsint : IsIntegral ℤ s := by
        have : IsIntegral ℤ (s ^ 2) := by
          rw [hs]; exact (RingOfIntegers.isIntegral_coe a).algebraMap
        exact IsIntegral.of_pow two_pos this
      set sO : 𝓞 L := ⟨s, hsint⟩ with hsO
      have hf1 : t.asIdeal.inertiaDeg' P.asIdeal ≠ 1 := by
        intro hf
        obtain ⟨c, hc⟩ := exists_residue_of_f_eq_one (F := F) P hf sO
        have hprod : (sO - algebraMap (𝓞 F) (𝓞 L) c) * (sO + algebraMap (𝓞 F) (𝓞 L) c) =
            algebraMap (𝓞 F) (𝓞 L) (a - c ^ 2) := by
          apply FaithfulSMul.algebraMap_injective (𝓞 L) L
          have e1 : algebraMap (𝓞 L) L sO = s := rfl
          have e2 : ∀ c : 𝓞 F, algebraMap (𝓞 L) L (algebraMap (𝓞 F) (𝓞 L) c) =
              algebraMap F L (c : F) := fun c => rfl
          simp only [map_mul, map_sub, map_add, map_pow, e1, e2]
          rw [← hs]; ring
        have hmem : algebraMap (𝓞 F) (𝓞 L) (a - c ^ 2) ∈ P.asIdeal := by
          rw [← hprod]; exact P.asIdeal.mul_mem_right _ hc
        rw [hmemP] at hmem
        have hct : c ∉ t.asIdeal := by
          intro hc'
          apply hat
          have : a = (a - c ^ 2) + c * c := by ring
          rw [this]; exact t.asIdeal.add_mem hmem (t.asIdeal.mul_mem_left _ hc')
        apply haSq
        have hcF : (c : F) ≠ 0 := by
          intro h0; apply hct
          rw [show c = 0 from (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mp h0]
          exact zero_mem _
        have hval : t.valuation F ((a : F) / (c : F) ^ 2 - 1) < 1 := by
          have e : (a : F) / (c : F) ^ 2 - 1 = algebraMap (𝓞 F) F (a - c ^ 2) / (c : F) ^ 2 := by
            rw [map_sub, map_pow]; field_simp
          have hvc : t.valuation F (c : F) = 1 :=
            (HeightOneSpectrum.valuation_eq_one_iff_notMem t).mpr hct
          rw [e, map_div₀, map_pow, hvc, one_pow, div_one]
          exact (HeightOneSpectrum.valuation_lt_one_iff_mem t _).mpr hmem
        obtain ⟨u, hu⟩ := NFLocal.isSquare_of_valuation_sub_one_lt_nf t h2t _ hval
        refine ⟨u * algebraMap F _ (c : F), ?_⟩
        have : (a : F) = (a : F) / (c : F) ^ 2 * ((c : F) * (c : F)) := by field_simp
        rw [this, map_mul, hu, map_mul]; ring
      have hle : t.asIdeal.ramificationIdx' P.asIdeal * t.asIdeal.inertiaDeg' P.asIdeal ≤ 2 := by
        rw [← sum_ef (L := L) t]
        exact Finset.single_le_sum (f := fun X => t.asIdeal.ramificationIdx' X *
          t.asIdeal.inertiaDeg' X) (fun _ _ => Nat.zero_le _) (mem_primesOverFinset (F := F) P)
      have he1 : 0 < t.asIdeal.ramificationIdx' P.asIdeal := e_pos (F := F) P
      have hfpos : 0 < t.asIdeal.inertiaDeg' P.asIdeal := f_pos (F := F) P
      have hf2 : t.asIdeal.inertiaDeg' P.asIdeal = 2 := by
        have : 2 ≤ t.asIdeal.inertiaDeg' P.asIdeal := by omega
        nlinarith
      have := t.isMaximal
      have := P.isMaximal
      let := Ideal.Quotient.field t.asIdeal
      let := Ideal.Quotient.field P.asIdeal
      have : Finite (𝓞 F ⧸ t.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ t.ne_bot
      have : Finite (𝓞 L ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
      let := Fintype.ofFinite (𝓞 F ⧸ t.asIdeal)
      let := Fintype.ofFinite (𝓞 L ⧸ P.asIdeal)
      set q := Fintype.card (𝓞 F ⧸ t.asIdeal) with hqdef
      have hcardP : Fintype.card (𝓞 L ⧸ P.asIdeal) = q ^ 2 := by
        have hf' : t.asIdeal.inertiaDeg' P.asIdeal = P.asIdeal.inertiaDeg (𝓞 F) :=
          Ideal.inertiaDeg'_eq_inertiaDeg _ _
        have hN := Ideal.absNorm_pow_inertiaDeg t.asIdeal P.asIdeal
        rw [← hf', hf2, Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
          Submodule.cardQuot_apply] at hN
        rw [← Nat.card_eq_fintype_card, ← hN, hqdef, Nat.card_eq_fintype_card]
      have hqodd : Odd q := by
        have hchar : ringChar (𝓞 F ⧸ t.asIdeal) ≠ 2 := by
          intro h
          apply h2t
          rw [← Ideal.Quotient.eq_zero_iff_mem, map_ofNat]
          have := ringChar.spec (𝓞 F ⧸ t.asIdeal) 2
          rw [h] at this
          exact_mod_cast this.mpr dvd_rfl
        have := mt FiniteField.even_card_iff_char_two.mpr hchar
        exact Nat.odd_iff.mpr (by omega)
      have hle' : t.asIdeal ≤ P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 L)) := le_of_eq rfl
      set φ := Ideal.quotientMap P.asIdeal (algebraMap (𝓞 F) (𝓞 L)) hle'
      have hy : Ideal.Quotient.mk P.asIdeal xL = φ (Ideal.Quotient.mk t.asIdeal x) := by
        rw [Ideal.quotientMap_mk]
      have hyq : (Ideal.Quotient.mk P.asIdeal xL) ^ q = Ideal.Quotient.mk P.asIdeal xL := by
        rw [hy, ← map_pow, FiniteField.pow_card]
      obtain ⟨rb, hrb⟩ := isSquare_of_pow_card_eq q hqodd hcardP _ hyq
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective rb
      exact ⟨r, by rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, hrb, pow_two, sub_self]⟩
  obtain ⟨r, hr⟩ := hsqP
  obtain ⟨Q, Q', hne, hQ1, hQ2⟩ := SqLG.exists_two_primes_over (F := L) (L := L') xL hxL' s' hs' hspan'
    P hPx r hr
  obtain ⟨n1, n2⟩ := SqLG.absNorm_eq_of_two_primes (F := L) hdeg P Q Q' hne hQ1 hQ2
  exact ⟨Q, Q', hne, hQ1, hQ2, n1, n2⟩

end QuadFormsKB.HN

end
