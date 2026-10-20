/-
# Squares are local–global over a number field

**Theorem.** If $a \in F$ is a square in every completion $F_v$, then $a$ is a square in $F$.

*Proof* (Dedekind's density argument; Neukirch VII §13, Marcus Ch. 7). Suppose $a$ is not a square
(WLOG $a \in \mathcal{O}_F$) and let $L = F(\sqrt a)$, a quadratic extension. At every prime
$\mathfrak{p} \nmid 2a$, $a$ is a unit square in $F_{\mathfrak{p}}$, so $X^2 - a$ splits into distinct
linear factors mod $\mathfrak{p}$ and $\mathfrak{p}$ splits into two primes of $L$ of norm $N\mathfrak{p}$
(Kummer–Dedekind). Counting ideals gives $\zeta_L(s) \ge c\, \zeta_F(s)^2$ for real $s > 1$, so
$(s-1)\zeta_L(s) \to \infty$ as $s \to 1^+$ — contradicting the simple pole of $\zeta_L$ (Mathlib's
class number formula `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`).

Locators are from memory and still `[unverified]`.
-/
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowskiNF

open NumberField IsDedekindDomain

namespace QuadFormsKB.SqLG

variable {F : Type} [Field F] [NumberField F]

/-- **Residue square root:** if $\mathfrak{p} \nmid 2a$ ($a \in \mathcal{O}_F$) and $a$ is a square in
$F_{\mathfrak{p}}$, then $a \equiv r^2 \pmod{\mathfrak{p}}$ for some $r \in \mathcal{O}_F$.
*Proof.* Write $a = x^2$ with $x \in F_{\mathfrak{p}}$; $v(x)^2 = v(a) = 1$ so $x$ is a $\mathfrak{p}$-adic unit;
by density (`HeightOneSpectrum.denseRange_algebraMap`) pick $y \in F$ with $v(x - y) < 1$, so $y$ is
$\mathfrak{p}$-integral; write $y = r/t$ with $r, t \in \mathcal{O}_F$, $t \notin \mathfrak{p}$, and replace $r$ by
$r t'$ where $t t' \equiv 1 \bmod \mathfrak{p}$ ($\mathcal{O}_F/\mathfrak{p}$ is a field). Then
$v(a - r^2) < 1$, i.e. $a - r^2 \in \mathfrak{p}$ (`valuation_lt_one_iff_mem`-type lemmas). -/
@[kb "neukirch1999" "Ch. II §4 [unverified]"]
theorem exists_sq_mod_of_isSquare (a : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) (h2a : (2 * a) ∉ v.asIdeal)
    (hsq : IsSquare (algebraMap F (v.adicCompletion F) (a : F))) :
    ∃ r : 𝓞 F, a - r ^ 2 ∈ v.asIdeal := by
  have key : ∀ y : F, v.valuation F y ≤ 1 → ∃ a s : 𝓞 F, s ∉ v.asIdeal ∧ y * s = a := by
    intro y hy
    have hy' : y ∈ HeightOneSpectrum.valuationSubringAtPrime F v := by
      rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]; exact hy
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.mk'_surjective v.asIdeal.primeCompl (⟨y, hy'⟩ : HeightOneSpectrum.valuationSubringAtPrime F v)
    have h2 := IsLocalization.mk'_spec (HeightOneSpectrum.valuationSubringAtPrime F v) a s
    simp only at h
    rw [h] at h2
    refine ⟨a, s, s.2, ?_⟩
    have h3 := congrArg Subtype.val h2
    exact h3
  have hval : ∀ y : F, Valued.v (algebraMap F (v.adicCompletion F) y) = v.valuation F y := by
    intro y
    rw [HeightOneSpectrum.algebraMap_adicCompletion (𝓞 F)]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v y
  have ha : a ∉ v.asIdeal := fun h => h2a (v.asIdeal.mul_mem_left 2 h)
  have hva : v.valuation F (a : F) = 1 := by
    apply le_antisymm (v.valuation_le_one a)
    exact not_lt.mp (fun h => ha ((v.valuation_lt_one_iff_mem a).mp h))
  obtain ⟨x, hx⟩ := hsq
  have hvx : Valued.v x ≤ 1 := by
    have h1 : Valued.v x * Valued.v x = 1 := by
      rw [← map_mul, ← hx, hval, hva]
    by_contra hc
    have hc' : 1 < Valued.v x := lt_of_not_ge hc
    have : 1 < Valued.v x * Valued.v x := one_lt_mul hc'.le hc'
    rw [h1] at this
    exact lt_irrefl _ this
  obtain ⟨y, hy⟩ : ∃ y : F, Valued.v (x - algebraMap F _ y) < 1 := by
    have hn : {z : v.adicCompletion F | Valued.v (z - x) < 1} ∈ nhds x := Valued.mem_nhds.mpr ⟨1, by simp⟩
    obtain ⟨_, h1, ⟨y, rfl⟩⟩ := mem_closure_iff_nhds.mp (HeightOneSpectrum.denseRange_algebraMap F v x) _ hn
    refine ⟨y, ?_⟩
    rw [← Valuation.map_neg, neg_sub]; exact h1
  set w := algebraMap F (v.adicCompletion F) y with hw
  have hvw : Valued.v w ≤ 1 := by
    have : w = x - (x - w) := by ring
    rw [this]
    exact (Valuation.map_sub _ _ _).trans (max_le hvx hy.le)
  have hvy : v.valuation F y ≤ 1 := by rw [← hval]; exact hvw
  have hay : v.valuation F ((a : F) - y ^ 2) < 1 := by
    rw [← hval, map_sub, map_pow, hx, ← hw]
    have : x * x - w ^ 2 = (x - w) * (x + w) := by ring
    rw [this, map_mul]
    have h3 : Valued.v (x + w) ≤ 1 := (Valuation.map_add _ _ _).trans (max_le hvx hvw)
    calc Valued.v (x - w) * Valued.v (x + w) ≤ Valued.v (x - w) * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact hy
  obtain ⟨b, s, hs, hys⟩ := key y hvy
  obtain ⟨t, i, hi, hti⟩ := Ideal.IsMaximal.exists_inv (v.isMaximal) hs
  refine ⟨t * b, ?_⟩
  rw [← v.valuation_lt_one_iff_mem (K := F)]
  have hi' : v.valuation F (i : F) < 1 := (v.valuation_lt_one_iff_mem i).mpr hi
  have hyr : v.valuation F (y - ((t * b : 𝓞 F) : F)) < 1 := by
    have : y - ((t * b : 𝓞 F) : F) = y * (i : F) := by
      have e : ((t : F) * s + i) = 1 := by exact_mod_cast congrArg (fun z : 𝓞 F => (z : F)) hti
      push_cast
      linear_combination (-y) * e + (t : F) * hys
    rw [this, map_mul]
    calc v.valuation F y * v.valuation F i ≤ 1 * v.valuation F i := by gcongr
      _ < 1 := by rw [one_mul]; exact hi'
  have hyr2 : v.valuation F (y + ((t * b : 𝓞 F) : F)) ≤ 1 :=
    (Valuation.map_add _ _ _).trans (max_le hvy (v.valuation_le_one _))
  have e2 : (((a - (t * b) ^ 2 : 𝓞 F)) : F) = ((a : F) - y ^ 2) + (y - ((t * b : 𝓞 F) : F)) * (y + ((t * b : 𝓞 F) : F)) := by
    push_cast; ring
  change v.valuation F (((a - (t * b) ^ 2 : 𝓞 F)) : F) < 1
  rw [e2]
  apply Valuation.map_add_lt _ hay
  rw [map_mul]
  calc v.valuation F (y - ((t * b : 𝓞 F) : F)) * v.valuation F (y + ((t * b : 𝓞 F) : F))
      ≤ v.valuation F (y - ((t * b : 𝓞 F) : F)) * 1 := by gcongr
    _ < 1 := by rw [mul_one]; exact hyr

/-- **Two primes over $\mathfrak{p}$:** with $L = F(\sqrt a)$, $s^2 = a$, $a \in \mathcal{O}_F$, $\mathfrak{p} \nmid 2a$,
and $a \equiv r^2 \pmod{\mathfrak{p}}$, there are distinct primes $\mathfrak{P} \ne \mathfrak{Q}$ of $\mathcal{O}_L$
over $\mathfrak{p}$.

*Proof.* $s \in \mathcal{O}_L$ (it is integral: $s^2 = a$). Let $\sigma = s$ as an element of $\mathcal{O}_L$.
The ideal $\mathfrak{p}\mathcal{O}_L + (\sigma - r)$ is proper: otherwise $1 = \pi + (\sigma - r)y$ with
$\pi \in \mathfrak{p}\mathcal{O}_L$, and multiplying by $\sigma + r$ gives $\sigma + r \in \mathfrak{p}\mathcal{O}_L$
(as $(\sigma - r)(\sigma + r) = a - r^2 \in \mathfrak{p}$). Apply the $F$-automorphism $\tau$ of
$L = F \oplus F s$ with $\tau(s) = -s$ (it exists because $a$ is not a square, so $X^2 - a$ is the
minimal polynomial of $s$; it preserves $\mathcal{O}_L$ and $\mathfrak{p}\mathcal{O}_L$): then
$-\sigma + r \in \mathfrak{p}\mathcal{O}_L$ too, so $2r \in \mathfrak{p}\mathcal{O}_L \cap \mathcal{O}_F = \mathfrak{p}$
(lying over / `Ideal.comap_map_eq_self`-type lemmas for the integral extension), impossible as
$2 \notin \mathfrak{p}$ and $r \notin \mathfrak{p}$ ($r^2 \equiv a \not\equiv 0$). Symmetrically for $\sigma + r$.
Take maximal $\mathfrak{P} \supseteq \mathfrak{p}\mathcal{O}_L + (\sigma - r)$ and
$\mathfrak{Q} \supseteq \mathfrak{p}\mathcal{O}_L + (\sigma + r)$; both lie over $\mathfrak{p}$ (the contraction is a
proper ideal containing the maximal ideal $\mathfrak{p}$). If $\mathfrak{P} = \mathfrak{Q}$ then
$2r \in \mathfrak{P} \cap \mathcal{O}_F = \mathfrak{p}$, impossible.

*Correction.* An earlier version was stated without `hd` and `hspan`, which is false: $F = L = \mathbb{Q}$,
$a = s = r = 1$, $\mathfrak{p} = (3)$ has only one prime above $\mathfrak{p}$. -/
@[kb "neukirch1999" "Ch. I, Prop. 8.3 [unverified]"]
theorem exists_two_primes_over {L : Type} [Field L] [NumberField L] [Algebra F L]
    (a : 𝓞 F) (hd : ¬ IsSquare (a : F)) (s : L) (hs : s ^ 2 = algebraMap F L (a : F))
    (hspan : ∀ y : L, ∃ b₀ b₁ : F, y = algebraMap F L b₀ + algebraMap F L b₁ * s)
    (v : HeightOneSpectrum (𝓞 F)) (h2a : (2 * a) ∉ v.asIdeal) (r : 𝓞 F)
    (hr : a - r ^ 2 ∈ v.asIdeal) :
    ∃ P Q : HeightOneSpectrum (𝓞 L), P ≠ Q ∧
      P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 L)) = v.asIdeal ∧
      Q.asIdeal.comap (algebraMap (𝓞 F) (𝓞 L)) = v.asIdeal := by
  classical
  have ha : a ∉ v.asIdeal := fun h => h2a (v.asIdeal.mul_mem_left 2 h)
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := fun h => h2a (v.asIdeal.mul_mem_right a h)
  have hrv : r ∉ v.asIdeal := by
    intro h
    apply ha
    have := v.asIdeal.add_mem hr (v.asIdeal.mul_mem_left r h)
    simpa [pow_two] using this
  have hsint : IsIntegral ℤ s := by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    rw [hs]
    exact a.2.algebraMap
  set σ : 𝓞 L := ⟨s, hsint⟩ with hσ
  have hσ2 : σ ^ 2 = algebraMap (𝓞 F) (𝓞 L) a := by
    apply RingOfIntegers.ext
    exact hs
  have hirr : Irreducible (Polynomial.X ^ 2 - Polynomial.C (a : F)) :=
    _root_.X_pow_sub_C_irreducible_of_prime Nat.prime_two (fun b hb => hd ⟨b, by rw [← hb]; ring⟩)
  have hmin : minpoly F s = Polynomial.X ^ 2 - Polynomial.C (a : F) :=
    (minpoly.eq_of_irreducible_of_monic hirr (by simp [hs]) (Polynomial.monic_X_pow_sub_C _ (by norm_num))).symm
  have hsF : IsIntegral F s := .of_finite F s
  have htop : Algebra.adjoin F {s} = ⊤ := by
    rw [Algebra.eq_top_iff]
    intro y
    obtain ⟨b₀, b₁, rfl⟩ := hspan y
    exact Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ _) (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (Algebra.subset_adjoin rfl))
  let pb := PowerBasis.ofAdjoinEqTop hsF htop
  have hgen : pb.gen = s := rfl
  have hroot : Polynomial.aeval (-s) (minpoly F pb.gen) = 0 := by
    rw [hgen, hmin]; simp [hs]
  let τ : L →ₐ[F] L := pb.lift (-s) hroot
  have hτs : τ s = -s := PowerBasis.lift_gen pb (-s) hroot
  let τ' : 𝓞 L →+* 𝓞 L := RingOfIntegers.mapRingHom τ.toRingHom
  have hτσ : τ' σ = -σ := by
    apply RingOfIntegers.ext
    rw [RingOfIntegers.mapRingHom_apply]
    exact hτs
  have hτalg : ∀ x : 𝓞 F, τ' (algebraMap (𝓞 F) (𝓞 L) x) = algebraMap (𝓞 F) (𝓞 L) x := by
    intro x
    apply RingOfIntegers.ext
    rw [RingOfIntegers.mapRingHom_apply]
    exact τ.commutes (x : F)
  have hinj := FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 L)
  haveI := v.isPrime
  obtain ⟨P, -, hPp, hPc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 L) v.asIdeal ⊥ (by
    intro x hx
    rw [Ideal.under_def, Ideal.mem_comap, Ideal.mem_bot] at hx
    have : x = 0 := hinj (by rw [hx, map_zero])
    rw [this]; exact v.asIdeal.zero_mem)
  rw [Ideal.under_def] at hPc
  obtain ⟨x0, hx0, hx0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hx0P : algebraMap (𝓞 F) (𝓞 L) x0 ∈ P := by
    rw [← Ideal.mem_comap, hPc]; exact hx0
  have hx0ne' : algebraMap (𝓞 F) (𝓞 L) x0 ≠ 0 := by
    intro h; apply hx0ne; apply hinj; rw [h, map_zero]
  have hPne : P ≠ ⊥ := fun h => hx0ne' (by rw [h] at hx0P; exact (Ideal.mem_bot).1 hx0P)
  let PP : HeightOneSpectrum (𝓞 L) := ⟨P, hPp, hPne⟩
  haveI : (P.comap τ').IsPrime := Ideal.comap_isPrime τ' P
  have hQne : P.comap τ' ≠ ⊥ := by
    intro h
    have : algebraMap (𝓞 F) (𝓞 L) x0 ∈ P.comap τ' := by
      rw [Ideal.mem_comap, hτalg]; exact hx0P
    rw [h] at this
    exact hx0ne' ((Ideal.mem_bot).1 this)
  let QQ : HeightOneSpectrum (𝓞 L) := ⟨P.comap τ', inferInstance, hQne⟩
  have hcomp : τ'.comp (algebraMap (𝓞 F) (𝓞 L)) = algebraMap (𝓞 F) (𝓞 L) := RingHom.ext hτalg
  have hQc : (P.comap τ').comap (algebraMap (𝓞 F) (𝓞 L)) = v.asIdeal := by
    rw [Ideal.comap_comap, hcomp, hPc]
  have key : ∀ t : 𝓞 F, t ∉ v.asIdeal → σ - algebraMap (𝓞 F) (𝓞 L) t ∈ P →
      ∃ P Q : HeightOneSpectrum (𝓞 L), P ≠ Q ∧
        P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 L)) = v.asIdeal ∧
        Q.asIdeal.comap (algebraMap (𝓞 F) (𝓞 L)) = v.asIdeal := by
    intro t ht hmem
    refine ⟨PP, QQ, ?_, hPc, hQc⟩
    intro hPQ
    have hPQ' : P = P.comap τ' := congrArg HeightOneSpectrum.asIdeal hPQ
    have h1 : σ + algebraMap (𝓞 F) (𝓞 L) t ∈ P := by
      rw [hPQ', Ideal.mem_comap, map_add, hτσ, hτalg]
      have := P.neg_mem_iff.2 hmem
      convert this using 1; ring
    have h3 : algebraMap (𝓞 F) (𝓞 L) (2 * t) ∈ P := by
      have := P.sub_mem h1 hmem
      convert this using 1; rw [map_mul, map_ofNat]; ring
    rw [← Ideal.mem_comap, hPc] at h3
    rcases v.isPrime.mem_or_mem h3 with h | h
    · exact h2 h
    · exact ht h
  have hprod : (σ - algebraMap (𝓞 F) (𝓞 L) r) * (σ - algebraMap (𝓞 F) (𝓞 L) (-r)) ∈ P := by
    have : algebraMap (𝓞 F) (𝓞 L) (a - r ^ 2) ∈ P := by
      rw [← Ideal.mem_comap, hPc]; exact hr
    convert this using 1
    rw [map_sub, map_pow, map_neg, ← hσ2]; ring
  rcases hPp.mem_or_mem hprod with h | h
  · exact key r hrv h
  · exact key (-r) (fun h' => hrv (v.asIdeal.neg_mem_iff.1 h')) h

/-- **Split primes have the same norm:** if $[L : F] = 2$ and $\mathfrak{P} \ne \mathfrak{Q}$ are primes of
$\mathcal{O}_L$ over $\mathfrak{p}$, then $N\mathfrak{P} = N\mathfrak{Q} = N\mathfrak{p}$.

*Proof.* $\sum_{\mathfrak{P}' \mid \mathfrak{p}} e(\mathfrak{P}')f(\mathfrak{P}') = [L:F] = 2$
(`Ideal.sum_ramification_inertia`), and there are at least two terms, each $\ge 1$, so
$f(\mathfrak{P}) = f(\mathfrak{Q}) = 1$; then $N\mathfrak{P} = N\mathfrak{p}^{f(\mathfrak{P})}$
(`Ideal.absNorm_eq_pow_inertiaDeg`-type lemma). -/
@[kb "neukirch1999" "Ch. I, Prop. 8.2 [unverified]"]
theorem absNorm_eq_of_two_primes {L : Type} [Field L] [NumberField L] [Algebra F L]
    (hdeg : Module.finrank F L = 2) (v : HeightOneSpectrum (𝓞 F)) (P Q : HeightOneSpectrum (𝓞 L))
    (hPQ : P ≠ Q) (hP : P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 L)) = v.asIdeal)
    (hQ : Q.asIdeal.comap (algebraMap (𝓞 F) (𝓞 L)) = v.asIdeal) :
    Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal ∧
      Ideal.absNorm Q.asIdeal = Ideal.absNorm v.asIdeal := by
  haveI : P.asIdeal.LiesOver v.asIdeal := ⟨by rw [Ideal.under_def, hP]⟩
  haveI : Q.asIdeal.LiesOver v.asIdeal := ⟨by rw [Ideal.under_def, hQ]⟩
  haveI := v.isMaximal
  haveI := P.isMaximal
  haveI := Q.isMaximal
  have hnorm : ∀ R : HeightOneSpectrum (𝓞 L), R.asIdeal.LiesOver v.asIdeal →
      Ideal.absNorm R.asIdeal = Ideal.absNorm v.asIdeal ^ R.asIdeal.inertiaDeg (𝓞 F) := by
    intro R hR
    haveI := R.isMaximal
    rw [← Ideal.absNorm_relNorm (𝓞 F) (𝓞 L), Ideal.relNorm_eq_pow_of_isMaximal R.asIdeal v.asIdeal, map_pow]
  have hsum := Ideal.sum_ramification_inertia (p := v.asIdeal) (𝓞 L) F L v.ne_bot
  rw [hdeg] at hsum
  have hmemP : P.asIdeal ∈ IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 L) :=
    (IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot _).2 ⟨inferInstance, inferInstance⟩
  have hmemQ : Q.asIdeal ∈ IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 L) :=
    (IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot _).2 ⟨inferInstance, inferInstance⟩
  have hne : P.asIdeal ≠ Q.asIdeal := fun h => hPQ (HeightOneSpectrum.ext h)
  have hle : v.asIdeal.ramificationIdx' P.asIdeal * v.asIdeal.inertiaDeg' P.asIdeal +
      v.asIdeal.ramificationIdx' Q.asIdeal * v.asIdeal.inertiaDeg' Q.asIdeal ≤ 2 := by
    rw [← hsum]
    refine le_trans (le_of_eq (Finset.sum_pair (f := fun X => v.asIdeal.ramificationIdx' X * v.asIdeal.inertiaDeg' X) hne).symm) ?_
    exact Finset.sum_le_sum_of_subset (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption)
  have hmap : Ideal.map (algebraMap (𝓞 F) (𝓞 L)) v.asIdeal ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]
    exact v.ne_bot
  have heP := Ideal.IsDedekindDomain.ramificationIdx_ne_zero hmap P.isPrime
    (Ideal.map_le_iff_le_comap.2 hP.ge)
  have heQ := Ideal.IsDedekindDomain.ramificationIdx_ne_zero hmap Q.isPrime
    (Ideal.map_le_iff_le_comap.2 hQ.ge)
  have hfP := Ideal.inertiaDeg'_pos v.asIdeal P.asIdeal
  have hfQ := Ideal.inertiaDeg'_pos v.asIdeal Q.asIdeal
  have h1P : v.asIdeal.inertiaDeg' P.asIdeal = 1 := by
    have := Nat.one_le_iff_ne_zero.2 heP
    have := Nat.one_le_iff_ne_zero.2 heQ
    nlinarith
  have h1Q : v.asIdeal.inertiaDeg' Q.asIdeal = 1 := by
    have := Nat.one_le_iff_ne_zero.2 heP
    have := Nat.one_le_iff_ne_zero.2 heQ
    nlinarith
  rw [Ideal.inertiaDeg_eq_inertiaDeg'] at h1P h1Q
  rw [hnorm P inferInstance, hnorm Q inferInstance, h1P, h1Q]
  simp

/-- **Splitting of $\mathfrak{p}$ in $F(\sqrt a)$:** let $a \in \mathcal{O}_F$ be a non-square in $F$ and
$L = F(\sqrt a)$ (given by $s \in L$ with $s^2 = a$ and $L = F + F s$). If $\mathfrak{p} \nmid 2a$ and $a$ is a
square in $F_{\mathfrak{p}}$, then $\mathfrak{p}$ splits in $L$: there are two distinct primes
$\mathfrak{P} \ne \mathfrak{Q}$ of $\mathcal{O}_L$ over $\mathfrak{p}$, each of absolute norm $N\mathfrak{p}$.

*Proof* (Neukirch I §8, Prop. 8.3). Combine `exists_sq_mod_of_isSquare`, `exists_two_primes_over` and `absNorm_eq_of_two_primes` ($[L:F] = 2$ from `hspan` and `hd`). Background (Kummer–Dedekind): $s \in \mathcal{O}_L$ and the conductor of
$\mathcal{O}_F[s]$ divides $4a$, which is prime to $\mathfrak{p}$, so primes over $\mathfrak{p}$ correspond to
irreducible factors of $X^2 - \bar a$ over $\mathcal{O}_F/\mathfrak{p}$ (Mathlib: `KummerDedekind`,
`normalizedFactorsMapEquivNormalizedFactorsMinPolyMk`). Since $a$ is a square in $F_{\mathfrak{p}}$ and
a unit, $\bar a = \bar r^2$ is a nonzero square, and $\bar r \ne -\bar r$ as $2 \notin \mathfrak{p}$: two
distinct linear factors, so two primes, each with residue degree $1$. Alternatively use
$\sum_{\mathfrak{P} \mid \mathfrak{p}} e f = 2$ (`Ideal.sum_ramification_inertia`) and exhibit two distinct
primes $\mathfrak{p} + (s - r)$, $\mathfrak{p} + (s + r)$ for a lift $r \in \mathcal{O}_F$. -/
@[kb "neukirch1999" "Ch. I, Prop. 8.3 [unverified]"]
theorem exists_two_primes_of_isSquare {L : Type} [Field L] [NumberField L] [Algebra F L]
    (a : 𝓞 F) (hd : ¬ IsSquare (a : F)) (s : L) (hs : s ^ 2 = algebraMap F L (a : F))
    (hspan : ∀ y : L, ∃ b₀ b₁ : F, y = algebraMap F L b₀ + algebraMap F L b₁ * s)
    (v : HeightOneSpectrum (𝓞 F)) (h2a : (2 * a) ∉ v.asIdeal)
    (hsq : IsSquare (algebraMap F (v.adicCompletion F) (a : F))) :
    ∃ P Q : HeightOneSpectrum (𝓞 L), P ≠ Q ∧
      P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 L)) = v.asIdeal ∧
      Q.asIdeal.comap (algebraMap (𝓞 F) (𝓞 L)) = v.asIdeal ∧
      Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal ∧
      Ideal.absNorm Q.asIdeal = Ideal.absNorm v.asIdeal := by
  obtain ⟨r, hr⟩ := exists_sq_mod_of_isSquare a v h2a hsq
  obtain ⟨P, Q, hPQ, hP, hQ⟩ := exists_two_primes_over a hd s hs hspan v h2a r hr
  have hirr : Irreducible (Polynomial.X ^ 2 - Polynomial.C (a : F)) :=
    _root_.X_pow_sub_C_irreducible_of_prime Nat.prime_two (fun b hb => hd ⟨b, by rw [← hb]; ring⟩)
  have hmin : minpoly F s = Polynomial.X ^ 2 - Polynomial.C (a : F) :=
    (minpoly.eq_of_irreducible_of_monic hirr (by simp [hs]) (Polynomial.monic_X_pow_sub_C _ (by norm_num))).symm
  have hsF : IsIntegral F s := .of_finite F s
  have htop : Algebra.adjoin F {s} = ⊤ := by
    rw [Algebra.eq_top_iff]
    intro y
    obtain ⟨b₀, b₁, rfl⟩ := hspan y
    exact Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ _) (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (Algebra.subset_adjoin rfl))
  let pb := PowerBasis.ofAdjoinEqTop hsF htop
  have hdeg : Module.finrank F L = 2 := by
    rw [pb.finrank]
    show (minpoly F s).natDegree = 2
    rw [hmin]
    exact Polynomial.natDegree_X_pow_sub_C
  obtain ⟨h1, h2⟩ := absNorm_eq_of_two_primes hdeg v P Q hPQ hP hQ
  exact ⟨P, Q, hPQ, hP, hQ, h1, h2⟩

/-- **Counting ideals when almost all primes split:** let $L \supseteq F$ be number fields and $S$ a
finite set of primes of $F$ such that every prime $\mathfrak{p} \notin S$ has two distinct primes
$\mathfrak{P} \ne \mathfrak{Q}$ of $L$ over it, both of norm $N\mathfrak{p}$. Then for every $n \ge 1$,
the number of ideals of $\mathcal{O}_L$ of norm $n$ is at least the number of pairs
$(\mathfrak{a}, \mathfrak{b})$ of ideals of $\mathcal{O}_F$, both prime to $S$, with
$N\mathfrak{a} \, N\mathfrak{b} = n$.

*Proof.* Choose $\mathfrak{p} \mapsto (\mathfrak{P}, \mathfrak{Q})$ for $\mathfrak{p} \notin S$ and send
$(\mathfrak{a}, \mathfrak{b}) = (\prod \mathfrak{p}^{e_\mathfrak{p}}, \prod \mathfrak{p}^{f_\mathfrak{p}})$ to
$\prod \mathfrak{P}^{e_\mathfrak{p}} \mathfrak{Q}^{f_\mathfrak{p}}$ (unique factorization of ideals in
Dedekind domains, `Ideal.factorization` / `normalizedFactors`). Norms multiply
(`Ideal.absNorm` is multiplicative), so the norm is $N\mathfrak{a}\,N\mathfrak{b}$; the map is injective
because the $\mathfrak{P}$'s and $\mathfrak{Q}$'s are pairwise distinct primes (over distinct
$\mathfrak{p}$ they differ by `comap`). -/
@[kb "neukirch1999" "Ch. VII §13 [unverified]"]
theorem card_pairs_le_card_ideals {L : Type} [Field L] [NumberField L] [Algebra F L]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hsplit : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ∃ P Q : HeightOneSpectrum (𝓞 L), P ≠ Q ∧
      P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 L)) = v.asIdeal ∧
      Q.asIdeal.comap (algebraMap (𝓞 F) (𝓞 L)) = v.asIdeal ∧
      Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal ∧
      Ideal.absNorm Q.asIdeal = Ideal.absNorm v.asIdeal)
    (n : ℕ) (hn : 0 < n) :
    Nat.card {p : Ideal (𝓞 F) × Ideal (𝓞 F) // (∀ v ∈ S, ¬ p.1 ≤ v.asIdeal) ∧
        (∀ v ∈ S, ¬ p.2 ≤ v.asIdeal) ∧ Ideal.absNorm p.1 * Ideal.absNorm p.2 = n} ≤
      Nat.card {I : Ideal (𝓞 L) // Ideal.absNorm I = n} := by
  classical
  let Good : Ideal (𝓞 F) → Prop := fun p => ∃ v : HeightOneSpectrum (𝓞 F), v ∉ S ∧ v.asIdeal = p
  have key : ∀ p : Ideal (𝓞 F), Good p → ∃ P Q : Ideal (𝓞 L), P ≠ Q ∧ Prime P ∧ Prime Q ∧
      P.comap (algebraMap (𝓞 F) (𝓞 L)) = p ∧ Q.comap (algebraMap (𝓞 F) (𝓞 L)) = p ∧
      Ideal.absNorm P = Ideal.absNorm p ∧ Ideal.absNorm Q = Ideal.absNorm p := by
    rintro p ⟨v, hv, rfl⟩
    obtain ⟨P, Q, hPQ, h1, h2, h3, h4⟩ := hsplit v hv
    refine ⟨P.asIdeal, Q.asIdeal, ?_, P.prime, Q.prime, h1, h2, h3, h4⟩
    intro h; exact hPQ (HeightOneSpectrum.ext h)
  let φ : Ideal (𝓞 F) → Ideal (𝓞 L) := fun p => if h : Good p then (key p h).choose else ⊤
  let ψ : Ideal (𝓞 F) → Ideal (𝓞 L) := fun p => if h : Good p then (key p h).choose_spec.choose else ⊤
  have hφ : ∀ p, Good p → φ p ≠ ψ p ∧ Prime (φ p) ∧ Prime (ψ p) ∧
      (φ p).comap (algebraMap (𝓞 F) (𝓞 L)) = p ∧ (ψ p).comap (algebraMap (𝓞 F) (𝓞 L)) = p ∧
      Ideal.absNorm (φ p) = Ideal.absNorm p ∧ Ideal.absNorm (ψ p) = Ideal.absNorm p := by
    intro p hp
    simp only [φ, ψ, dif_pos hp]
    exact (key p hp).choose_spec.choose_spec
  let g : Ideal (𝓞 L) → Ideal (𝓞 F) ⊕ Ideal (𝓞 F) := fun P =>
    if φ (P.comap (algebraMap (𝓞 F) (𝓞 L))) = P then Sum.inl (P.comap (algebraMap (𝓞 F) (𝓞 L)))
    else Sum.inr (P.comap (algebraMap (𝓞 F) (𝓞 L)))
  have hgφ : ∀ p, Good p → g (φ p) = Sum.inl p := by
    intro p hp
    obtain ⟨-, -, -, h1, -⟩ := hφ p hp
    simp only [g, h1, if_true]
  have hgψ : ∀ p, Good p → g (ψ p) = Sum.inr p := by
    intro p hp
    obtain ⟨hne, -, -, -, h2, -⟩ := hφ p hp
    simp only [g, h2, if_neg hne]
  have hgood : ∀ I : Ideal (𝓞 F), (∀ v ∈ S, ¬ I ≤ v.asIdeal) → I ≠ ⊥ →
      ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors I, Good p := by
    intro I hI hI0 p hp
    have hpr : Prime p := UniqueFactorizationMonoid.prime_of_normalized_factor p hp
    have hdvd : p ∣ I := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hp
    refine ⟨⟨p, Ideal.isPrime_of_prime hpr, hpr.ne_zero⟩, ?_, rfl⟩
    intro hS
    exact hI _ hS (Ideal.le_of_dvd hdvd)
  let T := {p : Ideal (𝓞 F) × Ideal (𝓞 F) // (∀ v ∈ S, ¬ p.1 ≤ v.asIdeal) ∧
          (∀ v ∈ S, ¬ p.2 ≤ v.asIdeal) ∧ Ideal.absNorm p.1 * Ideal.absNorm p.2 = n}
  have hne : ∀ x : T, x.1.1 ≠ ⊥ ∧ x.1.2 ≠ ⊥ := by
    intro x
    have h := x.2.2.2
    constructor
    · intro h0; rw [h0, Ideal.absNorm_bot] at h; omega
    · intro h0; rw [h0, Ideal.absNorm_bot] at h; omega
  let M : T → Multiset (Ideal (𝓞 L)) := fun x =>
    (UniqueFactorizationMonoid.normalizedFactors x.1.1).map φ +
      (UniqueFactorizationMonoid.normalizedFactors x.1.2).map ψ
  have hMprime : ∀ x : T, ∀ P ∈ M x, Prime P := by
    intro x P hP
    rcases Multiset.mem_add.1 hP with h | h
    · obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 h
      exact (hφ p (hgood _ x.2.1 (hne x).1 p hp)).2.1
    · obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 h
      exact (hφ p (hgood _ x.2.2.1 (hne x).2 p hp)).2.2.1
  have hMnorm : ∀ x : T, Ideal.absNorm (M x).prod = n := by
    intro x
    rw [← x.2.2.2, map_multiset_prod, Multiset.map_add, Multiset.prod_add, Multiset.map_map,
      Multiset.map_map]
    have e1 : Multiset.map (Ideal.absNorm ∘ φ) (UniqueFactorizationMonoid.normalizedFactors x.1.1)
        = Multiset.map Ideal.absNorm (UniqueFactorizationMonoid.normalizedFactors x.1.1) := by
      apply Multiset.map_congr rfl
      intro p hp
      exact (hφ p (hgood _ x.2.1 (hne x).1 p hp)).2.2.2.2.2.1
    have e2 : Multiset.map (Ideal.absNorm ∘ ψ) (UniqueFactorizationMonoid.normalizedFactors x.1.2)
        = Multiset.map Ideal.absNorm (UniqueFactorizationMonoid.normalizedFactors x.1.2) := by
      apply Multiset.map_congr rfl
      intro p hp
      exact (hφ p (hgood _ x.2.2.1 (hne x).2 p hp)).2.2.2.2.2.2
    rw [e1, e2, ← map_multiset_prod, ← map_multiset_prod,
      Ideal.prod_normalizedFactors_eq_self (hne x).1, Ideal.prod_normalizedFactors_eq_self (hne x).2]
  have hMg : ∀ x : T, (M x).map g =
      (UniqueFactorizationMonoid.normalizedFactors x.1.1).map Sum.inl +
      (UniqueFactorizationMonoid.normalizedFactors x.1.2).map Sum.inr := by
    intro x
    simp only [M, Multiset.map_add, Multiset.map_map]
    congr 1
    · apply Multiset.map_congr rfl
      intro p hp
      exact hgφ p (hgood _ x.2.1 (hne x).1 p hp)
    · apply Multiset.map_congr rfl
      intro p hp
      exact hgψ p (hgood _ x.2.2.1 (hne x).2 p hp)
  haveI : Finite {I : Ideal (𝓞 L) // Ideal.absNorm I = n} :=
    (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
  let f : T → {I : Ideal (𝓞 L) // Ideal.absNorm I = n} := fun x => ⟨(M x).prod, hMnorm x⟩
  have hnone : ∀ s : Multiset (Ideal (𝓞 F)),
      Multiset.filterMap (fun _ => (none : Option (Ideal (𝓞 F)))) s = 0 := by
    intro s
    induction s using Multiset.induction_on with
    | empty => rfl
    | cons a s ih => rw [Multiset.filterMap_cons_none _ _ rfl, ih]
  have hinj : Function.Injective f := by
    intro x y hxy
    have h1 : (M x).prod = (M y).prod := congrArg Subtype.val hxy
    have h2 : M x = M y := by
      rw [← UniqueFactorizationMonoid.normalizedFactors_prod_of_prime (hMprime x),
        ← UniqueFactorizationMonoid.normalizedFactors_prod_of_prime (hMprime y), h1]
    have h3 := congrArg (Multiset.map g) h2
    rw [hMg, hMg] at h3
    have hl := congrArg (Multiset.filterMap Sum.getLeft?) h3
    have hr := congrArg (Multiset.filterMap Sum.getRight?) h3
    simp only [Multiset.filterMap_add, Multiset.filterMap_map] at hl hr
    have ea : ∀ s : Multiset (Ideal (𝓞 F)),
        Multiset.filterMap (Sum.getLeft? ∘ (Sum.inl : _ → Ideal (𝓞 F) ⊕ Ideal (𝓞 F))) s = s := by
      intro s
      have : (Sum.getLeft? ∘ (Sum.inl : _ → Ideal (𝓞 F) ⊕ Ideal (𝓞 F))) = some := by
        funext a; rfl
      rw [this, Multiset.filterMap_some]
    have eb : ∀ s : Multiset (Ideal (𝓞 F)),
        Multiset.filterMap (Sum.getLeft? ∘ (Sum.inr : _ → Ideal (𝓞 F) ⊕ Ideal (𝓞 F))) s = 0 := by
      intro s
      have : (Sum.getLeft? ∘ (Sum.inr : _ → Ideal (𝓞 F) ⊕ Ideal (𝓞 F))) = fun _ => none := by
        funext a; rfl
      rw [this, hnone]
    have ec : ∀ s : Multiset (Ideal (𝓞 F)),
        Multiset.filterMap (Sum.getRight? ∘ (Sum.inr : _ → Ideal (𝓞 F) ⊕ Ideal (𝓞 F))) s = s := by
      intro s
      have : (Sum.getRight? ∘ (Sum.inr : _ → Ideal (𝓞 F) ⊕ Ideal (𝓞 F))) = some := by
        funext a; rfl
      rw [this, Multiset.filterMap_some]
    have ed : ∀ s : Multiset (Ideal (𝓞 F)),
        Multiset.filterMap (Sum.getRight? ∘ (Sum.inl : _ → Ideal (𝓞 F) ⊕ Ideal (𝓞 F))) s = 0 := by
      intro s
      have : (Sum.getRight? ∘ (Sum.inl : _ → Ideal (𝓞 F) ⊕ Ideal (𝓞 F))) = fun _ => none := by
        funext a; rfl
      rw [this, hnone]
    rw [ea, ea, eb, eb, add_zero, add_zero] at hl
    rw [ec, ec, ed, ed, zero_add, zero_add] at hr
    apply Subtype.ext
    apply Prod.ext
    · rw [← Ideal.prod_normalizedFactors_eq_self (hne x).1,
        ← Ideal.prod_normalizedFactors_eq_self (hne y).1, hl]
    · rw [← Ideal.prod_normalizedFactors_eq_self (hne x).2,
        ← Ideal.prod_normalizedFactors_eq_self (hne y).2, hr]
  exact Nat.card_le_card_of_injective f hinj

/-- **Removing finitely many primes costs a bounded factor:** for a finite set $S$ of primes of $F$
and real $s > 1$, $\zeta_F(s) \le 2^{|S|} \sum_{\mathfrak{a}\ \text{prime to}\ S} N\mathfrak{a}^{-s}$.

*Proof.* Each nonzero ideal is uniquely $\mathfrak{a}_S \mathfrak{a}'$ with $\mathfrak{a}_S$ supported on $S$
and $\mathfrak{a}'$ prime to $S$, so $\zeta_F(s) = \prod_{\mathfrak{p} \in S} (1 - N\mathfrak{p}^{-s})^{-1}
\cdot \sum_{\mathfrak{a}'} N\mathfrak{a}'^{-s}$, and $(1 - N\mathfrak{p}^{-s})^{-1} \le 2$ as $N\mathfrak{p} \ge 2$.
(Only the inequality is needed.) -/
@[kb "neukirch1999" "Ch. VII §13 [unverified]"]
theorem dedekindZeta_le_sFree (S : Finset (HeightOneSpectrum (𝓞 F))) (s : ℝ) (hs : 1 < s) :
    (dedekindZeta F s).re ≤ 2 ^ S.card * ∑' n : ℕ,
      (Nat.card {I : Ideal (𝓞 F) // (∀ v ∈ S, ¬ I ≤ v.asIdeal) ∧ Ideal.absNorm I = n} : ℝ) /
        (n : ℝ) ^ s := by
  classical
  have hs0 : s ≠ 0 := by linarith
  set a : ℕ → ℝ := fun n => (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℝ) with ha
  have hterm : ∀ n : ℕ, LSeries.term (fun n => (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ)) (s : ℂ) n
      = ((a n / (n : ℝ) ^ s : ℝ) : ℂ) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [Real.zero_rpow hs0]
    · rw [LSeries.term_of_ne_zero hn, Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg _)]
      simp [ha]
  have hzeta : (dedekindZeta F s).re = ∑' n : ℕ, a n / (n : ℝ) ^ s := by
    rw [dedekindZeta, LSeries]
    simp_rw [hterm]
    rw [← Complex.ofReal_tsum, Complex.ofReal_re]
  have hsumC : LSeriesSummable (fun n => (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ)) (s : ℂ) := by
    by_contra hns
    have hev : (fun t : ℝ => ((t : ℂ) - 1) * dedekindZeta F t) =ᶠ[nhdsWithin 1 (Set.Ioi 1)] fun _ => 0 := by
      filter_upwards [Ioo_mem_nhdsGT hs] with t ht
      have : ¬ LSeriesSummable (fun n => (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ)) (t : ℂ) := by
        intro h
        exact hns (h.of_re_le_re (by simpa using ht.2.le))
      rw [dedekindZeta, LSeries.eq_zero_of_not_LSeriesSummable _ _ this, mul_zero]
    have h1 := tendsto_sub_one_mul_dedekindZeta_nhdsGT F
    have h2 : Filter.Tendsto (fun t : ℝ => ((t : ℂ) - 1) * dedekindZeta F t) (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) :=
      tendsto_const_nhds.congr' hev.symm
    have := tendsto_nhds_unique h1 h2
    have hpos := dedekindZeta_residue_pos F
    norm_cast at this
    linarith
  have hsumR : Summable (fun n : ℕ => a n / (n : ℝ) ^ s) :=
    Complex.summable_ofReal.mp (Summable.congr hsumC hterm)
  set P : Finset (HeightOneSpectrum (𝓞 F)) → Ideal (𝓞 F) → Prop := fun T I => ∀ v ∈ T, ¬ I ≤ v.asIdeal with hP
  set G : Ideal (𝓞 F) → ENNReal := fun I => ENNReal.ofReal (1 / ((Ideal.absNorm I : ℕ) : ℝ) ^ s) with hG
  set Z : Finset (HeightOneSpectrum (𝓞 F)) → ENNReal := fun T => ∑' I, Set.indicator {I | P T I} G I with hZ
  have hconv : ∀ T, ∑' n : ℕ, ENNReal.ofReal ((Nat.card {I : Ideal (𝓞 F) // P T I ∧ Ideal.absNorm I = n} : ℝ) / (n : ℝ) ^ s) = Z T := by
    intro T
    show _ = ∑' I, Set.indicator {I | P T I} G I
    rw [← tsum_subtype {I | P T I} G]
    rw [← (Equiv.sigmaFiberEquiv (fun J : ({I | P T I} : Set (Ideal (𝓞 F))) => Ideal.absNorm (J : Ideal (𝓞 F)))).tsum_eq]
    rw [ENNReal.tsum_sigma']
    congr 1
    funext n
    have hfin : Finite {J : ({I | P T I} : Set (Ideal (𝓞 F))) // Ideal.absNorm (J : Ideal (𝓞 F)) = n} := by
      have : Finite {I : Ideal (𝓞 F) | Ideal.absNorm I = n} := (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
      exact Finite.of_injective (fun J : {J : ({I | P T I} : Set (Ideal (𝓞 F))) // Ideal.absNorm (J : Ideal (𝓞 F)) = n} => (⟨J.1.1, J.2⟩ : {I : Ideal (𝓞 F) | Ideal.absNorm I = n})) (by
        intro x y hxy
        simp at hxy
        exact Subtype.ext (Subtype.ext hxy))
    have hfib : ∀ c : {J : ({I | P T I} : Set (Ideal (𝓞 F))) // Ideal.absNorm (J : Ideal (𝓞 F)) = n},
        G ((Equiv.sigmaFiberEquiv (fun J : ({I | P T I} : Set (Ideal (𝓞 F))) => Ideal.absNorm (J : Ideal (𝓞 F)))) ⟨n, c⟩) = ENNReal.ofReal (1 / (n : ℝ) ^ s) := by
      intro c
      simp [Equiv.sigmaFiberEquiv, hG, c.2]
    simp_rw [hfib]
    have := Fintype.ofFinite {J : ({I | P T I} : Set (Ideal (𝓞 F))) // Ideal.absNorm (J : Ideal (𝓞 F)) = n}
    have hcard : Nat.card {J : ({I | P T I} : Set (Ideal (𝓞 F))) // Ideal.absNorm (J : Ideal (𝓞 F)) = n} = Nat.card {I : Ideal (𝓞 F) // P T I ∧ Ideal.absNorm I = n} :=
      Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun I => I ∈ {I | P T I}) (fun I => Ideal.absNorm I = n))
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
      hcard, div_eq_mul_one_div, ENNReal.ofReal_mul (by positivity)]
    simp
  have hle : ∀ T, Z T ≤ Z ∅ := by
    intro T
    apply ENNReal.tsum_le_tsum
    intro I
    apply Set.indicator_le_indicator_of_subset
    · intro I _; simp [hP]
    · intro _; exact bot_le
  have hcardE : ∀ n : ℕ, (Nat.card {I : Ideal (𝓞 F) // P ∅ I ∧ Ideal.absNorm I = n} : ℝ) = a n := by
    intro n
    simp only [ha]
    congr 1
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun I => by simp [hP]))
  have hfin0 : Z ∅ ≠ ⊤ := by
    rw [← hconv ∅]
    simp_rw [hcardE]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => div_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hsumR]
    exact ENNReal.ofReal_ne_top
  have hstep : ∀ T, ∀ p ∉ T, Z T ≤ 2 * Z (insert p T) := by
    intro T p hp
    set q := p.asIdeal with hq
    have hq0 : q ≠ ⊥ := p.ne_bot
    have hNq : (2:ℝ) ≤ ((Ideal.absNorm q : ℕ) : ℝ) := by
      have h0 : Ideal.absNorm q ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
      have h1 : Ideal.absNorm q ≠ 1 := by rw [Ne, Ideal.absNorm_eq_one_iff]; exact p.isPrime.ne_top
      norm_cast; omega
    set c : ENNReal := ENNReal.ofReal (1 / ((Ideal.absNorm q : ℕ) : ℝ) ^ s) with hc
    have hc2 : c ≤ 2⁻¹ := by
      have : 1 / ((Ideal.absNorm q : ℕ) : ℝ) ^ s ≤ 1 / 2 := by
        apply one_div_le_one_div_of_le (by norm_num)
        calc (2:ℝ) ≤ ((Ideal.absNorm q : ℕ) : ℝ) := hNq
          _ = ((Ideal.absNorm q : ℕ) : ℝ) ^ (1:ℝ) := (Real.rpow_one _).symm
          _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) hs.le
      rw [hc]
      calc ENNReal.ofReal (1 / ((Ideal.absNorm q : ℕ) : ℝ) ^ s) ≤ ENNReal.ofReal (1/2) := ENNReal.ofReal_le_ofReal this
        _ = 2⁻¹ := by rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]; simp
    set h : Ideal (𝓞 F) → ENNReal := Set.indicator {I | P T I ∧ I ≤ q} G with hh
    have h1 : Z T ≤ Z (insert p T) + ∑' I, h I := by
      rw [← ENNReal.tsum_add]
      apply ENNReal.tsum_le_tsum
      intro I
      by_cases hI : P T I
      · by_cases hIq : I ≤ q
        · have : h I = G I := Set.indicator_of_mem (show I ∈ {I | P T I ∧ I ≤ q} from ⟨hI, hIq⟩) _
          rw [this, Set.indicator_of_mem (show I ∈ {I | P T I} from hI)]
          exact le_add_self
        · have : I ∈ {I | P (insert p T) I} := by
            intro v hv
            rcases Finset.mem_insert.mp hv with rfl | hv
            · exact hIq
            · exact hI v hv
          rw [Set.indicator_of_mem this, Set.indicator_of_mem (show I ∈ {I | P T I} from hI)]
          exact le_self_add
      · rw [Set.indicator_of_notMem (show I ∉ {I | P T I} from hI)]; exact bot_le
    have h2 : ∑' I, h I ≤ c * Z T := by
      have hinj : Function.Injective (fun J : Ideal (𝓞 F) => q * J) := fun x y hxy => mul_left_cancel₀ hq0 hxy
      have hsupp : Function.support h ⊆ Set.range (fun J : Ideal (𝓞 F) => q * J) := by
        intro I hI
        have hmem : I ∈ {I | P T I ∧ I ≤ q} := by
          by_contra hn; exact hI (Set.indicator_of_notMem hn _)
        obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hmem.2
        exact ⟨J, hJ.symm⟩
      rw [← hinj.tsum_eq hsupp, ← ENNReal.tsum_mul_left]
      apply ENNReal.tsum_le_tsum
      intro J
      by_cases hJ : q * J ∈ {I | P T I ∧ I ≤ q}
      · have hPJ : P T J := fun v hv hle => hJ.1 v hv (le_trans Ideal.mul_le_right hle)
        simp only [hh]
        rw [Set.indicator_of_mem hJ, Set.indicator_of_mem (show J ∈ {I | P T I} from hPJ), hG, hc]
        simp only
        rw [← ENNReal.ofReal_mul (by positivity), map_mul, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _), one_div_mul_one_div]
      · simp only [hh]; rw [Set.indicator_of_notMem hJ]; exact bot_le
    have hZT : Z T ≠ ⊤ := ne_top_of_le_ne_top hfin0 (hle T)
    have h3 : Z T ≤ Z (insert p T) + 2⁻¹ * Z T := by
      refine h1.trans ?_
      gcongr
      exact h2.trans (mul_le_mul_of_nonneg_right hc2 bot_le)
    have h4 : Z T + Z T ≤ 2 * Z (insert p T) + Z T := by
      calc Z T + Z T = 2 * Z T := (two_mul _).symm
        _ ≤ 2 * (Z (insert p T) + 2⁻¹ * Z T) := by gcongr
        _ = 2 * Z (insert p T) + Z T := by
          rw [mul_add, ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
    exact (ENNReal.add_le_add_iff_right hZT).mp h4
  have hind : ∀ T : Finset (HeightOneSpectrum (𝓞 F)), Z ∅ ≤ 2 ^ T.card * Z T := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | insert p T hp ih =>
      rw [Finset.card_insert_of_notMem hp, pow_succ, mul_assoc]
      exact ih.trans (by gcongr; exact hstep T p hp)
  have hreal : ∀ T, ∑' n : ℕ, (Nat.card {I : Ideal (𝓞 F) // P T I ∧ Ideal.absNorm I = n} : ℝ) / (n : ℝ) ^ s = (Z T).toReal := by
    intro T
    rw [← hconv T, ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
    congr 1; funext n
    rw [ENNReal.toReal_ofReal (by positivity)]
  have hfinS : Z S ≠ ⊤ := ne_top_of_le_ne_top hfin0 (hle S)
  rw [hzeta]
  have e0 : ∑' n : ℕ, a n / (n : ℝ) ^ s = (Z ∅).toReal := by
    rw [← hreal ∅]
    simp_rw [hcardE]
  rw [e0]
  change (Z ∅).toReal ≤ 2 ^ S.card * ∑' n : ℕ, (Nat.card {I : Ideal (𝓞 F) // P S I ∧ Ideal.absNorm I = n} : ℝ) / (n : ℝ) ^ s
  rw [hreal S]
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) hfinS) (hind S)
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow] at this
  simpa using this

/-- **A quadratic extension cannot split at almost all primes:** with $L = F(\sqrt a)$ as above
($a$ not a square), there is no finite set $S$ outside which every prime of $F$ splits into two
primes of $L$ of the same norm.

*Proof.* For real $s > 1$, by `card_pairs_le_card_ideals` (Dirichlet series with nonnegative
coefficients, `LSeries_convolution`) and `dedekindZeta_le_sFree`,
$\zeta_L(s) \ge (\sum_{\mathfrak{a}\ \text{prime to}\ S} N\mathfrak{a}^{-s})^2 \ge 4^{-|S|} \zeta_F(s)^2$.
By the class number formula `tendsto_sub_one_mul_dedekindZeta_nhdsGT` for $F$ and $L$,
$(s-1)\zeta_L(s)$ tends to a finite limit while $(s-1)\zeta_F(s)^2 = ((s-1)\zeta_F(s)) \cdot \zeta_F(s)$
tends to $+\infty$ (the first factor tends to the residue $> 0$, `dedekindZeta_residue_pos`, so
$\zeta_F(s) \to \infty$). Contradiction. -/
@[kb "neukirch1999" "Ch. VII, Cor. 13.7 [unverified]"]
theorem not_almost_all_split {L : Type} [Field L] [NumberField L] [Algebra F L]
    (a : F) (hd : ¬ IsSquare a) (s : L) (hs : s ^ 2 = algebraMap F L a)
    (hspan : ∀ y : L, ∃ b₀ b₁ : F, y = algebraMap F L b₀ + algebraMap F L b₁ * s)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hsplit : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ∃ P Q : HeightOneSpectrum (𝓞 L), P ≠ Q ∧
      P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 L)) = v.asIdeal ∧
      Q.asIdeal.comap (algebraMap (𝓞 F) (𝓞 L)) = v.asIdeal ∧
      Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal ∧
      Ideal.absNorm Q.asIdeal = Ideal.absNorm v.asIdeal) : False := by
  classical
  have hgen : ∀ (s : ℝ), 1 < s → ∀ (X : Type) (N : X → ℕ), (∀ n, 0 < n → Finite {x // N x = n}) →
      ∑' x, ENNReal.ofReal (1 / (N x : ℝ)^s) = ∑' n : ℕ, ENNReal.ofReal ((Nat.card {x // N x = n} : ℝ) / (n:ℝ)^s) := by
    intro s hs X N hfin
    have hs0 : s ≠ 0 := by linarith
    rw [← (Equiv.sigmaFiberEquiv N).tsum_eq, ENNReal.tsum_sigma']
    congr 1
    funext n
    have hc : ∀ c : {x // N x = n}, ENNReal.ofReal (1 / (N ((Equiv.sigmaFiberEquiv N) ⟨n, c⟩) : ℝ)^s)
        = ENNReal.ofReal (1 / (n : ℝ)^s) := by
      intro c
      simp [Equiv.sigmaFiberEquiv, c.2]
    simp_rw [hc]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Real.zero_rpow hs0]
    · have := hfin n hn
      have := Fintype.ofFinite {x // N x = n}
      rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
        div_eq_mul_inv (Nat.card _ : ℝ), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, one_div]
  have hfinle : ∀ n : ℕ, {I : Ideal (𝓞 F) | Ideal.absNorm I ≤ n}.Finite := by
    intro n
    have : {I : Ideal (𝓞 F) | Ideal.absNorm I ≤ n} = ⋃ d ∈ Finset.range (n+1), {I | Ideal.absNorm I = d} := by
      ext I; simp [Nat.lt_succ_iff]
    rw [this]
    exact Set.Finite.biUnion (Finset.finite_toSet _) (fun d _ => Ideal.finite_setOfPred_absNorm_eq d)
  have hL : ∀ s : ℝ, 1 < s → (dedekindZeta L s).re = ∑' n : ℕ, (Nat.card {I : Ideal (𝓞 L) // Ideal.absNorm I = n} : ℝ) / (n:ℝ)^s ∧ Summable (fun n : ℕ => (Nat.card {I : Ideal (𝓞 L) // Ideal.absNorm I = n} : ℝ) / (n:ℝ)^s) := by
    intro s hs
    have hs0 : s ≠ 0 := by linarith
    have hterm : ∀ n : ℕ, LSeries.term (fun n => (Nat.card {I : Ideal (𝓞 L) // Ideal.absNorm I = n} : ℂ)) (s : ℂ) n
        = (((Nat.card {I : Ideal (𝓞 L) // Ideal.absNorm I = n} : ℝ) / (n : ℝ) ^ s : ℝ) : ℂ) := by
      intro n
      rcases eq_or_ne n 0 with rfl | hn
      · simp [Real.zero_rpow hs0]
      · rw [LSeries.term_of_ne_zero hn, Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg _)]
        simp
    have hzeta : (dedekindZeta L s).re = ∑' n : ℕ, (Nat.card {I : Ideal (𝓞 L) // Ideal.absNorm I = n} : ℝ) / (n:ℝ)^s := by
      rw [dedekindZeta, LSeries]
      simp_rw [hterm]
      rw [← Complex.ofReal_tsum, Complex.ofReal_re]
    have hsumC : LSeriesSummable (fun n => (Nat.card {I : Ideal (𝓞 L) // Ideal.absNorm I = n} : ℂ)) (s : ℂ) := by
      by_contra hns
      have hev : (fun t : ℝ => ((t : ℂ) - 1) * dedekindZeta L t) =ᶠ[nhdsWithin 1 (Set.Ioi 1)] fun _ => 0 := by
        filter_upwards [Ioo_mem_nhdsGT hs] with t ht
        have : ¬ LSeriesSummable (fun n => (Nat.card {I : Ideal (𝓞 L) // Ideal.absNorm I = n} : ℂ)) (t : ℂ) := by
          intro h
          exact hns (h.of_re_le_re (by simpa using ht.2.le))
        rw [dedekindZeta, LSeries.eq_zero_of_not_LSeriesSummable _ _ this, mul_zero]
      have h1 := tendsto_sub_one_mul_dedekindZeta_nhdsGT L
      have h2 : Filter.Tendsto (fun t : ℝ => ((t : ℂ) - 1) * dedekindZeta L t) (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) :=
        tendsto_const_nhds.congr' hev.symm
      have := tendsto_nhds_unique h1 h2
      have hpos := dedekindZeta_residue_pos L
      norm_cast at this
      linarith
    exact ⟨hzeta, Complex.summable_ofReal.mp (Summable.congr hsumC hterm)⟩
  have key : ∀ s : ℝ, 1 < s → ∃ X : ℝ, 0 ≤ X ∧ (dedekindZeta F s).re ≤ 2 ^ S.card * X ∧
      X ^ 2 ≤ (dedekindZeta L s).re := by
    intro s hs
    obtain ⟨hzL, hsumL⟩ := hL s hs
    have hzL0 : 0 ≤ (dedekindZeta L s).re := hzL ▸ tsum_nonneg (fun n => by positivity)
    set C : ℕ → ℝ := fun n => (Nat.card {I : Ideal (𝓞 F) // (∀ v ∈ S, ¬ I ≤ v.asIdeal) ∧ Ideal.absNorm I = n} : ℝ) with hC
    set Z : ENNReal := ∑' n : ℕ, ENNReal.ofReal (C n / (n:ℝ)^s) with hZdef
    have hZreal : Z.toReal = ∑' n : ℕ, C n / (n:ℝ)^s := by
      rw [hZdef, ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
      congr 1; funext n; rw [ENNReal.toReal_ofReal (by positivity)]
    refine ⟨Z.toReal, ENNReal.toReal_nonneg, ?_, ?_⟩
    · rw [hZreal]; exact dedekindZeta_le_sFree S s hs
    let X := {I : Ideal (𝓞 F) // ∀ v ∈ S, ¬ I ≤ v.asIdeal}
    let G : X → ENNReal := fun I => ENNReal.ofReal (1 / ((Ideal.absNorm I.1 : ℕ) : ℝ) ^ s)
    have hZ : Z = ∑' I, G I := by
      rw [hgen s hs X (fun I => Ideal.absNorm I.1)]
      · rw [hZdef]
        congr 1; funext n
        rw [hC]
        beta_reduce
        rw [Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun I : Ideal (𝓞 F) => ∀ v ∈ S, ¬ I ≤ v.asIdeal) (fun I => Ideal.absNorm I = n))]
      · intro n _
        have : Finite {I : Ideal (𝓞 F) | Ideal.absNorm I = n} := (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
        exact Finite.of_injective (fun J : {J : X // Ideal.absNorm J.1 = n} => (⟨J.1.1, J.2⟩ : {I : Ideal (𝓞 F) | Ideal.absNorm I = n})) (by
          intro x y hxy
          simp at hxy
          exact Subtype.ext (Subtype.ext hxy))
    have hZZ : Z * Z ≤ ENNReal.ofReal (dedekindZeta L s).re := by
      have e1 : Z * Z = ∑' p : X × X, ENNReal.ofReal (1 / ((Ideal.absNorm p.1.1 * Ideal.absNorm p.2.1 : ℕ) : ℝ) ^ s) := by
        calc Z * Z = ∑' I, ∑' J, G I * G J := by
                rw [hZ, ← ENNReal.tsum_mul_right]; congr 1; funext I; rw [← ENNReal.tsum_mul_left]
          _ = ∑' p : X × X, G p.1 * G p.2 := (ENNReal.tsum_prod (f := fun I J => G I * G J)).symm
          _ = _ := by
                congr 1; funext p
                simp only [G]
                rw [← ENNReal.ofReal_mul (by positivity), Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _), one_div_mul_one_div]
      rw [e1, hgen s hs (X × X) (fun p => Ideal.absNorm p.1.1 * Ideal.absNorm p.2.1), hzL,
        ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsumL]
      · apply ENNReal.tsum_le_tsum
        intro n
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp [Real.zero_rpow (by linarith : s ≠ 0)]
        apply ENNReal.ofReal_le_ofReal
        gcongr
        have := card_pairs_le_card_ideals S hsplit n hn
        refine le_trans (le_of_eq ?_) this
        refine Nat.card_congr
          { toFun := fun x => ⟨(x.1.1.1, x.1.2.1), x.1.1.2, x.1.2.2, x.2⟩
            invFun := fun p => ⟨(⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2.1⟩), p.2.2.2⟩
            left_inv := fun x => rfl
            right_inv := fun p => rfl }
      · intro n hn
        have h1 := (hfinle n).to_subtype
        exact Finite.of_injective (fun x : {p : X × X // Ideal.absNorm p.1.1 * Ideal.absNorm p.2.1 = n} =>
          ((⟨x.1.1.1, Nat.le_of_dvd hn (Dvd.intro _ x.2)⟩ : {I : Ideal (𝓞 F) | Ideal.absNorm I ≤ n}),
           (⟨x.1.2.1, Nat.le_of_dvd hn (Dvd.intro_left _ x.2)⟩ : {I : Ideal (𝓞 F) | Ideal.absNorm I ≤ n}))) (by
          intro x y hxy
          simp only [Prod.mk.injEq, Subtype.mk.injEq] at hxy
          exact Subtype.ext (Prod.ext (Subtype.ext hxy.1) (Subtype.ext hxy.2)))
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hZZ
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hzL0] at this
    nlinarith
  have hFre : Filter.Tendsto (fun t : ℝ => (t - 1) * (dedekindZeta F t).re) (nhdsWithin 1 (Set.Ioi 1))
      (nhds (dedekindZeta_residue F)) := by
    have := (Complex.continuous_re.tendsto _).comp (tendsto_sub_one_mul_dedekindZeta_nhdsGT F)
    simpa [Function.comp_def] using this
  have hLre : Filter.Tendsto (fun t : ℝ => (t - 1) * (dedekindZeta L t).re) (nhdsWithin 1 (Set.Ioi 1))
      (nhds (dedekindZeta_residue L)) := by
    have := (Complex.continuous_re.tendsto _).comp (tendsto_sub_one_mul_dedekindZeta_nhdsGT L)
    simpa [Function.comp_def] using this
  have hpos := dedekindZeta_residue_pos F
  have h1 : Filter.Tendsto (fun t : ℝ => ((t - 1) * (dedekindZeta F t).re) ^ 2 / ((2:ℝ) ^ S.card) ^ 2)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds ((dedekindZeta_residue F) ^ 2 / ((2:ℝ) ^ S.card) ^ 2)) :=
    (hFre.pow 2).div_const _
  have hlin : Filter.Tendsto (fun t : ℝ => t - 1) (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
    have h := ((Filter.tendsto_id (x := nhdsWithin (1:ℝ) (Set.Ioi 1))).mono_right nhdsWithin_le_nhds).sub_const (1:ℝ)
    rw [sub_self] at h
    exact h
  have h2 : Filter.Tendsto (fun t : ℝ => (t - 1) * ((t - 1) * (dedekindZeta L t).re))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
    simpa using hlin.mul hLre
  have hev : ∀ᶠ t : ℝ in nhdsWithin 1 (Set.Ioi 1),
      ((t - 1) * (dedekindZeta F t).re) ^ 2 / ((2:ℝ) ^ S.card) ^ 2 ≤ (t - 1) * ((t - 1) * (dedekindZeta L t).re) := by
    filter_upwards [self_mem_nhdsWithin, hFre.eventually_const_lt hpos] with t ht hpt
    have ht1 : (0:ℝ) < t - 1 := by simp at ht; linarith
    obtain ⟨X, hX0, hXF, hXL⟩ := key t ht
    have hF0 : 0 ≤ (dedekindZeta F t).re := by
      by_contra h
      have h' := not_le.mp h
      nlinarith
    have hsq : (dedekindZeta F t).re ^ 2 ≤ ((2:ℝ) ^ S.card) ^ 2 * (dedekindZeta L t).re := by
      calc (dedekindZeta F t).re ^ 2 ≤ (2 ^ S.card * X) ^ 2 := pow_le_pow_left₀ hF0 hXF 2
        _ = ((2:ℝ) ^ S.card) ^ 2 * X ^ 2 := by ring
        _ ≤ _ := by gcongr
    rw [div_le_iff₀ (by positivity)]
    calc ((t - 1) * (dedekindZeta F t).re) ^ 2 = (t - 1) ^ 2 * (dedekindZeta F t).re ^ 2 := by ring
      _ ≤ (t - 1) ^ 2 * (((2:ℝ) ^ S.card) ^ 2 * (dedekindZeta L t).re) := by gcongr
      _ = _ := by ring
  have := le_of_tendsto_of_tendsto h1 h2 hev
  have : 0 < (dedekindZeta_residue F) ^ 2 / ((2:ℝ) ^ S.card) ^ 2 := by positivity
  linarith

/-- **Squares are local–global over a number field** (proof of the input
`NFInputs.isSquare_iff_everywhere_nf`): $a \in F$ is a square in $F$ iff it is a square in every
completion $F_v$.

*Proof.* "Only if" is clear. For "if": $a = 0$ is a square; otherwise scale $a$ by a square
$d^2$ ($d \in \mathcal{O}_F$ a denominator) to get $a \in \mathcal{O}_F$. If $a$ were not a square, take
$L = F(\sqrt a)$ (`Lam.exists_quadExt`) and $S$ = the primes containing $2a$ (finite,
`NFLocal.finite_bad_places_nf`); every $\mathfrak{p} \notin S$ splits by
`exists_two_primes_of_isSquare`, contradicting `not_almost_all_split`. Only the finite places are
needed. -/
@[kb "omeara1963" "§65:15 [unverified]"]
theorem isSquare_iff_everywhere (a : F) :
    IsSquare a ↔ NFPlace.Everywhere (F := F) fun K _ _ => IsSquare (algebraMap F K a) := by
  constructor
  · rintro ⟨r, rfl⟩ v
    cases v with
    | infinite w => exact ⟨algebraMap F _ r, map_mul _ _ _⟩
    | finite v => exact ⟨algebraMap F _ r, map_mul _ _ _⟩
  · intro h
    by_contra hd
    have ha0 : a ≠ 0 := by rintro rfl; exact hd ⟨0, by simp⟩
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) a
    have hy0 : (y : F) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
    set b : 𝓞 F := x * y with hbdef
    have hb : (b : F) = algebraMap (𝓞 F) F x / algebraMap (𝓞 F) F y * (y : F) ^ 2 := by
      simp only [hbdef]
      push_cast
      change (x : F) * (y : F) = (x : F) / (y : F) * (y : F) ^ 2
      field_simp
    have hbd : ¬ IsSquare (b : F) := by
      rintro ⟨r, hr⟩
      apply hd
      refine ⟨r / y, ?_⟩
      have e : algebraMap (𝓞 F) F x / algebraMap (𝓞 F) F y
          = (algebraMap (𝓞 F) F x / algebraMap (𝓞 F) F y * (y : F) ^ 2) / ((y : F) * (y : F)) := by
        field_simp
      rw [e, ← hb, hr]
      field_simp
    have hb0 : b ≠ 0 := by
      intro h0
      apply hbd
      rw [h0]
      exact ⟨0, by simp⟩
    have hfin : {v : HeightOneSpectrum (𝓞 F) | 2 * b ∈ v.asIdeal}.Finite := by
      have h2 : (2 * b : 𝓞 F) ≠ 0 := mul_ne_zero two_ne_zero hb0
      have := Ideal.finite_factors (R := 𝓞 F) (I := Ideal.span {2 * b}) (by simpa using h2)
      convert this using 2 with v
      simp [Ideal.dvd_span_singleton]
    obtain ⟨L, _, _, _, s, hs, hspan⟩ := QuadFormsKB.Lam.exists_quadExt (b : F) hbd
    apply not_almost_all_split (b : F) hbd s hs hspan hfin.toFinset
    intro v hv
    have hv' : 2 * b ∉ v.asIdeal := by simpa using hv
    apply exists_two_primes_of_isSquare b hbd s hs hspan v hv'
    obtain ⟨t, ht⟩ := h (QuadFormsKB.NFPlace.finite v)
    refine ⟨t * algebraMap F (v.adicCompletion F) (y : F), ?_⟩
    rw [hb, map_mul, ht, map_pow]
    ring

end QuadFormsKB.SqLG
