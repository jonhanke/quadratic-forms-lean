/-
# O'Meara §71C: the ten-field construction, Proposition 71:15

O'Meara's ten-field construction (Propositions 71:15–71:17) proves the index statements 71:16 and 71:17 that his
proof of Hilbert's reciprocity law needs. The library proves the reciprocity law by the Weil index, and 71:16, 71:17
are derived from it in `Sec71BNorm.lean` (`mul_mem_principalNormIdeles`, `ideleSupportedAt_le_principalNormIdeles_iff`).
This file has Proposition 71:15 (O'Meara's proof: $\ell$ with $N\mathfrak p$ of even order modulo $\ell$, the Frobenius of $F(\zeta_\ell)/F$ at $\mathfrak p$, and the fixed field of its square).

**Proves**
* Lemma 71:14 (p. 197) is `infinite_setOf_even_orderOf` in `Sec71A.lean`;
* Proposition 71:15 (p. 197): `infinite_setOf_cyclotomic_localDegree_two`.
-/
import QuadFormsKB.Literature.OMeara.Sec71A

set_option linter.unusedSectionVars false

namespace QuadFormsKB.OMeara

/-- Lemma 71:14 in the form used below: `infinite_setOf_even_orderOf` (`Sec71A.lean`) says that $a$ has even
order modulo $p$, so every $n$ with $a^n \equiv 1 \pmod p$ is even. -/
theorem even_of_pow_modEq_one {a p n : ℕ} (hord : Even (orderOf (a : ZMod p))) (hn : a ^ n ≡ 1 [MOD p]) :
    Even n := by
  have h2 : (a : ZMod p) ^ n = 1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hn
    push_cast at this; simpa using this
  exact even_iff_two_dvd.mpr ((even_iff_two_dvd.mp hord).trans (orderOf_dvd_of_pow_eq_one h2))

/-! ### Auxiliary results for Proposition 71:15

Notation: $q = N\mathfrak p$, $L = F(\zeta_\ell)$, $G = \mathrm{Gal}(L/F)$. If $\ell \nmid q$ then $\ell \notin \mathfrak P$
for every prime $\mathfrak P$ of $L$ over $\mathfrak p$; the inertia group of $\mathfrak P$ is trivial, and the Frobenius
$\sigma \in G$ at $\mathfrak P$ is the automorphism $\zeta \mapsto \zeta^q$ (the same for all $\mathfrak P$ over
$\mathfrak p$). For $H = \langle \sigma^2 \rangle$ and $K = L^H$, comparing $e$ and $f$ in the tower $F \subset K \subset L$
shows that every prime of $K$ over $\mathfrak p$ has $e = 1$, $f = 2$ provided the order of $\sigma$ (the order of $q$
modulo $\ell$) is even. -/

section Prop7115Aux

set_option linter.style.haveILetI false

open NumberField IsDedekindDomain Polynomial

namespace Prop7115

section Aux
variable {S : Type*} [CommRing S] {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- If $\ell \notin Q$ and $\eta$ is a primitive $\ell$-th root of unity, then $1 - \eta \notin Q$
(since $1 - \eta \mid \Phi_\ell(1) = \ell$). -/
theorem one_sub_not_mem_of_primitiveRoot [IsDomain S] {η : S} (hη : IsPrimitiveRoot η ℓ) {Q : Ideal S}
    (hQ : (ℓ : S) ∉ Q) : 1 - η ∉ Q := by
  intro h
  apply hQ
  have h1 := Polynomial.sub_dvd_eval_sub 1 η (cyclotomic ℓ S)
  have hr : (cyclotomic ℓ S).eval η = 0 := hη.isRoot_cyclotomic hℓ.out.pos
  rw [eval_one_cyclotomic_prime, hr, sub_zero] at h1
  obtain ⟨c, hc⟩ := h1
  rw [hc]
  exact Q.mul_mem_right c h

/-- Two primitive $\ell$-th roots of unity that are congruent modulo $Q$ (with $\ell \notin Q$) are equal. -/
theorem eq_of_sub_mem_of_primitiveRoot [IsDomain S] {ζ ξ : S} (hζ : IsPrimitiveRoot ζ ℓ)
    (hξ : IsPrimitiveRoot ξ ℓ) {Q : Ideal S} (hQ : (ℓ : S) ∉ Q) (h : ξ - ζ ∈ Q) : ξ = ζ := by
  obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξ.pow_eq_one
  by_contra hne
  have hi0 : i ≠ 0 := by
    rintro rfl
    exact hξ.ne_one hℓ.out.one_lt (by simp)
  have hi1 : i ≠ 1 := by
    rintro rfl
    exact hne (by simp)
  have hcop : Nat.Coprime (i - 1) ℓ := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hℓ.out]
    intro hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  have hprim := hζ.pow_of_coprime (i - 1) hcop
  have hu : IsUnit ζ := hζ.isUnit hℓ.out.ne_zero
  have h2 : (ζ ^ (i - 1) - 1) * ζ ∈ Q := by
    have : (ζ ^ (i - 1) - 1) * ζ = ζ ^ i - ζ := by
      rw [sub_mul, one_mul, ← pow_succ]
      congr 2
      omega
    rw [this]; exact h
  have h3 : ζ ^ (i - 1) - 1 ∈ Q := (Ideal.mul_unit_mem_iff_mem Q hu).mp h2
  exact one_sub_not_mem_of_primitiveRoot hprim hQ (by simpa using Q.neg_mem h3)

end Aux

section Cyc
variable {F : Type} [Field F] [NumberField F] {ℓ : ℕ} [hℓ : Fact ℓ.Prime]
  {L : Type} [Field L] [NumberField L] [Algebra F L] [IsCyclotomicExtension {ℓ} F L] [IsGalois F L]

local instance : NeZero ℓ := ⟨hℓ.out.ne_zero⟩

/-- An automorphism of $F(\zeta)$ is determined by its value at $\zeta$. -/
theorem aut_ext {ζ : L} (hζ : IsPrimitiveRoot ζ ℓ) {σ τ : L ≃ₐ[F] L} (h : σ ζ = τ ζ) : σ = τ := by
  have : σ.toAlgHom = τ.toAlgHom := by
    apply (hζ.powerBasis F).algHom_ext
    simpa using h
  exact AlgEquiv.coe_toAlgHom_injective this

/-- The inertia group of a prime $Q$ of $L$ with $\ell \notin Q$ is trivial. -/
theorem inertia_eq_bot (Q : Ideal (𝓞 L)) (hQ : (ℓ : 𝓞 L) ∉ Q) :
    Q.inertia Gal(L/F) = ⊥ := by
  rw [eq_bot_iff]
  intro τ hτ
  have hζ := IsCyclotomicExtension.zeta_spec ℓ F L
  have hζ' := hζ.toInteger_isPrimitiveRoot
  have hξ : IsPrimitiveRoot (τ • hζ.toInteger) ℓ :=
    hζ'.map_of_injective (f := (MulSemiringAction.toRingEquiv Gal(L/F) (𝓞 L) τ).toMonoidHom)
      (MulSemiringAction.toRingEquiv Gal(L/F) (𝓞 L) τ).injective
  have h1 : τ • hζ.toInteger = hζ.toInteger :=
    eq_of_sub_mem_of_primitiveRoot hζ' hξ hQ (hτ hζ.toInteger)
  have h2 : τ (IsCyclotomicExtension.zeta ℓ F L) = IsCyclotomicExtension.zeta ℓ F L := by
    have := congrArg (fun x : 𝓞 L => (x : L)) h1
    exact this
  exact aut_ext hζ (by rw [h2]; simp)

/-- If $\ell \nmid N\mathfrak p$ and $Q$ lies over $\mathfrak p$, then $\ell \notin Q$. -/
theorem natCast_notMem_of_not_dvd (𝔭 : HeightOneSpectrum (𝓞 F))
    (hnd : ¬ ℓ ∣ Ideal.absNorm 𝔭.asIdeal) (Q : Ideal (𝓞 L))
    (hQ : Q.comap (algebraMap (𝓞 F) (𝓞 L)) = 𝔭.asIdeal) : (ℓ : 𝓞 L) ∉ Q := by
  intro h
  have h1 : (ℓ : 𝓞 F) ∈ 𝔭.asIdeal := by
    rw [← hQ, Ideal.mem_comap, map_natCast]; exact h
  have : 𝔭.asIdeal.IsMaximal := 𝔭.isMaximal
  letI := Ideal.Quotient.field 𝔭.asIdeal
  haveI : Finite (𝓞 F ⧸ 𝔭.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ 𝔭.ne_bot
  haveI := Fintype.ofFinite (𝓞 F ⧸ 𝔭.asIdeal)
  obtain ⟨p, hp⟩ := CharP.exists (𝓞 F ⧸ 𝔭.asIdeal)
  obtain ⟨n, hpp, hcard⟩ := FiniteField.card (𝓞 F ⧸ 𝔭.asIdeal) p
  have hp' : Fact p.Prime := ⟨hpp⟩
  have h2 : ((ℓ : 𝓞 F ⧸ 𝔭.asIdeal)) = 0 := by
    have := (Ideal.Quotient.eq_zero_iff_mem (I := 𝔭.asIdeal)).mpr h1
    simpa using this
  rw [CharP.cast_eq_zero_iff _ p] at h2
  have h3 : p = ℓ := (Nat.prime_dvd_prime_iff_eq hpp hℓ.out).mp h2
  apply hnd
  have h4 : Ideal.absNorm 𝔭.asIdeal = p ^ (n : ℕ) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]; exact hcard
  rw [h4, ← h3]
  exact dvd_pow_self _ n.ne_zero

/-- A Frobenius element at $Q$ sends $\zeta \mapsto \zeta^{N\mathfrak p}$. -/
theorem frob_zeta (𝔭 : HeightOneSpectrum (𝓞 F))
    (hnd : ¬ ℓ ∣ Ideal.absNorm 𝔭.asIdeal) (Q : Ideal (𝓞 L)) [Q.IsPrime]
    (hQ : Q.comap (algebraMap (𝓞 F) (𝓞 L)) = 𝔭.asIdeal) (σ : Gal(L/F))
    (hσ : IsArithFrobAt (𝓞 F) σ Q) :
    σ (IsCyclotomicExtension.zeta ℓ F L) =
      IsCyclotomicExtension.zeta ℓ F L ^ Ideal.absNorm 𝔭.asIdeal := by
  have hζ := IsCyclotomicExtension.zeta_spec ℓ F L
  have h1 := AlgHom.IsArithFrobAt.apply_of_pow_eq_one hσ (ζ := hζ.toInteger) (m := ℓ)
    hζ.toInteger_isPrimitiveRoot.pow_eq_one (natCast_notMem_of_not_dvd 𝔭 hnd Q hQ)
  have h2 : Nat.card (𝓞 F ⧸ Q.under (𝓞 F)) = Ideal.absNorm 𝔭.asIdeal := by
    have : Q.under (𝓞 F) = 𝔭.asIdeal := hQ
    rw [this, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [h2] at h1
  have := congrArg (fun x : 𝓞 L => (x : L)) h1
  exact this

/-- There is one automorphism $\sigma$ that is a Frobenius element at every prime of $L$ over $\mathfrak p$. -/
theorem exists_frob_aut (𝔭 : HeightOneSpectrum (𝓞 F))
    (hnd : ¬ ℓ ∣ Ideal.absNorm 𝔭.asIdeal) :
    ∃ σ : Gal(L/F), σ (IsCyclotomicExtension.zeta ℓ F L) =
        IsCyclotomicExtension.zeta ℓ F L ^ Ideal.absNorm 𝔭.asIdeal ∧
      ∀ Q : Ideal (𝓞 L), Q.IsPrime → Q.comap (algebraMap (𝓞 F) (𝓞 L)) = 𝔭.asIdeal →
        IsArithFrobAt (𝓞 F) σ Q := by
  have hζ := IsCyclotomicExtension.zeta_spec ℓ F L
  have key : ∀ Q : Ideal (𝓞 L), Q.IsPrime → Q.comap (algebraMap (𝓞 F) (𝓞 L)) = 𝔭.asIdeal →
      ∃ σ : Gal(L/F), IsArithFrobAt (𝓞 F) σ Q := by
    intro Q hQp hQ
    haveI : Q.LiesOver 𝔭.asIdeal := ⟨hQ.symm⟩
    have hne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q
    haveI : Finite (𝓞 L ⧸ Q) := Ideal.finiteQuotientOfFreeOfNeBot Q hne
    exact IsArithFrobAt.exists_of_isInvariant (𝓞 F) Gal(L/F) Q
  obtain ⟨⟨Q0, hQ0p, hQ0l⟩⟩ := 𝔭.asIdeal.nonempty_primesOver (S := 𝓞 L)
  obtain ⟨σ, hσ⟩ := key Q0 hQ0p hQ0l.over.symm
  refine ⟨σ, frob_zeta 𝔭 hnd Q0 hQ0l.over.symm σ hσ, ?_⟩
  intro Q hQp hQ
  obtain ⟨σ', hσ'⟩ := key Q hQp hQ
  have : σ' = σ := aut_ext hζ
    ((frob_zeta 𝔭 hnd Q hQ σ' hσ').trans (frob_zeta 𝔭 hnd Q0 hQ0l.over.symm σ hσ).symm)
  subst this
  exact hσ'

/-- For $\sigma\colon \zeta \mapsto \zeta^q$: $\sigma^n = 1$ iff $q^n \equiv 1 \pmod \ell$. -/
theorem pow_aut_eq_one_iff {σ : Gal(L/F)} {q : ℕ} (hq : 0 < q)
    (hσ : σ (IsCyclotomicExtension.zeta ℓ F L) = IsCyclotomicExtension.zeta ℓ F L ^ q) (n : ℕ) :
    σ ^ n = 1 ↔ q ^ n ≡ 1 [MOD ℓ] := by
  have hζ := IsCyclotomicExtension.zeta_spec ℓ F L
  set ζ := IsCyclotomicExtension.zeta ℓ F L
  have h1 : ∀ n : ℕ, (σ ^ n) ζ = ζ ^ (q ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, AlgEquiv.mul_apply, hσ, map_pow, ih, ← pow_mul, pow_succ]
  have hqn : 1 ≤ q ^ n := Nat.one_le_pow _ _ hq
  constructor
  · intro h
    have h2 : ζ ^ (q ^ n) = ζ := by rw [← h1 n, h]; rfl
    have h3 : ζ ^ (q ^ n - 1) = 1 := by
      have : ζ ^ (q ^ n - 1) * ζ = 1 * ζ := by
        rw [← pow_succ, Nat.sub_add_cancel hqn, h2, one_mul]
      exact mul_right_cancel₀ (hζ.ne_zero hℓ.out.ne_zero) this
    exact ((Nat.modEq_iff_dvd' hqn).mpr ((hζ.pow_eq_one_iff_dvd _).mp h3)).symm
  · intro h
    apply aut_ext hζ
    rw [h1]
    obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd' hqn).mp h.symm
    have : q ^ n = ℓ * c + 1 := by omega
    rw [this, pow_succ, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
    rfl

/-- $L/F$ is unramified at $\mathfrak p$ when $\ell \nmid N\mathfrak p$. -/
theorem ramificationIdx_eq_one (𝔭 : HeightOneSpectrum (𝓞 F))
    (hnd : ¬ ℓ ∣ Ideal.absNorm 𝔭.asIdeal) (Q : Ideal (𝓞 L)) [Q.IsPrime]
    (hQ : Q.comap (algebraMap (𝓞 F) (𝓞 L)) = 𝔭.asIdeal) :
    Q.ramificationIdx (𝓞 F) = 1 := by
  haveI : Q.LiesOver 𝔭.asIdeal := ⟨hQ.symm⟩
  have h1 := Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(L/F)) 𝔭.asIdeal Q
  rw [inertia_eq_bot Q (natCast_notMem_of_not_dvd 𝔭 hnd Q hQ),
    Ideal.ramificationIdxIn_eq_ramificationIdx 𝔭.asIdeal Q Gal(L/F)] at h1
  simpa using h1.symm

/-- The order of the Frobenius $\sigma$ divides the residue degree $f(Q \mid \mathfrak p)$. -/
theorem order_dvd_inertiaDeg (𝔭 : HeightOneSpectrum (𝓞 F))
    (hnd : ¬ ℓ ∣ Ideal.absNorm 𝔭.asIdeal) (Q : Ideal (𝓞 L)) [Q.IsPrime]
    (hQ : Q.comap (algebraMap (𝓞 F) (𝓞 L)) = 𝔭.asIdeal) {σ : Gal(L/F)}
    (hσ : σ (IsCyclotomicExtension.zeta ℓ F L) =
        IsCyclotomicExtension.zeta ℓ F L ^ Ideal.absNorm 𝔭.asIdeal) :
    orderOf σ ∣ Q.inertiaDeg (𝓞 F) := by
  haveI : Q.LiesOver 𝔭.asIdeal := ⟨hQ.symm⟩
  have hℓQ := natCast_notMem_of_not_dvd 𝔭 hnd Q hQ
  have hne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q
  have hmax : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne
  letI := Ideal.Quotient.field Q
  haveI : Finite (𝓞 L ⧸ Q) := Ideal.finiteQuotientOfFreeOfNeBot Q hne
  haveI := Fintype.ofFinite (𝓞 L ⧸ Q)
  have hζ := IsCyclotomicExtension.zeta_spec ℓ F L
  have hζ' := hζ.toInteger_isPrimitiveRoot
  have hcard : Fintype.card (𝓞 L ⧸ Q) = Ideal.absNorm 𝔭.asIdeal ^ Q.inertiaDeg (𝓞 F) := by
    rw [Ideal.absNorm_pow_inertiaDeg 𝔭.asIdeal Q, Ideal.absNorm_apply,
      Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hz1 : Ideal.Quotient.mk Q hζ.toInteger ≠ 1 := by
    intro h
    apply one_sub_not_mem_of_primitiveRoot hζ' hℓQ
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, h, sub_self]
  have hz0 : Ideal.Quotient.mk Q hζ.toInteger ≠ 0 := by
    intro h
    apply hz1
    have : IsUnit (Ideal.Quotient.mk Q hζ.toInteger) :=
      (hζ'.isUnit hℓ.out.ne_zero).map _
    exact absurd h this.ne_zero
  have hord : orderOf (Ideal.Quotient.mk Q hζ.toInteger) = ℓ := by
    apply orderOf_eq_prime _ hz1
    rw [← map_pow, hζ'.pow_eq_one, map_one]
  have h1 := FiniteField.pow_card_sub_one_eq_one _ hz0
  have h2 : ℓ ∣ Fintype.card (𝓞 L ⧸ Q) - 1 := hord ▸ orderOf_dvd_of_pow_eq_one h1
  have hpos : 0 < Ideal.absNorm 𝔭.asIdeal := by
    exact Nat.pos_of_ne_zero (fun h => 𝔭.ne_bot (Ideal.absNorm_eq_zero_iff.mp h))
  have h3 : Ideal.absNorm 𝔭.asIdeal ^ Q.inertiaDeg (𝓞 F) ≡ 1 [MOD ℓ] := by
    rw [← hcard]
    have : 1 ≤ Fintype.card (𝓞 L ⧸ Q) := Fintype.card_pos
    exact ((Nat.modEq_iff_dvd' this).mpr h2).symm
  exact orderOf_dvd_of_pow_eq_one ((pow_aut_eq_one_iff hpos hσ _).mpr h3)

/-- A prime of a number field has absolute norm at least $2$. -/
theorem one_lt_absNorm (𝔭 : HeightOneSpectrum (𝓞 F)) : 1 < Ideal.absNorm 𝔭.asIdeal := by
  have h0 : Ideal.absNorm 𝔭.asIdeal ≠ 0 := fun h => 𝔭.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  have h1 : Ideal.absNorm 𝔭.asIdeal ≠ 1 := fun h => 𝔭.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  omega

section Sub
variable [FiniteDimensional F L] (K : IntermediateField F L)

/-- If $\sigma^2$ fixes $\mathcal O_K$ and $\sigma$ is a Frobenius at the primes over $\mathfrak p$, then the residue
degree of a prime $P$ of $K$ over $\mathfrak p$ is at most $2$. -/
theorem inertiaDeg_le_two (𝔭 : HeightOneSpectrum (𝓞 F)) (σ : Gal(L/F))
    (hfrob : ∀ Q : Ideal (𝓞 L), Q.IsPrime → Q.comap (algebraMap (𝓞 F) (𝓞 L)) = 𝔭.asIdeal →
      IsArithFrobAt (𝓞 F) σ Q)
    (hfix : ∀ x : 𝓞 K, (σ ^ 2) • (algebraMap (𝓞 K) (𝓞 L) x) = algebraMap (𝓞 K) (𝓞 L) x)
    (P : Ideal (𝓞 K)) [P.IsPrime] (hP : P.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭.asIdeal) :
    P.inertiaDeg (𝓞 F) ≤ 2 := by
  have hPne : P ≠ ⊥ := by
    haveI : P.LiesOver 𝔭.asIdeal := ⟨hP.symm⟩
    exact Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P
  haveI : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hPne
  obtain ⟨⟨Q, hQp, hQl⟩⟩ := P.nonempty_primesOver (S := 𝓞 L)
  have hQP : Q.comap (algebraMap (𝓞 K) (𝓞 L)) = P := hQl.over.symm
  have hQ𝔭 : Q.comap (algebraMap (𝓞 F) (𝓞 L)) = 𝔭.asIdeal := by
    rw [IsScalarTower.algebraMap_eq (𝓞 F) (𝓞 K) (𝓞 L), ← Ideal.comap_comap, hQP, hP]
  have hF := hfrob Q hQp hQ𝔭
  have hq1 := one_lt_absNorm 𝔭
  set q := Ideal.absNorm 𝔭.asIdeal with hq
  have hcardF : Nat.card (𝓞 F ⧸ Q.under (𝓞 F)) = q := by
    have : Q.under (𝓞 F) = 𝔭.asIdeal := hQ𝔭
    rw [this, hq, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have e1 : ∀ y : 𝓞 L, Ideal.Quotient.mk Q (σ • y) = (Ideal.Quotient.mk Q y) ^ q := by
    intro y
    have := AlgHom.IsArithFrobAt.mk_apply hF y
    rwa [hcardF] at this
  have e2 : ∀ x : 𝓞 K, (Ideal.Quotient.mk Q (algebraMap (𝓞 K) (𝓞 L) x)) ^ (q * q) =
      Ideal.Quotient.mk Q (algebraMap (𝓞 K) (𝓞 L) x) := by
    intro x
    calc (Ideal.Quotient.mk Q (algebraMap (𝓞 K) (𝓞 L) x)) ^ (q * q)
        = ((Ideal.Quotient.mk Q (algebraMap (𝓞 K) (𝓞 L) x)) ^ q) ^ q := pow_mul _ _ _
      _ = (Ideal.Quotient.mk Q (σ • algebraMap (𝓞 K) (𝓞 L) x)) ^ q := by rw [e1]
      _ = Ideal.Quotient.mk Q (σ • σ • algebraMap (𝓞 K) (𝓞 L) x) := (e1 _).symm
      _ = Ideal.Quotient.mk Q ((σ ^ 2) • algebraMap (𝓞 K) (𝓞 L) x) := by
          rw [pow_two, mul_smul]
      _ = _ := by rw [hfix x]
  letI := Ideal.Quotient.field P
  haveI : Finite (𝓞 K ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hPne
  haveI := Fintype.ofFinite (𝓞 K ⧸ P)
  have hinj : Function.Injective (Ideal.quotientMap Q (algebraMap (𝓞 K) (𝓞 L))
      (le_of_eq hQP.symm)) := Ideal.quotientMap_injective' (le_of_eq hQP)
  have e3 : ∀ y : 𝓞 K ⧸ P, y ^ (q * q) = y := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    apply hinj
    rw [map_pow]
    simpa using e2 x
  have hcard : Fintype.card (𝓞 K ⧸ P) ≤ q * q := by
    have hq2 : 1 < q * q := by nlinarith
    have hdeg := FiniteField.X_pow_card_sub_X_natDegree_eq (𝓞 K ⧸ P) hq2
    have hne : (X ^ (q * q) - X : (𝓞 K ⧸ P)[X]) ≠ 0 := by
      intro h
      rw [h] at hdeg
      simp at hdeg
      omega
    have := Polynomial.card_le_degree_of_subset_roots (p := (X ^ (q * q) - X : (𝓞 K ⧸ P)[X]))
      (Z := Finset.univ) (by
        intro y _
        rw [Polynomial.mem_roots hne]
        simp [e3 y])
    rwa [hdeg] at this
  have hnorm : q ^ P.inertiaDeg (𝓞 F) = Nat.card (𝓞 K ⧸ P) := by
    haveI : P.LiesOver 𝔭.asIdeal := ⟨hP.symm⟩
    rw [hq, Ideal.absNorm_pow_inertiaDeg 𝔭.asIdeal P, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [Nat.card_eq_fintype_card] at hnorm
  have : q ^ P.inertiaDeg (𝓞 F) ≤ q ^ 2 := by rw [hnorm, pow_two]; exact hcard
  exact (Nat.pow_le_pow_iff_right hq1).mp this

/-- The residue degree of a prime of $L$ over a prime of $L^H$ is at most $|H|$. -/
theorem inertiaDeg_le_card (H : Subgroup Gal(L/F))
    (P : Ideal (𝓞 (FixedPoints.intermediateField H : IntermediateField F L))) [P.IsPrime]
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver P] :
    Q.inertiaDeg (𝓞 (FixedPoints.intermediateField H : IntermediateField F L)) ≤ Nat.card H := by
  haveI : NumberField (FixedPoints.intermediateField H : IntermediateField F L) :=
    NumberField.of_module_finite F _
  haveI : IsGaloisGroup H (FixedPoints.intermediateField H : IntermediateField F L) L :=
    IsGaloisGroup.subgroup Gal(L/F) F L H
  haveI : IsGaloisGroup H (𝓞 (FixedPoints.intermediateField H : IntermediateField F L)) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing H _ _ (FixedPoints.intermediateField H : IntermediateField F L) L
  haveI : Fintype (P.primesOver (𝓞 L)) := (Algebra.QuasiFinite.finite_primesOver P).fintype
  have h := Ideal.sum_ramification_inertia_eq_card (G := H) P (𝓞 L)
  calc Q.inertiaDeg (𝓞 (FixedPoints.intermediateField H : IntermediateField F L))
      ≤ Q.ramificationIdx (𝓞 (FixedPoints.intermediateField H : IntermediateField F L)) *
        Q.inertiaDeg (𝓞 (FixedPoints.intermediateField H : IntermediateField F L)) :=
        Nat.le_mul_of_pos_left _ (Q.ramificationIdx_pos _)
    _ ≤ _ := Finset.single_le_sum (f := fun q : P.primesOver (𝓞 L) =>
        q.1.ramificationIdx (𝓞 (FixedPoints.intermediateField H : IntermediateField F L)) *
        q.1.inertiaDeg (𝓞 (FixedPoints.intermediateField H : IntermediateField F L)))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨Q, inferInstance, inferInstance⟩ :
          P.primesOver (𝓞 L)))
    _ = Nat.card H := h

/-- **Core of Proposition 71:15.** If $\ell \nmid N\mathfrak p$ and $N\mathfrak p$ has even order modulo $\ell$, then
$L = F(\zeta_\ell)$ has a subfield $K$ in which every prime over $\mathfrak p$ has $e = 1$ and $f = 2$. -/
theorem exists_good_K (𝔭 : HeightOneSpectrum (𝓞 F))
    (hnd : ¬ ℓ ∣ Ideal.absNorm 𝔭.asIdeal)
    (hev : ∀ n : ℕ, Ideal.absNorm 𝔭.asIdeal ^ n ≡ 1 [MOD ℓ] → Even n) :
    ∃ K : IntermediateField F L, ∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ →
      P.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭.asIdeal →
        P.ramificationIdx (𝓞 F) = 1 ∧ P.inertiaDeg (𝓞 F) = 2 := by
  obtain ⟨σ, hσ, hfrob⟩ := exists_frob_aut (L := L) 𝔭 hnd
  have hq0 : 0 < Ideal.absNorm 𝔭.asIdeal := lt_trans Nat.zero_lt_one (one_lt_absNorm 𝔭)
  have hopos : 0 < orderOf σ := orderOf_pos σ
  have hoev : Even (orderOf σ) :=
    hev _ ((pow_aut_eq_one_iff hq0 hσ _).mp (pow_orderOf_eq_one σ))
  obtain ⟨m, hm⟩ := hoev
  set H : Subgroup Gal(L/F) := Subgroup.zpowers (σ ^ 2) with hH
  have hcardH : Nat.card H = m := by
    rw [hH, Nat.card_zpowers, orderOf_pow_of_dvd two_ne_zero ⟨m, by omega⟩]
    omega
  haveI : NumberField (FixedPoints.intermediateField H : IntermediateField F L) :=
    NumberField.of_module_finite F _
  haveI : IsGaloisGroup H (FixedPoints.intermediateField H : IntermediateField F L) L :=
    IsGaloisGroup.subgroup Gal(L/F) F L H
  refine ⟨FixedPoints.intermediateField H, ?_⟩
  intro P hPp hPne hP
  obtain ⟨⟨Q, hQp, hQl⟩⟩ := P.nonempty_primesOver (S := 𝓞 L)
  have hQP : Q.comap (algebraMap (𝓞 (FixedPoints.intermediateField H : IntermediateField F L))
      (𝓞 L)) = P := hQl.over.symm
  have hQ𝔭 : Q.comap (algebraMap (𝓞 F) (𝓞 L)) = 𝔭.asIdeal := by
    rw [IsScalarTower.algebraMap_eq (𝓞 F)
      (𝓞 (FixedPoints.intermediateField H : IntermediateField F L)) (𝓞 L),
      ← Ideal.comap_comap, hQP, hP]
  have hfix : ∀ x : 𝓞 (FixedPoints.intermediateField H : IntermediateField F L),
      (σ ^ 2) • (algebraMap _ (𝓞 L) x) = algebraMap _ (𝓞 L) x := by
    intro x
    apply Subtype.ext
    have h1 := x.1.2 ⟨σ ^ 2, Subgroup.mem_zpowers _⟩
    exact h1
  have he := ramificationIdx_eq_one 𝔭 hnd Q hQ𝔭
  have hf1 := inertiaDeg_le_two (FixedPoints.intermediateField H : IntermediateField F L) 𝔭 σ
    hfrob hfix P hP
  have hf2 := inertiaDeg_le_card H P Q
  have hf3 := order_dvd_inertiaDeg 𝔭 hnd Q hQ𝔭 hσ
  have hf4 := Ideal.inertiaDeg_tower (R := 𝓞 F) P Q
  have he2 := Ideal.ramificationIdx_below_dvd (R := 𝓞 F) P Q
  rw [he] at he2
  refine ⟨Nat.dvd_one.mp he2, ?_⟩
  have hapos := P.inertiaDeg_pos (𝓞 F)
  have hQpos := Q.inertiaDeg_pos (𝓞 F)
  have hle : orderOf σ ≤ Q.inertiaDeg (𝓞 F) := Nat.le_of_dvd hQpos hf3
  rw [hf4] at hle
  rw [hcardH] at hf2
  generalize P.inertiaDeg (𝓞 F) = a at *
  generalize Q.inertiaDeg (𝓞 (FixedPoints.intermediateField H : IntermediateField F L)) = b at *
  interval_cases a
  · omega
  · rfl

end Sub

end Cyc

end Prop7115

end Prop7115Aux

open NumberField IsDedekindDomain in
/-- **Proposition 71:15** (O'Meara 1963, p. 197): let $\mathfrak p$ be a discrete spot of the number field $F$. For
infinitely many prime numbers $\ell$ there is an $\ell$-cyclotomic extension $K/F$ which is unramified of local degree
$2$ at $\mathfrak p$: every prime $\mathfrak P$ of $K$ over $\mathfrak p$ has ramification index
$e(\mathfrak P \mid \mathfrak p) = 1$ and residue degree $f(\mathfrak P \mid \mathfrak p) = 2$ (so
$[K_\mathfrak P : F_\mathfrak p] = 2$). -/
@[kb "omeara1963" "§71C, 71:15, p. 197"]
theorem infinite_setOf_cyclotomic_localDegree_two {F : Type} [Field F] [NumberField F]
    (𝔭 : HeightOneSpectrum (𝓞 F)) :
    {ℓ : ℕ | ℓ.Prime ∧ ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra F K),
      IsMCyclotomic ℓ F K ∧ ∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ →
        P.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭.asIdeal →
          P.ramificationIdx (𝓞 F) = 1 ∧ P.inertiaDeg (𝓞 F) = 2}.Infinite := by
  refine (infinite_setOf_even_orderOf _ (Prop7115.one_lt_absNorm 𝔭)).mono ?_
  rintro ℓ ⟨hℓ, hnd, hord⟩
  have hev : ∀ n : ℕ, Ideal.absNorm 𝔭.asIdeal ^ n ≡ 1 [MOD ℓ] → Even n := fun n hn =>
    even_of_pow_modEq_one hord hn
  refine ⟨hℓ, ?_⟩
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have : FiniteDimensional F (CyclotomicField ℓ F) :=
    IsCyclotomicExtension.finiteDimensional {ℓ} F _
  have : NumberField (CyclotomicField ℓ F) := NumberField.of_module_finite F _
  have : IsGalois F (CyclotomicField ℓ F) := IsCyclotomicExtension.isGalois {ℓ} F _
  obtain ⟨K, hK⟩ := Prop7115.exists_good_K (L := CyclotomicField ℓ F) 𝔭 hnd hev
  have : NumberField K := NumberField.of_module_finite F _
  exact ⟨K, inferInstance, inferInstance, inferInstance,
    ⟨CyclotomicField ℓ F, inferInstance, inferInstance, (haveI : NeZero ((ℓ : ℕ) : F) := ⟨Nat.cast_ne_zero.mpr hℓ.ne_zero⟩; exists_isAbsCyclotomic),
      ⟨K.val⟩⟩, hK⟩

end QuadFormsKB.OMeara
