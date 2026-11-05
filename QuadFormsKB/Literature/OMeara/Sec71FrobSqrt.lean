/-
# O'Meara §71B: Formula 71:10, the Frobenius automorphisms on square roots

**Setting** (as in `Sec71Frob.lean`): $F$ is a number field, $m > 1$, $K = F(\zeta)$ with $\zeta$ a primitive $m$-th
root of unity, $S$ the set of discrete spots $\mathfrak p$ of $F$ with $m \notin \mathfrak p$, $\sigma_\mathfrak p$ the
Frobenius automorphism (`frobCyc`) and $\sigma_\alpha = \prod_{\mathfrak p \in S}\sigma_\mathfrak p^{\operatorname{ord}_\mathfrak p
\alpha}$ (`frobProd`).

**Proves** Formula 71:10 (`frobProd_sqrt`): for $\beta \in \dot F$ with $\sqrt\beta \in K$,
$\sigma_\alpha(\sqrt\beta) = \sqrt\beta\prod_{\mathfrak p \in S}\left(\frac{\alpha,\beta}{\mathfrak p}\right)$.

**Proof** (O'Meara's, p. 194). It is enough that
$\sigma_\mathfrak p^{\operatorname{ord}_\mathfrak p\alpha}\sqrt\beta = \left(\frac{\alpha,\beta}{\mathfrak p}\right)\sqrt\beta$
for $\mathfrak p \in S$ (`Formula7110.sign_frobCyc_zpow`, phrased with the sign character
$\tau \mapsto \tau\sqrt\beta/\sqrt\beta$, `Formula7110.signHom`). If $\beta$ is a square in $F$ both sides are $1$.
Otherwise put $E = F(\sqrt\beta) \subseteq K$, a quadratic extension with discriminant class $\beta$
(`Formula7110.exists_relD_eq`).
* $K/F$ is unramified at $\mathfrak p$ (`ramificationIdx_eq_one`: the inertia group is trivial because distinct
  $m$-th roots of unity stay distinct modulo a prime not containing $m$), hence so is $E/F$.
* If $\sigma_\mathfrak p\sqrt\beta = \sqrt\beta$, then $\sigma_\mathfrak p$ fixes $E$ and the residue degree of $E/F$ at
  $\mathfrak p$ is $1$ (`inertiaDeg_eq_one_of_fix`), so $\mathfrak p$ splits in $E$, $\beta$ is a square in
  $F_\mathfrak p$ and the symbol is $1$.
* Conversely, if a prime of $E$ over $\mathfrak p$ has residue degree $1$, then the Frobenius of $K/E$ at a prime of $K$
  above it sends $\zeta$ to $\zeta^{N\mathfrak p}$, so it is $\sigma_\mathfrak p$, and $\sigma_\mathfrak p$ fixes $E$
  (`fix_of_inertiaDeg_eq_one`; this is O'Meara's "$\sqrt\beta$ is not in the fixed field of $\sigma_\mathfrak P$").
  So if $\sigma_\mathfrak p\sqrt\beta = -\sqrt\beta$ then $\mathfrak p$ is inert in $E$, $E_\mathfrak P/F_\mathfrak p$ is
  unramified quadratic, and $\left(\frac{\alpha,\beta}{\mathfrak p}\right) = (-1)^{\operatorname{ord}_\mathfrak p\alpha}$
  (Examples 63:10 and 63:16; here `Binary.Rel.genusSym_inert_iff`).

*Update:* the formula holds for every $\alpha \in \dot F$; O'Meara's hypothesis that $\alpha$ is integral at the spots of
$S$ (which he uses to define $\sigma_\alpha$ within the Galois group by nonnegative powers) is not needed, since
$\sigma_\mathfrak p^{k}$ makes sense for $k < 0$ in the group $\mathfrak G(K/F)$.
-/
import QuadFormsKB.Literature.OMeara.Sec71Frob
import QuadFormsKB.Binary.RelGenusExact

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

namespace QuadFormsKB.OMeara

namespace Formula7110

/-- An $m$-th root of unity congruent to $1$ modulo an ideal not containing $m$ is $1$
(since $(1 - \eta)\sum_{j<m}\eta^j = 1 - \eta^m = 0$ and $\sum_{j<m}\eta^j \equiv m$). -/
theorem eq_one_of_sub_one_mem {S : Type*} [CommRing S] [IsDomain S] {m : ℕ} {η : S} (hη : η ^ m = 1)
    {Q : Ideal S} (hQ : (m : S) ∉ Q) (h : η - 1 ∈ Q) : η = 1 := by
  by_contra hne
  have h1 : (∑ j ∈ Finset.range m, η ^ j) = 0 := by
    have := mul_neg_geom_sum η m
    rw [hη, sub_self] at this
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h).symm hne
    · exact h
  apply hQ
  have h2 : (∑ j ∈ Finset.range m, (η ^ j - 1)) ∈ Q := Q.sum_mem fun j _ => by
    rw [← mul_geom_sum η j]
    exact Q.mul_mem_right _ h
  rw [Finset.sum_sub_distrib, h1, Finset.sum_const, Finset.card_range, zero_sub, nsmul_one] at h2
  simpa using Q.neg_mem h2

variable {F : Type} [Field F] [NumberField F] {K : Type} [Field K] [NumberField K] [Algebra F K] {m : ℕ}
  {ζ : K}

/-- An automorphism of $F(\zeta)/F$ is determined by its value at $\zeta$. -/
theorem aut_ext (hK : IntermediateField.adjoin F {ζ} = ⊤) {σ τ : K ≃ₐ[F] K} (h : σ ζ = τ ζ) : σ = τ := by
  have hint : IsIntegral F ζ := Algebra.IsIntegral.isIntegral ζ
  have hS : Algebra.adjoin F {ζ} = ⊤ := by
    have := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic
    rw [← this, hK]; rfl
  have hle : Algebra.adjoin F {ζ} ≤ AlgHom.equalizer σ.toAlgHom τ.toAlgHom :=
    Algebra.adjoin_le (by simpa using h)
  rw [hS] at hle
  exact AlgEquiv.ext fun x => hle (Algebra.mem_top (x := x))

theorem frobCyc_apply (hζ : IsPrimitiveRoot ζ m) (hK : IntermediateField.adjoin F {ζ} = ⊤)
    (𝔭 : HeightOneSpectrum (𝓞 F)) (hm : (m : 𝓞 F) ∉ 𝔭.asIdeal) :
    frobCyc hζ hK 𝔭 ζ = ζ ^ Ideal.absNorm 𝔭.asIdeal := by
  unfold frobCyc
  rw [dif_pos hm]
  exact (existsUnique_frobCyc hζ hK 𝔭 hm).exists.choose_spec

theorem frobCyc_of_mem (hζ : IsPrimitiveRoot ζ m) (hK : IntermediateField.adjoin F {ζ} = ⊤)
    (𝔭 : HeightOneSpectrum (𝓞 F)) (hm : (m : 𝓞 F) ∈ 𝔭.asIdeal) : frobCyc hζ hK 𝔭 = 1 := by
  unfold frobCyc
  rw [dif_neg (not_not.mpr hm)]

theorem natCast_notMem (𝔭 : HeightOneSpectrum (𝓞 F)) (hm : (m : 𝓞 F) ∉ 𝔭.asIdeal) (Q : Ideal (𝓞 K))
    (hQ : Q.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭.asIdeal) : (m : 𝓞 K) ∉ Q := by
  intro h
  apply hm
  rw [← hQ, Ideal.mem_comap, map_natCast]
  exact h

theorem ne_zero_of_notMem (𝔭 : HeightOneSpectrum (𝓞 F)) (hm : (m : 𝓞 F) ∉ 𝔭.asIdeal) : m ≠ 0 := by
  rintro rfl
  exact hm (by simp)

/-- **$\sigma_\mathfrak p$ is the arithmetic Frobenius at every prime of $K$ over $\mathfrak p$.** -/
theorem isArithFrobAt_frobCyc (hζ : IsPrimitiveRoot ζ m) (hK : IntermediateField.adjoin F {ζ} = ⊤)
    [IsGalois F K] (𝔭 : HeightOneSpectrum (𝓞 F)) (hm : (m : 𝓞 F) ∉ 𝔭.asIdeal) (Q : Ideal (𝓞 K)) [Q.IsPrime]
    (hQ : Q.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭.asIdeal) :
    IsArithFrobAt (𝓞 F) (frobCyc hζ hK 𝔭) Q := by
  have hm0 := ne_zero_of_notMem 𝔭 hm
  haveI : NeZero m := ⟨hm0⟩
  haveI : Q.LiesOver 𝔭.asIdeal := ⟨hQ.symm⟩
  have hne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q
  haveI : Finite (𝓞 K ⧸ Q) := Ideal.finiteQuotientOfFreeOfNeBot Q hne
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 F) Gal(K/F) Q
  let ζB : 𝓞 K := ⟨ζ, hζ.isIntegral (Nat.pos_of_ne_zero hm0)⟩
  have h1 := AlgHom.IsArithFrobAt.apply_of_pow_eq_one hσ (ζ := ζB) (m := m)
    (Subtype.ext hζ.pow_eq_one) (natCast_notMem 𝔭 hm Q hQ)
  have h2 : Nat.card (𝓞 F ⧸ Q.under (𝓞 F)) = Ideal.absNorm 𝔭.asIdeal := by
    have : Q.under (𝓞 F) = 𝔭.asIdeal := hQ
    rw [this, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [h2] at h1
  have h3 : σ ζ = ζ ^ Ideal.absNorm 𝔭.asIdeal := congrArg (fun x : 𝓞 K => (x : K)) h1
  have : σ = frobCyc hζ hK 𝔭 := aut_ext hK (h3.trans (frobCyc_apply hζ hK 𝔭 hm).symm)
  rw [← this]
  exact hσ

/-- **$K/F$ is unramified at the spots of $S$** (O'Meara 1963, §71A, p. 192, by Corollary 32:6a): for a prime $Q$ of
$K = F(\zeta)$ over a discrete spot $\mathfrak p$ at which $m$ is a unit, $e(Q \mid \mathfrak p) = 1$. The inertia group
of $Q$ is trivial, because distinct $m$-th roots of unity stay distinct modulo $Q$. -/
@[kb "omeara1963" "§71A, p. 192 (an absolute m-cyclotomic extension is unramified at the discrete spots where m is a unit)"]
theorem ramificationIdx_eq_one (hζ : IsPrimitiveRoot ζ m) (hK : IntermediateField.adjoin F {ζ} = ⊤)
    (𝔭 : HeightOneSpectrum (𝓞 F)) (hm : (m : 𝓞 F) ∉ 𝔭.asIdeal) (Q : Ideal (𝓞 K)) [Q.IsPrime]
    (hQ : Q.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭.asIdeal) :
    Q.ramificationIdx (𝓞 F) = 1 := by
  have hm0 := ne_zero_of_notMem 𝔭 hm
  haveI : NeZero m := ⟨hm0⟩
  haveI : IsCyclotomicExtension {m} F K := (haveI : NeZero m := ⟨hm0⟩
    isAbsCyclotomic_iff_isCyclotomicExtension (m := m) (F := F) (K := K)).mp ⟨ζ, hζ, hK⟩
  haveI : IsGalois F K := IsCyclotomicExtension.isGalois {m} F K
  haveI : Q.LiesOver 𝔭.asIdeal := ⟨hQ.symm⟩
  have hinert : Q.inertia Gal(K/F) = ⊥ := by
    rw [eq_bot_iff]
    intro τ hτ
    let ζB : 𝓞 K := ⟨ζ, hζ.isIntegral (Nat.pos_of_ne_zero hm0)⟩
    have hζB : ζB ^ m = 1 := Subtype.ext hζ.pow_eq_one
    have hinv : ζB * ζB ^ (m - 1) = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0), hζB]
    set η : 𝓞 K := (τ • ζB) * ζB ^ (m - 1) with hη
    have hτm : (τ • ζB) ^ m = 1 := by rw [← smul_pow', hζB, smul_one]
    have hηm : η ^ m = 1 := by
      rw [hη, mul_pow, hτm, one_mul, ← pow_mul, mul_comm, pow_mul, hζB, one_pow]
    have hη1 : η - 1 ∈ Q := by
      have : η - 1 = (τ • ζB - ζB) * ζB ^ (m - 1) := by
        rw [hη, sub_mul, hinv]
      rw [this]
      exact Q.mul_mem_right _ (hτ ζB)
    have hη' := eq_one_of_sub_one_mem hηm (natCast_notMem 𝔭 hm Q hQ) hη1
    have hfix : τ • ζB = ζB := by
      calc τ • ζB = (τ • ζB) * (ζB ^ (m - 1) * ζB) := by
            rw [mul_comm (ζB ^ (m - 1)), hinv, mul_one]
        _ = η * ζB := by rw [hη, mul_assoc]
        _ = ζB := by rw [hη', one_mul]
    have h2 : τ ζ = ζ := congrArg (fun x : 𝓞 K => (x : K)) hfix
    exact aut_ext hK (by rw [h2]; rfl)
  have h1 := Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(K/F)) 𝔭.asIdeal Q
  rw [hinert, Ideal.ramificationIdxIn_eq_ramificationIdx 𝔭.asIdeal Q Gal(K/F)] at h1
  simpa using h1.symm

section Sub

variable [IsGalois F K] (E : IntermediateField F K) [NumberField E]

/-- A prime of $\mathcal O_K$ over a prime of $\mathcal O_E$ over $\mathfrak p$ lies over $\mathfrak p$. -/
theorem comap_eq_of_liesOver (𝔭 : HeightOneSpectrum (𝓞 F)) (P : Ideal (𝓞 E))
    (hP : P.comap (algebraMap (𝓞 F) (𝓞 E)) = 𝔭.asIdeal) (Q : Ideal (𝓞 K)) [Q.LiesOver P] :
    Q.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭.asIdeal := by
  rw [IsScalarTower.algebraMap_eq (𝓞 F) (𝓞 E) (𝓞 K), ← Ideal.comap_comap, ← hP, Ideal.over_def Q P]

/-- **$E/F$ is unramified at the spots of $S$** (O'Meara 1963, §71A, p. 192): for an intermediate field
$F \subseteq E \subseteq K = F(\zeta)$ (an $m$-cyclotomic extension) and a prime $P$ of $E$ over a discrete spot
$\mathfrak p$ at which $m$ is a unit, $e(P \mid \mathfrak p) = 1$. -/
@[kb "omeara1963" "§71A, p. 192 (an m-cyclotomic extension is unramified at the discrete spots where m is a unit)"]
theorem ramificationIdx_sub_eq_one (hζ : IsPrimitiveRoot ζ m) (hK : IntermediateField.adjoin F {ζ} = ⊤)
    (𝔭 : HeightOneSpectrum (𝓞 F)) (hm : (m : 𝓞 F) ∉ 𝔭.asIdeal) (P : Ideal (𝓞 E)) [P.IsPrime]
    (hP : P.comap (algebraMap (𝓞 F) (𝓞 E)) = 𝔭.asIdeal) :
    P.ramificationIdx (𝓞 F) = 1 := by
  obtain ⟨⟨Q, hQp, hQl⟩⟩ := P.nonempty_primesOver (S := 𝓞 K)
  have hQ𝔭 := comap_eq_of_liesOver E 𝔭 P hP Q
  have h := Ideal.ramificationIdx_below_dvd (R := 𝓞 F) P Q
  rw [ramificationIdx_eq_one hζ hK 𝔭 hm Q hQ𝔭] at h
  exact Nat.dvd_one.mp h

/-- **Residue degree $1$ when $\sigma_\mathfrak p$ fixes $E$:** then every residue class of $\mathcal O_E$ modulo a
prime over $\mathfrak p$ satisfies $x^{N\mathfrak p} = x$. -/
theorem inertiaDeg_eq_one_of_fix (hζ : IsPrimitiveRoot ζ m) (hK : IntermediateField.adjoin F {ζ} = ⊤)
    (𝔭 : HeightOneSpectrum (𝓞 F)) (hm : (m : 𝓞 F) ∉ 𝔭.asIdeal)
    (hfix : ∀ y : E, frobCyc hζ hK 𝔭 (y : K) = y) (P : Ideal (𝓞 E)) [P.IsPrime]
    (hP : P.comap (algebraMap (𝓞 F) (𝓞 E)) = 𝔭.asIdeal) :
    P.inertiaDeg (𝓞 F) = 1 := by
  have hPne : P ≠ ⊥ := by
    haveI : P.LiesOver 𝔭.asIdeal := ⟨hP.symm⟩
    exact Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P
  haveI : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hPne
  obtain ⟨⟨Q, hQp, hQl⟩⟩ := P.nonempty_primesOver (S := 𝓞 K)
  have hQP : Q.comap (algebraMap (𝓞 E) (𝓞 K)) = P := hQl.over.symm
  have hQ𝔭 := comap_eq_of_liesOver E 𝔭 P hP Q
  have hF := isArithFrobAt_frobCyc hζ hK 𝔭 hm Q hQ𝔭
  have hq1 : 1 < Ideal.absNorm 𝔭.asIdeal := by
    have h0 : Ideal.absNorm 𝔭.asIdeal ≠ 0 := fun h => 𝔭.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
    have h1 : Ideal.absNorm 𝔭.asIdeal ≠ 1 := fun h => 𝔭.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
    omega
  set q := Ideal.absNorm 𝔭.asIdeal with hq
  have hcardF : Nat.card (𝓞 F ⧸ Q.under (𝓞 F)) = q := by
    have : Q.under (𝓞 F) = 𝔭.asIdeal := hQ𝔭
    rw [this, hq, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hfix' : ∀ x : 𝓞 E, (frobCyc hζ hK 𝔭) • (algebraMap (𝓞 E) (𝓞 K) x) = algebraMap (𝓞 E) (𝓞 K) x := by
    intro x
    apply Subtype.ext
    exact hfix (x : E)
  have e2 : ∀ x : 𝓞 E, (Ideal.Quotient.mk Q (algebraMap (𝓞 E) (𝓞 K) x)) ^ q =
      Ideal.Quotient.mk Q (algebraMap (𝓞 E) (𝓞 K) x) := by
    intro x
    have e1 : Ideal.Quotient.mk Q ((frobCyc hζ hK 𝔭) • (algebraMap (𝓞 E) (𝓞 K) x)) =
        (Ideal.Quotient.mk Q (algebraMap (𝓞 E) (𝓞 K) x)) ^ q := by
      have := AlgHom.IsArithFrobAt.mk_apply hF (algebraMap (𝓞 E) (𝓞 K) x)
      rwa [hcardF] at this
    rw [hfix' x] at e1
    exact e1.symm
  letI := Ideal.Quotient.field P
  haveI : Finite (𝓞 E ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hPne
  haveI := Fintype.ofFinite (𝓞 E ⧸ P)
  have hinj : Function.Injective (Ideal.quotientMap Q (algebraMap (𝓞 E) (𝓞 K))
      (le_of_eq hQP.symm)) := Ideal.quotientMap_injective' (le_of_eq hQP)
  have e3 : ∀ y : 𝓞 E ⧸ P, y ^ q = y := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    apply hinj
    rw [map_pow]
    simpa using e2 x
  have hcard : Fintype.card (𝓞 E ⧸ P) ≤ q := by
    have hdeg := FiniteField.X_pow_card_sub_X_natDegree_eq (𝓞 E ⧸ P) hq1
    have hne : (Polynomial.X ^ q - Polynomial.X : Polynomial (𝓞 E ⧸ P)) ≠ 0 := by
      intro h
      rw [h] at hdeg
      simp at hdeg
      omega
    have := Polynomial.card_le_degree_of_subset_roots
      (p := (Polynomial.X ^ q - Polynomial.X : Polynomial (𝓞 E ⧸ P)))
      (Z := Finset.univ) (by
        intro y _
        rw [Polynomial.mem_roots hne]
        simp [e3 y])
    rwa [hdeg] at this
  have hnorm : q ^ P.inertiaDeg (𝓞 F) = Nat.card (𝓞 E ⧸ P) := by
    haveI : P.LiesOver 𝔭.asIdeal := ⟨hP.symm⟩
    rw [hq, Ideal.absNorm_pow_inertiaDeg 𝔭.asIdeal P, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [Nat.card_eq_fintype_card] at hnorm
  have h1 : q ^ P.inertiaDeg (𝓞 F) ≤ q ^ 1 := by rw [hnorm, pow_one]; exact hcard
  have h2 := (Nat.pow_le_pow_iff_right hq1).mp h1
  have h3 := P.inertiaDeg_pos (𝓞 F)
  omega

/-- **$\sigma_\mathfrak p$ fixes $E$ when the residue degree is $1$:** the Frobenius automorphism of $K/E$ at a prime
of $K$ over a prime $P$ of $E$ with $f(P \mid \mathfrak p) = 1$ sends $\zeta$ to $\zeta^{N\mathfrak p}$, so it is
$\sigma_\mathfrak p$ (`aut_ext`). -/
theorem fix_of_inertiaDeg_eq_one (hζ : IsPrimitiveRoot ζ m) (hK : IntermediateField.adjoin F {ζ} = ⊤)
    (𝔭 : HeightOneSpectrum (𝓞 F)) (hm : (m : 𝓞 F) ∉ 𝔭.asIdeal) (P : Ideal (𝓞 E)) [P.IsPrime]
    (hP : P.comap (algebraMap (𝓞 F) (𝓞 E)) = 𝔭.asIdeal) (hf : P.inertiaDeg (𝓞 F) = 1) (y : E) :
    frobCyc hζ hK 𝔭 (y : K) = y := by
  have hm0 := ne_zero_of_notMem 𝔭 hm
  haveI : NeZero m := ⟨hm0⟩
  have hPne : P ≠ ⊥ := by
    haveI : P.LiesOver 𝔭.asIdeal := ⟨hP.symm⟩
    exact Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P
  obtain ⟨⟨Q, hQp, hQl⟩⟩ := P.nonempty_primesOver (S := 𝓞 K)
  have hQP : Q.comap (algebraMap (𝓞 E) (𝓞 K)) = P := hQl.over.symm
  have hQ𝔭 := comap_eq_of_liesOver E 𝔭 P hP Q
  have hQne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hPne Q
  haveI : Finite (𝓞 K ⧸ Q) := Ideal.finiteQuotientOfFreeOfNeBot Q hQne
  haveI : IsGalois E K := IsGalois.tower_top_of_isGalois F E K
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 E) Gal(K/E) Q
  let ζB : 𝓞 K := ⟨ζ, hζ.isIntegral (Nat.pos_of_ne_zero hm0)⟩
  have h1 := AlgHom.IsArithFrobAt.apply_of_pow_eq_one hσ (ζ := ζB) (m := m)
    (Subtype.ext hζ.pow_eq_one) (natCast_notMem 𝔭 hm Q hQ𝔭)
  have h2 : Nat.card (𝓞 E ⧸ Q.under (𝓞 E)) = Ideal.absNorm 𝔭.asIdeal := by
    have hU : Q.under (𝓞 E) = P := hQP
    haveI : P.LiesOver 𝔭.asIdeal := ⟨hP.symm⟩
    rw [hU, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply,
      ← Ideal.absNorm_pow_inertiaDeg 𝔭.asIdeal P, hf, pow_one]
  rw [h2] at h1
  have h3 : σ ζ = ζ ^ Ideal.absNorm 𝔭.asIdeal := congrArg (fun x : 𝓞 K => (x : K)) h1
  have : σ.restrictScalars F = frobCyc hζ hK 𝔭 :=
    aut_ext hK (h3.trans (frobCyc_apply hζ hK 𝔭 hm).symm)
  rw [← this]
  exact σ.commutes y

end Sub

/-! ### The sign of an automorphism on $\sqrt\beta$ -/

section Sign

variable {β : F} {s : K}

/-- An automorphism sends $\sqrt\beta$ to $\pm\sqrt\beta$. -/
theorem sq_cases {L : Type*} [Field L] [Algebra F L] {t : L} (ht : t ^ 2 = algebraMap F L β) (τ : L ≃ₐ[F] L) :
    τ t = t ∨ τ t = -t := by
  have : (τ t) ^ 2 = t ^ 2 := by rw [← map_pow, ht, AlgEquiv.commutes]
  exact sq_eq_sq_iff_eq_or_eq_neg.mp this

theorem ne_zero_of_sq (hβ : β ≠ 0) (hs : s ^ 2 = algebraMap F K β) : s ≠ 0 := by
  rintro rfl
  apply hβ
  have : algebraMap F K β = 0 := by rw [← hs]; ring
  exact (map_eq_zero _).mp this

theorem ne_neg_self (hβ : β ≠ 0) (hs : s ^ 2 = algebraMap F K β) : s ≠ -s := by
  intro h
  have : (2 : K) * s = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h2 | h2
  · exact two_ne_zero h2
  · exact ne_zero_of_sq hβ hs h2

open scoped Classical in
/-- The sign $\tau\sqrt\beta/\sqrt\beta \in \{\pm 1\}$ of $\tau \in \mathfrak G(K/F)$. -/
def sign (s : K) (τ : K ≃ₐ[F] K) : ℤˣ := if τ s = s then 1 else -1

theorem sign_spec (hs : s ^ 2 = algebraMap F K β) (τ : K ≃ₐ[F] K) : ((sign s τ : ℤ) : K) * s = τ s := by
  unfold sign
  split_ifs with h
  · simp [h]
  · rcases sq_cases hs τ with h' | h'
    · exact absurd h' h
    · simp [h']

theorem sign_unique (hβ : β ≠ 0) (hs : s ^ 2 = algebraMap F K β) (τ : K ≃ₐ[F] K) (u : ℤˣ)
    (h : ((u : ℤ) : K) * s = τ s) : sign s τ = u := by
  rw [← sign_spec hs τ] at h
  have h' := mul_right_cancel₀ (ne_zero_of_sq hβ hs) h
  exact Units.ext (Int.cast_injective h').symm

/-- The sign as a homomorphism $\mathfrak G(K/F) \to \{\pm 1\}$. -/
def signHom (hβ : β ≠ 0) (hs : s ^ 2 = algebraMap F K β) : (K ≃ₐ[F] K) →* ℤˣ where
  toFun := sign s
  map_one' := sign_unique hβ hs 1 1 (by simp)
  map_mul' τ τ' := by
    apply sign_unique hβ hs
    rw [AlgEquiv.mul_apply, ← sign_spec hs τ', map_mul, map_intCast, ← sign_spec hs τ]
    push_cast
    ring

end Sign

/-- $(a, b)_\mathfrak p = 1$ if $b$ is a square in $F_\mathfrak p$. -/
theorem hilbert_eq_one_of_isSquare (𝔭 : HeightOneSpectrum (𝓞 F)) (a b : F)
    (h : IsSquare (algebraMap F (𝔭.adicCompletion F) b)) : (NFPlace.finite 𝔭).hilbert a b = 1 := by
  obtain ⟨c, hc⟩ := h
  simp only [NFPlace.hilbert, hilbertSymbol]
  rw [if_pos ⟨0, 1, c, by simp, by rw [hc]; ring⟩]

theorem hilbert_comm' (𝔭 : HeightOneSpectrum (𝓞 F)) (a b : F) :
    (NFPlace.finite 𝔭).hilbert a b = (NFPlace.finite 𝔭).hilbert b a :=
  hilbertSymbol_comm _ _ _

/-- **$E = F(\sqrt\beta)$ has $\delta = c^2\beta$** for the library's $\delta$ (`Binary.Rel.relD`) of $E/F$. -/
theorem exists_relD_eq {β : F} {E : Type} [Field E] [NumberField E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] (hβ : ¬ IsSquare β) {t : E} (ht : t ^ 2 = algebraMap F E β) :
    ∃ c : F, c ≠ 0 ∧ Binary.Rel.relD F E = c ^ 2 * β := by
  have hct : Binary.Rel.conj F E t = -t := by
    rcases sq_cases ht (Binary.Rel.conj F E) with h | h
    · obtain ⟨a, ha⟩ := (Binary.Rel.conj_eq_self_iff t).mp h
      exact absurd ⟨a, (algebraMap F E).injective (by rw [map_mul, ha, ← ht]; ring)⟩ hβ
    · exact h
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hβ ⟨0, (algebraMap F E).injective (by rw [← ht]; simp)⟩
  obtain ⟨c, hc⟩ := (Binary.Rel.conj_eq_self_iff ((Binary.Rel.relGen F E : E) / t)).mp (by
    rw [map_div₀, Binary.Rel.conj_relGen, hct, neg_div_neg_eq])
  refine ⟨c, ?_, (algebraMap F E).injective ?_⟩
  · rintro rfl
    rw [map_zero, eq_comm, div_eq_zero_iff] at hc
    exact hc.elim Binary.Rel.relGen_ne_zero ht0
  · rw [Binary.Rel.algebraMap_relD, map_mul, map_pow, hc, ← ht, div_pow]
    field_simp

/-- **The local step of Formula 71:10** (O'Meara 1963, p. 194): for $\mathfrak p \in S$,
$\sigma_\mathfrak p^{\operatorname{ord}_\mathfrak p\alpha}\sqrt\beta = \left(\frac{\alpha,\beta}{\mathfrak p}\right)
\sqrt\beta$, in terms of the sign `signHom`. -/
theorem sign_frobCyc_zpow (hζ : IsPrimitiveRoot ζ m) (hK : IntermediateField.adjoin F {ζ} = ⊤)
    (𝔭 : HeightOneSpectrum (𝓞 F)) (hm : (m : 𝓞 F) ∉ 𝔭.asIdeal) (α β : Fˣ) {s : K}
    (hs : s ^ 2 = algebraMap F K β) :
    ((signHom β.ne_zero hs (frobCyc hζ hK 𝔭 ^ ordAt 𝔭 α) : ℤˣ) : ℤ) = (NFPlace.finite 𝔭).hilbert α β := by
  have hm0 := ne_zero_of_notMem 𝔭 hm
  haveI : NeZero m := ⟨hm0⟩
  haveI : IsCyclotomicExtension {m} F K := (haveI : NeZero m := ⟨hm0⟩
    isAbsCyclotomic_iff_isCyclotomicExtension (m := m) (F := F) (K := K)).mp ⟨ζ, hζ, hK⟩
  haveI : IsGalois F K := IsCyclotomicExtension.isGalois {m} F K
  set σ := frobCyc hζ hK 𝔭
  rw [map_zpow]
  by_cases hsq : IsSquare (β : F)
  · -- $\beta$ is a square in $F$: every automorphism fixes $\sqrt\beta$
    obtain ⟨c, hc⟩ := hsq
    have hfix : ∀ τ : K ≃ₐ[F] K, signHom β.ne_zero hs τ = 1 := by
      intro τ
      apply sign_unique β.ne_zero hs
      have : (s - algebraMap F K c) * (s + algebraMap F K c) = 0 := by
        have h := hs
        rw [hc, map_mul] at h
        linear_combination h
      rcases mul_eq_zero.mp this with h | h
      · rw [sub_eq_zero.mp h, AlgEquiv.commutes]; simp
      · rw [eq_neg_of_add_eq_zero_left h, map_neg, AlgEquiv.commutes]; simp
    rw [hfix, one_zpow, Units.val_one, hilbert_eq_one_of_isSquare]
    exact ⟨algebraMap F _ c, by rw [hc, map_mul]⟩
  -- $E = F(\sqrt\beta)$ is quadratic
  set E := IntermediateField.adjoin F {s} with hE
  have hint : IsIntegral F s := Algebra.IsIntegral.isIntegral s
  have hnotF : s ∉ (⊥ : IntermediateField F K) := by
    rintro ⟨c, hc⟩
    change algebraMap F K c = s at hc
    exact hsq ⟨c, (algebraMap F K).injective (by rw [map_mul, ← sq, hc]; exact hs.symm)⟩
  have hdeg : Module.finrank F E = 2 := by
    have hle : Module.finrank F E ≤ 2 := by
      rw [IntermediateField.adjoin.finrank hint]
      have hp : (Polynomial.X ^ 2 - Polynomial.C (β : F)).natDegree = 2 := by
        rw [Polynomial.natDegree_sub_C, Polynomial.natDegree_X_pow]
      rw [← hp]
      apply Polynomial.natDegree_le_natDegree
      apply minpoly.degree_le_of_ne_zero F s (Polynomial.X_pow_sub_C_ne_zero (by norm_num) _)
      simp [hs]
    have hne1 : Module.finrank F E ≠ 1 := by
      intro h1
      rw [IntermediateField.finrank_eq_one_iff] at h1
      apply hnotF
      rw [← h1]
      exact IntermediateField.mem_adjoin_simple_self F s
    have hpos : 0 < Module.finrank F E := Module.finrank_pos
    omega
  haveI : Algebra.IsQuadraticExtension F E := ⟨hdeg⟩
  set t : E := ⟨s, IntermediateField.mem_adjoin_simple_self F s⟩
  have ht : t ^ 2 = algebraMap F E β := Subtype.ext hs
  obtain ⟨c, hc0, hrel⟩ := exists_relD_eq hsq ht
  -- $(\alpha,\beta)_\mathfrak p = \psi_\mathfrak p(\alpha)$
  have hgenus : (NFPlace.finite 𝔭).hilbert α β = Binary.Rel.genusSym E (NFPlace.finite 𝔭) α := by
    unfold Binary.Rel.genusSym
    rw [hrel, hilbert_comm' 𝔭 _ (α : F), NFPlace.hilbert_mul_right _ α.ne_zero (pow_ne_zero 2 hc0) β.ne_zero,
      hilbert_eq_one_of_isSquare 𝔭 _ (c ^ 2), one_mul]
    exact ⟨algebraMap F _ c, by rw [map_pow, sq]⟩
  rw [hgenus]
  -- primes of $E$ over $\mathfrak p$
  have hcomap : ∀ P : 𝔭.asIdeal.primesOver (𝓞 E), P.1.comap (algebraMap (𝓞 F) (𝓞 E)) = 𝔭.asIdeal :=
    fun P => (P.2.2.over).symm
  have he : ∀ P : 𝔭.asIdeal.primesOver (𝓞 E), P.1.ramificationIdx (𝓞 F) = 1 := fun P => by
    haveI := P.2.1
    exact ramificationIdx_sub_eq_one E hζ hK 𝔭 hm P.1 (hcomap P)
  have hfixE : σ s = s → ∀ y : E, σ (y : K) = y := by
    intro h y
    have hS : E.toSubalgebra = Algebra.adjoin F {s} :=
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic
    have hle : Algebra.adjoin F {s} ≤ AlgHom.equalizer σ.toAlgHom (AlgHom.id F K) :=
      Algebra.adjoin_le (by simpa using h)
    rw [← hS] at hle
    exact hle y.2
  rcases sq_cases hs σ with hσ | hσ
  · -- $\sigma_\mathfrak p$ fixes $\sqrt\beta$: $\mathfrak p$ splits, $\delta$ is a local square
    have hsign : signHom β.ne_zero hs σ = 1 := sign_unique β.ne_zero hs σ 1 (by simp [hσ])
    have hf : ∀ P : 𝔭.asIdeal.primesOver (𝓞 E), P.1.inertiaDeg (𝓞 F) = 1 := fun P => by
      haveI := P.2.1
      exact inertiaDeg_eq_one_of_fix E hζ hK 𝔭 hm (hfixE hσ) P.1 (hcomap P)
    have hsplit : Binary.Rel.relChar E 𝔭 = 1 := by
      rcases Binary.Rel.splitting hdeg 𝔭 with ⟨h, -⟩ | ⟨-, P₀, -, -, hf2⟩ | ⟨-, P₀, -, he2, -⟩
      · exact h
      · rw [hf P₀] at hf2; omega
      · rw [he P₀] at he2; omega
    rw [hsign, one_zpow, Units.val_one]
    unfold Binary.Rel.genusSym
    rw [hilbert_comm', hilbert_eq_one_of_isSquare]
    exact Binary.Rel.isSquare_relD_of_split hsplit
  · -- $\sigma_\mathfrak p\sqrt\beta = -\sqrt\beta$: $\mathfrak p$ is inert
    have hsne := ne_neg_self β.ne_zero hs
    have hsign : signHom β.ne_zero hs σ = -1 := sign_unique β.ne_zero hs σ (-1) (by simp [hσ])
    have hf : ∀ P : 𝔭.asIdeal.primesOver (𝓞 E), P.1.inertiaDeg (𝓞 F) ≠ 1 := fun P h1 => by
      haveI := P.2.1
      have := fix_of_inertiaDeg_eq_one E hζ hK 𝔭 hm P.1 (hcomap P) h1 t
      exact hsne (this.symm.trans hσ)
    have hinert : Binary.Rel.relChar E 𝔭 = -1 := by
      rcases Binary.Rel.splitting hdeg 𝔭 with ⟨-, P₀, -, -, -, -, hf1, -⟩ | ⟨h, -⟩ | ⟨-, P₀, -, -, hf1⟩
      · exact absurd hf1 (hf P₀)
      · exact h
      · exact absurd hf1 (hf P₀)
    have hv := SqDual.valuation_eq_exp_ordL 𝔭 α
    have hiff := Binary.Rel.genusSym_inert_iff hinert α.ne_zero hv
    rw [hsign]
    unfold ordAt
    rcases Int.even_or_odd (SqDual.ordL 𝔭 α) with hev | hodd
    · rw [hiff.mpr hev, hev.neg.neg_one_zpow, Units.val_one]
    · rcases Binary.Rel.genusSym_eq_one_or (E := E) (NFPlace.finite 𝔭) α with h1 | h1
      · exact absurd (hiff.mp h1) (Int.not_even_iff_odd.mpr hodd)
      · rw [h1, hodd.neg.neg_one_zpow, Units.val_neg, Units.val_one]

end Formula7110

open Formula7110

variable {F : Type} [Field F] [NumberField F] {K : Type} [Field K] [NumberField K] [Algebra F K] {m : ℕ}
  {ζ : K}

open scoped Classical in
/-- **Formula 71:10** (O'Meara 1963, §71B, p. 193): let $K = F(\zeta)$ with $\zeta$ a primitive $m$-th root of unity,
$m > 1$, and let $\beta \in \dot F$ have a square root $\sqrt\beta$ (`s`) in $K$. Then
$$\sigma_\alpha(\sqrt\beta) = \sqrt\beta\prod_{\mathfrak p \in S}\left(\frac{\alpha,\beta}{\mathfrak p}\right),$$
with $S$ the set of discrete spots at which $m$ is a unit and $\left(\frac{\alpha,\beta}{\mathfrak p}\right)$ the Hilbert
symbol at $\mathfrak p$ (`NFPlace.hilbert`; it is $1$ for almost all $\mathfrak p$, so the product is finite).

*Update:* stated for every $\alpha \in \dot F$; O'Meara defines $\sigma_\alpha$ only for $\alpha$ integral at the spots
of $S$, but negative powers $\sigma_\mathfrak p^{\operatorname{ord}_\mathfrak p\alpha}$ make sense in the group
$\mathfrak G(K/F)$, and the formula and its proof are unchanged. -/
@[kb "omeara1963" "§71B, 71:10, p. 193"]
theorem frobProd_sqrt (hζ : IsPrimitiveRoot ζ m) (hm1 : 1 < m) (hK : IntermediateField.adjoin F {ζ} = ⊤)
    (α β : Fˣ) {s : K} (hs : s ^ 2 = algebraMap F K β) :
    frobProd hζ hm1 hK α s =
      s * ∏ᶠ (𝔭 : HeightOneSpectrum (𝓞 F)) (_ : (m : 𝓞 F) ∉ 𝔭.asIdeal), ((NFPlace.finite 𝔭).hilbert α β : K) := by
  have : IsCyclotomicExtension {m} F K := (haveI : NeZero m := ⟨by omega⟩
    isAbsCyclotomic_iff_isCyclotomicExtension (m := m) (F := F) (K := K)).mp ⟨ζ, hζ, hK⟩
  letI : CommGroup (K ≃ₐ[F] K) :=
    { (inferInstance : Group (K ≃ₐ[F] K)) with
      mul_comm := fun a b => (IsCyclotomicExtension.isMulCommutative {m} F K).is_comm.comm a b }
  unfold frobProd
  change (∏ᶠ (𝔭 : HeightOneSpectrum (𝓞 F)) (_ : (m : 𝓞 F) ∉ 𝔭.asIdeal), frobCyc hζ hK 𝔭 ^ ordAt 𝔭 α) s = _
  have h1 : (∏ᶠ (𝔭 : HeightOneSpectrum (𝓞 F)) (_ : (m : 𝓞 F) ∉ 𝔭.asIdeal),
      frobCyc hζ hK 𝔭 ^ ordAt 𝔭 α) = ∏ᶠ 𝔭 : HeightOneSpectrum (𝓞 F), frobCyc hζ hK 𝔭 ^ ordAt 𝔭 α := by
    refine finprod_congr fun v => ?_
    by_cases hv : (m : 𝓞 F) ∈ v.asIdeal
    · rw [frobCyc_of_mem hζ hK v hv, one_zpow]
      simp [hv]
    · simp [hv]
  rw [h1]
  have hfin : Function.HasFiniteMulSupport fun 𝔭 : HeightOneSpectrum (𝓞 F) => frobCyc hζ hK 𝔭 ^ ordAt 𝔭 α := by
    refine Set.Finite.subset (SqDual.finite_ordL_ne_zero α) ?_
    intro v hv hz
    apply hv
    simp only [Function.mem_mulSupport, ordAt] at *
    rw [hz, neg_zero, zpow_zero]
  set χ := signHom β.ne_zero hs
  set ψ : (K ≃ₐ[F] K) →* K := ((Int.castRingHom K : ℤ →+* K) : ℤ →* K).comp ((Units.coeHom ℤ).comp χ)
  have hψ : ∀ τ, τ s = ψ τ * s := fun τ => (sign_spec hs τ).symm
  rw [hψ, MonoidHom.map_finprod ψ hfin, mul_comm]
  congr 1
  refine finprod_congr fun v => ?_
  rw [finprod_eq_if]
  split_ifs with hv
  · rw [frobCyc_of_mem hζ hK v hv, one_zpow, map_one]
  · change ((((χ (frobCyc hζ hK v ^ ordAt v α)) : ℤˣ) : ℤ) : K) = _
    rw [sign_frobCyc_zpow hζ hK v hv α β hs]

end QuadFormsKB.OMeara
