import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Binary.RelGenusCount
import QuadFormsKB.Literature.LocalGlobal.NumberFieldMain

/-!
# The exact number of genera of binary lattices over $F$

$E/F$ quadratic, $\delta$ = `relD`, $\psi_v = (\delta, \cdot)_v$ = `genusSym`. Previously proved: The genus of a normalized lattice
$(\mathfrak A, \frac{\eta}{a}N)$ is its vector $(\psi_v(\eta a))_v$, supported (CM, totally positive) on $S = \{\mathfrak p \mid 2\delta\}$ with
product one, so there are at most $2^{|S|-1}$ genera (`ncard_genera_le`). Here:

* **Inert primes, every residue characteristic** (`genusSym_inert_iff`): if $\mathfrak p$ is inert in $E$ then
  $\psi_\mathfrak p(x) = 1 \iff v_\mathfrak p(x)$ is even. *Proof (global, by density):* if $x = u^2 - \delta w^2$ in $F_\mathfrak p$, approximate
  $u, w$ by $u', w' \in F$ (`HeightOneSpectrum.denseRange_algebraMap`); then $x' = u'^2 - \delta w'^2 = N_{E/F}(u' + w'\theta)$ has
  $v_\mathfrak p(x') = v_\mathfrak p(x)$, and $v_\mathfrak p$ of a global norm is even at an inert prime (`even_count_relNorm_of_inert`, ideal
  norms). Conversely $\psi_\mathfrak p$ is a character with $\psi_\mathfrak p(\varpi) = -1$. No local field theory of $E_\mathfrak P$, no
  Hensel, works at dyadic $\mathfrak p$.
* **Norm ideals** (`exists_relNorm_eq`): a nonzero ideal $I$ of $\mathcal O_F$ is $N_{E/F}\mathfrak A$ iff $v_\mathfrak p(I)$ is even at
  every inert $\mathfrak p$ (the "if" direction is what is used; split and ramified primes are norms of a prime with $f = 1$).
* **Split / non-split** (`isSquare_relD_of_split`, `not_isSquare_relD_of_not_split`, every residue characteristic):
  $\delta \in F_\mathfrak p^{\times2}$ iff $\mathfrak p$ splits (from `HN.isSquare_of_ef_one`, `HN.two_primes_of_isSquare` of the Hasse norm
  theorem development); so $\psi_\mathfrak p \equiv 1$ at split $\mathfrak p$ and $\psi_\mathfrak p$ is nontrivial at inert and ramified
  $\mathfrak p$ (`exists_hilbertSymbol_neg`, local nondegeneracy).
* **The exact count** (`ncard_genera_eq`, CM): the genus vectors of the totally positive definite normalized lattices
  are exactly the sign vectors on the set $T$ of **ramified** finite primes with product one (`mem_genusVectors_iff`);
  there are $2^{|T|-1}$ of them ($1$ if $T = \emptyset$). Existence is by elements with prescribed Hilbert symbols
  (`NFInputs.exists_prescribed_hilbert_nf`, now proved). $T \subseteq \{\mathfrak p \mid 2\delta\}$ (`two_relD_mem_of_ramified`).

No unit index enters: the lattices range over **all** units $\eta$ with $\eta a \gg 0$. (The genera met with one fixed scale,
e.g. only $\eta = 1$, can be fewer; that count involves $[\mathcal O_F^{\times,+} : \mathcal O_F^{\times,+} \cap N(E^\times)]$ and is not formalized.)

Sources: Hecke, *Vorlesungen*, §48 [unverified]; O'Meara §§63, 65, 71:19; Serre, *Course*, Ch. III.
-/

open NumberField Module IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Binary.Rel

open LocalDensity

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

/-! ### Inert primes: $\psi_\mathfrak p$ is the parity of $v_\mathfrak p$ -/

/-- **Local norms are approximated by global norms:** if $\psi_\mathfrak p(x) = 1$ ($x \ne 0$) then some $z \in E^\times$ has
$v_\mathfrak p(N_{E/F}z) = v_\mathfrak p(x)$. -/
theorem exists_norm_valuation_eq {𝔭 : HeightOneSpectrum (𝓞 F)} {x : F} (hx : x ≠ 0)
    (h : genusSym E (NFPlace.finite 𝔭) x = 1) :
    ∃ z : E, z ≠ 0 ∧ 𝔭.valuation F (Algebra.norm F z) = 𝔭.valuation F x := by
  obtain ⟨u, w, huw⟩ := (genusSym_eq_one_iff (E := E) (NFPlace.finite 𝔭) x).mp h
  have hf : Continuous (fun p : 𝔭.adicCompletion F × 𝔭.adicCompletion F =>
      p.1 ^ 2 - algebraMap F (𝔭.adicCompletion F) (relD F E) * p.2 ^ 2) := by fun_prop
  have hxK : Valued.v (algebraMap F (𝔭.adicCompletion F) x) ≠ 0 := by
    rw [HN.valued_algebraMap]; exact (Valuation.ne_zero_iff _).mpr hx
  have hU := hf.continuousAt (x := (u, w)) |>.preimage_mem_nhds
    (show {y | Valued.v y = Valued.v (algebraMap F (𝔭.adicCompletion F) x)} ∈ nhds (u ^ 2 -
      algebraMap F (𝔭.adicCompletion F) (relD F E) * w ^ 2) from by
      rw [← huw]; exact Valued.locally_const hxK)
  have hd : DenseRange (Prod.map (algebraMap F (𝔭.adicCompletion F)) (algebraMap F (𝔭.adicCompletion F))) :=
    (HeightOneSpectrum.denseRange_algebraMap F 𝔭).prodMap (HeightOneSpectrum.denseRange_algebraMap F 𝔭)
  obtain ⟨_, h1, ⟨⟨s, t⟩, rfl⟩⟩ := mem_closure_iff_nhds.mp (hd (u, w)) _ hU
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Prod.map] at h1
  have heq := h1
  rw [← map_pow, ← map_pow, ← map_mul, ← map_sub, HN.valued_algebraMap, HN.valued_algebraMap] at heq
  refine ⟨algebraMap F E s + algebraMap F E t * (relGen F E : E), ?_, ?_⟩
  · intro h0
    have := norm_add_mul_relGen (E := E) s t
    rw [h0, Algebra.norm_zero] at this
    rw [← this, map_zero] at heq
    exact hx ((Valuation.zero_iff _).mp heq.symm)
  · rw [norm_add_mul_relGen]; exact heq

/-- $v_\mathfrak p(\nu) = \exp(-v)$ with $v$ = `Siegel.ordNF` = the multiplicity of $\mathfrak p$ in $(\nu)$, for $\nu \in \mathcal O_F \setminus 0$. -/
theorem valuation_algebraMap_eq_count (𝔭 : HeightOneSpectrum (𝓞 F)) {ν : 𝓞 F} (hν : ν ≠ 0) :
    𝔭.valuation F (algebraMap (𝓞 F) F ν) = WithZero.exp (-(Multiset.count 𝔭.asIdeal
      (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {ν})) : ℤ)) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap, count_normalizedFactors_span_eq_ordNF 𝔭 hν]
  exact HeightOneSpectrum.intValuation_if_neg 𝔭 hν

/-- **At an inert prime, global norms have even valuation:** $\chi_{E/F}(\mathfrak p) = -1$, $z \in E^\times$ $\Rightarrow$
$v_\mathfrak p(N_{E/F}z) = \exp(2k)$ for some $k \in \mathbb Z$. -/
theorem valuation_norm_even {𝔭 : HeightOneSpectrum (𝓞 F)} (h𝔭 : relChar E 𝔭 = -1) {z : E} (hz : z ≠ 0) :
    ∃ k : ℤ, 𝔭.valuation F (Algebra.norm F z) = WithZero.exp (2 * k) := by
  -- integral case
  have hint : ∀ α : 𝓞 E, α ≠ 0 → ∃ k : ℕ, 𝔭.valuation F (Algebra.norm F (algebraMap (𝓞 E) E α)) =
      WithZero.exp (-(2 * k : ℤ)) := by
    intro α hα
    have hN : Algebra.intNorm (𝓞 F) (𝓞 E) α ≠ 0 := by
      rw [Ne, Algebra.intNorm_eq_zero]; exact hα
    have hev := even_count_relNorm_of_inert h𝔭 (𝔄 := Ideal.span {α}) (by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact hα)
    rw [Ideal.relNorm_singleton] at hev
    obtain ⟨k, hk⟩ := hev
    refine ⟨k, ?_⟩
    rw [← Algebra.algebraMap_intNorm (A := 𝓞 F), valuation_algebraMap_eq_count 𝔭 hN, hk]
    push_cast; ring_nf
  obtain ⟨α, β, hβ, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) z
  have hβ0 : β ≠ 0 := nonZeroDivisors.ne_zero hβ
  have hα0 : α ≠ 0 := by
    rintro rfl; simp at hz
  obtain ⟨a, ha⟩ := hint α hα0
  obtain ⟨b, hb⟩ := hint β hβ0
  have hβE : algebraMap (𝓞 E) E β ≠ 0 := (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr hβ0
  have hmul : Algebra.norm F (algebraMap (𝓞 E) E α / algebraMap (𝓞 E) E β) *
      Algebra.norm F (algebraMap (𝓞 E) E β) = Algebra.norm F (algebraMap (𝓞 E) E α) := by
    rw [← map_mul, div_mul_cancel₀ _ hβE]
  have hv := congrArg (𝔭.valuation F) hmul
  rw [map_mul, ha, hb] at hv
  refine ⟨(b : ℤ) - a, ?_⟩
  have hne : WithZero.exp (-(2 * (b : ℕ) : ℤ)) ≠ 0 := WithZero.exp_ne_zero
  rw [← eq_div_iff hne, ← WithZero.exp_sub] at hv
  rw [hv]; congr 1; ring

/-- **The genus character at an inert prime is the parity of the valuation** (every inert $\mathfrak p$, dyadic included):
for $x \in F^\times$ with $v_\mathfrak p(x) = \exp(n)$, $\psi_\mathfrak p(x) = 1 \iff n$ is even. -/
@[kb "omeara1963" "§63B, 63:11a, p. 165; 63:3, 63:4, p. 161; serre1973 Ch. III §1.2 (Thm. 1, case F = Q_p); 63:16, p. 169"]
theorem genusSym_inert_iff {𝔭 : HeightOneSpectrum (𝓞 F)} (h𝔭 : relChar E 𝔭 = -1) {x : F} (hx : x ≠ 0)
    {n : ℤ} (hn : 𝔭.valuation F x = WithZero.exp n) :
    genusSym E (NFPlace.finite 𝔭) x = 1 ↔ Even n := by
  -- ψ = 1 ⇒ even
  have key : ∀ y : F, y ≠ 0 → ∀ m : ℤ, 𝔭.valuation F y = WithZero.exp m →
      genusSym E (NFPlace.finite 𝔭) y = 1 → Even m := by
    intro y hy m hm h1
    obtain ⟨z, hz, hzv⟩ := exists_norm_valuation_eq hy h1
    obtain ⟨k, hk⟩ := valuation_norm_even h𝔭 hz
    rw [hzv, hm] at hk
    exact ⟨k, by rw [WithZero.exp_injective hk]; ring⟩
  refine ⟨key x hx n hn, fun hev => ?_⟩
  -- a uniformizer has ψ = -1
  set π : F := algebraMap (𝓞 F) F (NF.unif 𝔭)
  have hπv : 𝔭.valuation F π = WithZero.exp (-1) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap, NF.intValuation_unif]
  have hπ0 : π ≠ 0 := by
    intro h; rw [h, map_zero] at hπv; exact WithZero.exp_ne_zero hπv.symm
  have hπψ : genusSym E (NFPlace.finite 𝔭) π = -1 := by
    rcases genusSym_eq_one_or (E := E) (NFPlace.finite 𝔭) π with h | h
    · exact absurd (key π hπ0 (-1) hπv h) (by decide)
    · exact h
  rcases genusSym_eq_one_or (E := E) (NFPlace.finite 𝔭) x with h | h
  · exact h
  · exfalso
    have hxπ : genusSym E (NFPlace.finite 𝔭) (x * π) = 1 := by
      rw [genusSym_mul _ hx hπ0, h, hπψ]; norm_num
    have := key (x * π) (mul_ne_zero hx hπ0) (n + -1) (by rw [map_mul, hn, hπv, ← WithZero.exp_add]) hxπ
    obtain ⟨j, hj⟩ := hev
    obtain ⟨i, hi⟩ := this
    omega

/-! ### Norm ideals -/

/-- **Ideals with even valuation at the inert primes are relative norms:** a nonzero ideal $I$ of $\mathcal O_F$ with
$v_\mathfrak p(I)$ even at every inert $\mathfrak p$ is $N_{E/F}\mathfrak A$ for an ideal $\mathfrak A$ of $\mathcal O_E$. (A split or ramified $\mathfrak p$ is
$N\mathfrak P$ for a prime $\mathfrak P$ over it with $f = 1$; an inert one has $N(\mathfrak p\mathcal O_E) = \mathfrak p^2$.) -/
@[kb "neukirch1999" "Ch. I §8 [unverified]"]
theorem exists_relNorm_eq {I : Ideal (𝓞 F)} (hI : I ≠ ⊥)
    (hev : ∀ 𝔭 : HeightOneSpectrum (𝓞 F), relChar E 𝔭 = -1 →
      Even (Multiset.count 𝔭.asIdeal (UniqueFactorizationMonoid.normalizedFactors I))) :
    ∃ 𝔄 : Ideal (𝓞 E), Ideal.relNorm (𝓞 F) 𝔄 = I := by
  classical
  set M := MonoidHom.mrange ((Ideal.relNorm (𝓞 F) : Ideal (𝓞 E) →*₀ Ideal (𝓞 F)) : Ideal (𝓞 E) →* Ideal (𝓞 F))
  suffices hM : I ∈ M by
    obtain ⟨𝔄, h⟩ := MonoidHom.mem_mrange.mp hM; exact ⟨𝔄, h⟩
  rw [← Ideal.prod_normalizedFactors_eq_self hI, Finset.prod_multiset_count]
  refine Submonoid.prod_mem _ (fun q hq => ?_)
  rw [Multiset.mem_toFinset] at hq
  have hqp : Prime q := UniqueFactorizationMonoid.prime_of_normalized_factor q hq
  have hq0 : q ≠ ⊥ := hqp.ne_zero
  set 𝔭 : HeightOneSpectrum (𝓞 F) := ⟨q, (Ideal.prime_iff_isPrime hq0).mp hqp, hq0⟩
  have : 𝔭.asIdeal.IsMaximal := 𝔭.isMaximal
  have hnorm : ∀ P : 𝔭.asIdeal.primesOver (𝓞 E),
      Ideal.relNorm (𝓞 F) P.1 = q ^ P.1.inertiaDeg (𝓞 F) := by
    intro P
    have := isMaximal_of_primesOver P
    have : P.1.LiesOver 𝔭.asIdeal := P.2.2
    exact Ideal.relNorm_eq_pow_of_isMaximal P.1 𝔭.asIdeal
  rcases splitting (Algebra.IsQuadraticExtension.finrank_eq_two F E) 𝔭 with
    ⟨-, P₀, -, -, -, -, hf, -, -⟩ | ⟨h, P₀, -, -, hf⟩ | ⟨-, P₀, -, -, hf⟩
  · refine MonoidHom.mem_mrange.mpr ⟨P₀.1 ^ Multiset.count q (UniqueFactorizationMonoid.normalizedFactors I), ?_⟩
    simp only [MonoidHom.coe_ofClass, map_pow]
    rw [hnorm, hf, pow_one]
  · obtain ⟨j, hj⟩ := hev 𝔭 h
    refine MonoidHom.mem_mrange.mpr ⟨P₀.1 ^ j, ?_⟩
    simp only [MonoidHom.coe_ofClass, map_pow]
    rw [hnorm, hf, ← pow_mul]
    change q ^ (2 * j) = q ^ Multiset.count 𝔭.asIdeal _
    rw [hj]; ring_nf
  · refine MonoidHom.mem_mrange.mpr ⟨P₀.1 ^ Multiset.count q (UniqueFactorizationMonoid.normalizedFactors I), ?_⟩
    simp only [MonoidHom.coe_ofClass, map_pow]
    rw [hnorm, hf, pow_one]

/-! ### Split, inert, ramified: where $\psi_\mathfrak p$ is nontrivial -/

/-- **An anti-invariant square root is not in $F$:** if $s \in E$, $s \ne 0$, $\sigma s = -s$ and $s^2 = a \in F$, then $a$ is not a square
in $F$ (else $s = \pm c \in F$, but $\sigma s = -s \ne s$). -/
theorem not_isSquare_of_anti {s : E} (hs0 : s ≠ 0) (hσ : conj F E s = -s) {a : F} (ha : algebraMap F E a = s ^ 2) :
    ¬ IsSquare a := by
  rintro ⟨c, hc⟩
  have h : (s - algebraMap F E c) * (s + algebraMap F E c) = 0 := by
    rw [hc, map_mul] at ha
    linear_combination -ha
  rcases mul_eq_zero.mp h with h | h
  · have e : s = algebraMap F E c := sub_eq_zero.mp h
    have := hσ
    rw [e, conj_algebraMap, eq_neg_iff_add_eq_zero, ← two_mul, mul_eq_zero] at this
    rcases this with h2 | h0
    · exact two_ne_zero h2
    · exact hs0 (by rw [e, h0])
  · have e : s = -algebraMap F E c := eq_neg_of_add_eq_zero_left h
    have := hσ
    rw [e, map_neg, conj_algebraMap, neg_neg, neg_eq_iff_add_eq_zero, ← two_mul, mul_eq_zero] at this
    rcases this with h2 | h0
    · exact two_ne_zero h2
    · exact hs0 (by rw [e, h0, neg_zero])

/-- $\delta$ is not a square in $F$. -/
theorem not_isSquare_relD : ¬ IsSquare (relD F E) :=
  not_isSquare_of_anti relGen_ne_zero conj_relGen algebraMap_relD

/-- The prime $\mathfrak P$ of $\mathcal O_E$ over $\mathfrak p$ as a point of `HeightOneSpectrum`. -/
def primeOf {𝔭 : HeightOneSpectrum (𝓞 F)} (P : 𝔭.asIdeal.primesOver (𝓞 E)) : HeightOneSpectrum (𝓞 E) where
  asIdeal := P.1
  isPrime := P.2.1
  ne_bot := by
    have := isMaximal_of_primesOver P
    intro h0
    have hl := (P.2.2 : P.1.LiesOver 𝔭.asIdeal).over
    rw [h0] at hl
    apply 𝔭.ne_bot
    rw [hl]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))

theorem under_primeOf {𝔭 : HeightOneSpectrum (𝓞 F)} (P : 𝔭.asIdeal.primesOver (𝓞 E)) :
    HN.under (F := F) (primeOf P) = 𝔭 := by
  ext1
  exact ((P.2.2 : P.1.LiesOver 𝔭.asIdeal).over).symm

/-- **Split primes: $\delta$ is a local square** (every residue characteristic): if $\mathfrak p$ splits in $E$, then
$\delta \in F_\mathfrak p^{\times 2}$ (`HN.isSquare_of_ef_one`: a prime over $\mathfrak p$ with $e = f = 1$). -/
@[kb "neukirch1999" "Ch. II, Prop. 8.2 [unverified]"]
theorem isSquare_of_split {𝔭 : HeightOneSpectrum (𝓞 F)} (h : relChar E 𝔭 = 1) {s : E} {a : F} (ha0 : a ≠ 0)
    (ha : algebraMap F E a = s ^ 2) : IsSquare (algebraMap F (𝔭.adicCompletion F) a) := by
  obtain ⟨-, P₀, -, -, -, he, hf, -, -⟩ | ⟨h', -⟩ | ⟨h', -⟩ :=
    splitting (Algebra.IsQuadraticExtension.finrank_eq_two F E) 𝔭
  · have := isMaximal_of_primesOver P₀
    have : (HN.under (F := F) (primeOf P₀)).asIdeal.IsMaximal := (HN.under (F := F) (primeOf P₀)).isMaximal
    have hf' : (HN.under (F := F) (primeOf P₀)).asIdeal.inertiaDeg' (primeOf P₀).asIdeal = 1 := by
      rw [Ideal.inertiaDeg'_eq_inertiaDeg]; exact hf
    have := HN.isSquare_of_ef_one (primeOf P₀) he hf' a ha0 s ha.symm
    rwa [under_primeOf] at this
  · rw [h] at h'; norm_num at h'
  · rw [h] at h'; norm_num at h'

/-- **Split primes: $\delta$ is a local square.** -/
theorem isSquare_relD_of_split {𝔭 : HeightOneSpectrum (𝓞 F)} (h : relChar E 𝔭 = 1) :
    IsSquare (algebraMap F (𝔭.adicCompletion F) (relD F E)) :=
  isSquare_of_split h relD_ne_zero algebraMap_relD

/-- **Non-split primes: $\delta$ is not a local square** (every residue characteristic): if $\mathfrak p$ is inert or ramified,
$\delta \notin F_\mathfrak p^{\times 2}$ (`HN.two_primes_of_isSquare`: a local square gives two primes over $\mathfrak p$). -/
@[kb "neukirch1999" "Ch. II, Prop. 8.2 [unverified]"]
theorem not_isSquare_of_not_split {𝔭 : HeightOneSpectrum (𝓞 F)} (h : relChar E 𝔭 ≠ 1) {s : E} (hs0 : s ≠ 0)
    (hσ : conj F E s = -s) {a : F} (ha : algebraMap F E a = s ^ 2) :
    ¬ IsSquare (algebraMap F (𝔭.adicCompletion F) a) := by
  intro hsq
  obtain ⟨w, w', hne, hw, hw'⟩ := HN.two_primes_of_isSquare (conj F E) s a
    ha.symm hσ (not_isSquare_of_anti hs0 hσ ha) 𝔭 hsq
  have huniq : ∃ P₀ : 𝔭.asIdeal.primesOver (𝓞 E), ∀ P, P = P₀ := by
    obtain ⟨h', -⟩ | ⟨-, P₀, hall, -⟩ | ⟨-, P₀, hall, -⟩ :=
      splitting (Algebra.IsQuadraticExtension.finrank_eq_two F E) 𝔭
    · exact absurd h' h
    · exact ⟨P₀, hall⟩
    · exact ⟨P₀, hall⟩
  obtain ⟨P₀, hall⟩ := huniq
  have e1 := congrArg Subtype.val (hall ⟨w.asIdeal, w.isPrime, ⟨by rw [← hw]; rfl⟩⟩)
  have e2 := congrArg Subtype.val (hall ⟨w'.asIdeal, w'.isPrime, ⟨by rw [← hw']; rfl⟩⟩)
  exact hne (HeightOneSpectrum.ext (show w.asIdeal = w'.asIdeal from e1.trans e2.symm))

/-- **Non-split primes: $\delta$ is not a local square.** -/
theorem not_isSquare_relD_of_not_split {𝔭 : HeightOneSpectrum (𝓞 F)} (h : relChar E 𝔭 ≠ 1) :
    ¬ IsSquare (algebraMap F (𝔭.adicCompletion F) (relD F E)) :=
  not_isSquare_of_not_split h relGen_ne_zero conj_relGen algebraMap_relD

/-- **Local nondegeneracy:** if $\delta \notin F_\mathfrak p^{\times 2}$ then $(\delta, x)_\mathfrak p = -1$ for some $x \in F_\mathfrak p^\times$
(`SqDual.hilbCl_nondeg_fin`). -/
@[kb "omeara1963" "§63B, 63:13, p. 166"]
theorem exists_hilbertSymbol_neg {𝔭 : HeightOneSpectrum (𝓞 F)}
    (h : ¬ IsSquare (algebraMap F (𝔭.adicCompletion F) (relD F E))) :
    ∃ x : 𝔭.adicCompletion F, x ≠ 0 ∧
      hilbertSymbol (𝔭.adicCompletion F) (algebraMap F (𝔭.adicCompletion F) (relD F E)) x = -1 := by
  have hd0 : algebraMap F (𝔭.adicCompletion F) (relD F E) ≠ 0 := (map_ne_zero _).mpr relD_ne_zero
  set d : (𝔭.adicCompletion F)ˣ := Units.mk0 _ hd0
  have hy : (QuotientGroup.mk d : SqDual.SqCl (𝔭.adicCompletion F)) ≠ 1 := fun h1 =>
    h ((SqDual.mk_eq_one_iff_isSquare _ d).mp h1)
  obtain ⟨x, hx⟩ := SqDual.hilbCl_nondeg_fin 𝔭 _ hy
  induction x using QuotientGroup.induction_on with
  | H u =>
    refine ⟨u, u.ne_zero, ?_⟩
    rw [SqDual.hilbCl_mk, hilbertSymbol_comm] at hx
    exact hx

/-- $\psi_\mathfrak p \equiv 1$ when $\delta$ is a square in $F_\mathfrak p$. -/
theorem genusSym_eq_one_of_isSquare {𝔭 : HeightOneSpectrum (𝓞 F)}
    (h : IsSquare (algebraMap F (𝔭.adicCompletion F) (relD F E))) (x : F) :
    genusSym E (NFPlace.finite 𝔭) x = 1 := by
  obtain ⟨z, hz⟩ := h
  rw [genusSym, NFPlace.hilbert]
  unfold hilbertSymbol
  exact if_pos ⟨1, 0, z, by simp, by rw [hz]; ring⟩

/-- **Ramified primes divide $2\delta$** ($\delta \in \mathcal O_F$, $\delta = \theta^2$; `relChar_eq_one_iff_sq`). -/
theorem two_relD_mem_of_ramified {δ : 𝓞 F} (hδE : algebraMap (𝓞 F) (𝓞 E) δ = relGen F E ^ 2)
    {𝔭 : HeightOneSpectrum (𝓞 F)} (h𝔭 : relChar E 𝔭 = 0) : 2 * δ ∈ 𝔭.asIdeal := by
  by_contra hn
  have h2 : (2 : 𝓞 F) ∉ 𝔭.asIdeal := fun h => hn (𝔭.asIdeal.mul_mem_right _ h)
  have hδ𝔭 : δ ∉ 𝔭.asIdeal := fun h => hn (𝔭.asIdeal.mul_mem_left _ h)
  exact (relChar_eq_one_iff_sq (conjO_relGen (F := F) (E := E)) hδE h2 hδ𝔭).1 h𝔭

/-- The ramified primes form a finite set. -/
theorem finite_ramified : {𝔭 : HeightOneSpectrum (𝓞 F) | relChar E 𝔭 = 0}.Finite := by
  obtain ⟨δ, hδ, hδE⟩ := exists_relD_int (F := F) (E := E)
  have hδ0 : (2 * δ : 𝓞 F) ≠ 0 := by
    refine mul_ne_zero two_ne_zero (fun h => relD_ne_zero (F := F) (E := E) ?_)
    rw [← hδ, h]; rfl
  refine (Ideal.finite_factors (I := Ideal.span {2 * δ}) (by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hδ0)).subset (fun 𝔭 h𝔭 => ?_)
  show 𝔭.asIdeal ∣ Ideal.span {2 * δ}
  rw [Ideal.dvd_span_singleton]
  exact two_relD_mem_of_ramified hδE h𝔭

/-- **Product formula on a finite set carrying all nontrivial characters:** if $\psi_v(x) = 1$ at every place outside the finite set
$T$ of finite primes, then $\prod_{\mathfrak p \in T}\psi_\mathfrak p(x) = 1$. -/
theorem prod_genusSym_eq_one {x : F} (hx : x ≠ 0) (T : Finset (HeightOneSpectrum (𝓞 F)))
    (hT : ∀ v : NFPlace F, (∀ 𝔭 ∈ T, v ≠ NFPlace.finite 𝔭) → genusSym E v x = 1) :
    ∏ 𝔭 ∈ T, signOf (genusSym E (NFPlace.finite 𝔭) x) = 1 := by
  classical
  obtain ⟨-, hev⟩ := genusSym_reciprocity (E := E) hx
  have hS : {v : NFPlace F | genusSym E v x = -1} =
      ((T.filter fun 𝔭 => genusSym E (NFPlace.finite 𝔭) x = -1).image NFPlace.finite : Set (NFPlace F)) := by
    ext v
    simp only [Set.mem_setOf_eq, Finset.coe_image, Finset.coe_filter, Set.mem_image]
    constructor
    · intro hv
      by_contra hno
      have h1 := hT v (by
        rintro 𝔭 h𝔭 rfl
        exact hno ⟨𝔭, ⟨h𝔭, hv⟩, rfl⟩)
      rw [h1] at hv; norm_num at hv
    · rintro ⟨𝔭, ⟨-, h𝔭⟩, rfl⟩; exact h𝔭
  rw [hS, Set.ncard_coe_finset, Finset.card_image_of_injective _ (fun _ _ h => by cases h; rfl)] at hev
  rw [← Finset.prod_filter_mul_prod_filter_not T (fun 𝔭 => genusSym E (NFPlace.finite 𝔭) x = -1)]
  rw [Finset.prod_congr rfl (fun 𝔭 h𝔭 => by
      rw [(Finset.mem_filter.mp h𝔭).2]; rfl : ∀ 𝔭 ∈ T.filter (fun 𝔭 => genusSym E (NFPlace.finite 𝔭) x = -1),
        signOf (genusSym E (NFPlace.finite 𝔭) x) = -1),
    Finset.prod_congr rfl (fun 𝔭 h𝔭 => by
      have h1 := (Finset.mem_filter.mp h𝔭).2
      rcases genusSym_eq_one_or (E := E) (NFPlace.finite 𝔭) x with h | h
      · rw [h]; rfl
      · exact absurd h h1 : ∀ 𝔭 ∈ T.filter (fun 𝔭 => ¬ genusSym E (NFPlace.finite 𝔭) x = -1),
        signOf (genusSym E (NFPlace.finite 𝔭) x) = 1),
    Finset.prod_const, Finset.prod_const_one, mul_one, hev.neg_one_pow]

/-! ### CM: the exact set of genus vectors, and $2^{|T|-1}$ genera -/

section CMExact

variable [IsTotallyReal F] [IsTotallyComplex E]

variable (E) in
/-- **The totally positive normalized values** $\eta a$: $N_{E/F}\mathfrak A = (a)$ for a nonzero ideal $\mathfrak A$ of $\mathcal O_E$, $\eta \in \mathcal O_F^\times$,
$\eta a \gg 0$. The lattice $(\mathfrak A, \frac{\eta}{a}N)$ is totally positive definite, and its genus is the vector $(\psi_v(\eta a))_v$
(`genusSym_normalized`, `isometryEquiv_iff_genusSym`). -/
def posNormValues : Set F :=
  {x | ∃ (𝔄 : Ideal (𝓞 E)) (a : 𝓞 F) (η : (𝓞 F)ˣ), 𝔄 ≠ ⊥ ∧ Ideal.relNorm (𝓞 F) 𝔄 = Ideal.span {a} ∧
    x = ((η : 𝓞 F) : F) * (a : F) ∧ ∀ w : Siegel.RealPlace F, 0 < Siegel.realEmb w x}

theorem valuation_unit_eq_one (𝔭 : HeightOneSpectrum (𝓞 F)) (η : (𝓞 F)ˣ) :
    𝔭.valuation F ((η : 𝓞 F) : F) = 1 := by
  rw [show ((η : 𝓞 F) : F) = algebraMap (𝓞 F) F (η : 𝓞 F) from rfl, HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_eq_one_iff.mpr (fun h => 𝔭.isPrime.ne_top
    (Ideal.eq_top_of_isUnit_mem _ h η.isUnit))

/-- **Off the genus primes the characters of a positive normalized value are trivial** (infinite places: positivity; inert primes:
the valuation is even, `genusSym_inert_iff`; other primes outside $T$: by definition of $T$). -/
theorem genusSym_posNormValues_eq_one {T : Finset (HeightOneSpectrum (𝓞 F))}
    (hT : ∀ 𝔭, 𝔭 ∈ T ↔ relChar E 𝔭 = 0) {x : F} (hx : x ∈ posNormValues E) (v : NFPlace F)
    (hv : ∀ 𝔭 ∈ T, v ≠ NFPlace.finite 𝔭) : genusSym E v x = 1 := by
  obtain ⟨𝔄, a, η, h𝔄, ha, rfl, hpos⟩ := hx
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [Set.singleton_zero, Ideal.span_zero, Ideal.relNorm_eq_bot_iff] at ha
    exact h𝔄 ha
  have hx0 : ((η : 𝓞 F) : F) * (a : F) ≠ 0 :=
    mul_ne_zero (fun h => η.ne_zero (by exact_mod_cast h)) (by exact_mod_cast ha0)
  cases v with
  | infinite w =>
    have hw : w.IsReal := IsTotallyReal.isReal w
    exact (genusSym_infinite_iff ⟨w, hw⟩ hx0).mpr (hpos ⟨w, hw⟩)
  | finite 𝔭 =>
    have h𝔭T : relChar E 𝔭 ≠ 0 := fun h => hv 𝔭 ((hT 𝔭).mpr h) rfl
    by_cases hin : relChar E 𝔭 = -1
    · have hev := even_count_relNorm_of_inert hin h𝔄
      rw [ha] at hev
      have hval : 𝔭.valuation F (((η : 𝓞 F) : F) * (a : F)) = WithZero.exp (-(Multiset.count 𝔭.asIdeal
          (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a})) : ℤ)) := by
        rw [map_mul, valuation_unit_eq_one, one_mul]
        exact valuation_algebraMap_eq_count 𝔭 ha0
      refine (genusSym_inert_iff hin hx0 hval).mpr ?_
      exact (Int.even_coe_nat _).mpr hev |>.neg
    · have hsplit : relChar E 𝔭 = 1 := by
        rcases relChar_trichotomy (E := E) 𝔭 with h | h | h
        · exact h
        · exact absurd h hin
        · exact absurd h h𝔭T
      exact genusSym_eq_one_of_isSquare (isSquare_relD_of_split hsplit) _

theorem signOf_neg_one : signOf (-1) = -1 := by unfold signOf; decide
theorem signOf_one : signOf 1 = 1 := by unfold signOf; decide
theorem signOf_coe (e : ℤˣ) : signOf (e : ℤ) = e := by
  rcases Int.units_eq_one_or e with rfl | rfl
  · exact signOf_one
  · exact signOf_neg_one

/-- **The exact set of genus vectors** (CM): a function $\varphi$ on the places of $F$ is the genus vector $(\psi_v(x))_v$ of a totally
positive normalized value $x$ iff $\varphi = 1$ off the genus primes $T$, $\varphi = \pm 1$ on $T$, and $\prod_{\mathfrak p \in T}\varphi(\mathfrak p) = 1$.
Existence: elements with prescribed Hilbert symbols (`NFInputs.exists_prescribed_hilbert_nf`), then a norm ideal with even
valuations at the inert primes (`exists_relNorm_eq`, `genusSym_inert_iff`). -/
@[kb "hecke1923" "§48 [unverified]; omeara1963 §71D, 71:19, p. 203 (prescribed Hilbert symbols); cf. genusChar_surjective"]
theorem mem_genusVectors_iff {T : Finset (HeightOneSpectrum (𝓞 F))} (hT : ∀ 𝔭, 𝔭 ∈ T ↔ relChar E 𝔭 = 0)
    (φ : NFPlace F → ℤ) :
    φ ∈ (fun (x : F) v => genusSym E v x) '' posNormValues E ↔
      (∀ v, (∀ 𝔭 ∈ T, v ≠ NFPlace.finite 𝔭) → φ v = 1) ∧
      (∀ 𝔭 ∈ T, φ (NFPlace.finite 𝔭) = 1 ∨ φ (NFPlace.finite 𝔭) = -1) ∧
      ∏ 𝔭 ∈ T, signOf (φ (NFPlace.finite 𝔭)) = 1 := by
  classical
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hoff := genusSym_posNormValues_eq_one hT hx
    have hx0 : x ≠ 0 := by
      obtain ⟨𝔄, a, η, h𝔄, ha, rfl, hpos⟩ := hx
      intro h0
      have := hpos ⟨_, IsTotallyReal.isReal (Classical.arbitrary (InfinitePlace F))⟩
      rw [h0, map_zero] at this; exact lt_irrefl _ this
    exact ⟨hoff, fun 𝔭 _ => genusSym_eq_one_or _ _, prod_genusSym_eq_one hx0 T hoff⟩
  · rintro ⟨hoff, hpm, hprod⟩
    have hε : ∀ v, φ v = 1 ∨ φ v = -1 := by
      intro v
      by_cases hv : ∃ 𝔭 ∈ T, v = NFPlace.finite 𝔭
      · obtain ⟨𝔭, h𝔭, rfl⟩ := hv; exact hpm 𝔭 h𝔭
      · push Not at hv; exact Or.inl (hoff v hv)
    have hneg : ∀ v, φ v = -1 → ∃ 𝔭 ∈ T, v = NFPlace.finite 𝔭 := by
      intro v hv
      by_contra hno
      push Not at hno
      rw [hoff v hno] at hv; norm_num at hv
    have hset : {v : NFPlace F | φ v = -1} =
        ((T.filter fun 𝔭 => φ (NFPlace.finite 𝔭) = -1).image NFPlace.finite : Set (NFPlace F)) := by
      ext v
      simp only [Set.mem_setOf_eq, Finset.coe_image, Finset.coe_filter, Set.mem_image]
      constructor
      · intro hv
        obtain ⟨𝔭, h𝔭, rfl⟩ := hneg v hv
        exact ⟨𝔭, ⟨h𝔭, hv⟩, rfl⟩
      · rintro ⟨𝔭, ⟨-, h𝔭⟩, rfl⟩; exact h𝔭
    have hcardev : Even {v : NFPlace F | φ v = -1}.ncard := by
      rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injective _ (fun _ _ h => by cases h; rfl)]
      rw [← Finset.prod_filter_mul_prod_filter_not T (fun 𝔭 => φ (NFPlace.finite 𝔭) = -1)] at hprod
      rw [Finset.prod_congr rfl (fun 𝔭 h𝔭 => by
          rw [(Finset.mem_filter.mp h𝔭).2]; exact signOf_neg_one : ∀ 𝔭 ∈ T.filter
            (fun 𝔭 => φ (NFPlace.finite 𝔭) = -1), signOf (φ (NFPlace.finite 𝔭)) = -1),
        Finset.prod_congr rfl (fun 𝔭 h𝔭 => by
          have h1 := (Finset.mem_filter.mp h𝔭).2
          rcases hpm 𝔭 (Finset.mem_filter.mp h𝔭).1 with h | h
          · rw [h]; exact signOf_one
          · exact absurd h h1 : ∀ 𝔭 ∈ T.filter (fun 𝔭 => ¬ φ (NFPlace.finite 𝔭) = -1),
            signOf (φ (NFPlace.finite 𝔭)) = 1),
        Finset.prod_const, Finset.prod_const_one, mul_one] at hprod
      exact (neg_one_pow_eq_one_iff_even (by decide)).mp hprod
    -- prescribed Hilbert symbols
    obtain ⟨x, hx0, hxφ⟩ := NFInputs.exists_prescribed_hilbert_nf (ι := Unit) (fun _ => relD F E)
      (fun _ => relD_ne_zero) (fun _ v => φ v) (fun _ v => hε v)
      ((Finset.finite_toSet ((T.filter fun 𝔭 => φ (NFPlace.finite 𝔭) = -1).image NFPlace.finite)).subset
        (fun v hv => by
          obtain ⟨-, hv⟩ := hv
          rw [← hset]; exact hv))
      (fun _ => hcardev)
      (fun v => by
        rcases hε v with h1 | h1
        · cases v with
          | infinite w => exact ⟨1, one_ne_zero, fun _ => by rw [h1]; exact hilbertSymbol_one_right _ _⟩
          | finite 𝔭 => exact ⟨1, one_ne_zero, fun _ => by rw [h1]; exact hilbertSymbol_one_right _ _⟩
        · obtain ⟨𝔭, h𝔭, rfl⟩ := hneg v h1
          have hns := not_isSquare_relD_of_not_split (E := E) (𝔭 := 𝔭) (by rw [(hT 𝔭).mp h𝔭]; norm_num)
          obtain ⟨y, hy0, hy⟩ := exists_hilbertSymbol_neg hns
          exact ⟨y, hy0, fun _ => by rw [h1]; exact hy⟩)
    have hxψ : ∀ v, genusSym E v x = φ v := fun v => hxφ () v
    -- clear denominators
    obtain ⟨n, d, hd, hnd⟩ := IsFractionRing.div_surjective (A := 𝓞 F) x
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    have hdF : (d : F) ≠ 0 := by exact_mod_cast hd0
    have haF : ((n * d : 𝓞 F) : F) = x * (d : F) ^ 2 := by
      rw [← hnd]; push_cast
      change (algebraMap (𝓞 F) F n) * (algebraMap (𝓞 F) F d) =
        algebraMap (𝓞 F) F n / algebraMap (𝓞 F) F d * (algebraMap (𝓞 F) F d) ^ 2
      field_simp
    have ha0 : (n * d : 𝓞 F) ≠ 0 := by
      intro h
      have : ((n * d : 𝓞 F) : F) = 0 := by rw [h]; rfl
      rw [haF] at this
      exact mul_ne_zero hx0 (pow_ne_zero 2 hdF) this
    have haψ : ∀ v, genusSym E v ((n * d : 𝓞 F) : F) = φ v := by
      intro v
      rw [haF, genusSym_mul v hx0 (pow_ne_zero 2 hdF), hxψ,
        show genusSym E v ((d : F) ^ 2) = 1 from NFPlace.hilbert_eq_one_of_norm v (d : F) 0 (by ring), mul_one]
    -- a norm ideal
    obtain ⟨𝔄, h𝔄⟩ := exists_relNorm_eq (E := E) (I := Ideal.span {n * d})
      (by rw [Ne, Ideal.span_singleton_eq_bot]; exact ha0) (fun 𝔭 hin => by
        have h𝔭T : 𝔭 ∉ T := fun h => by rw [(hT 𝔭).mp h] at hin; norm_num at hin
        have h1 : genusSym E (NFPlace.finite 𝔭) ((n * d : 𝓞 F) : F) = 1 := by
          rw [haψ]; exact hoff _ (fun 𝔮 h𝔮 h => h𝔭T (by cases h; exact h𝔮))
        have hne : algebraMap (𝓞 F) F (n * d) ≠ 0 :=
          (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mpr ha0
        have := (genusSym_inert_iff hin hne (valuation_algebraMap_eq_count 𝔭 ha0)).mp h1
        exact (Int.even_coe_nat _).mp (even_neg.mp this))
    have h𝔄0 : 𝔄 ≠ ⊥ := by
      rintro rfl
      rw [Ideal.relNorm_bot, eq_comm, Ideal.span_singleton_eq_bot] at h𝔄
      exact ha0 h𝔄
    refine ⟨((n * d : 𝓞 F) : F), ⟨𝔄, n * d, 1, h𝔄0, h𝔄, by simp, fun w => ?_⟩, funext haψ⟩
    rw [haF, map_mul, map_pow]
    have hxw : 0 < Siegel.realEmb w x := (genusSym_infinite_iff w hx0).mp (by
      rw [hxψ]; exact hoff _ (fun 𝔭 _ h => by cases h))
    have hdw : Siegel.realEmb w (d : F) ≠ 0 := (map_ne_zero _).mpr hdF
    positivity

/-- **The exact number of genera of totally positive definite normalized binary lattices over $F$** ($E/F$ CM):
$$\#\{(\psi_v(x))_v : x \in \texttt{posNormValues}\} = 2^{|T|-1}, \qquad T = \{\mathfrak p : \mathfrak p \text{ ramified in } E\}$$
(natural-number subtraction: $1$ genus when $T = \emptyset$). Upper bound: The argument with $T$ for $S$; lower bound: every
product-one sign vector on $T$ occurs (`mem_genusVectors_iff`). By `isometryEquiv_iff_genusSym` the genus vector is the
rational genus. Over $\mathbb Q$ this is Gauss's $2^{t-1}$ (`card_genera`). -/
@[kb "hecke1923" "§48 [unverified]; cf. card_genera"]
theorem ncard_genera_eq {T : Finset (HeightOneSpectrum (𝓞 F))} (hT : ∀ 𝔭, 𝔭 ∈ T ↔ relChar E 𝔭 = 0) :
    ((fun (x : F) v => genusSym E v x) '' posNormValues E).ncard = 2 ^ (T.card - 1) := by
  classical
  set R := (fun (x : F) v => genusSym E v x) '' posNormValues E
  let g : (NFPlace F → ℤ) → (T → ℤˣ) := fun φ 𝔭 => signOf (φ (NFPlace.finite 𝔭.1))
  have hinj : Set.InjOn g R := by
    intro φ hφ φ' hφ' hg
    obtain ⟨h1, h2, -⟩ := (mem_genusVectors_iff hT φ).mp hφ
    obtain ⟨h1', h2', -⟩ := (mem_genusVectors_iff hT φ').mp hφ'
    funext v
    by_cases hv : ∃ 𝔭 ∈ T, v = NFPlace.finite 𝔭
    · obtain ⟨𝔭, h𝔭, rfl⟩ := hv
      have := congrFun hg ⟨𝔭, h𝔭⟩
      rw [← coe_signOf (h2 𝔭 h𝔭), ← coe_signOf (h2' 𝔭 h𝔭)]
      exact congrArg Units.val this
    · push Not at hv; rw [h1 v hv, h1' v hv]
  have himg : g '' R = {e : T → ℤˣ | ∏ i, e i = 1} := by
    ext e
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      obtain ⟨-, -, h3⟩ := (mem_genusVectors_iff hT φ).mp hφ
      rw [← Finset.prod_coe_sort] at h3
      exact h3
    · intro he
      let φ : NFPlace F → ℤ := fun v => match v with
        | NFPlace.infinite _ => 1
        | NFPlace.finite 𝔭 => if h : 𝔭 ∈ T then ((e ⟨𝔭, h⟩ : ℤˣ) : ℤ) else 1
      have hφT : ∀ 𝔭 (h : 𝔭 ∈ T), φ (NFPlace.finite 𝔭) = ((e ⟨𝔭, h⟩ : ℤˣ) : ℤ) := fun 𝔭 h => dif_pos h
      refine ⟨φ, (mem_genusVectors_iff hT φ).mpr ⟨fun v hv => ?_, fun 𝔭 h𝔭 => ?_, ?_⟩, ?_⟩
      · cases v with
        | infinite w => rfl
        | finite 𝔭 => exact dif_neg (fun h => hv 𝔭 h rfl)
      · rw [hφT 𝔭 h𝔭]; exact Int.units_eq_one_or _ |>.imp (congrArg _) (congrArg _)
      · rw [← Finset.prod_coe_sort]
        rw [← he]
        exact Finset.prod_congr rfl (fun i _ => by rw [hφT i.1 i.2, signOf_coe])
      · funext i
        simp only [g]
        rw [hφT i.1 i.2, signOf_coe]
  rw [← hinj.ncard_image, himg, ← Nat.card_coe_set_eq]
  change Nat.card {e : T → ℤˣ // ∏ i, e i = 1} = _
  rcases T.eq_empty_or_nonempty with h0 | hne
  · subst h0
    rw [Finset.card_empty]
    have : IsEmpty (↥(∅ : Finset (HeightOneSpectrum (𝓞 F)))) := ⟨fun i => Finset.notMem_empty _ i.2⟩
    rw [show (2 : ℕ) ^ (0 - 1) = 1 by norm_num, Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Subtype.ext (funext fun i => isEmptyElim i)⟩, ⟨⟨isEmptyElim, by simp⟩⟩⟩
  · have : Nonempty T := ⟨⟨hne.choose, hne.choose_spec⟩⟩
    rw [card_signVec_prod_one, Fintype.card_coe]

end CMExact

end QuadFormsKB.Binary.Rel
