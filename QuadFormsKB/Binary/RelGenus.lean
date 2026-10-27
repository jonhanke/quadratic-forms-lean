import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Binary.RelRepCount

/-!
# Genus characters over $F$ at the ramified primes (partial)

Let $E/F$ be a quadratic extension of number fields and $\mathfrak p$ a prime of $F$ **ramified** in $E$ ($\chi_{E/F}(\mathfrak p) = 0$,
the `relChar`; then $\mathfrak p\mathcal O_E = \mathfrak P^2$ with residue degree $1$, the `splitting`). The analogue
over $F$ of the genus characters $\psi_p$ for $p \mid D$:

* **Norms are squares mod $\mathfrak p$** (`exists_sq_sub_intNorm_mem`): for every $x \in \mathcal O_E$ there is $b \in \mathcal O_F$ with
  $N_{E/F}(x) \equiv b^2 \pmod{\mathfrak p}$. Proof: $\sigma(\mathfrak P) = \mathfrak P$ (`conjIdeal_prime_eq`, the only prime over $\mathfrak p$),
  and residue degree $1$ gives $x \equiv b \pmod{\mathfrak P}$ with $b \in \mathcal O_F$ (`exists_sub_mem_of_inertiaDeg_one`); then
  $N(x) = x\,\sigma(x) \equiv b\cdot b \pmod{\mathfrak P}$, and $\mathfrak P \cap \mathcal O_F = \mathfrak p$.
* **Genus characters are well defined** (`exists_sq_sub_mul_mem`, `quadraticChar_eq`): let $\mathfrak A \ne 0$ with $N_{E/F}\mathfrak A = (a)$
  and $x, y \in \mathfrak A$, $N(x) = as$, $N(y) = at$ (so the values of the normalized form $\frac{\eta}{a}N$ at $x, y$ are $\eta s$, $\eta t$).
  Then $st \equiv b^2 \pmod{\mathfrak p}$; hence for $s, t \notin \mathfrak p$, $\psi_\mathfrak p(s) = \psi_\mathfrak p(t)$ for the
  quadratic character $\psi_\mathfrak p$ of the residue field $\mathcal O_F/\mathfrak p$ (Mathlib's `quadraticChar`). So every normalized lattice
  $(\mathfrak A, \frac{\eta}{a}N)$ has a well-defined genus character $\chi_\mathfrak p = \psi_\mathfrak p(\eta)\psi_\mathfrak p(s)$ at each odd ramified $\mathfrak p$:
  the value of $\psi_\mathfrak p$ on any represented value prime to $\mathfrak p$. Proof: $x\,\sigma(y) \in \mathfrak A\,\sigma(\mathfrak A) = a\,\mathcal O_E$
  (`mul_conjIdeal`), so $x\sigma(y) = az$ and $st = N(z)$, a square mod $\mathfrak p$. This is the argument of the
  `genusChar_eval_eq_formChar` (there: $4af(x,y) = X^2 - DY^2$), and over $\mathbb Q$ it is the statement for odd $p \mid D$.

**Not done:** the dyadic ramified primes (squares modulo $\mathfrak p$ carry no information there; one needs
the norm residue symbol of $E_\mathfrak P/F_\mathfrak p$ modulo a power of $\mathfrak p$), the product formula $\prod_\mathfrak p\chi_\mathfrak p = 1$
(quadratic reciprocity over $F$ / Hilbert reciprocity), genus = local equivalence, the number of genera, the classes per
genus and the mass of a genus. These need local class field theory for $E_\mathfrak P/F_\mathfrak p$ (or Hilbert symbols over $F$),
which Mathlib does not have.

*Update:* the repository proves Hilbert symbols, reciprocity and the Hasse norm theorem over $F$; the
`RelGenusHilbert.lean` defines the characters at every place (dyadic included) as $(\delta, \cdot)_v$ and proves the product
formula, genus = local equivalence and the principal genus theorem; `RelGenusCount.lean` bounds the number of genera.

Sources: Shimura, *Arithmetic of Quadratic Forms* (2010), §4 [unverified locator]; Neukirch, *Algebraic Number Theory*,
Ch. I §9 (ramified primes in Galois extensions) [unverified locator]; Cox §3 (the case $F = \mathbb Q$).
-/

open NumberField Module IsDedekindDomain
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Binary.Rel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

/-- With residue degree $1$, every $x \in \mathcal O_E$ is congruent mod $\mathfrak P$ to an element of $\mathcal O_F$. -/
theorem exists_sub_mem_of_inertiaDeg_one (𝔭 : Ideal (𝓞 F)) [𝔭.IsMaximal] (P : Ideal (𝓞 E)) [P.IsMaximal]
    [P.LiesOver 𝔭] (hf : P.inertiaDeg (𝓞 F) = 1) (x : 𝓞 E) :
    ∃ b : 𝓞 F, x - algebraMap (𝓞 F) (𝓞 E) b ∈ P := by
  rw [Ideal.inertiaDeg_eq_of_isMaximal 𝔭 P] at hf
  let : Field (𝓞 F ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  let : Field (𝓞 E ⧸ P) := Ideal.Quotient.field P
  have htop := Subalgebra.bot_eq_top_iff_finrank_eq_one.mpr hf
  have hx : Ideal.Quotient.mk P x ∈ (⊥ : Subalgebra (𝓞 F ⧸ 𝔭) (𝓞 E ⧸ P)) := htop ▸ Algebra.mem_top
  obtain ⟨b', hb'⟩ := Algebra.mem_bot.mp hx
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b'
  refine ⟨b, ?_⟩
  rw [← Ideal.Quotient.eq, ← hb', Ideal.Quotient.algebraMap_mk_of_liesOver]

/-- The conjugate of a prime over $\mathfrak p$ is a prime over $\mathfrak p$. -/
theorem conjIdeal_mem_primesOver (𝔭 : Ideal (𝓞 F)) (P : 𝔭.primesOver (𝓞 E)) :
    conjIdeal F P.1 ∈ 𝔭.primesOver (𝓞 E) := by
  have hP := P.2
  have : P.1.IsPrime := hP.1
  have : P.1.LiesOver 𝔭 := hP.2
  refine ⟨Ideal.map_isPrime_of_equiv (conjO F E), ?_⟩
  exact Ideal.LiesOver.of_eq_map_equiv 𝔭 (RingOfIntegers.mapAlgEquiv (conj F E)) rfl

/-- **At a ramified prime, $\sigma(\mathfrak P) = \mathfrak P$** (the only prime over $\mathfrak p$). -/
theorem conjIdeal_prime_eq {𝔭 : HeightOneSpectrum (𝓞 F)} (h𝔭 : relChar E 𝔭 = 0) :
    ∃ P : 𝔭.asIdeal.primesOver (𝓞 E), conjIdeal F P.1 = P.1 ∧
      P.1.ramificationIdx (𝓞 F) = 2 ∧ P.1.inertiaDeg (𝓞 F) = 1 := by
  rcases splitting (Algebra.IsQuadraticExtension.finrank_eq_two F E) 𝔭 with
    ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, P, hP, he, hf⟩
  · rw [h𝔭] at h; exact absurd h (by norm_num)
  · rw [h𝔭] at h; exact absurd h (by norm_num)
  · refine ⟨P, ?_, he, hf⟩
    have := hP ⟨conjIdeal F P.1, conjIdeal_mem_primesOver 𝔭.asIdeal P⟩
    exact congrArg Subtype.val this

/-- **Relative norms are squares modulo a ramified prime:** if $\chi_{E/F}(\mathfrak p) = 0$, then for every $x \in \mathcal O_E$ there
is $b \in \mathcal O_F$ with $N_{E/F}(x) \equiv b^2 \pmod{\mathfrak p}$. -/
@[kb "neukirch1999" "Ch. I §9 [unverified]"]
theorem exists_sq_sub_intNorm_mem {𝔭 : HeightOneSpectrum (𝓞 F)} (h𝔭 : relChar E 𝔭 = 0) (x : 𝓞 E) :
    ∃ b : 𝓞 F, Algebra.intNorm (𝓞 F) (𝓞 E) x - b ^ 2 ∈ 𝔭.asIdeal := by
  obtain ⟨P, hσ, -, hf⟩ := conjIdeal_prime_eq h𝔭
  have hP := P.2
  have : P.1.IsPrime := hP.1
  have : P.1.LiesOver 𝔭.asIdeal := hP.2
  have : 𝔭.asIdeal.IsMaximal := 𝔭.isMaximal
  have : P.1.IsMaximal := Ideal.IsPrime.isMaximal hP.1 (by
    intro h0
    have := Ideal.LiesOver.over (P := P.1) (p := 𝔭.asIdeal)
    rw [h0] at this
    apply 𝔭.ne_bot
    rw [this]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E)))
  obtain ⟨b, hb⟩ := exists_sub_mem_of_inertiaDeg_one 𝔭.asIdeal P.1 hf x
  refine ⟨b, ?_⟩
  -- σ(x - b) ∈ σ P = P
  have hσb : conjO F E x - algebraMap (𝓞 F) (𝓞 E) b ∈ P.1 := by
    have h1 : conjO F E (x - algebraMap (𝓞 F) (𝓞 E) b) ∈ conjIdeal F P.1 := Ideal.mem_map_of_mem _ hb
    rw [hσ] at h1
    have h2 : conjO F E (algebraMap (𝓞 F) (𝓞 E) b) = algebraMap (𝓞 F) (𝓞 E) b := by
      apply FaithfulSMul.algebraMap_injective (𝓞 E) E
      rw [algebraMap_conjO, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E]
      exact (conj F E).commutes _
    rwa [map_sub, h2] at h1
  have hmem : algebraMap (𝓞 F) (𝓞 E) (Algebra.intNorm (𝓞 F) (𝓞 E) x - b ^ 2) ∈ P.1 := by
    rw [map_sub, algebraMap_intNorm_eq, map_pow]
    have e : x * conjO F E x - algebraMap (𝓞 F) (𝓞 E) b ^ 2 =
        (x - algebraMap (𝓞 F) (𝓞 E) b) * conjO F E x +
          algebraMap (𝓞 F) (𝓞 E) b * (conjO F E x - algebraMap (𝓞 F) (𝓞 E) b) := by ring
    rw [e]
    exact P.1.add_mem (P.1.mul_mem_right _ hb) (P.1.mul_mem_left _ hσb)
  have := Ideal.LiesOver.over (P := P.1) (p := 𝔭.asIdeal)
  rw [this]
  exact hmem

/-- **Genus characters over $F$ are well defined at the ramified primes.** Let $\mathfrak A \ne 0$ with $N_{E/F}\mathfrak A = (a)$, and
$x, y \in \mathfrak A$ with $N(x) = as$, $N(y) = at$. If $\chi_{E/F}(\mathfrak p) = 0$, then $st \equiv b^2 \pmod{\mathfrak p}$ for some
$b \in \mathcal O_F$. -/
@[kb "neukirch1999" "Ch. I §9 [unverified]; cf. genusChar_eval_eq_formChar"]
theorem exists_sq_sub_mul_mem {𝔭 : HeightOneSpectrum (𝓞 F)} (h𝔭 : relChar E 𝔭 = 0)
    {𝔄 : Ideal (𝓞 E)} {a : 𝓞 F} (ha : a ≠ 0) (h𝔄 : Ideal.relNorm (𝓞 F) 𝔄 = Ideal.span {a})
    {x y : 𝓞 E} (hx : x ∈ 𝔄) (hy : y ∈ 𝔄) {s t : 𝓞 F}
    (hs : Algebra.intNorm (𝓞 F) (𝓞 E) x = a * s) (ht : Algebra.intNorm (𝓞 F) (𝓞 E) y = a * t) :
    ∃ b : 𝓞 F, s * t - b ^ 2 ∈ 𝔭.asIdeal := by
  -- x σ(y) ∈ 𝔄 σ(𝔄) = a 𝓞_E
  have hxy : x * conjO F E y ∈ Ideal.span {algebraMap (𝓞 F) (𝓞 E) a} := by
    have h1 : x * conjO F E y ∈ 𝔄 * conjIdeal F 𝔄 := Ideal.mul_mem_mul hx (Ideal.mem_map_of_mem _ hy)
    rwa [mul_conjIdeal, h𝔄, Ideal.map_span, Set.image_singleton] at h1
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hxy
  -- N(x) N(y) = a^2 N(z), computed in F
  have hN : a * s * (a * t) = a ^ 2 * Algebra.intNorm (𝓞 F) (𝓞 E) z := by
    rw [← hs, ← ht]
    apply FaithfulSMul.algebraMap_injective (𝓞 F) F
    rw [map_mul, map_mul, map_pow, algebraMap_intNorm', algebraMap_intNorm', algebraMap_intNorm']
    have h1 := congrArg (fun w : 𝓞 E => nrm (F := F) w) hz
    simp only [nrm_mul] at h1
    have hcy : nrm (F := F) (conjO F E y) = nrm (F := F) y := by
      rw [nrm, nrm, algebraMap_conjO, norm_conj]
    have ha2 : nrm (F := F) (algebraMap (𝓞 F) (𝓞 E) a) = algebraMap (𝓞 F) F a ^ 2 := by
      rw [nrm, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E,
        Algebra.norm_algebraMap, Algebra.IsQuadraticExtension.finrank_eq_two]
    rw [hcy, ha2] at h1
    rw [← h1]
    ring
  have hst : s * t = Algebra.intNorm (𝓞 F) (𝓞 E) z := by
    have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
    refine mul_left_cancel₀ ha2 ?_
    rw [← hN]; ring
  rw [hst]
  exact exists_sq_sub_intNorm_mem h𝔭 z

/-- **The genus character at a ramified prime.** In the situation of `exists_sq_sub_mul_mem`, if moreover
$s, t \notin \mathfrak p$, then $\psi_\mathfrak p(s) = \psi_\mathfrak p(t)$, $\psi_\mathfrak p$ the
quadratic character of $\mathcal O_F/\mathfrak p$: the value of $\psi_\mathfrak p$ on the represented values prime to $\mathfrak p$ is an invariant of the
lattice. (For a dyadic $\mathfrak p$ the residue field has characteristic $2$, $\psi_\mathfrak p$ is trivial on $(\mathcal O_F/\mathfrak p)^\times$, and
the statement carries no information; the dyadic genus characters need congruences modulo higher powers of $\mathfrak p$.) -/
@[kb "neukirch1999" "Ch. I §9 [unverified]; cf. genusChar_eval_eq_formChar"]
theorem quadraticChar_eq {𝔭 : HeightOneSpectrum (𝓞 F)} (h𝔭 : relChar E 𝔭 = 0)
    [Fintype (𝓞 F ⧸ 𝔭.asIdeal)] [DecidableEq (𝓞 F ⧸ 𝔭.asIdeal)]
    {𝔄 : Ideal (𝓞 E)} {a : 𝓞 F} (ha : a ≠ 0) (h𝔄 : Ideal.relNorm (𝓞 F) 𝔄 = Ideal.span {a})
    {x y : 𝓞 E} (hx : x ∈ 𝔄) (hy : y ∈ 𝔄) {s t : 𝓞 F}
    (hs : Algebra.intNorm (𝓞 F) (𝓞 E) x = a * s) (ht : Algebra.intNorm (𝓞 F) (𝓞 E) y = a * t)
    (hs𝔭 : s ∉ 𝔭.asIdeal) (ht𝔭 : t ∉ 𝔭.asIdeal) :
    letI : Field (𝓞 F ⧸ 𝔭.asIdeal) := @Ideal.Quotient.field _ _ 𝔭.asIdeal 𝔭.isMaximal
    quadraticChar (𝓞 F ⧸ 𝔭.asIdeal) (Ideal.Quotient.mk 𝔭.asIdeal s) =
      quadraticChar (𝓞 F ⧸ 𝔭.asIdeal) (Ideal.Quotient.mk 𝔭.asIdeal t) := by
  let : Field (𝓞 F ⧸ 𝔭.asIdeal) := @Ideal.Quotient.field _ _ 𝔭.asIdeal 𝔭.isMaximal
  obtain ⟨b, hb⟩ := exists_sq_sub_mul_mem h𝔭 ha h𝔄 hx hy hs ht
  have hsq : Ideal.Quotient.mk 𝔭.asIdeal s * Ideal.Quotient.mk 𝔭.asIdeal t =
      Ideal.Quotient.mk 𝔭.asIdeal b ^ 2 := by
    rw [← map_mul, ← map_pow, Ideal.Quotient.eq]; exact hb
  have hs0 : Ideal.Quotient.mk 𝔭.asIdeal s ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have ht0 : Ideal.Quotient.mk 𝔭.asIdeal t ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hb0 : Ideal.Quotient.mk 𝔭.asIdeal b ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero] at hsq
    exact mul_ne_zero hs0 ht0 hsq
  have hprod := congrArg (quadraticChar (𝓞 F ⧸ 𝔭.asIdeal)) hsq
  rw [map_mul, quadraticChar_sq_one' hb0] at hprod
  have hss := quadraticChar_sq_one hs0
  -- χ(s) χ(t) = 1 and χ(s)^2 = 1 ⇒ χ(s) = χ(t)
  calc quadraticChar (𝓞 F ⧸ 𝔭.asIdeal) (Ideal.Quotient.mk 𝔭.asIdeal s)
      = quadraticChar (𝓞 F ⧸ 𝔭.asIdeal) (Ideal.Quotient.mk 𝔭.asIdeal s) *
          (quadraticChar (𝓞 F ⧸ 𝔭.asIdeal) (Ideal.Quotient.mk 𝔭.asIdeal s) *
            quadraticChar (𝓞 F ⧸ 𝔭.asIdeal) (Ideal.Quotient.mk 𝔭.asIdeal t)) := by rw [hprod, mul_one]
    _ = quadraticChar (𝓞 F ⧸ 𝔭.asIdeal) (Ideal.Quotient.mk 𝔭.asIdeal s) ^ 2 *
          quadraticChar (𝓞 F ⧸ 𝔭.asIdeal) (Ideal.Quotient.mk 𝔭.asIdeal t) := by ring
    _ = _ := by rw [hss, one_mul]

end QuadFormsKB.Binary.Rel
