import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Binary.RelDensities
import QuadFormsKB.Tamagawa.SquareClassDuality
import QuadFormsKB.Siegel.NFDyadicGood
import QuadFormsKB.Binary.GenusCount

/-!
# Where the genus characters live: trivial at the good primes

$E/F$ quadratic, $\theta$ = `relGen`, $\delta = \theta^2$ = `relD` (integral, `exists_relD_int`), $\psi_v = (\delta, \cdot)_v$ = `genusSym`.
For a normalized lattice $(\mathfrak A, \frac\eta aN)$ ($N\mathfrak A = (a)$, $\eta \in \mathcal O_F^\times$) the genus character at $v$ is $\psi_v(\eta a)$
(`genusSym_normalized`). Here:

* **`even_ordNF_of_inert`:** if $\mathfrak p$ is inert in $E$, then $v_\mathfrak p(N\mathfrak A)$ is even (Mathlib's `Ideal.relNorm_eq_pow_of_isMaximal`:
  $N\mathfrak P = \mathfrak p^{f(\mathfrak P|\mathfrak p)}$, $f = 2$).
* **`genusSym_good`:** at every finite $\mathfrak p \nmid 2\delta$, $\psi_\mathfrak p(\eta a) = 1$. Split $\mathfrak p$: $\delta$ is a square mod $\mathfrak p$
  (`relChar_eq_one_iff_sq`), hence in $F_\mathfrak p$ (Hensel, `Siegel.quadSymbolNF_eq_charNF`), and every symbol $(\delta, \cdot)_\mathfrak p$ is $1$.
  Inert $\mathfrak p$: $\eta a = y\varpi^{2k}$ with $y$ a $\mathfrak p$-unit, and $(\delta, y)_\mathfrak p = 1$ for two units at a non-dyadic place
  (`SqDual.hilbert_units_nondyadic`). ($\mathfrak p \nmid 2\delta$ is never ramified, `relChar_eq_one_iff_sq`.)
* **`prod_genusSym_bad`:** for a totally positive $\eta a$ in a CM extension (the totally positive definite normalized lattices), the
  genus vector is supported on the finite set $S = \{\mathfrak p : \mathfrak p \mid 2\delta\}$ and $\prod_{\mathfrak p \in S}\psi_\mathfrak p(\eta a) = 1$
  (`genusSym_reciprocity`, `genusSym_infinite_iff`). With `genusSym_eq_iff_exists_norm`: **two such lattices lie in the same
  (rational) genus iff their characters agree on $S$** (`sameGenus_iff_bad`), so there are at most $2^{|S|-1}$ genera.

The exact number of genera (Gauss: $2^{t-1}$ over $\mathbb Q$) needs, over $F$, the existence of elements with prescribed Hilbert
symbols (`NFInputs.exists_prescribed_hilbert_nf`, still stated only) and the unit index $[\mathcal O_F^\times : \mathcal O_F^\times \cap N E^\times]$;
not done here.

Sources: Hecke, *Vorlesungen*, §48 [unverified]; Neukirch Ch. VI §4 [unverified]; Serre, *Course*, Ch. III §1.
-/

open NumberField Module IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Binary.Rel

open LocalDensity

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

theorem conjO_relGen : conjO F E (relGen F E) = -relGen F E := by
  apply FaithfulSMul.algebraMap_injective (𝓞 E) E
  rw [algebraMap_conjO, map_neg]
  exact conj_relGen

/-- $\delta$ = `relD` is integral: $\delta = \delta'$ with $\delta' \in \mathcal O_F$ and $\delta' = \theta^2$ in $\mathcal O_E$. -/
theorem exists_relD_int : ∃ δ : 𝓞 F, ((δ : 𝓞 F) : F) = relD F E ∧
    algebraMap (𝓞 F) (𝓞 E) δ = relGen F E ^ 2 := by
  have hint : IsIntegral ℤ (relD F E) := by
    rw [← isIntegral_algebraMap_iff (A := F) (B := E), algebraMap_relD]
    exact (relGen F E).2.pow 2
  refine ⟨⟨relD F E, hint⟩, rfl, ?_⟩
  have key : ∀ x : 𝓞 F, algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) x) =
      algebraMap F E (algebraMap (𝓞 F) F x) := fun x => by
    rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E, ← IsScalarTower.algebraMap_apply (𝓞 F) F E]
  apply FaithfulSMul.algebraMap_injective (𝓞 E) E
  exact (key _).trans (by rw [map_pow]; exact algebraMap_relD)

/-- **Inert primes divide relative norms to even order:** if $\chi_{E/F}(\mathfrak p) = -1$ then $v_\mathfrak p(N_{E/F}\mathfrak A)$ is even. -/
@[kb "neukirch1999" "Ch. I §8 [unverified]"]
theorem even_count_relNorm_of_inert {𝔭 : HeightOneSpectrum (𝓞 F)} (h𝔭 : relChar E 𝔭 = -1)
    {𝔄 : Ideal (𝓞 E)} (h𝔄 : 𝔄 ≠ ⊥) :
    Even (Multiset.count 𝔭.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.relNorm (𝓞 F) 𝔄))) := by
  classical
  obtain ⟨P₀, hall, -, hf⟩ : ∃ P₀ : 𝔭.asIdeal.primesOver (𝓞 E), (∀ P, P = P₀) ∧
      P₀.1.ramificationIdx (𝓞 F) = 1 ∧ P₀.1.inertiaDeg (𝓞 F) = 2 := by
    rcases splitting (Algebra.IsQuadraticExtension.finrank_eq_two F E) 𝔭 with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
    · rw [h] at h𝔭; norm_num at h𝔭
    · exact h
    · rw [h] at h𝔭; norm_num at h𝔭
  have : 𝔭.asIdeal.IsMaximal := 𝔭.isMaximal
  -- the count for a prime factor
  have hprime : ∀ P : Ideal (𝓞 E), Prime P →
      Even (Multiset.count 𝔭.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.relNorm (𝓞 F) P))) := by
    intro P hP
    have hP0 : P ≠ ⊥ := hP.ne_zero
    have : P.IsPrime := (Ideal.prime_iff_isPrime hP0).mp hP
    have : P.IsMaximal := Ideal.IsPrime.isMaximal this hP0
    set 𝔮 := P.under (𝓞 F)
    have : 𝔮.IsMaximal := inferInstance
    rw [Ideal.relNorm_eq_pow_of_isMaximal P 𝔮]
    have h𝔮0 : 𝔮 ≠ ⊥ := by
      intro h0
      apply hP0
      have : P.LiesOver (⊥ : Ideal (𝓞 F)) := ⟨by rw [← h0]⟩
      exact Ideal.eq_bot_of_liesOver_bot (𝓞 F) P
    have h𝔮p : Prime 𝔮 := Ideal.prime_of_isPrime h𝔮0 inferInstance
    rw [UniqueFactorizationMonoid.normalizedFactors_pow, Multiset.count_nsmul,
      UniqueFactorizationMonoid.normalizedFactors_irreducible h𝔮p.irreducible, normalize_eq,
      Multiset.count_singleton]
    by_cases hq : 𝔭.asIdeal = 𝔮
    · rw [if_pos hq]
      have hmem : P ∈ 𝔭.asIdeal.primesOver (𝓞 E) := ⟨inferInstance, ⟨by rw [hq]⟩⟩
      have := hall ⟨P, hmem⟩
      have hPeq : P = P₀.1 := congrArg Subtype.val this
      have : P.inertiaDeg (𝓞 F) = 2 := by rw [hPeq]; exact hf
      rw [show P.inertiaDeg (𝓞 F) = 2 from this]
      exact ⟨1, rfl⟩
    · rw [if_neg hq, mul_zero]; exact ⟨0, rfl⟩
  induction 𝔄 using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl h𝔄
  | h₂ x hx =>
    rw [Ideal.isUnit_iff.mp hx, ← Ideal.one_eq_top, map_one, UniqueFactorizationMonoid.normalizedFactors_one]
    simp
  | h₃ a p ha hp ih =>
    have ha0 : a ≠ ⊥ := fun h => h𝔄 (by rw [h, Ideal.mul_bot])
    have hrp : Ideal.relNorm (𝓞 F) p ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.relNorm_eq_bot_iff]; exact hp.ne_zero
    have hra : Ideal.relNorm (𝓞 F) a ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.relNorm_eq_bot_iff]; exact ha0
    rw [map_mul, UniqueFactorizationMonoid.normalizedFactors_mul hrp hra, Multiset.count_add]
    exact (hprime p hp).add (ih ha0)

/-- **The genus characters are trivial at the good primes:** for $\mathfrak p \nmid 2\delta$ (finite), $N\mathfrak A = (a)$, $\mathfrak A \ne 0$ and
$\eta \in \mathcal O_F^\times$, $\psi_\mathfrak p(\eta a) = 1$. -/
@[kb "hecke1923" "§48 [unverified]; serre1973 Ch. III §1.2"]
theorem genusSym_good {𝔭 : HeightOneSpectrum (𝓞 F)} {δ : 𝓞 F} (hδ : ((δ : 𝓞 F) : F) = relD F E)
    (hδE : algebraMap (𝓞 F) (𝓞 E) δ = relGen F E ^ 2) (h2 : (2 : 𝓞 F) ∉ 𝔭.asIdeal) (hδ𝔭 : δ ∉ 𝔭.asIdeal)
    {𝔄 : Ideal (𝓞 E)} (h𝔄 : 𝔄 ≠ ⊥) {a : 𝓞 F} (ha : Ideal.relNorm (𝓞 F) 𝔄 = Ideal.span {a}) (η : (𝓞 F)ˣ) :
    genusSym E (NFPlace.finite 𝔭) (((η : 𝓞 F) : F) * (a : F)) = 1 := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [Set.singleton_zero, Ideal.span_zero, Ideal.relNorm_eq_bot_iff] at ha
    exact h𝔄 ha
  obtain ⟨h0, hiff⟩ := relChar_eq_one_iff_sq (conjO_relGen (F := F) (E := E)) hδE h2 hδ𝔭
  rcases relChar_trichotomy (E := E) 𝔭 with hsplit | hinert | hram
  · -- split: δ is a square in F_𝔭
    have hc := (charNF_eq_one_iff 𝔭 hδ𝔭).mpr (hiff.mp hsplit)
    rw [← Siegel.quadSymbolNF_eq_charNF 𝔭 h2, Siegel.quadSymbolNF, if_neg hδ𝔭] at hc
    split_ifs at hc with hsq
    · obtain ⟨z, hz⟩ := hsq
      rw [genusSym, NFPlace.hilbert, ← hδ]
      unfold hilbertSymbol
      refine if_pos ⟨1, 0, z, by simp, ?_⟩
      rw [show (algebraMap F (𝔭.adicCompletion F)) ((δ : 𝓞 F) : F) =
        algebraMap (𝔭.adicCompletionIntegers F) (𝔭.adicCompletion F) (NF.ι 𝔭 δ) from rfl, hz]
      ring
  · -- inert: v_𝔭(a) even
    have hev := even_count_relNorm_of_inert hinert h𝔄
    rw [ha, count_normalizedFactors_span_eq_ordNF 𝔭 ha0] at hev
    obtain ⟨k, hk⟩ := hev
    set u : 𝓞 F := NF.unif 𝔭
    have hu00 : u ≠ 0 := by
      intro h
      have := NF.intValuation_unif 𝔭
      rw [show NF.unif 𝔭 = u from rfl, h, map_zero] at this
      exact WithZero.exp_ne_zero this.symm
    have hu0 : (u : F) ≠ 0 :=
      (map_ne_zero_iff (algebraMap (𝓞 F) F) (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mpr hu00
    have hηF : ((η : 𝓞 F) : F) ≠ 0 := fun h => η.ne_zero (by exact_mod_cast h)
    have haF : (a : F) ≠ 0 := by exact_mod_cast ha0
    set y : F := ((η : 𝓞 F) : F) * (a : F) / (u : F) ^ (2 * k)
    have hy0 : y ≠ 0 := div_ne_zero (mul_ne_zero hηF haF) (pow_ne_zero _ hu0)
    have hyval : 𝔭.valuation F y = 1 := by
      have hη1 : 𝔭.intValuation (η : 𝓞 F) = 1 :=
        HeightOneSpectrum.intValuation_eq_one_iff.mpr (fun h => 𝔭.isPrime.ne_top
          (Ideal.eq_top_of_isUnit_mem _ h η.isUnit))
      have ha1 : 𝔭.intValuation a = WithZero.exp (-(Siegel.ordNF 𝔭 a : ℤ)) :=
        HeightOneSpectrum.intValuation_if_neg 𝔭 ha0
      simp only [y, map_div₀, map_mul, map_pow]
      rw [show ((η : 𝓞 F) : F) = algebraMap (𝓞 F) F (η : 𝓞 F) from rfl,
        show (a : F) = algebraMap (𝓞 F) F a from rfl, show (u : F) = algebraMap (𝓞 F) F u from rfl,
        HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
        HeightOneSpectrum.valuation_of_algebraMap, hη1, ha1, NF.intValuation_unif, hk, one_mul,
        ← WithZero.exp_nsmul, div_eq_one_iff_eq (by simp)]
      congr 1
      push_cast
      ring
    have hδval : 𝔭.valuation F (relD F E) = 1 := by
      rw [← hδ, show ((δ : 𝓞 F) : F) = algebraMap (𝓞 F) F δ from rfl, HeightOneSpectrum.valuation_of_algebraMap]
      exact HeightOneSpectrum.intValuation_eq_one_iff.mpr hδ𝔭
    have hsym := SqDual.hilbert_units_nondyadic 𝔭 h2 (relD F E) y hδval hyval
    have hsplit : ((η : 𝓞 F) : F) * (a : F) = y * ((u : F) ^ k) ^ 2 := by
      simp only [y]; field_simp; ring
    rw [hsplit, genusSym_mul _ hy0 (pow_ne_zero _ (pow_ne_zero _ hu0))]
    change (NFPlace.finite 𝔭).hilbert (relD F E) y * (NFPlace.finite 𝔭).hilbert (relD F E) _ = 1
    rw [hsym, NFPlace.hilbert_eq_one_of_norm _ ((u : F) ^ k) 0 (by ring), one_mul]
  · exact absurd hram h0

/-! ### CM: genus vectors on the bad primes, and at most $2^{|S|-1}$ genera -/

section CMCount

variable [IsTotallyReal F] [IsTotallyComplex E]

/-- **Outside $S \supseteq \{\mathfrak p \mid 2\delta\}$ the genus characters of a totally positive normalized value are trivial** (every infinite
place by `genusSym_infinite_iff`, every finite $\mathfrak p \notin S$ by `genusSym_good`). -/
theorem genusSym_eq_one_of_not_mem {δ : 𝓞 F} (hδ : ((δ : 𝓞 F) : F) = relD F E)
    (hδE : algebraMap (𝓞 F) (𝓞 E) δ = relGen F E ^ 2) {S : Finset (HeightOneSpectrum (𝓞 F))}
    (hS : ∀ 𝔭 : HeightOneSpectrum (𝓞 F), 2 * δ ∈ 𝔭.asIdeal → 𝔭 ∈ S)
    {𝔄 : Ideal (𝓞 E)} (h𝔄 : 𝔄 ≠ ⊥) {a : 𝓞 F} (ha : Ideal.relNorm (𝓞 F) 𝔄 = Ideal.span {a}) (η : (𝓞 F)ˣ)
    (hpos : ∀ w : Siegel.RealPlace F, 0 < Siegel.realEmb w (((η : 𝓞 F) : F) * (a : F)))
    (v : NFPlace F) (hv : ∀ 𝔭 ∈ S, v ≠ NFPlace.finite 𝔭) :
    genusSym E v (((η : 𝓞 F) : F) * (a : F)) = 1 := by
  cases v with
  | infinite w =>
    have hw : w.IsReal := IsTotallyReal.isReal w
    have hx : ((η : 𝓞 F) : F) * (a : F) ≠ 0 := fun h => by
      have := hpos ⟨w, hw⟩; rw [h, map_zero] at this; exact lt_irrefl _ this
    exact (genusSym_infinite_iff ⟨w, hw⟩ hx).mpr (hpos ⟨w, hw⟩)
  | finite 𝔭 =>
    have hn : 2 * δ ∉ 𝔭.asIdeal := fun h => hv 𝔭 (hS 𝔭 h) rfl
    exact genusSym_good hδ hδE (fun h => hn (𝔭.asIdeal.mul_mem_right _ h))
      (fun h => hn (𝔭.asIdeal.mul_mem_left _ h)) h𝔄 ha η

/-- $\psi_v$ as a sign in $\mathbb Z^\times$. -/
def signOf (z : ℤ) : ℤˣ := if z = 1 then 1 else -1

theorem coe_signOf {z : ℤ} (hz : z = 1 ∨ z = -1) : ((signOf z : ℤˣ) : ℤ) = z := by
  unfold signOf; rcases hz with rfl | rfl <;> simp

/-- **The genus vector on $S$ has product one:** $\prod_{\mathfrak p \in S}\psi_\mathfrak p(\eta a) = 1$ for a totally positive normalized value
(the product formula `genusSym_reciprocity`, all other characters being trivial). -/
@[kb "hecke1923" "§48 [unverified]; cf. prod_formChar_eq_one"]
theorem prod_genusSym_bad {δ : 𝓞 F} (hδ : ((δ : 𝓞 F) : F) = relD F E)
    (hδE : algebraMap (𝓞 F) (𝓞 E) δ = relGen F E ^ 2) {S : Finset (HeightOneSpectrum (𝓞 F))}
    (hS : ∀ 𝔭 : HeightOneSpectrum (𝓞 F), 2 * δ ∈ 𝔭.asIdeal → 𝔭 ∈ S)
    {𝔄 : Ideal (𝓞 E)} (h𝔄 : 𝔄 ≠ ⊥) {a : 𝓞 F} (ha : Ideal.relNorm (𝓞 F) 𝔄 = Ideal.span {a}) (η : (𝓞 F)ˣ)
    (hpos : ∀ w : Siegel.RealPlace F, 0 < Siegel.realEmb w (((η : 𝓞 F) : F) * (a : F))) :
    ∏ 𝔭 ∈ S, signOf (genusSym E (NFPlace.finite 𝔭) (((η : 𝓞 F) : F) * (a : F))) = 1 := by
  classical
  set x := ((η : 𝓞 F) : F) * (a : F)
  have hx : x ≠ 0 := by
    have hηF : ((η : 𝓞 F) : F) ≠ 0 := fun h => η.ne_zero (by exact_mod_cast h)
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [Set.singleton_zero, Ideal.span_zero, Ideal.relNorm_eq_bot_iff] at ha
      exact h𝔄 ha
    exact mul_ne_zero hηF (by exact_mod_cast ha0)
  obtain ⟨-, hev⟩ := genusSym_reciprocity (E := E) hx
  set f : HeightOneSpectrum (𝓞 F) → ℤˣ := fun 𝔭 => signOf (genusSym E (NFPlace.finite 𝔭) x)
  have hT : {v : NFPlace F | genusSym E v x = -1} =
      ((S.filter fun 𝔭 => genusSym E (NFPlace.finite 𝔭) x = -1).image NFPlace.finite : Set (NFPlace F)) := by
    ext v
    simp only [Set.mem_setOf_eq, Finset.coe_image, Finset.coe_filter, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · intro hv
      by_contra hno
      have h1 := genusSym_eq_one_of_not_mem hδ hδE hS h𝔄 ha η hpos v (by
        rintro 𝔭 h𝔭 rfl
        exact hno ⟨𝔭, ⟨h𝔭, hv⟩, rfl⟩)
      rw [h1] at hv; norm_num at hv
    · rintro ⟨𝔭, ⟨-, h𝔭⟩, rfl⟩; exact h𝔭
  rw [hT, Set.ncard_coe_finset, Finset.card_image_of_injective _ (fun _ _ h => by cases h; rfl)] at hev
  rw [← Finset.prod_filter_mul_prod_filter_not S (fun 𝔭 => genusSym E (NFPlace.finite 𝔭) x = -1)]
  rw [Finset.prod_congr rfl (fun 𝔭 h𝔭 => by
      rw [(Finset.mem_filter.mp h𝔭).2]; rfl : ∀ 𝔭 ∈ S.filter (fun 𝔭 => genusSym E (NFPlace.finite 𝔭) x = -1),
        signOf (genusSym E (NFPlace.finite 𝔭) x) = -1),
    Finset.prod_congr rfl (fun 𝔭 h𝔭 => by
      have h1 := (Finset.mem_filter.mp h𝔭).2
      rcases genusSym_eq_one_or (E := E) (NFPlace.finite 𝔭) x with h | h
      · rw [h]; rfl
      · exact absurd h h1 : ∀ 𝔭 ∈ S.filter (fun 𝔭 => ¬ genusSym E (NFPlace.finite 𝔭) x = -1),
        signOf (genusSym E (NFPlace.finite 𝔭) x) = 1),
    Finset.prod_const, Finset.prod_const_one, mul_one, hev.neg_one_pow]

/-- **Same genus iff same characters on $S$** (two totally positive normalized values $x = \eta a$, $x' = \eta'a'$): $\psi_v(x) = \psi_v(x')$
at every place iff at every $\mathfrak p \in S$. With `genusSym_eq_iff_exists_norm`, the (rational) genus of a totally positive
normalized lattice is determined by its genus vector on $S$. -/
@[kb "hecke1923" "§48 [unverified]; cf. sameGenus_iff_formChar_eq"]
theorem sameGenus_iff_bad {δ : 𝓞 F} (hδ : ((δ : 𝓞 F) : F) = relD F E)
    (hδE : algebraMap (𝓞 F) (𝓞 E) δ = relGen F E ^ 2) {S : Finset (HeightOneSpectrum (𝓞 F))}
    (hS : ∀ 𝔭 : HeightOneSpectrum (𝓞 F), 2 * δ ∈ 𝔭.asIdeal → 𝔭 ∈ S)
    {𝔄 𝔄' : Ideal (𝓞 E)} (h𝔄 : 𝔄 ≠ ⊥) (h𝔄' : 𝔄' ≠ ⊥) {a a' : 𝓞 F}
    (ha : Ideal.relNorm (𝓞 F) 𝔄 = Ideal.span {a}) (ha' : Ideal.relNorm (𝓞 F) 𝔄' = Ideal.span {a'})
    (η η' : (𝓞 F)ˣ)
    (hpos : ∀ w : Siegel.RealPlace F, 0 < Siegel.realEmb w (((η : 𝓞 F) : F) * (a : F)))
    (hpos' : ∀ w : Siegel.RealPlace F, 0 < Siegel.realEmb w (((η' : 𝓞 F) : F) * (a' : F))) :
    (∀ v : NFPlace F, genusSym E v (((η : 𝓞 F) : F) * (a : F)) = genusSym E v (((η' : 𝓞 F) : F) * (a' : F))) ↔
      ∀ 𝔭 ∈ S, genusSym E (NFPlace.finite 𝔭) (((η : 𝓞 F) : F) * (a : F)) =
        genusSym E (NFPlace.finite 𝔭) (((η' : 𝓞 F) : F) * (a' : F)) := by
  refine ⟨fun h 𝔭 _ => h _, fun h v => ?_⟩
  by_cases hv : ∃ 𝔭 ∈ S, v = NFPlace.finite 𝔭
  · obtain ⟨𝔭, h𝔭, rfl⟩ := hv; exact h 𝔭 h𝔭
  · push Not at hv
    rw [genusSym_eq_one_of_not_mem hδ hδE hS h𝔄 ha η hpos v hv,
      genusSym_eq_one_of_not_mem hδ hδE hS h𝔄' ha' η' hpos' v hv]

/-- **At most $2^{|S|-1}$ genera:** for any set $X$ of totally positive normalized values $\eta a$, the number of distinct genus
character vectors $(\psi_v(x))_v$, $x \in X$ (= the number of rational genera met by $X$) is at most $2^{|S|-1}$,
$S \supseteq \{\mathfrak p \mid 2\delta\}$ nonempty. -/
@[kb "hecke1923" "§48 [unverified]; cf. card_genera"]
theorem ncard_genera_le {δ : 𝓞 F} (hδ : ((δ : 𝓞 F) : F) = relD F E)
    (hδE : algebraMap (𝓞 F) (𝓞 E) δ = relGen F E ^ 2) {S : Finset (HeightOneSpectrum (𝓞 F))}
    (hS : ∀ 𝔭 : HeightOneSpectrum (𝓞 F), 2 * δ ∈ 𝔭.asIdeal → 𝔭 ∈ S) (hSne : S.Nonempty) (X : Set F)
    (hX : ∀ x ∈ X, ∃ (𝔄 : Ideal (𝓞 E)) (a : 𝓞 F) (η : (𝓞 F)ˣ), 𝔄 ≠ ⊥ ∧
      Ideal.relNorm (𝓞 F) 𝔄 = Ideal.span {a} ∧ x = ((η : 𝓞 F) : F) * (a : F) ∧
      ∀ w : Siegel.RealPlace F, 0 < Siegel.realEmb w x) :
    ((fun x v => genusSym E v x) '' X).ncard ≤ 2 ^ (S.card - 1) := by
  classical
  have : Nonempty S := ⟨⟨hSne.choose, hSne.choose_spec⟩⟩
  let g : (NFPlace F → ℤ) → {e : S → ℤˣ // ∏ i, e i = 1} := fun φ =>
    if h : ∏ i : S, signOf (φ (NFPlace.finite i.1)) = 1 then ⟨fun i => signOf (φ (NFPlace.finite i.1)), h⟩
    else ⟨fun _ => 1, by simp⟩
  have hcard := card_signVec_prod_one (ι := S)
  rw [Fintype.card_coe] at hcard
  rw [← hcard, ← Set.ncard_univ]
  refine Set.ncard_le_ncard_of_injOn g (fun _ _ => Set.mem_univ _) ?_ Set.finite_univ
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
  obtain ⟨𝔄, a, η, h𝔄, ha, rfl, hpos⟩ := hX x hx
  obtain ⟨𝔄', a', η', h𝔄', ha', rfl, hpos'⟩ := hX y hy
  have hp1 := prod_genusSym_bad hδ hδE hS h𝔄 ha η hpos
  have hp2 := prod_genusSym_bad hδ hδE hS h𝔄' ha' η' hpos'
  rw [← Finset.prod_coe_sort] at hp1 hp2
  simp only [g, dif_pos hp1, dif_pos hp2, Subtype.mk.injEq] at hxy
  funext v
  refine (sameGenus_iff_bad hδ hδE hS h𝔄 h𝔄' ha ha' η η' hpos hpos').mpr (fun 𝔭 h𝔭 => ?_) v
  have := congrFun hxy ⟨𝔭, h𝔭⟩
  have e1 := coe_signOf (genusSym_eq_one_or (E := E) (NFPlace.finite 𝔭) (((η : 𝓞 F) : F) * (a : F)))
  have e2 := coe_signOf (genusSym_eq_one_or (E := E) (NFPlace.finite 𝔭) (((η' : 𝓞 F) : F) * (a' : F)))
  rw [← e1, ← e2, this]

end CMCount

end QuadFormsKB.Binary.Rel
