/-
# Möbius inversion over the ideals of $\mathcal{O}_F$

$F$ a number field. The Möbius function of the integral ideals of $\mathcal{O}_F$ is supported on squarefree ideals, and a
squarefree ideal is $\mathfrak d_S = \prod_{\mathfrak p\in S}\mathfrak p$ for a unique finite set $S$ of nonzero primes (`sqfIdeal`,
`sqfIdeal_injective`). So we index the Möbius sum by $S$, with $\mu(\mathfrak d_S) = (-1)^{|S|}$:

* `sqfIdeal_dvd_iff`: $\mathfrak d_S \mid \mathfrak c \iff \mathfrak p \mid \mathfrak c$ for all $\mathfrak p \in S$ (distinct maximal ideals are coprime);
* **`hasSum_moebius`** (Möbius inversion): for $\mathfrak c \ne 0$ and $a \in \mathbb{C}$,
  $$\sum_{S:\ \mathfrak d_S \mid \mathfrak c}(-1)^{|S|}a = [\mathfrak c = \mathcal{O}_F]\,a,$$
  i.e. $\sum_{\mathfrak d\mid\mathfrak c}\mu(\mathfrak d) = [\mathfrak c = 1]$: the sum runs over the subsets of the finite set of primes dividing
  $\mathfrak c$, and $\sum_{S\subseteq P}(-1)^{|S|} = [P = \emptyset]$; $P = \emptyset$ iff $\mathfrak c = \mathcal{O}_F$;
* `summable_absNorm_sqfIdeal`: $\sum_SN(\mathfrak d_S)^{-s} < \infty$ for $s > 1$ (a subseries of $\zeta_F(s)$, `NFEuler.summable_absNorm_rpow`).

Sources: Hecke, *Vorlesungen über die Theorie der algebraischen Zahlen* (1923), §§36–37 (ideal theory, the Möbius function of
ideals) [unverified]; Neukirch, *Algebraic Number Theory*, Ch. VII §5 [unverified].
-/
import QuadFormsKB.Analysis.NFEulerProduct

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

namespace QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F]

/-- **The squarefree ideal of a finite set of primes**: $\mathfrak d_S = \prod_{\mathfrak p\in S}\mathfrak p$. -/
@[kb "hecke1923" "§37, squarefree ideals and the Möbius function of ideals [unverified]"]
noncomputable def sqfIdeal (S : Finset (HeightOneSpectrum (𝓞 F))) : Ideal (𝓞 F) := ∏ 𝔭 ∈ S, 𝔭.asIdeal

lemma sqfIdeal_ne_bot (S : Finset (HeightOneSpectrum (𝓞 F))) : sqfIdeal S ≠ ⊥ := by
  rw [sqfIdeal, ← Ideal.zero_eq_bot, Ne, Finset.prod_eq_zero_iff]
  rintro ⟨𝔭, -, h⟩
  exact 𝔭.ne_bot (by rw [h, Ideal.zero_eq_bot])

/-- $\mathfrak p \in S \iff \mathfrak d_S \subseteq \mathfrak p$. -/
lemma mem_iff_sqfIdeal_le {S : Finset (HeightOneSpectrum (𝓞 F))} {𝔭 : HeightOneSpectrum (𝓞 F)} :
    𝔭 ∈ S ↔ sqfIdeal S ≤ 𝔭.asIdeal := by
  constructor
  · intro h
    exact Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun 𝔮 : HeightOneSpectrum (𝓞 F) => 𝔮.asIdeal) h)
  · intro h
    obtain ⟨𝔮, h𝔮, hle⟩ := (Ideal.IsPrime.prod_le 𝔭.isPrime).mp h
    have : 𝔮.asIdeal = 𝔭.asIdeal := 𝔮.isMaximal.eq_of_le 𝔭.isPrime.ne_top hle
    rwa [← HeightOneSpectrum.ext this]

/-- **$S \mapsto \mathfrak d_S$ is injective** (unique factorization for squarefree ideals). -/
lemma sqfIdeal_injective : Function.Injective (sqfIdeal (F := F)) := by
  intro S T h
  ext 𝔭
  rw [mem_iff_sqfIdeal_le, mem_iff_sqfIdeal_le, h]

/-- **$\mathfrak d_S \mid \mathfrak c$ iff every $\mathfrak p \in S$ divides $\mathfrak c$** (distinct maximal ideals are coprime). -/
lemma sqfIdeal_dvd_iff {S : Finset (HeightOneSpectrum (𝓞 F))} {𝔠 : Ideal (𝓞 F)} :
    sqfIdeal S ∣ 𝔠 ↔ ∀ 𝔭 ∈ S, 𝔭.asIdeal ∣ 𝔠 := by
  constructor
  · intro h 𝔭 h𝔭
    exact (Finset.dvd_prod_of_mem (fun 𝔮 : HeightOneSpectrum (𝓞 F) => 𝔮.asIdeal) h𝔭).trans h
  · intro h
    refine Finset.prod_dvd_of_coprime ?_ h
    intro 𝔭 _ 𝔮 _ hne
    refine Ideal.isCoprime_iff_sup_eq.mpr (Ideal.IsMaximal.coprime_of_ne 𝔭.isMaximal 𝔮.isMaximal ?_)
    exact fun h' => hne (HeightOneSpectrum.ext h')

/-- **The finite set of primes dividing $\mathfrak c \ne 0$.** -/
noncomputable def primesOf {𝔠 : Ideal (𝓞 F)} (h𝔠 : 𝔠 ≠ ⊥) : Finset (HeightOneSpectrum (𝓞 F)) :=
  (Ideal.finite_factors (by rwa [Ideal.zero_eq_bot])).toFinset

lemma mem_primesOf {𝔠 : Ideal (𝓞 F)} (h𝔠 : 𝔠 ≠ ⊥) {𝔭 : HeightOneSpectrum (𝓞 F)} :
    𝔭 ∈ primesOf h𝔠 ↔ 𝔭.asIdeal ∣ 𝔠 := by
  rw [primesOf, Set.Finite.mem_toFinset]; rfl

/-- **$\mathfrak c \ne 0$ has no prime factor iff $\mathfrak c = \mathcal{O}_F$.** -/
lemma primesOf_eq_empty_iff {𝔠 : Ideal (𝓞 F)} (h𝔠 : 𝔠 ≠ ⊥) : primesOf h𝔠 = ∅ ↔ 𝔠 = ⊤ := by
  constructor
  · intro h
    by_contra htop
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal 𝔠 htop
    have hMb : M ≠ ⊥ := fun hb => h𝔠 (le_bot_iff.mp (hb ▸ hle))
    set 𝔭 : HeightOneSpectrum (𝓞 F) := ⟨M, hM.isPrime, hMb⟩
    have : 𝔭 ∈ primesOf h𝔠 := (mem_primesOf h𝔠).mpr (Ideal.dvd_iff_le.mpr hle)
    rw [h] at this
    exact Finset.notMem_empty _ this
  · rintro rfl
    refine Finset.eq_empty_of_forall_notMem fun 𝔭 h𝔭 => ?_
    have := Ideal.le_of_dvd ((mem_primesOf h𝔠).mp h𝔭)
    exact 𝔭.isPrime.ne_top (top_le_iff.mp this)

open Classical in
/-- **Möbius inversion over the ideals of $\mathcal{O}_F$**: for $\mathfrak c \ne 0$ and $a \in \mathbb{C}$,
$$\sum_{S}[\mathfrak d_S \mid \mathfrak c]\,(-1)^{|S|}\,a = [\mathfrak c = \mathcal{O}_F]\,a,$$
the sum over finite sets $S$ of nonzero primes (finitely many nonzero terms). Equivalently
$\sum_{\mathfrak d\mid\mathfrak c}\mu(\mathfrak d) = [\mathfrak c = 1]$. -/
@[kb "hecke1923" "§37, Möbius inversion over ideals [unverified]"]
theorem hasSum_moebius {𝔠 : Ideal (𝓞 F)} (h𝔠 : 𝔠 ≠ ⊥) (a : ℂ) :
    HasSum (fun S : Finset (HeightOneSpectrum (𝓞 F)) =>
      if sqfIdeal S ∣ 𝔠 then (-1 : ℂ) ^ S.card * a else 0) (if 𝔠 = ⊤ then a else 0) := by
  set P := primesOf h𝔠
  have hsub : ∀ S : Finset (HeightOneSpectrum (𝓞 F)), sqfIdeal S ∣ 𝔠 ↔ S ∈ P.powerset := by
    intro S
    rw [sqfIdeal_dvd_iff, Finset.mem_powerset]
    exact ⟨fun h 𝔭 h𝔭 => (mem_primesOf h𝔠).mpr (h 𝔭 h𝔭), fun h 𝔭 h𝔭 => (mem_primesOf h𝔠).mp (h h𝔭)⟩
  have h0 : ∀ S ∉ P.powerset, (if sqfIdeal S ∣ 𝔠 then (-1 : ℂ) ^ S.card * a else 0) = 0 := by
    intro S hS
    rw [if_neg (fun h => hS ((hsub S).mp h))]
  convert (hasSum_sum_of_ne_finset_zero h0 : HasSum _ _) using 1
  rw [Finset.sum_congr rfl fun S hS => if_pos ((hsub S).mpr hS), ← Finset.sum_mul]
  have hpow : ∑ S ∈ P.powerset, (-1 : ℂ) ^ S.card = ((∑ S ∈ P.powerset, (-1 : ℤ) ^ S.card : ℤ) : ℂ) := by
    push_cast; rfl
  rw [hpow, Finset.sum_powerset_neg_one_pow_card]
  by_cases h : 𝔠 = ⊤
  · rw [if_pos h, if_pos ((primesOf_eq_empty_iff h𝔠).mpr h)]; simp
  · rw [if_neg h, if_neg (fun h' => h ((primesOf_eq_empty_iff h𝔠).mp h'))]; simp

/-- **$\sum_SN(\mathfrak d_S)^{-s} < \infty$ for $s > 1$** (a subseries of $\zeta_F(s) = \sum_{\mathfrak a}N\mathfrak a^{-s}$). -/
theorem summable_absNorm_sqfIdeal {s : ℝ} (hs : 1 < s) :
    Summable fun S : Finset (HeightOneSpectrum (𝓞 F)) => (Ideal.absNorm (sqfIdeal S) : ℝ) ^ (-s) :=
  (QuadFormsKB.NFEuler.summable_absNorm_rpow hs).comp_injective sqfIdeal_injective

end QuadFormsKB.HilbertModular
