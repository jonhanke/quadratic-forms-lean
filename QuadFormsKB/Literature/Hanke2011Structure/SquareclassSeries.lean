/-
# Hanke 2011, §4: normalization, distinguished squareclasses and formal Dirichlet series

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (bib key `hanke2011structure`), §4, pp. 14–20.

Global (idelic) forms of the local definitions in `Squareclasses.lean`, for a number field $F$ and the canonical family
$P = \{\pi_{\mathfrak p}\}$ of uniformizing squareclasses $\pi_{\mathfrak p} = [\varpi_{\mathfrak p}]$ (`unifSqCl`, Remark 4.4: the family is
fixed once and for all):

* `hOrd n v` $= \operatorname{ord}_{\mathfrak p}(h_n)$ ($0$ for $n$ even, $\operatorname{ord}_{\mathfrak p}(2)$ for $n$ odd; Lemma 2.5);
  **Definition 4.1** (`IsNormalizedAdelic`): $I(\widetilde S) = h_n$; **Definition 4.3** (`normalizeAdelic`):
  $\widetilde S = S\prod_{\mathfrak p}\pi_{\mathfrak p}^{\operatorname{ord}_{\mathfrak p}(h_n/I(S))}$, with the local compatibility
  $(\widetilde S)_{\mathfrak p} = \widetilde{S_{\mathfrak p}}$ (`comp_normalizeAdelic`) and $I(\widetilde S) = h_n$
  (`isNormalizedAdelic_normalizeAdelic`).
* **Remark 4.10** (`remark_4_10_global`): $\widetilde{S\,T^2} = \widetilde S$; for a distinguished family,
  $\widetilde{\lambda(\mathfrak a\mathfrak b^2)} = \widetilde{\lambda(\mathfrak a)}$ (`DistinguishedFamily.normalize_mul_sq`), the map
  $\widetilde\lambda$ of diagram (13).
* **Definition 4.9** (`DistinguishedFamily`): a homomorphism $\lambda$ from the monoid of nonzero ideals of $\mathcal O_F$ to
  $\mathrm{SqCl}(\mathbb A_{F,f}^\times, U_f)$ with $I(\lambda(\mathfrak a)) = \mathfrak a$, i.e.
  $\operatorname{ord}_{\mathfrak p}(\lambda(\mathfrak a)) = \operatorname{ord}_{\mathfrak p}(\mathfrak a)$ for every $\mathfrak p$.
* **Definition 4.12** (`assocDirichlet`): the coefficients $a \mapsto X(\lambda(\mathfrak a))$ of the formal Dirichlet series
  $D^T_{X,\lambda}(s) = \sum_{\mathfrak a\in I^T(\mathcal O_F)}X(\lambda(\mathfrak a))\,\mathfrak a^{-s}$ (a formal series in the symbols
  $\mathfrak a^{-s}$, i.e. a function on the nonzero ideals).
* **Corollaries 4.13 and 4.15, coefficientwise** (`cor_4_13_coeff`, `cor_4_15_coeff`), for arbitrary local mass data
  (`LocalMassData`: finite sets of local genera at each prime and local squareclass, with Hasse invariants, local
  densities and generic densities), at the primes of a finite set $T$ (Theorem 4.8 for $S = \lambda(\mathfrak a)$, the
  normalized class depending only on the squarefree part $\mathfrak t$ of $\mathfrak a = \mathfrak t\mathfrak b^2$). As in
  `StructureTheorem.lean`, the true sets of local genera are not constructed here.

*Clarification* (Corollary 4.13): the paper says that
$D^{\mathbb S}_{A^*,\lambda;n}$ and $D^{\mathbb S}_{B^*,\lambda;n}$ "are both given as Euler products". The coefficient
$A^*(\lambda(\mathfrak a)) = \prod_{\mathfrak p}A^*_{\mathfrak p;n}(\lambda(\mathfrak a)_{\mathfrak p})$ is multiplicative in $\mathfrak a$ only when
$A^*_{\mathfrak p;n}(\lambda(\mathfrak a)_{\mathfrak p})$ depends on $\mathfrak a$ only through $\operatorname{ord}_{\mathfrak p}(\mathfrak a)$; in general
$\lambda(\mathfrak a)_{\mathfrak p}$ also depends on the unit classes $\lambda(\mathfrak q)_{\mathfrak p}$ for $\mathfrak q \ne \mathfrak p$. For $n$ odd this
holds for $A^*$ at every $\mathfrak p$ and for $B^*$ at $\mathfrak p \nmid 2$ (Theorem 5.7, Remark 5.8), but for $n \equiv 3 \pmod 4$
and $\mathfrak p \mid 2$, $B^*_{\mathfrak p}(uS) = (u,u)_{\mathfrak p}B^*_{\mathfrak p}(S)$: for $F = \mathbb Q$, $n = 3$, $\lambda(a\mathbb Z) = |a|$ the
factor at $2$ depends on $a/2^{\operatorname{ord}_2a} \bmod 4$ (paper 7, `Hanke2011Ternary.globalB`, which handles it by a
global sign).
-/
import QuadFormsKB.Literature.Hanke2011Structure.HessianSquareclass
import QuadFormsKB.Literature.Hanke2011Structure.StructureTheorem

namespace QuadFormsKB.Hanke2011Structure

open IsDedekindDomain NumberField WithZero
open scoped nonZeroDivisors

noncomputable section

variable {F : Type} [Field F] [NumberField F]

/-! ### The canonical uniformizing family and $\operatorname{ord}_{\mathfrak p}(h_n)$ -/

section Uniformizer

variable (v : HeightOneSpectrum (𝓞 F))

/-- The uniformizer $\varpi_{\mathfrak p}$ (`Lattices.unifF`) as a unit of $F_{\mathfrak p}$. -/
def unifUnit : (v.adicCompletion F)ˣ :=
  Units.mk0 (algebraMap F (v.adicCompletion F) (Lattices.unifF v)) (by simpa using Lattices.unifF_ne_zero v)

/-- **The canonical uniformizing squareclass** $\pi_{\mathfrak p} = [\varpi_{\mathfrak p}]$ (Definition 4.2; the family
$P = \{\pi_{\mathfrak p}\}$ is fixed once and for all, Remark 4.4). -/
@[kb "hanke2011structure" "Def. 4.2, p. 15; Rem. 4.4, p. 15 (the family P)"]
def unifSqCl : LocalSqCl v := SqCl.mk (unifUnit v)

theorem isUniformizing_unifSqCl : IsUniformizing (localOrd v) (localUnits_le_ker v) (unifSqCl v) := by
  unfold IsUniformizing unifSqCl
  rw [SqCl.ordZ_mk]
  change -log (Valued.v (algebraMap F (v.adicCompletion F) (Lattices.unifF v))) = 1
  have h := Lattices.valued_unifF_zpow v 1
  rw [zpow_one] at h
  rw [h, log_exp]
  rfl

/-- **$\operatorname{ord}_{\mathfrak p}(h_n)$** (Lemma 2.5): $h_n = \mathcal O_F$ for $n$ even, $h_n = 2\mathcal O_F$ for $n$ odd. -/
def hOrd (n : ℕ) : ℤ :=
  if Even n then 0 else
    Multiplicative.toAdd (localOrd v (Units.mk0 (algebraMap F (v.adicCompletion F) 2) (by simp)))

theorem mem_localUnitSqCl_of_ordZ {s : LocalSqCl v} (hs : SqCl.ordZ (localOrd v) (localUnits_le_ker v) s = 0) :
    s ∈ localUnitSqCl F v := by
  obtain ⟨x, rfl⟩ := SqCl.mk_surjective s
  rw [SqCl.ordZ_mk] at hs
  refine mk_mem_localUnitSqCl ((mem_localUnits_iff_ord v).mpr ?_)
  exact congrArg Multiplicative.ofAdd hs

theorem eventually_hOrd_eq_zero (n : ℕ) : ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, hOrd w n = 0 := by
  filter_upwards [eventually_algebraMap_mem_localUnits (two_ne_zero : (2 : F) ≠ 0)] with w hw
  unfold hOrd
  split_ifs
  · rfl
  · rw [(mem_localUnits_iff_ord w).mp hw]; rfl

end Uniformizer

/-! ### Definitions 4.1 and 4.3, Remark 4.10: global normalization -/

section Normalization

variable (n : ℕ)

/-- **Definition 4.1** (p. 15): $S$ is *normalized* for $n$ if $I(S) = h_n$, i.e.
$\operatorname{ord}_{\mathfrak p}(S) = \operatorname{ord}_{\mathfrak p}(h_n)$ for every $\mathfrak p$. -/
@[kb "hanke2011structure" "Def. 4.1, p. 15 (global)"]
def IsNormalizedAdelic (S : AdelicSqCl F) : Prop := ∀ v, adelicOrd v S = hOrd v n

theorem eventually_normalize_mem (S : AdelicSqCl F) :
    ∀ᶠ v in Filter.cofinite,
      normalize (localOrd v) (localUnits_le_ker v) (unifSqCl v) (hOrd v n) (AdelicSqCl.comp v S) ∈
        localUnitSqCl F v := by
  have hS : ∀ᶠ v in Filter.cofinite, adelicOrd v S = 0 := by
    have := supp_finite S
    rw [Filter.eventually_cofinite]
    simpa [supp] using this
  filter_upwards [hS, eventually_hOrd_eq_zero n] with v hv hh
  refine mem_localUnitSqCl_of_ordZ v ?_
  have := ordZ_normalize (isUniformizing_unifSqCl v) (hOrd v n) (AdelicSqCl.comp v S)
  rw [IsNormalized] at this
  rw [this, hh]

/-- **Definition 4.3** (p. 15): the *normalized squareclass*
$\widetilde S = S\cdot\prod_{\mathfrak p}\pi_{\mathfrak p}^{\operatorname{ord}_{\mathfrak p}(h_n/I(S))}$, built componentwise from the local
normalization (`normalize`) with the canonical family $P$. -/
@[kb "hanke2011structure" "Def. 4.3, p. 15 (global)"]
def normalizeAdelic (S : AdelicSqCl F) : AdelicSqCl F :=
  AdelicSqCl.ofLocal (fun v => normalize (localOrd v) (localUnits_le_ker v) (unifSqCl v) (hOrd v n)
    (AdelicSqCl.comp v S)) (eventually_normalize_mem n S)

/-- **Local compatibility** (Definition 4.3): $(\widetilde S)_{\mathfrak p} = \widetilde{S_{\mathfrak p}}$. -/
@[kb "hanke2011structure" "Def. 4.3, p. 15 (local compatibility)"]
theorem comp_normalizeAdelic (S : AdelicSqCl F) (v : HeightOneSpectrum (𝓞 F)) :
    AdelicSqCl.comp v (normalizeAdelic n S) =
      normalize (localOrd v) (localUnits_le_ker v) (unifSqCl v) (hOrd v n) (AdelicSqCl.comp v S) :=
  AdelicSqCl.comp_ofLocal _ _ v

/-- $\widetilde S$ is normalized: $I(\widetilde S) = h_n$ (Definition 4.3). -/
theorem isNormalizedAdelic_normalizeAdelic (S : AdelicSqCl F) : IsNormalizedAdelic n (normalizeAdelic n S) :=
  fun v => by
    rw [adelicOrd, comp_normalizeAdelic]
    exact ordZ_normalize (isUniformizing_unifSqCl v) _ _

/-- **Remark 4.10** (global form, p. 19): $\widetilde{S\,T^2} = \widetilde S$. -/
@[kb "hanke2011structure" "Rem. 4.10, p. 18-19 (global)"]
theorem remark_4_10_global (S T : AdelicSqCl F) : normalizeAdelic n (S * T ^ 2) = normalizeAdelic n S :=
  AdelicSqCl.ext fun v => by
    rw [comp_normalizeAdelic, comp_normalizeAdelic, map_mul, map_pow]
    exact normalize_mul_sq (isUniformizing_unifSqCl v) rfl (localOrd_gen v) _ _ _

end Normalization

/-! ### Definition 4.9: distinguished families -/

/-- The exponent $\operatorname{ord}_{\mathfrak p}(\mathfrak a)$ of $\mathfrak p$ in the ideal $\mathfrak a$ (its multiplicity in the
factorization of $\mathfrak a$). -/
def idealOrd (v : HeightOneSpectrum (𝓞 F)) (a : Ideal (𝓞 F)) : ℤ :=
  ((UniqueFactorizationMonoid.normalizedFactors a).count v.asIdeal : ℤ)

variable (F) in
/-- **Definition 4.9** (Distinguished squareclasses, p. 18): a homomorphism $\lambda : I(\mathcal O_F) \to
\mathrm{SqCl}(\mathbb A_{F,f}^\times, U_f)$ from the monoid of nonzero ideals with $I(\lambda(\mathfrak a)) = \mathfrak a$, i.e.
$\operatorname{ord}_{\mathfrak p}(\lambda(\mathfrak a)) = \operatorname{ord}_{\mathfrak p}(\mathfrak a)$ for every prime $\mathfrak p$. Fields: `toHom`, `ord_eq`. -/
@[kb "hanke2011structure" "Def. 4.9, p. 18"]
structure DistinguishedFamily where
  /-- the homomorphism $\mathfrak a \mapsto \lambda(\mathfrak a)$ -/
  toHom : (Ideal (𝓞 F))⁰ →* AdelicSqCl F
  /-- $I(\lambda(\mathfrak a)) = \mathfrak a$, prime by prime -/
  ord_eq : ∀ (a : (Ideal (𝓞 F))⁰) (v : HeightOneSpectrum (𝓞 F)),
    adelicOrd v (toHom a) = idealOrd v (a : Ideal (𝓞 F))

/-- **Remark 4.10** (p. 19, diagram (13)): $\widetilde{\lambda(\mathfrak a\mathfrak b^2)} = \widetilde{\lambda(\mathfrak a)}$, so
$\widetilde\lambda$ factors through the ideals modulo squares. -/
@[kb "hanke2011structure" "Rem. 4.10, p. 19 (diagram (13))"]
theorem DistinguishedFamily.normalize_mul_sq (lam : DistinguishedFamily F) (n : ℕ) (a b : (Ideal (𝓞 F))⁰) :
    normalizeAdelic n (lam.toHom (a * b ^ 2)) = normalizeAdelic n (lam.toHom a) := by
  rw [map_mul, map_pow, remark_4_10_global]

/-! ### Definition 4.12: the associated formal Dirichlet series -/

open Classical in
/-- **Definition 4.12** (p. 19): the coefficients of the formal Dirichlet series
$D^T_{X,\lambda}(s) = \sum_{\mathfrak a\in I^T(\mathcal O_F)}X(\lambda(\mathfrak a))\,\mathfrak a^{-s}$ associated to a formal
squareclass series with coefficients $X$ and a distinguished family $\lambda$: the coefficient of $\mathfrak a^{-s}$ is
$X(\lambda(\mathfrak a))$ if $\mathfrak a$ is prime to every $\mathfrak p \in T$ and $0$ otherwise. -/
@[kb "hanke2011structure" "Def. 4.12, p. 19"]
def assocDirichlet {K : Type*} [Zero K] (T : Finset (HeightOneSpectrum (𝓞 F))) (X : AdelicSqCl F → K)
    (lam : DistinguishedFamily F) (a : (Ideal (𝓞 F))⁰) : K :=
  if ∀ v ∈ T, idealOrd v (a : Ideal (𝓞 F)) = 0 then X (lam.toHom a) else 0

/-! ### Local mass data and Corollaries 4.13 and 4.15 -/

variable (F) in
/-- **Local mass data** for the primes of $F$ (the data of Definitions 3.5, 4.5 and 4.6): for every prime $\mathfrak p$ and
local squareclass $S_{\mathfrak p} \in \mathrm{SqCl}(F_{\mathfrak p}^\times,\mathcal O_{\mathfrak p}^\times)$ a finite set `G v s` of local genera
$G_{\mathfrak p}$ with $\det_H(G_{\mathfrak p}) = S_{\mathfrak p}$, their Hasse invariants `hasse` $= c_{\mathfrak p}(G_{\mathfrak p})$ and local
densities `beta` $= \beta_{G_{\mathfrak p},\mathfrak p}(G_{\mathfrak p})$, and the generic local density `betaGen v s̃`
$= \beta_{n,\mathfrak p}(\widetilde S_{\mathfrak p})$ of a normalized class (Definition 4.5). -/
structure LocalMassData (K : Type*) where
  /-- the local genera $G_{\mathfrak p}$ with $\det_H(G_{\mathfrak p}) = S_{\mathfrak p}$ -/
  G : ∀ v : HeightOneSpectrum (𝓞 F), LocalSqCl v → Type
  /-- finiteness of each set of local genera -/
  fintype : ∀ v s, Fintype (G v s)
  /-- the Hasse invariant $c_{\mathfrak p}(G_{\mathfrak p}) \in \{\pm1\}$ -/
  hasse : ∀ v s, G v s → ℤˣ
  /-- the local density $\beta_{G_{\mathfrak p},\mathfrak p}(G_{\mathfrak p})$ -/
  beta : ∀ v s, G v s → K
  /-- the generic local density $\beta_{n,\mathfrak p}(\widetilde S_{\mathfrak p})$ of a normalized class -/
  betaGen : ∀ v : HeightOneSpectrum (𝓞 F), LocalSqCl v → K

attribute [instance] LocalMassData.fintype

namespace LocalMassData

attribute [local instance] Classical.propDecidable

variable {K : Type*} [Field K] (D : LocalMassData F K) (n : ℕ)

/-- The local genus data of `D` at the primes of a finite set $T$ (the type `↥T`) for the squareclass $S$, with the
normalized weights $\beta_{n,\mathfrak p}(\widetilde S_{\mathfrak p})/\beta_{G_{\mathfrak p},\mathfrak p}(G_{\mathfrak p})$ (Definition 4.6). -/
def dataAt (T : Finset (HeightOneSpectrum (𝓞 F))) (S : AdelicSqCl F) : LocalGenusData T K where
  G i := D.G i (AdelicSqCl.comp i S)
  fintype _ := inferInstance
  hasse i := D.hasse i (AdelicSqCl.comp i S)
  weight i g := D.betaGen i (AdelicSqCl.comp i (normalizeAdelic n S)) / D.beta i _ g

/-- **The part at $T$ of the primitive total adelic mass** (Definition 3.5): the sum over the tuples
$(G_{\mathfrak p})_{\mathfrak p\in T}$ with $c_{\mathfrak p}(G_{\mathfrak p}) = (\vec c_{\mathbb S})_{\mathfrak p}$ ($\mathfrak p \in \mathbb S$) and
$\prod_{\mathfrak p\in T}c_{\mathfrak p}(G_{\mathfrak p}) = \varepsilon_\infty$ of $\prod_{\mathfrak p\in T}\beta_{G_{\mathfrak p},\mathfrak p}(G_{\mathfrak p})^{-1}$. When
the data satisfy Lemma 4.7 and Theorem 2.6 outside $T$ (a unique genus, $c_{\mathfrak p} = 1$, $\beta = \beta_{n,\mathfrak p}$), the full
$M^*_{\varepsilon_\infty,\vec c_{\mathbb S};n}(S)$ is this times $\prod_{\mathfrak p\notin T}\beta_{n,\mathfrak p}(\widetilde S_{\mathfrak p})^{-1}$. -/
@[kb "hanke2011structure" "Def. 3.5, p. 12 (the factor at T)"]
def massAt (T : Finset (HeightOneSpectrum (𝓞 F))) (𝕊 : Finset T) (c : T → ℤˣ) (ε : ℤˣ) (S : AdelicSqCl F) : K :=
  ∑ g : (∀ i : T, (D.dataAt n T S).G i),
    if (∀ i ∈ 𝕊, (D.dataAt n T S).hasse i (g i) = c i) ∧ ∏ i : T, (D.dataAt n T S).hasse i (g i) = ε then
      ∏ i : T, (D.beta i _ (g i))⁻¹
    else 0

/-- **Theorem 4.8, global coefficient form** (eqs. (6)–(12)), for local mass data with nonzero generic densities: with
$C = \varepsilon_\infty\prod_{\mathfrak p\in\mathbb S}(\vec c_{\mathbb S})_{\mathfrak p}$,
$$\mathrm{massAt}(S) = \prod_{\mathfrak p\in T}\beta_{n,\mathfrak p}(\widetilde S_{\mathfrak p})^{-1}\cdot\prod_{\mathfrak p\in\mathbb S}
\widetilde M^{*,(\vec c_{\mathbb S})_{\mathfrak p}}_{\mathfrak p;n}(S_{\mathfrak p})\cdot\frac12\Big[\prod_{\mathfrak p\in T\smallsetminus\mathbb S}
A^*_{\mathfrak p;n}(S_{\mathfrak p}) + C\prod_{\mathfrak p\in T\smallsetminus\mathbb S}B^*_{\mathfrak p;n}(S_{\mathfrak p})\Big].$$ -/
@[kb "hanke2011structure" "Thm. 4.8, p. 17 (global coefficient form)"]
theorem theorem_4_8_global (h2 : (2 : K) ≠ 0) (T : Finset (HeightOneSpectrum (𝓞 F))) (𝕊 : Finset T) (c : T → ℤˣ)
    (ε : ℤˣ) (S : AdelicSqCl F) (hgen : ∀ i : T, D.betaGen i (AdelicSqCl.comp i (normalizeAdelic n S)) ≠ 0) :
    D.massAt n T 𝕊 c ε S =
      (∏ i : T, D.betaGen i (AdelicSqCl.comp i (normalizeAdelic n S)))⁻¹ *
        ((∏ i ∈ 𝕊, (D.dataAt n T S).massSum i (c i)) *
          ((∏ i ∈ 𝕊ᶜ, (D.dataAt n T S).A i + ((ε * ∏ i ∈ 𝕊, c i : ℤˣ) : ℤ) * ∏ i ∈ 𝕊ᶜ, (D.dataAt n T S).B i) / 2)) := by
  have h := (D.dataAt n T S).theorem_4_8_mass h2 (fun i g => D.beta i _ g)
    (fun i => D.betaGen i (AdelicSqCl.comp i (normalizeAdelic n S))) hgen (fun _ _ => rfl) 𝕊 c ε
  exact h

/-- **Corollary 4.13, coefficientwise** (p. 20): for a distinguished family $\lambda$ and $\mathfrak a = \mathfrak t\mathfrak b^2$, the
coefficient of $\mathfrak a^{-s}$ in $D_{M^*,\lambda,\varepsilon_\infty,\vec c_{\mathbb S};n}(s)$ (at the primes of $T$) is
$$\prod_{\mathfrak p\in T}\beta_{n,\mathfrak p}(\widetilde{\lambda(\mathfrak t)}_{\mathfrak p})^{-1}\cdot\prod_{\mathfrak p\in\mathbb S}
\widetilde M^{*,(\vec c_{\mathbb S})_{\mathfrak p}}_{\mathfrak p;n}(\lambda(\mathfrak a)_{\mathfrak p})\cdot\frac12\Big[\prod_{\mathfrak p\in T\smallsetminus\mathbb S}
A^*_{\mathfrak p;n}(\lambda(\mathfrak a)_{\mathfrak p}) + C\prod_{\mathfrak p\in T\smallsetminus\mathbb S}B^*_{\mathfrak p;n}(\lambda(\mathfrak a)_{\mathfrak p})\Big]:$$
the generic factor depends only on $\mathfrak t$ (Remark 4.10). -/
@[kb "hanke2011structure" "Cor. 4.13, p. 20 (coefficientwise)"]
theorem cor_4_13_coeff (h2 : (2 : K) ≠ 0) (lam : DistinguishedFamily F) (T : Finset (HeightOneSpectrum (𝓞 F)))
    (𝕊 : Finset T) (c : T → ℤˣ) (ε : ℤˣ) (t b : (Ideal (𝓞 F))⁰)
    (hgen : ∀ i : T, D.betaGen i (AdelicSqCl.comp i (normalizeAdelic n (lam.toHom t))) ≠ 0) :
    D.massAt n T 𝕊 c ε (lam.toHom (t * b ^ 2)) =
      (∏ i : T, D.betaGen i (AdelicSqCl.comp i (normalizeAdelic n (lam.toHom t))))⁻¹ *
        ((∏ i ∈ 𝕊, (D.dataAt n T (lam.toHom (t * b ^ 2))).massSum i (c i)) *
          ((∏ i ∈ 𝕊ᶜ, (D.dataAt n T (lam.toHom (t * b ^ 2))).A i +
            ((ε * ∏ i ∈ 𝕊, c i : ℤˣ) : ℤ) * ∏ i ∈ 𝕊ᶜ, (D.dataAt n T (lam.toHom (t * b ^ 2))).B i) / 2)) := by
  have e := lam.normalize_mul_sq n t b
  have hgen' : ∀ i : T, D.betaGen i (AdelicSqCl.comp i (normalizeAdelic n (lam.toHom (t * b ^ 2)))) ≠ 0 := by
    rw [e]; exact hgen
  rw [D.theorem_4_8_global n h2 T 𝕊 c ε _ hgen', e]

/-- **Corollary 4.15, coefficientwise** (p. 20): if the generic density product does not depend on the normalized class
(Remark 4.14; for $n$ odd this is proved at the primes $\mathfrak p \nmid 2$, `remark_4_14_nondyadic`, and is a hypothesis
`hconst` here), then the generic factor in Corollary 4.13 is $\prod_{\mathfrak p\in T}\beta_{n,\mathfrak p}(\widetilde{\lambda(\mathcal O_F)}_{\mathfrak p})^{-1}$
for every $\mathfrak a$, so $D_{M^*} = \tfrac12\beta^{-1}_{n,f}(\widetilde{\lambda(\mathcal O_F)})\,K\,[D^{\mathbb S}_{A^*} + C\,D^{\mathbb S}_{B^*}]$. -/
@[kb "hanke2011structure" "Cor. 4.15, p. 20 (coefficientwise)"]
theorem cor_4_15_coeff (h2 : (2 : K) ≠ 0) (lam : DistinguishedFamily F) (T : Finset (HeightOneSpectrum (𝓞 F)))
    (𝕊 : Finset T) (c : T → ℤˣ) (ε : ℤˣ) (a : (Ideal (𝓞 F))⁰)
    (hconst : ∀ i : T, D.betaGen i (AdelicSqCl.comp i (normalizeAdelic n (lam.toHom a))) =
      D.betaGen i (AdelicSqCl.comp i (normalizeAdelic n (lam.toHom 1))))
    (hgen : ∀ i : T, D.betaGen i (AdelicSqCl.comp i (normalizeAdelic n (lam.toHom 1))) ≠ 0) :
    D.massAt n T 𝕊 c ε (lam.toHom a) =
      (∏ i : T, D.betaGen i (AdelicSqCl.comp i (normalizeAdelic n (lam.toHom 1))))⁻¹ *
        ((∏ i ∈ 𝕊, (D.dataAt n T (lam.toHom a)).massSum i (c i)) *
          ((∏ i ∈ 𝕊ᶜ, (D.dataAt n T (lam.toHom a)).A i +
            ((ε * ∏ i ∈ 𝕊, c i : ℤˣ) : ℤ) * ∏ i ∈ 𝕊ᶜ, (D.dataAt n T (lam.toHom a)).B i) / 2)) := by
  have hgen' : ∀ i : T, D.betaGen i (AdelicSqCl.comp i (normalizeAdelic n (lam.toHom a))) ≠ 0 := fun i => by
    rw [hconst]; exact hgen i
  rw [D.theorem_4_8_global n h2 T 𝕊 c ε _ hgen']
  congr 2
  exact Finset.prod_congr rfl fun i _ => hconst i

end LocalMassData

end

end QuadFormsKB.Hanke2011Structure
