/-
# Hanke 2013, Algorithm 3.2: a local $\mathfrak a$-saturated superlattice from a Jordan splitting

J. Hanke, *Algorithms for computing maximal lattices in bilinear (and quadratic) spaces over number fields*,
Contemp. Math. 587 (2013); source used: arXiv:1208.2481v3 (bib key `hanke2013algorithms`), §3.1.1, p. 7, and
Definition 3.6, p. 9.

Setting as in `Saturation.lean`: $R$ is a Dedekind domain with fraction field $F$, $2 \in F^\times$, and the bilinear
space $(V, B)$ is encoded by $Q = Q_B$ (`bil Q` $= B$). The paper's local ring $\mathcal O_{\mathfrak p}$ is the case
where $R$ is a discrete valuation ring (`algorithm_3_2_isASaturated`); the statements below hold for any Dedekind $R$ and a
non-zero prime $\mathfrak p$ (with $\mathfrak P = \mathfrak p$ as a fractional ideal, `idealF p`).

**Algorithm 3.2** (p. 7). Input: an $\mathfrak a$-valued lattice $L$ with a Jordan decomposition
$L = \bigoplus_i L_i$, $L_i$ an $\mathfrak a\mathfrak p^{e_i}$-modular lattice. Output:
$L' = \bigoplus_i\mathfrak p^{-\nu_i}L_i$, $\nu_i = \lfloor e_i/2\rfloor$ (`alg32`).

**Proves** (`algorithm_3_2`): $L\subseteq L'$, $L'$ is a lattice, $L'$ is $\mathfrak a$-valued, and
$\mathfrak p\subseteq\operatorname{Ann}D_{\mathfrak a}(L')$, i.e. $D_{\mathfrak a}(L')$ (so also its localization at
$\mathfrak p$) is killed by $\mathfrak p$: Definition 3.1 at $\mathfrak p$ (`algorithm_3_2_local`); over a discrete
valuation ring, $L'$ is $\mathfrak a$-saturated (`algorithm_3_2_isASaturated`).

**Definition 3.6, comparison** (`maxScaleIndex_eq_of_split`): if $L$ has such a splitting and $m = \max_ke_k$, then
$\operatorname{Ann}D_{\mathfrak a}(L) = \mathfrak p^m$, so the maximal scale index of `Saturation.lean` (defined through the
annihilator) equals the paper's Jordan index $m_{\mathfrak p,\mathfrak a}(L) = m$ (the two halves:
`maxScaleIndex_le_of_split`, `annD_le_of_component`).

*Reading of the input:* the paper's components are the Jordan components of $L_{\mathfrak p}$ with distinct scales
$\mathfrak a\mathfrak p^i$; here any finite orthogonal family of modular sublattices $L_k$ with scales
$\mathfrak a\mathfrak p^{e_k}$ and $\sum_kL_k = L$ is allowed (several components may have the same $e_k$, and independence
is not needed for the proof). O'Meara's Jordan splittings (`OMeara.IsJordanSplitting`, 91C) give such families.
-/
import QuadFormsKB.Literature.Hanke2013Algorithms.Saturation
import QuadFormsKB.Literature.Hanke2013Algorithms.Neighbors
import QuadFormsKB.Literature.OMeara.Sec82Modular
import QuadFormsKB.Literature.OMeara.Sec82Splitting

open QuadraticMap Submodule Module
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2013Algorithms

open QuadFormsKB.OMeara

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-! ### Orthogonal families of modular lattices and the annihilator -/

/-- Pairwise orthogonal families stay orthogonal on the $F$-spans. -/
theorem bil_span_orth_family {ι : Type*} {Ls : ι → Submodule R V}
    (horth : ∀ i j, i ≠ j → ∀ x ∈ Ls i, ∀ y ∈ Ls j, bil Q x y = 0) {i j : ι} (hij : i ≠ j) {x y : V}
    (hx : x ∈ span F (Ls i : Set V)) (hy : y ∈ span F (Ls j : Set V)) : bil Q x y = 0 := by
  have h1 : ∀ z ∈ Ls j, bil Q x z = 0 := fun z hz => by
    rw [bil_comm]
    exact bil_zero_of_mem_span_F Q (fun w hw => horth j i (Ne.symm hij) z hz w hw) hx
  exact bil_zero_of_mem_span_F Q h1 hy

/-- **The annihilator from an orthogonal splitting**: let $L = \sum_kL_k$ be a lattice spanning a non-degenerate space,
with the $L_k$ pairwise orthogonal and $L_k$ $\mathfrak s_k$-modular. If $r\,\mathfrak a\subseteq\mathfrak s_k$ for all $k$,
then $r\in\operatorname{Ann}D_{\mathfrak a}(L)$, i.e. $rL^{\#\mathfrak a}\subseteq L$. *Proof:* write $x\in L^{\#\mathfrak a}$ as
$x = \sum_ky_k$ with $y_k\in FL_k$ its orthogonal projections; $B(ry_k, L_k) = rB(x, L_k)\subseteq r\mathfrak a\subseteq
\mathfrak s_k$, so $ry_k\in L_k$ by modularity (O'Meara 82:14). -/
theorem mem_annD_of_split (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F} {L : Submodule R V}
    (hL : L.IsLattice F) {ι : Type*} [Fintype ι] {Ls : ι → Submodule R V}
    (horth : ∀ i j, i ≠ j → ∀ x ∈ Ls i, ∀ y ∈ Ls j, bil Q x y = 0) (hsup : ⨆ k, Ls k = L)
    (s : ι → Submodule R F) (hmod : ∀ k, IsModular Q (s k) (Ls k)) (hfg : ∀ k, (Ls k).FG) {r : R}
    (hr : ∀ k, span R {algebraMap R F r} * a ≤ s k) : r ∈ annD Q a L := by
  classical
  rw [mem_annD]
  intro x hx
  have hreg : ∀ k, IsRegular Q (Ls k) := fun k => isRegular_of_isModular Q (hmod k) (hfg k)
  choose y hyspan hy using fun k => exists_proj Q (hfg k) (hreg k) x
  -- `x = ∑ y k`
  have hspan : ∀ v : V, v ∈ ⨆ k, span F (Ls k : Set V) := fun v => by
    rw [← span_iSup, hsup, hL.span_eq_top]; trivial
  have hx_eq : x = ∑ k, y k := by
    have hz : ∀ w : V, bil Q (x - ∑ k, y k) w = 0 := by
      intro w
      refine Submodule.iSup_induction (motive := fun w => bil Q (x - ∑ k, y k) w = 0) _ (hspan w) ?_ ?_ ?_
      · intro j w hw
        rw [bil_sub_left, bil_sum_left, Finset.sum_eq_single j, hy j w hw, sub_self]
        · intro k _ hkj; exact bil_span_orth_family Q horth hkj (hyspan k) hw
        · intro h; exact absurd (Finset.mem_univ j) h
      · simp [bil]
      · intro w₁ w₂ h₁ h₂; rw [bil_add_right, h₁, h₂, add_zero]
    exact sub_eq_zero.1 (hV.1 (x - ∑ k, y k) hz)
  -- each `r • y k` lies in `Ls k`
  have hmem : ∀ k, r • y k ∈ Ls k := fun k => by
    refine Dedekind.mem_of_isModular Q (hmod k) (hfg k) ?_ fun z hz => ?_
    · rw [← algebraMap_smul F r (y k)]
      exact Submodule.smul_mem _ _ (hyspan k)
    · rw [bil_rsmul_left, hy k z (subset_span hz)]
      refine hr k (mul_mem_mul (mem_span_singleton_self _) ?_)
      exact hx z (hsup ▸ (le_iSup Ls k) hz)
  rw [hx_eq, Finset.smul_sum, ← hsup]
  exact sum_mem fun k _ => (le_iSup Ls k) (hmem k)

/-! ### Fractional-ideal arithmetic for $\mathfrak P = \mathfrak p$ -/

section Ideal

variable {p : Ideal R}

theorem idealF_le_one : idealF (F := F) p ≤ 1 := by
  rintro _ ⟨r, -, rfl⟩
  exact Submodule.algebraMap_mem r

theorem one_le_one_div_idealF : (1 : Submodule R F) ≤ 1 / idealF (F := F) p := by
  rw [Submodule.le_div_iff_mul_le, one_mul]; exact idealF_le_one

theorem one_le_pow_one_div_idealF (ν : ℕ) : (1 : Submodule R F) ≤ (1 / idealF (F := F) p) ^ ν := by
  induction ν with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    calc (1 : Submodule R F) = 1 * 1 := (mul_one 1).symm
      _ ≤ _ := mul_le_mul' ih one_le_one_div_idealF

theorem idealF_pow_le_one (j : ℕ) : idealF (F := F) p ^ j ≤ 1 := by
  induction j with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    calc idealF (F := F) p ^ k * idealF p ≤ 1 * 1 := mul_le_mul' ih idealF_le_one
      _ = 1 := mul_one 1

/-- $(\mathfrak p^{-\nu})^2\mathfrak a\mathfrak p^e = \mathfrak a\mathfrak p^{e\bmod2}$ for $\nu = \lfloor e/2\rfloor$. -/
theorem scale_alg32 (hp0 : p ≠ ⊥) (a : Submodule R F) (e : ℕ) :
    ((1 / idealF (F := F) p) ^ (e / 2)) ^ 2 * (a * idealF p ^ e) = a * idealF p ^ (e % 2) := by
  have h1 : idealF (F := F) p * (1 / idealF p) = 1 := mul_one_div_cancel_of_fg (idealF_fg p) (idealF_ne_bot hp0)
  have hPe : idealF (F := F) p ^ e = (idealF p ^ (e / 2)) ^ 2 * idealF p ^ (e % 2) := by
    conv_lhs => rw [← Nat.div_add_mod e 2, pow_add, pow_mul']
  rw [hPe]
  calc ((1 / idealF p) ^ (e / 2)) ^ 2 * (a * ((idealF p ^ (e / 2)) ^ 2 * idealF p ^ (e % 2)))
      = a * ((idealF (F := F) p * (1 / idealF p)) ^ (e / 2)) ^ 2 * idealF p ^ (e % 2) := by
        rw [mul_pow]; ring
    _ = _ := by rw [h1, one_pow, one_pow, mul_one]

end Ideal

/-! ### Algorithm 3.2 -/

/-- **Algorithm 3.2, step 2** (Hanke 2013, p. 7): $L' = \sum_k\mathfrak p^{-\nu_k}L_k$, $\nu_k = \lfloor e_k/2\rfloor$. -/
@[kb "hanke2013algorithms" "Algorithm 3.2, step 2, p. 7"]
def alg32 (p : Ideal R) {ι : Type*} (e : ι → ℕ) (Ls : ι → Submodule R V) : Submodule R V :=
  ⨆ k, (1 / idealF (F := F) p) ^ (e k / 2) • Ls k

theorem fg_of_le_lattice {L N : Submodule R V} (hL : L.FG) (hN : N ≤ L) : N.FG := by
  haveI : IsNoetherian R L := isNoetherian_of_fg_of_noetherian L hL
  have := IsNoetherian.noetherian (N.comap L.subtype)
  have h2 := this.map L.subtype
  rwa [Submodule.map_comap_eq, inf_eq_right.2 (by simpa using hN)] at h2

theorem span_le_span_smul {c : Submodule R F} (hc0 : c ≠ ⊥) (N : Submodule R V) :
    span F (N : Set V) ≤ span F ((c • N : Submodule R V) : Set V) := by
  obtain ⟨γ, hγ, hγ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc0
  rw [Submodule.span_le]
  intro x hx
  have : x = γ⁻¹ • (γ • x) := by rw [smul_smul, inv_mul_cancel₀ hγ0, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (subset_span (Submodule.smul_mem_smul hγ hx))

theorem smul_le_span {c : Submodule R F} (N : Submodule R V) :
    ((c • N : Submodule R V) : Set V) ⊆ span F (N : Set V) := by
  intro x hx
  refine Submodule.smul_induction_on (p := fun x => x ∈ span F (N : Set V)) hx (fun γ _ n hn => ?_)
    (fun _ _ h₁ h₂ => add_mem h₁ h₂)
  exact Submodule.smul_mem _ _ (subset_span hn)

/-- **Algorithm 3.2, correctness** (Hanke 2013, p. 7): let $\mathfrak p\ne0$ be a prime, $\mathfrak a$ a non-zero
fractional ideal, and $L$ a lattice in a non-degenerate space with $L = \sum_kL_k$, the $L_k$ pairwise orthogonal and
$L_k$ $\mathfrak a\mathfrak p^{e_k}$-modular. Then $L' = \sum_k\mathfrak p^{-\lfloor e_k/2\rfloor}L_k$ (`alg32`) is a lattice
containing $L$, it is $\mathfrak a$-valued, and $\mathfrak p\subseteq\operatorname{Ann}D_{\mathfrak a}(L')$. Moreover each
$\mathfrak p^{-\lfloor e_k/2\rfloor}L_k$ is $\mathfrak a\mathfrak p^{e_k\bmod 2}$-modular, so $L'$ has a splitting with
exponents in $\{0, 1\}$. -/
@[kb "hanke2013algorithms" "Algorithm 3.2, p. 7 (correctness)"]
theorem algorithm_3_2 (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F} (ha : a.FG)
    (ha0 : a ≠ ⊥) {p : Ideal R} (hp0 : p ≠ ⊥) {L : Submodule R V} (hL : L.IsLattice F) {ι : Type*} [Fintype ι]
    {Ls : ι → Submodule R V} (horth : ∀ i j, i ≠ j → ∀ x ∈ Ls i, ∀ y ∈ Ls j, bil Q x y = 0)
    (hsup : ⨆ k, Ls k = L) (e : ι → ℕ) (hmod : ∀ k, IsModular Q (a * idealF p ^ e k) (Ls k)) :
    L ≤ alg32 (F := F) p e Ls ∧ (alg32 (F := F) p e Ls).IsLattice F ∧ IsAValued Q a (alg32 (F := F) p e Ls) ∧
      p ≤ annD Q a (alg32 (F := F) p e Ls) ∧
      ∀ k, IsModular Q (a * idealF p ^ (e k % 2)) ((1 / idealF (F := F) p) ^ (e k / 2) • Ls k) := by
  classical
  set P := idealF (F := F) p with hP
  set c : ι → Submodule R F := fun k => (1 / P) ^ (e k / 2) with hc
  have hPfg : P.FG := idealF_fg p
  have hP0 : P ≠ ⊥ := idealF_ne_bot hp0
  obtain ⟨hiP, hiP0⟩ := one_div_fg hPfg hP0
  have hcfg : ∀ k, (c k).FG ∧ c k ≠ ⊥ := fun k => pow_fg_ne_bot hiP hiP0 _
  have hfg : ∀ k, (Ls k).FG := fun k => fg_of_le_lattice hL.fg (hsup ▸ le_iSup Ls k)
  set L' := alg32 (F := F) p e Ls with hL'
  have hmod' : ∀ k, IsModular Q (a * P ^ (e k % 2)) (c k • Ls k) := fun k => by
    have := (hmod k).ideal_smul Q (hfg k) (hcfg k).1 (hcfg k).2
    rwa [hc, scale_alg32 hp0] at this
  have hLL' : L ≤ L' := by
    rw [← hsup]
    refine iSup_mono fun k => ?_
    calc Ls k = (1 : Submodule R F) • Ls k := (Submodule.one_smul _).symm
      _ ≤ c k • Ls k := Submodule.smul_mono_left (one_le_pow_one_div_idealF _)
  have hfull : span F (L' : Set V) = ⊤ := by
    rw [eq_top_iff, ← hL.span_eq_top]; exact span_mono hLL'
  have horth' : ∀ i j, i ≠ j → ∀ x ∈ c i • Ls i, ∀ y ∈ c j • Ls j, bil Q x y = 0 :=
    fun i j hij x hx y hy => bil_span_orth_family Q horth hij (smul_le_span _ hx) (smul_le_span _ hy)
  have hfg' : ∀ k, (c k • Ls k).FG := fun k => fg_smul_max (hcfg k).1 (hfg k)
  have hL'fg : L'.FG := by
    rw [hL', alg32]
    exact Submodule.fg_iSup _ hfg'
  have hval : IsAValued Q a L' := by
    unfold IsAValued scale
    rw [span_le]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    have hx : x ∈ ⨆ k, c k • Ls k := hx
    have hy : y ∈ ⨆ k, c k • Ls k := hy
    refine Submodule.iSup_induction (motive := fun x => bil Q x y ∈ a) _ hx ?_ (by simp [bil]) ?_
    · intro i x hx
      refine Submodule.iSup_induction (motive := fun y => bil Q x y ∈ a) _ hy ?_ (by simp [bil]) ?_
      · intro j y hy
        by_cases hij : i = j
        · subst hij
          have h1 : bil Q x y ∈ scale Q (c i • Ls i) := bil_mem_scale Q hx hy
          rw [(hmod' i).2.1] at h1
          have h2 : a * P ^ (e i % 2) ≤ a := by
            calc a * P ^ (e i % 2) ≤ a * 1 := mul_le_mul' le_rfl (idealF_pow_le_one _)
              _ = a := mul_one a
          exact h2 h1
        · rw [horth' i j hij x hx y hy]; exact zero_mem _
      · intro y₁ y₂ h₁ h₂; rw [bil_add_right]; exact add_mem h₁ h₂
    · intro x₁ x₂ h₁ h₂; rw [bil_add_left]; exact add_mem h₁ h₂
  refine ⟨hLL', ⟨hL'fg, hfull⟩, hval, fun r hr => ?_, hmod'⟩
  refine mem_annD_of_split Q hV ⟨hL'fg, hfull⟩ horth' rfl _ hmod' hfg' fun k => ?_
  have hrP : span R {algebraMap R F r} ≤ P := by
    rw [span_le, Set.singleton_subset_iff]; exact ⟨r, hr, rfl⟩
  calc span R {algebraMap R F r} * a ≤ P * a := mul_le_mul' hrP le_rfl
    _ = a * P ^ 1 := by rw [pow_one, mul_comm]
    _ ≤ a * P ^ (e k % 2) := by
      refine mul_le_mul' le_rfl ?_
      rcases Nat.mod_two_eq_zero_or_one (e k) with h | h
      · rw [h, pow_zero, pow_one]; exact idealF_le_one
      · rw [h]

/-- **Algorithm 3.2: the output is $\mathfrak a$-saturated at $\mathfrak p$** (Definition 3.1 at $\mathfrak p$): the
localization $(D_{\mathfrak a}(L'))_{\mathfrak p}$ is annihilated by $\mathfrak p$. -/
@[kb "hanke2013algorithms" "Algorithm 3.2, p. 7; Definition 3.1, p. 7 (saturated at p)"]
theorem algorithm_3_2_local (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F} (ha : a.FG)
    (ha0 : a ≠ ⊥) {p : Ideal R} [p.IsPrime] (hp0 : p ≠ ⊥) {L : Submodule R V} (hL : L.IsLattice F) {ι : Type*}
    [Fintype ι] {Ls : ι → Submodule R V} (horth : ∀ i j, i ≠ j → ∀ x ∈ Ls i, ∀ y ∈ Ls j, bil Q x y = 0)
    (hsup : ⨆ k, Ls k = L) (e : ι → ℕ) (hmod : ∀ k, IsModular Q (a * idealF p ^ e k) (Ls k)) :
    ∀ r ∈ p, ∀ x : LocalizedModule p.primeCompl (DiscModule Q a (alg32 (F := F) p e Ls)), r • x = 0 := by
  obtain ⟨-, hlat, -, hann, -⟩ := algorithm_3_2 Q hV ha ha0 hp0 hL horth hsup e hmod
  haveI : Module.Finite R (DiscModule Q a (alg32 (F := F) p e Ls)) := by
    have := (isLattice_aDual Q hV ha ha0 hlat).fg
    have : Module.Finite R (aDual Q a (alg32 (F := F) p e Ls)) := Module.Finite.iff_fg.2 this
    infer_instance
  rw [localization_annihilated_iff]
  exact ⟨1, fun h => (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one _).2 h),
    fun r hr => by rw [one_mul]; exact hann hr⟩

/-- **Algorithm 3.2 over the local ring** (Hanke 2013, p. 7: "an $\mathfrak a$-saturated superlattice of $L_{\mathfrak p}$"):
for $R$ a discrete valuation ring with maximal ideal $\mathfrak p$, the output $L'$ is an $\mathfrak a$-saturated lattice
(Definition 3.1) containing $L$. -/
@[kb "hanke2013algorithms" "Algorithm 3.2, p. 7 (L'_p is an a-saturated superlattice of L_p)"]
theorem algorithm_3_2_isASaturated [IsDiscreteValuationRing R] (hV : (QuadraticMap.associated Q).Nondegenerate)
    {a : Submodule R F} (ha : a.FG) (ha0 : a ≠ ⊥) {L : Submodule R V} (hL : L.IsLattice F) {ι : Type*}
    [Fintype ι] {Ls : ι → Submodule R V} (horth : ∀ i j, i ≠ j → ∀ x ∈ Ls i, ∀ y ∈ Ls j, bil Q x y = 0)
    (hsup : ⨆ k, Ls k = L) (e : ι → ℕ)
    (hmod : ∀ k, IsModular Q (a * idealF (IsLocalRing.maximalIdeal R) ^ e k) (Ls k)) :
    L ≤ alg32 (F := F) (IsLocalRing.maximalIdeal R) e Ls ∧
      IsASaturated Q a (alg32 (F := F) (IsLocalRing.maximalIdeal R) e Ls) := by
  have hp0 : IsLocalRing.maximalIdeal R ≠ ⊥ := IsDiscreteValuationRing.not_a_field R
  obtain ⟨hLL', -, hval, -, -⟩ := algorithm_3_2 Q hV ha ha0 hp0 hL horth hsup e hmod
  refine ⟨hLL', hval, fun q _ hq0 => ?_⟩
  have hqm : q = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal inferInstance hq0)
  subst hqm
  exact algorithm_3_2_local Q hV ha ha0 hp0 hL horth hsup e hmod

/-! ### Definition 3.6: the annihilator index against the Jordan index -/

/-- **Definition 3.6, comparison** (Hanke 2013, p. 9): if $L$ (a lattice in a non-degenerate space) is a sum of
pairwise orthogonal $\mathfrak a\mathfrak p^{e_k}$-modular lattices with all $e_k\le m$, then
$\mathfrak p^m\subseteq\operatorname{Ann}D_{\mathfrak a}(L)$, hence $m_{\mathfrak p,\mathfrak a}(L)\le m$ for the maximal
scale index `maxScaleIndex` (defined through the annihilator). With $m = \max_ke_k$ (the paper's definition through
the Jordan decomposition) this is one half of the agreement of the two definitions. -/
@[kb "hanke2013algorithms" "Definition 3.6, p. 9 (annihilator index ≤ Jordan index)"]
theorem maxScaleIndex_le_of_split (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F}
    (ha : a.FG) (ha0 : a ≠ ⊥) {p : Ideal R} [hp : p.IsPrime] (hp0 : p ≠ ⊥) {L : Submodule R V}
    (hL : L.IsLattice F) {ι : Type*} [Fintype ι] {Ls : ι → Submodule R V}
    (horth : ∀ i j, i ≠ j → ∀ x ∈ Ls i, ∀ y ∈ Ls j, bil Q x y = 0) (hsup : ⨆ k, Ls k = L) (e : ι → ℕ)
    (hmod : ∀ k, IsModular Q (a * idealF p ^ e k) (Ls k)) {m : ℕ} (hm : ∀ k, e k ≤ m) :
    p ^ m ≤ annD Q a L ∧ maxScaleIndex Q a L p ≤ m := by
  have hfg : ∀ k, (Ls k).FG := fun k => fg_of_le_lattice hL.fg (hsup ▸ le_iSup Ls k)
  have hle : p ^ m ≤ annD Q a L := fun r hr =>
    mem_annD_of_split Q hV hL horth hsup _ hmod hfg fun k => by
      have hrP : span R {algebraMap R F r} ≤ idealF (F := F) p ^ m := by
        rw [span_le, Set.singleton_subset_iff]
        have : algebraMap R F r ∈ idealF (F := F) (p ^ m) := ⟨r, hr, rfl⟩
        rwa [show idealF (F := F) (p ^ m) = idealF p ^ m from Submodule.map_pow p (Algebra.ofId R F) m] at this
      calc span R {algebraMap R F r} * a ≤ idealF p ^ m * a := mul_le_mul' hrP le_rfl
        _ = a * (idealF p ^ e k * idealF p ^ (m - e k)) := by
          rw [← pow_add, Nat.add_sub_cancel' (hm k), mul_comm]
        _ ≤ a * (idealF p ^ e k * 1) :=
          mul_le_mul' le_rfl (mul_le_mul' le_rfl (idealF_pow_le_one _))
        _ = a * idealF p ^ e k := by rw [mul_one]
  refine ⟨hle, ?_⟩
  have hprime : Prime p := Ideal.prime_of_isPrime hp0 hp
  have hfin := finiteMultiplicity_annD Q hV ha ha0 hL hp hp0
  unfold maxScaleIndex
  rw [← Nat.lt_succ_iff, hfin.multiplicity_lt_iff_not_dvd]
  intro hdvd
  have h1 : p ^ m * p ∣ p ^ m * 1 := by
    rw [mul_one, ← pow_succ]; exact dvd_trans hdvd (Ideal.dvd_iff_le.2 hle)
  exact hprime.not_dvd_one ((mul_dvd_mul_iff_left (pow_ne_zero _ hp0)).1 h1)

/-- **The other half**: if some component $L_k$ is $\mathfrak a\mathfrak p^m$-modular, then
$\operatorname{Ann}D_{\mathfrak a}(L)\subseteq\mathfrak p^m$. *Proof:* $N = \mathfrak p^{-m}L_k$ lies in $L^{\#\mathfrak a}$;
for $r\in\operatorname{Ann}D_{\mathfrak a}(L)$, $rN\subseteq L$, so $r\,\mathfrak s(N) = r\,\mathfrak a\mathfrak p^{-m}
\subseteq\mathfrak a$, i.e. $r\in\mathfrak p^m$. -/
theorem annD_le_of_component (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F}
    (ha : a.FG) (ha0 : a ≠ ⊥) {p : Ideal R} (hp0 : p ≠ ⊥) {L : Submodule R V} {ι : Type*}
    {Ls : ι → Submodule R V} (horth : ∀ i j, i ≠ j → ∀ x ∈ Ls i, ∀ y ∈ Ls j, bil Q x y = 0)
    (hsup : ⨆ k, Ls k = L) {k : ι} {m : ℕ} (hk : IsModular Q (a * idealF p ^ m) (Ls k)) :
    annD Q a L ≤ p ^ m := by
  classical
  set P := idealF (F := F) p with hP
  have hPfg : P.FG := idealF_fg p
  have hP0 : P ≠ ⊥ := idealF_ne_bot hp0
  have h1 : P * (1 / P) = 1 := mul_one_div_cancel_of_fg hPfg hP0
  have h1a : a * (1 / a) = 1 := mul_one_div_cancel_of_fg ha ha0
  set c : Submodule R F := (1 / P) ^ m with hc
  set N : Submodule R V := c • Ls k with hN
  have hcP : c * P ^ m = 1 := by rw [hc, ← mul_pow, mul_comm, h1, one_pow]
  -- `N ⊆ L^{#a}`
  have hNd : ∀ z ∈ N, ∀ y ∈ L, bil Q z y ∈ a := by
    intro z hz y hy
    rw [← hsup] at hy
    refine Submodule.iSup_induction (motive := fun y => bil Q z y ∈ a) _ hy ?_ (by simp [bil]) ?_
    · intro j y hy
      by_cases hjk : j = k
      · subst hjk
        refine Submodule.smul_induction_on (p := fun z => bil Q z y ∈ a) hz (fun γ hγ l hl => ?_)
          (fun z₁ z₂ h₁ h₂ => by rw [bil_add_left]; exact add_mem h₁ h₂)
        rw [bil_smul_left]
        have hb : bil Q l y ∈ a * P ^ m := by rw [← hk.2.1]; exact bil_mem_scale Q hl hy
        have := mul_mem_mul hγ hb
        rwa [← mul_assoc, mul_comm c a, mul_assoc, hcP, mul_one] at this
      · rw [bil_span_orth_family Q horth (Ne.symm hjk) (smul_le_span _ hz) (subset_span hy)]
        exact zero_mem _
    · intro y₁ y₂ h₁ h₂; rw [bil_add_right]; exact add_mem h₁ h₂
  intro r hr
  have hrN : ∀ z ∈ N, r • z ∈ L := fun z hz => (mem_annD Q).1 hr z (hNd z hz)
  -- `r 𝔰(N) ⊆ 𝔞`
  have hsc : span R {algebraMap R F r} * scale Q N ≤ a := by
    rw [Submodule.mul_le]
    intro x hx y hy
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [smul_mul_assoc]
    refine Submodule.smul_mem _ s ?_
    refine Submodule.span_induction (p := fun y _ => algebraMap R F r * y ∈ a) ?_ (by simp)
      (fun _ _ _ _ h₁ h₂ => by rw [mul_add]; exact add_mem h₁ h₂)
      (fun t _ _ h => by rw [mul_smul_comm]; exact Submodule.smul_mem _ t h) hy
    rintro _ ⟨z, hz, w, hw, rfl⟩
    rw [← bil_rsmul_left, bil_comm]
    exact hNd w hw _ (hrN z hz)
  rw [hN, scale_smul, hk.2.1] at hsc
  -- cancel `c² 𝔞 𝔭^m = 𝔞 c`
  have hspan : span R {algebraMap R F r} ≤ P ^ m := by
    have key : span R {algebraMap R F r} * (c ^ 2 * (a * P ^ m)) * (P ^ m * (1 / a)) =
        span R {algebraMap R F r} := by
      calc _ = span R {algebraMap R F r} * (c * P ^ m) ^ 2 * (a * (1 / a)) := by ring
        _ = _ := by rw [hcP, h1a, one_pow, mul_one, mul_one]
    have := mul_le_mul' hsc (le_refl (P ^ m * (1 / a)))
    rw [key] at this
    calc span R {algebraMap R F r} ≤ a * (P ^ m * (1 / a)) := this
      _ = P ^ m * (a * (1 / a)) := by ring
      _ = P ^ m := by rw [h1a, mul_one]
  have hmem : algebraMap R F r ∈ idealF (F := F) (p ^ m) := by
    rw [show idealF (F := F) (p ^ m) = idealF p ^ m from Submodule.map_pow p (Algebra.ofId R F) m]
    exact hspan (mem_span_singleton_self _)
  obtain ⟨r', hr', he⟩ := hmem
  have : r' = r := IsFractionRing.injective R F he
  exact this ▸ hr'

/-- **Definition 3.6: the two definitions agree** (Hanke 2013, p. 9): if $L$ (a lattice in a non-degenerate space) is a
sum of pairwise orthogonal $\mathfrak a\mathfrak p^{e_k}$-modular lattices $L_k$ and $m = \max_ke_k$ (attained at some
$k_0$), then $\operatorname{Ann}D_{\mathfrak a}(L) = \mathfrak p^m$ and the maximal scale index `maxScaleIndex` (defined
through the annihilator) equals the paper's $m_{\mathfrak p,\mathfrak a}(L) = m$, the largest $i$ with a non-zero
$\mathfrak a\mathfrak p^i$-modular component. -/
@[kb "hanke2013algorithms" "Definition 3.6, p. 9 (annihilator index = Jordan index)"]
theorem maxScaleIndex_eq_of_split (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F}
    (ha : a.FG) (ha0 : a ≠ ⊥) {p : Ideal R} [hp : p.IsPrime] (hp0 : p ≠ ⊥) {L : Submodule R V}
    (hL : L.IsLattice F) {ι : Type*} [Fintype ι] {Ls : ι → Submodule R V}
    (horth : ∀ i j, i ≠ j → ∀ x ∈ Ls i, ∀ y ∈ Ls j, bil Q x y = 0) (hsup : ⨆ k, Ls k = L) (e : ι → ℕ)
    (hmod : ∀ k, IsModular Q (a * idealF p ^ e k) (Ls k)) {m : ℕ} (hm : ∀ k, e k ≤ m) {k₀ : ι}
    (hk₀ : e k₀ = m) : annD Q a L = p ^ m ∧ maxScaleIndex Q a L p = m := by
  obtain ⟨hle, -⟩ := maxScaleIndex_le_of_split Q hV ha ha0 hp0 hL horth hsup e hmod hm
  have hge := annD_le_of_component Q hV ha ha0 hp0 horth hsup (k := k₀) (hk₀ ▸ hmod k₀)
  have heq : annD Q a L = p ^ m := le_antisymm hge hle
  refine ⟨heq, ?_⟩
  unfold maxScaleIndex
  rw [heq]
  exact multiplicity_pow_self_of_prime (Ideal.prime_of_isPrime hp0 hp) m

/-! ### Algorithm 3.8, steps 1–2 -/

/-- **Algorithm 3.8, step 1** (Hanke 2013, p. 9): the $R$-span of an $F$-basis of $V$ is a lattice. -/
@[kb "hanke2013algorithms" "Algorithm 3.8, step 1, p. 9 (an O_F-lattice spanned by a basis)"]
theorem algorithm_3_8_step1 : ∃ L : Submodule R V, L.IsLattice F := by
  classical
  let b := Module.finBasis F V
  refine ⟨span R (Set.range b), ⟨fg_span (Set.finite_range b), ?_⟩⟩
  rw [Submodule.span_span_of_tower, b.span_eq]

/-- **Algorithm 3.8, step 2** (Hanke 2013, p. 9): for a lattice $L$ and a non-zero fractional ideal $\mathfrak a$ there
is $c\in R\setminus\{0\}$ such that $\mathfrak cL$, $\mathfrak c = cR$, is an $\mathfrak a$-valued lattice
($\mathfrak c^2\mathfrak sL\subseteq\mathfrak a$). -/
@[kb "hanke2013algorithms" "Algorithm 3.8, step 2, p. 9 (rescaling L to be a-valued)"]
theorem algorithm_3_8_step2 {a : Submodule R F} (ha0 : a ≠ ⊥) {L : Submodule R V} (hL : L.IsLattice F) :
    ∃ c : R, c ≠ 0 ∧ (span R {algebraMap R F c} • L).IsLattice F ∧
      IsAValued Q a (span R {algebraMap R F c} • L) := by
  obtain ⟨α, hα, hα0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ha0
  have hsub : ((scale Q L : Submodule R F) : Set F) ⊆ span F ((a : Submodule R F) : Set F) := by
    intro x _
    have : x = (x * α⁻¹) • α := by rw [smul_eq_mul, mul_assoc, inv_mul_cancel₀ hα0, mul_one]
    rw [this]; exact Submodule.smul_mem _ _ (subset_span hα)
  obtain ⟨c, hc0, hc⟩ := exists_smul_le_of_fg (scale_fg Q hL.fg) hsub
  have hc' : algebraMap R F c ≠ 0 := by
    rw [map_ne_zero_iff _ (IsFractionRing.injective R F)]; exact hc0
  set b : Submodule R F := span R {algebraMap R F c}
  have hb0 : b ≠ ⊥ := by
    rw [Ne, Submodule.span_singleton_eq_bot]; exact hc'
  refine ⟨c, hc0, isLattice_smul_max (fg_span_singleton _) hb0 hL, ?_⟩
  unfold IsAValued
  rw [scale_smul, pow_two, mul_assoc]
  have hb1 : b ≤ 1 := by
    rw [span_le, Set.singleton_subset_iff]; exact Submodule.algebraMap_mem c
  have hbs : b * scale Q L ≤ a := by
    rw [Submodule.mul_le]
    intro x hx y hy
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [smul_mul_assoc]
    refine Submodule.smul_mem _ r ?_
    have := hc y hy
    rwa [Algebra.smul_def] at this
  calc b * (b * scale Q L) ≤ 1 * a := mul_le_mul' hb1 hbs
    _ = a := one_mul a

/-- **Algorithm 3.8, all steps** (Hanke 2013, pp. 9–10): every non-degenerate space $(V, B)$ contains an
$\mathfrak a$-saturated lattice (steps 1–2: `algorithm_3_8_step1`, `algorithm_3_8_step2`; steps 3–4: `algorithm_3_8`). -/
@[kb "hanke2013algorithms" "Algorithm 3.8, pp. 9-10 (an a-saturated lattice exists in (V, B))"]
theorem algorithm_3_8_exists (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F} (ha : a.FG)
    (ha0 : a ≠ ⊥) : ∃ L : Submodule R V, L.IsLattice F ∧ IsASaturated Q a L := by
  obtain ⟨L₀, hL₀⟩ := algorithm_3_8_step1 (R := R) (V := V) (F := F)
  obtain ⟨c, -, hlat, hval⟩ := algorithm_3_8_step2 Q ha0 hL₀
  obtain ⟨L', -, hL', hsat⟩ := algorithm_3_8 Q hV ha ha0 hlat hval
  exact ⟨L', hL', hsat⟩

end QuadFormsKB.Hanke2013Algorithms
