/-
# O'Meara §93E: the ideals $\mathfrak f_i$ (p. 264) and 93:26 (p. 267)

**Setting** (as in `Sec93E.lean`): $R$ a discrete valuation ring with fraction field $F$, $2 \in F^\times$,
$\pi$ an irreducible element (a prime element), `dord hπ` the order function; $(V, Q)$ a quadratic space over $F$,
lattices `Submodule R V`. Indices are $0$-based; O'Meara's $\mathfrak f_i$ is `fIdeal Q L Ls (i-1) i`.

**Proves**
* `mul_fIdealOf`, `fIdealOf_eq`: O'Meara's defining equation $\mathfrak s^2\mathfrak f = \sum \mathfrak d(\alpha\beta)
  + 2\mathfrak c\mathfrak s$ for `fIdealOf` (division by the invertible ideal $\mathfrak s^2$ is exact);
* `span_sqRoots` (the ideal $\mathfrak c$ spanned by the $z$ with $(z\mathfrak o)^2 = a\mathfrak o\cdot a'\mathfrak o$ is
  $\mathfrak p^{\frac12(u+u')}$ or $0$), `mul_fIdealOf_odd`, `mul_fIdealOf_even` (the two cases of the definition);
* `normIdeal_eq_span_normGroup`, `fIdeal_eq_of_sameFundamentalType` ($\mathfrak f_i$ depends only on the fundamental
  type);
* `fIdeal_le_pfrac` ($\mathfrak f_i \subseteq \mathfrak p$ in all cases);
* `mul_fIdeal_of_odd` (**93:26**, odd case: $\mathfrak s_i^2\mathfrak f_i = a_ia_{i+1}\mathfrak o$).
-/
import QuadFormsKB.Literature.OMeara.Sec93EBasic

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

-- Helper lemmas of this file live in `FIdealAux` (to avoid name clashes).
namespace FIdealAux
end FIdealAux
open FIdealAux

section Basic

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F]

namespace FIdealAux

lemma span_mul_span' (a b : F) : (R ∙ a) * (R ∙ b) = R ∙ (a * b) := by
  rw [Submodule.span_mul_span, Set.singleton_mul_singleton]

lemma mem_div_span_iff {X : Submodule R F} {c z : F} : z ∈ X / (R ∙ c) ↔ z * c ∈ X := by
  rw [Submodule.mem_div_iff_forall_mul_mem]
  constructor
  · intro h; exact h c (mem_span_singleton_self c)
  · intro h r hr
    obtain ⟨a, rfl⟩ := mem_span_singleton.1 hr
    have : z * (a • c) = a • (z * c) := by rw [Algebra.smul_def, Algebra.smul_def]; ring
    rw [this]; exact X.smul_mem a h

lemma mul_div_span {X : Submodule R F} {c : F} (hc : c ≠ 0) : (R ∙ c) * (X / (R ∙ c)) = X := by
  apply le_antisymm
  · rw [Submodule.mul_le]
    intro m hm n hn
    obtain ⟨a, rfl⟩ := mem_span_singleton.1 hm
    have h := mem_div_span_iff.1 hn
    have : (a • c) * n = a • (n * c) := by rw [Algebra.smul_def, Algebra.smul_def]; ring
    rw [this]; exact X.smul_mem a h
  · intro x hx
    have h : x / c ∈ X / (R ∙ c) := mem_div_span_iff.2 (by rwa [div_mul_cancel₀ _ hc])
    have := Submodule.mul_mem_mul (mem_span_singleton_self c) h
    rwa [mul_div_cancel₀ _ hc] at this

lemma smul_span_singleton (c x : F) : c • (R ∙ x) = R ∙ (c * x) := by
  ext y
  rw [Submodule.mem_smul_pointwise_iff_exists, mem_span_singleton]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨r, rfl⟩ := mem_span_singleton.1 hw
    exact ⟨r, by simp only [smul_eq_mul, Algebra.smul_def]; ring⟩
  · rintro ⟨r, rfl⟩
    exact ⟨r • x, mem_span_singleton.2 ⟨r, rfl⟩, by
      simp only [smul_eq_mul, Algebra.smul_def]; ring⟩

end FIdealAux

/-- **The defining equation of $\mathfrak f$** (O'Meara 1963, §93E, p. 264): for a principal $\mathfrak s = \sigma\mathfrak o$,
$\mathfrak s^2\,\mathfrak f = \sum_{\alpha \in \mathfrak g,\ \beta \in \mathfrak g'} \mathfrak d(\alpha\beta) +
2\mathfrak c\mathfrak s$, where $\mathfrak c$ is the ideal spanned by the $z$ with $(z\mathfrak o)^2 =
\mathfrak n\mathfrak n'$. (Division by the invertible principal ideal $\mathfrak s^2$ is exact.) -/
@[kb "omeara1963" "§93E, p. 264 (s_i² f_i = Σ 𝔡(αβ) (+ 2p^{(u_i+u_{i+1})/2+s_i}): the defining equation)"]
theorem mul_fIdealOf {σ : F} (hσ : σ ≠ 0) (g g' : AddSubgroup F) (n n' : Submodule R F) :
    (R ∙ σ) * (R ∙ σ) * fIdealOf R (R ∙ σ) g g' n n' =
      (⨆ (α : F) (_ : α ∈ g) (β : F) (_ : β ∈ g'), quadDefect R (α * β)) ⊔
        (2 : F) • (span R {z : F | (R ∙ z) * (R ∙ z) = n * n'} * (R ∙ σ)) := by
  unfold fIdealOf
  rw [span_mul_span']
  exact mul_div_span (mul_ne_zero hσ hσ)

/-- **$\mathfrak f$ as a scaled sum** (O'Meara 1963, §93E, p. 264): $\mathfrak f = \sigma^{-2}\bigl(\sum
\mathfrak d(\alpha\beta) + 2\mathfrak c\mathfrak s\bigr)$ for $\mathfrak s = \sigma\mathfrak o$. -/
@[kb "omeara1963" "§93E, p. 264 (s_i² f_i = Σ 𝔡(αβ) (+ 2p^{(u_i+u_{i+1})/2+s_i}): the defining equation)"]
theorem fIdealOf_eq {σ : F} (hσ : σ ≠ 0) (g g' : AddSubgroup F) (n n' : Submodule R F) :
    fIdealOf R (R ∙ σ) g g' n n' =
      (σ⁻¹ * σ⁻¹) •
        ((⨆ (α : F) (_ : α ∈ g) (β : F) (_ : β ∈ g'), quadDefect R (α * β)) ⊔
          (2 : F) • (span R {z : F | (R ∙ z) * (R ∙ z) = n * n'} * (R ∙ σ))) := by
  unfold fIdealOf
  rw [span_mul_span']
  generalize ((⨆ (α : F) (_ : α ∈ g) (β : F) (_ : β ∈ g'), quadDefect R (α * β)) ⊔
          (2 : F) • (span R {z : F | (R ∙ z) * (R ∙ z) = n * n'} * (R ∙ σ))) = X
  ext z
  rw [mem_div_span_iff, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · intro h
    refine ⟨z * (σ * σ), h, ?_⟩
    rw [smul_eq_mul]; field_simp
  · rintro ⟨x, hx, rfl⟩
    rw [smul_eq_mul]
    have : σ⁻¹ * σ⁻¹ * x * (σ * σ) = x := by field_simp
    rwa [this]

end Basic

section Order

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] {π : R}

namespace FIdealAux

lemma span_eq_iff_dord (hπ : Irreducible π) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    R ∙ x = R ∙ y ↔ dord hπ x = dord hπ y := by
  constructor
  · intro h
    have h1 : x ∈ R ∙ y := h ▸ mem_span_singleton_self x
    have h2 : y ∈ R ∙ x := h ▸ mem_span_singleton_self y
    have := (mem_span_iff hπ hx hy).1 h1
    have := (mem_span_iff hπ hy hx).1 h2
    omega
  · exact span_eq_of_dord_eq hπ hx hy

lemma mem_sqRoots_iff (hπ : Irreducible π) {a a' : F} (ha : a ≠ 0) (ha' : a' ≠ 0) (z : F) :
    (R ∙ z) * (R ∙ z) = (R ∙ a) * (R ∙ a') ↔ z ≠ 0 ∧ 2 * dord hπ z = dord hπ a + dord hπ a' := by
  rw [span_mul_span', span_mul_span']
  have haa : a * a' ≠ 0 := mul_ne_zero ha ha'
  by_cases hz : z = 0
  · subst hz
    simp only [mul_zero, ne_eq, not_true_eq_false, false_and, iff_false]
    intro h
    apply haa
    have : a * a' ∈ R ∙ (0 : F) := h ▸ mem_span_singleton_self _
    simpa using this
  · have hzz : z * z ≠ 0 := mul_ne_zero hz hz
    rw [span_eq_iff_dord hπ hzz haa, dord_mul hπ hz hz, dord_mul hπ ha ha']
    simp only [hz, ne_eq, not_false_eq_true, true_and]
    constructor <;> intro h <;> omega

end FIdealAux

/-- **The ideal $\mathfrak c$ of square roots** (O'Meara 1963, §93E, p. 264): for $a, a' \neq 0$ the $R$-span of the
$z \in F$ with $(z\mathfrak o)^2 = a\mathfrak o \cdot a'\mathfrak o$ is $\mathfrak p^{\frac12(u + u')}$ if
$u + u' = \operatorname{ord} a + \operatorname{ord} a'$ is even, and $0$ if it is odd. -/
@[kb "omeara1963" "§93E, p. 264 (the term 2p^{(u_i+u_{i+1})/2 + s_i})"]
theorem span_sqRoots (hπ : Irreducible π) {a a' : F} (ha : a ≠ 0) (ha' : a' ≠ 0) :
    span R {z : F | (R ∙ z) * (R ∙ z) = (R ∙ a) * (R ∙ a')} =
      if Even (dord hπ a + dord hπ a') then
        R ∙ (algebraMap R F π ^ ((dord hπ a + dord hπ a') / 2)) else ⊥ := by
  have key := mem_sqRoots_iff hπ ha ha'
  split_ifs with he
  · rw [Int.even_iff] at he
    apply le_antisymm
    · rw [span_le]
      intro z hz
      obtain ⟨hz0, hz2⟩ := (key z).1 hz
      exact (mem_span_zpow_iff hπ hz0 _).2 (by omega)
    · apply span_mono
      rw [Set.singleton_subset_iff]
      refine (key _).2 ⟨zpow_ne_zero _ (alg_pi_ne_zero hπ), ?_⟩
      rw [dord_zpow]; omega
  · rw [Int.not_even_iff] at he
    rw [eq_bot_iff, span_le]
    intro z hz
    exfalso
    obtain ⟨hz0, hz2⟩ := (key z).1 hz
    omega

/-- **The definition of $\mathfrak f$, odd case** (O'Meara 1963, §93E, p. 264): if $u_i + u_{i+1}$ is odd then
$\mathfrak s^2\mathfrak f = \sum_{\alpha \in \mathfrak g,\ \beta \in \mathfrak g'}\mathfrak d(\alpha\beta)$; here
$\mathfrak s = \sigma\mathfrak o$, $\mathfrak n = a\mathfrak o$, $\mathfrak n' = a'\mathfrak o$ and
$u = \operatorname{ord} a$, $u' = \operatorname{ord} a'$. -/
@[kb "omeara1963" "§93E, p. 264 (the term 2p^{(u_i+u_{i+1})/2 + s_i})"]
theorem mul_fIdealOf_odd (hπ : Irreducible π) {σ a a' : F} (hσ : σ ≠ 0) (ha : a ≠ 0) (ha' : a' ≠ 0)
    (hodd : Odd (dord hπ a + dord hπ a')) (g g' : AddSubgroup F) :
    (R ∙ σ) * (R ∙ σ) * fIdealOf R (R ∙ σ) g g' (R ∙ a) (R ∙ a') =
      ⨆ (α : F) (_ : α ∈ g) (β : F) (_ : β ∈ g'), quadDefect R (α * β) := by
  rw [mul_fIdealOf hσ, span_sqRoots hπ ha ha', if_neg (Int.not_even_iff_odd.2 hodd)]
  simp

/-- **The definition of $\mathfrak f$, even case** (O'Meara 1963, §93E, p. 264): if $u_i + u_{i+1}$ is even then
$\mathfrak s^2\mathfrak f = \sum \mathfrak d(\alpha\beta) + 2\mathfrak p^{\frac12(u + u') + s}$, where $s =
\operatorname{ord}\mathfrak s = \operatorname{ord}\sigma$ and $2\mathfrak p^k = (2\pi^k)\mathfrak o$. -/
@[kb "omeara1963" "§93E, p. 264 (the term 2p^{(u_i+u_{i+1})/2 + s_i})"]
theorem mul_fIdealOf_even (hπ : Irreducible π) {σ a a' : F} (hσ : σ ≠ 0) (ha : a ≠ 0) (ha' : a' ≠ 0)
    (heven : Even (dord hπ a + dord hπ a')) (g g' : AddSubgroup F) :
    (R ∙ σ) * (R ∙ σ) * fIdealOf R (R ∙ σ) g g' (R ∙ a) (R ∙ a') =
      (⨆ (α : F) (_ : α ∈ g) (β : F) (_ : β ∈ g'), quadDefect R (α * β)) ⊔
        R ∙ (2 * algebraMap R F π ^ ((dord hπ a + dord hπ a') / 2 + dord hπ σ)) := by
  have hpi := alg_pi_ne_zero (R := R) (F := F) hπ
  have h1 : R ∙ (algebraMap R F π ^ ((dord hπ a + dord hπ a') / 2) * σ) =
      R ∙ (algebraMap R F π ^ ((dord hπ a + dord hπ a') / 2 + dord hπ σ)) :=
    span_eq_of_dord_eq hπ (mul_ne_zero (zpow_ne_zero _ hpi) hσ) (zpow_ne_zero _ hpi)
      (by rw [dord_mul hπ (zpow_ne_zero _ hpi) hσ, dord_zpow, dord_zpow])
  rw [mul_fIdealOf hσ, span_sqRoots hπ ha ha', if_pos heven, span_mul_span', h1, smul_span_singleton]

end Order

section TypeSec

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {V' : Type*} [AddCommGroup V'] [Module F V'] [Module R V'] [IsScalarTower R F V']
variable (Q : QuadraticForm F V) (Q' : QuadraticForm F V')

theorem fIdeal_fundNormIdeal_eq_span (L : Submodule R V) {t : ℕ} (Ls : Fin t → Submodule R V) (i : Fin t) :
    fundNormIdeal Q L Ls i = span R (fundNormGroup Q L Ls i : Set F) :=
  normIdeal_eq_span_normGroup Q _

/-- **$\mathfrak f_i$ depends only on the fundamental type** (O'Meara 1963, §93E, p. 264): if $L, L'$ with Jordan
splittings `Ls`, `Ks` have the same fundamental type, then $\mathfrak f_i = \mathfrak f_i'$ (the ideals $\mathfrak s_i$,
$\mathfrak g_i$ agree by assumption, and $\mathfrak nL^{\mathfrak s_i}$ is the span of $\mathfrak g_i$). -/
@[kb "omeara1963" "§93E, p. 264 (f_i depends only on the fundamental type)"]
theorem fIdeal_eq_of_sameFundamentalType {L : Submodule R V} {L' : Submodule R V'} {t t' : ℕ}
    {Ls : Fin t → Submodule R V} {Ks : Fin t' → Submodule R V'} (h : t = t')
    (hs : SameFundamentalType Q Q' L L' Ls Ks) (i j : Fin t) :
    fIdeal Q L Ls i j = fIdeal Q' L' Ks (Fin.cast h i) (Fin.cast h j) := by
  obtain ⟨h', H⟩ := hs
  have hi := H i
  have hj := H j
  unfold fIdeal
  rw [fIdeal_fundNormIdeal_eq_span, fIdeal_fundNormIdeal_eq_span, fIdeal_fundNormIdeal_eq_span Q',
    fIdeal_fundNormIdeal_eq_span Q', hi.2.1, hi.2.2, hj.2.2]

end TypeSec

section Pfrac

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)] {π : R}
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

namespace FIdealAux

lemma mulpow (hπ : Irreducible π) (a b : ℤ) :
    (R ∙ (algebraMap R F π ^ a)) * (R ∙ (algebraMap R F π ^ b)) = R ∙ (algebraMap R F π ^ (a + b)) := by
  rw [span_mul_span', ← zpow_add₀ (alg_pi_ne_zero hπ)]

lemma pfrac_eq (hπ : Irreducible π) :
    Submodule.map (Algebra.linearMap R F) (maximalIdeal R) = R ∙ (algebraMap R F π ^ (1 : ℤ)) := by
  rw [hπ.maximalIdeal_eq]
  show Submodule.map _ (Submodule.span R {π}) = _
  rw [Submodule.map_span, Set.image_singleton, zpow_one]
  rfl

lemma two_smul_le (N : Submodule R F) : (2 : F) • N ≤ N := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.1 hy
  have : (2 : F) • x = (2 : R) • x := by rw [smul_eq_mul, Algebra.smul_def, map_ofNat]
  rw [this]; exact N.smul_mem _ hx

/-- If `T` is a proper submodule of `σ𝔬`, its non-zero elements have order `> ord σ`. -/
lemma le_span_pow_succ_of_lt (hπ : Irreducible π) {σ : F} (hσ : σ ≠ 0) {T : Submodule R F} (hT : T < R ∙ σ) :
    T ≤ R ∙ (algebraMap R F π ^ (dord hπ σ + 1)) := by
  intro β hβ
  by_cases hβ0 : β = 0
  · rw [hβ0]; exact zero_mem _
  have h1 : β ∈ R ∙ σ := hT.le hβ
  have h2 := (mem_span_iff hπ hβ0 hσ).1 h1
  rw [mem_span_zpow_iff hπ hβ0]
  by_contra hlt
  have heq : dord hπ σ = dord hπ β := by omega
  have : R ∙ σ ≤ T := by
    rw [span_eq_of_dord_eq hπ hσ hβ0 heq, span_singleton_le_iff_mem]; exact hβ
  exact hT.not_ge this

lemma sqRoots_le (hπ : Irreducible π) {e : ℤ} {n n' : Submodule R F} (hn : n ≤ R ∙ (algebraMap R F π ^ e))
    (hn' : n' ≤ R ∙ (algebraMap R F π ^ (e + 1))) :
    span R {z : F | (R ∙ z) * (R ∙ z) = n * n'} ≤ R ∙ (algebraMap R F π ^ (e + 1)) := by
  rw [span_le]
  intro z hz
  have hzz : z * z ∈ R ∙ (algebraMap R F π ^ (e + (e + 1))) := by
    have h1 : z * z ∈ (R ∙ z) * (R ∙ z) :=
      Submodule.mul_mem_mul (mem_span_singleton_self z) (mem_span_singleton_self z)
    have hz' : (R ∙ z) * (R ∙ z) = n * n' := hz
    rw [hz'] at h1
    have := mul_le_mul' hn hn' h1
    rwa [mulpow hπ] at this
  by_cases hz0 : z = 0
  · rw [hz0]; exact zero_mem _
  · rw [SetLike.mem_coe, mem_span_zpow_iff hπ hz0]
    rw [mem_span_zpow_iff hπ (mul_ne_zero hz0 hz0), dord_mul hπ hz0 hz0] at hzz
    omega

lemma mem_pfrac_of_mul (hπ : Irreducible π) {σ f : F} (hσ : σ ≠ 0) {e : ℤ} (he : dord hπ σ = e)
    (hf : f * (σ * σ) ∈ R ∙ (algebraMap R F π ^ (e + (e + 1)))) :
    f ∈ R ∙ (algebraMap R F π ^ (1 : ℤ)) := by
  by_cases hf0 : f = 0
  · rw [hf0]; exact zero_mem _
  rw [mem_span_zpow_iff hπ (mul_ne_zero hf0 (mul_ne_zero hσ hσ)), dord_mul hπ hf0 (mul_ne_zero hσ hσ),
    dord_mul hπ hσ hσ] at hf
  rw [mem_span_zpow_iff hπ hf0]
  omega

lemma norms_le_scale (L : Submodule R V) {t : ℕ} (Ls : Fin t → Submodule R V) (k : Fin t) :
    ((fundNormGroup Q L Ls k : Set F) ⊆ scale Q (Ls k)) ∧ fundNormIdeal Q L Ls k ≤ scale Q (Ls k) := by
  have h1 : fundNormIdeal Q L Ls k ≤ scale Q (Ls k) :=
    (normIdeal_le_scale Q _).trans (scale_subA_le Q _ _)
  exact ⟨fun x hx => h1 (normGroup_subset_normIdeal Q _ hx), h1⟩

end FIdealAux

/-- **$\mathfrak f_i \subseteq \mathfrak p$** (O'Meara 1963, §93E, p. 264, "in all cases"): for a finitely generated
lattice $L$ with Jordan splitting, $\mathfrak f_i \subseteq \mathfrak p$ (here `𝔭` is the maximal ideal of $R$ as an
$R$-submodule of $F$). Indices are $0$-based: `j = i + 1`. Proof: $\mathfrak d(\xi) \subseteq \xi\mathfrak o$,
$\alpha \in \mathfrak g_i \subseteq \mathfrak s_i$, $\beta \in \mathfrak g_{i+1} \subseteq \mathfrak s_{i+1} \subseteq
\mathfrak p\mathfrak s_i$, and a $z$ with $(z\mathfrak o)^2 = \mathfrak n_i\mathfrak n_{i+1} \subseteq \mathfrak p\mathfrak
s_i^2$ lies in $\mathfrak p\mathfrak s_i$; so the numerator of $\mathfrak f_i$ lies in $\mathfrak p\mathfrak s_i^2$. -/
@[kb "omeara1963" "§93E, p. 264 (f_i ⊆ p in all cases)"]
theorem fIdeal_le_pfrac (hπ : Irreducible π) {L : Submodule R V} (hfg : L.FG) {t : ℕ} {Ls : Fin t → Submodule R V}
    (hJ : IsJordanSplitting Q L Ls) (i j : Fin t) (hij : (j : ℕ) = i + 1) :
    fIdeal Q L Ls i j ≤ Submodule.map (Algebra.linearMap R F) (maximalIdeal R) := by
  have hLs : ∀ k, Ls k ≤ L := fun k => hJ.split.iSup_eq ▸ le_iSup Ls k
  obtain ⟨σ, hσ, hs⟩ := exists_eq_span_singleton (R := R) (scale_fg Q (FG.of_le hfg (hLs i))) (hJ.modular i).1
  have hlt : scale Q (Ls j) < scale Q (Ls i) :=
    hJ.scale_strictAnti (show i < j by rw [Fin.lt_def]; omega)
  rw [hs] at hlt
  obtain ⟨e, he⟩ : ∃ e, dord hπ σ = e := ⟨_, rfl⟩
  have hP : scale Q (Ls i) ≤ R ∙ (algebraMap R F π ^ e) := by
    rw [hs, span_eq_of_dord_eq hπ hσ (zpow_ne_zero _ (alg_pi_ne_zero hπ)) (by rw [dord_zpow, he])]
  have hP1 : scale Q (Ls j) ≤ R ∙ (algebraMap R F π ^ (e + 1)) := by
    have := le_span_pow_succ_of_lt hπ hσ hlt
    rwa [he] at this
  obtain ⟨hgi, hni⟩ := norms_le_scale Q L Ls i
  obtain ⟨hgj, hnj⟩ := norms_le_scale Q L Ls j
  have hdef : ⨆ (α : F) (_ : α ∈ fundNormGroup Q L Ls i) (β : F) (_ : β ∈ fundNormGroup Q L Ls j),
      quadDefect R (α * β) ≤ R ∙ (algebraMap R F π ^ (e + (e + 1))) := by
    refine iSup_le fun α => iSup_le fun hα => iSup_le fun β => iSup_le fun hβ => ?_
    refine (quadDefect_le_span _).trans ((span_singleton_le_iff_mem _ _).2 ?_)
    have := Submodule.mul_mem_mul (hP (hgi hα)) (hP1 (hgj hβ))
    rwa [mulpow hπ] at this
  have hS := sqRoots_le hπ (hni.trans hP) (hnj.trans hP1)
  have hsec : (2 : F) • (span R {z : F | (R ∙ z) * (R ∙ z) = fundNormIdeal Q L Ls i * fundNormIdeal Q L Ls j} *
      (R ∙ σ)) ≤ R ∙ (algebraMap R F π ^ (e + (e + 1))) := by
    refine (two_smul_le _).trans ?_
    rw [← hs] at *
    have := mul_le_mul' hS hP
    rw [mulpow hπ, add_comm (e + 1) e] at this
    exact this
  have hX := sup_le hdef hsec
  have key : fIdeal Q L Ls i j = fIdealOf R (R ∙ σ) (fundNormGroup Q L Ls i) (fundNormGroup Q L Ls j)
      (fundNormIdeal Q L Ls i) (fundNormIdeal Q L Ls j) := by
    unfold fIdeal; rw [hs]
  intro f hf
  rw [key, fIdealOf, span_mul_span', mem_div_span_iff] at hf
  rw [pfrac_eq hπ]
  exact mem_pfrac_of_mul hπ hσ he (hX hf)

end Pfrac

section Odd93

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)] {π : R}
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

namespace FIdealAux

lemma fundNormGenerator_ne_zero {L : Submodule R V} (hfg : L.FG) {t : ℕ} {Ls : Fin t → Submodule R V}
    (hJ : IsJordanSplitting Q L Ls) {a : Fin t → F} (ha : IsFundNormGenerators Q L Ls a) (k : Fin t) :
    a k ≠ 0 := by
  intro h0
  have hn : normIdeal Q (fundSub Q L Ls k) = ⊥ := by rw [← (ha k).2, h0]; simp
  have hbot : scale Q (Ls k) = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    have h1 : (2 : F) • c ∈ (2 : F) • scale Q (fundSub Q L Ls k) := by
      rw [scale_fundSub Q hfg hJ k]; exact Submodule.smul_mem_pointwise_smul _ _ _ hc
    have h2 := normGroupIdeal_le_normIdeal Q _ (two_smul_scale_le_normGroupIdeal Q _ h1)
    rw [hn] at h2
    have h3 : (2 : F) * c = 0 := by simpa using h2
    have := (mul_eq_zero.1 h3).resolve_left (two_ne_zero' F)
    rw [this]; exact zero_mem _
  exact (hJ.modular k).1 ((hJ.modular k).2.1.symm.trans hbot)

end FIdealAux

/-- **93:26, odd case** (O'Meara 1963, §93E, 93:26, p. 267): let $L$ be a finitely generated lattice with Jordan
splitting and fundamental norm generators $a_i$. If $u_i + u_{i+1} = \operatorname{ord} a_i + \operatorname{ord}
a_{i+1}$ is odd, then $\mathfrak s_i^2\mathfrak f_i = a_ia_{i+1}\mathfrak o$. (Indices $0$-based, `j = i + 1`.) Proof:
$\mathfrak d(\alpha\beta) \subseteq \alpha\beta\mathfrak o \subseteq a_ia_{i+1}\mathfrak o$ for $\alpha \in \mathfrak g_i
\subseteq a_i\mathfrak o$, $\beta \in \mathfrak g_{i+1} \subseteq a_{i+1}\mathfrak o$; conversely an element of odd
order has $\mathfrak d(\xi) = \xi\mathfrak o$ (63A) and $a_ia_{i+1} \in \mathfrak g_i\mathfrak g_{i+1}$.
*Update:* the dyadic, Henselian and finite-residue-field hypotheses are not needed for this case. -/
@[kb "omeara1963" "§93E, 93:26, p. 267 (s_i² f_i = a_i a_{i+1} o when u_i + u_{i+1} is odd)"]
theorem mul_fIdeal_of_odd (hπ : Irreducible π) {L : Submodule R V} (hfg : L.FG) {t : ℕ}
    {Ls : Fin t → Submodule R V} (hJ : IsJordanSplitting Q L Ls) {a : Fin t → F}
    (ha : IsFundNormGenerators Q L Ls a) (i j : Fin t)
    (hodd : Odd (dord hπ (a i) + dord hπ (a j))) :
    scale Q (Ls i) * scale Q (Ls i) * fIdeal Q L Ls i j = R ∙ (a i * a j) := by
  have hLs : ∀ k, Ls k ≤ L := fun k => hJ.split.iSup_eq ▸ le_iSup Ls k
  obtain ⟨σ, hσ, hs⟩ := exists_eq_span_singleton (R := R) (scale_fg Q (FG.of_le hfg (hLs i))) (hJ.modular i).1
  have hai := fundNormGenerator_ne_zero Q hfg hJ ha i
  have haj := fundNormGenerator_ne_zero Q hfg hJ ha j
  have key : fIdeal Q L Ls i j = fIdealOf R (R ∙ σ) (fundNormGroup Q L Ls i) (fundNormGroup Q L Ls j)
      (R ∙ a i) (R ∙ a j) := by
    unfold fIdeal fundNormIdeal; rw [hs, (ha i).2, (ha j).2]
  rw [hs, key, mul_fIdealOf_odd hπ hσ hai haj hodd]
  apply le_antisymm
  · refine iSup_le fun α => iSup_le fun hα => iSup_le fun β => iSup_le fun hβ => ?_
    refine (quadDefect_le_span _).trans ((span_singleton_le_iff_mem _ _).2 ?_)
    have h1 : α ∈ R ∙ a i := (ha i).2 ▸ normGroup_subset_normIdeal Q _ hα
    have h2 : β ∈ R ∙ a j := (ha j).2 ▸ normGroup_subset_normIdeal Q _ hβ
    have := Submodule.mul_mem_mul h1 h2
    rwa [span_mul_span'] at this
  · obtain ⟨u, hu, hu'⟩ := dord_spec hπ (mul_ne_zero hai haj)
    rw [dord_mul hπ hai haj] at hu'
    have hq := quadDefect_of_odd (F := F) hπ hu hodd
    rw [← hu'] at hq
    rw [← hq]
    exact le_iSup_of_le (a i) <| le_iSup_of_le (ha i).1 <| le_iSup_of_le (a j) <|
      le_iSup_of_le (ha j).1 le_rfl

end Odd93

end QuadFormsKB.OMeara
