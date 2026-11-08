/-
# Hanke 2013, Algorithm 3.13: existence of the decomposition $V = R\perp H\perp A$

J. Hanke, *Algorithms for computing maximal lattices in bilinear (and quadratic) spaces over number fields*,
Contemp. Math. 587 (2013); source used: arXiv:1208.2481v3 (bib key `hanke2013algorithms`), Algorithm 3.13, p. 12.

**Setting.** As in `FiniteField.lean`: $K$ a field with $2\ne0$, $V$ a finite-dimensional $K$-vector space and
$B$ = `B : LinearMap.BilinForm K V` a symmetric bilinear form (`hB`); `IsTotIso`, `IsMaxTotIso` are the paper's
(maximal) totally isotropic subspaces.

**Proves** the existence part of Algorithm 3.13 (`algorithm_3_13_exists`): there are subspaces $R$, $L$, $L'$, $A$ with
$R = \operatorname{Rad}(V)$, $V = R + L + L' + A$, $L$ totally isotropic, $L\cap R = L\cap L' = 0$,
$\dim L = \dim L'$ and $L'$ paired non-degenerately with $L$ (so $H = L\oplus L'$ has the Lagrangian $L$ of half its
dimension), $A$ anisotropic with $B(L + L', A) = 0$; and then $M = R + L$ is maximal totally isotropic (the
maximality is `algorithm_3_13`, whose hypotheses are exactly these). The paper produces the decomposition by splitting
off hyperbolic planes (Lemma 3.10, Algorithms 3.11, 3.12) over a finite field; the proof here is for any field with
$2\ne0$: start from a maximal totally isotropic $M$ (it contains $R$), take $A$ a complement of $M$ in $M^\perp$ (it is
anisotropic by maximality, so $V = A\oplus A^\perp$), $L'$ a complement of $M$ in $A^\perp$ and $L$ a complement of $R$
in $M$. `algorithm_3_13_exists_lagrangian` moreover makes $L'$ totally isotropic (so $H = L\oplus L'$ is a sum of
two Lagrangians, i.e. hyperbolic), by shearing $L'$ along $L$.
-/
import QuadFormsKB.Literature.Hanke2013Algorithms.FiniteField
import QuadFormsKB.Citation

open Module

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Hanke2013Algorithms

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- A complement of $N$ inside $P\supseteq N$. -/
theorem exists_compl_in {N P : Submodule K V} (h : N ≤ P) :
    ∃ C : Submodule K V, C ≤ P ∧ N ⊔ C = P ∧ N ⊓ C = ⊥ := by
  obtain ⟨C', hC'⟩ := Submodule.exists_isCompl N
  refine ⟨C' ⊓ P, inf_le_right, ?_, ?_⟩
  · rw [← sup_inf_assoc_of_le C' h, hC'.sup_eq_top, top_inf_eq]
  · rw [← inf_assoc, hC'.inf_eq_bot, bot_inf_eq]

/-- A maximal totally isotropic subspace exists (finite dimension). -/
theorem exists_isMaxTotIso (B : LinearMap.BilinForm K V) : ∃ M, IsMaxTotIso B M := by
  obtain ⟨M, hM, hmax⟩ := (set_has_maximal_iff_noetherian (R := K) (M := V)).2 inferInstance
    {M : Submodule K V | IsTotIso B M} ⟨⊥, fun w hw => by rw [Submodule.mem_bot] at hw; simp [hw]⟩
  exact ⟨M, hM, fun M' hle hM' => by
    by_contra hne
    exact hmax M' hM' (lt_of_le_of_ne hle (Ne.symm hne))⟩

/-- The sum of two orthogonal totally isotropic subspaces is totally isotropic. -/
theorem isTotIso_sup {B : LinearMap.BilinForm K V} (hB : ∀ x y, B x y = B y x) {M N : Submodule K V}
    (hM : IsTotIso B M) (hN : IsTotIso B N) (hMN : ∀ m ∈ M, ∀ n ∈ N, B m n = 0) : IsTotIso B (M ⊔ N) := by
  intro x hx
  obtain ⟨m, hm, n, hn, rfl⟩ := Submodule.mem_sup.1 hx
  have h1 := hMN m hm n hn
  have h2 : B n m = 0 := by rw [hB]; exact h1
  simp only [map_add, LinearMap.add_apply, hM m hm, hN n hn, h1, h2, add_zero]

/-- **Algorithm 3.13, existence of the decomposition** (Hanke 2013, p. 12), for a symmetric bilinear form over a field
with $2\ne0$: there are subspaces $R = \operatorname{Rad}(V)$ (`LinearMap.ker B`), $L$, $L'$, $A$ with $L\cap R = L\cap L' = 0$,
$L$ totally isotropic, $A$ anisotropic, $B(L, A) = B(L', A) = 0$, every $\vec l'\in L'\setminus0$ pairing non-trivially
with $L$, $V = R + L + L' + A$ and $\dim L = \dim L'$ (the decomposition $V = R\perp(L\oplus L')\perp A$ with $L$ a
Lagrangian of $H = L\oplus L'$); and $M = R + L$ is maximal totally isotropic. See the file header for the proof and for
`algorithm_3_13_exists_lagrangian` for $L'$ totally isotropic. -/
@[kb "hanke2013algorithms" "Algorithm 3.13, p. 12 (the decomposition V = R ⊥ H ⊥ A exists)"]
theorem algorithm_3_13_exists (B : LinearMap.BilinForm K V) (hB : ∀ x y, B x y = B y x) (h2 : (2 : K) ≠ 0) :
    ∃ R L L' A : Submodule K V, R = LinearMap.ker B ∧ L ⊓ R = ⊥ ∧ L ⊓ L' = ⊥ ∧ IsTotIso B L ∧
      (∀ a ∈ A, B a a = 0 → a = 0) ∧ (∀ l ∈ L, ∀ a ∈ A, B l a = 0) ∧ (∀ l' ∈ L', ∀ a ∈ A, B l' a = 0) ∧
      (∀ l' ∈ L', l' ≠ 0 → ∃ l₀ ∈ L, B l' l₀ ≠ 0) ∧ R ⊔ L ⊔ L' ⊔ A = ⊤ ∧
      finrank K L = finrank K L' ∧ IsMaxTotIso B (R ⊔ L) := by
  obtain ⟨M, hMi, hMmax⟩ := exists_isMaxTotIso B
  have hMM : ∀ m ∈ M, ∀ m' ∈ M, B m m' = 0 := fun m hm m' hm' => hMi.bil_eq_zero hB h2 hm hm'
  set R := LinearMap.ker B with hRdef
  have hRB : ∀ r ∈ R, ∀ x, B r x = 0 := fun r hr x => by
    rw [LinearMap.mem_ker.1 hr, LinearMap.zero_apply]
  have hRM : R ≤ M := by
    have hiso : IsTotIso B (M ⊔ R) := isTotIso_sup hB hMi (fun r hr => hRB r hr r) fun m _ r hr => by
      rw [hB]; exact hRB r hr m
    have := hMmax (M ⊔ R) le_sup_left hiso
    rw [← this]; exact le_sup_right
  set P := B.orthogonal M with hPdef
  have hMP : M ≤ P := fun x hx => (LinearMap.BilinForm.mem_orthogonal_iff).2 fun m hm => hMM m hm x hx
  obtain ⟨A, hAP, hMA, hMA0⟩ := exists_compl_in hMP
  have hPA : ∀ a ∈ A, ∀ m ∈ M, B m a = 0 := fun a ha m hm =>
    (LinearMap.BilinForm.mem_orthogonal_iff).1 (hAP ha) m hm
  have hAaniso : ∀ a ∈ A, B a a = 0 → a = 0 := by
    intro a ha haa
    have hspan : IsTotIso B (Submodule.span K {a}) := fun x hx => by
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hx
      simp [haa]
    have hiso : IsTotIso B (M ⊔ Submodule.span K {a}) := isTotIso_sup hB hMi hspan fun m hm x hx => by
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hx
      simp [hPA a ha m hm]
    have hM' := hMmax _ le_sup_left hiso
    have ham : a ∈ M := by
      rw [← hM']; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self a)
    have : a ∈ M ⊓ A := ⟨ham, ha⟩
    rwa [hMA0, Submodule.mem_bot] at this
  set Aperp := B.orthogonal A with hAperpdef
  have hAnd : (B.restrict A).Nondegenerate := by
    refine ⟨fun x hx => Subtype.ext (hAaniso x x.2 (by simpa using hx x)),
      fun y hy => Subtype.ext (hAaniso y y.2 (by simpa using hy y))⟩
  have hrefl : B.IsRefl := fun x y h => by rw [hB]; exact h
  have hcompl : IsCompl A Aperp := B.isCompl_orthogonal_of_restrict_nondegenerate hrefl hAnd
  have hMAp : M ≤ Aperp := fun m hm => (LinearMap.BilinForm.mem_orthogonal_iff).2 fun a ha => by
    rw [hB]; exact hPA a ha m hm
  obtain ⟨L', hL'A, hML', hML'0⟩ := exists_compl_in hMAp
  obtain ⟨L, hLM, hRL, hRL0⟩ := exists_compl_in hRM
  have hLA : ∀ l ∈ L, ∀ a ∈ A, B l a = 0 := fun l hl a ha => hPA a ha l (hLM hl)
  have hL'A' : ∀ l' ∈ L', ∀ a ∈ A, B l' a = 0 := fun l' hl' a ha => by
    rw [hB]; exact (LinearMap.BilinForm.mem_orthogonal_iff).1 (hL'A hl') a ha
  have hpair : ∀ l' ∈ L', l' ≠ 0 → ∃ l₀ ∈ L, B l' l₀ ≠ 0 := by
    intro l' hl' hne
    by_contra h
    push Not at h
    have hl'P : l' ∈ P := (LinearMap.BilinForm.mem_orthogonal_iff).2 fun m hm => by
      rw [← hRL] at hm
      obtain ⟨r, hr, l, hl, rfl⟩ := Submodule.mem_sup.1 hm
      rw [map_add, LinearMap.add_apply, hRB r hr, hB, h l hl, zero_add]
    rw [← hMA] at hl'P
    obtain ⟨m, hm, a, ha, hma⟩ := Submodule.mem_sup.1 hl'P
    have haAp : a ∈ Aperp := by
      have : a = l' - m := by rw [← hma]; abel
      rw [this]; exact Aperp.sub_mem (hL'A hl') (hMAp hm)
    have ha0 : a = 0 := by
      have : a ∈ A ⊓ Aperp := ⟨ha, haAp⟩
      rwa [hcompl.inf_eq_bot, Submodule.mem_bot] at this
    have : l' ∈ M ⊓ L' := ⟨by rw [← hma, ha0, add_zero]; exact hm, hl'⟩
    rw [hML'0, Submodule.mem_bot] at this
    exact hne this
  have hsup : R ⊔ L ⊔ L' ⊔ A = ⊤ := by
    rw [hRL, hML', sup_comm, hcompl.sup_eq_top]
  have hLL' : L ⊓ L' = ⊥ := eq_bot_iff.2 fun x hx => by
    have : x ∈ M ⊓ L' := ⟨hLM hx.1, hx.2⟩
    rwa [hML'0] at this
  -- `dim L = dim L'`: the pairing `L' × L → K` is non-degenerate on both sides
  have hrank : finrank K L = finrank K L' := by
    set g : L' →ₗ[K] Module.Dual K L := (B.domRestrict L').compl₂ L.subtype
    set f : L →ₗ[K] Module.Dual K L' := (B.domRestrict L).compl₂ L'.subtype
    have hg : Function.Injective g := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro x hx
      rw [LinearMap.mem_ker] at hx
      by_contra hx0
      have hx0' : (x : V) ≠ 0 := fun h => hx0 (by rw [Submodule.mem_bot]; exact Subtype.ext h)
      obtain ⟨l₀, hl₀, hne⟩ := hpair x x.2 hx0'
      exact hne (by simpa [g] using LinearMap.congr_fun hx ⟨l₀, hl₀⟩)
    have hf : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro x hx
      rw [LinearMap.mem_ker] at hx
      have hxL' : ∀ l' ∈ L', B x l' = 0 := fun l' hl' => by
        simpa [f] using LinearMap.congr_fun hx ⟨l', hl'⟩
      have hxR : (x : V) ∈ R := by
        rw [LinearMap.mem_ker]
        ext y
        have hy : y ∈ R ⊔ L ⊔ L' ⊔ A := hsup ▸ Submodule.mem_top
        obtain ⟨y₁, hy₁, a, ha, rfl⟩ := Submodule.mem_sup.1 hy
        obtain ⟨y₂, hy₂, l', hl', rfl⟩ := Submodule.mem_sup.1 hy₁
        obtain ⟨r, hr, l, hl, rfl⟩ := Submodule.mem_sup.1 hy₂
        have hxr : B x r = 0 := by rw [hB]; exact hRB r hr x
        simp only [map_add, hxr, hMM x (hLM x.2) l (hLM hl), hxL' l' hl', hLA x x.2 a ha, add_zero,
          LinearMap.zero_apply]
      have : (x : V) ∈ L ⊓ R := ⟨x.2, hxR⟩
      rw [inf_comm, hRL0, Submodule.mem_bot] at this
      rw [Submodule.mem_bot]; exact Subtype.ext this
    have h1 := LinearMap.finrank_le_finrank_of_injective hg
    have h2' := LinearMap.finrank_le_finrank_of_injective hf
    rw [Subspace.dual_finrank_eq] at h1 h2'
    exact le_antisymm h2' h1
  refine ⟨R, L, L', A, rfl, by rw [inf_comm]; exact hRL0, hLL', fun l hl => hMi l (hLM hl), hAaniso, hLA,
    hL'A', hpair, hsup, hrank, ?_⟩
  rw [hRL]; exact ⟨hMi, hMmax⟩

/-- **Algorithm 3.13, the decomposition with $H$ hyperbolic** (Hanke 2013, p. 12, "by writing the hyperbolic space $H$ as a
(non-orthogonal) direct sum of two Lagrangian subspaces $H = L\oplus L'$"): `algorithm_3_13_exists` with, in addition, $L'$
totally isotropic. *Proof*: shear $L'$ along $L$: with $f : L\to L'^*$, $\vec l\mapsto B(\vec l,\cdot)$ (bijective) put
$S\vec l' = f^{-1}(-\tfrac12B(\vec l',\cdot))$ and replace $L'$ by $\{\vec l' + S\vec l'\}$. -/
@[kb "hanke2013algorithms" "Algorithm 3.13, p. 12 (V = R ⊥ H ⊥ A with H = L ⊕ L' a sum of two Lagrangians)"]
theorem algorithm_3_13_exists_lagrangian (B : LinearMap.BilinForm K V) (hB : ∀ x y, B x y = B y x)
    (h2 : (2 : K) ≠ 0) :
    ∃ R L L' A : Submodule K V, R = LinearMap.ker B ∧ L ⊓ R = ⊥ ∧ L ⊓ L' = ⊥ ∧ IsTotIso B L ∧ IsTotIso B L' ∧
      (∀ a ∈ A, B a a = 0 → a = 0) ∧ (∀ l ∈ L, ∀ a ∈ A, B l a = 0) ∧ (∀ l' ∈ L', ∀ a ∈ A, B l' a = 0) ∧
      (∀ l' ∈ L', l' ≠ 0 → ∃ l₀ ∈ L, B l' l₀ ≠ 0) ∧ R ⊔ L ⊔ L' ⊔ A = ⊤ ∧
      finrank K L = finrank K L' ∧ IsMaxTotIso B (R ⊔ L) := by
  obtain ⟨R, L, L', A, hR, hLR, hLL', hLi, hA, hLA, hL'A, hpair, hsup, hrank, hmax⟩ :=
    algorithm_3_13_exists B hB h2
  have hLL : ∀ l ∈ L, ∀ l₀ ∈ L, B l l₀ = 0 := fun l hl l₀ hl₀ => hLi.bil_eq_zero hB h2 hl hl₀
  have hRB : ∀ r ∈ R, ∀ x, B r x = 0 := fun r hr x => by
    rw [hR] at hr; rw [LinearMap.mem_ker.1 hr, LinearMap.zero_apply]
  -- `f : L → L'^*` is bijective
  obtain ⟨f, hfB⟩ : ∃ f : L →ₗ[K] Module.Dual K L', ∀ l m, f l m = B l m :=
    ⟨(B.domRestrict L).compl₂ L'.subtype, fun _ _ => rfl⟩
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have hxL' : ∀ l' ∈ L', B x l' = 0 := fun l' hl' => by
      rw [← hfB x ⟨l', hl'⟩, hx]; rfl
    have hxR : (x : V) ∈ R := by
      rw [hR, LinearMap.mem_ker]
      ext y
      have hy : y ∈ R ⊔ L ⊔ L' ⊔ A := hsup ▸ Submodule.mem_top
      obtain ⟨y₁, hy₁, a, ha, rfl⟩ := Submodule.mem_sup.1 hy
      obtain ⟨y₂, hy₂, l', hl', rfl⟩ := Submodule.mem_sup.1 hy₁
      obtain ⟨r, hr, l, hl, rfl⟩ := Submodule.mem_sup.1 hy₂
      have hxr : B x r = 0 := by rw [hB]; exact hRB r hr x
      simp only [map_add, hxr, hLL x x.2 l hl, hxL' l' hl', hLA x x.2 a ha, add_zero, LinearMap.zero_apply]
    have : (x : V) ∈ L ⊓ R := ⟨x.2, hxR⟩
    rw [hLR, Submodule.mem_bot] at this
    rw [Submodule.mem_bot]; exact Subtype.ext this
  have hdim : finrank K L = finrank K (Module.Dual K L') := by rw [Subspace.dual_finrank_eq]; exact hrank
  obtain ⟨e, he⟩ : ∃ e : L ≃ₗ[K] Module.Dual K L', ∀ l m, e l m = B l m :=
    ⟨f.linearEquivOfInjective hf hdim, fun l m => hfB l m⟩
  obtain ⟨g, hg⟩ : ∃ g : L' →ₗ[K] Module.Dual K L', ∀ l m, g l m = B l m :=
    ⟨(B.domRestrict L').compl₂ L'.subtype, fun _ _ => rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : L' →ₗ[K] L, ∀ l m : L', B (S l) m = -(2 : K)⁻¹ * B l m := by
    refine ⟨e.symm.toLinearMap ∘ₗ ((-(2 : K)⁻¹) • g), fun l m => ?_⟩
    have h1 : e (e.symm ((-(2 : K)⁻¹) • g l)) = (-(2 : K)⁻¹) • g l := e.apply_symm_apply _
    have h3 : (e.symm.toLinearMap ∘ₗ ((-(2 : K)⁻¹) • g)) l = e.symm ((-(2 : K)⁻¹) • g l) := rfl
    rw [h3, ← he, h1, LinearMap.smul_apply, hg, smul_eq_mul]
  obtain ⟨φ, hφ⟩ : ∃ φ : L' →ₗ[K] V, ∀ l : L', φ l = (l : V) + (S l : V) :=
    ⟨L'.subtype + L.subtype ∘ₗ S, fun _ => rfl⟩
  set L'' := LinearMap.range φ
  have hφinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker, hφ] at hx
    have : (x : V) ∈ L ⊓ L' := ⟨by
      have : (x : V) = -(S x : V) := by rw [← sub_eq_zero, sub_neg_eq_add, hx]
      rw [this]; exact L.neg_mem (S x).2, x.2⟩
    rw [hLL', Submodule.mem_bot] at this
    rw [Submodule.mem_bot]; exact Subtype.ext this
  refine ⟨R, L, L'', A, hR, hLR, ?_, hLi, ?_, hA, hLA, ?_, ?_, ?_, ?_, hmax⟩
  · rw [eq_bot_iff]
    rintro x ⟨hxL, ⟨l, rfl⟩⟩
    rw [hφ] at hxL ⊢
    have hl : (l : V) ∈ L ⊓ L' := ⟨by
      have : (l : V) = ((l : V) + (S l : V)) - (S l : V) := by abel
      rw [this]; exact L.sub_mem hxL (S l).2, l.2⟩
    rw [hLL', Submodule.mem_bot] at hl
    have hl0 : l = 0 := Subtype.ext hl
    rw [Submodule.mem_bot, hl0, map_zero]; simp
  · rintro _ ⟨l, rfl⟩
    rw [hφ]
    have h1 : B (S l : V) (S l : V) = 0 := hLL _ (S l).2 _ (S l).2
    have h2' : B (l : V) (S l : V) = B (S l : V) l := hB _ _
    simp only [map_add, LinearMap.add_apply, h1, add_zero]
    rw [h2', hS l l]
    field_simp
    ring
  · rintro _ ⟨l, rfl⟩ a ha
    rw [hφ, map_add, LinearMap.add_apply, hL'A l l.2 a ha, hLA _ (S l).2 a ha, add_zero]
  · rintro _ ⟨l, rfl⟩ hne
    have hl0 : (l : V) ≠ 0 := fun h => hne (by rw [hφ, h, show l = 0 from Subtype.ext h, map_zero]; simp)
    obtain ⟨l₀, hl₀, hB0⟩ := hpair l l.2 hl0
    refine ⟨l₀, hl₀, ?_⟩
    rw [hφ, map_add, LinearMap.add_apply, hLL _ (S l).2 _ hl₀, add_zero]
    exact hB0
  · apply eq_top_iff.2
    rw [← hsup]
    have h1 : R ⊔ L ≤ R ⊔ L ⊔ L'' ⊔ A :=
      (le_sup_left : R ⊔ L ≤ R ⊔ L ⊔ L'').trans (le_sup_left : R ⊔ L ⊔ L'' ≤ R ⊔ L ⊔ L'' ⊔ A)
    have h3 : A ≤ R ⊔ L ⊔ L'' ⊔ A := le_sup_right
    have h2 : L' ≤ R ⊔ L ⊔ L'' ⊔ A := by
      intro x hx
      have hx' : x = φ ⟨x, hx⟩ - (S ⟨x, hx⟩ : V) := by rw [hφ]; abel
      rw [hx']
      exact Submodule.sub_mem _ ((le_sup_left : R ⊔ L ⊔ L'' ≤ R ⊔ L ⊔ L'' ⊔ A)
        (Submodule.mem_sup_right ⟨_, rfl⟩)) (h1 (Submodule.mem_sup_right (S ⟨x, hx⟩).2))
    exact sup_le (sup_le h1 h2) h3
  · rw [hrank, LinearMap.finrank_range_of_inj hφinj]

end QuadFormsKB.Hanke2013Algorithms
