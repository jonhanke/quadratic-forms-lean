/-
# Kitaoka 1993, Proposition 1.1.2, Corollary 1.1.1 and Proposition 1.2.2: subspaces meeting the radical trivially

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §1.1, Proposition 1.1.2 and Corollary 1.1.1, p. 3;
§1.2, Proposition 1.2.2, p. 11 (printed pages).

**Setting.** $F$ is a field (every characteristic) and $U$ a finite-dimensional vector space over $F$ (Kitaoka's spaces
are finite-dimensional). For a bilinear form $b$ on $U$ (Mathlib `LinearMap.BilinForm F U`) and a subspace $V$,
$V^\perp = \{x \in U \mid b(V, x) = 0\}$ is `b.orthogonal V`, and the radical $U^\perp$ is `b.orthogonal ⊤`. For a
quadratic form $q$ (Mathlib `QuadraticForm F U`) the associated bilinear form is $b(x, y) = q(x+y) - q(x) - q(y)$
(`QuadraticMap.polarBilin q`). A space is *regular* when $b$ is nondegenerate (`LinearMap.BilinForm.Nondegenerate`);
a subspace $W$ is regular when the restriction `b.restrict W` is. A *hyperbolic space* is an orthogonal sum of
hyperbolic planes, `QuadraticForm.hyperbolicSpace F k` ($(x_i, y_i)_{i<k} \mapsto \sum_i x_i y_i$).

**Proves** (unconditional)
* `proposition112` (Proposition 1.1.2): $V \cap U^\perp = \{0\}$ if and only if every linear form on $V$ is
  $x \mapsto b(x, y)$ for some $y \in U$; and then $\dim V^\perp = \dim U - \dim V$ (written
  $\dim V^\perp + \dim V = \dim U$).
* `corollary111` (Corollary 1.1.1): $V \cap U^\perp = \{0\}$ if and only if $V$ lies in a regular subspace of $U$.
* `proposition122` (Proposition 1.2.2): if $V$ is totally isotropic ($q(V) = 0$) and $V \cap U^\perp = \{0\}$, there is
  a totally isotropic subspace $W$ with $\dim W = \dim V$, $V \cap W = \{0\}$ and $V \oplus W$ hyperbolic.
* `proposition122_plane` (the last sentence of Proposition 1.2.2): a regular isotropic quadratic space of dimension
  $2$ is a hyperbolic plane.
-/
import QuadFormsKB.Witt.Extension
import QuadFormsKB.Witt.Decomposition
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.TotallySplit

open QuadraticMap Module

noncomputable section

namespace QuadFormsKB.Kitaoka.Radical

open _root_.QuadraticForm.Witt

variable {F U : Type*} [Field F] [AddCommGroup U] [Module F U] [FiniteDimensional F U]

/-- **Kitaoka 1993, Proposition 1.1.2** (p. 3). Let $b$ be a symmetric bilinear form on a finite-dimensional space
$U$ over a field $F$ and $V$ a subspace. Then $V \cap U^\perp = \{0\}$ if and only if
$\operatorname{Hom}_F(V, F) = \{x \mapsto b(x, y) \mid y \in U\}$, and in that case
$\dim V^\perp = \dim U - \dim V$. Unconditional. -/
@[kb "kitaoka1993" "§1.1, Prop. 1.1.2, p. 3"]
theorem proposition112 (B : LinearMap.BilinForm F U) (hB : B.IsSymm) (V : Submodule F U) :
    (V ⊓ B.orthogonal ⊤ = ⊥ ↔ ∀ f : Module.Dual F V, ∃ y : U, ∀ x : V, f x = B x y) ∧
    (V ⊓ B.orthogonal ⊤ = ⊥ → finrank F (B.orthogonal V) + finrank F V = finrank F U) := by
  classical
  set T : U →ₗ[F] Module.Dual F V := (LinearMap.lcomp F F V.subtype) ∘ₗ B.flip with hT
  have hTapp : ∀ (y : U) (x : V), T y x = B x y := fun y x => rfl
  have hker : LinearMap.ker T = B.orthogonal V := by
    ext y
    simp only [LinearMap.mem_ker, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h n hn
      have := hTapp y ⟨n, hn⟩
      rw [h] at this
      exact this.symm
    · intro h
      ext x
      rw [hTapp]
      exact h x x.2
  have hsurj : V ⊓ B.orthogonal ⊤ = ⊥ ↔ ∀ f : Module.Dual F V, ∃ y : U, ∀ x : V, f x = B x y := by
    constructor
    · intro h f
      have h1 := LinearMap.BilinForm.finrank_add_finrank_orthogonal hB.isRefl V
      rw [h] at h1
      simp only [finrank_bot, add_zero] at h1
      have h2 := LinearMap.finrank_range_add_finrank_ker T
      rw [hker] at h2
      have h3 : finrank F (LinearMap.range T) = finrank F (Module.Dual F V) := by
        rw [Subspace.dual_finrank_eq]; omega
      have h4 : LinearMap.range T = ⊤ := Submodule.eq_top_of_finrank_eq h3
      have : f ∈ LinearMap.range T := by rw [h4]; trivial
      obtain ⟨y, hy⟩ := this
      exact ⟨y, fun x => by rw [← hy, hTapp]⟩
    · intro h
      rw [eq_bot_iff]
      intro v hv
      obtain ⟨hvV, hvr⟩ := hv
      rw [Submodule.mem_bot]
      have : ∀ φ : Module.Dual F V, φ ⟨v, hvV⟩ = 0 := by
        intro φ
        obtain ⟨y, hy⟩ := h φ
        rw [hy]
        show B v y = 0
        rw [hB.eq]
        exact hvr y trivial
      have := (Module.forall_dual_apply_eq_zero_iff F (⟨v, hvV⟩ : V)).mp this
      simpa using congrArg Subtype.val this
  refine ⟨hsurj, fun h => ?_⟩
  have h1 := LinearMap.BilinForm.finrank_add_finrank_orthogonal hB.isRefl V
  rw [h] at h1
  simp only [finrank_bot, add_zero] at h1
  omega

/-- **Kitaoka 1993, Corollary 1.1.1** (p. 3). In the setting of Proposition 1.1.2, $V \cap U^\perp = \{0\}$ if and
only if $V$ is contained in a regular subspace $W$ of $U$ (the restriction of $b$ to $W$ is nondegenerate).
Unconditional. -/
@[kb "kitaoka1993" "§1.1, Cor. 1.1.1, p. 3"]
theorem corollary111 (B : LinearMap.BilinForm F U) (hB : B.IsSymm) (V : Submodule F U) :
    V ⊓ B.orthogonal ⊤ = ⊥ ↔ ∃ W : Submodule F U, V ≤ W ∧ (B.restrict W).Nondegenerate := by
  classical
  constructor
  · intro h
    obtain ⟨C, hC⟩ := Submodule.exists_isCompl (V ⊔ B.orthogonal ⊤)
    have hcod : (V ⊔ C) ⊔ B.orthogonal ⊤ = ⊤ := by
      have := hC.sup_eq_top
      rw [sup_right_comm]; exact this
    have hinf : (V ⊔ C) ⊓ B.orthogonal ⊤ = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxW, hxr⟩ := hx
      obtain ⟨v, hv, c, hc, rfl⟩ := Submodule.mem_sup.mp hxW
      have hcmem : c ∈ V ⊔ B.orthogonal ⊤ := by
        have : c = (v + c) - v := by abel
        rw [this]
        exact Submodule.sub_mem _ (Submodule.mem_sup_right hxr) (Submodule.mem_sup_left hv)
      have hc0 : c = 0 := by
        have := hC.disjoint.le_bot ⟨hcmem, hc⟩
        simpa using this
      subst hc0
      have : v ∈ V ⊓ B.orthogonal ⊤ := ⟨hv, by simpa using hxr⟩
      rw [h] at this
      simpa using this
    refine ⟨V ⊔ C, le_sup_left, ?_⟩
    have hrefl : (B.restrict (V ⊔ C)).IsRefl := fun x y hxy => hB.isRefl x y hxy
    refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft hrefl).mpr ?_
    intro x hx
    have hxr : (x : U) ∈ B.orthogonal ⊤ := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro u _
      have : u ∈ (V ⊔ C) ⊔ B.orthogonal ⊤ := by rw [hcod]; trivial
      obtain ⟨w, hw, r, hr, rfl⟩ := Submodule.mem_sup.mp this
      have h2 : B w x = 0 := by
        rw [hB.eq]; exact hx ⟨w, hw⟩
      show B (w + r) x = 0
      rw [map_add, LinearMap.add_apply]
      have h3 : B r x = 0 := by rw [hB.eq]; exact hr x trivial
      rw [h2, h3, add_zero]
    have : (x : U) ∈ (V ⊔ C) ⊓ B.orthogonal ⊤ := ⟨x.2, hxr⟩
    rw [hinf] at this
    exact Subtype.ext (by simpa using this)
  · rintro ⟨W, hVW, hW⟩
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hvV, hvr⟩ := hv
    have hvW := hVW hvV
    have := hW.1 ⟨v, hvW⟩ (by
      intro y
      show B v y = 0
      rw [hB.eq]; exact hvr y trivial)
    rw [Submodule.mem_bot]
    simpa using congrArg Subtype.val this

/-- The linear map $(a_i, b_i)_i \mapsto \sum_i (a_i x_i + b_i y_i)$ from $(F \times F)^n$ to $U$. -/
def pairMap {n : ℕ} (x y : Fin n → U) : (Fin n → F × F) →ₗ[F] U where
  toFun v := ∑ i, ((v i).1 • x i + (v i).2 • y i)
  map_add' v w := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add, add_smul]
    abel
  map_smul' c v := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [smul_add, smul_smul]

omit [FiniteDimensional F U] in
theorem polar_sum_left' (Q : QuadraticForm F U) {ι : Type*} (s : Finset ι) (g : ι → U) (z : U) :
    polar Q (∑ i ∈ s, g i) z = ∑ i ∈ s, polar Q (g i) z := by
  simp only [← polarBilin_apply_apply, map_sum, LinearMap.sum_apply]

omit [FiniteDimensional F U] in
theorem polar_sum_right' (Q : QuadraticForm F U) {ι : Type*} (s : Finset ι) (g : ι → U) (z : U) :
    polar Q z (∑ i ∈ s, g i) = ∑ i ∈ s, polar Q z (g i) := by
  simp only [← polarBilin_apply_apply, map_sum]

section pairs

variable {n : ℕ} (Q : QuadraticForm F U) (x y : Fin n → U)

/-- Hyperbolic pair relations for the families `x`, `y`. -/
structure IsHypPairs : Prop where
  qx : ∀ i, Q (x i) = 0
  qy : ∀ i, Q (y i) = 0
  pxx : ∀ i j, polar Q (x i) (x j) = 0
  pyy : ∀ i j, i ≠ j → polar Q (y i) (y j) = 0
  pxy : ∀ i j, polar Q (x i) (y j) = if i = j then 1 else 0

variable {Q x y}

omit [FiniteDimensional F U] in
theorem IsHypPairs.polar_fiber (h : IsHypPairs Q x y) (v : Fin n → F × F) (i j : Fin n) (hij : i ≠ j) :
    polar Q ((v i).1 • x i + (v i).2 • y i) ((v j).1 • x j + (v j).2 • y j) = 0 := by
  simp only [polar_add_left, polar_add_right, polar_smul_left, polar_smul_right, h.pxx, h.pyy i j hij,
    h.pxy i j, h.pxy j i, polar_comm Q (y i) (x j)]
  simp [hij, hij.symm]

omit [FiniteDimensional F U] in
theorem IsHypPairs.Q_pairMap (h : IsHypPairs Q x y) (v : Fin n → F × F) :
    Q (pairMap x y v) = QuadraticForm.hyperbolicSpace F n v := by
  classical
  have : pairMap x y v = ∑ i, ((v i).1 • x i + (v i).2 • y i) := rfl
  rw [this, QuadraticMap.map_sum, QuadraticForm.hyperbolicSpace_apply]
  rw [add_eq_left.mpr]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_add_eq, QuadraticMap.map_smul, QuadraticMap.map_smul, h.qx, h.qy, polar_smul_left,
      polar_smul_right, h.pxy i i]
    simp [smul_eq_mul]
  · refine Finset.sum_eq_zero fun ij hij => ?_
    induction ij using Sym2.ind with
    | h i j =>
      simp only [Finset.mem_filter, Sym2.mk_isDiag_iff] at hij
      simp only [Sym2.map_mk, polarSym2_sym2Mk]
      exact h.polar_fiber v i j hij.2

omit [FiniteDimensional F U] in
theorem IsHypPairs.pairMap_injective (h : IsHypPairs Q x y) : Function.Injective (pairMap (F := F) x y) := by
  classical
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro v hv
  rw [LinearMap.mem_ker] at hv
  have hsum : pairMap x y v = ∑ i, ((v i).1 • x i + (v i).2 • y i) := rfl
  rw [Submodule.mem_bot]
  funext j
  have hx : polar Q (pairMap x y v) (x j) = (v j).2 := by
    rw [hsum, polar_sum_left']
    simp only [polar_add_left, polar_smul_left, h.pxx, polar_comm Q (y _) (x j), h.pxy j]
    simp [Finset.sum_ite_eq]
  have hy : polar Q (pairMap x y v) (y j) = (v j).1 := by
    rw [hsum, polar_sum_left']
    have : ∀ i, polar Q (y i) (y j) = 0 := fun i => by
      by_cases hij : i = j
      · subst hij; rw [polar_self_eq, h.qy, mul_zero]
      · exact h.pyy i j hij
    simp only [polar_add_left, polar_smul_left, this, h.pxy]
    simp [Finset.sum_ite_eq]
  rw [hv, polar_zero_left] at hx hy
  exact Prod.ext hy.symm hx.symm

end pairs

/-- Existence of a hyperbolic-pair basis: given a totally isotropic `V` meeting the radical trivially, there
are `x` spanning `V` and `y` with the hyperbolic pair relations. -/
theorem exists_hypPairs (Q : QuadraticForm F U) (V : Submodule F U)
    (hV : V ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) ⊤ = ⊥) (hiso : ∀ v ∈ V, Q v = 0) :
    ∃ x y : Fin (finrank F V) → U, (∀ i, x i ∈ V) ∧ (∀ v ∈ V, ∃ a : Fin (finrank F V) → F, v = ∑ i, a i • x i) ∧
      IsHypPairs Q x y := by
  classical
  have hsymm : LinearMap.BilinForm.IsSymm (polarBilin Q) := ⟨fun u w => polar_comm Q u w⟩
  have hrep := ((proposition112 (polarBilin Q) hsymm V).1.mp hV)
  choose z hz using fun j : Fin (finrank F V) => hrep ((Module.finBasis F V).coord j)
  set b := Module.finBasis F V with hb
  have hxz : ∀ i j, polar Q (b i : U) (z j) = if i = j then 1 else 0 := by
    intro i j
    have := hz j (b i)
    simpa [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply] using this.symm
  have hVV : ∀ u ∈ V, ∀ w ∈ V, polar Q u w = 0 := by
    intro u hu w hw
    rw [polar, hiso (u + w) (V.add_mem hu hw), hiso u hu, hiso w hw]; simp
  let c : Fin (finrank F V) → Fin (finrank F V) → F := fun j k =>
    if k < j then -polar Q (z j) (z k) else if k = j then -Q (z j) else 0
  let v : Fin (finrank F V) → U := fun j => ∑ k, c j k • (b k : U)
  have hvV : ∀ j, v j ∈ V := fun j =>
    V.sum_mem fun k _ => V.smul_mem _ (b k).2
  have hzv : ∀ i j, polar Q (z i) (v j) = c j i := by
    intro i j
    have hvj : v j = ∑ k, c j k • (b k : U) := rfl
    rw [hvj, polar_sum_right']
    simp only [polar_comm Q (z i) _]
    simp [hxz]
  have hvz : ∀ i j, polar Q (v i) (z j) = c i j := fun i j => by rw [polar_comm, hzv]
  have hxv : ∀ i j, polar Q (b i : U) (v j) = 0 := fun i j => hVV _ (b i).2 _ (hvV j)
  refine ⟨fun i => b i, fun j => z j + v j, fun i => (b i).2, ?_, ?_⟩
  · intro u hu
    refine ⟨fun i => b.repr ⟨u, hu⟩ i, ?_⟩
    have h2 := congrArg (fun w : V => (w : U)) (b.sum_repr ⟨u, hu⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    exact h2.symm
  · refine ⟨fun i => hiso _ (b i).2, fun j => ?_, fun i j => hVV _ (b i).2 _ (b j).2, fun i j hij => ?_,
      fun i j => ?_⟩
    · rw [map_add_eq, hiso _ (hvV j), hzv]
      simp [c]
    · simp only [polar_add_left, polar_add_right, hzv, hvz, hVV _ (hvV i) _ (hvV j)]
      rcases lt_or_gt_of_ne hij with h | h
      · simp [c, h, h.ne', not_lt.mpr h.le, polar_comm Q (z j) (z i)]
      · simp [c, h, h.ne', not_lt.mpr h.le, polar_comm Q (z j) (z i)]
    · rw [polar_add_right, hxz, hxv, add_zero]

/-- **Kitaoka 1993, Proposition 1.2.2** (p. 11). Let $(U, q)$ be a finite-dimensional quadratic space over a field
$F$ and $V$ a totally isotropic subspace ($q(v) = 0$ for $v \in V$) with $V \cap U^\perp = \{0\}$ ($U^\perp$ the
radical of $b(x, y) = q(x+y) - q(x) - q(y)$). Then there is a totally isotropic subspace $W$ of $U$ with
$\dim W = \dim V$, $V \cap W = \{0\}$, and $V \oplus W$ with the restriction of $q$ isometric to the hyperbolic space
$H^{\dim V}$. Unconditional, every characteristic. -/
@[kb "kitaoka1993" "§1.2, Prop. 1.2.2, p. 11"]
theorem proposition122 (Q : QuadraticForm F U) (V : Submodule F U)
    (hV : V ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) ⊤ = ⊥) (hiso : ∀ v ∈ V, Q v = 0) :
    ∃ W : Submodule F U, (∀ w ∈ W, Q w = 0) ∧ finrank F W = finrank F V ∧ Disjoint V W ∧
      (Q.comp (V ⊔ W).subtype).Equivalent (QuadraticForm.hyperbolicSpace F (finrank F V)) := by
  classical
  obtain ⟨x, y, hxV, hspan, hyp⟩ := exists_hypPairs Q V hV hiso
  set Φ : (Fin (finrank F V) → F × F) →ₗ[F] U := pairMap x y with hΦdef
  have hinj : Function.Injective Φ := hyp.pairMap_injective
  let ι₁ : (Fin (finrank F V) → F) →ₗ[F] (Fin (finrank F V) → F × F) :=
    LinearMap.pi fun i => (LinearMap.inl F F F) ∘ₗ LinearMap.proj i
  let ι₂ : (Fin (finrank F V) → F) →ₗ[F] (Fin (finrank F V) → F × F) :=
    LinearMap.pi fun i => (LinearMap.inr F F F) ∘ₗ LinearMap.proj i
  have hι₁ : ∀ a i, ι₁ a i = (a i, 0) := fun a i => rfl
  have hι₂ : ∀ b i, ι₂ b i = (0, b i) := fun b i => rfl
  have hΦ₁ : ∀ a, Φ (ι₁ a) = ∑ i, a i • x i := by
    intro a
    show ∑ i, ((ι₁ a i).1 • x i + (ι₁ a i).2 • y i) = _
    simp [hι₁]
  have hΦ₂ : ∀ b, Φ (ι₂ b) = ∑ i, b i • y i := by
    intro b
    show ∑ i, ((ι₂ b i).1 • x i + (ι₂ b i).2 • y i) = _
    simp [hι₂]
  have hι₁inj : Function.Injective ι₁ := fun a a' h => by
    funext i
    have := congrFun h i
    simpa [hι₁] using this
  have hι₂inj : Function.Injective ι₂ := fun a a' h => by
    funext i
    have := congrFun h i
    simpa [hι₂] using this
  set W : Submodule F U := LinearMap.range (Φ ∘ₗ ι₂) with hW
  have hVeq : V = LinearMap.range (Φ ∘ₗ ι₁) := by
    ext u
    constructor
    · intro hu
      obtain ⟨a, ha⟩ := hspan u hu
      exact ⟨a, by simp [hΦ₁, ← ha]⟩
    · rintro ⟨a, rfl⟩
      simp only [LinearMap.comp_apply, hΦ₁]
      exact V.sum_mem fun i _ => V.smul_mem _ (hxV i)
  have hsup : V ⊔ W = LinearMap.range Φ := by
    apply le_antisymm
    · apply sup_le
      · exact hVeq.le.trans (LinearMap.range_comp_le_range _ _)
      · exact LinearMap.range_comp_le_range _ _
    · rintro u ⟨v, rfl⟩
      have hv : v = ι₁ (fun i => (v i).1) + ι₂ (fun i => (v i).2) := by
        funext i; simp [hι₁, hι₂]
      rw [hv, map_add]
      exact Submodule.add_mem_sup (hVeq.ge ⟨_, rfl⟩) ⟨_, rfl⟩
  refine ⟨W, ?_, ?_, ?_, ?_⟩
  · rintro w ⟨b, rfl⟩
    show Q (Φ (ι₂ b)) = 0
    rw [hΦdef, hyp.Q_pairMap, QuadraticForm.hyperbolicSpace_apply]
    simp [hι₂]
  · rw [hW, LinearMap.finrank_range_of_inj
      (show Function.Injective (Φ ∘ₗ ι₂) from fun a b h => hι₂inj (hinj h))]
    simp
  · rw [Submodule.disjoint_def]
    intro u hu ⟨b, hb⟩
    obtain ⟨a, rfl⟩ := hVeq.le hu
    have h1 : ι₁ a = ι₂ b := hinj hb.symm
    have h2 : a = 0 := by
      funext i
      have := congrFun h1 i
      simp only [hι₁, hι₂, Prod.mk.injEq] at this
      exact this.1
    subst h2
    simp
  · let e : (Fin (finrank F V) → F × F) ≃ₗ[F] ↥(V ⊔ W) :=
      (LinearEquiv.ofInjective Φ hinj).trans (LinearEquiv.ofEq _ _ hsup.symm)
    have hmap : ∀ v, (Q.comp (V ⊔ W).subtype) (e v) =
        QuadraticForm.hyperbolicSpace F (finrank F V) v := by
      intro v
      show Q (Φ v) = _
      rw [hΦdef, hyp.Q_pairMap]
    let iso : (QuadraticForm.hyperbolicSpace F (finrank F V)).IsometryEquiv
        (Q.comp (V ⊔ W).subtype) := { e with map_app' := hmap }
    exact ⟨iso.symm⟩

/-- **Kitaoka 1993, Proposition 1.2.2, last sentence** (p. 11): a regular isotropic quadratic space of dimension $2$
over a field $F$ is a hyperbolic plane. Unconditional, every characteristic. -/
@[kb "kitaoka1993" "§1.2, Prop. 1.2.2, p. 11 (regular isotropic plane)"]
theorem proposition122_plane (Q : QuadraticForm F U) (hdim : finrank F U = 2)
    (hreg : (polarBilin Q).Nondegenerate) (hiso : ∃ v : U, v ≠ 0 ∧ Q v = 0) :
    Q.Equivalent (QuadraticForm.hyperbolicPlane F) := by
  classical
  obtain ⟨v, hv0, hv⟩ := hiso
  have hvR : ∃ w, polar Q v w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv0 (hreg.1 v (fun y => hcon y))
  obtain ⟨w, hw⟩ := hvR
  have hu : polar Q ((polar Q v w)⁻¹ • w) v = 1 := by
    rw [polar_smul_left, smul_eq_mul, polar_comm Q w v, inv_mul_cancel₀ hw]
  obtain ⟨hv', hvv'⟩ := QuadraticForm.Witt.hyperbolic_partner Q hv hu
  set v' := (polar Q v w)⁻¹ • w - Q ((polar Q v w)⁻¹ • w) • v
  have hvv : polar Q v v = 0 := by rw [polar_self_eq, hv, mul_zero]
  have hv'v' : polar Q v' v' = 0 := by rw [polar_self_eq, hv', mul_zero]
  have hv'v : polar Q v' v = 1 := by rw [polar_comm, hvv']
  let Φ : (F × F) →ₗ[F] U :=
    (LinearMap.fst F F F).smulRight v + (LinearMap.snd F F F).smulRight v'
  have hΦ : ∀ x : F × F, Φ x = x.1 • v + x.2 • v' := fun x => rfl
  have hQ : ∀ x : F × F, Q (Φ x) = x.1 * x.2 := by
    rintro ⟨a, b⟩
    rw [hΦ]
    simp only
    rw [map_add_eq, QuadraticMap.map_smul, QuadraticMap.map_smul, hv, hv', polar_smul_left,
      polar_smul_right, hvv']
    simp [smul_eq_mul]
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨a, b⟩ hx
    rw [LinearMap.mem_ker] at hx
    have hb : b = 0 := by
      have := congrArg (fun z => polar Q z v) ((hΦ (a, b)).symm.trans hx)
      simp only [polar_zero_left, polar_add_left, polar_smul_left, hvv, hv'v] at this
      simpa using this
    have ha : a = 0 := by
      have := congrArg (fun z => polar Q z v') ((hΦ (a, b)).symm.trans hx)
      simp only [polar_zero_left, polar_add_left, polar_smul_left, hv'v', hvv'] at this
      simpa using this
    rw [Submodule.mem_bot]
    ext <;> simp [ha, hb]
  have hdim : finrank F (F × F) = finrank F U := by
    rw [hdim]; simp
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  exact ⟨({ LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩ with
    map_app' := fun x => hQ x } :
      (QuadraticForm.hyperbolicPlane F).IsometryEquiv Q).symm⟩

end QuadFormsKB.Kitaoka.Radical
