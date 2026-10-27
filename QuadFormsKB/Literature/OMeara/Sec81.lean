/-
# O'Meara §81A–§81B: lattices and coefficients over a Dedekind domain

**Setting.** $R$ is a Dedekind domain with fraction field $F$ (O'Meara's $\mathfrak o = \mathfrak o(S)$ defined by a
Dedekind set of spots $S$ on $F$, Chapter VIII, p. 208), and $V$ is a vector space over $F$. A *lattice in $V$* is a
finitely generated $R$-submodule of $V$ (`Submodule.FG`; this is equivalent to O'Meara's definition by 81:6, proved
here as `fg_iff_le_span_basis`), and a lattice *on $V$* is one that moreover spans $V$ (Mathlib's
`Submodule.IsLattice F L`). A *fractional ideal* of $F$ is a non-zero finitely generated $R$-submodule of $F$
(O'Meara's group $J = I(S)$); here it is a `Submodule R F` $\mathfrak a$ with `a.FG` and `a ≠ ⊥`, and its inverse
$\mathfrak a^{-1}$ is `1 / a` (`mul_one_div_cancel_of_fg`). For such an $\mathfrak a$ and an $R$-submodule $M$ of $V$,
O'Meara's $\mathfrak aM$ is Mathlib's `a • M`, and $\mathfrak ax$ is `a • span R {x}`.

No quadratic form is used in this file (O'Meara: "the general assumption that the characteristic of the underlying
field $F$ is not $2$ will not be used in the first paragraph of this chapter", p. 208).

**Index convention.** O'Meara's bases $x_1, \dots, x_n$ are `x 0, …, x (n-1)` here.

**Proves** (O'Meara 1963, §81A–§81B, pp. 208–213):
* `fg_iff_exists_smul_le` (**81:1**), `fg_iff_le_span_basis` (**81:6**, with O'Meara's definition of a lattice),
  `le_span_basis_iff_of_le` (**81:1a**);
* the coefficient $\mathfrak a_x$ of a vector (`coeff`, §81B, p. 210) and its properties (`coeff_fg`, `coeff_ne_bot`,
  `coeff_smul`, `coeff_smul_span`, `one_le_coeff_iff`, `isMaxVec_iff_coeff_eq_one`,
  `exists_isMaxVec_of_principal`);
* `mem_iSup_smul_span_iff` and `coeff_sum_basis` (**81:4**).
-/
import QuadFormsKB.Literature.OMeara.Sec91

open Submodule Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Coeff

variable {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]

/-- **The coefficient** $\mathfrak a_x = \{\alpha \in F : \alpha x \in L\}$ of a vector $x$ in an $R$-submodule $L$
of $V$ (O'Meara 1963, §81B, p. 210). O'Meara defines it for non-zero $x \in FL$, where it is a fractional ideal
(`coeff_fg`, `coeff_ne_bot`). -/
@[kb "omeara1963" "§81B, p. 210 (the coefficient a_x of x in L)"]
def coeff (F : Type*) [Field F] [Algebra R F] [Module F V] [IsScalarTower R F V] (L : Submodule R V) (x : V) : Submodule R F :=
  L.comap ((LinearMap.toSpanSingleton F V x).restrictScalars R)

theorem mem_coeff {L : Submodule R V} {x : V} {α : F} : α ∈ coeff F L x ↔ α • x ∈ L := Iff.rfl

/-- **$\mathfrak a_x \supseteq \mathfrak o$ if and only if $x \in L$** (O'Meara 1963, §81B, p. 210). -/
@[kb "omeara1963" "§81B, p. 210 (a_x ⊇ o iff x ∈ L)"]
theorem one_le_coeff_iff {L : Submodule R V} {x : V} : 1 ≤ coeff F L x ↔ x ∈ L := by
  constructor
  · intro h
    have := h (Submodule.mem_one.mpr ⟨1, map_one _⟩)
    simpa [mem_coeff] using this
  · intro h α hα
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hα
    rw [mem_coeff, algebraMap_smul]
    exact L.smul_mem r h

/-- **$\mathfrak a_x x = L \cap Fx$** (O'Meara 1963, §81B, p. 210). -/
@[kb "omeara1963" "§81B, p. 210 (a_x x = L ∩ Fx)"]
theorem coeff_smul_span (L : Submodule R V) (x : V) :
    coeff F L x • span R {x} = L ⊓ (span F {x}).restrictScalars R := by
  apply le_antisymm
  · rw [Submodule.smul_le]
    intro α hα n hn
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hn
    refine ⟨?_, ?_⟩
    · rw [smul_comm]; exact L.smul_mem r hα
    · rw [smul_comm]
      exact Submodule.smul_mem _ r (Submodule.smul_mem _ α (Submodule.mem_span_singleton_self x))
  · rintro v ⟨hvL, hv⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (by simpa using hv)
    exact Submodule.smul_mem_smul (show c ∈ coeff F L x from hvL) (Submodule.mem_span_singleton_self x)

/-- **$\mathfrak a_{\alpha x} = \alpha^{-1}\mathfrak a_x$** for $\alpha \in F^\times$ (O'Meara 1963, §81B, p. 210). -/
@[kb "omeara1963" "§81B, p. 210 (a_{αx} = α⁻¹ a_x)"]
theorem coeff_smul (L : Submodule R V) (x : V) {α : F} (hα : α ≠ 0) :
    coeff F L (α • x) = span R {α⁻¹} * coeff F L x := by
  ext β
  rw [Submodule.mem_span_singleton_mul, mem_coeff]
  constructor
  · intro h
    refine ⟨α * β, ?_, ?_⟩
    · rw [mem_coeff, mul_smul, smul_comm]; exact h
    · field_simp
  · rintro ⟨z, hz, rfl⟩
    rw [mem_coeff] at hz
    rw [smul_smul, show α⁻¹ * z * α = z by field_simp]
    exact hz

/-- **A maximal vector** of $L$ (O'Meara 1963, §81B, p. 210: $\mathfrak a_x = \mathfrak o$) is a vector $x$ of $L$
with $\alpha x \in L \Rightarrow \alpha \in \mathfrak o$ (`IsMaxVec`): the two definitions agree. -/
@[kb "omeara1963" "§81B, p. 210 (maximal vector: a_x = o)"]
theorem isMaxVec_iff_coeff_eq_one {L : Submodule R V} {x : V} : IsMaxVec F L x ↔ coeff F L x = 1 := by
  constructor
  · rintro ⟨hx, h⟩
    apply le_antisymm
    · intro c hc
      obtain ⟨r, hr⟩ := h c hc
      exact Submodule.mem_one.mpr ⟨r, hr⟩
    · exact one_le_coeff_iff.mpr hx
  · intro h
    refine ⟨one_le_coeff_iff.mp h.ge, fun c hc => ?_⟩
    have : c ∈ (1 : Submodule R F) := h ▸ hc
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp this
    exact ⟨r, hr⟩

end Coeff

section Dedekind

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]

/-- **Fractional ideals are invertible** (O'Meara 1963, §22, p. 47): $\mathfrak a\mathfrak a^{-1} = \mathfrak o$
for a non-zero finitely generated $R$-submodule $\mathfrak a$ of $F$, with $\mathfrak a^{-1} = \mathfrak o / \mathfrak a
= \{\alpha \in F : \alpha\mathfrak a \subseteq \mathfrak o\}$ (from Mathlib's `FractionalIdeal`). -/
theorem mul_one_div_cancel_of_fg {a : Submodule R F} (ha : a.FG) (h : a ≠ ⊥) : a * (1 / a) = 1 := by
  let I : FractionalIdeal (nonZeroDivisors R) F := ⟨a, FractionalIdeal.isFractional_of_fg ha⟩
  have hI : I ≠ 0 := by
    intro h0; apply h
    have := congrArg (fun J : FractionalIdeal (nonZeroDivisors R) F => (J : Submodule R F)) h0
    simpa [I] using this
  have := mul_inv_cancel₀ hI
  rw [FractionalIdeal.inv_eq] at this
  have h2 := congrArg (fun J : FractionalIdeal (nonZeroDivisors R) F => (J : Submodule R F)) this
  simp only [FractionalIdeal.coe_mul, FractionalIdeal.coe_div hI, FractionalIdeal.coe_one] at h2
  simpa [I, FractionalIdeal.coe_one_eq_coeSubmodule_top] using h2

/-- The inverse $\mathfrak a^{-1}$ of a fractional ideal is a fractional ideal. -/
theorem one_div_fg {a : Submodule R F} (ha : a.FG) (h : a ≠ ⊥) : (1 / a).FG ∧ 1 / a ≠ ⊥ := by
  have h1 := mul_one_div_cancel_of_fg ha h
  refine ⟨?_, ?_⟩
  · let I : FractionalIdeal (nonZeroDivisors R) F := ⟨a, FractionalIdeal.isFractional_of_fg ha⟩
    have hI : I ≠ 0 := by
      intro h0; apply h
      have := congrArg (fun J : FractionalIdeal (nonZeroDivisors R) F => (J : Submodule R F)) h0
      simpa [I] using this
    have e : (1 / a : Submodule R F) = ((I⁻¹ : FractionalIdeal (nonZeroDivisors R) F) : Submodule R F) := by
      rw [FractionalIdeal.inv_eq, FractionalIdeal.coe_div hI]
      simp [I]
    rw [e]
    have := FractionalIdeal.isNoetherian (I⁻¹)
    exact Module.Finite.iff_fg.mp inferInstance
  · intro h0
    rw [h0, Submodule.mul_bot] at h1
    have : (1 : F) ∈ (1 : Submodule R F) := Submodule.mem_one.mpr ⟨1, map_one _⟩
    rw [← h1] at this
    simp at this

/-- **Proposition 81:1** (O'Meara 1963, p. 209). Let $L$ be a lattice on $V$. An $R$-submodule $M$ of $V$ is a
lattice in $V$ if and only if $\alpha M \subseteq L$ for some non-zero $\alpha \in \mathfrak o$. (Lattices in $V$ are
the finitely generated submodules, 81:6.) -/
@[kb "omeara1963" "§81A, 81:1, p. 209"]
theorem fg_iff_exists_smul_le {L : Submodule R V} (hL : L.IsLattice F) (M : Submodule R V) :
    M.FG ↔ ∃ α : R, α ≠ 0 ∧ ∀ x ∈ M, α • x ∈ L := by
  have htf := isTorsionFree_of_fractionRing (R := R) (F := F) (V := V)
  classical
  constructor
  · rintro ⟨S, rfl⟩
    have hd : ∀ s : V, ∃ d : R, d ≠ 0 ∧ d • s ∈ L := fun s =>
      exists_smul_mem_of_mem_span (by rw [hL.span_eq_top]; trivial)
    choose d hd0 hdL using hd
    refine ⟨∏ s ∈ S, d s, Finset.prod_ne_zero_iff.mpr fun s _ => hd0 s, fun x hx => ?_⟩
    induction hx using Submodule.span_induction with
    | mem s hs =>
      rw [← Finset.mul_prod_erase S d hs, mul_comm, mul_smul]
      exact L.smul_mem _ (hdL s)
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact L.add_mem hx hy
    | smul r x _ hx => rw [smul_comm]; exact L.smul_mem r hx
  · rintro ⟨α, hα, h⟩
    have : Module.Finite R L := Module.Finite.iff_fg.mpr hL.fg
    have : IsNoetherian R L := isNoetherian_of_isNoetherianRing_of_finite R L
    let g : M →ₗ[R] L := LinearMap.codRestrict L
      ((LinearMap.lsmul R V α) ∘ₗ M.subtype) (fun x => h x x.2)
    have hg : Function.Injective g := by
      intro x y hxy
      have := congrArg Subtype.val hxy
      exact Subtype.ext (smul_right_injective V hα this)
    have := Module.Finite.of_injective g hg
    exact Module.Finite.iff_fg.mp this

/-- A submodule of a finitely generated submodule over a Noetherian ring is finitely generated. -/
private theorem fg_of_le_fg_aux {N M : Submodule R V} (hM : M.FG) (h : N ≤ M) : N.FG := by
  have : Module.Finite R M := Module.Finite.iff_fg.mpr hM
  have : IsNoetherian R M := isNoetherian_of_isNoetherianRing_of_finite R M
  exact Module.Finite.iff_fg.mp (Module.Finite.of_injective (Submodule.inclusion h)
    (Submodule.inclusion_injective h))

/-- A finitely generated submodule of $V$ lies in the $R$-span of some basis of $V$. -/
private theorem exists_basis_of_fg_aux {W : Type*} [AddCommGroup W] [Module F W] [Module R W]
    [IsScalarTower R F W] [FiniteDimensional F W] {M : Submodule R W} (hM : M.FG) :
    ∃ b : Basis (Fin (finrank F W)) F W, M ≤ span R (Set.range b) := by
  classical
  obtain ⟨S, rfl⟩ := hM
  let b₀ := Module.finBasis F W
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R) (S ×ˢ (Finset.univ : Finset (Fin (finrank F W))))
    (fun p => b₀.repr p.1 p.2)
  have hd0 : algebraMap R F d ≠ 0 := by
    intro h0
    exact nonZeroDivisors.ne_zero d.2 ((IsFractionRing.injective R F) (by simp at h0))
  let b := b₀.isUnitSMul (w := fun _ => (algebraMap R F d)⁻¹) (fun _ => isUnit_iff_ne_zero.mpr (inv_ne_zero hd0))
  refine ⟨b, ?_⟩
  rw [Submodule.span_le]
  intro s hs
  have hsum := b₀.sum_repr s
  have hr' : ∀ i, ∃ r : R, algebraMap R F r = algebraMap R F d * b₀.repr s i := by
    intro i
    obtain ⟨r, h⟩ := hd (s, i) (Finset.mem_product.mpr ⟨hs, Finset.mem_univ _⟩)
    exact ⟨r, by rw [h]; exact Algebra.smul_def _ _⟩
  choose r hr using hr'
  have : s = ∑ i, r i • b i := by
    conv_lhs => rw [← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul F (r i), hr]
    simp only [b, Basis.isUnitSMul_apply, smul_smul]
    congr 1
    field_simp
  rw [this]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- **Example 81:6** (O'Meara 1963, p. 212), with O'Meara's definition of a lattice (§81A, p. 209): an
$R$-submodule $M$ of the finite-dimensional space $V$ is a lattice in $V$, i.e. $M \subseteq \mathfrak ox_1 + \cdots +
\mathfrak ox_n$ for some base $x_1, \dots, x_n$ of $V$, if and only if it is finitely generated. -/
@[kb "omeara1963" "§81B, 81:6, p. 212; §81A, p. 209 (lattice in V)"]
theorem fg_iff_le_span_basis [FiniteDimensional F V] (M : Submodule R V) :
    M.FG ↔ ∃ b : Basis (Fin (finrank F V)) F V, M ≤ span R (Set.range b) := by
  constructor
  · exact exists_basis_of_fg_aux (F := F)
  · rintro ⟨b, hb⟩
    exact fg_of_le_fg_aux (Submodule.fg_span (Set.finite_range b)) hb

/-- **Corollary 81:1a** (O'Meara 1963, pp. 209–210). Let $U$ be a subspace of $V$ with $M \subseteq U \subseteq V$.
Then $M$ is a lattice in $V$ if and only if it is a lattice in $U$ (O'Meara's definition: $M$ lies in the
$\mathfrak o$-span of a base of $V$, respectively of $U$). -/
@[kb "omeara1963" "§81A, 81:1a, pp. 209–210"]
theorem le_span_basis_iff_of_le [FiniteDimensional F V] {M : Submodule R V} {U : Submodule F V}
    (hMU : ∀ x ∈ M, x ∈ U) :
    (∃ b : Basis (Fin (finrank F U)) F U, M ≤ span R (Set.range fun i => (b i : V))) ↔
      ∃ b : Basis (Fin (finrank F V)) F V, M ≤ span R (Set.range b) := by
  have hV : (∃ b : Basis (Fin (finrank F V)) F V, M ≤ span R (Set.range b)) ↔ M.FG :=
    (fg_iff_le_span_basis M).symm
  rw [hV]
  constructor
  · rintro ⟨b, hb⟩
    exact fg_of_le_fg_aux (Submodule.fg_span (Set.finite_range _)) hb
  · intro hM
    let f : U →ₗ[R] V := (U.subtype).restrictScalars R
    have hf : Function.Injective f := Subtype.val_injective
    let M' : Submodule R U := M.comap f
    have hM' : M'.FG :=
      Submodule.fg_of_fg_map_injective f hf (fg_of_le_fg_aux hM (Submodule.map_comap_le f M))
    obtain ⟨b, hb⟩ := exists_basis_of_fg_aux (F := F) hM'
    refine ⟨b, fun x hx => ?_⟩
    have h1 : (⟨x, hMU x hx⟩ : U) ∈ M' := hx
    have h2 := Submodule.mem_map_of_mem (f := f) (hb h1)
    rw [Submodule.map_span, ← Set.range_comp] at h2
    exact h2

/-- **The coefficient of a vector of $FL$ is non-zero** (O'Meara 1963, §81B, p. 210: "it follows from the fact that
$L$ spans $FL$ that it is not zero"). -/
theorem coeff_ne_bot {L : Submodule R V} {x : V} (hx : x ∈ span F (L : Set V)) : coeff F L x ≠ ⊥ := by
  obtain ⟨d, hd0, hd⟩ := exists_smul_mem_of_mem_span (F := F) hx
  intro h
  have hmem : algebraMap R F d ∈ coeff F L x := by
    rw [mem_coeff, algebraMap_smul]; exact hd
  rw [h] at hmem
  have : algebraMap R F d = 0 := by simpa using hmem
  exact hd0 ((IsFractionRing.injective R F) (by simpa using this))

/-- **The coefficient is a fractional ideal** (O'Meara 1963, §81B, p. 210): for $x \ne 0$ in $FL$, $\mathfrak a_x$
is finitely generated (and non-zero by `coeff_ne_bot`). -/
@[kb "omeara1963" "§81B, p. 210 (a_x is a fractional ideal)"]
theorem coeff_fg {L : Submodule R V} (hL : L.FG) {x : V} (hx0 : x ≠ 0) : (coeff F L x).FG := by
  have htf := isTorsionFree_of_fractionRing (R := R) (F := F) (V := V)
  have : Module.Finite R L := Module.Finite.iff_fg.mpr hL
  have : IsNoetherian R L := isNoetherian_of_isNoetherianRing_of_finite R L
  let g : coeff F L x →ₗ[R] L := LinearMap.codRestrict L
    ((LinearMap.toSpanSingleton F V x).restrictScalars R ∘ₗ (coeff F L x).subtype) (fun α => α.2)
  have hg : Function.Injective g := by
    intro α β hαβ
    have := congrArg Subtype.val hαβ
    exact Subtype.ext (smul_left_injective F hx0 this)
  have := Module.Finite.of_injective g hg
  exact Module.Finite.iff_fg.mp this

/-- **Maximal vectors on every line when the class number is $1$** (O'Meara 1963, §81B, p. 210): if every
fractional ideal is principal, then every line $Fy$ of $FL$ contains a maximal vector of $L$. -/
@[kb "omeara1963" "§81B, p. 210 (maximal vectors when the class number is 1)"]
theorem exists_isMaxVec_of_principal (hP : ∀ a : Submodule R F, a.FG → ∃ α : F, a = span R {α})
    {L : Submodule R V} (hL : L.FG) {y : V} (hy : y ∈ span F (L : Set V)) (hy0 : y ≠ 0) :
    ∃ c : F, c ≠ 0 ∧ IsMaxVec F L (c • y) := by
  obtain ⟨α, hα⟩ := hP _ (coeff_fg hL hy0)
  have hne := coeff_ne_bot hy (L := L)
  have hα0 : α ≠ 0 := by
    rintro rfl
    apply hne
    rw [hα]; simp
  refine ⟨α, hα0, isMaxVec_iff_coeff_eq_one.mpr ?_⟩
  rw [coeff_smul L y hα0, hα, Submodule.span_mul_span, Set.singleton_mul_singleton, inv_mul_cancel₀ hα0,
    ← Submodule.one_eq_span]

end Dedekind

section Basis

variable {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]

/-- **Membership in $\mathfrak a_1x_1 + \cdots + \mathfrak a_nx_n$** for a base $x$ of $V$: a vector lies in it if
and only if its $i$-th coordinate lies in $\mathfrak a_i$ for every $i$ (the computation behind O'Meara's 81:4 and
81:7). -/
theorem mem_iSup_smul_span_iff {ι : Type*} (x : Basis ι F V) (a : ι → Submodule R F) (v : V) :
    v ∈ ⨆ i, a i • span R {x i} ↔ ∀ i, x.repr v i ∈ a i := by
  classical
  constructor
  · intro hv
    let N : Submodule R V :=
      { carrier := {v | ∀ i, x.repr v i ∈ a i}
        add_mem' := fun {u w} hu hw i => by
          rw [map_add, Finsupp.add_apply]; exact (a i).add_mem (hu i) (hw i)
        zero_mem' := fun i => by simp
        smul_mem' := fun r u hu i => by
          rw [← algebraMap_smul F r u, map_smul, Finsupp.smul_apply, smul_eq_mul, ← Algebra.smul_def]
          exact (a i).smul_mem r (hu i) }
    have : (⨆ i, a i • span R {x i}) ≤ N := by
      refine iSup_le fun i => ?_
      rw [Submodule.smul_le]
      intro α hα n hn
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hn
      intro j
      show x.repr (α • r • x i) j ∈ a j
      rw [← algebraMap_smul F r (x i), smul_smul, map_smul, Finsupp.smul_apply, Basis.repr_self,
        Finsupp.single_apply, smul_eq_mul]
      by_cases hij : i = j
      · subst hij
        simp only [↓reduceIte, mul_one]
        rw [mul_comm, ← Algebra.smul_def]
        exact (a i).smul_mem r hα
      · simp [hij]
    exact this hv
  · intro h
    have hv : v = (x.repr v).sum fun i c => c • x i := by
      have := Basis.linearCombination_repr x v
      rw [Finsupp.linearCombination_apply] at this
      exact this.symm
    rw [hv, Finsupp.sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact Submodule.mem_iSup_of_mem i (Submodule.smul_mem_smul (h i) (Submodule.mem_span_singleton_self _))

/-- **Example 81:4** (O'Meara 1963, p. 212). Let $x_1, \dots, x_n$ be a base for $V$ and
$L = \mathfrak a_1x_1 + \cdots + \mathfrak a_nx_n$. The coefficient in $L$ of $\alpha_1x_1 + \cdots + \alpha_nx_n$
is $\bigcap_i \mathfrak a_i\alpha_i^{-1}$, the intersection over the $i$ with $\alpha_i \ne 0$ (the OCR text shows
$(\mathfrak a_1\alpha_1^{-1}) \cap \cdots \cap (\mathfrak a_n\alpha_n^{-1})$; the restriction to $\alpha_i \ne 0$ is
implicit in the book). In particular the coefficient of $x_i$ is $\mathfrak a_i$ (`coeff_basis`). -/
@[kb "omeara1963" "§81B, 81:4, p. 212"]
theorem coeff_sum_basis {ι : Type*} [Fintype ι] (x : Basis ι F V) (a : ι → Submodule R F) (α : ι → F) :
    coeff F (⨆ i, a i • span R {x i}) (∑ i, α i • x i) = ⨅ i ∈ {i | α i ≠ 0}, span R {(α i)⁻¹} * a i := by
  classical
  have hrepr : ∀ (β : F) (i : ι), x.repr (β • ∑ j, α j • x j) i = β * α i := by
    intro β i
    simp [map_sum, Finsupp.single_apply]
  ext β
  rw [mem_coeff, mem_iSup_smul_span_iff, Submodule.mem_iInf]
  refine forall_congr' fun i => ?_
  rw [hrepr, Submodule.mem_iInf]
  by_cases hi : α i = 0
  · simp [hi]
  · constructor
    · intro h _
      rw [Submodule.mem_span_singleton_mul]
      exact ⟨β * α i, h, by field_simp⟩
    · intro h
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_span_singleton_mul.mp (h hi)
      rwa [show (α i)⁻¹ * z * α i = z by field_simp]

/-- **Example 81:4, the coefficient of a basis vector** (O'Meara 1963, p. 212): the coefficient of $x_i$ in
$\mathfrak a_1x_1 + \cdots + \mathfrak a_nx_n$ is $\mathfrak a_i$. -/
@[kb "omeara1963" "§81B, 81:4, p. 212 (the coefficient of x_i is a_i)"]
theorem coeff_basis {ι : Type*} (x : Basis ι F V) (a : ι → Submodule R F) (i : ι) :
    coeff F (⨆ j, a j • span R {x j}) (x i) = a i := by
  classical
  ext β
  rw [mem_coeff, mem_iSup_smul_span_iff]
  constructor
  · intro h
    simpa [Finsupp.single_apply] using h i
  · intro h j
    simp only [map_smul, Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij; simpa using h
    · simp [hij]

end Basis

end QuadFormsKB.OMeara
