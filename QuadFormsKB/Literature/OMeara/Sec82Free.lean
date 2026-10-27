/-
# O'Meara §82A–§82C: representations of lattices, free lattices and matrices, the class and the proper class

**Setting.** $R$ is an integral domain with fraction field $F$ (O'Meara: a Dedekind domain; nothing more is used
here), $2 \in F^\times$, and $(V, Q)$, $(V', Q')$ are quadratic spaces over $F$ with O'Meara's bilinear form $B$ =
`bil Q` ($B(x,x) = Q(x)$). Lattices are $R$-submodules (`Submodule R V`); a free lattice with base $x_1, \dots, x_n$ is
given by a base `b : Basis ι R L` of the lattice, or, for a lattice on $V$, by a base `x : Basis ι F V` of $V$ with
$L = \mathfrak ox_1 + \cdots + \mathfrak ox_n$ (`span R (Set.range x)`). The matrix of $L$ in the base is
$(B(x_i, x_j))$ (`gram`). Integral matrices are matrices over $R$, mapped to $F$ by `Matrix.map (algebraMap R F)`;
a matrix over $R$ is unimodular when its determinant is a unit of $R$ (O'Meara §81C, p. 214).

**Matrix conventions.** O'Meara writes $M \to N$ for $M = {}^tTNT$ with $T$ integral; here the base change
$x'_i = \sum_j T_{ij}x_j$ gives the matrix $TNT^{\mathsf t}$ (`gram_comb`), so the statements use $T N T^{\mathsf t}$
(O'Meara's $T$ is the transpose of the one here). An automorph of $M$ is a matrix $T$ with ${}^tTMT = M$
(O'Meara §43A); the matrix $T$ of $\sigma$ in the base $x$ has $\sigma x_j = \sum_i T_{ij}x_i$.

**Defines** the representation $K \to L$ of a lattice by a lattice (`LatticeIsRepresentedBy`, §82A, p. 220).

**Proves** (O'Meara 1963, §82B–§82C, pp. 220–223):
* `isRepresentedBy_iff_gram` (**82:1 (1)**) and `isometricLat_iff_gram` (**82:1 (2)**);
* `orthLat_latMap` (**82:2**); `clsPlus_eq_cls_iff_relIndex` (**82:3**); `clsPlus_eq_cls_of_odd` (**82:4**);
* `mem_orthLat_iff_integral` and `clsPlus_eq_cls_iff_improper_automorph` (**82:5**);
* `mem_cls_iff_gram` (**82:6**).
-/
import QuadFormsKB.Literature.OMeara.Sec82Isom
import QuadFormsKB.Literature.OMeara.Sec81Change
import QuadFormsKB.Literature.OMeara.Sec91Units
import QuadFormsKB.Literature.OMeara.Sec92Jordan

open QuadraticMap Submodule Module
open scoped Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Rep

variable {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {V' : Type*} [AddCommGroup V'] [Module F V'] [Module R V'] [IsScalarTower R F V']

/-- **Representation of a lattice by a lattice** $K \to L$ (O'Meara 1963, §82A, p. 220): there is a representation
$\sigma : FK \to FL$ with $\sigma K \subseteq L$. Here: an $R$-linear map $f : K \to L$ with $Q(f x) = Q'(x)$ (it
extends uniquely to an $F$-linear map $FK \to FL$, which is then a representation of quadratic spaces). The lattice
$K$ lies in $(V', Q')$ and $L$ in $(V, Q)$. -/
@[kb "omeara1963" "§82A, p. 220 (K is represented by L, K → L)"]
def LatticeIsRepresentedBy (Q' : QuadraticForm F V') (Q : QuadraticForm F V) (K : Submodule R V')
    (L : Submodule R V) : Prop :=
  ∃ f : K →ₗ[R] L, ∀ x : K, Q (f x : V) = Q' (x : V')

end Rep

section Domain

variable {R : Type*} [CommRing R] [IsDomain R] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {V' : Type*} [AddCommGroup V'] [Module F V'] [Module R V'] [IsScalarTower R F V']
variable (Q : QuadraticForm F V) (Q' : QuadraticForm F V')

/-- An $R$-linear representation $K \to L$ preserves $B$. -/
theorem bil_eq_of_rep {K : Submodule R V'} {L : Submodule R V} (f : K →ₗ[R] L)
    (hf : ∀ x : K, Q (f x : V) = Q' (x : V')) (x y : K) :
    bil Q (f x : V) (f y : V) = bil Q' (x : V') (y : V') := by
  rw [bil_eq_half, bil_eq_half, ← hf x, ← hf y]
  have : Q' ((x : V') + y) = Q ((f x : V) + f y) := by
    rw [← Submodule.coe_add, ← hf (x + y), map_add, Submodule.coe_add]
  rw [this]

/-- The image of a free lattice under $\sigma$. -/
theorem latMap_span_range {ι : Type*} (σ : V ≃ₗ[F] V) (c : ι → V) :
    latMap σ (span R (Set.range c)) = span R (Set.range fun i => σ (c i)) := by
  rw [latMap, Submodule.map_span, ← Set.range_comp]
  rfl

/-- $\sigma^{-1}(\sigma L) = L$. -/
theorem latMap_inv_latMap (σ : V ≃ₗ[F] V) (L : Submodule R V) : latMap σ⁻¹ (latMap σ L) = L := by
  rw [← latMap_mul, inv_mul_cancel, latMap_one]

/-- A linear automorphism preserving $B$ on a base is an isometry. -/
theorem mem_orth_of_bil_eq {ι : Type*} [Fintype ι] (x : Basis ι F V) (σ : V ≃ₗ[F] V)
    (h : ∀ i j, bil Q (σ (x i)) (σ (x j)) = bil Q (x i) (x j)) : σ ∈ orth Q := by
  intro v
  conv_lhs => rw [← x.sum_repr v]
  conv_rhs => rw [← x.sum_repr v]
  rw [map_sum]
  simp only [map_smul]
  rw [Q_sum, Q_sum]
  simp only [h]

/-- Bases with the same matrix are related by an isometry. -/
theorem equiv_mem_orth {ι : Type*} [Fintype ι] (c d : Basis ι F V) (h : gram Q c = gram Q d) :
    c.equiv d (Equiv.refl ι) ∈ orth Q := by
  refine mem_orth_of_bil_eq Q c _ fun i j => ?_
  have := congrFun (congrFun h i) j
  simp only [gram, Matrix.of_apply] at this
  simp only [Basis.equiv_apply, Equiv.refl_apply]
  exact this.symm

/-- If two bases of $V$ span the same $R$-lattice, they differ by a unimodular integral matrix. -/
theorem exists_unimodular_of_span_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (c d : Basis ι F V)
    (h : span R (Set.range c) = span R (Set.range d)) :
    ∃ T : Matrix ι ι R, IsUnit T.det ∧ ∀ i, d i = ∑ j, T i j • c j := by
  have hint : ∀ i j, c.repr (d i) j ∈ (algebraMap R F).range := fun i j =>
    (mem_span_range_iff_integral c (d i)).mp (h ▸ subset_span ⟨i, rfl⟩) j
  have hint' : ∀ i j, d.repr (c i) j ∈ (algebraMap R F).range := fun i j =>
    (mem_span_range_iff_integral d (c i)).mp (h ▸ subset_span ⟨i, rfl⟩) j
  choose T hT using hint
  choose S hS using hint'
  have hd : ∀ i, d i = ∑ j, T i j • c j := by
    intro i
    conv_lhs => rw [← c.sum_repr (d i)]
    simp_rw [← hT, algebraMap_smul]
  refine ⟨Matrix.of T, ?_, hd⟩
  have h1 : (Matrix.of T).map (algebraMap R F) * (Matrix.of S).map (algebraMap R F) = 1 := by
    ext i k
    have h2 := congrArg (fun v => d.repr v k) (c.sum_repr (d i))
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul, Basis.repr_self, Finsupp.single_apply] at h2
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, hT, hS, Matrix.one_apply]
    rw [h2]
  have h3 : (Matrix.of T * Matrix.of S).map (algebraMap R F) = 1 := by
    rw [Matrix.map_mul]; exact h1
  have h4 : (Matrix.of T * Matrix.of S).det = 1 := by
    apply IsFractionRing.injective R F
    rw [map_one, RingHom.map_det]
    simpa using congrArg Matrix.det h3
  rw [Matrix.det_mul] at h4
  exact IsUnit.of_mul_eq_one _ h4

/-- **Proposition 82:1 (1)** (O'Meara 1963, p. 222). Let $K$ and $L$ be free lattices with bases $b'$ and $b$ and
matrices $M = (B'(b'_k, b'_l))$ and $N = (B(b_i, b_j))$. Then $K \to L$ if and only if $M \to N$ over $\mathfrak o$,
i.e. $M = TNT^{\mathsf t}$ for an integral (rectangular) matrix $T$. -/
@[kb "omeara1963" "§82B, 82:1 (1), p. 222"]
theorem isRepresentedBy_iff_gram {K : Submodule R V'} {L : Submodule R V} {κ ι : Type*} [Fintype κ] [Fintype ι]
    (b' : Basis κ R K) (b : Basis ι R L) :
    LatticeIsRepresentedBy Q' Q K L ↔ ∃ T : Matrix κ ι R,
      gram Q' (fun k => (b' k : V')) = T.map (algebraMap R F) * gram Q (fun i => (b i : V)) *
        (T.map (algebraMap R F))ᵀ := by
  classical
  constructor
  · rintro ⟨f, hf⟩
    set T : Matrix κ ι R := Matrix.of fun k i => b.repr (f (b' k)) i with hTdef
    have hfb : (fun k => (f (b' k) : V)) = fun k => ∑ i, T k i • (b i : V) := by
      funext k
      have := congrArg Subtype.val (b.sum_repr (f (b' k)))
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      simpa [T] using this.symm
    refine ⟨T, ?_⟩
    rw [← gram_comb Q (fun i => (b i : V)) T, ← hfb]
    ext k l
    simp only [gram, Matrix.of_apply]
    exact (bil_eq_of_rep Q Q' f hf (b' k) (b' l)).symm
  · rintro ⟨T, hT⟩
    let g : κ → L := fun k => ∑ i, T k i • b i
    refine ⟨b'.constr R g, fun x => ?_⟩
    have hx : (x : V') = ∑ k, b'.repr x k • (b' k : V') := by
      have := congrArg Subtype.val (b'.sum_repr x)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this.symm
    have hfx : ((b'.constr R g x : L) : V) = ∑ k, b'.repr x k • ∑ i, T k i • (b i : V) := by
      conv_lhs => rw [← b'.sum_repr x]
      simp only [map_sum, map_smul, Basis.constr_basis, Submodule.coe_sum, Submodule.coe_smul, g]
    rw [hfx, hx, Q_sum_R Q (b'.repr x) (fun k => ∑ i, T k i • (b i : V)),
      Q_sum_R Q' (b'.repr x) (fun k => (b' k : V'))]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    have h1 := congrFun (congrFun (gram_comb Q (fun i => (b i : V)) T) k) l
    rw [← hT] at h1
    simp only [gram, Matrix.of_apply] at h1
    rw [← h1]

/-- **Proposition 82:1 (2)** (O'Meara 1963, p. 222). Let $L$ and $K$ be free lattices with bases $b$ and $b'$ (of the
same size) and matrices $N$ and $M$. Then $L \cong K$ if and only if $M \cong N$ over $\mathfrak o$, i.e.
$M = TNT^{\mathsf t}$ for a unimodular matrix $T$. -/
@[kb "omeara1963" "§82B, 82:1 (2), p. 222"]
theorem isometricLat_iff_gram {L : Submodule R V} {K : Submodule R V'} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι R L) (b' : Basis ι R K) :
    IsometricLat Q Q' L K ↔ ∃ T : Matrix ι ι R, IsUnit T.det ∧
      gram Q' (fun i => (b' i : V')) = T.map (algebraMap R F) * gram Q (fun i => (b i : V)) *
        (T.map (algebraMap R F))ᵀ := by
  constructor
  · rintro ⟨f, hf⟩
    let c : Basis ι R K := b.map f
    let T : Matrix ι ι R := (c.toMatrix b')ᵀ
    refine ⟨T, ?_, ?_⟩
    · have h := c.toMatrix_mul_toMatrix_flip b'
      have := congrArg Matrix.det h
      rw [Matrix.det_mul, Matrix.det_one] at this
      simp only [T, Matrix.det_transpose]
      exact IsUnit.of_mul_eq_one _ this
    · have hb' : (fun i => (b' i : V')) = fun i => ∑ j, T i j • (c j : V') := by
        funext i
        have := congrArg Subtype.val (c.sum_repr (b' i))
        simp only [Submodule.coe_sum, Submodule.coe_smul] at this
        rw [← this]
        simp [T, Basis.toMatrix_apply]
      have hc : (gram Q' fun i => (c i : V')) = gram Q (fun i => (b i : V)) := by
        ext i j
        simp only [gram, Matrix.of_apply, c, Basis.map_apply]
        exact bil_eq_of_isometricLat Q Q' f hf _ _
      rw [hb', gram_comb, hc]
  · rintro ⟨T, hT, hG⟩
    let A : L ≃ₗ[R] L := Matrix.toLinearEquiv b Tᵀ (by rwa [Matrix.det_transpose])
    let b'' : Basis ι R L := b.map A
    have hb'' : ∀ i, (b'' i : V) = ∑ j, T i j • (b j : V) := by
      intro i
      simp [b'', A, Matrix.toLinearEquiv, Matrix.toLin_self]
    apply isometricLat_of_gram_eq Q Q' b'' b'
    rw [hG]
    have : (fun i => (b'' i : V)) = fun i => ∑ j, T i j • (b j : V) := funext hb''
    rw [this, gram_comb]

variable [FiniteDimensional F V]

/-- A regular non-zero space has an anisotropic vector. -/
theorem exists_Q_ne_zero (hV : (QuadraticMap.associated Q).Nondegenerate) [Nontrivial V] :
    ∃ u : V, Q u ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨m, hm⟩ := exists_ne (0 : V)
  refine hm (hV.1 m fun n => ?_)
  change bil Q m n = 0
  rw [bil_eq_half, hcon, hcon, hcon]; simp

/-- Membership in $O^+(L)$ for a unit of $L$ means determinant $1$. -/
theorem mem_orthLatPlus_iff' {L : Submodule R V} {σ : V ≃ₗ[F] V} (h : σ ∈ orthLat Q L) :
    σ ∈ orthLatPlus Q L ↔ LinearEquiv.det σ = 1 :=
  ⟨fun H => H.2.2, fun H => ⟨h, h.1, H⟩⟩

omit [IsDomain R] [IsFractionRing R F] in
/-- $-1 \ne 1$ in $F^\times$. -/
theorem neg_one_ne_one_units : (-1 : Fˣ) ≠ 1 := by
  intro h
  have h2 : ((-1 : Fˣ) : F) = ((1 : Fˣ) : F) := congrArg Units.val h
  simp only [Units.val_neg, Units.val_one] at h2
  have : (2 : F) = 0 := by linear_combination -h2
  exact two_ne_zero this

/-- $(O(L) : O^+(L)) = 2$ iff $O(L)$ contains an isometry of determinant $-1$. -/
theorem relIndex_eq_two_iff_exists (hV : (QuadraticMap.associated Q).Nondegenerate)
    (L : Submodule R V) : (orthLatPlus Q L).relIndex (orthLat Q L) = 2 ↔
      ∃ σ ∈ orthLat Q L, LinearEquiv.det σ = -1 := by
  have hmem : ∀ c : orthLat Q L, c ∈ (orthLatPlus Q L).subgroupOf (orthLat Q L) ↔
      LinearEquiv.det (c : V ≃ₗ[F] V) = 1 := fun c => mem_orthLatPlus_iff' Q c.2
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  constructor
  · rintro ⟨a, ha⟩
    have h1 := ha 1
    have h1mem : (1 : orthLat Q L) ∈ (orthLatPlus Q L).subgroupOf (orthLat Q L) := one_mem _
    have hna : a ∉ (orthLatPlus Q L).subgroupOf (orthLat Q L) := by
      intro hm
      rw [one_mul] at h1
      rcases h1 with ⟨-, h'⟩ | ⟨-, h'⟩
      · exact h' h1mem
      · exact h' hm
    rw [hmem] at hna
    refine ⟨a, a.2, ?_⟩
    rcases det_orth_eq Q hV a.2.1 with h | h
    · exact absurd h hna
    · exact h
  · rintro ⟨σ, hσ, hd⟩
    refine ⟨⟨σ, hσ⟩, fun b => ?_⟩
    have hb := det_orth_eq Q hV b.2.1
    rw [hmem, hmem]
    have hd' : LinearEquiv.det ((b * ⟨σ, hσ⟩ : orthLat Q L) : V ≃ₗ[F] V) =
        LinearEquiv.det (b : V ≃ₗ[F] V) * -1 := by
      rw [← hd, ← map_mul]; rfl
    rw [hd']
    have hne := neg_one_ne_one_units (F := F)
    rcases hb with h | h
    · rw [h]; simp [hne]
    · rw [h]; simp [hne]

/-- $\operatorname{cls}^+ L = \operatorname{cls} L$ iff $O(L)$ contains an isometry of determinant $-1$. -/
theorem clsPlus_eq_cls_iff_exists (hV : (QuadraticMap.associated Q).Nondegenerate) [Nontrivial V]
    (L : Submodule R V) : clsPlus Q L = cls Q L ↔ ∃ σ ∈ orthLat Q L, LinearEquiv.det σ = -1 := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ := exists_Q_ne_zero Q hV
    have hmem : latMap (symmetry Q u hu) L ∈ cls Q L := ⟨_, symmetry_mem_orth Q hu, rfl⟩
    rw [← h] at hmem
    obtain ⟨ρ, hρ, hρL⟩ := hmem
    have hρd : LinearEquiv.det ρ = 1 := hρ.2
    refine ⟨ρ⁻¹ * symmetry Q u hu, ⟨(orth Q).mul_mem ((orth Q).inv_mem hρ.1) (symmetry_mem_orth Q hu), ?_⟩,
      ?_⟩
    · rw [latMap_mul, hρL, latMap_inv_latMap]
    · rw [map_mul, map_inv, hρd, det_symmetry Q hu]; simp
  · rintro ⟨σ₀, hσ₀, hd⟩
    ext K
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      exact ⟨σ, hσ.1, rfl⟩
    · rintro ⟨σ, hσ, rfl⟩
      rcases det_orth_eq Q hV hσ with h | h
      · exact ⟨σ, ⟨hσ, h⟩, rfl⟩
      · refine ⟨σ * σ₀, ⟨(orth Q).mul_mem hσ hσ₀.1, ?_⟩, ?_⟩
        · show LinearEquiv.det (σ * σ₀) = 1
          rw [map_mul, h, hd]; simp
        · rw [latMap_mul, hσ₀.2]

/-- **Example 82:3** (O'Meara 1963, p. 223). For a lattice $L$ on a regular non-zero quadratic space $V$:
$\operatorname{cls} L = \operatorname{cls}^+ L$ if and only if $(O(L) : O^+(L)) = 2$. -/
@[kb "omeara1963" "§82C, 82:3, p. 223"]
theorem clsPlus_eq_cls_iff_relIndex (hV : (QuadraticMap.associated Q).Nondegenerate) [Nontrivial V]
    (L : Submodule R V) : clsPlus Q L = cls Q L ↔ (orthLatPlus Q L).relIndex (orthLat Q L) = 2 := by
  rw [relIndex_eq_two_iff_exists Q hV, clsPlus_eq_cls_iff_exists Q hV]

/-- **Example 82:4** (O'Meara 1963, p. 223): $\operatorname{cls} L = \operatorname{cls}^+ L$ if $\dim V$ is odd, since
$-1_V$ is in $O(L)$ but not in $O^+(L)$ ($V$ regular). -/
@[kb "omeara1963" "§82C, 82:4, p. 223"]
theorem clsPlus_eq_cls_of_odd (hV : (QuadraticMap.associated Q).Nondegenerate) (hodd : Odd (finrank F V))
    (L : Submodule R V) : clsPlus Q L = cls Q L := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos hodd.pos
  rw [clsPlus_eq_cls_iff_exists Q hV]
  have hneg : (LinearEquiv.neg F : V ≃ₗ[F] V) ∈ orth Q := fun x => by simp
  refine ⟨LinearEquiv.neg F, ⟨hneg, ?_⟩, ?_⟩
  · ext v
    simp only [latMap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
      LinearEquiv.neg_apply]
    constructor
    · rintro ⟨w, hw, rfl⟩; exact L.neg_mem hw
    · intro hv; exact ⟨-v, L.neg_mem hv, by simp⟩
  · apply Units.ext
    rw [LinearEquiv.coe_det]
    have : ((LinearEquiv.neg F : V ≃ₗ[F] V) : V →ₗ[F] V) = (-1 : F) • LinearMap.id := by
      ext v; simp
    rw [this, LinearMap.det_smul, LinearMap.det_id, mul_one, hodd.neg_one_pow]
    simp

/-- **Example 82:5, units of a free lattice** (O'Meara 1963, p. 223). Let $L = \mathfrak ox_1 + \cdots +
\mathfrak ox_n$ for a base $x$ of the regular space $V$. An isometry $\sigma \in O(V)$ is a unit of $L$ if and only if
its matrix in the base $x$ is integral, i.e. the isomorphism $\sigma \mapsto$ (matrix of $\sigma$) of $O(V)$ onto the
automorphs of the matrix of $V$ (§43A) carries $O(L)$ onto the integral automorphs. -/
@[kb "omeara1963" "§82C, 82:5, p. 223 (O(L) ↔ integral automorphs)"]
theorem mem_orthLat_iff_integral (hV : (QuadraticMap.associated Q).Nondegenerate) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (x : Basis ι F V) {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q) :
    σ ∈ orthLat Q (span R (Set.range x)) ↔ ∀ i j, x.repr (σ (x j)) i ∈ (algebraMap R F).range := by
  classical
  show (σ ∈ orth Q ∧ latMap σ (span R (Set.range x)) = span R (Set.range x)) ↔ _
  constructor
  · rintro ⟨-, h⟩ i j
    have : σ (x j) ∈ span R (Set.range x) := by
      rw [← h]; exact ⟨x j, subset_span ⟨j, rfl⟩, rfl⟩
    exact (mem_span_range_iff_integral x _).mp this i
  · intro h
    refine ⟨hσ, le_antisymm ?_ ?_⟩
    · rw [latMap_span_range, span_le]
      rintro _ ⟨j, rfl⟩
      exact (mem_span_range_iff_integral x _).mpr (fun i => h i j)
    · choose A hA using h
      have hAf : (Matrix.of A).map (algebraMap R F) = LinearMap.toMatrix x x σ := by
        ext i j; simp [hA, LinearMap.toMatrix_apply]
      have hdet : IsUnit (Matrix.of A).det := by
        have h1 : algebraMap R F (Matrix.of A).det = ((LinearEquiv.det σ : Fˣ) : F) := by
          rw [RingHom.map_det, RingHom.mapMatrix_apply, hAf, LinearMap.det_toMatrix,
            LinearEquiv.coe_det]
        rcases det_orth_eq Q hV hσ with h | h
        · rw [h] at h1
          have : (Matrix.of A).det = 1 := IsFractionRing.injective R F (by simpa using h1)
          rw [this]; exact isUnit_one
        · rw [h] at h1
          have : (Matrix.of A).det = -1 := IsFractionRing.injective R F (by simpa using h1)
          rw [this]; exact isUnit_one.neg
      have hσx : ∀ k, σ (x k) = ∑ i, A i k • x i := by
        intro k
        conv_lhs => rw [← x.sum_repr (σ (x k))]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← hA i k, algebraMap_smul]
      have hAB : Matrix.of A * (Matrix.of A)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
      rw [span_le]
      rintro _ ⟨j, rfl⟩
      refine ⟨∑ k, (Matrix.of A)⁻¹ k j • x k,
        sum_mem fun k _ => smul_mem _ _ (subset_span ⟨k, rfl⟩), ?_⟩
      simp only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, map_sum]
      have hs : ∀ k, σ (((Matrix.of A)⁻¹ k j) • x k) = ((Matrix.of A)⁻¹ k j) • σ (x k) := fun k => by
        rw [← algebraMap_smul F, map_smul, algebraMap_smul]
      simp_rw [hs, hσx, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul]
      have h2 : ∀ i, ∑ k, (Matrix.of A)⁻¹ k j * A i k = (Matrix.of A * (Matrix.of A)⁻¹) i j := by
        intro i; simp [Matrix.mul_apply, mul_comm]
      simp_rw [h2, hAB, Matrix.one_apply]
      simp

/-- **Example 82:5, improper automorphs** (O'Meara 1963, p. 223). Let $L = \mathfrak ox_1 + \cdots + \mathfrak ox_n$
for a base $x$ of the regular non-zero space $V$, with matrix $M$. Then $\operatorname{cls} L = \operatorname{cls}^+ L$
if and only if $M$ has an improper integral automorph: an integral $T$ with $\det T = -1$ and ${}^tTMT = M$. -/
@[kb "omeara1963" "§82C, 82:5, p. 223 (cls L = cls⁺ L iff an improper integral automorph)"]
theorem clsPlus_eq_cls_iff_improper_automorph (hV : (QuadraticMap.associated Q).Nondegenerate) [Nontrivial V]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (x : Basis ι F V) :
    clsPlus Q (span R (Set.range x)) = cls Q (span R (Set.range x)) ↔
      ∃ T : Matrix ι ι R, T.det = -1 ∧
        (T.map (algebraMap R F))ᵀ * gram Q x * T.map (algebraMap R F) = gram Q x := by
  classical
  rw [clsPlus_eq_cls_iff_exists Q hV]
  constructor
  · rintro ⟨σ, hσ, hdet⟩
    have hint := (mem_orthLat_iff_integral Q hV x hσ.1).mp hσ
    choose T hT using hint
    have hTf : (Matrix.of T).map (algebraMap R F) = LinearMap.toMatrix x x σ := by
      ext i j; simp [hT, LinearMap.toMatrix_apply]
    refine ⟨Matrix.of T, ?_, ?_⟩
    · apply IsFractionRing.injective R F
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hTf, LinearMap.det_toMatrix, ← LinearEquiv.coe_det,
        hdet]
      simp
    · have hσx : (fun j => σ (x j)) = fun j => ∑ i, (Matrix.of T)ᵀ j i • x i := by
        funext j
        conv_lhs => rw [← x.sum_repr (σ (x j))]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← hT i j, algebraMap_smul]; rfl
      have hg : (gram Q fun j => σ (x j)) = gram Q x := by
        ext i j
        simp only [gram, Matrix.of_apply]
        exact bil_orth Q hσ.1 _ _
      rw [hσx, gram_comb, Matrix.transpose_map, Matrix.transpose_transpose] at hg
      exact hg
  · rintro ⟨T, hdet, hT⟩
    let Tf : Matrix ι ι F := T.map (algebraMap R F)
    have hdetf : Tf.det = -1 := by
      have : Tf.det = algebraMap R F T.det := (RingHom.map_det _ _).symm
      rw [this, hdet, map_neg, map_one]
    have hTf : IsUnit Tf.det := by rw [hdetf]; exact isUnit_one.neg
    let σ : V ≃ₗ[F] V := Matrix.toLinearEquiv x Tf hTf
    have hσlin : (σ : V →ₗ[F] V) = Matrix.toLin x x Tf := rfl
    have hσx : ∀ j, σ (x j) = ∑ i, Tf i j • x i := by
      intro j; exact Matrix.toLin_self x x Tf j
    have hrepr : ∀ i j, x.repr (σ (x j)) i = Tf i j := by
      intro i j
      rw [show x.repr (σ (x j)) i = LinearMap.toMatrix x x (Matrix.toLin x x Tf) i j by
        rw [LinearMap.toMatrix_apply]; rfl, LinearMap.toMatrix_toLin]
    have hσorth : σ ∈ orth Q := by
      refine mem_orth_of_bil_eq Q x σ fun i j => ?_
      have hfun : (fun j => σ (x j)) = fun j => ∑ i, Tᵀ j i • x i := by
        funext j; rw [hσx]
        refine Finset.sum_congr rfl fun i _ => ?_
        show algebraMap R F (T i j) • x i = _
        rw [algebraMap_smul]; rfl
      have h1 : (gram Q fun j => σ (x j)) = gram Q x := by
        rw [hfun, gram_comb, Matrix.transpose_map, Matrix.transpose_transpose]
        exact hT
      have := congrFun (congrFun h1 i) j
      simpa [gram] using this
    refine ⟨σ, (mem_orthLat_iff_integral Q hV x hσorth).mpr fun i j => ⟨T i j, by rw [hrepr]; rfl⟩, ?_⟩
    apply Units.ext
    rw [LinearEquiv.coe_det, hσlin, LinearMap.det_toLin]
    simpa using hdetf

/-- A unimodular integral change of generators does not change the $R$-span. -/
theorem span_range_eq_of_unimodular {ι : Type*} [Fintype ι] [DecidableEq ι] (c d : ι → V)
    (T : Matrix ι ι R) (hT : IsUnit T.det) (h : ∀ i, d i = ∑ j, T i j • c j) :
    span R (Set.range c) = span R (Set.range d) := by
  apply le_antisymm
  · rw [span_le]
    rintro _ ⟨j, rfl⟩
    have : c j = ∑ k, T⁻¹ j k • d k := by
      simp_rw [h, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul]
      have : ∀ l, ∑ k, T⁻¹ j k * T k l = (T⁻¹ * T) j l := fun l => rfl
      simp_rw [this, Matrix.nonsing_inv_mul _ hT]
      simp [Matrix.one_apply]
    rw [this]
    exact sum_mem fun k _ => smul_mem _ _ (subset_span ⟨k, rfl⟩)
  · rw [span_le]
    rintro _ ⟨i, rfl⟩
    rw [h]
    exact sum_mem fun j _ => smul_mem _ _ (subset_span ⟨j, rfl⟩)

/-- **Example 82:6** (O'Meara 1963, p. 223). Let $K = \mathfrak ox_1 + \cdots + \mathfrak ox_n$ and
$L = \mathfrak oy_1 + \cdots + \mathfrak oy_n$ be free lattices on $V$ with matrices $M$ and $N$. Then
$\operatorname{cls} K = \operatorname{cls} L$ (i.e. $K \in \operatorname{cls} L$) if and only if
$\operatorname{cls} M = \operatorname{cls} N$, i.e. $M = TNT^{\mathsf t}$ for a unimodular $T$. -/
@[kb "omeara1963" "§82C, 82:6, p. 223"]
theorem mem_cls_iff_gram {ι : Type*} [Fintype ι] [DecidableEq ι] (x y : Basis ι F V) :
    span R (Set.range x) ∈ cls Q (span R (Set.range y)) ↔ ∃ T : Matrix ι ι R, IsUnit T.det ∧
      gram Q x = T.map (algebraMap R F) * gram Q y * (T.map (algebraMap R F))ᵀ := by
  classical
  constructor
  · rintro ⟨σ, hσ, hK⟩
    have hfun : (⇑(y.map σ)) = fun i => σ (y i) := by funext i; simp
    have hy' : span R (Set.range (y.map σ)) = span R (Set.range x) := by
      rw [hK, latMap_span_range, hfun]
    obtain ⟨T, hT, hx⟩ := exists_unimodular_of_span_eq (y.map σ) x hy'
    refine ⟨T, hT, ?_⟩
    have hx' : (⇑x) = fun i => ∑ j, T i j • σ (y j) := by
      funext i; rw [hx i]; simp
    have hg : (gram Q fun j => σ (y j)) = gram Q y := by
      ext i j
      simp only [gram, Matrix.of_apply]
      exact bil_orth Q hσ _ _
    rw [hx', gram_comb, hg]
  · rintro ⟨T, hT, hG⟩
    let Tf : Matrix ι ι F := T.map (algebraMap R F)
    have hTf : IsUnit Tf.det := by
      have : Tf.det = algebraMap R F T.det := (RingHom.map_det _ _).symm
      rw [this]; exact hT.map _
    let y' : Basis ι F V := y.map (Matrix.toLinearEquiv y Tfᵀ (by rwa [Matrix.det_transpose]))
    have hy' : ∀ i, y' i = ∑ j, T i j • y j := by
      intro i
      simp [y', Matrix.toLinearEquiv, Matrix.toLin_self, Tf]
    have hgram : gram Q y' = gram Q x := by
      have : (⇑y') = fun i => ∑ j, T i j • y j := funext hy'
      rw [this, gram_comb, hG]
    refine ⟨y'.equiv x (Equiv.refl ι), equiv_mem_orth Q y' x hgram, ?_⟩
    rw [span_range_eq_of_unimodular y y' T hT hy', latMap_span_range]
    have : (fun i => (y'.equiv x (Equiv.refl ι)) (y' i)) = ⇑x := by
      funext i; simp
    rw [this]

/-- **Example 82:2** (O'Meara 1963, p. 223): $\sigma O(L)\sigma^{-1} = O(\sigma L)$ for $\sigma \in O(V)$. -/
@[kb "omeara1963" "§82C, 82:2, p. 223"]
theorem orthLat_latMap {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q) (L : Submodule R V) :
    orthLat Q (latMap σ L) = (orthLat Q L).map (MulAut.conj σ).toMonoidHom := by
  ext τ
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨hτ, hτL⟩
    refine ⟨σ⁻¹ * τ * σ, ⟨?_, ?_⟩, ?_⟩
    · exact (orth Q).mul_mem ((orth Q).mul_mem ((orth Q).inv_mem hσ) hτ) hσ
    · rw [latMap_mul, latMap_mul, hτL, latMap_inv_latMap]
    · simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,MulAut.conj_apply]
      group
  · rintro ⟨ρ, ⟨hρ, hρL⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · exact (orth Q).mul_mem ((orth Q).mul_mem hσ hρ) ((orth Q).inv_mem hσ)
    · show latMap (σ * ρ * σ⁻¹) (latMap σ L) = latMap σ L
      rw [latMap_mul, latMap_mul, latMap_inv_latMap, hρL]

end Domain

end QuadFormsKB.OMeara
