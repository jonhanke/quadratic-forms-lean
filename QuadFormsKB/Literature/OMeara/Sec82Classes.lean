/-
# O'Meara §82A–§82C, §82E, §82H: isometries into, integral equivalence of matrices, proper classes

**Setting.** $R$ is a commutative ring with an algebra map to a field $F$ with $2 \in F^\times$; from the second section
on, $R$ is a domain with fraction field $F$ (O'Meara's $\mathfrak o$ and $F$ in Chapter VIII). $(V, Q)$ is a quadratic
space over $F$ with O'Meara's bilinear form $B$ = `bil Q`; lattices are `Submodule R V` as in `Sec82.lean`.

**Defines** (O'Meara 1963, §82A–§82C, pp. 220–223; §82H, p. 234):
* `LatticeIsometryInto Q' Q K L`: an isometry of $K$ into $L$, $K \rightarrowtail L$ (§82A, p. 220);
* `MatIntRep M N`, `MatIntEquiv M N`, `matCls N`: $M$ is integrally represented by $N$, $M \to N$; $M$ is integrally
  equivalent to $N$, $M \cong N$; the class $\operatorname{cls} N$ of $N$ (§82B, p. 221);
* `matForm N`, `matLat ι`: the quadratic space $(N)$ with matrix $N$ (on $F^\iota$) and the free lattice
  $\langle N \rangle = \sum_i \mathfrak o e_i$ in it (§82B, p. 221);
* `orthMinus`, `orthLatMinus`: $O^-(V)$ (isometries of determinant $-1$) and $O^-(L) = O(L) \cap O^-(V)$ (§82C,
  p. 223);
* `HasMatrix Q L N`: $L$ has the matrix $N$, $L \cong N$ (§82B, p. 221); `Splits Q K L`: $K$ splits $L$ (§82D,
  p. 224); `IsOrthBase Q b`: an orthogonal base of a lattice (§82D, p. 225);
* `IsMaximalOn Q L`: $L$ is maximal on $V$, i.e. $\mathfrak a$-maximal for some fractional ideal $\mathfrak a$ (§82H,
  p. 234).

**Proves**
* `LatticeIsometryInto.isRepresentedBy`, `injective_of_isRegular`, `latticeIsometryInto_iff_of_isRegular`: an isometry
  into is a representation, and every representation of a regular lattice is an isometry into (§82A);
* `matIntEquiv_equivalence`, `mem_matCls_iff`, `isRepresentedBy_iff_matIntRep`, `isometricLat_iff_matIntEquiv`:
  integral equivalence is an equivalence relation, the classes partition the matrices, and 82:1 in this language
  (§82B, pp. 221–222);
* `gram_matForm`, `matLat_isLattice`, `exists_basis_matLat`: every symmetric matrix is the matrix of a free lattice on a
  quadratic space, so every class of matrices comes from a free lattice (§82B, p. 221);
* `matIntEquiv_gram_of_basis`, `hasMatrix_of_matIntEquiv`: a change of base replaces the matrix $N$ of a free lattice
  by a matrix of $\operatorname{cls} N$, and every matrix of $\operatorname{cls} N$ arises so (§82B, p. 221);
  `hasDisc_bot`, `volume_bot`: the conventions $d\,0 = 1$ (p. 222) and $\mathfrak v\,0 = \mathfrak o$ (§82E, p. 229);
* `mem_clsPlus_iff`, `mem_cls_iff`, `clsPlus_subset_cls`, `cls_eq_biUnion_clsPlus`, `ncard_clsPlus_image_cls`: the proper classes
  partition the lattices on $V$, refine the classes, and each class contains one or two proper classes (§82C,
  p. 222);
* `orthLat_eq_union`, `disjoint_orthLatPlus_orthLatMinus`, `relIndex_eq_two_of_symmetry_mem`:
  $O(L) = O^+(L) \cup O^-(L)$ disjointly, and $(O(L) : O^+(L)) = 2$ when a reflexion (symmetry) of $V$ is a unit of $L$
  (§82C, p. 223);
* `image_span_eq`, `scale_normIdeal_tfae`: $Q(FL) = F^2Q(L)$, and $\mathfrak sL$, $\mathfrak nL$, $B(FL, FL)$,
  $Q(FL)$ are $0$ if one of them is (§82E, p. 227).
-/
import QuadFormsKB.Literature.OMeara.Sec82Free

open QuadraticMap Submodule Module
open scoped Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Rep

variable {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {V' : Type*} [AddCommGroup V'] [Module F V'] [Module R V'] [IsScalarTower R F V']

/-- **Isometry of a lattice into a lattice** $K \rightarrowtail L$ (O'Meara 1963, §82A, p. 220): an isometry
$\sigma : FK \rightarrowtail FL$ (an injective representation) with $\sigma K \subseteq L$. Here, as for
`LatticeIsRepresentedBy`: an injective $R$-linear map $f : K \to L$ with $Q(f x) = Q'(x)$ (it extends uniquely to an
injective $F$-linear isometry $FK \to FL$). The lattice $K$ lies in $(V', Q')$ and $L$ in $(V, Q)$. -/
@[kb "omeara1963" "§82A, p. 220 (isometry of K into L, K ↣ L)"]
def LatticeIsometryInto (Q' : QuadraticForm F V') (Q : QuadraticForm F V) (K : Submodule R V')
    (L : Submodule R V) : Prop :=
  ∃ f : K →ₗ[R] L, Function.Injective f ∧ ∀ x : K, Q (f x : V) = Q' (x : V')

variable {Q : QuadraticForm F V} {Q' : QuadraticForm F V'}

/-- An isometry into is a representation (O'Meara 1963, §82A, p. 220). -/
@[kb "omeara1963" "§82A, p. 220 (K ↣ L implies K → L)"]
theorem LatticeIsometryInto.isRepresentedBy {K : Submodule R V'} {L : Submodule R V}
    (h : LatticeIsometryInto Q' Q K L) : LatticeIsRepresentedBy Q' Q K L :=
  let ⟨f, _, hf⟩ := h; ⟨f, hf⟩

/-- An isometry onto is an isometry into (O'Meara 1963, §82A, p. 220). -/
@[kb "omeara1963" "§82A, p. 220 (K ≅ L implies K ↣ L)"]
theorem IsometricLat.latticeIsometryInto {K : Submodule R V'} {L : Submodule R V}
    (h : IsometricLat Q' Q K L) : LatticeIsometryInto Q' Q K L :=
  let ⟨f, hf⟩ := h; ⟨f.toLinearMap, f.injective, hf⟩

end Rep

section Domain

variable {R : Type*} [CommRing R] [IsDomain R] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {V' : Type*} [AddCommGroup V'] [Module F V'] [Module R V'] [IsScalarTower R F V']
variable (Q : QuadraticForm F V) (Q' : QuadraticForm F V')

/-- **A representation of a regular lattice is injective** (O'Meara 1963, §82A, p. 220): if $K$ is regular, every
representation $f : K \to L$ is an isometry of $K$ into $L$. -/
@[kb "omeara1963" "§82A, p. 220 (a representation of a regular lattice is an isometry into)"]
theorem injective_of_isRegular {K : Submodule R V'} {L : Submodule R V} (hK : IsRegular Q' K)
    (f : K →ₗ[R] L) (hf : ∀ x : K, Q (f x : V) = Q' (x : V')) : Function.Injective f := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  rw [Submodule.mem_bot, ← Subtype.coe_inj, Submodule.coe_zero]
  refine hK x x.2 fun y hy => ?_
  have := bil_eq_of_rep Q Q' f hf x ⟨y, hy⟩
  rw [hx] at this
  simpa [bil] using this.symm

/-- For a regular lattice $K$: $K \rightarrowtail L$ if and only if $K \to L$ (O'Meara 1963, §82A, p. 220). -/
@[kb "omeara1963" "§82A, p. 220 (K regular: K ↣ L iff K → L)"]
theorem latticeIsometryInto_iff_of_isRegular {K : Submodule R V'} {L : Submodule R V} (hK : IsRegular Q' K) :
    LatticeIsometryInto Q' Q K L ↔ LatticeIsRepresentedBy Q' Q K L :=
  ⟨LatticeIsometryInto.isRepresentedBy, fun ⟨f, hf⟩ => ⟨f, injective_of_isRegular Q Q' hK f hf, hf⟩⟩

end Domain

/-! ### Integral representation and equivalence of matrices (§82B) -/

section Matrices

variable (R : Type*) [CommRing R] {F : Type*} [Field F] [Algebra R F]

/-- **Integral representation of matrices** $M \to N$ over $\mathfrak o$ (O'Meara 1963, §82B, p. 221): for a
$\kappa \times \kappa$ matrix $M$ and an $\iota \times \iota$ matrix $N$ over $F$, there is a $\kappa \times \iota$
matrix $T$ with entries in $\mathfrak o$ such that $M = TN\,{}^tT$ (O'Meara writes $M = {}^tTNT$ with an
$\iota \times \kappa$ matrix $T$, the transpose of the one here; see the matrix conventions of `Sec82Free.lean`). -/
@[kb "omeara1963" "§82B, p. 221 (M is integrally represented by N, M → N)"]
def MatIntRep {κ ι : Type*} [Fintype ι] [Fintype κ] (M : Matrix κ κ F) (N : Matrix ι ι F) : Prop :=
  ∃ T : Matrix κ ι R, M = T.map (algebraMap R F) * N * (T.map (algebraMap R F))ᵀ

/-- **Integral equivalence of matrices** $M \cong N$ over $\mathfrak o$ (O'Meara 1963, §82B, p. 221):
$M = TN\,{}^tT$ for a unimodular matrix $T$ (entries in $\mathfrak o$, determinant a unit of $\mathfrak o$; O'Meara's
${}^tTNT$ with $T$ transposed). -/
@[kb "omeara1963" "§82B, p. 221 (M is integrally equivalent to N)"]
def MatIntEquiv {ι : Type*} [Fintype ι] [DecidableEq ι] (M N : Matrix ι ι F) : Prop :=
  ∃ T : Matrix ι ι R, IsUnit T.det ∧ M = T.map (algebraMap R F) * N * (T.map (algebraMap R F))ᵀ

/-- **The class** $\operatorname{cls} N$ of a matrix (O'Meara 1963, §82B, p. 221): the matrices integrally
equivalent to $N$. -/
@[kb "omeara1963" "§82B, p. 221 (the class cls N of a matrix)"]
def matCls {ι : Type*} [Fintype ι] [DecidableEq ι] (N : Matrix ι ι F) : Set (Matrix ι ι F) :=
  {M | MatIntEquiv R M N}

variable {R}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem map_mul_map {κ μ : Type*} [Fintype κ] (A : Matrix ι κ R) (B : Matrix κ μ R) :
    A.map (algebraMap R F) * B.map (algebraMap R F) = (A * B).map (algebraMap R F) :=
  Matrix.map_mul.symm

/-- **Integral equivalence is an equivalence relation** on the symmetric $n \times n$ matrices over $F$ (O'Meara 1963,
§82B, p. 221; it holds on all square matrices). -/
@[kb "omeara1963" "§82B, p. 221 (integral equivalence is an equivalence relation)"]
theorem matIntEquiv_equivalence : Equivalence (MatIntEquiv (F := F) (ι := ι) R) := by
  refine ⟨fun N => ⟨1, by simp, by simp⟩, ?_, ?_⟩
  · rintro M N ⟨T, hT, rfl⟩
    have hinv : T⁻¹ * T = 1 := Matrix.nonsing_inv_mul T hT
    have hinv' : Tᵀ * T⁻¹ᵀ = 1 := by rw [← Matrix.transpose_mul, hinv, Matrix.transpose_one]
    refine ⟨T⁻¹, Matrix.isUnit_nonsing_inv_det T hT, ?_⟩
    symm
    calc (T⁻¹).map (algebraMap R F) * (T.map (algebraMap R F) * N * (T.map (algebraMap R F))ᵀ) *
          ((T⁻¹).map (algebraMap R F))ᵀ
        = ((T⁻¹).map (algebraMap R F) * T.map (algebraMap R F)) * N *
            ((T.map (algebraMap R F))ᵀ * ((T⁻¹).map (algebraMap R F))ᵀ) := by
          simp only [Matrix.mul_assoc]
      _ = (T⁻¹ * T).map (algebraMap R F) * N * (Tᵀ * T⁻¹ᵀ).map (algebraMap R F) := by
          rw [← Matrix.transpose_map, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]
      _ = N := by
          rw [hinv, hinv', Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, Matrix.mul_one]
  · rintro M N P ⟨T, hT, rfl⟩ ⟨U, hU, rfl⟩
    refine ⟨T * U, by rw [Matrix.det_mul]; exact hT.mul hU, ?_⟩
    rw [Matrix.map_mul, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]

/-- **The classes of matrices partition the matrices** (O'Meara 1963, §82B, p. 221): $M \in \operatorname{cls} N$ if
and only if $\operatorname{cls} M = \operatorname{cls} N$. -/
@[kb "omeara1963" "§82B, p. 221 (the classes partition the symmetric matrices)"]
theorem mem_matCls_iff {M N : Matrix ι ι F} : M ∈ matCls R N ↔ matCls R M = matCls R N := by
  have e := matIntEquiv_equivalence (R := R) (F := F) (ι := ι)
  constructor
  · intro h
    ext P
    exact ⟨fun hP => e.trans hP h, fun hP => e.trans hP (e.symm h)⟩
  · intro h
    have : M ∈ matCls R M := e.refl M
    rwa [h] at this

end Matrices

section Free

variable {R : Type*} [CommRing R] [IsDomain R] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {V' : Type*} [AddCommGroup V'] [Module F V'] [Module R V'] [IsScalarTower R F V']
variable (Q : QuadraticForm F V) (Q' : QuadraticForm F V')

/-- **82:1 (1) in the language of matrices** (O'Meara 1963, §82B, p. 222): for free lattices $K$, $L$ with bases
$b'$, $b$: $K \to L$ if and only if $M \to N$ for their matrices. -/
@[kb "omeara1963" "§82B, 82:1 (1), p. 222 (with M → N)"]
theorem isRepresentedBy_iff_matIntRep {K : Submodule R V'} {L : Submodule R V} {κ ι : Type*} [Fintype κ]
    [Fintype ι] (b' : Basis κ R K) (b : Basis ι R L) :
    LatticeIsRepresentedBy Q' Q K L ↔
      MatIntRep R (gram Q' fun k => (b' k : V')) (gram Q fun i => (b i : V)) :=
  isRepresentedBy_iff_gram Q Q' b' b

/-- **82:1 (2) in the language of matrices** (O'Meara 1963, §82B, p. 222): for free lattices $L$, $K$ with bases
$b$, $b'$ of the same size: $L \cong K$ if and only if their matrices are integrally equivalent. -/
@[kb "omeara1963" "§82B, 82:1 (2), p. 222 (with M ≅ N)"]
theorem isometricLat_iff_matIntEquiv {L : Submodule R V} {K : Submodule R V'} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Basis ι R L) (b' : Basis ι R K) :
    IsometricLat Q Q' L K ↔
      MatIntEquiv R (gram Q' fun i => (b' i : V')) (gram Q fun i => (b i : V)) :=
  isometricLat_iff_gram Q Q' b b'

end Free

/-! ### The space $(N)$ and the free lattice $\langle N \rangle$ (§82B) -/

section MatForm

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The quadratic space $(N)$** (O'Meara 1963, §82B, p. 221): $F^\iota$ with the quadratic form
$Q(x) = {}^t x N x$; for symmetric $N$ its matrix in the standard base is $N$ (`gram_matForm`). -/
@[kb "omeara1963" "§82B, p. 221 (the quadratic space (N) with matrix N)"]
def matForm (N : Matrix ι ι F) : QuadraticForm F (ι → F) :=
  LinearMap.BilinMap.toQuadraticMap (Matrix.toLinearMap₂' F N)

/-- The matrix of $(N)$ in the standard base $e_i$ is $N$ for a symmetric matrix $N$. -/
@[kb "omeara1963" "§82B, p. 221 ((N) has the matrix N)"]
theorem gram_matForm {N : Matrix ι ι F} (hN : N.IsSymm) :
    gram (matForm N) (fun i => Pi.single i 1) = N := by
  have hsymm : ∀ x y : ι → F, Matrix.toLinearMap₂' F N x y = Matrix.toLinearMap₂' F N y x := by
    intro x y
    rw [Matrix.toLinearMap₂'_apply', Matrix.toLinearMap₂'_apply', Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose, hN.eq, dotProduct_comm]
  have hB : QuadraticMap.associated (matForm N) = Matrix.toLinearMap₂' F N :=
    QuadraticMap.associated_left_inverse F hsymm
  ext i j
  simp only [gram, Matrix.of_apply, bil, hB]
  rw [Matrix.toLinearMap₂'_apply']
  simp

variable (R : Type*) [CommRing R] [IsDomain R] [Algebra R F] [IsFractionRing R F]

/-- **The free lattice $\langle N \rangle$** (O'Meara 1963, §82B, p. 221): $\mathfrak oe_1 + \cdots + \mathfrak oe_n$
in $F^\iota$, the standard base $e_i$ being a base of it; in the space $(N)$ it has the matrix $N$. -/
@[kb "omeara1963" "§82B, p. 221 (the free lattice ⟨N⟩ with matrix N)"]
def matLat (ι : Type*) [DecidableEq ι] : Submodule R (ι → F) :=
  span R (Set.range fun i : ι => (Pi.single i 1 : ι → F))

omit [Invertible (2 : F)] in
theorem basisFun_coe : ⇑(Pi.basisFun F ι) = fun i => (Pi.single i 1 : ι → F) :=
  funext (Pi.basisFun_apply F ι)

theorem linearIndependent_single : LinearIndependent R fun i : ι => (Pi.single i 1 : ι → F) :=
  (LinearIndependent.iff_fractionRing R F).2 (by
    rw [← basisFun_coe]; exact (Pi.basisFun F ι).linearIndependent)

/-- $\langle N \rangle$ is a lattice on $F^\iota$. -/
theorem matLat_isLattice : (matLat R (F := F) ι).IsLattice F := by
  refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
  unfold matLat
  rw [Submodule.span_span_of_tower]
  rw [← basisFun_coe]; exact (Pi.basisFun F ι).span_eq

/-- **Every class of matrices comes from a free lattice** (O'Meara 1963, §82B, p. 221): for a symmetric matrix $N$,
the lattice $\langle N \rangle$ on the space $(N)$ has a base in which its matrix is $N$. -/
@[kb "omeara1963" "§82B, p. 221 (every class of matrices comes from a free lattice)"]
theorem exists_basis_matLat {N : Matrix ι ι F} (hN : N.IsSymm) :
    ∃ b : Basis ι R (matLat R (F := F) ι), gram (matForm N) (fun i => (b i : ι → F)) = N := by
  refine ⟨Basis.span (linearIndependent_single R), ?_⟩
  convert gram_matForm hN using 2
  funext i
  exact congrArg Subtype.val (Basis.span_apply (linearIndependent_single R (F := F) (ι := ι)) i)

end MatForm

/-! ### Proper classes, $O^-(L)$, zero scale, maximal lattices (§82C, §82E, §82H) -/

section Classes

variable {R : Type*} [CommRing R] [IsDomain R] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- Orbits of a group of linear automorphisms on lattices: $K \in GL$ if and only if $GK = GL$. -/
theorem mem_orbit_iff (G : Subgroup (V ≃ₗ[F] V)) {K L : Submodule R V} :
    K ∈ {M | ∃ σ ∈ G, M = latMap σ L} ↔
      {M | ∃ σ ∈ G, M = latMap σ K} = {M | ∃ σ ∈ G, M = latMap σ L} := by
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    ext M
    constructor
    · rintro ⟨ρ, hρ, rfl⟩
      exact ⟨ρ * σ, G.mul_mem hρ hσ, (latMap_mul ρ σ L).symm⟩
    · rintro ⟨τ, hτ, rfl⟩
      refine ⟨τ * σ⁻¹, G.mul_mem hτ (G.inv_mem hσ), ?_⟩
      rw [latMap_mul, latMap_inv_latMap]
  · intro h
    have : K ∈ {M | ∃ σ ∈ G, M = latMap σ K} := ⟨1, G.one_mem, by ext; simp⟩
    rwa [h] at this

/-- **The proper classes partition the lattices on $V$** (O'Meara 1963, §82C, p. 222): $K \in \operatorname{cls}^+ L$
if and only if $\operatorname{cls}^+ K = \operatorname{cls}^+ L$. -/
@[kb "omeara1963" "§82C, p. 222 (the proper classes partition the lattices on V)"]
theorem mem_clsPlus_iff {K L : Submodule R V} : K ∈ clsPlus Q L ↔ clsPlus Q K = clsPlus Q L :=
  mem_orbit_iff (orthPlus Q)

/-- **The classes partition the lattices on $V$** (O'Meara 1963, §82C, p. 222): $K \in \operatorname{cls} L$ if and
only if $\operatorname{cls} K = \operatorname{cls} L$. -/
@[kb "omeara1963" "§82C, p. 222 (the classes partition the lattices on V)"]
theorem mem_cls_iff {K L : Submodule R V} : K ∈ cls Q L ↔ cls Q K = cls Q L :=
  mem_orbit_iff (orth Q)

/-- **The partition into proper classes is finer** (O'Meara 1963, §82C, p. 222):
$\operatorname{cls}^+ L \subseteq \operatorname{cls} L$. -/
@[kb "omeara1963" "§82C, p. 222 (the proper classes refine the classes)"]
theorem clsPlus_subset_cls (L : Submodule R V) : clsPlus Q L ⊆ cls Q L := by
  rintro K ⟨σ, hσ, rfl⟩
  exact ⟨σ, hσ.1, rfl⟩

/-- **A class is the union of the proper classes it contains** (O'Meara 1963, §82C, p. 222). -/
@[kb "omeara1963" "§82C, p. 222 (each class is a union of proper classes)"]
theorem cls_eq_biUnion_clsPlus (L : Submodule R V) : cls Q L = ⋃ K ∈ cls Q L, clsPlus Q K := by
  apply le_antisymm
  · intro K hK
    exact Set.mem_biUnion hK ⟨1, (orthPlus Q).one_mem, by ext; simp⟩
  · refine Set.iUnion₂_subset fun K hK => ?_
    rw [← (mem_cls_iff Q).1 hK]
    exact clsPlus_subset_cls Q K

/-- **Each class contains one or two proper classes** (O'Meara 1963, §82C, p. 222): for a lattice $L$ on a regular
non-zero quadratic space $V$, the set of proper classes $\operatorname{cls}^+ K$, $K \in \operatorname{cls} L$, has one
or two elements (because $O^+(V)$ has index $2$ in $O(V)$). -/
@[kb "omeara1963" "§82C, p. 222 (each class contains one or two proper classes)"]
theorem ncard_clsPlus_image_cls [FiniteDimensional F V] (hV : (QuadraticMap.associated Q).Nondegenerate)
    [Nontrivial V] (L : Submodule R V) :
    (clsPlus Q '' cls Q L).ncard = 1 ∨ (clsPlus Q '' cls Q L).ncard = 2 := by
  obtain ⟨u, hu⟩ := exists_Q_ne_zero Q hV
  set τ := symmetry Q u hu
  have hsub : clsPlus Q '' cls Q L ⊆ {clsPlus Q L, clsPlus Q (latMap τ L)} := by
    rintro _ ⟨K, ⟨σ, hσ, rfl⟩, rfl⟩
    rcases det_orth_eq Q hV hσ with h | h
    · left
      exact (mem_clsPlus_iff Q).1 ⟨σ, ⟨hσ, h⟩, rfl⟩
    · right
      refine (mem_clsPlus_iff Q).1 ⟨σ * τ⁻¹,
        ⟨(orth Q).mul_mem hσ ((orth Q).inv_mem (symmetry_mem_orth Q hu)), ?_⟩, ?_⟩
      · show LinearEquiv.det (σ * τ⁻¹) = 1
        rw [map_mul, map_inv, h, det_symmetry Q hu]; simp
      · rw [latMap_mul, latMap_inv_latMap]
  have hne : (clsPlus Q '' cls Q L).Nonempty :=
    ⟨_, L, ⟨1, (orth Q).one_mem, by ext; simp⟩, rfl⟩
  have hfin : (clsPlus Q '' cls Q L).Finite := (Set.toFinite _).subset hsub
  have h1 := (Set.ncard_pos hfin).2 hne
  have h2 : (clsPlus Q '' cls Q L).ncard ≤ 2 :=
    (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ((Set.ncard_insert_le _ _).trans (by simp))
  omega

/-- **$O^-(V)$** (O'Meara 1963, §43A, p. 100, used in §82C, p. 223): the isometries of $V$ of determinant $-1$. -/
@[kb "omeara1963" "§82C, p. 223 (O⁻(V), isometries of determinant −1)"]
def orthMinus : Set (V ≃ₗ[F] V) := {σ | σ ∈ orth Q ∧ LinearEquiv.det σ = -1}

/-- **$O^-(L) = O(L) \cap O^-(V)$** (O'Meara 1963, §82C, p. 223). -/
@[kb "omeara1963" "§82C, p. 223 (O⁻(L) = O(L) ∩ O⁻(V))"]
def orthLatMinus (L : Submodule R V) : Set (V ≃ₗ[F] V) := (orthLat Q L : Set (V ≃ₗ[F] V)) ∩ orthMinus Q

/-- **$O(L) = O^+(L) \cup O^-(L)$** (O'Meara 1963, §82C, p. 223), for a lattice in a regular space $V$. -/
@[kb "omeara1963" "§82C, p. 223 (O(L) = O⁺(L) ∪ O⁻(L))"]
theorem orthLat_eq_union [FiniteDimensional F V] (hV : (QuadraticMap.associated Q).Nondegenerate)
    (L : Submodule R V) :
    (orthLat Q L : Set (V ≃ₗ[F] V)) = (orthLatPlus Q L : Set (V ≃ₗ[F] V)) ∪ orthLatMinus Q L := by
  ext σ
  constructor
  · intro h
    rcases det_orth_eq Q hV h.1 with hd | hd
    · exact Or.inl ⟨h, h.1, hd⟩
    · exact Or.inr ⟨h, h.1, hd⟩
  · rintro (h | h)
    · exact h.1
    · exact h.1

/-- **$O^+(L) \cap O^-(L) = \emptyset$** (O'Meara 1963, §82C, p. 223). -/
@[kb "omeara1963" "§82C, p. 223 (O⁺(L) ∩ O⁻(L) = ∅)"]
theorem disjoint_orthLatPlus_orthLatMinus (L : Submodule R V) :
    Disjoint (orthLatPlus Q L : Set (V ≃ₗ[F] V)) (orthLatMinus Q L) := by
  rw [Set.disjoint_left]
  rintro σ ⟨-, -, h1⟩ ⟨-, -, h2⟩
  have h1' : LinearEquiv.det σ = 1 := h1
  exact neg_one_ne_one_units (F := F) (h2.symm.trans h1')

/-- **The index is $2$ when a reflexion is a unit** (O'Meara 1963, §82C, p. 223): if some symmetry $\tau_u$ of the
regular space $V$ lies in $O(L)$ then $(O(L) : O^+(L)) = 2$. (O'Meara adds "otherwise it is $1$", to be seen later;
that converse is not formalized here.) -/
@[kb "omeara1963" "§82C, p. 223 (index 2 when some reflexion is a unit of L)"]
theorem relIndex_eq_two_of_symmetry_mem [FiniteDimensional F V] (hV : (QuadraticMap.associated Q).Nondegenerate)
    {L : Submodule R V} {u : V} (hu : Q u ≠ 0) (h : symmetry Q u hu ∈ orthLat Q L) :
    (orthLatPlus Q L).relIndex (orthLat Q L) = 2 :=
  (relIndex_eq_two_iff_exists Q hV L).2 ⟨_, h, det_symmetry Q hu⟩

/-- **$Q(FL) = F^2Q(L)$** (O'Meara 1963, §82E, p. 227): the values of $Q$ on $FL$ are the $\alpha^2Q(x)$ with
$\alpha \in F$, $x \in L$. (The exponent is garbled in the machine-read text; reconstructed from
$Q(\varepsilon^{-1}x) = \varepsilon^{-2}Q(x)$.) -/
@[kb "omeara1963" "§82E, p. 227 (Q(FL) = F²Q(L))"]
theorem image_span_eq (L : Submodule R V) :
    Q '' (span F (L : Set V) : Set V) = {c | ∃ α : F, ∃ x ∈ L, c = α ^ 2 * Q x} := by
  ext c
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨d, hd, hdv⟩ := exists_smul_mem_of_mem_span (F := F) hv
    have hd' : algebraMap R F d ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hd)
    refine ⟨(algebraMap R F d)⁻¹, _, hdv, ?_⟩
    rw [Q_rsmul, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hd', one_pow, one_mul]
  · rintro ⟨α, x, hx, rfl⟩
    exact ⟨α • x, Submodule.smul_mem _ α (subset_span hx), Q_smul Q α x⟩

/-- **$\mathfrak sL$, $\mathfrak nL$, $B(FL, FL)$, $Q(FL)$ vanish together** (O'Meara 1963, §82E, p. 227): the
following are equivalent: $\mathfrak sL = 0$; $\mathfrak nL = 0$; $B(FL, FL) = 0$; $Q(FL) = 0$. -/
@[kb "omeara1963" "§82E, p. 227 (sL, nL, B(FL,FL), Q(FL) are 0 if one of them is)"]
theorem scale_normIdeal_tfae (L : Submodule R V) :
    List.TFAE [scale Q L = ⊥, normIdeal Q L = ⊥,
      ∀ x ∈ span F (L : Set V), ∀ y ∈ span F (L : Set V), bil Q x y = 0,
      ∀ x ∈ span F (L : Set V), Q x = 0] := by
  have hne : ∀ d : R, d ≠ 0 → algebraMap R F d ≠ 0 := fun d hd =>
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hd)
  tfae_have 2 → 1 := by
    intro h
    rw [normIdeal, Submodule.span_eq_bot] at h
    rw [scale, Submodule.span_eq_bot]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    rw [bil_eq_half, h _ ⟨_, L.add_mem hx hy, rfl⟩, h _ ⟨_, hx, rfl⟩, h _ ⟨_, hy, rfl⟩]
    simp
  tfae_have 1 → 3 := by
    intro h v hv w hw
    rw [scale, Submodule.span_eq_bot] at h
    obtain ⟨d, hd, hdv⟩ := exists_smul_mem_of_mem_span (F := F) hv
    obtain ⟨d', hd', hdw⟩ := exists_smul_mem_of_mem_span (F := F) hw
    have := h _ ⟨_, hdv, _, hdw, rfl⟩
    rw [bil_rsmul_left, bil_rsmul_right] at this
    rcases mul_eq_zero.1 this with h1 | h1
    · exact absurd h1 (hne d hd)
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · exact absurd h2 (hne d' hd')
      · exact h2
  tfae_have 3 → 4 := fun h x hx => by rw [← bil_self]; exact h x hx x hx
  tfae_have 4 → 2 := by
    intro h
    rw [normIdeal, Submodule.span_eq_bot]
    rintro _ ⟨x, hx, rfl⟩
    exact h x (subset_span hx)
  tfae_finish

/-- **Maximal lattice on $V$** (O'Meara 1963, §82H, p. 234): $L$ is $\mathfrak a$-maximal on $V$ for some fractional
ideal $\mathfrak a$ (a finitely generated non-zero $R$-submodule of $F$). -/
@[kb "omeara1963" "§82H, p. 234 (L is maximal on V)"]
def IsMaximalOn (L : Submodule R V) : Prop :=
  ∃ a : Submodule R F, a.FG ∧ a ≠ ⊥ ∧ IsMaximal Q a L

end Classes

/-! ### The matrix of a free lattice, change of base, conventions for $0$, splitting (§82B, §82D, §82E) -/

section FreeMatrix

variable {R : Type*} [CommRing R] [IsDomain R] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **$L$ has the matrix $N$**, $L \cong N$ (O'Meara 1963, §82B, p. 221): some base $x_1, \dots, x_n$ of $L$ has
$(B(x_i, x_j)) = N$. -/
@[kb "omeara1963" "§82B, p. 221 (L has the matrix N, L ≅ N)"]
def HasMatrix (L : Submodule R V) {ι : Type*} (N : Matrix ι ι F) : Prop :=
  ∃ b : Basis ι R L, gram Q (fun i => (b i : V)) = N

/-- **Change of base** (O'Meara 1963, §82B, p. 221): the matrices of a free lattice in two bases are integrally
equivalent. -/
@[kb "omeara1963" "§82B, p. 221 (a change of base leads from N to a matrix N' in cls N)"]
theorem matIntEquiv_gram_of_basis {L : Submodule R V} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b b' : Basis ι R L) :
    MatIntEquiv R (gram Q fun i => (b' i : V)) (gram Q fun i => (b i : V)) :=
  (isometricLat_iff_matIntEquiv Q Q b b').1 ⟨LinearEquiv.refl R L, fun _ => rfl⟩

/-- **Every matrix of $\operatorname{cls} N$ is a matrix of $L$** (O'Meara 1963, §82B, p. 221): if $L$ has the matrix
$N$ in the base $b$ and $M \cong N$, then $L$ has the matrix $M$ in another base. -/
@[kb "omeara1963" "§82B, p. 221 (every matrix of cls N is obtained by a change of base)"]
theorem hasMatrix_of_matIntEquiv {L : Submodule R V} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι R L) {M : Matrix ι ι F} (hM : MatIntEquiv R M (gram Q fun i => (b i : V))) :
    HasMatrix Q L M := by
  obtain ⟨T, hT, hG⟩ := hM
  let A : L ≃ₗ[R] L := Matrix.toLinearEquiv b Tᵀ (by rwa [Matrix.det_transpose])
  let b'' : Basis ι R L := b.map A
  have hb'' : ∀ i, (b'' i : V) = ∑ j, T i j • (b j : V) := by
    intro i
    simp [b'', A, Matrix.toLinearEquiv, Matrix.toLin_self]
  refine ⟨b'', ?_⟩
  rw [hG]
  have : (fun i => (b'' i : V)) = fun i => ∑ j, T i j • (b j : V) := funext hb''
  rw [this, gram_comb]

/-- **The convention $d\,0 = 1$** (O'Meara 1963, §82B, p. 222): the zero lattice has discriminant $1$ (the
determinant of the empty matrix). -/
@[kb "omeara1963" "§82B, p. 222 (dL = 1 for L = 0)"]
theorem hasDisc_bot : HasDisc Q (⊥ : Submodule R V) 1 := by
  have : IsEmpty (Fin (finrank R (⊥ : Submodule R V))) := by rw [finrank_bot]; infer_instance
  exact ⟨Basis.empty _, Matrix.det_isEmpty⟩

/-- **The convention $\mathfrak v\,0 = \mathfrak o$** (O'Meara 1963, §82E, p. 229). -/
@[kb "omeara1963" "§82E, p. 229 (v0 = o)"]
theorem volume_bot : volume Q (⊥ : Submodule R V) = 1 := by
  have : IsEmpty (Fin (finrank R (⊥ : Submodule R V))) := by rw [finrank_bot]; infer_instance
  have hset : {d | ∃ x : Fin (finrank R (⊥ : Submodule R V)) → V, (∀ i, x i ∈ (⊥ : Submodule R V)) ∧
      (gram Q x).det = d} = {1} := by
    ext d
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Matrix.det_isEmpty]
    exact ⟨fun ⟨_, _, h⟩ => h.symm, fun h => ⟨isEmptyElim, isEmptyElim, h.symm⟩⟩
  rw [volume, hset, ← Submodule.one_eq_span]

/-- **$K$ splits $L$** ($K$ is a component of $L$; O'Meara 1963, §82D, p. 224): $L = K \perp J$ for some sublattice
$J$ of $L$. -/
@[kb "omeara1963" "§82D, p. 224 (K splits L, K is a component of L)"]
def Splits (K L : Submodule R V) : Prop :=
  ∃ J : Submodule R V, IsOrthSum Q L K J

/-- **Orthogonal base of a lattice** (O'Meara 1963, §82D, p. 225): a base $x_1, \dots, x_n$ of $L$ with
$B(x_i, x_j) = 0$ for $i \ne j$, i.e. $L = \langle Q(x_1) \rangle \perp \cdots \perp \langle Q(x_n) \rangle$. -/
@[kb "omeara1963" "§82D, p. 225 (orthogonal base of a lattice)"]
def IsOrthBase {L : Submodule R V} {ι : Type*} (b : Basis ι R L) : Prop :=
  ∀ i j, i ≠ j → bil Q (b i : V) (b j : V) = 0

end FreeMatrix

end QuadFormsKB.OMeara
