import QuadFormsKB.Literature.Cassels.Ch12.Tessellation

/-!
# Cassels, Chapter 12, §7: Corollary to Theorem 7.7 for every $n$

Cassels, *Rational Quadratic Forms* (1978), Ch. 12, §7, Corollary to Theorem 7.7, p. 279: *every integral unimodular
$T$ is a product $T = S_1 \cdots S_k D$ of elements $S_i$ of $\Sigma'$ (the $S$ for which $\mathcal R$ and $S\mathcal R$
are neighbours) and a diagonal matrix $D$ with entries $\pm 1$.* The named statement is
`Reduction.Tessellation.NeighbourGeneration n` (`Tessellation.lean`), proved there for $n = 2$; here it is proved for
every $n$ (`neighbourGeneration`), following Cassels' argument:

*Proof (Cassels).* Join an inner point $x$ of $\mathcal R$ to an inner point $y$ of $T\mathcal R$ by a segment. The
segment is compact, so it meets only finitely many $L\mathcal R$ (Theorem 7.6), and $y$ may be moved inside $T\mathcal R$
so that the segment avoids the finitely many sets $L_1\mathcal R \cap L_2\mathcal R$ of codimension $\ge 2$. Then
consecutive sets $L\mathcal R$ met by the segment are neighbours, and the chain of neighbours from $\mathcal R$ to
$T\mathcal R$ gives the product.

The formal proof:
* `finrank_symSub`: the forms (symmetric matrices) are a space of dimension $N = n(n+1)/2$;
* `exists_mem_symInterior`: a convex set of forms whose affine span has dimension $N$ has an inner point (relative to
  the forms); with Theorem 7.4 (`thm_7_4`) two different sets $L_1\mathcal R \ne L_2\mathcal R$ meet in a set of
  dimension $\le N - 1$, hence (if not neighbours) $\le N - 2$ (`finrank_inter_add_two_le`);
* `exists_avoid`: a nonempty open set of forms is not covered by finitely many affine subspaces of dimension $< N$
  (they are closed with empty interior); applied to the cones $\mathrm{span}(\{x\} \cup (L_1\mathcal R \cap
  L_2\mathcal R))$ of dimension $\le N - 1$ this moves $y$;
* `reachable_of_segment`: the parameter interval $[0, 1]$ is connected and is covered by the finitely many closed
  sets $\{t : \gamma(t) \in L\mathcal R\}$; splitting them into those reachable from $\mathcal R$ by a chain of
  neighbours and the others, a common point would be a point of two sets that are neither equal nor neighbours,
  which the choice of $y$ excludes;
* `neighbourGeneration`: a chain of neighbours $\mathcal R = L_0\mathcal R, \dots, L_k\mathcal R = T\mathcal R$ gives
  $L_{i+1}L_i^{-1} \in \Sigma'$ (`areNeighbours_mul_iff`), and $TL_k^{-1}$ is diagonal with entries $\pm1$ (Theorem 7.2),
  which is moved to the right since $\Sigma'$ is stable under conjugation by such matrices.

Order of composition as in `Sec7.lean`: `img (S * T)` is the image of `img S` under the substitution $T$.
-/

open Matrix

namespace QuadFormsKB.Reduction

namespace Tessellation

namespace NeighbourGen

variable {n : ℕ}

/-! ### The space of forms and its dimension -/

/-- Helper: the subspace of symmetric real $n \times n$ matrices (the space of forms, Cassels'
$\mathbb R^{n(n+1)/2}$, Ch. 12, §5). -/
def symSub (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := {F | F.IsSymm}
  add_mem' ha hb := ha.add hb
  zero_mem' := isSymm_zero
  smul_mem' c _ hF := hF.smul c

/-- Helper: membership in `symSub`. -/
theorem mem_symSub {F : Matrix (Fin n) (Fin n) ℝ} : F ∈ symSub n ↔ F.IsSymm := Iff.rfl

/-- Helper: a form is determined by its values on unordered pairs of indices: the linear equivalence between
symmetric matrices and functions on `Sym2 (Fin n)`. -/
noncomputable def symEquiv (n : ℕ) : symSub n ≃ₗ[ℝ] (Sym2 (Fin n) → ℝ) where
  toFun F := Sym2.lift ⟨fun i j => F.1 i j, fun i j => F.2.apply j i⟩
  invFun g := ⟨Matrix.of fun i j => g s(i, j), by
    ext i j; simp [Sym2.eq_swap]⟩
  left_inv F := by ext i j; simp
  right_inv g := by funext z; induction z using Sym2.ind; simp
  map_add' F G := by funext z; induction z using Sym2.ind; simp
  map_smul' c F := by funext z; induction z using Sym2.ind; simp

/-- **The space of forms has dimension $n(n+1)/2$** (Cassels, Ch. 12, §5, p. 270: a form is a point of
$\mathbb R^{n(n+1)/2}$). -/
@[kb "cassels1978" "Ch. 12, §5, p. 270 (the forms are the points of ℝ^{n(n+1)/2})"]
theorem finrank_symSub (n : ℕ) : Module.finrank ℝ (symSub n) = n * (n + 1) / 2 := by
  rw [(symEquiv n).finrank_eq, Module.finrank_fintype_fun_eq_card, ← Finset.card_univ, ← Finset.sym2_univ,
    Finset.card_sym2, Finset.card_univ, Fintype.card_fin, Nat.choose_two_right, Nat.add_sub_cancel, mul_comm]

/-- Helper: a positive definite real matrix is symmetric. -/
theorem isSymm_of_posDef {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosDef) : F.IsSymm := by
  have h := hF.isHermitian
  unfold Matrix.IsHermitian at h
  rwa [conjTranspose_eq_transpose_of_trivial] at h

/-- Helper: $\mathcal R$ is `img 1`. -/
theorem img_one_eq' : img (1 : GL (Fin n) ℤ) = {G | IsMinkowskiReduced G} := by
  ext G
  constructor
  · rintro ⟨H, hH, rfl⟩
    rw [Units.val_one, act_one]; exact hH
  · intro h
    exact ⟨G, h, by rw [Units.val_one, act_one]⟩

/-- Helper: every set `img T` consists of positive definite forms. -/
theorem posDef_of_mem_img {T : GL (Fin n) ℤ} {F : Matrix (Fin n) (Fin n) ℝ} (h : F ∈ img T) : F.PosDef :=
  ((mem_img_iff7 T F).1 h).2

/-- Helper: every set `img T` lies in the space of forms. -/
theorem img_subset_symSub (T : GL (Fin n) ℤ) : img T ⊆ symSub n := fun _ h => isSymm_of_posDef (posDef_of_mem_img h)

/-- Helper: the direction of the affine span of a set of forms consists of forms. -/
theorem direction_le_symSub {S : Set (Matrix (Fin n) (Fin n) ℝ)} (hS : S ⊆ symSub n) :
    (affineSpan ℝ S).direction ≤ symSub n := by
  rw [direction_affineSpan, vectorSpan_def, Submodule.span_le]
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact (symSub n).sub_mem (hS ha) (hS hb)

/-- Helper: the dimension of the affine span of a set of forms is at most $N$. -/
theorem finrank_direction_le {S : Set (Matrix (Fin n) (Fin n) ℝ)} (hS : S ⊆ symSub n) :
    Module.finrank ℝ (affineSpan ℝ S).direction ≤ Module.finrank ℝ (symSub n) :=
  Submodule.finrank_mono (direction_le_symSub hS)

/-- Helper: adding one point raises the dimension of the affine span by at most one. -/
theorem finrank_direction_insert_le (x : Matrix (Fin n) (Fin n) ℝ) {S : Set (Matrix (Fin n) (Fin n) ℝ)}
    (hS : S.Nonempty) :
    Module.finrank ℝ (affineSpan ℝ (insert x S)).direction ≤ Module.finrank ℝ (affineSpan ℝ S).direction + 1 := by
  obtain ⟨p, hp⟩ := hS
  rw [← affineSpan_insert_affineSpan, AffineSubspace.direction_affineSpan_insert (subset_affineSpan ℝ S hp)]
  refine (Submodule.finrank_add_le_finrank_add_finrank _ _).trans ?_
  rw [add_comm]
  gcongr
  exact (finrank_span_le_card ({x -ᵥ p} : Set (Matrix (Fin n) (Fin n) ℝ))).trans (by simp)

/-! ### Inner points and the avoidance of small affine subspaces (with the sup norm on matrices) -/

section Normed

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- **A convex set of forms of full dimension has an inner point** (relative to the forms): if $S$ is a convex set of
symmetric matrices whose affine span has dimension $N = \dim$ (forms), some $F \in S$ has a neighbourhood $U$ whose
symmetric members all lie in $S$ (`symInterior`). -/
theorem exists_mem_symInterior {S : Set (Matrix (Fin n) (Fin n) ℝ)} (hS : S ⊆ symSub n) (hconv : Convex ℝ S)
    (hne : S.Nonempty) (hdim : Module.finrank ℝ (affineSpan ℝ S).direction = Module.finrank ℝ (symSub n)) :
    ∃ F, F ∈ symInterior S := by
  set ι := (symSub n).subtype with hι
  set S' : Set (symSub n) := ι ⁻¹' S with hS'
  have himg : ι '' S' = S := by
    rw [hS', Set.image_preimage_eq_inter_range]
    ext F
    exact ⟨fun h => h.1, fun h => ⟨h, ⟨F, hS h⟩, rfl⟩⟩
  have hconv' : Convex ℝ S' := hconv.linear_preimage ι
  have hne' : S'.Nonempty := by
    obtain ⟨F, hF⟩ := hne
    exact ⟨⟨F, hS hF⟩, hF⟩
  have hdir : Module.finrank ℝ (affineSpan ℝ S').direction = Module.finrank ℝ (symSub n) := by
    have h1 : (affineSpan ℝ (ι '' S')).direction = (affineSpan ℝ S').direction.map ι := by
      have : (ι '' S') = ι.toAffineMap '' S' := rfl
      rw [this, ← AffineSubspace.map_span, AffineSubspace.map_direction]
      rfl
    have h3 := Submodule.finrank_map_subtype_eq (symSub n) (affineSpan ℝ S').direction
    rw [← h1, himg, hdim] at h3
    exact h3.symm
  have htop : affineSpan ℝ S' = ⊤ := by
    have hd : (affineSpan ℝ S').direction = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [hdir])
    exact (AffineSubspace.direction_eq_top_iff_of_nonempty (hne'.mono (subset_affineSpan ℝ S'))).1 hd
  obtain ⟨p, hp⟩ := (hconv'.interior_nonempty_iff_affineSpan_eq_top).2 htop
  obtain ⟨U, hU, hUeq⟩ := isOpen_induced_iff.1 (isOpen_interior (s := S'))
  refine ⟨p.1, p.2, U, hU, ?_, ?_⟩
  · have : p ∈ Subtype.val ⁻¹' U := by rw [hUeq]; exact hp
    exact this
  · rintro G ⟨hGU, hGs⟩
    have : (⟨G, hGs⟩ : symSub n) ∈ interior S' := by
      rw [← hUeq]; exact hGU
    exact (interior_subset this : (⟨G, hGs⟩ : symSub n) ∈ S')

/-- Helper: a point of `symInterior S` lies in `S`. -/
theorem mem_of_mem_symInterior {S : Set (Matrix (Fin n) (Fin n) ℝ)} {F : Matrix (Fin n) (Fin n) ℝ}
    (h : F ∈ symInterior S) : F ∈ S := by
  obtain ⟨hs, U, -, hFU, hUS⟩ := h
  exact hUS ⟨hFU, hs⟩

/-- Helper: `symInterior` is monotone. -/
theorem symInterior_mono {S S' : Set (Matrix (Fin n) (Fin n) ℝ)} (h : S ⊆ S') : symInterior S ⊆ symInterior S' := by
  rintro F ⟨hs, U, hU, hFU, hUS⟩
  exact ⟨hs, U, hU, hFU, hUS.trans h⟩

/-- **Two different sets $L_1\mathcal R \ne L_2\mathcal R$ meet in a set of dimension $< N$** (Cassels, Ch. 12, §7,
p. 279, from Theorem 7.4): a full-dimensional intersection would contain an inner point of $L_1\mathcal R$. -/
@[kb "cassels1978" "Ch. 12, §7, p. 279 (distinct L₁𝓡, L₂𝓡 meet in dimension < n(n+1)/2)"]
theorem img_eq_of_finrank_eq {X Y : GL (Fin n) ℤ} (hne : (img X ∩ img Y).Nonempty)
    (hdim : Module.finrank ℝ (affineSpan ℝ (img X ∩ img Y)).direction = Module.finrank ℝ (symSub n)) :
    img X = img Y := by
  obtain ⟨F, hF⟩ := exists_mem_symInterior (Set.inter_subset_left.trans (img_subset_symSub X))
    (convex_img_inter X Y) hne hdim
  exact thm_7_4 (symInterior_mono Set.inter_subset_left hF) (mem_of_mem_symInterior hF).2

/-- **Different, meeting, non-neighbouring sets meet in codimension $\ge 2$** (Cassels, Ch. 12, §7, p. 279). -/
@[kb "cassels1978" "Ch. 12, §7, proof of Cor. to Thm. 7.7, p. 279 (codimension ≥ 2 unless neighbours)"]
theorem finrank_inter_add_two_le {X Y : GL (Fin n) ℤ} (hXY : img X ≠ img Y) (hne : (img X ∩ img Y).Nonempty)
    (hnb : ¬ AreNeighbours X Y) :
    Module.finrank ℝ (affineSpan ℝ (img X ∩ img Y)).direction + 2 ≤ Module.finrank ℝ (symSub n) := by
  have h1 := finrank_direction_le (Set.inter_subset_left.trans (img_subset_symSub X) : img X ∩ img Y ⊆ symSub n)
  have h2 : Module.finrank ℝ (affineSpan ℝ (img X ∩ img Y)).direction ≠ Module.finrank ℝ (symSub n) :=
    fun h => hXY (img_eq_of_finrank_eq hne h)
  have h3 : Module.finrank ℝ (affineSpan ℝ (img X ∩ img Y)).direction + 1 ≠ Module.finrank ℝ (symSub n) := by
    rw [finrank_symSub]; exact fun h => hnb ⟨hne, h⟩
  omega

/-- **A nonempty open set of forms avoids finitely many small affine subspaces**: for a finite set $\mathcal H$ of
affine subspaces of $M_n(\mathbb R)$, each of dimension $< N$, and an open set $U$ containing a form, some form in $U$
lies in none of them (in the space of forms they are closed with empty interior). -/
theorem exists_avoid (𝓗 : Finset (AffineSubspace ℝ (Matrix (Fin n) (Fin n) ℝ)))
    (h𝓗 : ∀ H ∈ 𝓗, Module.finrank ℝ H.direction < Module.finrank ℝ (symSub n))
    {U : Set (Matrix (Fin n) (Fin n) ℝ)} (hU : IsOpen U) (hne : (U ∩ symSub n).Nonempty) :
    ∃ y ∈ U, y ∈ symSub n ∧ ∀ H ∈ 𝓗, y ∉ H := by
  classical
  set ι := (symSub n).subtype with hι
  have hcont : Continuous ι := continuous_subtype_val
  -- each `ι ⁻¹' H` is closed with empty interior
  have hA : ∀ H ∈ 𝓗, IsClosed (ι ⁻¹' (H : Set _)) ∧ interior (ι ⁻¹' (H : Set _)) = ∅ := by
    intro H hH
    refine ⟨(AffineSubspace.closed_of_finiteDimensional H).preimage hcont, ?_⟩
    by_contra hint
    have hconv : Convex ℝ (ι ⁻¹' (H : Set _)) := H.convex.linear_preimage ι
    have htop := (hconv.interior_nonempty_iff_affineSpan_eq_top).1 (Set.nonempty_iff_ne_empty.2 hint)
    have hall : ∀ p : symSub n, (p : Matrix (Fin n) (Fin n) ℝ) ∈ H := by
      intro p
      have hp : p ∈ affineSpan ℝ (ι ⁻¹' (H : Set _)) := by rw [htop]; trivial
      have hmap : ι.toAffineMap p ∈ (affineSpan ℝ (ι ⁻¹' (H : Set _))).map ι.toAffineMap :=
        AffineSubspace.mem_map_of_mem _ hp
      rw [AffineSubspace.map_span] at hmap
      exact (affineSpan_le.2 (Set.image_preimage_subset _ _)) hmap
    have hle : symSub n ≤ H.direction := by
      intro v hv
      have := AffineSubspace.vsub_mem_direction (hall ⟨v, hv⟩) (hall 0)
      simpa using this
    exact absurd (Submodule.finrank_mono hle) (not_le.2 (h𝓗 H hH))
  -- the union is closed with empty interior
  have hunion : ∀ s ⊆ 𝓗, IsClosed (⋃ H ∈ s, ι ⁻¹' (H : Set _)) ∧
      interior (⋃ H ∈ s, ι ⁻¹' (H : Set _)) = ∅ := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simp
    | insert a s ha ih =>
      intro hs
      obtain ⟨ih1, ih2⟩ := ih ((Finset.subset_insert a s).trans hs)
      obtain ⟨ha1, ha2⟩ := hA a (hs (Finset.mem_insert_self a s))
      have heq : (⋃ H ∈ insert a s, ι ⁻¹' (H : Set _)) = (⋃ H ∈ s, ι ⁻¹' (H : Set _)) ∪ ι ⁻¹' (a : Set _) := by
        rw [Finset.set_biUnion_insert, Set.union_comm]
      rw [heq]
      exact ⟨ih1.union ha1, by rw [interior_union_isClosed_of_interior_empty ih1 ha2, ih2]⟩
  obtain ⟨-, hint⟩ := hunion 𝓗 le_rfl
  by_contra hcon
  push Not at hcon
  have hsub : ι ⁻¹' U ⊆ ⋃ H ∈ 𝓗, ι ⁻¹' (H : Set _) := by
    intro p hp
    obtain ⟨H, hH, hpH⟩ := hcon p hp p.2
    exact Set.mem_biUnion hH hpH
  have hopen : IsOpen (ι ⁻¹' U) := hU.preimage hcont
  have : ι ⁻¹' U ⊆ interior (⋃ H ∈ 𝓗, ι ⁻¹' (H : Set _)) := interior_maximal hsub hopen
  rw [hint] at this
  obtain ⟨F, hFU, hFs⟩ := hne
  exact this (show (⟨F, hFs⟩ : symSub n) ∈ ι ⁻¹' U from hFU)

end Normed

/-! ### Neighbours, chains and products -/

/-- Helper: neighbourhood depends only on the sets `img`. -/
theorem areNeighbours_congr {X X' Y Y' : GL (Fin n) ℤ} (hX : img X = img X') (hY : img Y = img Y') :
    AreNeighbours X Y ↔ AreNeighbours X' Y' := by
  unfold AreNeighbours; rw [hX, hY]

/-- Helper: a chain of neighbours from $\mathcal R$ to $X\mathcal R$ writes $X$ as a product of elements of $\Sigma'$. -/
theorem exists_prod_of_reflTransGen {X : GL (Fin n) ℤ} (h : Relation.ReflTransGen AreNeighbours 1 X) :
    ∃ l : List (GL (Fin n) ℤ), (∀ S ∈ l, S ∈ sigmaPrime n) ∧ X = l.prod := by
  induction h with
  | refl => exact ⟨[], by simp, by simp⟩
  | @tail W Z _ hWZ ih =>
    obtain ⟨l, hl, rfl⟩ := ih
    refine ⟨(Z * l.prod⁻¹) :: l, ?_, by simp⟩
    intro S hS
    rcases List.mem_cons.1 hS with rfl | hS
    · show AreNeighbours 1 (Z * l.prod⁻¹)
      rw [areNeighbours_comm, ← areNeighbours_mul_iff (Z * l.prod⁻¹) l.prod, inv_mul_cancel_right,
        areNeighbours_comm]
      exact hWZ
    · exact hl S hS

/-- Helper: $\Sigma'$ is stable under conjugation by a diagonal matrix $D$ with entries $\pm 1$ ($D\mathcal R = \mathcal R$). -/
theorem conj_mem_sigmaPrime {D S : GL (Fin n) ℤ} (hD : IsSignDiagonal D) (hS : S ∈ sigmaPrime n) :
    D * S * D⁻¹ ∈ sigmaPrime n := by
  show AreNeighbours 1 (D * S * D⁻¹)
  have h1 : img D⁻¹ = img 1 := img_eq_of_signDiag7 hD.inv7 (mul_one _).symm
  have h2 : img (D * S) = img S := img_eq_of_signDiag7 hD rfl
  rw [areNeighbours_comm, areNeighbours_congr rfl h1.symm, areNeighbours_mul_iff,
    areNeighbours_congr h2 rfl, areNeighbours_comm]
  exact hS

/-- Helper: moving a diagonal matrix $D$ with entries $\pm 1$ through a product. -/
theorem mul_prod_eq (D : GL (Fin n) ℤ) (l : List (GL (Fin n) ℤ)) :
    D * l.prod = (l.map fun S => D * S * D⁻¹).prod * D := by
  induction l with
  | nil => simp
  | cons S l ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons, mul_assoc, ← mul_assoc D, ← ih]
    group

/-! ### The segment argument -/

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
/-- **The segment argument** (Cassels, Ch. 12, §7, proof of the Corollary to Theorem 7.7, p. 279): for every
unimodular $T$ there is a chain of neighbours from $\mathcal R$ to a set $X\mathcal R = T\mathcal R$. -/
theorem reachable (T : GL (Fin n) ℤ) :
    ∃ X, Relation.ReflTransGen AreNeighbours 1 X ∧ img X = img T := by
  classical
  set C : Set (GL (Fin n) ℤ) := {Y | ∃ X, Relation.ReflTransGen AreNeighbours 1 X ∧ img X = img Y} with hC
  -- the inner point x₀ of 𝓡
  obtain ⟨x₀, hx₀⟩ := exists_isStrictlyReduced n
  have hx₀int : x₀ ∈ symInterior (img 1) := by
    obtain ⟨U, hU, hUeq⟩ := lemma_5_3_open (n := n)
    have hx₀U : x₀ ∈ U ∩ {F | F.IsSymm} := by rw [← hUeq]; exact hx₀
    refine ⟨hx₀U.2, U, hU, hx₀U.1, ?_⟩
    intro G hG
    rw [← hUeq] at hG
    rw [img_one_eq']; exact hG.1
  have hx₀1 : x₀ ∈ img 1 := mem_of_mem_symInterior hx₀int
  have hx₀pd : x₀.PosDef := posDef_of_mem_img hx₀1
  -- the inner point y₀ of T𝓡
  set y₀ := act T.val x₀ with hy₀
  obtain ⟨U₀, hU₀, hx₀U₀, hU₀S⟩ := hx₀int.2
  have hy₀U : y₀ ∈ (act T⁻¹.val) ⁻¹' U₀ := by
    show act T⁻¹.val (act T.val x₀) ∈ U₀; rw [act_inv_act7]; exact hx₀U₀
  have hU₀' : ∀ G ∈ (act T⁻¹.val) ⁻¹' U₀, G.IsSymm → G ∈ img T := by
    intro G hG hGs
    have h : act T⁻¹.val G ∈ img 1 := hU₀S ⟨hG, isSymm_act7 _ hGs⟩
    rw [img_one_eq'] at h
    exact (mem_img_iff_red7 T G).2 h
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hU₀.preimage (continuous_act7 T⁻¹.val)) y₀ hy₀U
  have hy₀s : y₀.IsSymm := isSymm_act7 _ hx₀int.1
  -- the compact set B of admissible endpoints and the compact set K₀ swept by the segments
  set B := Metric.closedBall y₀ (ε / 2) ∩ {F : Matrix (Fin n) (Fin n) ℝ | F.IsSymm} with hB
  have hBT : B ⊆ img T := by
    rintro G ⟨hG, hGs⟩
    refine hU₀' G (hball ?_) hGs
    rw [Metric.mem_closedBall] at hG
    rw [Metric.mem_ball]; linarith
  have hBc : IsCompact B := (isCompact_closedBall y₀ (ε / 2)).inter_right isClosed_isSymm7
  set γ₂ : ℝ × Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ := fun p => x₀ + p.1 • (p.2 - x₀) with hγ₂
  have hγ₂c : Continuous γ₂ := continuous_const.add (continuous_fst.smul (continuous_snd.sub continuous_const))
  set K₀ := γ₂ '' (Set.Icc (0 : ℝ) 1 ×ˢ B) with hK₀
  have hK₀c : IsCompact K₀ := (isCompact_Icc.prod hBc).image hγ₂c
  have hpd_seg : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ z, z.PosDef → (x₀ + t • (z - x₀)).PosDef := by
    intro t ht z hz
    have h := thm_5_1_convex (n := n) hx₀pd hz (sub_nonneg.2 ht.2) ht.1 (by ring)
    have e : (1 - t) • x₀ + t • z = x₀ + t • (z - x₀) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [← e]; exact h
  have hK₀P : ∀ F ∈ K₀, F.PosDef := by
    rintro _ ⟨⟨t, z⟩, ⟨ht, hz⟩, rfl⟩
    exact hpd_seg t ht z (posDef_of_mem_img (hBT hz))
  -- the finitely many sets met, and the bad pairs
  set 𝒳 := {X : GL (Fin n) ℤ | (img X ∩ K₀).Nonempty} with h𝒳
  have h𝒳f : 𝒳.Finite := thm_7_6 hK₀c hK₀P
  set P := {p : GL (Fin n) ℤ × GL (Fin n) ℤ | p.1 ∈ 𝒳 ∧ p.2 ∈ 𝒳 ∧ img p.1 ≠ img p.2 ∧
    (img p.1 ∩ img p.2).Nonempty ∧ ¬ AreNeighbours p.1 p.2} with hP
  have hPf : P.Finite := (h𝒳f.prod h𝒳f).subset fun p hp => ⟨hp.1, hp.2.1⟩
  set cone : GL (Fin n) ℤ × GL (Fin n) ℤ → AffineSubspace ℝ (Matrix (Fin n) (Fin n) ℝ) :=
    fun p => affineSpan ℝ (insert x₀ (img p.1 ∩ img p.2)) with hcone
  set 𝓗 := (hPf.image cone).toFinset with h𝓗
  have h𝓗dim : ∀ H ∈ 𝓗, Module.finrank ℝ H.direction < Module.finrank ℝ (symSub n) := by
    intro H hH
    rw [Set.Finite.mem_toFinset] at hH
    obtain ⟨p, hp, rfl⟩ := hH
    have h1 := finrank_inter_add_two_le hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2
    have h2 := finrank_direction_insert_le x₀ hp.2.2.2.1
    exact lt_of_le_of_lt h2 (by omega)
  -- the endpoint y
  obtain ⟨y, hyU, hys, hyH⟩ := exists_avoid 𝓗 h𝓗dim (U := Metric.ball y₀ (ε / 2)) Metric.isOpen_ball
    ⟨y₀, Metric.mem_ball_self (by linarith), hy₀s⟩
  have hyB : y ∈ B := ⟨Metric.ball_subset_closedBall hyU, hys⟩
  have hyT : y ∈ img T := hBT hyB
  set γ : ℝ → Matrix (Fin n) (Fin n) ℝ := fun t => x₀ + t • (y - x₀) with hγ
  have hγc : Continuous γ := continuous_const.add (continuous_id.smul continuous_const)
  have hγK : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ K₀ := fun t ht => ⟨(t, y), ⟨ht, hyB⟩, rfl⟩
  have hγP : ∀ t ∈ Set.Icc (0 : ℝ) 1, (γ t).PosDef := fun t ht => hK₀P _ (hγK t ht)
  -- the connectedness argument
  by_contra hTC
  have hTC' : T ∉ C := hTC
  set Su := ⋃ X ∈ 𝒳 ∩ C, γ ⁻¹' clR7 X with hSu
  set Sv := ⋃ X ∈ 𝒳 \ C, γ ⁻¹' clR7 X with hSv
  have hSuc : IsClosed Su :=
    (h𝒳f.subset Set.inter_subset_left).isClosed_biUnion fun X _ => (isClosed_clR7 X).preimage hγc
  have hSvc : IsClosed Sv :=
    (h𝒳f.subset Set.sdiff_subset).isClosed_biUnion fun X _ => (isClosed_clR7 X).preimage hγc
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ X, γ t ∈ img X → X ∈ 𝒳 ∧ γ t ∈ clR7 X := fun t ht X h =>
    ⟨⟨γ t, h, hγK t ht⟩, ((mem_img_iff7 X _).1 h).1⟩
  have hcover : Set.Icc (0 : ℝ) 1 ⊆ Su ∪ Sv := by
    intro t ht
    have h := (thm_7_1 (n := n)).subset (show γ t ∈ {F | F.PosDef} from hγP t ht)
    obtain ⟨X, hX⟩ := Set.mem_iUnion.1 h
    obtain ⟨hX𝒳, hXcl⟩ := hmem t ht X hX
    by_cases hXC : X ∈ C
    · exact Or.inl (Set.mem_biUnion ⟨hX𝒳, hXC⟩ hXcl)
    · exact Or.inr (Set.mem_biUnion ⟨hX𝒳, hXC⟩ hXcl)
  have h0 : (Set.Icc (0 : ℝ) 1 ∩ Su).Nonempty := by
    refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
    have hγ0 : γ 0 = x₀ := by simp [hγ]
    have h := hmem 0 ⟨le_rfl, zero_le_one⟩ 1 (by rw [hγ0]; exact hx₀1)
    exact Set.mem_biUnion ⟨h.1, ⟨1, Relation.ReflTransGen.refl, rfl⟩⟩ h.2
  have h1 : (Set.Icc (0 : ℝ) 1 ∩ Sv).Nonempty := by
    refine ⟨1, ⟨zero_le_one, le_rfl⟩, ?_⟩
    have hγ1 : γ 1 = y := by simp [hγ]
    have h := hmem 1 ⟨zero_le_one, le_rfl⟩ T (by rw [hγ1]; exact hyT)
    exact Set.mem_biUnion ⟨h.1, hTC'⟩ h.2
  obtain ⟨t, ht, htu, htv⟩ := isPreconnected_closed_iff.1 isPreconnected_Icc Su Sv hSuc hSvc hcover h0 h1
  obtain ⟨X, ⟨hX𝒳, hXC⟩, hXt⟩ := Set.mem_iUnion₂.1 htu
  obtain ⟨Y, ⟨hY𝒳, hYC⟩, hYt⟩ := Set.mem_iUnion₂.1 htv
  have hXi : γ t ∈ img X := (mem_img_iff7 X _).2 ⟨hXt, hγP t ht⟩
  have hYi : γ t ∈ img Y := (mem_img_iff7 Y _).2 ⟨hYt, hγP t ht⟩
  obtain ⟨W, hW, hWX⟩ := hXC
  by_cases hXY : img X = img Y
  · exact hYC ⟨W, hW, hWX.trans hXY⟩
  by_cases hnb : AreNeighbours X Y
  · exact hYC ⟨Y, hW.tail ((areNeighbours_congr hWX rfl).2 hnb), rfl⟩
  -- a bad pair: the segment would meet it, so y would lie in its cone
  have hpP : (X, Y) ∈ P := ⟨hX𝒳, hY𝒳, hXY, ⟨γ t, hXi, hYi⟩, hnb⟩
  have hH : cone (X, Y) ∈ 𝓗 := by
    rw [Set.Finite.mem_toFinset]; exact ⟨(X, Y), hpP, rfl⟩
  apply hyH _ hH
  have ht0 : t ≠ 0 := by
    rintro rfl
    have hγ0 : γ 0 = x₀ := by simp [hγ]
    rw [hγ0] at hXi hYi
    exact hXY ((thm_7_4 hx₀int hXi).symm.trans (thm_7_4 hx₀int hYi))
  have hx₀H : x₀ ∈ cone (X, Y) := subset_affineSpan ℝ _ (Set.mem_insert _ _)
  have hγH : γ t ∈ cone (X, Y) := subset_affineSpan ℝ _ (Set.mem_insert_of_mem _ ⟨hXi, hYi⟩)
  have hdir : t⁻¹ • (γ t -ᵥ x₀) ∈ (cone (X, Y)).direction :=
    (cone (X, Y)).direction.smul_mem _ (AffineSubspace.vsub_mem_direction hγH hx₀H)
  have hy : y = t⁻¹ • (γ t -ᵥ x₀) +ᵥ x₀ := by
    simp only [hγ, vsub_eq_sub, vadd_eq_add, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht0, one_smul,
      sub_add_cancel]
  rw [hy]
  exact AffineSubspace.vadd_mem_of_mem_direction hdir hx₀H

end NeighbourGen

open NeighbourGen in
/-- **Cassels, Ch. 12, §7, Corollary to Theorem 7.7, for every $n$** (p. 279): every $T \in \mathrm{GL}_n(\mathbb Z)$ is a
product $S_0 \cdots S_{k-1} D$ of elements $S_i$ of $\Sigma'$ (`sigmaPrime n`: $\mathcal R$ and $S_i\mathcal R$ are
neighbours) and a diagonal matrix $D$ with entries $\pm 1$. **Unconditional**: the named statement
`NeighbourGeneration n` holds for every $n$ (Cassels' segment argument; see the module docstring). -/
@[kb "cassels1978" "Ch. 12, §7, Cor. to Thm. 7.7, p. 279 (every n; proved)"]
theorem neighbourGeneration (n : ℕ) : NeighbourGeneration n := by
  refine ⟨fun T => ?_⟩
  obtain ⟨X, hX, hXT⟩ := reachable T
  obtain ⟨l, hl, rfl⟩ := exists_prod_of_reflTransGen hX
  -- $T(X)^{-1}$ fixes $\mathcal R$, so it is diagonal with entries $\pm 1$ (Theorem 7.2)
  have hD : IsSignDiagonal (T * l.prod⁻¹) := by
    apply thm_7_2
    rw [img_mul, ← hXT, ← img_mul, mul_inv_cancel, img_one_eq']
  refine ⟨l.map fun S => (T * l.prod⁻¹) * S * (T * l.prod⁻¹)⁻¹, T * l.prod⁻¹, ?_, hD, ?_⟩
  · intro S hS
    obtain ⟨S', hS', rfl⟩ := List.mem_map.1 hS
    exact conj_mem_sigmaPrime hD (hl S' hS')
  · rw [← mul_prod_eq, inv_mul_cancel_right]

end Tessellation

end QuadFormsKB.Reduction
