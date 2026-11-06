/-
# Cassels, Chapter 2: Examples 7, 16, 17 (totally isotropic subspaces; isotropy over $k(\sqrt D)$)

Source: J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 2, *Examples*, pp. 29–30 and 33.

**Setting.** As in `Ch2/Exercises.lean`: $k$ = `F` is a field of characteristic $\ne 2$, $(U, \phi)$ is
`Q : QuadraticForm F V` with $V$ finite-dimensional, $\phi(u, v)$ = `OMeara.bil Q`, regular means that it is
nondegenerate, autometries are `OMeara.orth Q`.

**Proves.**
* Ex. 7 (pp. 29–30): for a regular space of dimension $2r$ with a totally isotropic subspace $V$ of dimension $r$:
  a totally isotropic complement $W$ (`ex7_i`), a dual basis of $W$ (`ex7_ii`), the description of all such
  complements (`ex7_iii`), and every autometry with $\sigma V = V$ is proper (`ex7_iv`).
* Ex. 16, 17 (p. 33): isotropy over $k(\sqrt D)$, written over $k$ (`ex16`, `ex17`).
-/
import QuadFormsKB.Literature.OMeara.Sec43CD

open QuadraticMap Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Cassels.Ch2Ex

open QuadFormsKB.OMeara

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] (Q : QuadraticForm F V)

/-- `bil` is the associated bilinear form. -/
lemma bil_eq_assoc (x y : V) : bil Q x y = associated Q x y := rfl

/-- Linearity of `bil` in the second variable over a finite sum. -/
lemma bil_sum_right' {ι : Type*} (s : Finset ι) (x : V) (c : ι → F) (z : ι → V) :
    bil Q x (∑ k ∈ s, c k • z k) = ∑ k ∈ s, c k * bil Q x (z k) := by
  simp [bil, map_sum]

/-- Linearity of `bil` in the first variable over a finite sum. -/
lemma bil_sum_left' {ι : Type*} (s : Finset ι) (y : V) (c : ι → F) (z : ι → V) :
    bil Q (∑ k ∈ s, c k • z k) y = ∑ k ∈ s, c k * bil Q (z k) y := by
  simp [bil, map_sum]

/-- Totally isotropic subspaces are `bil`-orthogonal to themselves. -/
lemma bil_zero_of_iso {P : Submodule F V} (hPiso : ∀ x ∈ P, Q x = 0) {x y : V} (hx : x ∈ P)
    (hy : y ∈ P) : bil Q x y = 0 :=
  cd_bil_eq_zero_of_Q Q (hPiso x hx) (hPiso y hy) (hPiso _ (P.add_mem hx hy))

/-- A half-dimensional totally isotropic subspace of a regular space equals its orthogonal. -/
lemma perp_eq_of_iso (hQ : (associated Q).Nondegenerate) {r : ℕ} (hn : finrank F V = 2 * r)
    (P : Submodule F V) (hP : finrank F P = r) (hPiso : ∀ x ∈ P, Q x = 0) :
    LinearMap.BilinForm.orthogonal (associated Q) P = P := by
  have hle : P ≤ LinearMap.BilinForm.orthogonal (associated Q) P := fun a ha => by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro b hb
    exact bil_zero_of_iso Q hPiso hb ha
  have hd := LinearMap.BilinForm.finrank_orthogonal hQ P
  symm
  apply Submodule.eq_of_le_of_finrank_eq hle
  omega

/-- Every functional on `P` is represented by a vector of `V`. -/
lemma exists_rep (hQ : (associated Q).Nondegenerate) {r : ℕ} (hn : finrank F V = 2 * r)
    (P : Submodule F V) (hP : finrank F P = r) (hPiso : ∀ x ∈ P, Q x = 0) (φ : Dual F P) :
    ∃ y : V, ∀ p : P, bil Q p y = φ p := by
  let Φ : V →ₗ[F] Dual F P := P.subtype.dualMap ∘ₗ (associated Q).flip
  have hker : LinearMap.ker Φ = P := by
    have key : ∀ y, Φ y = 0 ↔ y ∈ LinearMap.BilinForm.orthogonal (associated Q) P := fun y => by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      constructor
      · intro h p hp
        have := LinearMap.congr_fun h ⟨p, hp⟩
        simpa [Φ] using this
      · intro h
        ext p
        simpa [Φ] using h p p.2
    ext y
    rw [LinearMap.mem_ker, key, perp_eq_of_iso Q hQ hn P hP hPiso]
  have hr := LinearMap.finrank_range_add_finrank_ker Φ
  rw [hker] at hr
  have hdual : finrank F (Dual F P) = r := by rw [Subspace.dual_finrank_eq, hP]
  have htop : LinearMap.range Φ = ⊤ := Submodule.eq_top_of_finrank_eq (by omega)
  have : φ ∈ LinearMap.range Φ := by rw [htop]; trivial
  obtain ⟨y, hy⟩ := this
  exact ⟨y, fun p => by simpa [Φ, bil_eq_assoc] using LinearMap.congr_fun hy p⟩

/-- A family with `bil (v i) (y j) = δ` is linearly independent. -/
lemma lin_indep_of_pair {r : ℕ} (v y : Fin r → V)
    (h : ∀ i j, bil Q (v i) (y j) = if i = j then 1 else 0) : LinearIndependent F y := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have := congrArg (bil Q (v i)) hc
  rw [bil_sum_right'] at this
  simpa [h] using this

/-- Dual family: vectors `y j` with `bil (v i) (y j) = δ_ij`. -/
lemma exists_dual_family (hQ : (associated Q).Nondegenerate) {r : ℕ} (hn : finrank F V = 2 * r)
    (P : Submodule F V) (hP : finrank F P = r) (hPiso : ∀ x ∈ P, Q x = 0) (v : Basis (Fin r) F P) :
    ∃ y : Fin r → V, ∀ i j, bil Q (v i) (y j) = if i = j then 1 else 0 := by
  have := fun j => exists_rep Q hQ hn P hP hPiso (v.dualBasis j)
  choose y hy using this
  refine ⟨y, fun i j => ?_⟩
  rw [hy j (v i), Basis.dualBasis_apply_self]

/-- **Cassels, Ch. 2, Ex. 7 (i) (p. 29).** Let $(U, \phi)$ be regular of dimension $n = 2r$ and $V \subseteq U$ a
subspace of dimension $r$ on which $\phi$ vanishes. Then $U = V \oplus W$ for a subspace $W$ of dimension $r$ on
which $\phi$ also vanishes. -/
@[kb "cassels1978" "Ch. 2, Ex. 7 (i), p. 29"]
theorem ex7_i (hQ : (associated Q).Nondegenerate) {r : ℕ} (hn : finrank F V = 2 * r) (P : Submodule F V)
    (hP : finrank F P = r) (hPiso : ∀ x ∈ P, Q x = 0) :
    ∃ W : Submodule F V, IsCompl P W ∧ finrank F W = r ∧ ∀ x ∈ W, Q x = 0 := by
  classical
  let v : Basis (Fin r) F P := Module.finBasisOfFinrankEq F P hP
  obtain ⟨y, hy⟩ := exists_dual_family Q hQ hn P hP hPiso v
  have h2 : (2 : F) ≠ 0 := cd_two_ne
  let w : Fin r → V := fun j => y j - ∑ k, (bil Q (y j) (y k) / 2) • ((v k : P) : V)
  have hvy : ∀ i j, bil Q (y j) ((v i : P) : V) = if i = j then 1 else 0 := fun i j => by
    rw [bil_comm, hy]
  have hvw : ∀ i j, bil Q ((v i : P) : V) (w j) = if i = j then 1 else 0 := by
    intro i j
    simp only [w, bil_sub_right, bil_sum_right', hy]
    rw [Finset.sum_eq_zero (fun k _ => by rw [bil_zero_of_iso Q hPiso (v i).2 (v k).2, mul_zero])]
    simp
  have hww : ∀ i j, bil Q (w i) (w j) = 0 := by
    intro i j
    have e1 : bil Q (y i) (w j) = bil Q (y i) (y j) - bil Q (y j) (y i) / 2 := by
      simp only [w, bil_sub_right, bil_sum_right', hvy]
      simp [Finset.sum_ite_eq']
    have e2 : bil Q (w i) (w j) = bil Q (y i) (w j) - bil Q (y i) (y j) / 2 := by
      conv_lhs => rw [show w i = y i - ∑ k, (bil Q (y i) (y k) / 2) • ((v k : P) : V) from rfl]
      rw [bil_sub_left, bil_sum_left']
      simp only [hvw]
      simp
    rw [e2, e1, bil_comm Q (y j) (y i)]
    field_simp
    ring
  have hli := lin_indep_of_pair Q (fun i => ((v i : P) : V)) w hvw
  refine ⟨Submodule.span F (Set.range w), ?_, ?_, ?_⟩
  · have hfr : finrank F (Submodule.span F (Set.range w)) = r := by
      rw [finrank_span_eq_card hli]; simp
    rw [Submodule.isCompl_iff_disjoint _ _ (by omega)]
    rw [Submodule.disjoint_def]
    intro x hxP hxW
    obtain ⟨c, rfl⟩ := Submodule.mem_span_range_iff_exists_fun F |>.mp hxW
    have : ∀ i, c i = 0 := fun i => by
      have := bil_zero_of_iso Q hPiso (v i).2 hxP
      rw [bil_sum_right'] at this
      simpa [hvw] using this
    simp [this]
  · rw [finrank_span_eq_card hli]; simp
  · intro x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_range_iff_exists_fun F |>.mp hx
    rw [← bil_self, bil_sum_left']
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [bil_sum_right']
    rw [Finset.sum_eq_zero (fun k _ => by rw [hww, mul_zero]), mul_zero]

/-- **Cassels, Ch. 2, Ex. 7 (ii) (p. 29).** In the situation of (i), if $v_0, \dots, v_{r-1}$ is a basis of $V$, then
$W$ has a basis $w_0, \dots, w_{r-1}$ with $\phi(v_i, w_j) = 1$ if $i = j$ and $0$ otherwise. -/
@[kb "cassels1978" "Ch. 2, Ex. 7 (ii), p. 29"]
theorem ex7_ii (hQ : (associated Q).Nondegenerate) {r : ℕ} (hn : finrank F V = 2 * r) (P W : Submodule F V)
    (hPW : IsCompl P W) (hPiso : ∀ x ∈ P, Q x = 0) (hWiso : ∀ x ∈ W, Q x = 0) (v : Basis (Fin r) F P) :
    ∃ w : Basis (Fin r) F W, ∀ i j, bil Q (v i) (w j) = if i = j then 1 else 0 := by
  have hPr : finrank F P = r := by simpa using Module.finrank_eq_card_basis v
  have hWr : finrank F W = r := by
    have := Submodule.finrank_add_eq_of_isCompl hPW
    omega
  obtain ⟨y, hy⟩ := exists_dual_family Q hQ hn P hPr hPiso v
  have hdec : ∀ j, ∃ p ∈ P, ∃ w ∈ W, p + w = y j := fun j =>
    Submodule.mem_sup.mp (by rw [hPW.sup_eq_top]; trivial)
  choose p hp w hw hpw using hdec
  have hpair : ∀ i j, bil Q (v i) (w j) = if i = j then 1 else 0 := by
    intro i j
    have h1 := hy i j
    rw [← hpw j, bil_add_right, bil_zero_of_iso Q hPiso (v i).2 (hp j), zero_add] at h1
    exact h1
  have hli : LinearIndependent F (fun j => (⟨w j, hw j⟩ : W)) :=
    LinearIndependent.of_comp W.subtype
      (lin_indep_of_pair Q (fun i => ((v i : P) : V)) w hpair)
  refine ⟨basisOfLinearIndependentOfCardEqFinrank' _ hli (by simp [hWr]), fun i j => ?_⟩
  simpa using hpair i j

/-- `bil` is symmetric. -/
lemma bil_comm' (x y : V) : bil Q x y = bil Q y x := by
  rw [bil_eq_assoc, bil_eq_assoc]
  exact associated_isSymm F Q x y

/-- An element of $V$ written in the basis $v_0, \dots, v_{r-1}$ of the subspace $P$. -/
lemma eq_sum_basis {r : ℕ} (P : Submodule F V) (v : Basis (Fin r) F P) {x : V} (hx : x ∈ P) :
    x = ∑ j, v.repr ⟨x, hx⟩ j • (v j : V) := by
  have := congrArg Subtype.val (v.sum_repr ⟨x, hx⟩)
  rw [Submodule.coe_sum] at this
  simp only [Submodule.coe_smul] at this
  exact this.symm

/-- **Cassels, Ch. 2, Ex. 7 (iii) (p. 29).** In the situation of (i) and (ii) ($V$ with basis $v_0, \dots, v_{r-1}$,
a totally isotropic complement $W$ with basis $w_0, \dots, w_{r-1}$, $\phi(v_i, w_j) = 1$ if $i = j$ and $0$
otherwise), let $W^{*}$ be any subspace with the properties of $W$ in (i). Then $W^{*}$ has a basis
$w_0^{*}, \dots, w_{r-1}^{*}$ with $w_i^{*} = w_i + \sum_j \lambda_{ij}v_j$, where $\lambda_{ij} + \lambda_{ji} = 0$. (The
displayed formula is partly lost in the machine-read text; it is reconstructed from the conditions on $\lambda$.) -/
@[kb "cassels1978" "Ch. 2, Ex. 7 (iii), p. 29"]
theorem ex7_iii (hQ : (associated Q).Nondegenerate) {r : ℕ} (hn : finrank F V = 2 * r) (P W W' : Submodule F V)
    (hPW' : IsCompl P W') (hPiso : ∀ x ∈ P, Q x = 0) (hWiso : ∀ x ∈ W, Q x = 0) (hW'iso : ∀ x ∈ W', Q x = 0)
    (v : Basis (Fin r) F P) (w : Basis (Fin r) F W) (hw : ∀ i j, bil Q (v i) (w j) = if i = j then 1 else 0) :
    ∃ (w' : Basis (Fin r) F W') (l : Fin r → Fin r → F),
      (∀ i, (w' i : V) = w i + ∑ j, l i j • (v j : V)) ∧ ∀ i j, l i j + l j i = 0 := by
  have hPr : finrank F P = r := by simpa using Module.finrank_eq_card_basis v
  obtain ⟨w', hw'⟩ := ex7_ii Q hQ hn P W' hPW' hPiso hW'iso v
  have hd : ∀ i, (w' i : V) - w i ∈ P := by
    intro i
    rw [← perp_eq_of_iso Q hQ hn P hPr hPiso, LinearMap.BilinForm.mem_orthogonal_iff]
    intro x hx
    show associated Q x _ = 0
    rw [← bil_eq_assoc, eq_sum_basis P v hx, bil_sum_left']
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [bil_sub_right, hw', hw, sub_self, mul_zero]
  let l : Fin r → Fin r → F := fun i j => v.repr ⟨_, hd i⟩ j
  have hl : ∀ i, (w' i : V) = w i + ∑ j, l i j • (v j : V) := fun i => by
    rw [← eq_sum_basis P v (hd i)]; abel
  refine ⟨w', l, hl, fun i k => ?_⟩
  have h0 : bil Q (w' i) (w' k) = 0 := bil_zero_of_iso Q hW'iso (w' i).2 (w' k).2
  have hvv : ∀ j m, bil Q (v j) (v m) = 0 := fun j m => bil_zero_of_iso Q hPiso (v j).2 (v m).2
  rw [hl, hl, bil_add_left, bil_add_right, bil_add_right, bil_zero_of_iso Q hWiso (w i).2 (w k).2,
    bil_sum_right', bil_sum_left', bil_sum_left'] at h0
  simp only [bil_sum_right', hvv, mul_zero, Finset.sum_const_zero, add_zero, zero_add] at h0
  simp only [bil_comm' Q (w i : V), hw, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte] at h0
  linear_combination h0

/-- **Cassels, Ch. 2, Ex. 7 (iv) (p. 30).** Let $(U, \phi)$ be regular of dimension $2r$ and $V$ a subspace of
dimension $r$ on which $\phi$ vanishes. An autometry $\sigma$ with $\sigma V = V$ is proper: $\det\sigma = 1$. -/
@[kb "cassels1978" "Ch. 2, Ex. 7 (iv), p. 30"]
theorem ex7_iv (hQ : (associated Q).Nondegenerate) {r : ℕ} (hn : finrank F V = 2 * r) (P : Submodule F V)
    (hP : finrank F P = r) (hPiso : ∀ x ∈ P, Q x = 0) {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q)
    (hσP : P.map (σ : V →ₗ[F] V) = P) :
    LinearMap.det (σ : V →ₗ[F] V) = 1 := by
  classical
  obtain ⟨W, hPW, hWr, hWiso⟩ := ex7_i Q hQ hn P hP hPiso
  let v : Basis (Fin r) F P := Module.finBasisOfFinrankEq F P hP
  obtain ⟨w, hw⟩ := ex7_ii Q hQ hn P W hPW hPiso hWiso v
  let e := Submodule.prodEquivOfIsCompl P W hPW
  let b : Basis (Fin r ⊕ Fin r) F V := (v.prod w).map e
  have hb_l : ∀ i, b (Sum.inl i) = ((v i : P) : V) := by intro i; simp [b, Basis.prod_apply, e]
  have hb_r : ∀ j, b (Sum.inr j) = ((w j : W) : V) := by intro j; simp [b, Basis.prod_apply, e]
  have hrepr : ∀ x, b.repr x = (v.prod w).repr (e.symm x) := by intro x; simp [b]
  have hbil : ∀ s t, bil Q (b s) (b t) =
      Sum.elim (fun k => Sum.elim (fun l => (0 : F)) (fun l => if k = l then 1 else 0))
        (fun k => Sum.elim (fun l => if l = k then 1 else 0) (fun l => (0 : F))) s t := by
    intro s t
    rcases s with k | k <;> rcases t with l | l <;> simp only [hb_l, hb_r, Sum.elim_inl, Sum.elim_inr]
    · exact bil_zero_of_iso Q hPiso (v k).2 (v l).2
    · exact hw k l
    · rw [bil_comm]; exact hw l k
    · exact bil_zero_of_iso Q hWiso (w k).2 (w l).2
  let M := LinearMap.toMatrix b b (σ : V →ₗ[F] V)
  have hM : ∀ s t, M s t = b.repr (σ (b t)) s := fun s t => by simp [M, LinearMap.toMatrix_apply]
  have hzero : ∀ l i, M (Sum.inr l) (Sum.inl i) = 0 := by
    intro l i
    rw [hM, hrepr, hb_l]
    have hmem : σ ((v i : P) : V) ∈ P := by
      have : σ ((v i : P) : V) ∈ P.map (σ : V →ₗ[F] V) := ⟨_, (v i).2, rfl⟩
      rwa [hσP] at this
    have : e.symm (σ ((v i : P) : V)) = (⟨σ ((v i : P) : V), hmem⟩, 0) := by
      rw [LinearEquiv.symm_apply_eq]; simp [e]
    rw [this]; simp
  have hAD : M.toBlocks₁₁.transpose * M.toBlocks₂₂ = 1 := by
    ext i j
    have h1 := cd_bil_orth Q hσ (b (Sum.inl i)) (b (Sum.inr j))
    rw [hbil] at h1
    have hx : ∀ t, σ (b t) = ∑ s, M s t • b s := fun t => by
      conv_lhs => rw [← b.sum_repr (σ (b t))]
      simp [hM]
    rw [hx, hx, bil_sum_left'] at h1
    simp only [bil_sum_right'] at h1
    simp only [hbil, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hzero] at h1
    simp [Matrix.mul_apply, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.one_apply] at h1 ⊢
    exact h1
  have hdet : LinearMap.det (σ : V →ₗ[F] V) = M.det := (LinearMap.det_toMatrix b _).symm
  have hblocks : M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂ := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
    congr 1
    ext l i
    simpa [Matrix.toBlocks₂₁] using hzero l i
  have hd2 := Matrix.det_fromBlocks_zero₂₁ M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₂
  rw [← hblocks] at hd2
  have := congrArg Matrix.det hAD
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
  rw [hdet, hd2]; exact this

/-- **Cassels, Ch. 2, Ex. 16 (p. 33), written over $k$.** Let $(U, \phi)$ be anisotropic, $D \in k^{\times}$ not a
square, $K = k(\delta)$ with $\delta^{2} = D$, and suppose $\phi(u + v\delta) = 0$ with $u, v \in U$ not both $0$.
Since $\phi(u + v\delta) = \phi(u) + D\phi(v) + 2\delta\phi(u, v)$ and $1, \delta$ are a $k$-basis of $K$, the hypothesis is
$\phi(u) + D\phi(v) = 0$ and $\phi(u, v) = 0$. Then $u, v$ span a space $V$ of dimension $2$ on which $\phi$ is regular
of determinant $\phi(u)\phi(v) \in -D(k^{\times})^{2}$. -/
@[kb "cassels1978" "Ch. 2, Ex. 16, p. 33"]
theorem ex16 (hQ : Q.Anisotropic) {D : F} (hD : ¬IsSquare D) {u v : V} (huv : u ≠ 0 ∨ v ≠ 0)
    (h1 : Q u + D * Q v = 0) (h2 : bil Q u v = 0) :
    LinearIndependent F ![u, v] ∧ Q u * Q v ≠ 0 ∧ ∃ t : F, t ≠ 0 ∧ Q u * Q v = -D * t ^ 2 := by
  have hD0 : D ≠ 0 := fun h => hD ⟨0, by simp [h]⟩
  have hv : v ≠ 0 := by
    rintro rfl
    rcases huv with h | h
    · apply h
      apply hQ
      simpa using h1
    · exact h rfl
  have hQv : Q v ≠ 0 := fun h => hv (hQ v h)
  have hQu : Q u ≠ 0 := by
    intro h
    rw [h, zero_add] at h1
    exact hQv ((mul_eq_zero.mp h1).resolve_left hD0)
  have hu : Q u = -(D * Q v) := by linear_combination h1
  refine ⟨?_, mul_ne_zero hQu hQv, Q u / D, div_ne_zero hQu hD0, ?_⟩
  · rw [LinearIndependent.pair_iff]
    intro a b hab
    have hz : Q (a • u + b • v) = 0 := by rw [hab]; simp
    rw [Q_add, QuadraticMap.map_smul, QuadraticMap.map_smul] at hz
    have hb : bil Q (a • u) (b • v) = 0 := by
      rw [bil_smul_left, bil_smul_right, h2]; ring
    rw [hb, hu] at hz
    have hz' : (a ^ 2 * -D + b ^ 2) * Q v = 0 := by simp only [smul_eq_mul] at hz; linear_combination hz
    have hz'' : b ^ 2 = D * a ^ 2 := by
      have := (mul_eq_zero.mp hz').resolve_right hQv
      linear_combination this
    by_cases ha : a = 0
    · subst ha
      have : b = 0 := by simpa using hz''
      exact ⟨rfl, this⟩
    · exfalso
      apply hD
      refine ⟨b / a, ?_⟩
      field_simp
      linear_combination -hz''
  · rw [hu]; field_simp

/-- A binary form with Gram determinant $-m^2$ on two independent vectors is isotropic. -/
lemma binary_iso (n : Fin 2 → V) (hli : LinearIndependent F n) (m : F)
    (hdet : Q (n 0) * Q (n 1) - bil Q (n 0) (n 1) ^ 2 = -m ^ 2) : ∃ x : V, x ≠ 0 ∧ Q x = 0 := by
  have key : ∀ c0 c1 : F, c0 • n 0 + c1 • n 1 = 0 → c0 = 0 ∧ c1 = 0 := fun c0 c1 h => by
    have := Fintype.linearIndependent_iff.mp hli ![c0, c1] (by simpa [Fin.sum_univ_two] using h)
    exact ⟨by simpa using this 0, by simpa using this 1⟩
  by_cases ha : Q (n 0) = 0
  · exact ⟨n 0, fun h => by have := key 1 0 (by simp [h]); simp at this, ha⟩
  · refine ⟨((m - bil Q (n 0) (n 1)) / Q (n 0)) • n 0 + n 1, fun h => by
      have := key ((m - bil Q (n 0) (n 1)) / Q (n 0)) 1 (by simpa using h)
      simp at this, ?_⟩
    rw [Q_add, QuadraticMap.map_smul, bil_smul_left]
    simp only [smul_eq_mul]
    field_simp
    linear_combination hdet

/-- **Cassels, Ch. 2, Ex. 17 (p. 33), written over $k$.** Let $(U, \phi)$ be regular of dimension $4$ with
determinant $d(\phi) \in d(k^{\times})^{2}$ (Gram determinant of a basis), and suppose $U$ is isotropic over
$K = k(\delta)$, $\delta^{2} = d$; as in Ex. 16 this means: $\phi(u) + d\phi(v) = 0$ and $\phi(u, v) = 0$ for some
$u, v \in U$ not both $0$. Then $U$ is isotropic over $k$. -/
@[kb "cassels1978" "Ch. 2, Ex. 17, p. 33"]
theorem ex17 (hQ : (associated Q).Nondegenerate) (hdim : finrank F V = 4) (b : Basis (Fin 4) F V) {d : F}
    (hd : ∃ t : F, t ≠ 0 ∧ (LinearMap.BilinForm.toMatrix b (associated Q)).det = d * t ^ 2) {u v : V}
    (huv : u ≠ 0 ∨ v ≠ 0) (h1 : Q u + d * Q v = 0) (h2 : bil Q u v = 0) :
    ∃ x : V, x ≠ 0 ∧ Q x = 0 := by
  classical
  by_contra hno
  push Not at hno
  have hQa : Q.Anisotropic := fun x hx => by_contra fun h => hno x h hx
  obtain ⟨t, ht, hdet⟩ := hd
  have hdet0 : (LinearMap.BilinForm.toMatrix b (associated Q)).det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hQ
  have hd0 : d ≠ 0 := by
    intro h; apply hdet0; rw [hdet, h]; ring
  by_cases hsq : IsSquare d
  · obtain ⟨e, he⟩ := hsq
    have hQe : ∀ s : F, s * s = d → u + s • v = 0 := by
      intro s hs
      apply hQa
      rw [Q_add, QuadraticMap.map_smul, bil_smul_right, h2]
      simp only [smul_eq_mul]
      linear_combination h1 + Q v * hs
    have a1 := hQe e he.symm
    have a2 := hQe (-e) (by rw [neg_mul_neg]; exact he.symm)
    have he0 : e ≠ 0 := by rintro rfl; apply hd0; rw [he]; ring
    have hv : v = 0 := by
      have : (2 * e) • v = 0 := by
        have := congrArg₂ (· - ·) a1 a2
        simp only [sub_self, neg_smul] at this
        rw [show (2 * e) • v = (u + e • v) - (u + -e • v) by module]
        rw [a1, a2]; simp
      exact (smul_eq_zero.mp this).resolve_left (mul_ne_zero two_ne_zero he0 |> fun h => by
        simpa using h)
    subst hv
    rw [smul_zero, add_zero] at a1
    rcases huv with h | h <;> simp_all
  · obtain ⟨hli, hQuv, -⟩ := ex16 Q hQa hsq huv h1 h2
    have hQu : Q u ≠ 0 := left_ne_zero_of_mul hQuv
    have hQv : Q v ≠ 0 := right_ne_zero_of_mul hQuv
    let S : Submodule F V := Submodule.span F (Set.range ![u, v])
    let sb : Basis (Fin 2) F S := Basis.span hli
    have hsb : ∀ i, (sb i : V) = ![u, v] i := fun i => congrArg Subtype.val (Basis.span_apply hli i)
    have hSr : finrank F S = 2 := by simp [S, finrank_span_eq_card hli]
    let N := LinearMap.BilinForm.orthogonal (associated Q) S
    have hNr : finrank F N = 2 := by
      have := LinearMap.BilinForm.finrank_orthogonal hQ S
      show finrank F (LinearMap.BilinForm.orthogonal (associated Q) S) = 2
      omega
    have huS : u ∈ S := Submodule.subset_span ⟨0, rfl⟩
    have hvS : v ∈ S := Submodule.subset_span ⟨1, rfl⟩
    have hdisj : Disjoint S N := by
      rw [Submodule.disjoint_def]
      intro x hxS hxN
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hxS
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hc
      have hu := LinearMap.BilinForm.mem_orthogonal_iff.mp hxN u huS
      have hv := LinearMap.BilinForm.mem_orthogonal_iff.mp hxN v hvS
      have hu' : bil Q u x = 0 := hu
      have hv' : bil Q v x = 0 := hv
      rw [← hc] at hu' hv'
      rw [bil_add_right, bil_smul_right, bil_smul_right, bil_self, h2] at hu'
      rw [bil_add_right, bil_smul_right, bil_smul_right, bil_self, bil_comm Q v u, h2] at hv'
      have c0 : c 0 = 0 := by simpa [hQu] using hu'
      have c1 : c 1 = 0 := by simpa [hQv] using hv'
      rw [← hc, c0, c1]; simp
    have hcompl : IsCompl S N := (Submodule.isCompl_iff_disjoint _ _ (by omega)).mpr hdisj
    let nb : Basis (Fin 2) F N := Module.finBasisOfFinrankEq F N hNr
    let e := Submodule.prodEquivOfIsCompl S N hcompl
    let b2 : Basis (Fin 2 ⊕ Fin 2) F V := (sb.prod nb).map e
    let b' : Basis (Fin 4) F V := b2.reindex finSumFinEquiv
    have hb_l : ∀ i, b2 (Sum.inl i) = ((sb i : S) : V) := by
      intro i; simp [b2, Basis.prod_apply, e]
    have hb_r : ∀ j, b2 (Sum.inr j) = ((nb j : N) : V) := by
      intro j; simp [b2, Basis.prod_apply, e]
    let G := LinearMap.BilinForm.toMatrix b2 (associated Q)
    have hG : ∀ s t, G s t = bil Q (b2 s) (b2 t) := fun s t => by
      simp [G, LinearMap.BilinForm.toMatrix_apply, bil_eq_assoc]
    have hortho : ∀ i j, bil Q (nb j : V) (sb i : V) = 0 := by
      intro i j
      rw [bil_comm]
      exact LinearMap.BilinForm.mem_orthogonal_iff.mp (nb j).2 _ (sb i).2
    have hG21 : G.toBlocks₂₁ = 0 := by
      ext j i
      simp [Matrix.toBlocks₂₁, hG, hb_l, hb_r, hortho]
    have hGdet : G.det = (Matrix.of fun i j : Fin 2 => bil Q (sb i : V) (sb j : V)).det *
        (Matrix.of fun i j : Fin 2 => bil Q (nb i : V) (nb j : V)).det := by
      have := Matrix.det_fromBlocks_zero₂₁ G.toBlocks₁₁ G.toBlocks₁₂ G.toBlocks₂₂
      rw [← hG21, Matrix.fromBlocks_toBlocks] at this
      rw [this]
      congr 2 <;> ext i j <;> simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, hG, hb_l, hb_r]
    have hGS : (Matrix.of fun i j : Fin 2 => bil Q (sb i : V) (sb j : V)).det = Q u * Q v := by
      simp [Matrix.det_fin_two, hsb, bil_self, h2, bil_comm Q v u]
    have hGN : (Matrix.of fun i j : Fin 2 => bil Q (nb i : V) (nb j : V)).det =
        Q (nb 0 : V) * Q (nb 1 : V) - bil Q (nb 0 : V) (nb 1 : V) ^ 2 := by
      simp [Matrix.det_fin_two, bil_self, bil_comm Q (nb 1 : V) (nb 0 : V)]
      ring
    have hb'G : LinearMap.BilinForm.toMatrix b' (associated Q) =
        Matrix.reindex finSumFinEquiv finSumFinEquiv G := by
      ext i j
      simp [G, b', LinearMap.BilinForm.toMatrix_apply, Basis.reindex_apply]
    have hP := LinearMap.BilinForm.toMatrix_mul_basis_toMatrix b b' (associated Q)
    have hdetP := congrArg Matrix.det hP
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hb'G, Matrix.det_reindex_self, hGdet,
      hGS, hGN, hdet] at hdetP
    set p := (b.toMatrix b').det
    have hu : Q u = -(d * Q v) := by linear_combination h1
    have hg : Q (nb 0 : V) * Q (nb 1 : V) - bil Q (nb 0 : V) (nb 1 : V) ^ 2 =
        -(p * t / Q v) ^ 2 := by
      rw [hu] at hdetP
      field_simp
      apply mul_left_cancel₀ hd0
      linear_combination hdetP
    have hnli : LinearIndependent F (fun i => ((nb i : N) : V)) :=
      nb.linearIndependent.map' N.subtype (Submodule.ker_subtype N)
    obtain ⟨x, hx0, hx⟩ := binary_iso Q (fun i => ((nb i : N) : V)) hnli (p * t / Q v) hg
    exact hno x hx0 hx

end QuadFormsKB.Cassels.Ch2Ex
