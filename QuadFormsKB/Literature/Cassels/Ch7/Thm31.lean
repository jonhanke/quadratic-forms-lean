/-
# Cassels, Chapter 7, Theorem 3.1 and Corollary: extending to a basis over a principal ideal domain

**Setting.** Cassels, *Rational Quadratic Forms*, Chapter 7, §3 (pp. 106–108): $I$ is a principal ideal domain inside a
field $k$ with $k \ne I$, $V$ a $k$-vector space with basis $e_0, \dots, e_{n-1}$ (Cassels: $e_1, \dots, e_n$), and
$\Lambda = Ie_0 + \cdots + Ie_{n-1}$ the lattice with this basis (`span I (Set.range e)`). Elements
$c_0, \dots, c_{J-1}$ of $\Lambda$ are given by their coordinates, $c_j = \sum_i r_{ji}e_i$ with $r_{ji} \in I$
(Cassels' (3.11)).

**Proves**
* `tfae_extends_basis_pid` (**Theorem 3.1**, p. 106): the three conditions (i) the $c_j$ extend to a basis of
  $\Lambda$, (ii) the $J \times J$ minors of $(r_{ji})$ are coprime, (iii) $\sum_j v_jc_j \in \Lambda$ with $v_j \in k$
  forces $v_j \in I$, are equivalent;
* `IsPrimitiveVec` (definition, p. 108): a vector is *primitive* if it belongs to some basis;
* `isPrimitiveVec_iff_coprime` (**Corollary**, p. 108): $c = \sum_i c_ie_i \in \Lambda$ is primitive if and only if
  $c_0, \dots, c_{n-1}$ are coprime.

**Conventions.** "Coprime" (Cassels' Note to (ii), p. 107: the ideal they generate is the whole ring) is
`Ideal.span (Set.range f) = ⊤`. The $J \times J$ minors are indexed by injections $s$ of `Fin J` into `Fin n` (the
rows $s(0), \dots, s(J-1)$, in any order; reordering only changes the sign). The special cases $I = \mathbb Z$ and
$I = \mathbb Z_p$ are `Siegel.tfae_extends_basis` (`Ch9Sec2.lean`) and `tfae_extends_basis_padic` (`Ch8/Bases.lean`).
-/
import QuadFormsKB.Literature.Cassels.Ch7.AdaptedBasis

namespace QuadFormsKB.Cassels

open Module Submodule Matrix

variable {I k V : Type*} [CommRing I] [IsDomain I] [IsPrincipalIdealRing I] [Field k] [Algebra I k]
  [AddCommGroup V] [Module k V] [Module I V] [IsScalarTower I k V]

/-- The $J \times n$ coordinate matrix $(r_{ji})$ of Cassels' (3.11), transposed: the $n \times J$ matrix whose
column $j$ is the coordinate vector of $c_j$. -/
def coordMat {n J : ℕ} (r : Fin J → Fin n → I) : Matrix (Fin n) (Fin J) I := Matrix.of fun i j => r j i

/-- Rectangular Cauchy–Binet (a copy of `Lattices.det_mul_rect`, `Ch11Sec6Subst.lean`, to keep the imports small). -/
private theorem det_mul_rect {R : Type*} [CommRing R] {m k : ℕ} (A : Matrix (Fin m) (Fin k) R)
    (B : Matrix (Fin k) (Fin m) R) :
    (A * B).det = ∑ p : Fin m → Fin k, (∏ i, A i (p i)) * (B.submatrix p id).det := by
  classical
  have key : ∀ M : Matrix (Fin m) (Fin m) R,
      M.det = ∑ σ : Equiv.Perm (Fin m), (Equiv.Perm.sign σ : ℤ) • ∏ i, M i (σ i) := by
    intro M
    rw [← Matrix.det_transpose, Matrix.det_apply]
    rfl
  rw [key (A * B)]
  have h1 : ∀ σ : Equiv.Perm (Fin m), ∏ i, (A * B) i (σ i) =
      ∑ p : Fin m → Fin k, (∏ i, A i (p i)) * ∏ i, B (p i) (σ i) := by
    intro σ
    simp_rw [Matrix.mul_apply]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.prod_mul_distrib]
  simp_rw [h1, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [key (B.submatrix p id), Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [zsmul_eq_mul, Matrix.submatrix_apply, id]
  ring

omit [IsDomain I] [IsPrincipalIdealRing I] in
/-- If the first $J$ columns of an invertible $n \times n$ matrix `T` are the columns of `R`, the $J \times J$ minors
of `R` generate the unit ideal (Cauchy–Binet applied to the first $J$ rows of $T^{-1}$). -/
private theorem ideal_top_of_unit {n J : ℕ} (hJ : J ≤ n) (R : Matrix (Fin n) (Fin J) I)
    (T : Matrix (Fin n) (Fin n) I) (hT : IsUnit T.det) (hcol : ∀ i j, T i (Fin.castLE hJ j) = R i j) :
    Ideal.span (Set.range fun s : Fin J ↪ Fin n => (R.submatrix s id).det) = ⊤ := by
  classical
  set A : Matrix (Fin J) (Fin n) I := Matrix.of fun j k => (T⁻¹) (Fin.castLE hJ j) k with hA
  have hAB : A * R = 1 := by
    ext j j'
    have := congrFun (congrFun (Matrix.nonsing_inv_mul T hT) (Fin.castLE hJ j)) (Fin.castLE hJ j')
    simp only [Matrix.mul_apply] at this
    simp only [Matrix.mul_apply, hA, Matrix.of_apply, ← hcol, Matrix.one_apply]
    rw [this]
    simp [Matrix.one_apply, Fin.ext_iff]
  have hdet := det_mul_rect A R
  rw [hAB, Matrix.det_one] at hdet
  rw [Ideal.eq_top_iff_one, hdet]
  refine Ideal.sum_mem _ fun q _ => ?_
  by_cases hq : Function.Injective q
  · exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨⟨q, hq⟩, rfl⟩)
  · obtain ⟨i, i', hii, hne'⟩ : ∃ i i', q i = q i' ∧ i ≠ i' := by
      simpa [Function.Injective] using hq
    rw [Matrix.det_zero_of_row_eq hne' (by ext l; simp [hii])]
    simp

/-- Extending a linearly independent family `c` in `I^n` with torsion-free quotient to a basis of `I^n`. -/
private theorem exists_basis_extend {n J : ℕ} (hJ : J ≤ n) (c : Fin J → Fin n → I)
    (hli : LinearIndependent I c)
    (htf : ∀ (d : I) (y : Fin n → I), d ≠ 0 → d • y ∈ span I (Set.range c) → y ∈ span I (Set.range c)) :
    ∃ B : Basis (Fin n) I (Fin n → I), ∀ j, B (Fin.castLE hJ j) = c j := by
  classical
  set N : Submodule I (Fin n → I) := span I (Set.range c) with hN
  have : NoZeroSMulDivisors I ((Fin n → I) ⧸ N) := by
    refine ⟨fun {d q} h => ?_⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective N q
    by_cases hd : d = 0
    · exact Or.inl hd
    · right
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
      exact (Submodule.Quotient.mk_eq_zero N).2 (htf d y hd h)
  let bQ := Module.Free.chooseBasis I ((Fin n → I) ⧸ N)
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ (LinearMap.id) N.mkQ_surjective
  have hmk : ∀ x, N.mkQ (s x) = x := fun x => by simpa using LinearMap.congr_fun hs x
  let v : Fin J ⊕ Module.Free.ChooseBasisIndex I ((Fin n → I) ⧸ N) → (Fin n → I) :=
    Sum.elim c (fun q => s (bQ q))
  have hcN : ∀ j, N.mkQ (c j) = 0 := fun j =>
    (Submodule.Quotient.mk_eq_zero N).2 (subset_span ⟨j, rfl⟩)
  have hv_li : LinearIndependent I v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fintype.sum_sum_type] at hg
    simp only [v, Sum.elim_inl, Sum.elim_inr] at hg
    have h1 := congrArg N.mkQ hg
    rw [map_add, map_sum, map_sum, map_zero] at h1
    have h2 : ∑ j, N.mkQ (g (Sum.inl j) • c j) = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [map_smul, hcN j, smul_zero]
    simp only [map_smul, hmk] at h1 h2
    rw [h2, zero_add] at h1
    have h3 : ∀ q, g (Sum.inr q) = 0 := fun q => by
      have := Fintype.linearIndependent_iff.1 bQ.linearIndependent (fun q => g (Sum.inr q)) h1 q
      exact this
    simp only [h3, zero_smul, Finset.sum_const_zero, add_zero] at hg
    have h4 := Fintype.linearIndependent_iff.1 hli (fun j => g (Sum.inl j)) hg
    rintro (j | q)
    · exact h4 j
    · exact h3 q
  have hNle : N ≤ span I (Set.range v) :=
    span_le.2 (by rintro _ ⟨j, rfl⟩; exact subset_span ⟨Sum.inl j, rfl⟩)
  have hv_sp : ⊤ ≤ span I (Set.range v) := by
    intro m _
    have hm : m = (m - s (N.mkQ m)) + s (N.mkQ m) := by abel
    rw [hm]
    refine add_mem (hNle ?_) ?_
    · rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, hmk, sub_self]
    · rw [← bQ.sum_repr (N.mkQ m), map_sum]
      refine sum_mem fun q _ => ?_
      have hq : s (bQ q) ∈ span I (Set.range v) := subset_span ⟨Sum.inr q, rfl⟩
      rw [map_smul]
      exact Submodule.smul_mem _ _ hq
  let B0 : Basis (Fin J ⊕ Module.Free.ChooseBasisIndex I ((Fin n → I) ⧸ N)) I (Fin n → I) :=
    Basis.mk hv_li hv_sp
  have hB0 : ∀ x, B0 x = v x := fun x => by simp [B0]
  have hcard : Fintype.card (Fin J ⊕ Module.Free.ChooseBasisIndex I ((Fin n → I) ⧸ N)) = n := by
    rw [← Module.finrank_eq_card_basis B0, Module.finrank_fin_fun]
  rw [Fintype.card_sum, Fintype.card_fin] at hcard
  -- an equivalence sending `inl j` to `castLE j`
  set p : Fin n → Prop := fun a => a ∈ Set.range (Fin.castLE hJ) with hp
  let e1 : Fin J ≃ {a // p a} := Equiv.ofInjective _ (Fin.castLE_injective hJ)
  have hc1 : Fintype.card {a // p a} = J := by
    rw [← Fintype.card_congr e1, Fintype.card_fin]
  let e2 : Module.Free.ChooseBasisIndex I ((Fin n → I) ⧸ N) ≃ {a // ¬ p a} :=
    Fintype.equivOfCardEq (by
      rw [Fintype.card_subtype_compl, Fintype.card_fin, hc1]
      omega)
  let σ : Fin J ⊕ Module.Free.ChooseBasisIndex I ((Fin n → I) ⧸ N) ≃ Fin n :=
    (Equiv.sumCongr e1 e2).trans (Equiv.sumCompl p)
  refine ⟨B0.reindex σ, fun j => ?_⟩
  have hσ : σ.symm (Fin.castLE hJ j) = Sum.inl j := by
    rw [Equiv.symm_apply_eq]
    simp [σ, e1, Equiv.sumCompl_apply_inl]
    rfl
  rw [Basis.reindex_apply, hσ, hB0]
  rfl

/-- If the entries of `w` generate the unit ideal, `w` extends to a basis of `I^n`. -/
private theorem exists_basis_of_unit_ideal {n : ℕ} (hn : 1 ≤ n) (w : Fin n → I)
    (h : Ideal.span (Set.range w) = ⊤) : ∃ B : Basis (Fin n) I (Fin n → I), B (Fin.castLE hn 0) = w := by
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun I).1
    (show (1 : I) ∈ Ideal.span (Set.range w) by rw [h]; exact Submodule.mem_top)
  simp only [smul_eq_mul] at ha
  have hli : LinearIndependent I (fun _ : Fin 1 => w) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    rw [Fin.sum_univ_one] at hg
    have h0 : g 0 = 0 := by
      calc g 0 = g 0 * ∑ i, a i * w i := by rw [ha, mul_one]
        _ = ∑ i, a i * (g 0 • w) i := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; simp only [Pi.smul_apply, smul_eq_mul]; ring
        _ = 0 := by rw [hg]; simp
    rwa [Fin.fin_one_eq_zero j]
  have htf : ∀ (d : I) (y : Fin n → I), d ≠ 0 → d • y ∈ span I (Set.range fun _ : Fin 1 => w) →
      y ∈ span I (Set.range fun _ : Fin 1 => w) := by
    intro d y hd hy
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun I).1 hy
    rw [Fin.sum_univ_one] at hg
    -- d * y i = g 0 * w i
    have hyi : ∀ i, d * y i = g 0 * w i := fun i => by
      have := congrFun hg i
      simpa using this.symm
    have hdg : d * ∑ i, a i * y i = g 0 := by
      calc d * ∑ i, a i * y i = ∑ i, a i * (d * y i) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring
        _ = ∑ i, a i * (g 0 * w i) := by simp_rw [hyi]
        _ = g 0 * ∑ i, a i * w i := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring
        _ = g 0 := by rw [ha, mul_one]
    have : y = (∑ i, a i * y i) • w := by
      funext i
      apply mul_left_cancel₀ hd
      rw [Pi.smul_apply, smul_eq_mul, ← mul_assoc, hdg, hyi i]
    rw [this]
    exact smul_mem _ _ (subset_span ⟨0, rfl⟩)
  obtain ⟨B, hB⟩ := exists_basis_extend hn (fun _ => w) hli htf
  exact ⟨B, hB 0⟩

/-- **Cassels, Ch. 7, Theorem 3.1**: *let $I$ be a principal ideal domain contained in the field $k$, $k \ne I$. Let
$e_1, \dots, e_n$ be any $I$-basis of a lattice $\Lambda$ and let $c_1, \dots, c_J$ be elements of $\Lambda$. Then the
following three statements are equivalent: (i) there exist $c_{J+1}, \dots, c_n$ such that $c_1, \dots, c_n$ is a
basis for $\Lambda$; (ii) let $c_j = \sum_{i=1}^n r_{ji}e_i$ ($1 \le j \le J$) be the expression of the $c_j$ in
terms of the given basis $e_i$; then the set of determinants of the $J \times J$ submatrices of the $J \times n$
matrix $r_{ji}$ is coprime; (iii) if $a = v_1c_1 + \cdots + v_Jc_J \in \Lambda$ with $v_1, \dots, v_J \in k$ then
necessarily $v_j \in I$ ($1 \le j \le J$).*

Here $\Lambda$ = `span I (Set.range e)` for a $k$-basis `e` of $V$; the vectors are $c_j = \sum_i r_{ji}e_i$
(`hc`); in (i) "basis of $\Lambda$" means $I$-linearly independent elements of $\Lambda$ spanning $\Lambda$, and
$c_0, \dots, c_{J-1}$ are its first $J$ members (indices $0, \dots, n-1$); in (ii) the minors are those of the
$n \times J$ matrix `coordMat r` (the transpose of Cassels' $J \times n$ matrix; transposing does not change the
minors), with rows chosen by an injection $s$. "$I \subseteq k$" is the injectivity of `algebraMap I k` and
"$k \ne I$" is `hk`; as Cassels notes, `hk` is used only for (iii) $\Rightarrow$ (i). -/
@[kb "cassels1978" "Ch. 7, Thm. 3.1, pp. 106–108"]
theorem tfae_extends_basis_pid (hinj : Function.Injective (algebraMap I k))
    (hk : ∃ x : k, x ∉ Set.range (algebraMap I k)) {n J : ℕ} (hJ : J ≤ n) (e : Basis (Fin n) k V)
    (r : Fin J → Fin n → I) (c : Fin J → V) (hc : ∀ j, c j = ∑ i, algebraMap I k (r j i) • e i) :
    List.TFAE
      [∃ c' : Fin n → V, (∀ j, c' (Fin.castLE hJ j) = c j) ∧ (∀ i, c' i ∈ span I (Set.range e)) ∧
          LinearIndependent I c' ∧ span I (Set.range c') = span I (Set.range e),
       Ideal.span (Set.range fun s : Fin J ↪ Fin n => ((coordMat r).submatrix s id).det) = ⊤,
       ∀ v : Fin J → k, ∑ j, v j • c j ∈ span I (Set.range e) → ∀ j, v j ∈ Set.range (algebraMap I k)] := by
  classical
  set φ := algebraMap I k with hφ
  -- the coordinate map `I^n → V`
  set ι : (Fin n → I) →ₗ[I] V := Fintype.linearCombination I (fun i => e i) with hιdef
  have hι : ∀ y, ι y = ∑ i, φ (y i) • e i := fun y => by
    rw [hιdef, Fintype.linearCombination_apply]
    exact Finset.sum_congr rfl fun i _ => (algebraMap_smul k (y i) (e i)).symm
  have hιinj : Function.Injective ι := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    rw [hι] at hy
    have := Fintype.linearIndependent_iff.1 e.linearIndependent (fun i => φ (y i)) hy
    funext i
    exact hinj (by simpa using this i)
  have hιrange : LinearMap.range ι = span I (Set.range e) := Fintype.range_linearCombination _ _
  have hcι : ∀ j, c j = ι (r j) := fun j => by rw [hc j, hι]
  tfae_have 1 → 2 := by
    rintro ⟨c', hc'1, hc'2, hli, hsp⟩
    have hmem : ∀ i, ∃ y : Fin n → I, ι y = c' i := fun i => by
      have := hc'2 i
      rw [← hιrange] at this
      exact this
    choose y hy using hmem
    have hyc : ι ∘ y = c' := funext hy
    have hyli : LinearIndependent I y := LinearIndependent.of_comp ι (by rw [hyc]; exact hli)
    have hysp : span I (Set.range y) = ⊤ := by
      apply Submodule.map_injective_of_injective hιinj
      rw [Submodule.map_span, ← Set.range_comp, hyc, hsp, ← hιrange, Submodule.map_top]
    let B : Basis (Fin n) I (Fin n → I) := Basis.mk hyli hysp.ge
    have hB : ⇑B = y := funext fun i => by simp [B]
    have hdet : IsUnit (((Pi.basisFun I (Fin n)).toMatrix y).det) := by
      have := (Pi.basisFun I (Fin n)).isUnit_det B
      rwa [Basis.det_apply, hB] at this
    refine ideal_top_of_unit hJ (coordMat r) _ hdet fun i j => ?_
    have hyj : y (Fin.castLE hJ j) = r j := by
      apply hιinj
      rw [hy, hc'1, hcι]
    simp [Basis.toMatrix_apply, hyj, coordMat]
  tfae_have 2 → 3 := by
    intro h v hv j
    obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun I).1 hv
    have hrepr : ∀ j i, e.repr (c j) i = φ (r j i) := fun j i => by
      rw [hc j]; exact congrFun (e.repr_sum_self _) i
    have hcoord : ∀ i, φ (w i) = ∑ j, v j * φ (r j i) := fun i => by
      have h1 := congrArg (fun x => e.repr x i) hw
      have h2 : (∑ i, w i • e i) = ∑ i, φ (w i) • e i :=
        Finset.sum_congr rfl fun i _ => (algebraMap_smul k (w i) (e i)).symm
      rw [h2, congrFun (e.repr_sum_self _) i] at h1
      rw [h1]
      simp [map_sum, hrepr]
    obtain ⟨l, hl⟩ := (Submodule.mem_span_range_iff_exists_fun I).1
      (show (1 : I) ∈ Ideal.span (Set.range fun s : Fin J ↪ Fin n => ((coordMat r).submatrix s id).det) by
        rw [h]; exact Submodule.mem_top)
    simp only [smul_eq_mul] at hl
    have key : ∀ s : Fin J ↪ Fin n, ∃ z : Fin J → I,
        ∀ j, φ (((coordMat r).submatrix s id).det) * v j = φ (z j) := by
      intro s
      set M : Matrix (Fin J) (Fin J) I := (coordMat r).submatrix s id with hM
      refine ⟨(M.adjugate) *ᵥ (fun l => w (s l)), fun j => ?_⟩
      have hMv : M.map φ *ᵥ v = fun l => φ (w (s l)) := by
        funext l
        rw [hcoord (s l)]
        simp only [Matrix.mulVec, dotProduct, hM, Matrix.map_apply, Matrix.submatrix_apply, coordMat,
          Matrix.of_apply, id]
        exact Finset.sum_congr rfl fun m _ => mul_comm _ _
      have hz : (fun j => φ ((M.adjugate *ᵥ (fun l => w (s l))) j)) =
          (M.adjugate).map φ *ᵥ (fun l => φ (w (s l))) := by
        funext j
        simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
      have := congrFun hz j
      rw [this, ← hMv, Matrix.mulVec_mulVec, ← Matrix.map_mul, Matrix.adjugate_mul]
      simp [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.one_apply, apply_ite φ]
    choose z hz using key
    refine ⟨∑ s, l s * z s j, ?_⟩
    rw [map_sum]
    have : v j = ∑ s, φ (l s) * (φ (((coordMat r).submatrix s id).det) * v j) := by
      simp_rw [← mul_assoc]
      rw [← Finset.sum_mul]
      have := congrArg φ hl
      simp only [map_sum, map_mul, map_one] at this
      rw [this, one_mul]
    rw [this]
    exact (Finset.sum_congr rfl fun s _ => by rw [hz s j, map_mul])
  tfae_have 3 → 1 := by
    intro h
    have hsumι : ∀ (g : Fin J → I) (a : k), (∑ j, (a * φ (g j)) • c j) = a • ι (∑ j, g j • r j) := by
      intro g a
      rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, hcι j, mul_smul, algebraMap_smul]
    have hli : LinearIndependent I r := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      by_contra hne
      push Not at hne
      obtain ⟨j0, hj0⟩ := hne
      obtain ⟨x, hx⟩ := hk
      have hφ0 : φ (g j0) ≠ 0 := fun h0 => hj0 (hinj (by rw [h0, map_zero]))
      have := h (fun j => (x / φ (g j0)) * φ (g j)) (by
        rw [hsumι, hg, map_zero, smul_zero]; exact Submodule.zero_mem _) j0
      obtain ⟨y, hy⟩ := this
      exact hx ⟨y, by rw [hy]; field_simp⟩
    have htf : ∀ (d : I) (y : Fin n → I), d ≠ 0 → d • y ∈ span I (Set.range r) →
        y ∈ span I (Set.range r) := by
      intro d y hd hy
      obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun I).1 hy
      have hφd : φ d ≠ 0 := fun h0 => hd (hinj (by rw [h0, map_zero]))
      have hv : (∑ j, ((φ d)⁻¹ * φ (a j)) • c j) = ι y := by
        rw [hsumι, ha, map_smul, ← algebraMap_smul k d (ι y), smul_smul, inv_mul_cancel₀ hφd, one_smul]
      have hz := h (fun j => (φ d)⁻¹ * φ (a j)) (by
        rw [hv, ← hιrange]; exact LinearMap.mem_range_self ι y)
      choose z hz using hz
      have haz : ∀ j, a j = d * z j := fun j => by
        apply hinj
        rw [map_mul, hz j]
        field_simp
      have hy' : y = ∑ j, z j • r j := by
        apply smul_right_injective _ hd
        simp only
        rw [← ha, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [haz j, mul_smul]
      rw [hy']
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (subset_span ⟨j, rfl⟩)
    obtain ⟨B, hB⟩ := exists_basis_extend hJ r hli htf
    refine ⟨fun i => ι (B i), fun j => ?_, fun i => ?_, ?_, ?_⟩
    · simp only [hB, hcι]
    · rw [← hιrange]; exact LinearMap.mem_range_self ι _
    · exact B.linearIndependent.map' ι (LinearMap.ker_eq_bot.2 hιinj)
    · have : (fun i => ι (B i)) = ι ∘ B := rfl
      rw [this, Set.range_comp, ← Submodule.map_span, B.span_eq, Submodule.map_top, hιrange]
  tfae_finish

/-- A *primitive* vector of an $I$-module $M$ (Cassels, Ch. 7, p. 108: "a vector $c \in \Lambda$ is primitive if
there is a basis $c = c_1, c_2, \dots, c_n$ of $\Lambda$"): $c$ is a member of some basis of $M$, i.e. of a set
$s \ni c$ that is $I$-linearly independent and spans $M$. -/
@[kb "cassels1978" "Ch. 7, §3, p. 108 (primitive vector)"]
def IsPrimitiveVec (I : Type*) {M : Type*} [CommRing I] [AddCommGroup M] [Module I M] (c : M) : Prop :=
  ∃ s : Set M, c ∈ s ∧ LinearIndependent I (Subtype.val : s → M) ∧ span I s = ⊤

/-- **Cassels, Ch. 7, Corollary to Theorem 3.1**: *let $c = c_1e_1 + \cdots + c_ne_n \in \Lambda$ where
$e_1, \dots, e_n$ is any basis. A necessary and sufficient condition for $c$ to be primitive is that
$c_1, \dots, c_n$ should be coprime.* Here $\Lambda$ is any $I$-module with a basis `e` ($I$ a principal ideal
domain; no field $k$ is needed) and $c_i$ = `e.repr c i`; "coprime" means the $c_i$ generate the unit ideal. -/
@[kb "cassels1978" "Ch. 7, Cor. to Thm. 3.1, p. 108"]
theorem isPrimitiveVec_iff_coprime {Λ : Type*} [AddCommGroup Λ] [Module I Λ] {n : ℕ} (e : Basis (Fin n) I Λ)
    (c : Λ) : IsPrimitiveVec I c ↔ Ideal.span (Set.range (e.repr c)) = ⊤ := by
  classical
  constructor
  · rintro ⟨s, hcs, hli, hsp⟩
    let bs : Basis s I Λ := Basis.mk (v := (Subtype.val : s → Λ)) hli (by rw [Subtype.range_coe]; exact hsp.ge)
    have hbs : ∀ x, bs x = x := fun x => by simp [bs]
    let σ : s ≃ Fin n := bs.indexEquiv e
    have hn : 0 < n := Fin.pos (σ ⟨c, hcs⟩)
    let τ : s ≃ Fin n := σ.trans (Equiv.swap (σ ⟨c, hcs⟩) ⟨0, hn⟩)
    let b' : Basis (Fin n) I Λ := bs.reindex τ
    have hb' : b' ⟨0, hn⟩ = c := by
      have : τ.symm ⟨0, hn⟩ = ⟨c, hcs⟩ := by
        rw [Equiv.symm_apply_eq]
        simp [τ]
      simp only [b', Basis.reindex_apply, this, hbs]
    have hdet : IsUnit ((e.toMatrix b').det) := by
      have := e.isUnit_det b'
      rwa [Basis.det_apply] at this
    set R : Matrix (Fin n) (Fin 1) I := coordMat (fun _ : Fin 1 => fun i => e.repr c i) with hR
    have hcol : ∀ i j, (e.toMatrix b') i (Fin.castLE (Nat.succ_le_of_lt hn) j) = R i j := by
      intro i j
      have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      simp only [Basis.toMatrix_apply, hR, coordMat, Matrix.of_apply]
      have : Fin.castLE (Nat.succ_le_of_lt hn) (0 : Fin 1) = ⟨0, hn⟩ := rfl
      rw [this, hb']
    have htop := ideal_top_of_unit (Nat.succ_le_of_lt hn) R _ hdet hcol
    rw [eq_top_iff, ← htop]
    refine Ideal.span_le.2 ?_
    rintro _ ⟨t, rfl⟩
    show (R.submatrix t id).det ∈ Ideal.span (Set.range (e.repr c))
    rw [Matrix.det_unique]
    exact Ideal.subset_span ⟨t default, rfl⟩
  · intro h
    have hn : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0
        exfalso
        have : Set.range (e.repr c) = ∅ := by
          ext x; simp only [Set.mem_range, Set.mem_empty_iff_false, iff_false]
          rintro ⟨i, _⟩; exact i.elim0
        rw [this, Ideal.span_empty] at h
        exact bot_ne_top h
      · exact h0
    obtain ⟨B, hB⟩ := exists_basis_of_unit_ideal hn (fun i => e.repr c i) h
    let b'' : Basis (Fin n) I Λ := B.map e.equivFun.symm
    refine ⟨Set.range b'', ⟨Fin.castLE hn 0, ?_⟩, (linearIndepOn_id_range_iff b''.injective).2 b''.linearIndependent, b''.span_eq⟩
    simp only [b'', Basis.map_apply, hB]
    exact e.equivFun.symm_apply_eq.2 rfl

end QuadFormsKB.Cassels
