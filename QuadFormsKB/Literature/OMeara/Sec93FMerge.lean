/-
# O'Meara 93:28, proof of the necessity, step 2: merging the tail of a Jordan splitting (93:3 with a block base)

**Setting** (as in `Sec93D3.lean`): $R$ a discrete valuation ring with fraction field $F$, $2 \in F^\times$, a
finite-dimensional quadratic space $(V, Q)$, lattices `Submodule R V`. "Hyperbolic" for the space $FK$ spanned by a
lattice is carried, as in `D93.unimodular_of_maxFor`, by a totally isotropic subspace $T \subseteq FK$ with
$\operatorname{rank} K \le 2\dim T$.

**Proves** (O'Meara 1963, 93:3, pp. 252–253, and its use in the proof of 93:28, p. 270)
* `pairSpan_cons`: the lattice spanned by a family of pairs with one more pair;
* `blocks_of_maxFor`: the induction of 93:3 also produces a base of the maximal lattice $K$ consisting of blocks
  $A(c_k, 0)$: $K = (\mathfrak oy_1 + \mathfrak ox_1) \perp \cdots$, $Q(x_k) = 0$, $B(y_k, x_k) = 1$;
* `exists_unimodular_blocks`: **93:3 on the subspace $FL$**: a lattice $L$ of scale $\mathfrak o$ whose space $FL$ is
  hyperbolic lies in a unimodular lattice $K \subseteq FL$ with $\mathfrak gK = \mathfrak gL$, and $K$ has such a
  block base.
-/
import QuadFormsKB.Literature.OMeara.Sec93FNecBlock
import QuadFormsKB.Literature.OMeara.Sec93D3

open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.Merge28

open NecBlock D93

section Blocks

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- The pairs `Fin.cons p z` span $\mathfrak op_1 + \mathfrak op_2 + \mathrm{pairSpan}(z)$. -/
theorem pairSpan_cons {m : ℕ} (p : V × V) (z : Fin m → V × V) :
    pairSpan R (Fin.cons p z : Fin (m + 1) → V × V) = span R {p.1, p.2} ⊔ pairSpan R z := by
  apply le_antisymm
  · rw [pairSpan, span_le]
    rintro _ (⟨k, rfl⟩ | ⟨k, rfl⟩) <;> refine Fin.cases ?_ (fun k' => ?_) k
    · exact mem_sup_left (subset_span (by simp))
    · exact mem_sup_right (subset_span (Or.inl ⟨k', by simp⟩))
    · exact mem_sup_left (subset_span (by simp))
    · exact mem_sup_right (subset_span (Or.inr ⟨k', by simp⟩))
  · refine sup_le ?_ ?_
    · rw [span_le]
      intro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl
      · exact subset_span (Or.inl ⟨0, by simp⟩)
      · exact subset_span (Or.inr ⟨0, by simp⟩)
    · rw [pairSpan, span_le]
      rintro _ (⟨k, rfl⟩ | ⟨k, rfl⟩)
      · exact subset_span (Or.inl ⟨k.succ, by simp⟩)
      · exact subset_span (Or.inr ⟨k.succ, by simp⟩)

/-- The conditions on a block base `x` of a lattice `K`: $K$ is spanned by the pairs, the second vectors are
isotropic, $B(x_k^{(1)}, x_k^{(2)}) = 1$, and distinct pairs are orthogonal (matrix $A(c_1,0) \perp \cdots \perp
A(c_m, 0)$). -/
def IsBlockBase (K : Submodule R V) {m : ℕ} (x : Fin m → V × V) : Prop :=
  pairSpan R x = K ∧ (∀ k, Q (x k).2 = 0) ∧ (∀ k, bil Q (x k).1 (x k).2 = 1) ∧
    (∀ k l, k ≠ l → bil Q (x k).1 (x l).1 = 0) ∧ (∀ k l, k ≠ l → bil Q (x k).1 (x l).2 = 0) ∧
    (∀ k l, k ≠ l → bil Q (x k).2 (x l).2 = 0)

/-- **The induction of 93:3 with a block base** (O'Meara 1963, p. 253, as `D93.unimodular_of_maxFor`): a maximal
lattice $K$ (`MaxFor`) with $\mathfrak sK \subseteq \mathfrak o$, $\mathfrak gK \subseteq G$ in a space $FK$
containing a totally isotropic $T$ with $\operatorname{rank}K \le 2\dim T$ has a base of blocks $A(c_k, 0)$. -/
theorem blocks_of_maxFor [FiniteDimensional F V] {G : AddSubgroup F} (hG2 : ∀ r : R, 2 * algebraMap R F r ∈ G) :
    ∀ (n : ℕ) (K : Submodule R V), finrank R K = n → K.FG → scale Q K ≤ 1 → normGroup Q K ≤ G →
      MaxFor Q G K → (∃ T : Submodule F V, (∀ t ∈ T, Q t = 0) ∧ (∀ t ∈ T, t ∈ span F (K : Set V)) ∧
        n ≤ 2 * finrank F T) → ∃ m, ∃ x : Fin m → V × V, IsBlockBase Q K x := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K hrk hKfg hKs hKG hmax ⟨T, hTiso, hTK, hTdim⟩
  by_cases hK0 : K = ⊥
  · refine ⟨0, Fin.elim0, ?_, fun k => k.elim0, fun k => k.elim0, fun k => k.elim0, fun k => k.elim0,
      fun k => k.elim0⟩
    rw [hK0, pairSpan, Set.range_eq_empty, Set.range_eq_empty, Set.union_empty, span_empty]
  have hn1 : 1 ≤ n := hrk ▸ one_le_finrank_of_ne_bot (F := F) hK0
  have hT0 : T ≠ ⊥ := by
    rintro rfl
    simp at hTdim; omega
  obtain ⟨t, htT, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hT0
  obtain ⟨x, hxm, c, hc0, hxt⟩ := exists_isMaxVec_smul hKfg ht0 (hTK t htT)
  have hxT : x ∈ T := by
    have : x = c⁻¹ • t := by rw [hxt, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [this]; exact T.smul_mem _ htT
  have hQx : Q x = 0 := hTiso x hxT
  obtain ⟨k, hk, u, hu, hxk⟩ := exists_unit_bil_of_maxFor Q hG2 hKfg hKs hKG hmax hxm hQx
  obtain ⟨u', hu'⟩ := hu.exists_left_inv
  have hyK : u' • k ∈ K := K.smul_mem u' hk
  have hxy : bil Q x (u' • k) = 1 := by rw [bil_rsmul_right, hxk, ← map_mul, hu', map_one]
  obtain ⟨J, K', hsplit, hJ, hJrk, hxJ, hyJ, hJspan⟩ := exists_split_pair Q hKs hxm.1 hyK hQx hxy
  set y := u' • k with hy
  have hJle : J ≤ K := hsplit.sup_eq ▸ le_sup_left
  have hK'le : K' ≤ K := hsplit.sup_eq ▸ le_sup_right
  have hJfg : J.FG := FG.of_le hKfg hJle
  have hK'fg : K'.FG := FG.of_le hKfg hK'le
  have hrank : n = 2 + finrank R K' := by rw [← hrk, isOrthSum_finrank Q hsplit hKfg, hJrk]
  have hreg : IsRegular Q J := IsModular.isRegular Q hJ hJfg
  have hJ0 : J ≠ ⊥ := by
    rintro rfl; simp at hJrk
  have horthspan : ∀ j ∈ J, ∀ w ∈ span F (K' : Set V), bil Q j w = 0 := fun j hj w hw =>
    bil_zero_of_mem_span_F Q (fun z hz => hsplit.orth j hj z hz) hw
  -- maximality of `K'`
  have hmax' : MaxFor Q G K' := by
    intro M' hM'fg hK'M' hM'span hM's hM'G
    have horth : ∀ a ∈ J, ∀ b ∈ M', bil Q a b = 0 := fun a ha b hb => horthspan a ha b (hM'span b hb)
    have hM : J ⊔ M' = K := by
      apply hmax (J ⊔ M') (hJfg.sup hM'fg)
      · rw [← hsplit.sup_eq]; exact sup_le_sup_left hK'M' J
      · intro m hm
        obtain ⟨j, hj, m', hm', rfl⟩ := mem_sup.1 hm
        exact add_mem (subset_span (hJle hj))
          (span_mono (SetLike.coe_subset_coe.2 hK'le) (hM'span m' hm'))
      · rw [scale_sup_of_orth Q horth]; exact sup_le ((scale_mono Q hJle).trans hKs) hM's
      · rw [normGroup_sup_of_orth Q horth]; exact sup_le ((normGroup_mono Q hJle).trans hKG) hM'G
    apply le_antisymm _ hK'M'
    intro m' hm'
    have : m' ∈ J ⊔ K' := by rw [hsplit.sup_eq, ← hM]; exact mem_sup_right hm'
    obtain ⟨j, hj, k', hk', hjk⟩ := mem_sup.1 this
    have hj0 : j = 0 := by
      refine hreg j hj fun j'' hj'' => ?_
      have hjspan : j ∈ span F (K' : Set V) := by
        have : j = m' - k' := by rw [eq_sub_iff_add_eq]; exact hjk
        rw [this]; exact sub_mem (hM'span m' hm') (subset_span hk')
      rw [bil_comm]; exact horthspan j'' hj'' j hjspan
    rw [hj0, zero_add] at hjk
    rw [← hjk]; exact hk'
  -- the totally isotropic subspace of `FK'`
  set φ : V →ₗ[F] F := QuadraticMap.associated Q y with hφ
  have hxT_orth : ∀ t ∈ T, bil Q x t = 0 := by
    intro t ht
    have h1 := Q_add Q x t
    rw [hTiso _ (T.add_mem hxT ht), hQx, hTiso t ht] at h1
    have h2F : (2 : F) ≠ 0 := two_ne_zero
    have : 2 * bil Q x t = 0 := by linear_combination (-1 : F) * h1
    exact (mul_eq_zero.1 this).resolve_left h2F
  have hT'span : ∀ t ∈ T ⊓ LinearMap.ker φ, t ∈ span F (K' : Set V) := by
    intro t ht
    obtain ⟨d, hd0, hd⟩ := exists_smul_mem_of_mem_span (F := F) (S := K) (hTK t ht.1)
    obtain ⟨j, hj, k', hk', hjk⟩ := mem_sup.1 (hsplit.sup_eq ▸ hd : d • t ∈ J ⊔ K')
    have hj_eq : j = d • t - k' := eq_sub_of_add_eq hjk
    have hjx : bil Q j x = 0 := by
      rw [hj_eq, bil_sub_left, bil_rsmul_left, bil_comm Q t x, hxT_orth t ht.1, mul_zero,
        bil_comm Q k' x, hsplit.orth x hxJ k' hk', sub_zero]
    have hjy : bil Q j y = 0 := by
      have hty : bil Q t y = 0 := by
        rw [bil_comm]; exact LinearMap.mem_ker.1 ht.2
      rw [hj_eq, bil_sub_left, bil_rsmul_left, hty, mul_zero, bil_comm Q k' y,
        hsplit.orth y hyJ k' hk', sub_zero]
    have hj0 : j = 0 := by
      refine hreg j hj fun j'' hj'' => ?_
      obtain ⟨a, b, rfl⟩ := hJspan j'' hj''
      rw [bil_add_right, bil_rsmul_right, bil_rsmul_right, hjx, hjy]; simp
    rw [hj0, zero_add] at hjk
    have hdF : algebraMap R F d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).2 hd0
    have : t = (algebraMap R F d)⁻¹ • k' := by
      rw [hjk, ← algebraMap_smul F d t, smul_smul, inv_mul_cancel₀ hdF, one_smul]
    rw [this]
    exact (span F (K' : Set V)).smul_mem _ (subset_span hk')
  have hdim : finrank R K' ≤ 2 * finrank F (T ⊓ LinearMap.ker φ : Submodule F V) := by
    have := finrank_le_finrank_inf_ker_add_one T φ
    omega
  have hK'rk : finrank R K' < n := by omega
  obtain ⟨m', x', hx'span, hx'2, hx'12, hx'11, hx'12', hx'22⟩ := ih (finrank R K') hK'rk K' rfl hK'fg
    ((scale_mono Q hK'le).trans hKs) ((normGroup_mono Q hK'le).trans hKG) hmax'
    ⟨T ⊓ LinearMap.ker φ, fun t ht => hTiso t ht.1, hT'span, hdim⟩
  have hJeq : J = span R {y, x} := by
    apply le_antisymm
    · intro j hj
      obtain ⟨a, b, rfl⟩ := hJspan j hj
      exact add_mem (smul_mem _ _ (subset_span (by simp))) (smul_mem _ _ (subset_span (by simp)))
    · rw [span_le]; intro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl
      · exact hyJ
      · exact hxJ
  have hK'mem : ∀ k, (x' k).1 ∈ K' ∧ (x' k).2 ∈ K' := fun k =>
    ⟨hx'span ▸ subset_span (Or.inl ⟨k, rfl⟩), hx'span ▸ subset_span (Or.inr ⟨k, rfl⟩)⟩
  have hyx : bil Q y x = 1 := by rw [bil_comm]; exact hxy
  refine ⟨m' + 1, Fin.cons (y, x) x', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pairSpan_cons, hx'span, ← hJeq, hsplit.sup_eq]
  · intro k; refine Fin.cases ?_ (fun k' => ?_) k
    · simpa using hQx
    · simpa using hx'2 k'
  · intro k; refine Fin.cases ?_ (fun k' => ?_) k
    · simpa using hyx
    · simpa using hx'12 k'
  all_goals
    intro k l hkl
    refine Fin.cases (fun hkl => ?_) (fun k' hkl => ?_) k hkl <;>
      refine Fin.cases (fun hkl => ?_) (fun l' hkl => ?_) l hkl
    · exact absurd rfl hkl
    · simp only [Fin.cons_zero, Fin.cons_succ]
      first
        | exact hsplit.orth _ hyJ _ (hK'mem l').1
        | exact hsplit.orth _ hyJ _ (hK'mem l').2
        | exact hsplit.orth _ hxJ _ (hK'mem l').2
    · simp only [Fin.cons_zero, Fin.cons_succ]
      first
        | (rw [bil_comm]; exact hsplit.orth _ hyJ _ (hK'mem k').1)
        | (rw [bil_comm]; exact hsplit.orth _ hxJ _ (hK'mem k').1)
        | (rw [bil_comm]; exact hsplit.orth _ hxJ _ (hK'mem k').2)
    · simp only [Fin.cons_succ]
      have hkl' : k' ≠ l' := fun h => hkl (by rw [h])
      first
        | exact hx'11 k' l' hkl'
        | exact hx'12' k' l' hkl'
        | exact hx'22 k' l' hkl'

/-- **Proposition 93:3 on the subspace $FL$, with a block base** (O'Meara 1963, pp. 252–253, as used on p. 270 for
$FL^*_{(i+1)}$): let $L$ be a regular lattice of scale $\mathfrak o$ such that $FL$ contains a totally isotropic
subspace $T$ with $\operatorname{rank} L \le 2\dim T$ ($FL$ hyperbolic). Then there is a unimodular lattice $K$ with
$L \subseteq K \subseteq FL$, $\mathfrak gK = \mathfrak gL$, and $K$ has a base of blocks $A(c_k, 0)$. -/
@[kb "omeara1963" "§93A, 93:3, pp. 252–253 (on the subspace FL, with a block base)"]
theorem exists_unimodular_blocks [FiniteDimensional F V] {L : Submodule R V} (hLfg : L.FG) (hLreg : IsRegular Q L)
    (hs : scale Q L = 1) {T : Submodule F V} (hTiso : ∀ t ∈ T, Q t = 0) (hTL : ∀ t ∈ T, t ∈ span F (L : Set V))
    (hTdim : finrank R L ≤ 2 * finrank F T) :
    ∃ K : Submodule R V, L ≤ K ∧ (∀ k ∈ K, k ∈ span F (L : Set V)) ∧ K.FG ∧ IsUnimodular Q K ∧
      normGroup Q K = normGroup Q L ∧ finrank R K = finrank R L ∧ ∃ m, ∃ x : Fin m → V × V, IsBlockBase Q K x := by
  set G := normGroup Q L with hG
  have hG2 : ∀ r : R, 2 * algebraMap R F r ∈ G := fun r =>
    two_mul_mem_normGroup Q (by rw [hs]; exact Submodule.mem_one.2 ⟨r, rfl⟩)
  have hDfg : (dual Q L).FG := dual_fg Q hLfg hLreg
  let S : Set (Submodule R V) :=
    {M | L ≤ M ∧ (∀ m ∈ M, m ∈ span F (L : Set V)) ∧ scale Q M ≤ 1 ∧ normGroup Q M ≤ G}
  have hLS : L ∈ S := ⟨le_rfl, fun m hm => subset_span hm, hs.le, le_rfl⟩
  have hle : ∀ M ∈ S, M ≤ dual Q L := fun M hM m hm =>
    ⟨hM.2.1 m hm, fun y hy => hM.2.2.1 (bil_mem_scale Q hm (hM.1 hy))⟩
  obtain ⟨K, hKS, hKmax⟩ := exists_maximal_bounded S ⟨L, hLS⟩ hDfg hle
  have hKfg : K.FG := FG.of_le hDfg (hle K hKS)
  have hspanK : span F (K : Set V) = span F (L : Set V) := by
    apply le_antisymm
    · rw [span_le]; exact fun k hk => hKS.2.1 k hk
    · exact span_mono (SetLike.coe_subset_coe.2 hKS.1)
  have hmax : MaxFor Q G K := fun M _ hKM hMspan hMs hMG =>
    hKmax M ⟨hKS.1.trans hKM, fun m hm => hspanK ▸ hMspan m hm, hMs, hMG⟩ hKM
  have hrk : finrank R K = finrank R L := by
    rw [finrank_eq_finrank_span (F := F) K, finrank_eq_finrank_span (F := F) L, hspanK]
  have hT : ∃ T : Submodule F V, (∀ t ∈ T, Q t = 0) ∧ (∀ t ∈ T, t ∈ span F (K : Set V)) ∧
      finrank R K ≤ 2 * finrank F T := ⟨T, hTiso, fun t ht => hspanK ▸ hTL t ht, hrk ▸ hTdim⟩
  have hU : IsUnimodular Q K := by
    rcases unimodular_of_maxFor Q hG2 (finrank R K) K rfl hKfg hKS.2.2.1 hKS.2.2.2 hmax hT with h | h
    · exfalso
      have h1 : (1 : F) ∈ scale Q K := scale_mono Q hKS.1 (by
        rw [hs]; exact Submodule.mem_one.2 ⟨1, map_one _⟩)
      rw [h, scale_bot] at h1
      exact one_ne_zero ((Submodule.mem_bot R).1 h1)
    · exact h
  exact ⟨K, hKS.1, hKS.2.1, hKfg, hU, le_antisymm hKS.2.2.2 (normGroup_mono Q hKS.1), hrk,
    blocks_of_maxFor Q hG2 (finrank R K) K rfl hKfg hKS.2.2.1 hKS.2.2.2 hmax hT⟩

end Blocks

end QuadFormsKB.OMeara.Merge28
