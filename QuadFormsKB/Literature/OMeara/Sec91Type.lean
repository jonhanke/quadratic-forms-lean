/-
# O'Meara §91C: uniqueness of the Jordan type (Theorem 91:9)

**Setting** (as in `Sec82.lean`): $R$ a discrete valuation ring with fraction field $F$, $2 \in F^\times$, a
quadratic space $(V, Q)$ over $F$, O'Meara's bilinear form $B$ = `bil Q`, lattices = `Submodule R V`.

**Proves**
* `mem_of_isModular` (O'Meara 1963, **82:14a**, p. 232): an $\mathfrak a$-modular lattice is
  $L = \{x \in FL : B(x, L) \subseteq \mathfrak a\}$;
* `subA_eq_iSup`, `subA_eq_self`, `notMem_scale_subA`: the lattice $L^{\mathfrak a}$ of a Jordan splitting
  (§91C, p. 244): $L^{\mathfrak a} = L_1^{\mathfrak a} \perp \cdots \perp L_t^{\mathfrak a}$, $L_i^{\mathfrak a} = L_i$ if $L_i$
  is $\mathfrak a$-modular, and $\mathfrak s L_i^{\mathfrak a} \subsetneq \mathfrak a$ otherwise;
* `scale_subA_eq_iff` (§91C, p. 244): $\mathfrak sL^{\mathfrak a} = \mathfrak a$ if and only if the splitting has an
  $\mathfrak a$-modular component;
* `finrank_le_of_isOrthSum` (step 2 and 3 of the proof of 91:9, pp. 244–245);
* `IsJordanSplitting.sameJordanType` (**Theorem 91:9**, p. 244): any two Jordan splittings of $L$ are of the same type
  (`SameJordanType`, the definition on p. 245): same number of components, same scales, same ranks, and
  $\mathfrak nL_i = \mathfrak sL_i \iff \mathfrak nK_i = \mathfrak sK_i$.
-/
import QuadFormsKB.Literature.OMeara.Sec91Jordan

open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **Corollary 82:14a** (O'Meara 1963, p. 232): if $J$ is $\mathfrak a$-modular, then
$J = \{x \in FJ : B(x, J) \subseteq \mathfrak a\}$. -/
@[kb "omeara1963" "§82G, 82:14a, p. 232"]
theorem mem_of_isModular {a : Submodule R F} {J : Submodule R V} (hJ : IsModular Q a J) (hJfg : J.FG)
    {x : V} (hx : x ∈ span F (J : Set V)) (hB : ∀ z ∈ J, bil Q x z ∈ a) : x ∈ J := by
  obtain ⟨α, hα, rfl, b, U, hU, hG⟩ := exists_gram_of_isModular Q hJ hJfg
  obtain ⟨y, hy, hxy⟩ := exists_mem_bil_eq_of_gram Q b hU hG (x := x) fun j => hB _ (b j).2
  have hw : x - y ∈ span F (J : Set V) := sub_mem hx (subset_span hy)
  obtain ⟨d, hd, hdw⟩ := exists_smul_mem_of_mem_span (R := R) hw
  have h0 : d • (x - y) = 0 := hJ.isRegular Q hJfg _ hdw fun z hz => by
    rw [bil_rsmul_left, bil_sub_left, hxy z hz, sub_self, mul_zero]
  have := isTorsionFree_of_fractionRing (R := R) (F := F) (V := V)
  rcases smul_eq_zero.mp h0 with h | h
  · exact absurd h hd
  · rwa [sub_eq_zero.mp h]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] in
theorem mem_iSup_fin_iff {t : ℕ} (p : Fin t → Submodule R V) (x : V) :
    x ∈ ⨆ i, p i ↔ ∃ μ : ∀ i, p i, ∑ i, (μ i : V) = x := by
  have := mem_iSup_finset_iff_exists_sum (s := Finset.univ) p x
  simpa using this

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] in
/-- **$L^{\mathfrak a}$ of an orthogonal splitting** (O'Meara 1963, §82I, p. 237: "for any splitting
$L = J \perp K$ we have $L^{\mathfrak a} = J^{\mathfrak a} \perp K^{\mathfrak a}$"):
$L^{\mathfrak a} = \bigvee_i L_i^{\mathfrak a}$ for $L = L_1 \perp \cdots \perp L_t$. -/
@[kb "omeara1963" "§82I, p. 237 (L^a = J^a ⊥ K^a)"]
theorem subA_eq_iSup {L : Submodule R V} {t : ℕ} {Ls : Fin t → Submodule R V} (hL : IsOrthSplit Q L Ls)
    (a : Submodule R F) : subA Q a L = ⨆ i, subA Q a (Ls i) := by
  have hle : ∀ i, Ls i ≤ L := fun i => hL.iSup_eq ▸ le_iSup Ls i
  -- for `x ∈ Lᵢ` and `y = ∑ yⱼ ∈ L`, `B(x, y) = B(x, yᵢ)`
  have key : ∀ i, ∀ x ∈ Ls i, ∀ μ : ∀ j, Ls j, bil Q x (∑ j, (μ j : V)) = bil Q x (μ i) := by
    intro i x hx μ
    rw [bil_sum_right, Finset.sum_eq_single i]
    · intro j _ hj; exact hL.orth i j (Ne.symm hj) x hx _ (μ j).2
    · simp
  apply le_antisymm
  · rintro x ⟨hx, hxa⟩
    rw [← hL.iSup_eq, mem_iSup_fin_iff] at hx
    obtain ⟨μ, rfl⟩ := hx
    refine sum_mem fun i _ => mem_iSup_of_mem i ⟨(μ i).2, fun y hy => ?_⟩
    have h1 := hxa y (hle i hy)
    rw [bil_sum_left, Finset.sum_eq_single i] at h1
    · exact h1
    · intro j _ hj; rw [bil_comm]; exact hL.orth i j (Ne.symm hj) y hy _ (μ j).2
    · simp
  · refine iSup_le fun i => ?_
    rintro x ⟨hx, hxa⟩
    refine ⟨hle i hx, fun y hy => ?_⟩
    rw [← hL.iSup_eq, mem_iSup_fin_iff] at hy
    obtain ⟨μ, rfl⟩ := hy
    rw [key i x hx μ]
    exact hxa _ (μ i).2

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] in
/-- $L^{\mathfrak a} = L$ when $\mathfrak sL \subseteq \mathfrak a$ (O'Meara 1963, §82I, p. 237). -/
theorem subA_eq_self {a : Submodule R F} {L : Submodule R V} (h : scale Q L ≤ a) : subA Q a L = L :=
  le_antisymm (fun _ hx => hx.1) fun _ hx => ⟨hx, fun _ hy => h (bil_mem_scale Q hx hy)⟩

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] in
theorem scale_subA_le (a : Submodule R F) (L : Submodule R V) : scale Q (subA Q a L) ≤ a := by
  rw [scale, span_le]
  rintro _ ⟨x, hx, y, hy, rfl⟩
  exact hx.2 y hy.1

/-- **$L^{\mathfrak a}$ of a modular lattice of another scale** (O'Meara 1963, §91C, p. 244): if $J$ is
$\beta$-modular with $\beta\mathfrak o \ne \alpha\mathfrak o$, then $\mathfrak sJ^{\alpha\mathfrak o} \subsetneq
\alpha\mathfrak o$ (indeed $J^{\alpha\mathfrak o} = J$ if $\beta\mathfrak o \subsetneq \alpha\mathfrak o$, and
$J^{\alpha\mathfrak o} = \alpha\beta^{-1}J$ of scale $\alpha^2\beta^{-1}\mathfrak o$ otherwise). -/
theorem notMem_scale_subA {α β : F} (hα : α ≠ 0) {J : Submodule R V} (hJ : IsModular Q (R ∙ β) J)
    (hJfg : J.FG) (hne : R ∙ β ≠ R ∙ α) : α ∉ scale Q (subA Q (R ∙ α) J) := by
  have hβ : β ≠ 0 := by rintro rfl; exact hJ.1 (by simp)
  rcases span_pair_eq (R := R) α β with h | h
  · -- `βo ⊊ αo`: `J^a = J` and `sJ = βo`
    have hle : R ∙ β ≤ R ∙ α := sup_eq_left.mp h
    rw [subA_eq_self Q (hJ.2.1 ▸ hle), hJ.2.1]
    intro hmem
    exact hne (le_antisymm hle ((span_singleton_le_iff_mem _ _).mpr hmem))
  · -- `αo ⊊ βo`: every `x ∈ J^a` is `(α/β) j` with `j ∈ J`
    have hle : R ∙ α ≤ R ∙ β := sup_eq_right.mp h
    have hαβ : α ∈ R ∙ β := (span_singleton_le_iff_mem _ _).mp hle
    have hβα : β ∉ R ∙ α := fun hm => hne (le_antisymm ((span_singleton_le_iff_mem _ _).mpr hm) hle)
    obtain ⟨m, hm, hαm⟩ :=
      exists_maximalIdeal_mul_of_mem_of_notMem (R := R) (mem_span_singleton_self α) hβα
    -- elements of `J^a` lie in `(α/β) J`
    have hsub : ∀ x ∈ subA Q (R ∙ α) J, ∃ j ∈ J, x = algebraMap R F m • j := by
      rintro x ⟨hx, hxa⟩
      have hm0 : algebraMap R F m ≠ 0 := by
        intro h0; rw [h0, zero_mul] at hαm; exact hα hαm
      refine ⟨(algebraMap R F m)⁻¹ • x, mem_of_isModular Q hJ hJfg ?_ fun z hz => ?_, ?_⟩
      · exact smul_mem _ _ (subset_span hx)
      · obtain ⟨c, hc⟩ := mem_span_singleton.mp (hxa z hz)
        rw [bil_smul_left, ← hc, Algebra.smul_def, hαm]
        refine mem_span_singleton.mpr ⟨c, ?_⟩
        rw [Algebra.smul_def]; field_simp
      · rw [smul_smul, mul_inv_cancel₀ hm0, one_smul]
    intro hmem
    have hle' : scale Q (subA Q (R ∙ α) J) ≤ R ∙ (algebraMap R F m * α) := by
      rw [scale, span_le]
      rintro _ ⟨x, hx, y, hy, rfl⟩
      obtain ⟨j, hj, rfl⟩ := hsub x hx
      rw [bil_smul_left]
      obtain ⟨c, hc⟩ := mem_span_singleton.mp (hy.2 j hj)
      rw [bil_comm, ← hc, Algebra.smul_def]
      exact mem_span_singleton.mpr ⟨c, by rw [Algebra.smul_def]; ring⟩
    obtain ⟨c, hc⟩ := mem_span_singleton.mp (hle' hmem)
    rw [Algebra.smul_def, ← mul_assoc, ← map_mul] at hc
    have h1 : c * m = 1 := by
      apply IsFractionRing.injective R F
      rw [map_one]
      exact mul_right_cancel₀ hα (by rw [one_mul]; exact hc)
    exact (mem_maximalIdeal _).mp hm (IsUnit.of_mul_eq_one_right c h1)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] in
/-- The scale of a pairwise orthogonal family is contained in the sum of the scales (O'Meara 1963, §82E,
p. 227). -/
theorem scale_iSup_le {ι : Type*} {Ls : ι → Submodule R V}
    (horth : ∀ i j, i ≠ j → ∀ x ∈ Ls i, ∀ y ∈ Ls j, bil Q x y = 0) :
    scale Q (⨆ i, Ls i) ≤ ⨆ i, scale Q (Ls i) := by
  classical
  rw [scale, span_le]
  rintro _ ⟨x, hx, y, hy, rfl⟩
  refine iSup_induction Ls (motive := fun x => bil Q x y ∈ ⨆ i, scale Q (Ls i)) hx ?_ (by simp [bil])
    (fun x x' h h' => by rw [bil_add_left]; exact add_mem h h')
  intro i x hx
  refine iSup_induction Ls (motive := fun y => bil Q x y ∈ ⨆ i, scale Q (Ls i)) hy ?_ (by simp [bil])
    (fun y y' h h' => by rw [bil_add_right]; exact add_mem h h')
  intro j y hy
  by_cases hij : i = j
  · subst hij; exact mem_iSup_of_mem i (bil_mem_scale Q hx hy)
  · rw [horth i j hij x hx y hy]; exact zero_mem _

/-- In a valuation ring, a finite sum of finitely generated submodules of $F$ none of which contains $\alpha \ne 0$
does not contain $\alpha$. -/
theorem notMem_iSup_of_fg {ι : Type*} [Finite ι] {S : ι → Submodule R F} (hS : ∀ i, (S i).FG) {α : F}
    (hα : α ≠ 0) (h : ∀ i, α ∉ S i) : α ∉ ⨆ i, S i := by
  have hfg : (span R (⋃ i, (S i : Set F))).FG := by
    rw [span_iUnion]; simp only [span_eq]; exact fg_iSup S hS
  obtain ⟨γ, hγ, hspan⟩ := exists_mem_span_eq_singleton (R := R) hfg
  rw [span_iUnion] at hspan
  simp only [span_eq] at hspan
  rw [hspan]
  intro hmem
  rcases hγ with hγ | rfl
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hγ
    exact h i ((span_singleton_le_iff_mem _ _).mpr hi hmem)
  · exact hα (by simpa using hmem)

/-- **The modular component of scale $\mathfrak a$ splits $L^{\mathfrak a}$** (O'Meara 1963, §91C, p. 244): for a
Jordan splitting $L = L_1 \perp \cdots \perp L_t$ with $L_i$ $\mathfrak a$-modular,
$L^{\mathfrak a} = L_i \perp M'$ with $M' = \bigvee_{j \ne i} L_j^{\mathfrak a}$ and
$\mathfrak sM' \subsetneq \mathfrak a$. -/
theorem isOrthSum_subA {L : Submodule R V} (hfg : L.FG) {t : ℕ} {Ls : Fin t → Submodule R V}
    (hL : IsJordanSplitting Q L Ls) (i : Fin t) :
    IsOrthSum Q (subA Q (scale Q (Ls i)) L) (Ls i) (⨆ j : {j // j ≠ i}, subA Q (scale Q (Ls i)) (Ls j)) ∧
      ¬ scale Q (Ls i) ≤ scale Q (⨆ j : {j // j ≠ i}, subA Q (scale Q (Ls i)) (Ls j)) := by
  have hle : ∀ j, Ls j ≤ L := fun j => hL.split.iSup_eq ▸ le_iSup Ls j
  have hfgj : ∀ j, (Ls j).FG := fun j => FG.of_le hfg (hle j)
  set a := scale Q (Ls i) with ha
  obtain ⟨α, hα, haα⟩ := exists_eq_span_singleton (R := R) (scale_fg Q (hfgj i)) (hL.modular i).1
  set M' := ⨆ j : {j // j ≠ i}, subA Q a (Ls j) with hM'
  have hM'le : ∀ y ∈ M', ∀ x ∈ Ls i, bil Q y x = 0 := by
    intro y hy x hx
    refine iSup_induction _ (motive := fun y => bil Q y x = 0) hy ?_ (by simp [bil])
      (fun y y' h h' => by rw [bil_add_left, h, h', add_zero])
    intro j y hy
    exact hL.split.orth j i j.2 y hy.1 x hx
  refine ⟨⟨fun x hx y hy => by rw [bil_comm]; exact hM'le y hy x hx, ?_, ?_⟩, ?_⟩
  · rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨hxi, hxM⟩
    exact (mem_bot R).mpr ((hL.modular i).isRegular Q (hfgj i) x hxi fun z hz => hM'le x hxM z hz)
  · rw [subA_eq_iSup Q hL.split, iSup_split_single _ i, subA_eq_self Q le_rfl, hM', iSup_subtype']
  · have haα' : a = R ∙ α := haα
    rw [haα']
    intro hsub
    have hmem : α ∈ scale Q M' := hsub (mem_span_singleton_self α)
    have horth : ∀ j k : {j // j ≠ i}, j ≠ k → ∀ x ∈ subA Q a (Ls j), ∀ y ∈ subA Q a (Ls k),
        bil Q x y = 0 := fun j k hjk x hx y hy =>
      hL.split.orth j k (fun h => hjk (Subtype.ext h)) x hx.1 y hy.1
    have hsubfg : ∀ j : Fin t, (subA Q a (Ls j)).FG :=
      fun j => FG.of_le (hfgj j) (fun x (hx : x ∈ subA Q a (Ls j)) => hx.1)
    refine notMem_iSup_of_fg (S := fun j : {j // j ≠ i} => scale Q (subA Q a (Ls j)))
      (fun j => scale_fg Q (hsubfg j)) hα (fun j => ?_) (scale_iSup_le Q horth hmem)
    -- the other components have scale different from `a`
    have hmodj := hL.modular j
    obtain ⟨β, -, hβ⟩ := exists_eq_span_singleton (R := R) (scale_fg Q (hfgj j)) hmodj.1
    have hj : scale Q (Ls j) ≠ a := fun h => j.2 (hL.scale_strictAnti.injective h)
    rw [hβ] at hmodj hj
    rw [haα'] at hj ⊢
    exact notMem_scale_subA Q hα hmodj (hfgj j) hj

/-- **Steps 2 and 3 of the proof of 91:9** (O'Meara 1963, pp. 244–245). Let $M_1 \subseteq M$ and
$M = N_1 \perp N'$ with $M_1$, $N_1$ $\mathfrak a$-modular and $\mathfrak sN' \subsetneq \mathfrak a$. Then
$\operatorname{rank} M_1 \le \operatorname{rank} N_1$, and $\mathfrak nM_1 = \mathfrak a$ implies $\mathfrak nN_1 =
\mathfrak a$. *Proof:* write a base $x_i$ of $M_1$ as $x_i = y_i + z_i$ with $y_i \in N_1$, $z_i \in N'$ (O'Meara's
projection $\varphi x_i = y_i$); then $B(y_i, y_j) \equiv B(x_i, x_j) \bmod \alpha\mathfrak p$, so the matrix of the
$y_i$ is $\alpha$ times a matrix that is invertible over $\mathfrak o$, and the $y_i$ are independent in $N_1$;
similarly $Q(\varphi x) \equiv Q(x) \bmod \alpha\mathfrak p$. -/
@[kb "omeara1963" "§91C, proof of 91:9, steps 2–3, pp. 244–245"]
theorem finrank_le_of_isOrthSum {a : Submodule R F} {M M₁ N₁ N' : Submodule R V} (hMfg : M.FG)
    (hM₁M : M₁ ≤ M) (hN : IsOrthSum Q M N₁ N') (hM₁ : IsModular Q a M₁) (hN₁ : IsModular Q a N₁)
    (hN' : ¬ a ≤ scale Q N') :
    finrank R M₁ ≤ finrank R N₁ ∧ (normIdeal Q M₁ = a → normIdeal Q N₁ = a) := by
  obtain ⟨α, hα, rfl, b, U, hU, hG⟩ := exists_gram_of_isModular Q hM₁ (FG.of_le hMfg hM₁M)
  have hN₁M : N₁ ≤ M := hN.sup_eq ▸ le_sup_left
  have hαN' : α ∉ scale Q N' := fun h => hN' ((span_singleton_le_iff_mem _ _).mpr h)
  -- elements of `s N'` are `m α` with `m ∈ 𝔭`
  have hsmall : ∀ c ∈ scale Q N', ∃ m ∈ maximalIdeal R, c = algebraMap R F m * α :=
    fun c hc => exists_maximalIdeal_mul_of_mem_of_notMem (R := R) hc hαN'
  -- decompose `x ∈ M` as `y + z`
  have hdec : ∀ x ∈ M, ∃ y ∈ N₁, ∃ z ∈ N', x = y + z := by
    intro x hx
    rw [← hN.sup_eq] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup.mp hx
    exact ⟨y, hy, z, hz, rfl⟩
  have horth' : ∀ z ∈ N', ∀ y ∈ N₁, bil Q z y = 0 := fun z hz y hy => by
    rw [bil_comm]; exact hN.orth y hy z hz
  choose y hy z hz hyz using fun i => hdec (b i) (hM₁M (b i).2)
  refine ⟨?_, ?_⟩
  · -- the matrix of the `y i`
    have hentry : ∀ i j, ∃ m ∈ maximalIdeal R, bil Q (y i) (y j) = α * algebraMap R F (U i j - m) := by
      intro i j
      have h1 : bil Q (y i) (y j) = bil Q (b i : V) (b j : V) - bil Q (z i) (z j) := by
        rw [hyz i, hyz j, bil_add_left, bil_add_right, bil_add_right,
          hN.orth _ (hy i) _ (hz j), horth' _ (hz i) _ (hy j)]
        ring
      obtain ⟨m, hm, hm'⟩ := hsmall _ (bil_mem_scale Q (hz i) (hz j))
      refine ⟨m, hm, ?_⟩
      have hGij : bil Q (b i : V) (b j : V) = α * algebraMap R F (U i j) := by
        simpa [gram] using congrFun (congrFun hG i) j
      rw [h1, hGij, hm', map_sub]; ring
    choose m hm hm' using hentry
    let U' : Matrix (Fin (finrank R M₁)) (Fin (finrank R M₁)) R := U - Matrix.of m
    have hU' : IsUnit U'.det := by
      have hres : (residue R).mapMatrix U' = (residue R).mapMatrix U := by
        ext i j
        simp only [U', RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.of_apply,
          map_sub, (residue_eq_zero_iff _).mpr (hm i j), sub_zero]
      have h1 : residue R U'.det = residue R U.det := by
        rw [RingHom.map_det, RingHom.map_det, hres]
      by_contra hcon
      have h2 : residue R U.det = 0 := by
        rw [← h1]; exact (residue_eq_zero_iff _).mpr ((mem_maximalIdeal _).mpr hcon)
      rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff] at h2
      exact h2 hU
    have hGy : gram Q y = α • U'.map (algebraMap R F) := by
      ext i j
      simp only [gram, Matrix.of_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, U',
        Matrix.sub_apply]
      exact hm' i j
    by_cases hr : finrank R M₁ = 0
    · rw [hr]; exact Nat.zero_le _
    have : Nonempty (Fin (finrank R M₁)) := ⟨⟨0, Nat.pos_of_ne_zero hr⟩⟩
    obtain ⟨-, hrk⟩ := isModular_span_of_gram Q hα hU' hGy
    have hle : span R (Set.range y) ≤ N₁ := by rw [span_le]; rintro _ ⟨i, rfl⟩; exact hy i
    have := finrank_le_of_le (F := F) hle (FG.of_le hMfg hN₁M)
    rw [hrk, Fintype.card_fin] at this
    exact this
  · -- the norm
    intro hn
    obtain ⟨x, hx, hxn⟩ := exists_normIdeal_eq Q (FG.of_le hMfg hM₁M)
    rw [hn] at hxn
    obtain ⟨ε, hε⟩ := mem_span_singleton.mp (hxn ▸ mem_span_singleton_self α)
    obtain ⟨δ, hδ⟩ := mem_span_singleton.mp (hxn.symm ▸ mem_span_singleton_self (Q x))
    -- `Q x = δ α` with `δ` a unit
    have hδu : IsUnit δ := by
      refine IsUnit.of_mul_eq_one_right ε (IsFractionRing.injective R F ?_)
      rw [map_mul, map_one]
      apply mul_right_cancel₀ hα
      rw [Algebra.smul_def] at hε hδ
      rw [mul_assoc, hδ, hε, one_mul]
    obtain ⟨yx, hyx, zx, hzx, rfl⟩ := hdec x (hM₁M hx)
    have hQ : Q (yx + zx) = Q yx + Q zx := by rw [Q_add, hN.orth _ hyx _ hzx]; ring
    obtain ⟨m, hm, hm'⟩ := hsmall _ (normIdeal_le_scale Q N' (Q_mem_normIdeal Q hzx))
    have hu : IsUnit (δ - m) := by
      have := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (m * ↑hδu.unit⁻¹)
        (Ideal.mul_mem_right _ _ hm)
      have e : δ - m = (1 - m * ↑hδu.unit⁻¹) * δ := by
        rw [sub_mul, one_mul, mul_assoc, IsUnit.val_inv_mul, mul_one]
      rw [e]; exact this.mul hδu
    have hQy : Q yx = algebraMap R F (δ - m) * α := by
      rw [map_sub, sub_mul, ← hm', ← Algebra.smul_def, hδ, hQ]; ring
    apply le_antisymm (hN₁.2.1 ▸ normIdeal_le_scale Q N₁)
    rw [span_singleton_le_iff_mem]
    obtain ⟨u, hu'⟩ := hu
    have : α = (↑u⁻¹ : R) • Q yx := by
      rw [hQy, Algebra.smul_def, ← mul_assoc, ← map_mul, ← hu', Units.inv_mul, map_one, one_mul]
    rw [this]
    exact smul_mem _ _ (Q_mem_normIdeal Q hyx)

/-- Two strictly antitone sequences $f : \{0..t-1\} \to \alpha$, $g : \{0..t'-1\} \to \alpha$ in a partial order with
the same set of values are equal: $t = t'$ and $f_i = g_i$. -/
theorem eq_of_strictAnti_of_range_eq {α : Type*} [PartialOrder α] {t t' : ℕ} {f : Fin t → α}
    {g : Fin t' → α} (hf : StrictAnti f) (hg : StrictAnti g) (hfg : ∀ i, ∃ j, g j = f i)
    (hgf : ∀ j, ∃ i, f i = g j) : ∃ h : t = t', ∀ i, f i = g (Fin.cast h i) := by
  -- equality on the common indices, by strong induction
  have key : ∀ n, ∀ (i : Fin t) (j : Fin t'), i.val = n → j.val = n → f i = g j := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro i j hi hj
    obtain ⟨j', hj'⟩ := hfg i
    obtain ⟨i', hi'⟩ := hgf j
    -- `j' ≥ n`: otherwise `f i = g j' = f ⟨j'⟩` with `j' < n`
    have hj'n : n ≤ j'.val := by
      by_contra hlt; push Not at hlt
      have hit : j'.val < t := lt_trans hlt (hi ▸ i.2)
      have := ih j'.val hlt ⟨j'.val, hit⟩ j' rfl rfl
      rw [hj'] at this
      have := hf.injective this
      rw [Fin.ext_iff] at this; simp at this; omega
    have hi'n : n ≤ i'.val := by
      by_contra hlt; push Not at hlt
      have hjt : i'.val < t' := lt_trans hlt (hj ▸ j.2)
      have := ih i'.val hlt i' ⟨i'.val, hjt⟩ rfl rfl
      rw [hi'] at this
      have := hg.injective this
      rw [Fin.ext_iff] at this; simp at this; omega
    rcases Nat.eq_or_lt_of_le hj'n with h1 | h1
    · rw [← hj']; congr 1; ext; omega
    rcases Nat.eq_or_lt_of_le hi'n with h2 | h2
    · rw [← hi']; congr 1; ext; omega
    exfalso
    have a1 : f i' < f i := hf (show i < i' by rw [Fin.lt_def]; omega)
    have a2 : g j' < g j := hg (show j < j' by rw [Fin.lt_def]; omega)
    rw [hi', ← hj'] at a1
    exact lt_asymm a1 a2
  have htt : t = t' := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · obtain ⟨i, hi⟩ := hgf ⟨t, h⟩
      have := key i.val i ⟨i.val, by omega⟩ rfl rfl
      rw [this] at hi
      have := hg.injective hi; rw [Fin.ext_iff] at this; simp at this; omega
    · obtain ⟨j, hj⟩ := hfg ⟨t', h⟩
      have := key j.val ⟨j.val, by omega⟩ j rfl rfl
      rw [← this] at hj
      have := hf.injective hj; rw [Fin.ext_iff] at this; simp at this; omega
  exact ⟨htt, fun i => key i.val i (Fin.cast htt i) rfl rfl⟩

/-- **Jordan splittings of the same type** (O'Meara 1963, §91C, p. 245): Jordan splittings
$L = L_1 \perp \cdots \perp L_t$ and $K = K_1 \perp \cdots \perp K_{t'}$ (of lattices in possibly different quadratic
spaces) are of the same type if $t = t'$ and for every $i$: $\mathfrak sL_i = \mathfrak sK_i$,
$\dim L_i = \dim K_i$, and $\mathfrak nL_i = \mathfrak sL_i \iff \mathfrak nK_i = \mathfrak sK_i$. -/
@[kb "omeara1963" "§91C, p. 245 (Jordan splittings of the same type)"]
def SameJordanType {V' : Type*} [AddCommGroup V'] [Module F V'] [Module R V'] [IsScalarTower R F V']
    (Q' : QuadraticForm F V') {t t' : ℕ} (Ls : Fin t → Submodule R V) (Ks : Fin t' → Submodule R V') :
    Prop :=
  ∃ h : t = t', ∀ i : Fin t, scale Q (Ls i) = scale Q' (Ks (Fin.cast h i)) ∧
    finrank R (Ls i) = finrank R (Ks (Fin.cast h i)) ∧
    (normIdeal Q (Ls i) = scale Q (Ls i) ↔ normIdeal Q' (Ks (Fin.cast h i)) = scale Q' (Ks (Fin.cast h i)))

/-- **Theorem 91:9** (O'Meara 1963, p. 244): any two Jordan splittings $L = L_1 \perp \cdots \perp L_t$ and
$L = K_1 \perp \cdots \perp K_T$ of a lattice $L$ in a quadratic space over a local field are of the same type: $t = T$,
and for every $i$, $\mathfrak sL_i = \mathfrak sK_i$, $\dim L_i = \dim K_i$, and $\mathfrak nL_i = \mathfrak sL_i$ if and
only if $\mathfrak nK_i = \mathfrak sK_i$. (Only the discrete valuation ring is used.) -/
@[kb "omeara1963" "§91C, 91:9, p. 244"]
theorem IsJordanSplitting.sameJordanType {L : Submodule R V} (hfg : L.FG) {t t' : ℕ}
    {Ls : Fin t → Submodule R V} {Ks : Fin t' → Submodule R V} (hL : IsJordanSplitting Q L Ls)
    (hK : IsJordanSplitting Q L Ks) : SameJordanType Q Q Ls Ks := by
  have hfgL : ∀ i, (Ls i).FG := fun i => FG.of_le hfg (hL.split.iSup_eq ▸ le_iSup Ls i)
  have hfgK : ∀ i, (Ks i).FG := fun i => FG.of_le hfg (hK.split.iSup_eq ▸ le_iSup Ks i)
  -- step 1: an `a`-modular component in one splitting gives one in the other (`s L^a = a`)
  have step1 : ∀ {t₁ t₂ : ℕ} {L₁ : Fin t₁ → Submodule R V} {L₂ : Fin t₂ → Submodule R V},
      IsJordanSplitting Q L L₁ → IsJordanSplitting Q L L₂ → (∀ i, (L₁ i).FG) → (∀ i, (L₂ i).FG) →
      ∀ i, ∃ j, scale Q (L₂ j) = scale Q (L₁ i) := by
    intro t₁ t₂ L₁ L₂ h₁ h₂ hfg₁ hfg₂ i
    set a := scale Q (L₁ i)
    -- `s L^a = a`
    have hsa : scale Q (subA Q a L) = a := by
      apply le_antisymm (scale_subA_le Q a L)
      have : L₁ i ≤ subA Q a L := by
        rw [subA_eq_iSup Q h₁.split]
        exact le_iSup_of_le i (by rw [subA_eq_self Q le_rfl])
      exact scale_mono Q this
    by_contra hno
    push Not at hno
    obtain ⟨α, hα, haα⟩ := exists_eq_span_singleton (R := R) (scale_fg Q (hfg₁ i)) (h₁.modular i).1
    have horth : ∀ j k : Fin t₂, j ≠ k → ∀ x ∈ subA Q a (L₂ j), ∀ y ∈ subA Q a (L₂ k), bil Q x y = 0 :=
      fun j k hjk x hx y hy => h₂.split.orth j k hjk x hx.1 y hy.1
    have hsub : ∀ j, (subA Q a (L₂ j)).FG :=
      fun j => FG.of_le (hfg₂ j) (fun x (hx : x ∈ subA Q a (L₂ j)) => hx.1)
    have hmem : α ∈ scale Q (subA Q a L) := by
      rw [hsa, show a = R ∙ α from haα]; exact mem_span_singleton_self α
    rw [subA_eq_iSup Q h₂.split] at hmem
    refine notMem_iSup_of_fg (S := fun j => scale Q (subA Q a (L₂ j))) (fun j => scale_fg Q (hsub j))
      hα (fun j => ?_) (scale_iSup_le Q horth hmem)
    have hmodj := h₂.modular j
    obtain ⟨β, -, hβ⟩ := exists_eq_span_singleton (R := R) (scale_fg Q (hfg₂ j)) hmodj.1
    have hj := hno j
    rw [hβ] at hmodj hj
    show α ∉ scale Q (subA Q a (L₂ j))
    rw [show a = R ∙ α from haα] at hj ⊢
    exact notMem_scale_subA Q hα hmodj (hfg₂ j) hj
  obtain ⟨htt, hsc⟩ := eq_of_strictAnti_of_range_eq hL.scale_strictAnti hK.scale_strictAnti
    (step1 hL hK hfgL hfgK) (step1 hK hL hfgK hfgL)
  refine ⟨htt, fun i => ⟨hsc i, ?_⟩⟩
  -- steps 2 and 3, in both directions
  set j := Fin.cast htt i
  obtain ⟨hMi, hMi'⟩ := isOrthSum_subA Q hfg hL i
  obtain ⟨hNj, hNj'⟩ := isOrthSum_subA Q hfg hK j
  have haeq : scale Q (Ks j) = scale Q (Ls i) := (hsc i).symm
  rw [haeq] at hNj hNj'
  have hsubfg : (subA Q (scale Q (Ls i)) L).FG := FG.of_le hfg fun x hx => hx.1
  have hmodL : IsModular Q (scale Q (Ls i)) (Ls i) := hL.modular i
  have hmodK : IsModular Q (scale Q (Ls i)) (Ks j) := haeq ▸ hK.modular j
  have hLiM : Ls i ≤ subA Q (scale Q (Ls i)) L := hMi.sup_eq ▸ le_sup_left
  have hKjM : Ks j ≤ subA Q (scale Q (Ls i)) L := hNj.sup_eq ▸ le_sup_left
  obtain ⟨h1, h2⟩ := finrank_le_of_isOrthSum Q hsubfg hLiM hNj hmodL hmodK hNj'
  obtain ⟨h3, h4⟩ := finrank_le_of_isOrthSum Q hsubfg hKjM hMi hmodK hmodL hMi'
  refine ⟨le_antisymm h1 h3, ?_⟩
  rw [haeq]
  exact ⟨h2, h4⟩

end DVR

end QuadFormsKB.OMeara
