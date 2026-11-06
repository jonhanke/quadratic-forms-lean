/-
# O'Meara 93:28, proof of the necessity, step 2: reduction to the last index

**Setting** (as in `Sec93FNecDual.lean`).

**Proves** (O'Meara 1963, §93F, proof of 93:28, necessity, step 2, p. 270–271: "there is a unimodular lattice $J$ on
$FL^*_{(i+1)}$ with $L^*_{(i+1)} \subseteq J$ and $\mathfrak gJ = \mathfrak gL^*_{(i+1)}$. Put $L' = L + J$ ...
$K_\lambda$ splits $L'$ ... there is a splitting $L' = K_1 \perp \cdots \perp K_i \perp I$")
* `isOrthSum_splitComp_of_jordan`: a lattice $A$ with a Jordan splitting $A = K_1 \perp \cdots \perp K_r$ splits
  every $L' \supseteq A$ with $B(K_\lambda, L') \subseteq \mathfrak sK_\lambda$ (82:15 and 82:7);
-/
import QuadFormsKB.Literature.OMeara.Sec93FMerge
import QuadFormsKB.Literature.OMeara.Sec93FNecDual
import QuadFormsKB.Literature.OMeara.Sec82Splitting

open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.NecMerge

open Sat93 Transfer28 NecBase NecBlock Merge28 NecDual

section Split

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **A Jordan-split sublattice splits** (O'Meara 1963, 82:15 and 82:7, p. 232): if $A = K_1 \perp \cdots \perp K_r$ is
a Jordan splitting, $A \subseteq L'$ and $B(K_\lambda, L') \subseteq \mathfrak sK_\lambda$ for every $\lambda$, then
$L' = A \perp \{x \in L' : B(x, A) = 0\}$. -/
theorem isOrthSum_splitComp_of_jordan {A L' : Submodule R V} (hAL : A ≤ L') (hAfg : A.FG) {r : ℕ}
    {Ks : Fin r → Submodule R V} (hK : IsJordanSplitting Q A Ks)
    (hB : ∀ l, ∀ x ∈ Ks l, ∀ y ∈ L', bil Q x y ∈ scale Q (Ks l)) :
    IsOrthSum Q L' A (splitComp Q L' A) := by
  classical
  have hKle : ∀ l, Ks l ≤ A := fun l => hK.split.iSup_eq ▸ le_iSup Ks l
  have hreg : IsRegular Q A := isRegular_of_isJordanSplitting Q hAfg hK
  refine ⟨fun x hx y hy => by obtain ⟨-, h2⟩ := hy; rw [bil_comm]; exact h2 x hx, ?_, ?_⟩
  · rw [disjoint_def]
    intro v hvA hvC
    obtain ⟨-, h2⟩ := hvC
    exact hreg v hvA fun z hz => h2 z hz
  · apply le_antisymm (sup_le hAL fun x hx => by obtain ⟨h1, -⟩ := hx; exact h1)
    intro v hv
    -- the components `y_λ ∈ K_λ` with `B(y_λ, ·) = B(v, ·)` on `K_λ`
    have hproj : ∀ l, ∃ y ∈ Ks l, ∀ z ∈ Ks l, bil Q y z = bil Q v z := by
      intro l
      obtain ⟨α, -, hsc, b, U, hU, hG⟩ := exists_gram_of_isModular Q (hK.modular l) (FG.of_le hAfg (hKle l))
      exact exists_mem_bil_eq_of_gram Q b hU hG fun j => by
        rw [← hsc, bil_comm]; exact hB l _ (b j).2 v hv
    choose y hyK hy using hproj
    refine mem_sup.mpr ⟨∑ l, y l, sum_mem fun l _ => hKle l (hyK l), v - ∑ l, y l,
      ⟨sub_mem hv (hAL (sum_mem fun l _ => hKle l (hyK l))), fun z hz => ?_⟩, by abel⟩
    rw [← hK.split.iSup_eq] at hz
    refine Submodule.iSup_induction Ks (motive := fun z => bil Q (v - ∑ l, y l) z = 0) hz ?_ (by simp [bil]) ?_
    · intro m z hz
      rw [bil_sub_left, bil_sum_left, Finset.sum_eq_single m]
      · rw [hy m z hz, sub_self]
      · intro l _ hlm; exact hK.split.orth l m hlm _ (hyK l) z hz
      · intro h; exact absurd (Finset.mem_univ m) h
    · intro z z' hz hz'; rw [bil_add_right, hz, hz', add_zero]

/-- $(A \perp D)^{\mathfrak a} = A^{\mathfrak a} + D^{\mathfrak a}$ for orthogonal $A$, $D$. -/
theorem subA_sup_of_orth {A D : Submodule R V} (horth : ∀ x ∈ A, ∀ y ∈ D, bil Q x y = 0) (a : Submodule R F) :
    subA Q a (A ⊔ D) = subA Q a A ⊔ subA Q a D := by
  apply le_antisymm
  · rintro x ⟨hx, hxa⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup.mp hx
    refine mem_sup.mpr ⟨y, ⟨hy, fun w hw => ?_⟩, z, ⟨hz, fun w hw => ?_⟩, rfl⟩
    · have := hxa w (mem_sup_left hw)
      rwa [bil_add_left, bil_comm Q z w, horth w hw z hz, add_zero] at this
    · have := hxa w (mem_sup_right hw)
      rwa [bil_add_left, horth y hy w hw, zero_add] at this
  · refine sup_le ?_ ?_
    · rintro x ⟨hx, hxa⟩
      refine ⟨mem_sup_left hx, fun w hw => ?_⟩
      obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup.mp hw
      rw [bil_add_right, horth x hx z hz, add_zero]; exact hxa y hy
    · rintro x ⟨hx, hxa⟩
      refine ⟨mem_sup_right hx, fun w hw => ?_⟩
      obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup.mp hw
      rw [bil_add_right, bil_comm Q x y, horth y hy x hx, zero_add]; exact hxa z hz

/-- $\mathfrak g((A \perp D)^{\mathfrak a}) = \mathfrak g(A^{\mathfrak a}) + \mathfrak g(D^{\mathfrak a})$. -/
theorem normGroup_subA_sup {A D : Submodule R V} (horth : ∀ x ∈ A, ∀ y ∈ D, bil Q x y = 0)
    (a : Submodule R F) :
    normGroup Q (subA Q a (A ⊔ D)) = normGroup Q (subA Q a A) ⊔ normGroup Q (subA Q a D) := by
  rw [subA_sup_of_orth Q horth]
  exact normGroup_sup_of_orth Q fun x hx y hy => by
    obtain ⟨hx', -⟩ := hx; obtain ⟨hy', -⟩ := hy; exact horth x hx' y hy'

/-- $D^{\mathfrak a} = D$ when $\mathfrak sD \subseteq \mathfrak a$. -/
theorem subA_eq_self {D : Submodule R V} {a : Submodule R F} (h : scale Q D ≤ a) : subA Q a D = D :=
  le_antisymm (fun x hx => hx.1) fun x hx => ⟨hx, fun y hy => h (bil_mem_scale Q hx hy)⟩

/-- **Appending a last component** to a Jordan splitting: if $A = A_1 \perp \cdots \perp A_n$ is a Jordan splitting,
$D \perp A$ is modular of scale strictly inside every $\mathfrak sA_k$, then $A \perp D = A_1 \perp \cdots \perp A_n
\perp D$ is a Jordan splitting. -/
theorem isJordanSplitting_snoc {A D : Submodule R V} (hAfg : A.FG) (hDfg : D.FG) {n : ℕ}
    {C : Fin n → Submodule R V} (hA : IsJordanSplitting Q A C) (hD : IsModular Q (scale Q D) D)
    (horth : ∀ x ∈ A, ∀ y ∈ D, bil Q x y = 0) (hlt : ∀ k, scale Q D < scale Q (C k)) :
    IsJordanSplitting Q (A ⊔ D) (Fin.snoc C D : Fin (n + 1) → Submodule R V) := by
  have hCle : ∀ k, C k ≤ A := fun k => hA.split.iSup_eq ▸ le_iSup C k
  set M : Fin (n + 1) → Submodule R V := Fin.snoc C D with hM
  have hMc : ∀ k : Fin n, M k.castSucc = C k := fun k => by simp [hM]
  have hMl : M (Fin.last n) = D := by simp [hM]
  have hor : ∀ j k, j ≠ k → ∀ x ∈ M j, ∀ y ∈ M k, bil Q x y = 0 := by
    intro j k hjk
    induction j using Fin.lastCases with
    | last =>
      induction k using Fin.lastCases with
      | last => exact absurd rfl hjk
      | cast k =>
        intro x hx y hy; rw [hMl] at hx; rw [hMc] at hy
        rw [bil_comm]; exact horth y (hCle k hy) x hx
    | cast j =>
      induction k using Fin.lastCases with
      | last => intro x hx y hy; rw [hMc] at hx; rw [hMl] at hy; exact horth x (hCle j hx) y hy
      | cast k =>
        intro x hx y hy; rw [hMc] at hx hy
        exact hA.split.orth j k (fun h => hjk (by rw [h])) x hx y hy
  have hmod : ∀ k, IsModular Q (scale Q (M k)) (M k) := by
    intro k
    induction k using Fin.lastCases with
    | last => rw [hMl]; exact hD
    | cast k => rw [hMc]; exact hA.modular k
  have hMle : ∀ k, M k ≤ A ⊔ D := by
    intro k
    induction k using Fin.lastCases with
    | last => rw [hMl]; exact le_sup_right
    | cast k => rw [hMc]; exact (hCle k).trans le_sup_left
  have hfg : (A ⊔ D).FG := hAfg.sup hDfg
  refine ⟨⟨hor, iSupIndep_of_orth Q hor fun k => (hmod k).isRegular Q (FG.of_le hfg (hMle k)), ?_⟩, hmod, ?_⟩
  · apply le_antisymm (iSup_le hMle)
    refine sup_le ?_ ?_
    · rw [← hA.split.iSup_eq]
      exact iSup_le fun k => (hMc k) ▸ le_iSup M k.castSucc
    · exact hMl ▸ le_iSup M (Fin.last n)
  · intro j k hjk
    induction k using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact absurd hjk (lt_irrefl _)
      | cast j => simp only [hMl, hMc]; exact hlt j
    | cast k =>
      induction j using Fin.lastCases with
      | last => exact absurd hjk (not_lt.mpr (Fin.le_last _))
      | cast j =>
        simp only [hMc]
        exact hA.scale_strictAnti (Fin.castSucc_lt_castSucc_iff.mp hjk)

/-- The Jordan chain of `Fin.snoc C D` at the last index of `C` is $\bigvee C$. -/
theorem jordanChain_snoc {n : ℕ} (C : Fin (n + 1) → Submodule R V) (D : Submodule R V) :
    jordanChain (Fin.snoc C D : Fin (n + 2) → Submodule R V) (Fin.last n).castSucc = ⨆ k, C k := by
  apply le_antisymm
  · refine iSup₂_le fun k hk => ?_
    induction k using Fin.lastCases with
    | last => exact absurd hk (not_le.mpr (Fin.castSucc_lt_last _))
    | cast k => simp only [Fin.snoc_castSucc]; exact le_iSup C k
  · refine iSup_le fun k => ?_
    refine le_iSup₂_of_le k.castSucc (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last k)) ?_
    simp

/-- **$A^\#$ has scale in $\mathfrak o$ when all Jordan scales of $A$ contain $\mathfrak o$**: if $k, k' \in A$ satisfy
$B(k, A), B(k', A) \subseteq \mathfrak o$ then $B(k, k') \in \mathfrak o$ (componentwise $k_\lambda \in
\mathfrak s_\lambda^{-1}A_\lambda$). -/
theorem bil_mem_one_of_sharp [FiniteDimensional F V] {A : Submodule R V} (hAfg : A.FG) {n : ℕ}
    {C : Fin n → Submodule R V} (hA : IsJordanSplitting Q A C) (hsc : ∀ l, 1 ≤ scale Q (C l)) {k k' : V}
    (hk : k ∈ A) (hk' : k' ∈ A) (hkA : ∀ z ∈ A, bil Q k z ∈ (1 : Submodule R F))
    (hk'A : ∀ z ∈ A, bil Q k' z ∈ (1 : Submodule R F)) : bil Q k k' ∈ (1 : Submodule R F) := by
  classical
  have hCle : ∀ l, C l ≤ A := fun l => hA.split.iSup_eq ▸ le_iSup C l
  have hCfg : ∀ l, (C l).FG := fun l => FG.of_le hAfg (hCle l)
  obtain ⟨μ, hμ⟩ := (mem_iSup_fin_iff C k).mp (hA.split.iSup_eq ▸ hk)
  obtain ⟨μ', hμ'⟩ := (mem_iSup_fin_iff C k').mp (hA.split.iSup_eq ▸ hk')
  -- each component lies in `σ_l⁻¹ C_l`
  have hcomp : ∀ (κ : ∀ l, C l) (x : V), x = ∑ l, (κ l : V) → (∀ z ∈ A, bil Q x z ∈ (1 : Submodule R F)) →
      ∀ l, ∀ z ∈ C l, bil Q (κ l : V) z ∈ (1 : Submodule R F) := by
    intro κ x hx hxA l z hz
    have := hxA z (hCle l hz)
    rw [hx, bil_sum_left, Finset.sum_eq_single l] at this
    · exact this
    · intro m _ hml; exact hA.split.orth m l hml _ (κ m).2 z hz
    · intro h; exact absurd (Finset.mem_univ l) h
  have h1 := hcomp μ k hμ.symm hkA
  have h2 := hcomp μ' k' hμ'.symm hk'A
  rw [← hμ, ← hμ', bil_sum_left]
  refine sum_mem fun l _ => ?_
  rw [bil_sum_right, Finset.sum_eq_single l]
  · obtain ⟨σ, hσ0, hσ⟩ := exists_eq_span_singleton (R := R) ((hA.modular l).2.1 ▸ scale_fg Q (hCfg l))
      (hA.modular l).1
    have hmod : IsModular Q (R ∙ σ) (C l) := hσ ▸ hA.modular l
    have hdual := Dual93.dual_eq_smul Q hσ0 hmod (hCfg l)
    have hmemd : ∀ (y : C l), (∀ z ∈ C l, bil Q (y : V) z ∈ (1 : Submodule R F)) → (y : V) ∈ (R ∙ σ⁻¹) • C l := by
      intro y hy; rw [← hdual]; exact ⟨subset_span y.2, hy⟩
    obtain ⟨m, hm, hmy⟩ := mem_span_singleton_smul_iff.mp (hmemd (μ l) (h1 l))
    obtain ⟨m', hm', hmy'⟩ := mem_span_singleton_smul_iff.mp (hmemd (μ' l) (h2 l))
    rw [← hmy, ← hmy', bil_smul_left, bil_smul_right]
    have hB : bil Q m m' ∈ R ∙ σ := hσ ▸ bil_mem_scale Q hm hm'
    obtain ⟨c, hc⟩ := mem_span_singleton.mp hB
    have hσinv : σ⁻¹ ∈ (1 : Submodule R F) := by
      have h1σ : (1 : F) ∈ R ∙ σ := hσ ▸ hsc l (Submodule.mem_one.mpr ⟨1, map_one _⟩)
      obtain ⟨d, hd⟩ := mem_span_singleton.mp h1σ
      refine Submodule.mem_one.mpr ⟨d, ?_⟩
      rw [Algebra.smul_def] at hd
      field_simp; linear_combination hd
    obtain ⟨d, hd⟩ := Submodule.mem_one.mp hσinv
    refine Submodule.mem_one.mpr ⟨d * c, ?_⟩
    rw [← hc, Algebra.smul_def, map_mul, hd]; field_simp
  · intro m _ hml; exact hA.split.orth l m (Ne.symm hml) _ (μ l).2 _ (μ' m).2
  · intro h; exact absurd (Finset.mem_univ l) h

/-- **The complement $I$ of $K_{(i)}$ in $L' = L_{(i)} \perp J$ has scale in $\mathfrak o$** (the claim "this splitting is
saturated" of O'Meara 1963, p. 271, first half): with $L = A \perp L^* = A' \perp K^*$, $L^* \subseteq J$,
$\mathfrak sJ, \mathfrak sK^* \subseteq \mathfrak o$, and $B(k, k') \in \mathfrak o$ for $k, k' \in A'$ with
$B(k, A'), B(k', A') \subseteq \mathfrak o$: write $v \in I$ as $v = k + b + u$ ($k \in A'$, $b \in K^*$, $u \in J$);
then $B(k, A') = -B(u, A') \subseteq \mathfrak o$, and every term of $B(v, v')$ lies in $\mathfrak o$. -/
theorem scale_splitComp_le_one {L A Lst A' Kst J : Submodule R V} (hL : IsOrthSum Q L A Lst)
    (hLK : IsOrthSum Q L A' Kst) (hLstJ : Lst ≤ J) (hAJ : ∀ x ∈ A, ∀ y ∈ J, bil Q x y = 0)
    (hJs : scale Q J ≤ 1) (hKsts : scale Q Kst ≤ 1)
    (hsharp : ∀ k ∈ A', ∀ k' ∈ A', (∀ z ∈ A', bil Q k z ∈ (1 : Submodule R F)) →
      (∀ z ∈ A', bil Q k' z ∈ (1 : Submodule R F)) → bil Q k k' ∈ (1 : Submodule R F)) :
    scale Q (splitComp Q (A ⊔ J) A') ≤ 1 := by
  have hLL' : L ≤ A ⊔ J := by rw [← hL.sup_eq]; exact sup_le_sup_left hLstJ A
  have hA'L : A' ≤ L := hLK.sup_eq ▸ le_sup_left
  have hKL : Kst ≤ L := hLK.sup_eq ▸ le_sup_right
  -- `B(J, L') ⊆ 𝔬`
  have hJL' : ∀ u ∈ J, ∀ w ∈ A ⊔ J, bil Q u w ∈ (1 : Submodule R F) := by
    intro u hu w hw
    obtain ⟨a, ha, u', hu', rfl⟩ := mem_sup.mp hw
    rw [bil_add_right, bil_comm Q u a, hAJ a ha u hu, zero_add]
    exact hJs (bil_mem_scale Q hu hu')
  -- decomposition of a vector of `I`
  have hdec : ∀ v ∈ splitComp Q (A ⊔ J) A', ∃ k ∈ A', ∃ b ∈ Kst, ∃ u ∈ J, v = k + b + u ∧
      ∀ z ∈ A', bil Q k z ∈ (1 : Submodule R F) := by
    intro v hv
    obtain ⟨hvL, hvA⟩ := hv
    obtain ⟨a, ha, u, hu, rfl⟩ := mem_sup.mp hvL
    have haL : a ∈ L := hL.sup_eq ▸ mem_sup_left ha
    rw [← hLK.sup_eq] at haL
    obtain ⟨k, hk, b, hb, rfl⟩ := mem_sup.mp haL
    refine ⟨k, hk, b, hb, u, hu, rfl, fun z hz => ?_⟩
    have h0 := hvA z hz
    rw [bil_add_left, bil_add_left, bil_comm Q b z, hLK.orth z hz b hb, add_zero] at h0
    have : bil Q k z = -bil Q u z := by linear_combination h0
    rw [this]
    exact neg_mem (hJL' u hu z (hLL' (hA'L hz)))
  rw [scale, span_le]
  rintro _ ⟨v, hv, v', hv', rfl⟩
  obtain ⟨k, hk, b, hb, u, hu, rfl, hkA⟩ := hdec v hv
  obtain ⟨k', hk', b', hb', u', hu', rfl, hk'A⟩ := hdec v' hv'
  have hkL' : ∀ {x}, x ∈ A' → x ∈ A ⊔ J := fun hx => hLL' (hA'L hx)
  have hbL' : ∀ {x}, x ∈ Kst → x ∈ A ⊔ J := fun hx => hLL' (hKL hx)
  rw [show bil Q (k + b + u) (k' + b' + u') = (bil Q k k' + bil Q k b' + bil Q k u') +
      (bil Q b k' + bil Q b b' + bil Q b u') + (bil Q u k' + bil Q u b' + bil Q u u') by
    simp only [bil_add_left, bil_add_right]; ring]
  refine add_mem (add_mem (add_mem (add_mem ?_ ?_) ?_) (add_mem (add_mem ?_ ?_) ?_)) (add_mem (add_mem ?_ ?_) ?_)
  · exact hsharp k hk k' hk' hkA hk'A
  · rw [hLK.orth k hk b' hb']; exact zero_mem _
  · rw [bil_comm]; exact hJL' u' hu' k (hkL' hk)
  · rw [bil_comm, hLK.orth k' hk' b hb]; exact zero_mem _
  · exact hKsts (bil_mem_scale Q hb hb')
  · rw [bil_comm]; exact hJL' u' hu' b (hbL' hb)
  · exact hJL' u hu k' (hkL' hk')
  · exact hJL' u hu b' (hbL' hb')
  · exact hJL' u hu u' (mem_sup_right hu')

/-- **The complement is unimodular** (O'Meara 1963, p. 271): if $L' = A \perp J = A' \perp I$ with $\mathfrak vA =
\mathfrak vA'$, $\operatorname{rank} A = \operatorname{rank} A'$, $J$ unimodular and $\mathfrak sI \subseteq
\mathfrak o$, then $I$ is unimodular ($dI = \varepsilon^2\, dA\, dJ/dA'$ is a unit). -/
theorem isUnimodular_compl [FiniteDimensional F V] {L' A J A' I : Submodule R V} (hL'fg : L'.FG)
    (h1 : IsOrthSum Q L' A J) (h2 : IsOrthSum Q L' A' I) (hvol : volume Q A = volume Q A')
    (hrk : finrank R A = finrank R A') (hJ : IsUnimodular Q J) (hIs : scale Q I ≤ 1) (hAreg : IsRegular Q A)
    (hA'reg : IsRegular Q A') : IsUnimodular Q I := by
  classical
  have fg : ∀ {M : Submodule R V}, M ≤ L' → M.FG := fun hM => FG.of_le hL'fg hM
  have hAle : A ≤ L' := h1.sup_eq ▸ le_sup_left
  have hJle : J ≤ L' := h1.sup_eq ▸ le_sup_right
  have hA'le : A' ≤ L' := h2.sup_eq ▸ le_sup_left
  have hIle : I ≤ L' := h2.sup_eq ▸ le_sup_right
  obtain ⟨eA⟩ := exists_basis (R := R) (F := F) (fg hAle)
  obtain ⟨eJ⟩ := exists_basis (R := R) (F := F) (fg hJle)
  obtain ⟨eA'⟩ := exists_basis (R := R) (F := F) (fg hA'le)
  obtain ⟨eI⟩ := exists_basis (R := R) (F := F) (fg hIle)
  obtain ⟨e₁, he₁⟩ := exists_basis_isOrthSum Q h1 eA eJ
  obtain ⟨e₂, he₂⟩ := exists_basis_isOrthSum Q h2 eA' eI
  have hcard : Fintype.card (Fin (finrank R A') ⊕ Fin (finrank R I)) =
      Fintype.card (Fin (finrank R A) ⊕ Fin (finrank R J)) := by
    rw [← finrank_eq_card_basis e₁, ← finrank_eq_card_basis e₂]
  set σ := Fintype.equivOfCardEq hcard
  obtain ⟨u, hu, hu'⟩ := det_gram_change Q e₁ (e₂.reindex σ)
  have hd₂ : (gram Q fun s => ((e₂.reindex σ) s : V)).det = (gram Q fun s => (e₂ s : V)).det := by
    simp only [Basis.reindex_apply]
    exact Matrix.det_submatrix_equiv_self σ.symm (gram Q fun s => (e₂ s : V))
  have hd₁' : (gram Q fun s => (e₁ s : V)).det =
      (gram Q fun i => (eA i : V)).det * (gram Q fun i => (eJ i : V)).det := by
    rw [show (fun s => (e₁ s : V)) = Sum.elim (fun i => (eA i : V)) (fun k => (eJ k : V)) from funext he₁]
    exact det_gram_sumElim Q h1.orth _ _ (fun i => (eA i).2) (fun k => (eJ k).2)
  have hd₂' : (gram Q fun s => (e₂ s : V)).det =
      (gram Q fun i => (eA' i : V)).det * (gram Q fun i => (eI i : V)).det := by
    rw [show (fun s => (e₂ s : V)) = Sum.elim (fun i => (eA' i : V)) (fun k => (eI k : V)) from funext he₂]
    exact det_gram_sumElim Q h2.orth _ _ (fun i => (eA' i).2) (fun k => (eI k).2)
  rw [hd₂, hd₂', hd₁'] at hu'
  -- `dA = w dA'` with `w` a unit, `dJ` a unit
  set dA := (gram Q fun i => (eA i : V)).det
  set dA' := (gram Q fun i => (eA' i : V)).det
  set dJ := (gram Q fun i => (eJ i : V)).det
  set dI := (gram Q fun i => (eI i : V)).det
  have hdA0 : dA ≠ 0 := det_gram_ne_zero_of_isRegular Q hAreg eA
  have hdA'0 : dA' ≠ 0 := det_gram_ne_zero_of_isRegular Q hA'reg eA'
  have hspanA : R ∙ dA = R ∙ dA' := by
    rw [← volume_eq_span_det Q eA, ← volume_eq_span_det Q eA', hvol]
  have hunit_of_span : ∀ {x y : F}, x ≠ 0 → y ≠ 0 → R ∙ x = R ∙ y → ∃ w : R, IsUnit w ∧ x = algebraMap R F w * y := by
    intro x y hx hy hxy
    obtain ⟨a, ha⟩ := mem_span_singleton.mp (hxy ▸ mem_span_singleton_self x : x ∈ R ∙ y)
    obtain ⟨b, hb⟩ := mem_span_singleton.mp (hxy.symm ▸ mem_span_singleton_self y : y ∈ R ∙ x)
    rw [Algebra.smul_def] at ha hb
    have hab : algebraMap R F (a * b) = 1 := by
      rw [map_mul]; apply mul_left_cancel₀ hx
      calc x * (algebraMap R F a * algebraMap R F b) = algebraMap R F a * (algebraMap R F b * x) := by ring
        _ = x * 1 := by rw [hb, ha]; ring
    have hab' : a * b = 1 := IsFractionRing.injective R F (by rw [hab, map_one])
    exact ⟨a, IsUnit.of_mul_eq_one b hab', ha.symm⟩
  obtain ⟨w, hw, hdAw⟩ := hunit_of_span hdA0 hdA'0 hspanA
  have hJfg := fg hJle
  have hdJ : R ∙ dJ = 1 := by
    rw [← volume_eq_span_det Q eJ, hJ.2.2, one_pow]
  obtain ⟨v, hv, hdJv⟩ := hunit_of_span (x := dJ) (y := 1)
    (det_gram_ne_zero_of_isRegular Q (IsModular.isRegular Q hJ hJfg) eJ) one_ne_zero
    (by rw [hdJ, Submodule.one_eq_span])
  rw [mul_one] at hdJv
  -- `dI` is a unit
  have hdI : dI = algebraMap R F (u ^ 2 * w * v) := by
    rw [map_mul, map_mul, map_pow, ← hdJv]
    apply mul_left_cancel₀ hdA'0
    rw [hu', hdAw]; ring
  have hIunit : IsUnit (u ^ 2 * w * v) := ((hu.pow 2).mul hw).mul hv
  -- the matrix of `I` has entries in `𝔬`
  choose Uf hUf using fun i j => Submodule.mem_one.mp (hIs (bil_mem_scale Q (eI i).2 (eI j).2))
  set U : Matrix (Fin (finrank R I)) (Fin (finrank R I)) R := Matrix.of Uf with hUdef
  have hUmap : gram Q (fun i => (eI i : V)) = (1 : F) • U.map (algebraMap R F) := by
    ext i j; simp [gram, hUdef, hUf]
  have hUdet : IsUnit U.det := by
    have : U.det = u ^ 2 * w * v := IsFractionRing.injective R F (by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, ← one_smul F (U.map (algebraMap R F)), ← hUmap]
      exact hdI)
    rw [this]; exact hIunit
  have hrkI : finrank R I = finrank R J := by
    have h1r := isOrthSum_finrank Q h1 hL'fg
    have h2r := isOrthSum_finrank Q h2 hL'fg
    omega
  have hJ0 : J ≠ ⊥ := fun h => by
    have := hJ.1; rw [← hJ.2.1, h, scale_bot] at this; exact this rfl
  have hrkJ : 0 < finrank R J := Nat.pos_of_ne_zero fun h => hJ0 (by
    obtain ⟨b⟩ := exists_basis (R := R) (F := F) hJfg
    rw [← span_basis_eq b, span_eq_bot]
    rintro _ ⟨k, rfl⟩; exact Fin.elim0 (h ▸ k))
  have : Nonempty (Fin (finrank R I)) := ⟨⟨0, by omega⟩⟩
  obtain ⟨hmod, -⟩ := isModular_span_of_gram Q one_ne_zero hUdet hUmap
  rw [span_basis_eq, ← Submodule.one_eq_span] at hmod
  exact hmod

/-- $B(L_m, L) \subseteq \mathfrak sL_m$ for a component of an orthogonal splitting. -/
theorem bil_mem_scale_of_split {L : Submodule R V} {t : ℕ} {Ls : Fin t → Submodule R V}
    (hL : IsOrthSplit Q L Ls) (m : Fin t) {x y : V} (hx : x ∈ Ls m) (hy : y ∈ L) :
    bil Q x y ∈ scale Q (Ls m) := by
  rw [← hL.iSup_eq] at hy
  refine Submodule.iSup_induction Ls (motive := fun y => bil Q x y ∈ scale Q (Ls m)) hy ?_ (by simp [bil]) ?_
  · intro l y hy
    by_cases hlm : m = l
    · subst hlm; exact bil_mem_scale Q hx hy
    · rw [hL.orth m l hlm x hx y hy]; exact zero_mem _
  · intro y y' hy hy'; rw [bil_add_right]; exact add_mem hy hy'

/-- The scale of a lattice with an orthogonal splitting whose components have scale in $\mathfrak a$. -/
theorem scale_le_of_split {L : Submodule R V} {ι : Type*} {Ls : ι → Submodule R V} (hL : IsOrthSplit Q L Ls)
    {a : Submodule R F} (h : ∀ k, scale Q (Ls k) ≤ a) : scale Q L ≤ a := by
  rw [scale, span_le]
  rintro _ ⟨x, hx, y, hy, rfl⟩
  rw [← hL.iSup_eq] at hx hy
  refine Submodule.iSup_induction Ls (motive := fun x => bil Q x y ∈ a) hx ?_ (by simp [bil]) ?_
  · intro k x hx
    refine Submodule.iSup_induction Ls (motive := fun y => bil Q x y ∈ a) hy ?_ (by simp [bil]) ?_
    · intro l y hy
      by_cases hkl : k = l
      · subst hkl; exact h k (bil_mem_scale Q hx hy)
      · rw [hL.orth k l hkl x hx y hy]; exact zero_mem _
    · intro y y' hy hy'; rw [bil_add_right]; exact add_mem hy hy'
  · intro x x' hx hx'; rw [bil_add_left]; exact add_mem hx hx'

end Split

section Main

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- **The data of the reduction to the last index** (O'Meara 1963, §93F, proof of 93:28, step 2, pp. 270-271), shared by
the proofs of conditions (i) and (ii): the lattice $L' = L_{(i)} \perp J$ with its two Jordan splittings
$L_1 \perp \cdots \perp L_i \perp J$ and $K_1 \perp \cdots \perp K_i \perp I$ (saturated, all dimensions $\ge 3$, last
component unimodular with a block base), and the identifications of the chains, of $\mathfrak f_i$, of the weight and of
the last norm generator. -/
theorem nec_merge_data {L : Submodule R V} [L.IsLattice F] {t : ℕ}
    {Ls Ks : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls) (hK' : IsJordanSplitting Q L Ks)
    (i j : Fin t) (hij : i.val + 1 = j.val) (hdim : ∀ k, 3 ≤ finrank R (Ls k))
    (hsat : IsSaturated Q L Ls) {a : Fin t → F} (ha : IsFundNormGenerators Q L Ls a)
    (hU : scale Q (Ls j) = 1) {T : Submodule F V} (hTiso : ∀ x ∈ T, Q x = 0)
    (hTL : ∀ x ∈ T, x ∈ span F (invJordanChain Ls j : Set V))
    (hTdim : finrank R (invJordanChain Ls j) ≤ 2 * finrank F T) :
    ∃ (L' : Submodule R V) (_ : L'.IsLattice F) (Ms Ns : Fin (i.val + 1 + 1) → Submodule R V)
      (a' : Fin (i.val + 1 + 1) → F) (m : ℕ) (x : Fin m → V × V),
      IsJordanSplitting Q L' Ms ∧ IsJordanSplitting Q L' Ns ∧ (∀ k, 3 ≤ finrank R (Ms k)) ∧ IsSaturated Q L' Ms ∧
      IsFundNormGenerators Q L' Ms a' ∧ scale Q (Ms (Fin.last (i.val + 1))) = 1 ∧
      pairSpan R x = Ms (Fin.last (i.val + 1)) ∧ (∀ k, Q (x k).2 = 0) ∧ (∀ k, bil Q (x k).1 (x k).2 = 1) ∧
      (∀ k l, k ≠ l → bil Q (x k).1 (x l).1 = 0) ∧ (∀ k l, k ≠ l → bil Q (x k).1 (x l).2 = 0) ∧
      (∀ k l, k ≠ l → bil Q (x k).2 (x l).2 = 0) ∧
      jordanChain Ms (Fin.last i.val).castSucc = jordanChain Ls i ∧
      jordanChain Ns (Fin.last i.val).castSucc = jordanChain Ks i ∧
      fIdeal Q L' Ms (Fin.last i.val).castSucc (Fin.last (i.val + 1)) = fIdeal Q L Ls i j ∧
      fundWeight Q L' Ms (Fin.last (i.val + 1)) = fundWeight Q L Ls j ∧ a' (Fin.last (i.val + 1)) = a j := by
  classical
  have hfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hreg : IsRegular Q L := isRegular_of_isJordanSplitting Q hfg hL
  obtain ⟨hT, hJT⟩ := hL.sameJordanType Q hfg hK'
  have hc : ∀ k, Fin.cast hT k = k := fun k => Fin.ext (by simp)
  have hscLK : ∀ k, scale Q (Ls k) = scale Q (Ks k) := fun k => by have := (hJT k).1; rwa [hc] at this
  have hrkLK : ∀ k, finrank R (Ls k) = finrank R (Ks k) := fun k => by have := (hJT k).2.1; rwa [hc] at this
  set A := jordanChain Ls i with hAdef
  set A' := jordanChain Ks i with hA'def
  set Lst := invJordanChain Ls j with hLstdef
  set Kst := invJordanChain Ks j with hKstdef
  have hsL : IsOrthSum Q L A Lst := isOrthSum_jordanChain Q hL.split i j hij
  have hsK : IsOrthSum Q L A' Kst := isOrthSum_jordanChain Q hK'.split i j hij
  have hJA := isJordanSplitting_jordanChain Q hL i
  have hJA' := isJordanSplitting_jordanChain Q hK' i
  have hJst := isJordanSplitting_invJordanChain Q hL j
  have hJKst := isJordanSplitting_invJordanChain Q hK' j
  have hAle : A ≤ L := hsL.sup_eq ▸ le_sup_left
  have hLstle : Lst ≤ L := hsL.sup_eq ▸ le_sup_right
  have hA'le : A' ≤ L := hsK.sup_eq ▸ le_sup_left
  have hAfg : A.FG := FG.of_le hfg hAle
  have hA'fg : A'.FG := FG.of_le hfg hA'le
  have hLstfg : Lst.FG := FG.of_le hfg hLstle
  -- scales: `𝔰 = 𝔬` on the tail, `⊋ 𝔬` on the head
  have hsc_tail : ∀ {Ms : Fin t → Submodule R V}, IsJordanSplitting Q L Ms → (∀ k, scale Q (Ms k) = scale Q (Ls k)) →
      ∀ k : Fin (t - j.val), scale Q (Ms (tailIdx j k)) ≤ 1 := by
    intro Ms hMs hsM k
    rw [hsM, ← hU]
    exact hL.scale_strictAnti.antitone (Fin.le_def.2 (by simp [tailIdx]))
  have hscLst : scale Q Lst = 1 := by
    apply le_antisymm (scale_le_of_split Q hJst.split (hsc_tail hL fun _ => rfl))
    rw [← hU]; exact scale_mono Q (le_iSup₂_of_le j le_rfl le_rfl : Ls j ≤ invJordanChain Ls j)
  have hscKst : scale Q Kst ≤ 1 := scale_le_of_split Q hJKst.split (hsc_tail hK' fun k => (hscLK k).symm)
  have hsc_head : ∀ k : Fin (i.val + 1), 1 < scale Q (Ls (chainIdx i k)) := by
    intro k
    rw [← hU]
    exact hL.scale_strictAnti (Fin.lt_def.2 (by simp [chainIdx]; omega))
  have hLstreg : IsRegular Q Lst := isRegular_of_isJordanSplitting Q hLstfg hJst
  -- 93:3: the unimodular lattice `J ⊇ L*` with a block base
  obtain ⟨J, hLstJ, hJspan, hJfg, hJU, hgJ, hrkJ, m, x, hxbase⟩ :=
    exists_unimodular_blocks Q hLstfg hLstreg hscLst hTiso hTL hTdim
  have hAJ : ∀ y ∈ A, ∀ u ∈ J, bil Q y u = 0 := fun y hy u hu =>
    bil_zero_of_mem_span_F Q (fun z hz => hsL.orth y hy z hz) (hJspan u hu)
  set L' := A ⊔ J with hL'def
  have hAreg : IsRegular Q A := isRegular_of_isJordanSplitting Q hAfg hJA
  have hA'reg : IsRegular Q A' := isRegular_of_isJordanSplitting Q hA'fg hJA'
  have hL'1 : IsOrthSum Q L' A J := ⟨hAJ, disjoint_of_orth Q hAreg hAJ, rfl⟩
  have hLL' : L ≤ L' := by rw [← hsL.sup_eq]; exact sup_le_sup_left hLstJ A
  have hL'fg : L'.FG := hAfg.sup hJfg
  -- the `K`-side: `L' = K_(i) ⊥ I`
  have hBK : ∀ l, ∀ y ∈ Ks (chainIdx i l), ∀ z ∈ L', bil Q y z ∈ scale Q (Ks (chainIdx i l)) := by
    intro l y hy z hz
    obtain ⟨a₀, ha₀, u, hu, rfl⟩ := mem_sup.mp hz
    rw [bil_add_right]
    refine add_mem (bil_mem_scale_of_split Q hK'.split _ hy (hAle ha₀)) ?_
    have hyL : y ∈ L := hK'.split.iSup_eq ▸ mem_iSup_of_mem _ hy
    rw [← hsL.sup_eq] at hyL
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := mem_sup.mp hyL
    rw [bil_add_left, hAJ y₁ hy₁ u hu, zero_add, ← hscLK]
    exact (hsc_head l).le (hJU.2.1 ▸ bil_mem_scale Q (hLstJ hy₂) hu)
  have hsplitK := isOrthSum_splitComp_of_jordan Q (hA'le.trans hLL') hA'fg hJA' hBK
  set I := splitComp Q L' A' with hIdef
  have hIs : scale Q I ≤ 1 := scale_splitComp_le_one Q hsL hsK hLstJ hAJ hJU.2.1.le hscKst
    (fun k hk k' hk' hkA hk'A => bil_mem_one_of_sharp Q hA'fg hJA' (fun l => by
      rw [← hscLK]; exact (hsc_head l).le) hk hk' hkA hk'A)
  have hrkAA' : finrank R A = finrank R A' := by
    rw [hJA.split.finrank_eq_sum (F := F), hJA'.split.finrank_eq_sum (F := F)]
    exact Finset.sum_congr rfl fun k _ => hrkLK _
  have hvol : volume Q A = volume Q A' :=
    volume_jordanChain_eq Q Q hfg hfg hL hK' hscLK hrkLK i
  have hIU : IsUnimodular Q I := isUnimodular_compl Q hL'fg hL'1 hsplitK hvol hrkAA' hJU hIs hAreg hA'reg
  have hIfg : I.FG := FG.of_le hL'fg (hsplitK.sup_eq ▸ le_sup_right)
  -- the norm groups of `L'` and `L` agree above `𝔬`
  have hgeq : ∀ s : Submodule R F, 1 ≤ s → normGroup Q (subA Q s L') = normGroup Q (subA Q s L) := by
    intro s hs
    rw [hL'def, normGroup_subA_sup Q hAJ, ← hsL.sup_eq, normGroup_subA_sup Q hsL.orth,
      subA_eq_self Q (hJU.2.1.le.trans hs), subA_eq_self Q (hscLst.le.trans hs), hgJ]
  set C : Fin (i.val + 1) → Submodule R V := fun k => Ls (chainIdx i k) with hCdef
  set C' : Fin (i.val + 1) → Submodule R V := fun k => Ks (chainIdx i k) with hC'def
  set Ms : Fin (i.val + 1 + 1) → Submodule R V := Fin.snoc C J with hMsdef
  set Ns : Fin (i.val + 1 + 1) → Submodule R V := Fin.snoc C' I with hNsdef
  have hJmod : IsModular Q (scale Q J) J := by rw [hJU.2.1]; exact hJU
  have hMs : IsJordanSplitting Q L' Ms :=
    isJordanSplitting_snoc Q hAfg hJfg hJA hJmod hAJ (fun k => by rw [hJU.2.1]; exact hsc_head k)
  have hImod : IsModular Q (scale Q I) I := by rw [hIU.2.1]; exact hIU
  have hNs0 := isJordanSplitting_snoc Q hA'fg hIfg hJA' hImod hsplitK.orth
    (fun k => by rw [hIU.2.1, ← hscLK]; exact hsc_head k)
  have hNs : IsJordanSplitting Q L' Ns := hsplitK.sup_eq ▸ hNs0
  have hMlast : Ms (Fin.last (i.val + 1)) = J := Fin.snoc_last _ _
  have hMcs : ∀ k, Ms k.castSucc = C k := fun k => Fin.snoc_castSucc _ _ _
  have hlast : chainIdx i (Fin.last i.val) = i := Fin.ext (by simp [chainIdx])
  have hfMs : ∀ k : Fin (i.val + 1), fundNormGroup Q L' Ms k.castSucc = fundNormGroup Q L Ls (chainIdx i k) := by
    intro k
    simp only [fundNormGroup, fundSub, hMcs, hCdef]
    exact hgeq _ (hsc_head k).le
  have hfMl : fundNormGroup Q L' Ms (Fin.last (i.val + 1)) = fundNormGroup Q L Ls j := by
    simp only [fundNormGroup, fundSub, hMlast, hJU.2.1, hU]
    exact hgeq 1 le_rfl
  -- `L'` is a lattice on `V`
  have hL'lat : L'.IsLattice F := ⟨hL'fg, eq_top_iff.2 (by
    rw [← Submodule.IsLattice.span_eq_top (A := F) (M := L)]
    exact span_mono (SetLike.coe_subset_coe.2 hLL'))⟩
  -- dimensions, saturation, fundamental norm generators of the new splitting
  have hgLst : normGroup Q Lst = fundNormGroup Q L Ls j := by
    apply le_antisymm
    · rw [fundNormGroup, fundSub, hU]
      exact normGroup_mono Q fun y hy => ⟨hLstle hy, fun z hz => by
        rw [← hsL.sup_eq] at hz
        obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := mem_sup.mp hz
        rw [bil_add_right, bil_comm Q y z₁, hsL.orth z₁ hz₁ y hy, zero_add, ← hscLst]
        exact bil_mem_scale Q hy hz₂⟩
    · rw [← hsat.2 j]; exact normGroup_mono Q (le_iSup₂_of_le j le_rfl le_rfl)
  have hdim' : ∀ k, 3 ≤ finrank R (Ms k) := by
    intro k
    induction k using Fin.lastCases with
    | last =>
      rw [hMlast, hrkJ, hJst.split.finrank_eq_sum (F := F)]
      have hj0 : tailIdx j ⟨0, by omega⟩ = j := Fin.ext (by simp [tailIdx])
      calc 3 ≤ finrank R (Ls j) := hdim j
        _ = finrank R (Ls (tailIdx j ⟨0, by omega⟩)) := by rw [hj0]
        _ ≤ _ := Finset.single_le_sum (f := fun k => finrank R (Ls (tailIdx j k))) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ _)
    | cast k => rw [hMcs]; exact hdim _
  have hsat' : IsSaturated Q L' Ms := by
    refine ⟨hMs, fun k => ?_⟩
    induction k using Fin.lastCases with
    | last => rw [hMlast, hfMl, hgJ, hgLst]
    | cast k => rw [hMcs, hfMs]; exact hsat.2 _
  have ha' : IsFundNormGenerators Q L' Ms (Fin.snoc (fun k => a (chainIdx i k)) (a j)) := by
    intro k
    induction k using Fin.lastCases with
    | last => rw [Fin.snoc_last]; exact isNormGenerator_fundSub_of_eq Q Q hfMl (ha j)
    | cast k => rw [Fin.snoc_castSucc]; exact isNormGenerator_fundSub_of_eq Q Q (hfMs k) (ha _)
  have hU' : scale Q (Ms (Fin.last (i.val + 1))) = 1 := by rw [hMlast]; exact hJU.2.1
  obtain ⟨hxspan, hx2, hx12, hx11, hx12', hx22⟩ := hxbase
  have hfI : fIdeal Q L' Ms (Fin.last i.val).castSucc (Fin.last (i.val + 1)) = fIdeal Q L Ls i j := by
    simp only [fIdeal, fIdeal_fundNormIdeal_eq_span, hfMs, hfMl, hMcs, hCdef, hlast]
  have hfw : fundWeight Q L' Ms (Fin.last (i.val + 1)) = fundWeight Q L Ls j := by
    unfold fundWeight
    refine weight_congr Q Q hfMl ?_
    rw [scale_fundSub Q hL'fg hMs, scale_fundSub Q hfg hL, hMlast, hJU.2.1, hU]
  refine ⟨L', hL'lat, Ms, Ns, Fin.snoc (fun k => a (chainIdx i k)) (a j), _, x, hMs, hNs, hdim', hsat', ha', hU',
    by rw [hMlast]; exact hxspan, hx2, hx12, hx11, hx12', hx22, ?_, ?_, hfI, hfw, Fin.snoc_last _ _⟩
  · rw [jordanChain_snoc, ← jordanChain_eq_iSup]
  · rw [jordanChain_snoc, ← jordanChain_eq_iSup]

/-- **93:28, necessity, condition (i), reduced to the last index** (O'Meara 1963, §93F, proof of 93:28, step 2,
pp. 270–271). Let $L = L_1 \perp \cdots \perp L_t = K_1 \perp \cdots \perp K_t$ be Jordan splittings of a lattice on
$V$, the first saturated with all $\dim L_k \ge 3$, scaled so that $\mathfrak s_{i+1} = \mathfrak o$, and suppose
$FL^*_{(i+1)}$ is hyperbolic (a totally isotropic $T \subseteq FL^*_{(i+1)}$ of half the dimension). Then
$dL_{(i)}/dK_{(i)} \cong 1 \bmod \mathfrak f_i$: with $J \supseteq L^*_{(i+1)}$ unimodular on $FL^*_{(i+1)}$,
$\mathfrak gJ = \mathfrak gL^*_{(i+1)}$ (93:3), $L' = L_{(i)} \perp J$ has the Jordan splittings
$L_1 \perp \cdots \perp L_i \perp J$ and $K_1 \perp \cdots \perp K_i \perp I$ with the same $\mathfrak f_i$, and
`nec_disc_last_blocks` applies to $L'$ (`nec_merge_data`). -/
@[kb "omeara1963" "§93F, proof of 93:28, necessity, step 2, pp. 270–271 (condition (i), reduction to i = t-1)"]
theorem nec_disc_merge (hK : PadicClass.LocalHilbertField F) (h2p : ¬ IsUnit (2 : R)) (h2 : (2 : R) ≠ 0)
    (hQ : (QuadraticMap.associated Q).Nondegenerate) {L : Submodule R V} [L.IsLattice F] {t : ℕ}
    {Ls Ks : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls) (hK' : IsJordanSplitting Q L Ks)
    (i j : Fin t) (hij : i.val + 1 = j.val) (hdim : ∀ k, 3 ≤ finrank R (Ls k))
    (hsat : IsSaturated Q L Ls) {a : Fin t → F} (ha : IsFundNormGenerators Q L Ls a)
    (hU : scale Q (Ls j) = 1) {T : Submodule F V} (hTiso : ∀ x ∈ T, Q x = 0)
    (hTL : ∀ x ∈ T, x ∈ span F (invJordanChain Ls j : Set V))
    (hTdim : finrank R (invJordanChain Ls j) ≤ 2 * finrank F T) :
    DiscQuotSqEquivMod Q (jordanChain Ls i) (jordanChain Ks i) (fIdeal Q L Ls i j) := by
  obtain ⟨L', hlat, Ms, Ns, a', m, x, hMs, hNs, hdim', hsat', ha', hU', hxspan, hx2, hx12, hx11, hx12', hx22,
    hc1, hc2, hfI, -, -⟩ := nec_merge_data Q hL hK' i j hij hdim hsat ha hU hTiso hTL hTdim
  have hres := nec_disc_last_blocks Q hK h2p h2 hQ hMs hNs (Fin.last i.val).castSucc (Fin.last (i.val + 1))
    (by simp) (by simp) hdim' hsat' ha' hU' x hxspan hx2 hx12 hx11 hx12' hx22
  rw [hc1, hc2, hfI] at hres
  exact hres

end Main

end QuadFormsKB.OMeara.NecMerge
