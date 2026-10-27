/-
# O'Meara §91C: Jordan splittings

**Setting** (as in `Sec82.lean`): $R$ a discrete valuation ring with fraction field $F$, $2 \in F^\times$,
a quadratic space $(V, Q)$ over $F$, O'Meara's bilinear form $B$ = `bil Q`, lattices = `Submodule R V`.

**Defines** `IsJordanSplitting Q L Ls` (O'Meara 1963, §91C, p. 243): $L = L_1 \perp \cdots \perp L_t$ with every
component modular and $\mathfrak sL_1 \supsetneq \cdots \supsetneq \mathfrak sL_t$ (indices $0, \dots, t-1$ here).

**Proves**
* `isModular_span_of_gram`: vectors whose matrix is $\alpha U$ ($U$ invertible over $R$) are independent and span an
  $\alpha$-modular lattice;
* `iSupIndep_of_orth`: pairwise orthogonal regular sublattices are independent, so an orthogonal sum of regular
  lattices is direct (O'Meara 1963, §82D);
* `scale_sup_of_orth` ($\mathfrak s(J \perp K) = \mathfrak sJ + \mathfrak sK$, §82E, p. 227) and
  `isModular_sup` (an orthogonal sum of $\mathfrak a$-modular lattices is $\mathfrak a$-modular, §82G, p. 231);
* `exists_modular_le` (§91C, p. 243): a non-zero regular lattice $L$ contains an $\mathfrak sL$-modular sublattice of
  rank $1$ or $2$;
* `exists_isJordanSplitting` (**§91C, p. 243**): every non-zero regular lattice has a Jordan splitting.
-/
import QuadFormsKB.Literature.OMeara.Sec91

open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Domain

variable {R : Type*} [CommRing R] [IsDomain R] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- Vectors with non-zero discriminant $\det(B(x_i, x_j))$ are linearly independent over $R$. -/
theorem linearIndependent_of_det_gram_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {x : ι → V}
    (hx : (gram Q x).det ≠ 0) : LinearIndependent R x := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hv : Matrix.vecMul (fun i => algebraMap R F (g i)) (gram Q x) = 0 := by
    funext j
    have := congrArg (fun v => bil Q v (x j)) hg
    simp only [bil_sum_left, bil_rsmul_left] at this
    simpa [Matrix.vecMul, dotProduct, gram, bil] using this
  by_contra hne
  push Not at hne
  obtain ⟨i, hi⟩ := hne
  apply hx
  refine Matrix.exists_vecMul_eq_zero_iff.mp ⟨_, ?_, hv⟩
  intro h0
  apply hi
  have := congrFun h0 i
  exact (IsFractionRing.injective R F) (by simpa using this)

/-- **Lattices with matrix $\alpha U$** (O'Meara 1963, §82G, p. 231, and 82:13): if the matrix $(B(x_i, x_j))$ of a
non-empty finite family is $\alpha U$ with $\alpha \ne 0$ and $U$ invertible over $R$, then the $x_i$ are linearly
independent and span an $\alpha\mathfrak o$-modular lattice of rank $|\iota|$. -/
theorem isModular_span_of_gram {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {x : ι → V} {α : F}
    (hα : α ≠ 0) {U : Matrix ι ι R} (hU : IsUnit U.det) (hG : gram Q x = α • U.map (algebraMap R F)) :
    IsModular Q (R ∙ α) (span R (Set.range x)) ∧ finrank R (span R (Set.range x)) = Fintype.card ι := by
  have hdet : (gram Q x).det ≠ 0 := by
    rw [hG, Matrix.det_smul, show (U.map (algebraMap R F)).det = algebraMap R F U.det from
      (RingHom.map_det _ _).symm]
    refine mul_ne_zero (pow_ne_zero _ hα) fun h => hU.ne_zero ?_
    exact (IsFractionRing.injective R F) (h.trans (map_zero _).symm)
  have hli := linearIndependent_of_det_gram_ne_zero (R := R) Q hdet
  let b := Basis.span hli
  have hb : (fun i => (b i : V)) = x := by funext i; simp [b]
  refine ⟨(isModular_iff_gram Q b hα).mpr ⟨inferInstance, U, hU, by rw [hb]; exact hG⟩, ?_⟩
  exact finrank_eq_card_basis b

/-- If $z$ is orthogonal to every $L_j$, $j \in s$, it is orthogonal to $\bigvee_{j \in s} L_j$. -/
theorem bil_eq_zero_of_mem_iSup {ι : Type*} {Ls : ι → Submodule R V} {P : ι → Prop} {z x : V}
    (hz : ∀ j, P j → ∀ y ∈ Ls j, bil Q y z = 0) (hx : x ∈ ⨆ (j) (_ : P j), Ls j) : bil Q x z = 0 := by
  refine iSup_induction _ (motive := fun x => bil Q x z = 0) hx (fun j y hy => ?_) (by simp [bil])
    (fun x y hx hy => by rw [bil_add_left, hx, hy, add_zero])
  refine iSup_induction _ (motive := fun x => bil Q x z = 0) hy (fun hj y hy => hz j hj y hy)
    (by simp [bil]) (fun x y hx hy => by rw [bil_add_left, hx, hy, add_zero])

/-- **Orthogonal regular sublattices are independent** (O'Meara 1963, §82D, pp. 224–225): a pairwise orthogonal
family of regular lattices is independent, i.e. its sum is direct. -/
theorem iSupIndep_of_orth {ι : Type*} {Ls : ι → Submodule R V}
    (horth : ∀ i j, i ≠ j → ∀ x ∈ Ls i, ∀ y ∈ Ls j, bil Q x y = 0) (hreg : ∀ i, IsRegular Q (Ls i)) :
    iSupIndep Ls := by
  intro i
  rw [disjoint_iff, eq_bot_iff]
  rintro x ⟨hxi, hx⟩
  refine (mem_bot R).mpr (hreg i x hxi fun z hz => ?_)
  exact bil_eq_zero_of_mem_iSup Q (P := fun j => j ≠ i) (fun j hj y hy => horth j i hj y hy z hz) hx

/-- **Scale of an orthogonal sum** (O'Meara 1963, §82E, p. 227): $\mathfrak s(J \perp K) = \mathfrak sJ +
\mathfrak sK$. -/
@[kb "omeara1963" "§82E, p. 227 (s(J ⊥ K) = sJ + sK)"]
theorem scale_sup_of_orth {J K : Submodule R V} (horth : ∀ x ∈ J, ∀ y ∈ K, bil Q x y = 0) :
    scale Q (J ⊔ K) = scale Q J ⊔ scale Q K := by
  apply le_antisymm
  · rw [scale, span_le]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := mem_sup.mp hx
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := mem_sup.mp hy
    rw [bil_add_left, bil_add_right, bil_add_right, horth x₁ hx₁ y₂ hy₂, bil_comm Q x₂ y₁,
      horth y₁ hy₁ x₂ hx₂, add_zero, zero_add]
    exact add_mem (mem_sup_left (bil_mem_scale Q hx₁ hy₁)) (mem_sup_right (bil_mem_scale Q hx₂ hy₂))
  · exact sup_le (scale_mono Q le_sup_left) (scale_mono Q le_sup_right)

/-- **Norm of an orthogonal sum** (O'Meara 1963, §82E, p. 227): $\mathfrak n(J \perp K) = \mathfrak nJ +
\mathfrak nK$. -/
@[kb "omeara1963" "§82E, p. 227 (n(J ⊥ K) = nJ + nK)"]
theorem normIdeal_sup_of_orth {J K : Submodule R V} (horth : ∀ x ∈ J, ∀ y ∈ K, bil Q x y = 0) :
    normIdeal Q (J ⊔ K) = normIdeal Q J ⊔ normIdeal Q K := by
  apply le_antisymm
  · rw [normIdeal, span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := mem_sup.mp hx
    rw [Q_add, horth x₁ hx₁ x₂ hx₂, mul_zero, add_zero]
    exact add_mem (mem_sup_left (Q_mem_normIdeal Q hx₁)) (mem_sup_right (Q_mem_normIdeal Q hx₂))
  · exact sup_le (normIdeal_mono Q le_sup_left) (normIdeal_mono Q le_sup_right)

end Domain

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

omit [Invertible (2 : F)] in
include F in
/-- The rank of a sublattice is at most the rank of the lattice. -/
theorem finrank_le_of_le {J L : Submodule R V} (hJL : J ≤ L) (hL : L.FG) : finrank R J ≤ finrank R L := by
  obtain ⟨b⟩ := exists_basis (R := R) (F := F) (FG.of_le hL hJL)
  have : Module.Finite R L := Module.Finite.iff_fg.mpr hL
  have hli : LinearIndependent R (fun i => (⟨b i, hJL (b i).2⟩ : L)) := by
    have := b.linearIndependent.map' J.subtype (ker_subtype J)
    exact LinearIndependent.of_comp L.subtype (by simpa [Function.comp_def] using this)
  simpa using hli.fintype_card_le_finrank

omit [Invertible (2 : F)] in
include F in
/-- **Rank of a direct sum** (O'Meara 1963, §82D, p. 225: $\operatorname{rank}(L_1 \oplus L_2) =
\operatorname{rank}L_1 + \operatorname{rank}L_2$). -/
theorem finrank_sup_of_disjoint {J K : Submodule R V} (hJ : J.FG) (hK : K.FG) (h : Disjoint J K) :
    finrank R ↥(J ⊔ K) = finrank R J + finrank R K := by
  obtain ⟨bJ⟩ := exists_basis (R := R) (F := F) hJ
  obtain ⟨bK⟩ := exists_basis (R := R) (F := F) hK
  let x : Fin (finrank R J) ⊕ Fin (finrank R K) → V := Sum.elim (fun i => bJ i) (fun i => bK i)
  have hJs := span_basis_eq bJ
  have hKs := span_basis_eq bK
  have hli : LinearIndependent R x := by
    refine LinearIndependent.sum_type ?_ ?_ ?_
    · exact LinearIndependent.map' bJ.linearIndependent J.subtype (ker_subtype J)
    · exact LinearIndependent.map' bK.linearIndependent K.subtype (ker_subtype K)
    · rw [hJs, hKs]; exact h
  have hspan : span R (Set.range x) = J ⊔ K := by
    rw [Set.Sum.elim_range, span_union, hJs, hKs]
  rw [← hspan, finrank_eq_card_basis (Basis.span hli)]
  simp

theorem isOrthSum_finrank {L J K : Submodule R V} (h : IsOrthSum Q L J K) (hL : L.FG) :
    finrank R L = finrank R J + finrank R K := by
  rw [← h.sup_eq]
  exact finrank_sup_of_disjoint (F := F) (FG.of_le hL (h.sup_eq ▸ le_sup_left))
    (FG.of_le hL (h.sup_eq ▸ le_sup_right)) h.disjoint

/-- **An orthogonal sum of $\mathfrak a$-modular lattices is $\mathfrak a$-modular** (O'Meara 1963, §82G,
p. 231), and its rank is the sum of the ranks. -/
@[kb "omeara1963" "§82G, p. 231 (J ⊥ K is a-modular iff J and K are)"]
theorem isModular_sup {a : Submodule R F} {J K : Submodule R V} (hJ : IsModular Q a J) (hK : IsModular Q a K)
    (hJfg : J.FG) (hKfg : K.FG) (horth : ∀ x ∈ J, ∀ y ∈ K, bil Q x y = 0) :
    IsModular Q a (J ⊔ K) ∧ finrank R ↥(J ⊔ K) = finrank R J + finrank R K := by
  obtain ⟨α, hα, rfl, bJ, U, hU, hGJ⟩ := exists_gram_of_isModular Q hJ hJfg
  obtain ⟨β, hβ, hβα, bK, U', hU', hGK⟩ := exists_gram_of_isModular Q hK hKfg
  -- both scales are `αR`, so `β = εα` with a unit `ε`; rewrite `K`'s matrix in terms of `α`
  have hmem : β ∈ R ∙ α := hβα ▸ mem_span_singleton_self β
  have hmem' : α ∈ R ∙ β := hβα ▸ mem_span_singleton_self α
  obtain ⟨c, hc⟩ := mem_span_singleton.mp hmem
  obtain ⟨d, hd⟩ := mem_span_singleton.mp hmem'
  have hcd : c * d = 1 := by
    apply IsFractionRing.injective R F
    rw [map_mul, map_one]
    apply mul_left_cancel₀ hα
    rw [Algebra.smul_def] at hc hd
    linear_combination hd + (algebraMap R F d) * hc
  let U'' := c • U'
  have hU'' : IsUnit U''.det := by
    simp only [U'', Matrix.det_smul]
    exact (IsUnit.pow _ (IsUnit.of_mul_eq_one d hcd)).mul hU'
  have hGK' : gram Q (fun i => (bK i : V)) = α • U''.map (algebraMap R F) := by
    rw [hGK, ← hc]
    ext i j
    simp only [U'', Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul]
    rw [Algebra.smul_def]
    ring
  -- the combined family
  let x : Fin (finrank R J) ⊕ Fin (finrank R K) → V := Sum.elim (fun i => bJ i) (fun i => bK i)
  have hG : gram Q x = α • (Matrix.fromBlocks U 0 0 U'').map (algebraMap R F) := by
    ext (i | i) (j | j)
    · simpa [x, gram] using congrFun (congrFun hGJ i) j
    · simp [x, gram, horth _ (bJ i).2 _ (bK j).2]
    · simp [x, gram, bil_comm Q (bK i : V), horth _ (bJ j).2 _ (bK i).2]
    · simpa [x, gram] using congrFun (congrFun hGK' i) j
  have hdet : IsUnit (Matrix.fromBlocks U 0 0 U'').det := by
    rw [Matrix.det_fromBlocks_zero₂₁]; exact hU.mul hU''
  have hne : Nonempty (Fin (finrank R J) ⊕ Fin (finrank R K)) := by
    have : 0 < finrank R J := by
      rcases Nat.eq_zero_or_pos (finrank R J) with h | h
      · exfalso
        have hsc : scale Q J = ⊥ := by
          rw [← span_basis_eq bJ, scale_span, span_eq_bot]
          rintro _ ⟨p, rfl⟩; exact (Fin.elim0 (h ▸ p.1))
        exact hα (by simpa [hsc] using hJ.2.1.symm)
      · exact h
    exact ⟨Sum.inl ⟨0, this⟩⟩
  have hspan : span R (Set.range x) = J ⊔ K := by
    rw [Set.Sum.elim_range, span_union]
    exact congrArg₂ (· ⊔ ·) (span_basis_eq bJ) (span_basis_eq bK)
  obtain ⟨hmod, hrk⟩ := isModular_span_of_gram Q hα hdet hG
  rw [hspan] at hmod hrk
  exact ⟨hmod, by rw [hrk]; simp⟩

/-- The scale of a regular non-zero lattice is non-zero. -/
theorem scale_ne_bot {L : Submodule R V} (hreg : IsRegular Q L) (hne : L ≠ ⊥) : scale Q L ≠ ⊥ := by
  intro h
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff L).mp hne
  exact hx0 (hreg x hx fun y hy => by
    have := bil_mem_scale Q hx hy; rw [h, mem_bot] at this; exact this)

/-- **A modular sublattice of rank $1$ or $2$** (O'Meara 1963, §91C, p. 243): a non-zero regular lattice $L$
contains an $\mathfrak sL$-modular sublattice $J$ (of rank $1$ if $\mathfrak nL = \mathfrak sL$, else of rank $2$). -/
@[kb "omeara1963" "§91C, p. 243 (L contains a 1- or 2-dimensional sL-modular sublattice)"]
theorem exists_modular_le {L : Submodule R V} (hfg : L.FG) (hreg : IsRegular Q L) (hne : L ≠ ⊥) :
    ∃ J ≤ L, J.FG ∧ IsModular Q (scale Q L) J := by
  obtain ⟨u, hu, hn⟩ := exists_normIdeal_eq Q hfg
  obtain ⟨x, hx, y, hy, hs⟩ := exists_scale_eq Q hfg
  have hβ : bil Q x y ≠ 0 := by
    intro h0; exact scale_ne_bot Q hreg hne (by rw [hs, h0]; simp)
  by_cases heq : normIdeal Q L = scale Q L
  · -- a vector `u` with `Q(u)o = sL`
    have hQu : Q u ≠ 0 := by
      intro h0; exact scale_ne_bot Q hreg hne (by rw [← heq, hn, h0]; simp)
    let v : Fin 1 → V := fun _ => u
    have hG : gram Q v = Q u • (1 : Matrix (Fin 1) (Fin 1) R).map (algebraMap R F) := by
      ext i j; fin_cases i; fin_cases j; simp [v, gram]
    obtain ⟨hmod, -⟩ := isModular_span_of_gram Q hQu (by simp) hG
    refine ⟨span R (Set.range v), ?_, fg_span (Set.finite_range v), by rwa [← heq, hn]⟩
    rw [span_le]; rintro _ ⟨_, rfl⟩; exact hu
  · -- a binary lattice `ox + oy` with `B(x,y)o = sL`
    have hlt : normIdeal Q L < scale Q L := lt_of_le_of_ne (normIdeal_le_scale Q L) heq
    have hβn : bil Q x y ∉ normIdeal Q L := by
      intro h; apply heq; apply le_antisymm (normIdeal_le_scale Q L)
      rw [hs, span_singleton_le_iff_mem]; exact h
    obtain ⟨m₁, hm₁, h₁⟩ :=
      exists_maximalIdeal_mul_of_mem_of_notMem (R := R) (Q_mem_normIdeal Q hx) hβn
    obtain ⟨m₂, hm₂, h₂⟩ :=
      exists_maximalIdeal_mul_of_mem_of_notMem (R := R) (Q_mem_normIdeal Q hy) hβn
    let v : Fin 2 → V := ![x, y]
    let U : Matrix (Fin 2) (Fin 2) R := !![m₁, 1; 1, m₂]
    have hG : gram Q v = bil Q x y • U.map (algebraMap R F) := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [v, U, gram, h₁, h₂, bil_comm Q y x, mul_comm]
    have hU : IsUnit U.det := by
      rw [Matrix.det_fin_two_of]
      have : m₁ * m₂ - 1 * 1 = -(1 - m₁ * m₂) := by ring
      rw [this, IsUnit.neg_iff]
      exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ (Ideal.mul_mem_right _ _ hm₁)
    obtain ⟨hmod, -⟩ := isModular_span_of_gram Q hβ hU hG
    refine ⟨span R (Set.range v), ?_, fg_span (Set.finite_range v), by rwa [hs]⟩
    rw [span_le]; rintro _ ⟨i, rfl⟩; fin_cases i
    · exact hx
    · exact hy

/-- A component of an orthogonal splitting of a regular lattice is regular. -/
theorem IsOrthSum.isRegular_right {L J K : Submodule R V} (h : IsOrthSum Q L J K) (hreg : IsRegular Q L) :
    IsRegular Q K := by
  intro x hx h0
  refine hreg x (h.sup_eq ▸ mem_sup_right hx) fun z hz => ?_
  rw [← h.sup_eq] at hz
  obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := mem_sup.mp hz
  rw [bil_add_right, h0 z₂ hz₂, bil_comm, h.orth z₁ hz₁ x hx, add_zero]

/-- **Splitting off a modular component of scale $\mathfrak sL$** (O'Meara 1963, §91C, p. 243): a non-zero regular
lattice $L$ splits as $L = J \perp K$ with $J$ an $\mathfrak sL$-modular lattice and $K = 0$ or
$\mathfrak sK \subsetneq \mathfrak sL$. (Take $J$ of maximal rank; if $\mathfrak sK = \mathfrak sL$, then $K$ contains
an $\mathfrak sL$-modular $J'$ and $J \perp J'$ would be larger.) -/
theorem exists_isOrthSum_modular {L : Submodule R V} (hfg : L.FG) (hreg : IsRegular Q L) (hne : L ≠ ⊥) :
    ∃ J K, IsOrthSum Q L J K ∧ J.FG ∧ IsModular Q (scale Q L) J ∧ (K = ⊥ ∨ scale Q K < scale Q L) := by
  classical
  let P : ℕ → Prop := fun r => ∃ J ≤ L, J.FG ∧ IsModular Q (scale Q L) J ∧ finrank R J = r
  obtain ⟨J₀, hJ₀L, hJ₀fg, hJ₀⟩ := exists_modular_le Q hfg hreg hne
  have hP₀ : P (finrank R J₀) := ⟨J₀, hJ₀L, hJ₀fg, hJ₀, rfl⟩
  have hb₀ : finrank R J₀ ≤ finrank R L := finrank_le_of_le (F := F) hJ₀L hfg
  let r := Nat.findGreatest P (finrank R L)
  obtain ⟨J, hJL, hJfg, hJ, hJr⟩ : P r := Nat.findGreatest_spec hb₀ hP₀
  obtain ⟨K, hK⟩ := splits_of_isModular_of_scale_eq Q hJL hJ hJfg rfl
  refine ⟨J, K, hK, hJfg, hJ, ?_⟩
  by_cases hK0 : K = ⊥
  · exact Or.inl hK0
  right
  have hKL : K ≤ L := hK.sup_eq ▸ le_sup_right
  refine lt_of_le_of_ne (scale_mono Q hKL) fun hsK => ?_
  have hKfg : K.FG := FG.of_le hfg hKL
  have hKreg : IsRegular Q K := IsOrthSum.isRegular_right Q hK hreg
  obtain ⟨J', hJ'K, hJ'fg, hJ'⟩ := exists_modular_le Q hKfg hKreg hK0
  rw [hsK] at hJ'
  obtain ⟨hsum, hrk⟩ := isModular_sup Q hJ hJ' hJfg hJ'fg
    (fun x hx y hy => hK.orth x hx y (hJ'K hy))
  have hJ'pos : 0 < finrank R J' := by
    rcases Nat.eq_zero_or_pos (finrank R J') with h | h
    · exfalso
      obtain ⟨b⟩ := exists_basis (R := R) (F := F) hJ'fg
      have hsc : scale Q J' = ⊥ := by
        rw [← span_basis_eq b, scale_span, span_eq_bot]
        rintro _ ⟨p, rfl⟩; exact Fin.elim0 (h ▸ p.1)
      exact hJ'.1 (hJ'.2.1.symm.trans hsc)
    · exact h
  have hle : J ⊔ J' ≤ L := sup_le hJL (hJ'K.trans hKL)
  have hP : P (finrank R ↥(J ⊔ J')) := ⟨J ⊔ J', hle, hJfg.sup hJ'fg, hsum, rfl⟩
  have h2 : finrank R ↥(J ⊔ J') ≤ r := Nat.le_findGreatest (finrank_le_of_le (F := F) hle hfg) hP
  rw [hrk] at h2
  omega

/-- **Jordan splitting** (O'Meara 1963, §91C, p. 243): $L = L_1 \perp \cdots \perp L_t$ with each component
$L_i$ modular (`IsModular Q (scale Q (Ls i)) (Ls i)`) and strictly decreasing scales
$\mathfrak sL_1 \supsetneq \mathfrak sL_2 \supsetneq \cdots \supsetneq \mathfrak sL_t$. O'Meara's components
$L_1, \dots, L_t$ are `Ls 0, …, Ls (t-1)` here. -/
@[kb "omeara1963" "§91C, p. 243 (Jordan splitting)"]
structure IsJordanSplitting (L : Submodule R V) {t : ℕ} (Ls : Fin t → Submodule R V) : Prop where
  split : IsOrthSplit Q L Ls
  modular : ∀ i, IsModular Q (scale Q (Ls i)) (Ls i)
  scale_strictAnti : StrictAnti fun i => scale Q (Ls i)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] in
theorem iSup_fin_cons {t : ℕ} (J : Submodule R V) (Ks : Fin t → Submodule R V) :
    ⨆ i, (Fin.cons J Ks : Fin (t + 1) → Submodule R V) i = J ⊔ ⨆ i, Ks i := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    refine Fin.cases ?_ (fun i => ?_) i
    · simp
    · simp only [Fin.cons_succ]; exact le_sup_of_le_right (le_iSup Ks i)
  · refine sup_le ?_ (iSup_le fun i => ?_)
    · simpa using le_iSup (Fin.cons J Ks : Fin (t + 1) → Submodule R V) 0
    · simpa using le_iSup (Fin.cons J Ks : Fin (t + 1) → Submodule R V) i.succ

/-- **Existence of Jordan splittings** (O'Meara 1963, §91C, p. 243): every non-zero regular lattice $L$ in a
quadratic space over a local field has at least one Jordan splitting. (Only the discrete valuation ring is used.) -/
@[kb "omeara1963" "§91C, p. 243 (every non-zero regular lattice has a Jordan splitting)"]
theorem exists_isJordanSplitting {L : Submodule R V} (hfg : L.FG) (hreg : IsRegular Q L) (hne : L ≠ ⊥) :
    ∃ t, ∃ Ls : Fin t → Submodule R V, IsJordanSplitting Q L Ls := by
  induction h : finrank R L using Nat.strong_induction_on generalizing L with
  | _ n ih =>
  obtain ⟨J, K, hK, hJfg, hJ, hKs⟩ := exists_isOrthSum_modular Q hfg hreg hne
  have hJs : scale Q J = scale Q L := hJ.2.1
  have hJreg : IsRegular Q J := hJ.isRegular Q hJfg
  by_cases hK0 : K = ⊥
  · refine ⟨1, fun _ => J, ⟨⟨fun i j hij => absurd (Subsingleton.elim i j) hij, ?_, ?_⟩, ?_, ?_⟩⟩
    · exact iSupIndep_of_orth Q (fun i j hij => absurd (Subsingleton.elim i j) hij) fun _ => hJreg
    · rw [ciSup_const, ← hK.sup_eq, hK0, sup_bot_eq]
    · intro i; rw [hJs]; exact hJ
    · intro i j hij; exact absurd (Subsingleton.elim i j) (ne_of_lt hij)
  · have hlt := hKs.resolve_left hK0
    have hKL : K ≤ L := hK.sup_eq ▸ le_sup_right
    have hKfg : K.FG := FG.of_le hfg hKL
    have hKreg : IsRegular Q K := IsOrthSum.isRegular_right Q hK hreg
    have hrk := isOrthSum_finrank Q hK hfg
    have hJpos : 0 < finrank R J := by
      rcases Nat.eq_zero_or_pos (finrank R J) with h0 | h0
      · exfalso
        obtain ⟨b⟩ := exists_basis (R := R) (F := F) hJfg
        have hsc : scale Q J = ⊥ := by
          rw [← span_basis_eq b, scale_span, span_eq_bot]
          rintro _ ⟨p, rfl⟩; exact Fin.elim0 (h0 ▸ p.1)
        exact hJ.1 (hJ.2.1.symm.trans hsc)
      · exact h0
    obtain ⟨t, Ks, hKs⟩ := ih (finrank R K) (by omega) hKfg hKreg hK0 rfl
    have hKsle : ∀ i, Ks i ≤ K := fun i => hKs.split.iSup_eq ▸ le_iSup Ks i
    let Ls : Fin (t + 1) → Submodule R V := Fin.cons J Ks
    have horth : ∀ i j, i ≠ j → ∀ x ∈ Ls i, ∀ y ∈ Ls j, bil Q x y = 0 := by
      intro i j hij
      refine Fin.cases (fun hij => ?_) (fun i hij => ?_) i hij
      · refine Fin.cases (fun h => absurd rfl h) (fun j _ => ?_) j hij
        intro x hx y hy
        exact hK.orth x hx y (hKsle j hy)
      · refine Fin.cases (fun _ => ?_) (fun j hij => ?_) j hij
        · intro x hx y hy
          rw [bil_comm]; exact hK.orth y hy x (hKsle i hx)
        · exact hKs.split.orth i j (fun h => hij (h ▸ rfl))
    have hmod : ∀ i, IsModular Q (scale Q (Ls i)) (Ls i) := by
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp only [Ls, Fin.cons_zero]; rw [hJs]; exact hJ
      · simp only [Ls, Fin.cons_succ]; exact hKs.modular i
    refine ⟨t + 1, Ls, ⟨⟨horth, ?_, ?_⟩, hmod, ?_⟩⟩
    · exact iSupIndep_of_orth Q horth fun i => (hmod i).isRegular Q
        (FG.of_le hfg (by
          refine Fin.cases ?_ (fun i => ?_) i
          · simp only [Ls, Fin.cons_zero]; exact hK.sup_eq ▸ le_sup_left
          · simp only [Ls, Fin.cons_succ]; exact (hKsle i).trans hKL))
    · rw [iSup_fin_cons, hKs.split.iSup_eq, hK.sup_eq]
    · intro i j hij
      refine Fin.cases (fun hij => ?_) (fun i hij => ?_) i hij
      · obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr (ne_of_gt hij)
        simp only [Ls, Fin.cons_zero, Fin.cons_succ]
        rw [hJs]
        exact lt_of_le_of_lt (scale_mono Q (hKsle j)) hlt
      · obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr (ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) hij))
        simp only [Ls, Fin.cons_succ]
        exact hKs.scale_strictAnti (Fin.succ_lt_succ_iff.mp hij)

end DVR

end QuadFormsKB.OMeara
