import QuadFormsKB.Tamagawa.Measure.Weil.SplitSL1Finite
import QuadFormsKB.Tamagawa.Measure.Weil.SL2Tamagawa
import Mathlib.LinearAlgebra.SymplecticGroup

/-!
# $\tau(\mathrm{Sp}_2) = 1$ over every number field

$F$ is a number field and $\mathbb A = \mathbb A_F$ its adele ring. Throughout, $\mathrm{Sp}_2(R)$ is Mathlib's
`Matrix.symplecticGroup (Fin 1) R`: the $2\times2$ matrices $M$ with blocks indexed by `Fin 1 ⊕ Fin 1` and
$MJM^{\mathsf T} = J$, $J = \begin{pmatrix}0&-1\\1&0\end{pmatrix}$ (the genus $g = 1$ case of
`QuadFormsKB.WeilRep.Genus.Sp`).

* **`spSLEquiv R`**: for every commutative ring $R$, reindexing the blocks `Fin 1 ⊕ Fin 1` as `Fin 2` is a group
  isomorphism $\mathrm{Sp}_2(R)\cong\mathrm{SL}_2(R)$ (`WeilRep.Genus.sp1ToSL2` is the same map over a field, as a
  homomorphism). It is the identity on matrix entries, so it is an isomorphism of group schemes over $\mathbb Z$.
* **`Sp2A F`** $=\mathrm{Sp}_2(\mathbb A_F)$ with the subspace topology of $M_2(\mathbb A_F)$; `spSLEquivA F` is
  `spSLEquiv` over $\mathbb A_F$ as an isomorphism of topological groups.
* **`muSp2 F`**: the Tamagawa measure of $\mathrm{Sp}_2(\mathbb A_F)$, defined as the transport of the Tamagawa measure
  $\mu_T$ of $\mathrm{SL}_2(\mathbb A_F)$ (`muT`, `Tamagawa.Measure.Weil.tamagawa_SL2`) along the isomorphism. Since the
  isomorphism is defined over $\mathbb Z$ and is the identity on coordinates, it carries the invariant gauge form of
  $\mathrm{SL}_2$ to that of $\mathrm{Sp}_2$ and the local measures $|\omega|_v$ place by place (Weil 1982, §2.3); hence
  this is Weil's Tamagawa measure of $\mathrm{Sp}_2$ (no convergence factors are needed: $\mathrm{Sp}_2$ is semisimple).
* **`tamagawa_Sp2`**: $\tau(\mathrm{Sp}_2) = \operatorname{vol}(\mathrm{Sp}_2(\mathbb A_F)/\mathrm{Sp}_2(F)) = 1$, for the
  right action $\gamma\cdot g = g\gamma^{-1}$ of $\mathrm{Sp}_2(F)$ (the same convention as `tamagawa_SL2`).

Sources: Weil, *Adeles and Algebraic Groups* (1982), §3.5 ($\tau(\mathrm{Sp}_{2n}) = 1$) [unverified locator]; Kudla,
*Notes on the local theta correspondence* (1996), §I.1 ($\mathrm{Sp}_2 = \mathrm{SL}_2$) [unverified].
-/

open IsDedekindDomain NumberField MeasureTheory Measure Matrix
open scoped ENNReal MatrixGroups

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

/-! ### $\mathrm{Sp}_2(R)\cong\mathrm{SL}_2(R)$ over any commutative ring -/

section Ring

variable (R : Type*) [CommRing R]

/-- The reindexing `Fin 1 ⊕ Fin 1 ≃ Fin 2` (block $0$ is row/column $0$, block $1$ is row/column $1$). -/
def spIdx : Fin 1 ⊕ Fin 1 ≃ Fin 2 where
  toFun := Sum.elim (fun _ => 0) (fun _ => 1)
  invFun i := if i = 0 then Sum.inl 0 else Sum.inr 0
  left_inv := by rintro (i | i) <;> fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem spIdx_symm_zero : spIdx.symm 0 = Sum.inl 0 := rfl
theorem spIdx_symm_one : spIdx.symm 1 = Sum.inr 0 := rfl

/-- Every $2\times 2$ matrix of determinant $1$, with blocks `Fin 1 ⊕ Fin 1`, is symplectic. -/
theorem reindex_mem_symplecticGroup (g : SL(2, R)) :
    reindex spIdx.symm spIdx.symm (g : Matrix (Fin 2) (Fin 2) R) ∈ symplecticGroup (Fin 1) R := by
  rw [SymplecticGroup.mem_iff]
  have hdet := g.2
  rw [det_fin_two] at hdet
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, J, fromBlocks, spIdx,
      reindex_apply, submatrix_apply] <;> first | linear_combination (norm := ring1) hdet | linear_combination (norm := ring1) 2 * hdet | linear_combination (norm := ring1) -hdet | ring1

/-- **$\mathrm{Sp}_2(R)\cong\mathrm{SL}_2(R)$** for every commutative ring $R$: reindex the blocks `Fin 1 ⊕ Fin 1` as
`Fin 2` (the identity on matrix entries). -/
@[kb "kudla1996" "§I.1 ($\\mathrm{Sp}_2 = \\mathrm{SL}_2$) [unverified]"]
def spSLEquiv : symplecticGroup (Fin 1) R ≃* SL(2, R) where
  toFun M := ⟨reindex spIdx spIdx (M : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R), by
    rw [det_reindex_self]; exact SymplecticGroup.det_eq_one M.2⟩
  invFun g := ⟨_, reindex_mem_symplecticGroup R g⟩
  left_inv M := by ext i j; simp
  right_inv g := by ext i j; simp
  map_mul' M M' := by
    apply Subtype.ext
    show reindex spIdx spIdx ((M : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R) *
        (M' : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R)) =
      reindex spIdx spIdx (M : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R) *
        reindex spIdx spIdx (M' : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R)
    rw [reindex_apply, reindex_apply, reindex_apply, submatrix_mul_equiv]

theorem spSLEquiv_coe (M : symplecticGroup (Fin 1) R) :
    ((spSLEquiv R M : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) = reindex spIdx spIdx (M : Matrix _ _ R) := rfl

theorem spSLEquiv_symm_coe (g : SL(2, R)) :
    (((spSLEquiv R).symm g : symplecticGroup (Fin 1) R) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R) =
      reindex spIdx.symm spIdx.symm (g : Matrix (Fin 2) (Fin 2) R) := rfl

/-- Entrywise images of symplectic matrices are symplectic. -/
theorem sp_map_mem {S : Type*} [CommRing S] (f : R →+* S) (M : symplecticGroup (Fin 1) R) :
    (M : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R).map f ∈ symplecticGroup (Fin 1) S :=
  SymplecticGroup.map_mem M.2 f

end Ring

/-! ### The adelic group $\mathrm{Sp}_2(\mathbb A_F)$ -/

variable {F : Type} [Field F] [NumberField F]

variable (F) in
/-- $\mathrm{Sp}_2(\mathbb A_F)$, with the subspace topology from $M_2(\mathbb A_F)$ (blocks `Fin 1 ⊕ Fin 1`). -/
abbrev Sp2A : Type := symplecticGroup (Fin 1) (Adeles F)

instance : BorelSpace (Sp2A F) :=
  inferInstanceAs (BorelSpace {A : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) (Adeles F) //
    A ∈ symplecticGroup (Fin 1) (Adeles F)})

theorem continuous_spSLEquivA : Continuous (spSLEquiv (Adeles F)) := by
  refine Continuous.subtype_mk ?_ _
  exact (continuous_subtype_val).matrix_reindex _ _

theorem continuous_spSLEquivA_symm : Continuous (spSLEquiv (Adeles F)).symm := by
  refine Continuous.subtype_mk ?_ _
  exact (continuous_subtype_val).matrix_reindex _ _

variable (F) in
/-- $\mathrm{Sp}_2(\mathbb A_F)\cong\mathrm{SL}_2(\mathbb A_F)$ as topological groups. -/
def spSLEquivA : Sp2A F ≃ₜ* SL2A F :=
  { spSLEquiv (Adeles F) with
    continuous_toFun := continuous_spSLEquivA
    continuous_invFun := continuous_spSLEquivA_symm }

theorem spSLEquivA_apply (g : Sp2A F) : spSLEquivA F g = spSLEquiv (Adeles F) g := rfl

/-! ### The discrete subgroup $\mathrm{Sp}_2(F)$ and its right action -/

instance : Countable (Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) F) :=
  inferInstanceAs (Countable (Fin 1 ⊕ Fin 1 → Fin 1 ⊕ Fin 1 → F))

local instance : Countable (symplecticGroup (Fin 1) F) :=
  Function.Injective.countable (f := fun g : symplecticGroup (Fin 1) F =>
    (g : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) F)) Subtype.val_injective

variable (F) in
/-- The diagonal embedding $\mathrm{Sp}_2(F)\to\mathrm{Sp}_2(\mathbb A_F)$. -/
def spEmb : symplecticGroup (Fin 1) F →* Sp2A F where
  toFun M := Subtype.mk ((M : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) F).map (diagRing F))
    (SymplecticGroup.map_mem M.2 (diagRing F))
  map_one' := Subtype.ext (Matrix.map_one (diagRing F) (map_zero _) (map_one _))
  map_mul' M M' := Subtype.ext (Matrix.map_mul (f := diagRing F)
    (L := (M : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) F)) (M := (M' : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) F)))

/-- The embeddings commute with `spSLEquiv`: $\psi(\gamma) = \gamma$ for $\gamma\in\mathrm{Sp}_2(F)$. -/
theorem spSLEquivA_spEmb (γ : symplecticGroup (Fin 1) F) :
    spSLEquivA F (spEmb F γ) = slEmb F (spSLEquiv F γ) :=
  Matrix.SpecialLinearGroup.ext _ _ fun _ _ => rfl

/-- $\mathrm{Sp}_2(F)$ acts on $\mathrm{Sp}_2(\mathbb A_F)$ by right translation, $\gamma\cdot g = g\gamma^{-1}$; the
quotient is Weil's $G_{\mathbb A}/G_k$. -/
instance spRightAction : MulAction (symplecticGroup (Fin 1) F) (Sp2A F) where
  smul γ g := g * (spEmb F γ)⁻¹
  one_smul g := by show g * (spEmb F 1)⁻¹ = g; simp
  mul_smul γ δ g := by
    show g * (spEmb F (γ * δ))⁻¹ = g * (spEmb F δ)⁻¹ * (spEmb F γ)⁻¹
    rw [map_mul, _root_.mul_inv_rev, mul_assoc]

theorem spRight_smul_def (γ : symplecticGroup (Fin 1) F) (g : Sp2A F) : γ • g = g * (spEmb F γ)⁻¹ := rfl

instance : MeasurableConstSMul (symplecticGroup (Fin 1) F) (Sp2A F) :=
  ⟨fun γ => (continuous_id.mul continuous_const : Continuous fun g : Sp2A F => g * (spEmb F γ)⁻¹).measurable⟩

/-- The isomorphism intertwines the right actions of $\mathrm{Sp}_2(F)$ and $\mathrm{SL}_2(F)$. -/
theorem spSLEquivA_smul (γ : symplecticGroup (Fin 1) F) (g : Sp2A F) :
    spSLEquivA F (γ • g) = spSLEquiv F γ • spSLEquivA F g := by
  rw [spRight_smul_def, slRight_smul_def, map_mul, map_inv, spSLEquivA_spEmb]

/-! ### The Tamagawa measure and $\tau(\mathrm{Sp}_2) = 1$ -/

variable (F) in
/-- **The Tamagawa measure of $\mathrm{Sp}_2(\mathbb A_F)$**: the transport of the Tamagawa measure $\mu_T$ of
$\mathrm{SL}_2(\mathbb A_F)$ along the coordinate isomorphism $\mathrm{Sp}_2\cong\mathrm{SL}_2$ (defined over
$\mathbb Z$, so it matches the gauge forms and the local measures at every place). -/
def muSp2 : Measure (Sp2A F) := (muT F).map (spSLEquivA F).symm

theorem map_muSp2 : (muSp2 F).map (spSLEquivA F) = muT F := by
  have h1 : Measurable (spSLEquivA F) := (spSLEquivA F).continuous.measurable
  have h2 : Measurable (spSLEquivA F).symm := (spSLEquivA F).symm.continuous.measurable
  rw [muSp2, Measure.map_map h1 h2]
  convert Measure.map_id
  funext g
  exact (spSLEquivA F).apply_symm_apply g

/-- **The Tamagawa number of $\mathrm{Sp}_2$ over every number field is $1$**:
$\operatorname{vol}(\mathrm{Sp}_2(\mathbb A_F)/\mathrm{Sp}_2(F)) = 1$ for the Tamagawa measure `muSp2`, from
$\tau(\mathrm{SL}_2) = 1$ (`tamagawa_SL2`) through $\mathrm{Sp}_2\cong\mathrm{SL}_2$. -/
@[kb "weil1982" "§3.5 (τ(Sp_2n) = 1, case n = 1) [unverified locator]"]
theorem tamagawa_Sp2 : covolume (symplecticGroup (Fin 1) F) (Sp2A F) (muSp2 F) = 1 := by
  set φ := spSLEquivA F
  obtain ⟨D, hDm, hD⟩ := exists_measurableSet_forall_existsUnique_right (F := F)
  have hφm : Measurable φ := φ.continuous.measurable
  have hFD : IsFundamentalDomain (SL(2, F)) D (muT F) := IsFundamentalDomain.mk' hDm.nullMeasurableSet hD
  -- the pulled-back fundamental domain
  have hD' : ∀ g : Sp2A F, ∃! γ : symplecticGroup (Fin 1) F, γ • g ∈ φ ⁻¹' D := by
    intro g
    obtain ⟨δ, hδ, huniq⟩ := hD (φ g)
    refine ⟨(spSLEquiv F).symm δ, ?_, fun γ hγ => ?_⟩
    · show φ (_ • g) ∈ D
      rw [spSLEquivA_smul, MulEquiv.apply_symm_apply]; exact hδ
    · have hγ' : φ (γ • g) ∈ D := hγ
      rw [spSLEquivA_smul] at hγ'
      rw [← huniq _ hγ', MulEquiv.symm_apply_apply]
  have hinv : SMulInvariantMeasure (symplecticGroup (Fin 1) F) (Sp2A F) (muSp2 F) := by
    refine ⟨fun γ s hs => ?_⟩
    have := smulInvariantMeasure_SL2A (muT F)
    have h2 : Measurable (spSLEquivA F).symm := (spSLEquivA F).symm.continuous.measurable
    have hs' : MeasurableSet ((fun g : Sp2A F => γ • g) ⁻¹' s) := (measurable_const_smul γ) hs
    have hpre : (spSLEquivA F).symm ⁻¹' ((fun g : Sp2A F => γ • g) ⁻¹' s) =
        (fun h : SL2A F => spSLEquiv F γ • h) ⁻¹' ((spSLEquivA F).symm ⁻¹' s) := by
      ext h
      simp only [Set.mem_preimage]
      have : γ • (spSLEquivA F).symm h = (spSLEquivA F).symm (spSLEquiv F γ • h) := by
        apply (spSLEquivA F).injective
        rw [spSLEquivA_smul]; simp
      rw [this]
    rw [muSp2, Measure.map_apply h2 hs', Measure.map_apply h2 hs, hpre]
    exact measure_preimage_smul (μ := muT F) (spSLEquiv F γ) _
  have hFD' : IsFundamentalDomain (symplecticGroup (Fin 1) F) (φ ⁻¹' D) (muSp2 F) :=
    IsFundamentalDomain.mk' (hφm hDm).nullMeasurableSet hD'
  rw [hFD'.covolume_eq_volume, ← Measure.map_apply hφm hDm, map_muSp2, ← hFD.covolume_eq_volume]
  exact tamagawa_SL2

end

end QuadFormsKB.Tamagawa.Measure.Weil
