/-
# Hanke, Arizona Winter School 2009 notes, Ch. 1: Witt's theorem (Thm 1.5.5) and Lemma 1.8.1

J. Hanke, *Quadratic Forms and Automorphic Forms*, Arizona Winter School 2009 notes, arXiv:1105.5759 v3
(bibkey `hanke2011aws`; PDF page = printed page). Two items of Chapter 1 not covered by `NotesCh1.lean`:

- Thm 1.5.5, p. 16 (Witt's theorem for a possibly degenerate ambient space): `theorem_1_5_5`.
- Lemma 1.8.1, p. 19 (splitting a lattice along a nondegenerate subspace over a PID): the printed statement is
  false (`lemma_1_8_1_printed_false`); the corrected statement is `lemma_1_8_1`.
  See the *Erratum* in the docstring of `lemma_1_8_1`.
-/
import QuadFormsKB.Witt.Extension
import QuadFormsKB.Literature.Cassels.Ch2.Basic
import QuadFormsKB.Literature.OMeara.Sec82

open Module QuadraticMap

namespace QuadFormsKB.AWS.Notes

section WittThm

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- For $2$ invertible, $B(x,y) = \tfrac12 (Q(x+y)-Q(x)-Q(y))$ (`QuadraticMap.associated`) is $\tfrac12$ the polar form. -/
theorem associated_eq_polar [Invertible (2 : K)] (Q : QuadraticForm K V) (x y : V) :
    associated Q x y = ⅟2 * polar Q x y := by
  rw [associated_apply]
  simp [polar, smul_eq_mul]

/-- **Witt's extension theorem** (Hanke, Arizona Winter School notes, Thm 1.5.5, p. 16): "Suppose that $U$ and $U'$ are non-degenerate
isometric (quadratic) subspaces of a quadratic space $V$. Then any isometry $\alpha : U \to U'$ extends to an
isometry $\alpha : V \to V$." Here the ambient space may be **degenerate**.

**Hypotheses.** $K$ is a field in which $2$ is invertible (`[Invertible (2 : K)]`); $V$ is a finite-dimensional
$K$-vector space with a quadratic form $Q$ (possibly with nonzero radical); $B = $ `associated Q`,
$B(x,y) = \tfrac12(Q(x+y)-Q(x)-Q(y))$. $U \subseteq V$ is a subspace on which $B$ restricts to a nondegenerate
form (`hU`). $\sigma : U \to V$ is a $K$-linear map with $Q(\sigma u) = Q(u)$ for all $u \in U$ (`hσ`).

**Conclusion.** There is an isometry $\rho : (V,Q) \to (V,Q)$ (a linear equivalence with $Q \circ \rho = Q$) with
$\rho|_U = \sigma$.

*Update (generalization):* the notes take $\alpha : U \to U'$ to be an isometry onto a nondegenerate subspace
$U' = \sigma(U)$. Here only $Q\circ\sigma = Q|_U$ is assumed: injectivity of $\sigma$ and nondegeneracy of
$\sigma(U)$ follow from nondegeneracy of $U$ (the polar form is preserved) and are not hypotheses. The proof splits
$V = R \oplus V_1$ with $R$ the radical and $V_1$ nondegenerate, applies Witt's theorem on $V_1$
(`QuadraticForm.exists_isometryEquiv_extend_of_nondegenerate`) to the projection of $\sigma$, and corrects the
$R$-component by a linear map $V_1 \to R$. -/
@[kb "hanke2011aws" "§1.5, Thm. 1.5.5, p. 16"]
theorem theorem_1_5_5 [FiniteDimensional K V] [Invertible (2 : K)] (Q : QuadraticForm K V)
    {U : Submodule K V} (hU : (LinearMap.BilinForm.restrict (associated Q) U).Nondegenerate)
    (σ : U →ₗ[K] V) (hσ : ∀ u, Q (σ u) = Q u) :
    ∃ ρ : Q.IsometryEquiv Q, ∀ u : U, ρ u = σ u := by
  classical
  set B : LinearMap.BilinForm K V := QuadraticMap.polarBilin Q with hBdef
  have hB : B.IsSymm := ⟨fun x y => by
    simp only [hBdef, QuadraticMap.polarBilin_apply_apply]; exact QuadraticMap.polar_comm Q x y⟩
  obtain ⟨V₁, hRV, hreg⟩ := QuadFormsKB.Cassels.exists_regular_compl_radical hB
  set R := B.orthogonal ⊤ with hRdef
  have hR : ∀ r ∈ R, ∀ x, polar Q x r = 0 := fun r hr x =>
    (LinearMap.BilinForm.mem_orthogonal_iff.mp hr) x Submodule.mem_top
  have hQr : ∀ r ∈ R, Q r = 0 := fun r hr => by
    have h := hR r hr r
    rw [QuadraticMap.polar_self, two_smul] at h
    have h2 : (2 : K) * Q r = 0 := by rw [two_mul]; exact h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 (Invertible.ne_zero (2 : K))
    · exact h3
  have hadd : ∀ (a r : V), r ∈ R → Q (a + r) = Q a := fun a r hr => by
    rw [QuadraticMap.map_add Q a r, hQr r hr, hR r hr a, add_zero, add_zero]
  -- the projections
  let πR : V →ₗ[K] R := Submodule.projectionOnto R V₁ hRV
  let π₁ : V →ₗ[K] V₁ := Submodule.projectionOnto V₁ R hRV.symm
  have hsplit : ∀ x, (πR x : V) + (π₁ x : V) = x := fun x => by
    have := Submodule.projection_add_projection_eq_self hRV x
    simpa [πR, π₁, Submodule.coe_projectionOnto_apply] using this
  have hπ₁_R : ∀ r : R, π₁ r = 0 := fun r => Submodule.projectionOnto_apply_right hRV.symm r
  have hπ₁_V₁ : ∀ v : V₁, π₁ v = v := fun v => Submodule.projectionOnto_apply_left hRV.symm v
  have hQπ : ∀ x, Q x = Q (π₁ x) := fun x => by
    conv_lhs => rw [← hsplit x, add_comm]
    exact hadd _ _ (πR x).2
  -- the nondegenerate part
  let Q₁ : QuadraticForm K V₁ := Q.comp V₁.subtype
  have hQ₁ : ∀ v : V₁, Q₁ v = Q v := fun v => rfl
  have hnd : (QuadraticMap.polarBilin Q₁).Nondegenerate := by
    have : QuadraticMap.polarBilin Q₁ = B.restrict V₁ := by
      ext x y
      simp [hBdef, Q₁, QuadraticMap.polar]
    rw [this]; exact hreg
  -- U meets the radical trivially, and so does σ U
  have hUnd : ∀ u : U, (∀ y : U, polar Q (y : V) u = 0) → u = 0 := fun u h => by
    refine hU.1 u fun y => ?_
    have := h y
    rw [QuadraticMap.polar_comm] at this
    simp [associated_eq_polar, this]
  have hUR : ∀ u : U, (u : V) ∈ R → u = 0 := fun u hu => hUnd u fun y => hR _ hu _
  have hpolσ : ∀ a b : U, polar Q (σ a) (σ b) = polar Q (a : V) (b : V) := fun a b => by
    simp only [polar, ← map_add, hσ, Submodule.coe_add]
  have hσR : ∀ u : U, σ u ∈ R → u = 0 := fun u hu => hUnd u fun y => by
    rw [← hpolσ]; exact hR _ hu _
  let f : U →ₗ[K] V₁ := π₁ ∘ₗ U.subtype
  let g : U →ₗ[K] V₁ := π₁ ∘ₗ σ
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    apply hUR
    have := hsplit (u : V)
    have h0 : (π₁ (u : V) : V) = 0 := by simpa [f] using congrArg (fun v : V₁ => (v : V)) hu
    rw [h0, add_zero] at this
    rw [← this]; exact (πR u).2
  have hg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    apply hσR
    have := hsplit (σ u)
    have h0 : (π₁ (σ u) : V) = 0 := by simpa [g] using congrArg (fun v : V₁ => (v : V)) hu
    rw [h0, add_zero] at this
    rw [← this]; exact (πR (σ u)).2
  let e : U ≃ₗ[K] LinearMap.range f := LinearEquiv.ofInjective f hf
  let τ : LinearMap.range f →ₗ[K] V₁ := g ∘ₗ e.symm.toLinearMap
  have hτi : Function.Injective τ := hg.comp e.symm.injective
  have hτQ : ∀ w, Q₁ (τ w) = Q₁ w := fun w => by
    obtain ⟨u, rfl⟩ := e.surjective w
    simp only [τ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, g, e,
      LinearEquiv.ofInjective_apply, f, Submodule.subtype_apply, hQ₁]
    rw [← hQπ, hσ, hQπ (u : V)]
  obtain ⟨ρ₁, hρ₁⟩ := QuadraticForm.exists_isometryEquiv_extend_of_nondegenerate Q₁ hnd
    (W := LinearMap.range f) τ hτi hτQ
  have hρu : ∀ u : U, ρ₁ (π₁ (u : V)) = π₁ (σ u) := fun u => by
    have := hρ₁ (e u)
    simp only [τ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, g, e,
      LinearEquiv.ofInjective_apply, f, Submodule.subtype_apply] at this
    exact this
  -- the radical component
  let f₀ : LinearMap.range f →ₗ[K] R :=
    (πR ∘ₗ σ - πR ∘ₗ U.subtype) ∘ₗ e.symm.toLinearMap
  obtain ⟨γ, hγ⟩ := LinearMap.exists_extend f₀
  have hγu : ∀ u : U, γ (π₁ (u : V)) = πR (σ u) - πR (u : V) := fun u => by
    have := LinearMap.congr_fun hγ (e u)
    simpa [f₀, e, f] using this
  let L : V →ₗ[K] V := R.subtype ∘ₗ πR + (V₁.subtype ∘ₗ (ρ₁.toLinearEquiv : V₁ →ₗ[K] V₁) ∘ₗ π₁) +
    R.subtype ∘ₗ γ ∘ₗ π₁
  have hL : ∀ x, L x = ((πR x : R) : V) + ((ρ₁ (π₁ x) : V₁) : V) + ((γ (π₁ x) : R) : V) :=
    fun x => rfl
  have hLinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 : π₁ (L x) = ρ₁ (π₁ x) := by
      rw [hL, map_add, map_add, hπ₁_R, hπ₁_V₁, hπ₁_R, zero_add, add_zero]
    rw [hx, map_zero] at h1
    have h2 : π₁ x = 0 := by
      have : ρ₁.toLinearEquiv (π₁ x) = 0 := h1.symm
      simpa using this
    have h3 := hL x
    rw [hx, h2] at h3
    simp only [map_zero, ZeroMemClass.coe_zero, add_zero] at h3
    have := hsplit x
    rw [h2] at this
    simp only [ZeroMemClass.coe_zero, add_zero] at this
    rw [← this]
    exact h3.symm
  refine ⟨⟨LinearEquiv.ofInjectiveEndo L hLinj, fun x => ?_⟩, fun u => ?_⟩
  · show Q (L x) = Q x
    rw [hL, add_right_comm, add_comm]
    have hmem : ((πR x : R) : V) + ((γ (π₁ x) : R) : V) ∈ R := R.add_mem (πR x).2 (γ (π₁ x)).2
    rw [hadd _ _ hmem]
    have := ρ₁.map_app (π₁ x)
    rw [hQπ x]
    exact this
  · show L u = σ u
    rw [hL, hρu, hγu]
    conv_rhs => rw [← hsplit (σ u)]
    simp only [Submodule.coe_sub]
    abel

end WittThm


section Lemma181

open QuadFormsKB.OMeara Submodule

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
  {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
  (Q : QuadraticForm F V)

omit [Invertible (2 : F)] in
/-- Over a PID, a nonzero finitely generated $R$-submodule of the fraction field is $\alpha R$, $\alpha \neq 0$. -/
theorem exists_span_singleton_of_fg {a : Submodule R F} (ha : a.FG) (h0 : a ≠ ⊥) :
    ∃ α : F, α ≠ 0 ∧ a = R ∙ α := by
  let I : FractionalIdeal (nonZeroDivisors R) F :=
    ⟨a, FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors R) ha⟩
  have hI : (I : Submodule R F) = a := rfl
  have hp : (I : Submodule R F).IsPrincipal := inferInstance
  refine ⟨Submodule.IsPrincipal.generator (I : Submodule R F), ?_, ?_⟩
  · intro h
    apply h0
    rw [← hI, ← Submodule.IsPrincipal.span_singleton_generator (I : Submodule R F), h]
    simp
  · rw [← hI]; exact (Submodule.IsPrincipal.span_singleton_generator _).symm

omit [Invertible (2 : F)] in
include F in
/-- A finitely generated $R$-submodule of an $F$-vector space ($R$ a PID with fraction field $F$) is free. -/
theorem exists_basis_pid {L : Submodule R V} (hL : L.FG) :
    Nonempty (Basis (Fin (finrank R L)) R L) := by
  have := isTorsionFree_of_fractionRing (R := R) (F := F) (V := V)
  have : Module.Finite R L := Module.Finite.iff_fg.mpr hL
  have : Module.Free R L := Module.free_of_finite_type_torsion_free'
  exact ⟨Module.finBasis R L⟩

/-- **Lemma 1.8.1, corrected** (Hanke, Arizona Winter School notes, §1.8, p. 19). Printed: "Suppose that $R$ is a principal ideal
domain, $L$ is a quadratic $R$-lattice in the quadratic space $(V,Q)$, and $W$ is a non-degenerate subspace of
$(V,Q)$. If $\mathrm{Scale}(L \cap W) = \mathrm{Scale}(L)$, then we can write $L = (L\cap W) \oplus (L\cap W^\perp)$."

**Hypotheses.** $R$ is a PID with fraction field $F$, $2 \in F^\times$; $(V,Q)$ is a quadratic space over $F$;
$B =$ `associated Q` (so $\mathrm{Scale}_B = \tfrac12\mathrm{Scale}_H$, and the two scales are equal exactly when
the Hessian scales are). $L \subseteq V$ is a lattice: a finitely generated $R$-submodule (`hLfg`) spanning $V$
over $F$ (`hLspan`). $W \subseteq V$ is an $F$-subspace on which $B$ is nondegenerate (`hW`).
**Corrected hypothesis** (`hmod`): $L \cap W$ is *modular of scale $\mathrm{Scale}(L)$* (O'Meara's
`OMeara.IsModular`): $\mathrm{Scale}(L\cap W) = \mathrm{Scale}(L) =: \alpha R \ne 0$ **and**
$\mathfrak v(L\cap W) = (\alpha R)^{k}$, $k = \mathrm{rank}(L \cap W)$, i.e. the Gram matrix of $B$ on an
$R$-basis of $L\cap W$ is $\alpha U$ with $U \in \mathrm{GL}_k(R)$ (`OMeara.isModular_iff_gram`).

**Conclusion.** $L = (L \cap W) \perp (L\cap W^\perp)$ (`OMeara.IsOrthSum`): the two sublattices are $B$-orthogonal,
intersect in $0$, and sum to $L$.

*Erratum:* the printed hypothesis $\mathrm{Scale}(L\cap W) = \mathrm{Scale}(L)$ alone does not suffice; the notes'
proof implicitly uses that, after scaling $\mathrm{Scale}(L)$ to $R$, the Hessian matrix of $L\cap W$ lies in
$\mathrm{GL}_k(R)$. Counterexample (`lemma_1_8_1_printed_false`): $R=\mathbb Z$, $L=\mathbb Z^3$,
$Q = x_0^2+2x_1^2+2x_1x_2$, $W=\{x_2=0\}$: $\mathrm{Scale}(L\cap W) = \mathrm{Scale}(L)$ and $W$ is nondegenerate,
but $L\cap W = \mathbb Z^2$ has Gram matrix $\mathrm{diag}(1,2)$ (determinant $2$) and $L \ne (L\cap W)\oplus K$ for
every $K$. (For a DVR this is O'Meara 82:15a, `OMeara.splits_of_isModular_of_scale_eq`, with the same modularity
hypothesis.) Also, the printed lemma needs $L$ to span $V$ (a lattice *on* $V$), as assumed here. -/
@[kb "hanke2011aws" "§1.8, Lemma 1.8.1, p. 19"]
theorem lemma_1_8_1 {L : Submodule R V} (hLfg : L.FG) (hLspan : span F (L : Set V) = ⊤)
    {W : Submodule F V} (hW : (LinearMap.BilinForm.restrict (associated Q) W).Nondegenerate)
    (hmod : IsModular Q (scale Q L) (L ⊓ W.restrictScalars R)) :
    IsOrthSum Q L (L ⊓ W.restrictScalars R)
      (L ⊓ (LinearMap.BilinForm.orthogonal (associated Q) W).restrictScalars R) := by
  classical
  set J := L ⊓ W.restrictScalars R with hJ
  have hJL : J ≤ L := inf_le_left
  have hJfg : J.FG := Submodule.FG.of_le hLfg hJL
  obtain ⟨α, hα0, hα⟩ := exists_span_singleton_of_fg (scale_fg Q hLfg) hmod.1
  rw [hα] at hmod
  obtain ⟨b⟩ := exists_basis_pid (R := R) (F := F) hJfg
  obtain ⟨-, U, hU, hG⟩ := (isModular_iff_gram Q b hα0).mp hmod
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy
    have hxW : x ∈ W := hx.2
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hy.2) x hxW
  · rw [Submodule.disjoint_def]
    intro x hxJ hxK
    have hxW : x ∈ W := hxJ.2
    have := hW.1 ⟨x, hxW⟩ (fun y => by
      rw [LinearMap.BilinForm.restrict_apply]
      have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hxK.2) y y.2
      have h' : associated Q (y : V) x = 0 := h
      exact (bil_comm Q x (y : V)).trans h')
    simpa using congrArg Subtype.val this
  · refine le_antisymm (sup_le hJL inf_le_left) ?_
    intro x hx
    have hxj : ∀ j, bil Q x (b j : V) ∈ R ∙ α := fun j => by
      rw [← hα]; exact bil_mem_scale Q hx (hJL (b j).2)
    obtain ⟨y, hyJ, hy⟩ := exists_mem_bil_eq_of_gram Q b hU hG hxj
    refine Submodule.mem_sup.mpr ⟨y, hyJ, x - y, ⟨L.sub_mem hx (hJL hyJ), ?_⟩, by abel⟩
    show x - y ∈ (LinearMap.BilinForm.orthogonal (associated Q) W)
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    obtain ⟨d, hd, hdw⟩ := exists_smul_mem_of_mem_span (S := L) (x := w) (hLspan ▸ Submodule.mem_top)
    have hdwJ : d • w ∈ J := ⟨hdw, W.smul_of_tower_mem d hw⟩
    have h1 : bil Q (d • w) (x - y) = 0 := by
      rw [bil_comm, bil_sub_left, hy _ hdwJ, sub_self]
    rw [bil_rsmul_left] at h1
    have hd' : algebraMap R F d ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hd
    exact (mul_eq_zero.mp h1).resolve_left hd'

end Lemma181

section Counterexample

open QuadFormsKB.OMeara Submodule

local instance : Invertible (2 : ℚ) := invertibleOfNonzero (by norm_num)

/-- The counterexample form $Q(x) = x_0^2 + 2x_1^2 + 2x_1x_2$ on $\mathbb Q^3$. -/
def exQ : QuadraticForm ℚ (Fin 3 → ℚ) := Matrix.toQuadraticForm' !![1, 0, 0; 0, 2, 1; 0, 1, 0]

theorem exQ_apply (x : Fin 3 → ℚ) : exQ x = x 0 ^ 2 + 2 * x 1 ^ 2 + 2 * x 1 * x 2 := by
  simp [exQ, Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply', Matrix.vecHead, Matrix.vecTail]
  ring

theorem exB (x y : Fin 3 → ℚ) :
    bil exQ x y = x 0 * y 0 + 2 * x 1 * y 1 + x 1 * y 2 + x 2 * y 1 := by
  show associated exQ x y = _
  rw [associated_eq_polar]
  simp only [polar, exQ_apply, Pi.add_apply, invOf_eq_inv]
  ring

/-- The lattice $\mathbb Z^3 \subset \mathbb Q^3$. -/
def exL : Submodule ℤ (Fin 3 → ℚ) := span ℤ (Set.range fun i : Fin 3 => Pi.single i (1 : ℚ))

theorem exL_int {x : Fin 3 → ℚ} (hx : x ∈ exL) : ∀ i, ∃ n : ℤ, x i = n := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
  intro i
  refine ⟨c i, ?_⟩
  simp [Finset.sum_apply, Pi.single_apply]

theorem single_mem_exL (i : Fin 3) : (Pi.single i (1 : ℚ) : Fin 3 → ℚ) ∈ exL :=
  subset_span ⟨i, rfl⟩

/-- The plane $x_2 = 0$. -/
def exW : Submodule ℚ (Fin 3 → ℚ) := LinearMap.ker (LinearMap.proj 2 : (Fin 3 → ℚ) →ₗ[ℚ] ℚ)

theorem mem_exW {x : Fin 3 → ℚ} : x ∈ exW ↔ x 2 = 0 := by simp [exW]

theorem single_mem_J (i : Fin 3) (hi : i ≠ 2) :
    (Pi.single i (1 : ℚ) : Fin 3 → ℚ) ∈ exL ⊓ exW.restrictScalars ℤ :=
  ⟨single_mem_exL i, by simp [mem_exW, Pi.single_apply, hi.symm]⟩

theorem exW_zero (x : Fin 3 → ℚ) (h2 : x 2 = 0) (h0 : x 0 = 0) (h1 : 2 * x 1 = 0) : x = 0 := by
  funext i
  fin_cases i <;> simp_all

/-- **Lemma 1.8.1 as printed is false.** There are a lattice $L = \mathbb Z^3$ in $(\mathbb Q^3, Q)$,
$Q = x_0^2+2x_1^2+2x_1x_2$, and a nondegenerate plane $W = \{x_2 = 0\}$ with $\mathrm{Scale}(L\cap W)=\mathrm{Scale}(L)$
(equivalently for the Hessian scale, $\mathrm{Scale}_H = 2\,\mathrm{Scale}_B$) such that there is **no** sublattice $K$ with
$L = (L\cap W) \perp K$ (in particular not $K = L\cap W^\perp$). Here $L \cap W$ has Gram matrix
$\mathrm{diag}(1,2)$, not modular. See `lemma_1_8_1` for the corrected statement. -/
theorem lemma_1_8_1_printed_false :
    ∃ (L : Submodule ℤ (Fin 3 → ℚ)) (W : Submodule ℚ (Fin 3 → ℚ)) (Q : QuadraticForm ℚ (Fin 3 → ℚ)),
      L.FG ∧ span ℚ (L : Set (Fin 3 → ℚ)) = ⊤ ∧
      (LinearMap.BilinForm.restrict (associated Q) W).Nondegenerate ∧
      scale Q (L ⊓ W.restrictScalars ℤ) = scale Q L ∧
      ¬ ∃ K : Submodule ℤ (Fin 3 → ℚ), IsOrthSum Q L (L ⊓ W.restrictScalars ℤ) K := by
  refine ⟨exL, exW, exQ, Submodule.fg_span (Set.finite_range _), ?_, ?_, ?_, ?_⟩
  · rw [eq_top_iff, ← (Pi.basisFun ℚ (Fin 3)).span_eq]
    refine span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact subset_span (by simpa using single_mem_exL i)
  · have hsymm : ∀ x y : Fin 3 → ℚ, bil exQ x y = bil exQ y x := fun x y => bil_comm exQ x y
    constructor
    · intro x hx
      have h0 := hx ⟨Pi.single 0 1, by simp [mem_exW]⟩
      have h1 := hx ⟨Pi.single 1 1, by simp [mem_exW]⟩
      simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply] at h0 h1
      have h0' := h0
      have h1' := h1
      change bil exQ (x : Fin 3 → ℚ) _ = 0 at h0' h1'
      rw [exB] at h0' h1'
      have hx2 : (x : Fin 3 → ℚ) 2 = 0 := mem_exW.mp x.2
      refine Subtype.ext (exW_zero _ hx2 ?_ ?_) <;> simp [Pi.single_apply] at h0' h1' ⊢ <;> linarith
    · intro y hy
      have h0 := hy ⟨Pi.single 0 1, by simp [mem_exW]⟩
      have h1 := hy ⟨Pi.single 1 1, by simp [mem_exW]⟩
      simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply] at h0 h1
      have h0' := h0
      have h1' := h1
      change bil exQ _ (y : Fin 3 → ℚ) = 0 at h0' h1'
      rw [exB] at h0' h1'
      have hy2 : (y : Fin 3 → ℚ) 2 = 0 := mem_exW.mp y.2
      refine Subtype.ext (exW_zero _ hy2 ?_ ?_) <;> simp [Pi.single_apply] at h0' h1' ⊢ <;> linarith
  · refine le_antisymm (scale_mono exQ inf_le_left) ?_
    refine span_le.mpr ?_
    rintro _ ⟨x, hx, y, hy, rfl⟩
    obtain ⟨a0, ha0⟩ := exL_int hx 0
    obtain ⟨a1, ha1⟩ := exL_int hx 1
    obtain ⟨a2, ha2⟩ := exL_int hx 2
    obtain ⟨b0, hb0⟩ := exL_int hy 0
    obtain ⟨b1, hb1⟩ := exL_int hy 1
    obtain ⟨b2, hb2⟩ := exL_int hy 2
    have h1 : (1 : ℚ) ∈ scale exQ (exL ⊓ exW.restrictScalars ℤ) := by
      have := bil_mem_scale exQ (single_mem_J 0 (by decide)) (single_mem_J 0 (by decide))
      rw [exB] at this
      simpa [Pi.single_apply] using this
    have : bil exQ x y = ((a0 * b0 + 2 * a1 * b1 + a1 * b2 + a2 * b1 : ℤ) : ℤ) • (1 : ℚ) := by
      rw [exB, ha0, ha1, ha2, hb0, hb1, hb2, zsmul_eq_mul]; push_cast; ring
    rw [this]
    exact Submodule.smul_mem _ _ h1
  · rintro ⟨K, hK⟩
    have he2 : (Pi.single 2 (1 : ℚ) : Fin 3 → ℚ) ∈ exL ⊓ exW.restrictScalars ℤ ⊔ K := by
      rw [hK.sup_eq]; exact single_mem_exL 2
    obtain ⟨j, hj, k, hk, hjk⟩ := Submodule.mem_sup.mp he2
    have hj2 : j 2 = 0 := mem_exW.mp hj.2
    obtain ⟨n, hn⟩ := exL_int hj.1 1
    have o0 := hK.orth _ (single_mem_J 0 (by decide)) k hk
    have o1 := hK.orth _ (single_mem_J 1 (by decide)) k hk
    rw [exB] at o0 o1
    have c1 := congrFun hjk 1
    have c2 := congrFun hjk 2
    simp [Pi.single_apply] at o0 o1 c1 c2
    have : (2 * n : ℚ) = 1 := by linarith
    have : (2 * n : ℤ) = 1 := by exact_mod_cast this
    omega

end Counterexample
end QuadFormsKB.AWS.Notes
