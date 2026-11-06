/-
# O'Meara §53: extending the field of scalars (running text, pp. 129-131)

**Setting.** $E/F$ an extension of fields (O'Meara: arbitrary), $V$ an $F$-space.  O'Meara's $E$-ification
$EV$ of $V$ is, in the library, the concrete $E \otimes_F V$ (`TensorProduct`), and the abstract notion
"an $E$-space $T$ containing $V$ in which every $F$-base of $V$ is an $E$-base" corresponds to Mathlib's
`IsBaseChange E j` for the inclusion $j : V \to T$.  For a quadratic space $(V, Q)$ over $F$ with
$2$ invertible, $B$ is `QuadraticMap.associated Q` (`QuadFormsKB.OMeara.bil Q`) and the $E$-ification of the
quadratic space is Mathlib's `Q.baseChange E`.  The radical is the kernel of `QuadraticMap.associated Q`.
O'Meara assumes all spaces finite dimensional; the finite-dimensionality hypothesis is made below only where
the proof needs it (53.r17, 53.r18 use a finite base).  Indices are 0-based.

**Defines** (namespace `QuadFormsKB.OMeara.Ext53`)
* `IsEification j`: an $F$-linear $j : V \to T$ into an $E$-space $T$ is an $E$-ification of $V$ if it maps
  every $F$-base of $V$ to an $E$-base of $T$ (53A, p. 129).  Used only to state the comparison with Mathlib.
* `rad Q`: helper, the radical $\{x : B(x, V) = 0\}$ as a kernel (equal to the library's `splitComp Q ⊤ ⊤`).

**Proves**
* `isEification_iff_isBaseChange` (53A, p. 129): `IsEification j ↔ IsBaseChange E j`;
  `isEification_of_basis` (53.r3): one base mapped to a base suffices;
* `one_tmul_injective'` (53.r1), `isEification_tmul` (53.r4: existence);
* `exists_unique_lift`, `exists_unique_linearEquiv` (53.r6: uniqueness);
* `finrank_eification` (53.r7): $\dim_E EV = \dim_F V$;
* `isEification_baseChange_submodule` (53.r8): the $E$-span of $U$ in $EV$ is an $E$-ification of $U$;
* `isInternal_baseChange` (53.r9): $V = \bigoplus U_i$ implies $EV = \bigoplus EU_i$;
* `isInternal_orthogonal_baseChange` (53.r16): the same for $\perp$-splittings of quadratic spaces;
* `splitComp_baseChange` (53.r17): $\operatorname{rad} EV = E \operatorname{rad} V$ (via `rad_baseChange`);
* `gram_baseChange`, `det_gram_baseChange`, `disc_baseChange` (53.r18): $V$ and $EV$ have the same matrix
  in a base of $V$, hence the discriminants correspond.
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.OMeara.Sec82
import QuadFormsKB.Literature.OMeara.Sec58Bases

open scoped TensorProduct
open Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.Ext53

universe v

section Spaces

variable {F E : Type*} [Field F] [Field E] [Algebra F E]
variable {V : Type v} [AddCommGroup V] [Module F V]
variable {T : Type*} [AddCommGroup T] [Module E T] [Module F T] [IsScalarTower F E T]

/-- **$E$-ification of an $F$-space** (O'Meara 1963, §53A, p. 129): an $F$-linear map $j : V \to T$ into an
$E$-space $T$ is an $E$-ification of $V$ if every $F$-base of $V$ is carried to an $E$-base of $T$, i.e. for
every $F$-base $b$ of $V$ (indexed by $\iota$) there is an $E$-base of $T$ whose $i$-th vector is $j(b_i)$.
*Deviation:* O'Meara requires $V \subseteq T$ (a subset with induced laws); here the inclusion is the
$F$-linear map $j$, which is automatically injective (it maps a base to a linearly independent family). -/
@[kb "omeara1963" "§53, p. 129 (E-ification of an F-space)"]
def IsEification (j : V →ₗ[F] T) : Prop :=
  ∀ {ι : Type v} (b : Basis ι F V), ∃ b' : Basis ι E T, ∀ i, b' i = j (b i)

/-- If one $F$-base of $V$ is carried by $j$ to an $E$-base of $T$, then $j$ is the base change of $V$
to $E$ (Mathlib's `IsBaseChange E j`). -/
theorem isBaseChange_of_basis {ι : Type*} {j : V →ₗ[F] T} (b : Basis ι F V) (b' : Basis ι E T)
    (h : ∀ i, b' i = j (b i)) : IsBaseChange E j := by
  have hb := TensorProduct.isBaseChange F V E
  let c := hb.basis b
  let e : E ⊗[F] V ≃ₗ[E] T := c.equiv b' (Equiv.refl ι)
  have comm : j.comp (LinearEquiv.refl F V).toLinearMap =
      (e.restrictScalars F).comp (TensorProduct.mk F E V 1) := by
    refine b.ext fun i => ?_
    have h1 : c i = TensorProduct.mk F E V 1 (b i) := hb.basis_apply b i
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.refl_apply,
      LinearEquiv.restrictScalars_apply]
    rw [← h1, Basis.equiv_apply, ← h]
    rfl
  exact (IsBaseChange.iff_of_equiv_comm (LinearEquiv.refl F V) e comm).mp hb |> fun h' => by
    simpa using h'

/-- **Comparison** (O'Meara 1963, §53A, p. 129): O'Meara's abstract notion of an $E$-ification coincides
with Mathlib's `IsBaseChange E j`. -/
@[kb "omeara1963" "§53A, p. 129 (E-ification = IsBaseChange)"]
theorem isEification_iff_isBaseChange (j : V →ₗ[F] T) : IsEification (E := E) j ↔ IsBaseChange E j := by
  constructor
  · intro h
    obtain ⟨b', hb'⟩ := h (Basis.ofVectorSpace F V)
    exact isBaseChange_of_basis (Basis.ofVectorSpace F V) b' hb'
  · intro h ι b
    exact ⟨h.basis b, fun i => h.basis_apply b i⟩

/-- **53.r3** (O'Meara 1963, §53A, p. 129): if some $F$-base of $V$ is carried by $j$ to an $E$-base of $T$,
then every base is, so $T$ is an $E$-ification of $V$. -/
@[kb "omeara1963" "§53A, p. 129 (one base mapped to a base suffices)"]
theorem isEification_of_basis {ι : Type v} {j : V →ₗ[F] T} (b : Basis ι F V) (b' : Basis ι E T)
    (h : ∀ i, b' i = j (b i)) : IsEification (E := E) j :=
  (isEification_iff_isBaseChange j).mpr (isBaseChange_of_basis b b' h)

/-- **53.r1** (O'Meara 1963, §53A, p. 129): $V \subseteq EV$, i.e. the map $x \mapsto 1 \otimes x$ of $V$ into
$E \otimes_F V$ is injective.  This restates `QuadFormsKB.OMeara.Sp58.one_tmul_injective`. -/
@[kb "omeara1963" "§53A, p. 129 (V embeds in E ⊗ V)"]
theorem one_tmul_injective' [Invertible (2 : F)] [FiniteDimensional F V] :
    Function.Injective (fun v : V => (1 : E) ⊗ₜ[F] v) :=
  QuadFormsKB.OMeara.Sp58.one_tmul_injective

/-- **53.r4, existence** (O'Meara 1963, §53A, p. 129): every $F$-space $V$ has an $E$-ification, namely
$E \otimes_F V$ with $x \mapsto 1 \otimes x$.  (O'Meara's construction transports a disjoint $E$-space
by "the identification process"; the tensor product is the library's model.) -/
@[kb "omeara1963" "§53A, p. 129 (existence of E-ifications)"]
theorem isEification_tmul : IsEification (E := E) (TensorProduct.mk F E V 1) :=
  (isEification_iff_isBaseChange _).mpr (TensorProduct.isBaseChange F V E)

variable {j : V →ₗ[F] T}

/-- **53.r6, universal property** (O'Meara 1963, §53A, p. 130): if $T$ is an $E$-ification of $V$ and $T'$ is
any $E$-space with an $F$-linear $j' : V \to T'$ (O'Meara: $T' \supseteq V$, $j'$ the inclusion), there is exactly one
$E$-linear map $g : T \to T'$ with $g \circ j = j'$. -/
@[kb "omeara1963" "§53A, p. 130 (unique E-linear extension)"]
theorem exists_unique_lift (hj : IsEification (E := E) j) {T' : Type*} [AddCommGroup T']
    [Module E T'] [Module F T'] [IsScalarTower F E T'] (j' : V →ₗ[F] T') :
    ∃! g : T →ₗ[E] T', (g.restrictScalars F).comp j = j' := by
  have h := (isEification_iff_isBaseChange j).mp hj
  exact ⟨h.lift j', h.lift_comp j', fun g hg => h.algHom_ext' _ _ (hg.trans (h.lift_comp j').symm)⟩

/-- **53.r6, uniqueness theorem for $E$-ifications** (O'Meara 1963, §53A, p. 130): if $j : V \to T$ and
$j_2 : V \to T_2$ are $E$-ifications of $V$, there is exactly one $E$-linear isomorphism $\varphi : T \to T_2$
with $\varphi(j x) = j_2 x$ for all $x \in V$. -/
@[kb "omeara1963" "§53A, p. 130 (uniqueness of E-ifications)"]
theorem exists_unique_linearEquiv (hj : IsEification (E := E) j) {T₂ : Type*} [AddCommGroup T₂]
    [Module E T₂] [Module F T₂] [IsScalarTower F E T₂] {j₂ : V →ₗ[F] T₂}
    (hj₂ : IsEification (E := E) j₂) :
    ∃! φ : T ≃ₗ[E] T₂, ∀ x, φ (j x) = j₂ x := by
  have h := (isEification_iff_isBaseChange j).mp hj
  have h₂ := (isEification_iff_isBaseChange j₂).mp hj₂
  have e1 : (h₂.lift j).comp (h.lift j₂) = LinearMap.id :=
    h.algHom_ext _ _ fun x => by simp [h.lift_eq, h₂.lift_eq]
  have e2 : (h.lift j₂).comp (h₂.lift j) = LinearMap.id :=
    h₂.algHom_ext _ _ fun x => by simp [h.lift_eq, h₂.lift_eq]
  refine ⟨LinearEquiv.ofLinearMap (h.lift j₂) (h₂.lift j) e2 e1, fun x => h.lift_eq j₂ x, ?_⟩
  intro φ hφ
  refine LinearEquiv.ext fun t => ?_
  have : φ.toLinearMap = h.lift j₂ := h.algHom_ext _ _ fun x => by simpa [h.lift_eq] using hφ x
  exact LinearMap.congr_fun this t

/-- **53.r7** (O'Meara 1963, §53A, p. 130): $\dim_E EV = \dim_F V$ for an $E$-ification $T$ of $V$. -/
@[kb "omeara1963" "§53A, p. 130 (dim_E EV = dim_F V)"]
theorem finrank_eification (hj : IsEification (E := E) j) : finrank E T = finrank F V := by
  have h := (isEification_iff_isBaseChange j).mp hj
  rw [← h.equiv.finrank_eq, Module.finrank_baseChange]

/-- **53.r7**, concrete form: $\dim_E (E \otimes_F V) = \dim_F V$. -/
@[kb "omeara1963" "§53A, p. 130 (dim_E EV = dim_F V, tensor model)"]
theorem finrank_tensor : finrank E (E ⊗[F] V) = finrank F V := Module.finrank_baseChange

/-! ### Subspaces -/

section Subspace

variable (U : Submodule F V)

/-- The map $U \to E \otimes_F V$, $u \mapsto 1 \otimes u$, with codomain the $E$-span of $U$ in $EV$. -/
def toSpan : U →ₗ[F] U.baseChange E :=
  LinearMap.codRestrict ((U.baseChange E).restrictScalars F)
    ((TensorProduct.mk F E V 1).comp U.subtype) fun u =>
      Submodule.tmul_mem_baseChange_of_mem 1 u.2

/-- **53.r8** (O'Meara 1963, §53A, p. 130): for a subspace $U \le V$, the $E$-span $E U$ of $U$ in $EV$
(Mathlib's `Submodule.baseChange E U`, which is by definition the range of $E \otimes U \to E \otimes V$) is an
$E$-ification of $U$ via $u \mapsto 1 \otimes u$: the natural map $E \otimes_F U \to E \otimes_F V$ is injective,
its range is $E U$, and `toSpan` is an $E$-ification. -/
@[kb "omeara1963" "§53A, p. 130 (the E-span of U in EV is an E-ification of U)"]
theorem isEification_baseChange_submodule :
    Function.Injective (U.subtype.baseChange E) ∧
      LinearMap.range (U.subtype.baseChange E) = U.baseChange E ∧
      IsEification (E := E) (T := U.baseChange E) (toSpan (E := E) U) := by
  have inj : Function.Injective (U.subtype.baseChange E) := by
    rw [LinearMap.baseChange_eq_lTensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := E) U.subtype U.injective_subtype
  refine ⟨inj, rfl, ?_⟩
  rw [isEification_iff_isBaseChange]
  have hb := TensorProduct.isBaseChange F U E
  let eN : E ⊗[F] U ≃ₗ[E] U.baseChange E := LinearEquiv.ofInjective _ inj
  have comm : (toSpan (E := E) U).comp (LinearEquiv.refl F U).toLinearMap =
      (eN.restrictScalars F).comp (TensorProduct.mk F E U 1) := by
    refine LinearMap.ext fun u => Subtype.ext ?_
    rfl
  exact (IsBaseChange.iff_of_equiv_comm (LinearEquiv.refl F U) eN comm).mp hb

end Subspace

/-- **53.r9** (O'Meara 1963, §53A, p. 130): if $V = U_0 \oplus \cdots \oplus U_{r-1}$ (internal direct sum),
then $EV = EU_0 \oplus \cdots \oplus EU_{r-1}$, where $EU_i$ is the $E$-span of $U_i$ in $EV$. -/
@[kb "omeara1963" "§53A, p. 130 (V = ⊕ U_i implies EV = ⊕ EU_i)"]
theorem isInternal_baseChange {ι : Type*} [DecidableEq ι] {U : ι → Submodule F V}
    (hU : DirectSum.IsInternal U) :
    DirectSum.IsInternal fun i => (U i).baseChange E :=
  hU.baseChange (S := E)

end Spaces

/-! ### Quadratic spaces (§53C, p. 131) -/

section Quadratic

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Invertible (2 : F)] [Invertible (2 : E)]
variable {V : Type*} [AddCommGroup V] [Module F V]

/-- Helper: the radical $\{x \in V : B(x, V) = 0\}$ of a quadratic space as the kernel of
$B = $ `QuadraticMap.associated Q` (as a map $V \to V^*$). The library's radical (O'Meara §42, used in
`Sec42Rad.lean`) is `splitComp (R := F) Q ⊤ ⊤`; the two agree (`rad_eq_splitComp`). -/
def rad (Q : QuadraticForm F V) : Submodule F V :=
  LinearMap.ker (QuadraticMap.associated (R := F) Q)

theorem mem_rad {Q : QuadraticForm F V} {x : V} :
    x ∈ rad Q ↔ ∀ y, QuadFormsKB.OMeara.bil Q x y = 0 := by
  simp only [rad, LinearMap.mem_ker, LinearMap.ext_iff, LinearMap.zero_apply]

/-- Flat base change commutes with kernels: $\ker(E \otimes f) = E \cdot \ker f$. -/
theorem ker_baseChange {W : Type*} [AddCommGroup W] [Module F W] (f : V →ₗ[F] W) :
    LinearMap.ker (f.baseChange E) = (LinearMap.ker f).baseChange E := by
  have hex : Function.Exact (LinearMap.ker f).subtype f := LinearMap.exact_subtype_ker_map f
  have h := Module.Flat.lTensor_exact E hex
  ext x
  rw [LinearMap.mem_ker, LinearMap.baseChange_eq_lTensor]
  exact h x

/-- **53.r16** (O'Meara 1963, §53C, p. 131): if $V = U_0 \perp \cdots \perp U_{r-1}$ (internal direct sum of
pairwise $B$-orthogonal subspaces), then $EV = EU_0 \perp \cdots \perp EU_{r-1}$: the $E$-spans $EU_i$ form an
internal direct sum and are pairwise orthogonal for the $E$-ified form $B_E$ =
`associated (Q.baseChange E)`. -/
@[kb "omeara1963" "§53C, p. 131 (V = ⊥ U_i implies EV = ⊥ EU_i)"]
theorem isInternal_orthogonal_baseChange {ι : Type*} [DecidableEq ι] (Q : QuadraticForm F V)
    {U : ι → Submodule F V} (hU : DirectSum.IsInternal U)
    (horth : ∀ i j, i ≠ j → ∀ x ∈ U i, ∀ y ∈ U j, QuadFormsKB.OMeara.bil Q x y = 0) :
    DirectSum.IsInternal (fun i => (U i).baseChange E) ∧
      ∀ i j, i ≠ j → ∀ x ∈ (U i).baseChange E, ∀ y ∈ (U j).baseChange E,
        QuadraticMap.associated (Q.baseChange E) x y = 0 := by
  refine ⟨isInternal_baseChange hU, ?_⟩
  intro i j hij x hx y hy
  rw [QuadraticForm.associated_baseChange]
  obtain ⟨s, rfl⟩ := hx
  obtain ⟨t, rfl⟩ := hy
  induction s using TensorProduct.inductionOn with
  | add s₁ s₂ h₁ h₂ => simp [h₁, h₂]
  | tmul a u =>
    induction t using TensorProduct.inductionOn with
    | add t₁ t₂ h₁ h₂ => simp only [map_add, h₁, h₂, add_zero]
    | tmul c w =>
      simp [LinearMap.BilinForm.baseChange_tmul, QuadFormsKB.OMeara.bil] at horth ⊢
      simp [horth i j hij u u.2 w w.2]

/-- Over a field a vector lies in the radical of a bilinear form iff it is orthogonal to a base. -/
theorem mem_ker_iff_basis {K W : Type*} [Field K] [AddCommGroup W] [Module K W] {ι : Type*}
    (B : LinearMap.BilinForm K W) (c : Basis ι K W) (x : W) :
    x ∈ LinearMap.ker B ↔ ∀ j, B x (c j) = 0 := by
  constructor
  · intro h j
    rw [LinearMap.mem_ker] at h
    simp [h]
  · intro h
    rw [LinearMap.mem_ker]
    exact c.ext fun j => by simpa using h j

/-- **53.r17** (O'Meara 1963, §53C, p. 131): $\operatorname{rad} EV = E \operatorname{rad} V$, i.e. the radical of
$Q_E$ = `Q.baseChange E` is the $E$-span of the radical of $Q$ in $E \otimes_F V$.  (Finite dimensionality of
$V$ is used to take a finite base.) -/
theorem rad_baseChange [FiniteDimensional F V] (Q : QuadraticForm F V) :
    rad (Q.baseChange E) = (rad Q).baseChange E := by
  classical
  let n := finrank F V
  let b : Basis (Fin n) F V := Module.finBasis F V
  let B : LinearMap.BilinForm F V := QuadraticMap.associated (R := F) Q
  let Φ : V →ₗ[F] (Fin n → F) := LinearMap.pi fun j => B.flip (b j)
  let Ψ : E ⊗[F] V →ₗ[E] (Fin n → E) :=
    (TensorProduct.piScalarRight F E E (Fin n)).toLinearMap ∘ₗ Φ.baseChange E
  have hΦ : LinearMap.ker Φ = rad Q := by
    ext x
    rw [LinearMap.mem_ker, rad, mem_ker_iff_basis B b, funext_iff]
    rfl
  have hΨ : ∀ x j, Ψ x j = QuadraticMap.associated (Q.baseChange E) x
      (Algebra.TensorProduct.basis E b j) := by
    intro x j
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp [hx, hy]
    | tmul a v =>
      simp [Ψ, Φ, B, QuadraticForm.associated_baseChange, LinearMap.BilinForm.baseChange_tmul,
        Algebra.TensorProduct.basis_apply, TensorProduct.piScalarRight_apply,
        TensorProduct.piScalarRightHom_tmul]
  ext x
  rw [← hΦ, ← ker_baseChange, LinearMap.mem_ker, rad,
    mem_ker_iff_basis _ (Algebra.TensorProduct.basis E b)]
  simp_rw [← hΨ]
  have h0 : Φ.baseChange E x = 0 ↔ Ψ x = 0 := by
    exact (LinearEquiv.map_eq_zero_iff (TensorProduct.piScalarRight F E E (Fin n))).symm
  rw [h0, funext_iff]
  simp


/-- The helper `rad Q` (kernel of $B$) is the library's radical `splitComp (R := F) Q ⊤ ⊤`. -/
theorem rad_eq_splitComp (Q : QuadraticForm F V) : rad Q = splitComp (R := F) Q ⊤ ⊤ := by
  ext x
  rw [mem_rad]
  exact ⟨fun h => ⟨Submodule.mem_top, fun z _ => h z⟩, fun h z => h.2 z Submodule.mem_top⟩

/-- **53.r17** (O'Meara 1963, §53C, p. 131): $\operatorname{rad} EV = E \operatorname{rad} V$: the radical of the
$E$-ification $Q_E$ = `Q.baseChange E` is the $E$-span (`Submodule.baseChange`) of the radical of $Q$, with the
library's radical `splitComp Q ⊤ ⊤` $= \{x : B(x, V) = 0\}$. -/
@[kb "omeara1963" "§53C, p. 131 (rad EV = E rad V)"]
theorem splitComp_baseChange [FiniteDimensional F V] (Q : QuadraticForm F V) :
    splitComp (R := E) (Q.baseChange E) ⊤ ⊤ = (splitComp (R := F) Q ⊤ ⊤).baseChange E := by
  rw [← rad_eq_splitComp, ← rad_eq_splitComp, rad_baseChange]

/-- **53.r18, matrices** (O'Meara 1963, §53C, p. 131): $V$ and $EV$ have the same matrix in any given base of
$V$: the matrix $(B_E(1 \otimes b_i, 1 \otimes b_j))$ of $Q_E$ = `Q.baseChange E` in the base $1 \otimes b$
(`Algebra.TensorProduct.basis E b`) is the image under $F \to E$ of the matrix of $Q$ in $b$. -/
@[kb "omeara1963" "§53C, p. 131 (V and EV have the same matrix in a base of V)"]
theorem gram_baseChange {ι : Type*} (Q : QuadraticForm F V) (b : Basis ι F V) :
    QuadFormsKB.OMeara.gram (Q.baseChange E) (Algebra.TensorProduct.basis E b) =
      (QuadFormsKB.OMeara.gram Q b).map (algebraMap F E) := by
  ext i j
  simp [QuadFormsKB.OMeara.gram, QuadFormsKB.OMeara.bil, QuadraticForm.associated_baseChange,
    LinearMap.BilinForm.baseChange_tmul, Algebra.TensorProduct.basis_apply, Algebra.smul_def]

/-- **53.r18, determinants**: the Gram determinant of $Q_E$ in the base $1 \otimes b$ is the image under
$F \to E$ of the Gram determinant of $Q$ in $b$. -/
@[kb "omeara1963" "§53C, p. 131 (discriminant of EV in the base b equals that of V)"]
theorem det_gram_baseChange {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : QuadraticForm F V)
    (b : Basis ι F V) :
    (QuadFormsKB.OMeara.gram (Q.baseChange E) (Algebra.TensorProduct.basis E b)).det =
      algebraMap F E (QuadFormsKB.OMeara.gram Q b).det := by
  rw [gram_baseChange, RingHom.map_det]
  rfl

/-- **53.r18, discriminants** (O'Meara 1963, §53C, p. 131): $dV = dV' \Rightarrow d(EV) = d(EV')$.  The
discriminant $dV$ is the class of $\det B(b_i, b_j)$ modulo squares of units, so $dV = dV'$ means
$\det_b = u^2 \det_{b'}$ for a unit $u \in F^\times$; then the same holds over $E$ with the unit $u$
(as an element of $E^\times$), for the bases $1 \otimes b$, $1 \otimes b'$ of $EV$, $EV'$. -/
@[kb "omeara1963" "§53C, p. 131 (dV = dV' implies d(EV) = d(EV'))"]
theorem disc_baseChange {n : ℕ} {V' : Type*} [AddCommGroup V'] [Module F V']
    (Q : QuadraticForm F V) (Q' : QuadraticForm F V') (b : Basis (Fin n) F V) (b' : Basis (Fin n) F V')
    (u : Fˣ)
    (h : (QuadFormsKB.OMeara.gram Q b).det = (u : F) ^ 2 * (QuadFormsKB.OMeara.gram Q' b').det) :
    (QuadFormsKB.OMeara.gram (Q.baseChange E) (Algebra.TensorProduct.basis E b)).det =
      ((Units.map (algebraMap F E : F →* E) u : Eˣ) : E) ^ 2 *
        (QuadFormsKB.OMeara.gram (Q'.baseChange E) (Algebra.TensorProduct.basis E b')).det := by
  rw [det_gram_baseChange, det_gram_baseChange, h]
  simp

end Quadratic

end QuadFormsKB.OMeara.Ext53
