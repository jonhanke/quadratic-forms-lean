import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Tamagawa.Measure.FibreSO
import QuadFormsKB.Tamagawa.Measure.ConeReal

/-!
# The parabolic subgroup fixing an isotropic vector at a finite place

This file is the group-theoretic and algebraic layer of the cone case of Weil's $\tau(SO(V)) = 2$ at a **finite place**
$v$ of a number field $F$; it mirrors `ConeReal.lean` and `ConeRealOrbit.lean`, which do the same at the real places.

**Setting.** $c_0 \in \mathcal O_F \setminus \{0\}$, $Q_0'$ a nondegenerate form over $\mathcal O_F$ in $k$ variables,
$$Q_{m,0} = \langle -c_0\rangle \perp Q_0'\quad(k+1\text{ variables}),\qquad
  Q_0 = \langle c_0\rangle \perp Q_{m,0} = \langle c_0\rangle\perp\langle -c_0\rangle\perp Q_0'\quad(k+2\text{ variables}).$$
Over the completion $F_v$ write $c$ for the image of $c_0$ and $Q'_v$ for $Q_0'\otimes F_v$. The group $SO(V)(F_v)$ is
`SOv v Q₀`; its elements are matrices in $\mathrm{GL}_{k+2}(F_v)$ preserving the Hessian of $Q_0\otimes F$.
Indices are 0-based: the variables of $Q_0$ are $x_0, x_1, x_2, \dots, x_{k+1}$ and $x_0, x_1$ carry the hyperbolic plane.

**Contents.**
* (`det_dM_eq_one`) the torus matrix $d(a)$ has determinant $1$ over **every** field of characteristic $0$, with no
  hypothesis that $a$ or $-a$ be a square (the field-generic `ConeAlgebra.det_dM` needs one, false in general over $F_v$);
* (`hessV_cone`) the bridge: the Hessian of $Q_0\otimes F$ over $F_v$ is the Hessian of `ConeAlgebra.coneForm c Q'_v`,
  so that all of `ConeAlgebra` applies to $K = F_v$;
* the elements `dG` ($d(a)$), `nG` ($n(w)$, Eichler transformation), the Levi map `mG` ($h \mapsto \mathrm{diag}(1,1,h)$)
  and the corner embedding `iotaSO` ($h \mapsto \mathrm{diag}(1,h)$, for every split form), with their matrices and group
  laws; continuity and measurability;
* (`isMulRightInvariant_muLocSO`, `lintegral_inv_muLocSO`) **unimodularity** of $SO(V)(F_v)$ for the local measure
  `muLocSO`: it is also right invariant, hence inversion invariant;
* (`stabE`, `pElem`, `exists_pElem`, `measurableEmbedding_pElem`) the stabilizer of $e = e_0 + e_1$ in $SO(V)(F_v)$ is
  $N \rtimes SO(V')$, parametrized by $(w, h) \mapsto n(w)\,\mathrm{diag}(1,1,h)$ as a measurable embedding;
* (`lintegral_orbital_section`) the sphere identity (`FibreSO.lintegral_orbital_finitePlace`) for **an arbitrary**
  measurable section $s$ of $g \mapsto g e_0$ in place of the reflection section.

Source: Weil 1982, §2.4 (Lemma 2.4.1, Theorem 2.4.3) and §4.5; unverified page numbers.
-/

open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped ENNReal NNReal Pointwise
open QuadFormsKB QuadFormsKB.Tamagawa QuadFormsKB.Lattices QuadForm QuadFormsKB.LocalDensity
open QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.ConeAlgebra
open QuadFormsKB.Tamagawa.Measure.FibreDecomp QuadFormsKB.Tamagawa.Measure.FibreConst

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.ConeFinite

/-! ### The torus matrix has determinant one (any field of characteristic $0$) -/

section Det

variable {K : Type*} [Field K] [CharZero K] {k : ℕ}

/-- $d(a) = 1 + U V$ with $U, V$ of rank $2$: $d(a)x = x + \tfrac{a-1}{2}(e\cdot x)\,e + \tfrac{a^{-1}-1}{2}(f\cdot x)\,f$,
$e = e_0 + e_1$, $f = e_0 - e_1$. -/
theorem dM_eq_one_add (a : K) :
    dM (k := k) a = 1 + (Matrix.of fun (i : Fin (k + 1 + 1)) (j : Fin 2) =>
      ![(a - 1) / 2 * (eV : Fin (k + 1 + 1) → K) i, (a⁻¹ - 1) / 2 * (fV : Fin (k + 1 + 1) → K) i] j) *
      (Matrix.of fun (j : Fin 2) (i : Fin (k + 1 + 1)) =>
        ![(eV : Fin (k + 1 + 1) → K) i, (fV : Fin (k + 1 + 1) → K) i] j) := by
  refine mat_ext fun x => ?_
  rw [← v3_eta x, dM_mulVec_v3, add_mulVec, one_mulVec, ← mulVec_mulVec]
  have h1 : (Matrix.of fun (j : Fin 2) (i : Fin (k + 1 + 1)) =>
      ![(eV : Fin (k + 1 + 1) → K) i, (fV : Fin (k + 1 + 1) → K) i] j) *ᵥ v3 (x 0) (x 1) (tl x) =
      ![x 0 + x 1, x 0 - x 1] := by
    ext j
    fin_cases j
    · simp [mulVec, dotProduct, eV, v3, Fin.sum_univ_succ]
    · simp [mulVec, dotProduct, fV, v3, Fin.sum_univ_succ]
      ring
  rw [h1]
  ext i
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
  · simp [eV, fV, v3]
    ring
  · simp [eV, fV, v3]
    ring
  · simp [eV, fV, v3]

/-- **$\det d(a) = 1$ for every $a \ne 0$** over any field of characteristic $0$ (no square hypothesis). By the matrix
determinant lemma $\det(1 + UV) = \det(1 + VU)$, with $VU = \mathrm{diag}(a - 1, a^{-1} - 1)$ a $2 \times 2$ matrix. -/
@[kb "weil1982" "§2.4 (the torus of the parabolic subgroup has determinant one) [unverified]"]
theorem det_dM_eq_one {a : K} (ha : a ≠ 0) : (dM (k := k) a).det = 1 := by
  rw [dM_eq_one_add a, det_one_add_mul_comm]
  have : (1 : Matrix (Fin 2) (Fin 2) K) + (Matrix.of fun (j : Fin 2) (i : Fin (k + 1 + 1)) =>
      ![(eV : Fin (k + 1 + 1) → K) i, (fV : Fin (k + 1 + 1) → K) i] j) *
      (Matrix.of fun (i : Fin (k + 1 + 1)) (j : Fin 2) =>
        ![(a - 1) / 2 * (eV : Fin (k + 1 + 1) → K) i, (a⁻¹ - 1) / 2 * (fV : Fin (k + 1 + 1) → K) i] j) =
      !![a, 0; 0, a⁻¹] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, eV, fV, v3]
  rw [this, det_fin_two_of]
  simp [ha]

end Det

/-! ### Continuity of the explicit matrices over a topological field -/

section Continuity

variable {K : Type*} [Field K] [CharZero K] [TopologicalSpace K] [IsTopologicalDivisionRing K] {k : ℕ}

/-- A matrix-valued map is continuous if all its actions on vectors are. -/
theorem continuous_of_mulVec {n : ℕ} {X : Type*} [TopologicalSpace X] {M : X → Matrix (Fin n) (Fin n) K}
    (h : ∀ w, Continuous fun t => M t *ᵥ w) : Continuous M := by
  refine continuous_matrix fun i j => ?_
  have := (continuous_apply i).comp (h (Pi.single j 1))
  convert this using 1
  funext t
  simp

/-- Continuity of $(a, b, y) \mapsto$ `v3 a b y`. -/
theorem continuous_v3 {X : Type*} [TopologicalSpace X] {a b : X → K} {y : X → Fin k → K} (ha : Continuous a)
    (hb : Continuous b) (hy : Continuous y) : Continuous fun t => v3 (a t) (b t) (y t) :=
  ha.finCons (hb.finCons hy)

/-- The last $k$ coordinates $x \mapsto x'$ are continuous. -/
theorem continuous_tl : Continuous (tl : (Fin (k + 1 + 1) → K) → Fin k → K) :=
  continuous_pi fun _ => continuous_apply _

/-- The values $Q'(w)$ of a quadratic form are continuous in $w$ ($2Q'(w) = w^{\mathsf T}H'w$). -/
theorem continuous_eval_gen (Q' : QuadForm K k) : Continuous fun w : Fin k → K => Q'.eval w := by
  have h : ∀ w : Fin k → K, Q'.eval w = (w ⬝ᵥ (Q'.hessian *ᵥ w)) / 2 := fun w => by
    rw [dotProduct_hessian_self]; ring
  simp_rw [h]
  exact (continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)).div_const _

/-- **$w \mapsto n(w)$ is continuous.** -/
theorem continuous_nM (c : K) (Q' : QuadForm K k) : Continuous fun w : Fin k → K => nM c Q' w := by
  refine continuous_of_mulVec fun v => ?_
  have e : (fun w : Fin k → K => nM c Q' w *ᵥ v) = fun w => nM c Q' w *ᵥ v3 (v 0) (v 1) (tl v) := by
    rw [v3_eta]
  rw [e]
  simp only [nM_mulVec_v3]
  have hq := continuous_eval_gen Q'
  have hd : Continuous fun w : Fin k → K => (Q'.hessian *ᵥ w) ⬝ᵥ tl v :=
    (continuous_const.matrix_mulVec continuous_id).dotProduct continuous_const
  refine continuous_v3 ?_ ?_ ?_
  · exact continuous_const.sub ((hd.add (continuous_const.mul hq)).div_const _)
  · exact continuous_const.sub ((hd.add (continuous_const.mul hq)).div_const _)
  · exact continuous_const.add (continuous_const_smul _)

/-- **$a \mapsto d(a)$ is continuous on $\{a \ne 0\}$.** -/
theorem continuous_dM : Continuous fun a : {a : K // a ≠ 0} => dM (k := k) a.1 := by
  refine continuous_of_mulVec fun v => ?_
  have e : (fun a : {a : K // a ≠ 0} => dM (k := k) a.1 *ᵥ v) =
      fun a => dM (k := k) a.1 *ᵥ v3 (v 0) (v 1) (tl v) := by
    rw [v3_eta]
  rw [e]
  simp only [dM_mulVec_v3]
  have h1 : Continuous fun a : {a : K // a ≠ 0} => a.1 := continuous_subtype_val
  have h2 : Continuous fun a : {a : K // a ≠ 0} => a.1⁻¹ := continuous_subtype_val.inv₀ fun a => a.2
  have h3 : Continuous fun a : {a : K // a ≠ 0} => (a.1 - 1) / 2 * (v 0 + v 1) :=
    ((h1.sub continuous_const).div_const _).mul continuous_const
  have h4 : Continuous fun a : {a : K // a ≠ 0} => (a.1⁻¹ - 1) / 2 * (v 0 - v 1) :=
    ((h2.sub continuous_const).div_const _).mul continuous_const
  refine continuous_v3 ?_ ?_ continuous_const
  · exact (continuous_const.add h3).add h4
  · exact (continuous_const.add h3).sub h4

end Continuity

/-! ### Matrices of elements of $SO(V)(F_v)$ -/

section Gen

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {N : ℕ} (Q₀ : QuadForm (𝓞 F) N)

/-- **The matrix of an element of $SO(V)(F_v)$** in $\mathrm{GL}_N(F_v)$ (its underlying $N \times N$ matrix over $F_v$). -/
def mat (g : SOv v Q₀) : Matrix (Fin N) (Fin N) (v.adicCompletion F) :=
  ((g.1 : orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)) : GL (Fin N) (v.adicCompletion F)).val

@[simp] theorem mat_mul (g h : SOv v Q₀) : mat v Q₀ (g * h) = mat v Q₀ g * mat v Q₀ h := rfl

@[simp] theorem mat_one : mat v Q₀ (1 : SOv v Q₀) = 1 := rfl

/-- Elements of $SO(V)(F_v)$ have determinant $1$. -/
theorem det_mat (g : SOv v Q₀) : (mat v Q₀ g).det = 1 := g.2

/-- Elements of $SO(V)(F_v)$ preserve the Hessian of $Q_0 \otimes F$ over $F_v$. -/
theorem isometry_mat (g : SOv v Q₀) :
    (mat v Q₀ g)ᵀ * FibreO.hessV v (Q₀.map (algebraMap (𝓞 F) F)) * mat v Q₀ g =
      FibreO.hessV v (Q₀.map (algebraMap (𝓞 F) F)) := g.1.2

/-- An element of $SO(V)(F_v)$ is determined by its matrix. -/
theorem mat_injective : Function.Injective (mat v Q₀) :=
  fun _ _ e => Subtype.ext (Subtype.ext (Units.ext e))

/-- **The element of $SO(V)(F_v)$ with a given matrix**: $A^{\mathsf T}HA = H$ and $\det A = 1$. -/
def mkSO (A : Matrix (Fin N) (Fin N) (v.adicCompletion F))
    (hA : Aᵀ * FibreO.hessV v (Q₀.map (algebraMap (𝓞 F) F)) * A = FibreO.hessV v (Q₀.map (algebraMap (𝓞 F) F)))
    (hd : A.det = 1) : SOv v Q₀ :=
  ⟨⟨Matrix.nonsingInvUnit A (by rw [hd]; exact isUnit_one), hA⟩, hd⟩

@[simp] theorem mat_mkSO (A : Matrix (Fin N) (Fin N) (v.adicCompletion F))
    (hA : Aᵀ * FibreO.hessV v (Q₀.map (algebraMap (𝓞 F) F)) * A = FibreO.hessV v (Q₀.map (algebraMap (𝓞 F) F)))
    (hd : A.det = 1) : mat v Q₀ (mkSO v Q₀ A hA hd) = A := rfl

variable {Q₀}

/-- The matrix of the inverse (nondegenerate $Q_0$): $g^{-1} = H^{-1}g^{\mathsf T}H$. -/
theorem mat_inv (hQ : Q₀.Nondegenerate) (g : SOv v Q₀) :
    mat v Q₀ g⁻¹ = (FibreO.hessV v (Q₀.map (algebraMap (𝓞 F) F)))⁻¹ * (mat v Q₀ g)ᵀ *
      FibreO.hessV v (Q₀.map (algebraMap (𝓞 F) F)) :=
  FibreO.inv_val_eq v (Q₀.map (algebraMap (𝓞 F) F)) (nondegenerate_QF Q₀ hQ) g.1

/-- $g \mapsto$ its matrix is continuous. -/
theorem continuous_mat : Continuous (mat v Q₀) :=
  (Units.continuous_val.comp continuous_subtype_val).comp continuous_subtype_val

/-- **A map into $SO(V)(F_v)$ is continuous if its matrix is** (nondegenerate $Q_0$; the inverse matrix is
$H^{-1}g^{\mathsf T}H$). -/
theorem continuous_of_mat (hQ : Q₀.Nondegenerate) {α : Type*} [TopologicalSpace α] {f : α → SOv v Q₀}
    (h : Continuous fun a => mat v Q₀ (f a)) : Continuous f := by
  have h2 : Continuous fun a => mat v Q₀ (f a)⁻¹ := by
    simp_rw [mat_inv v hQ]
    exact (continuous_const.matrix_mul h.matrix_transpose).matrix_mul continuous_const
  have h3 : Continuous fun a => (f a).1 := by
    refine (FibreO.isEmbedding_orthPair v (Q₀.map (algebraMap (𝓞 F) F))).isInducing.continuous_iff.2 ?_
    exact h.prodMk h2
  exact h3.subtype_mk _

/-- **A map into $SO(V)(F_v)$ is measurable if its matrix is** (nondegenerate $Q_0$). -/
theorem measurable_of_mat (hQ : Q₀.Nondegenerate) {α : Type*} [MeasurableSpace α] {f : α → SOv v Q₀}
    (h : Measurable fun a => mat v Q₀ (f a)) : Measurable f :=
  ((measurableEmbedding_soSub v Q₀ hQ).measurable_comp_iff).1
    (FibreO.measurable_of_val v (Q₀.map (algebraMap (𝓞 F) F)) (nondegenerate_QF Q₀ hQ)
      (f := fun a => (f a).1) h)

end Gen

/-! ### The corner embedding $h \mapsto \mathrm{diag}(1, h)$ on $SO$ -/

section Corner

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

/-- **The corner embedding** $SO(Q_0')(F_v) \to SO(\langle m_0\rangle\perp Q_0')(F_v)$, $h \mapsto \mathrm{diag}(1, h)$:
the restriction of `FibreO.iota` (used by the coordinates `orb(x, h) = s(x)·diag(1, h)`) to $SO$. -/
def iotaSO (m₀ : 𝓞 F) (Q₀' : QuadForm (𝓞 F) n) : SOv v Q₀' →* SOv v (splitForm m₀ Q₀') where
  toFun h := ⟨FibreO.iota v (QQ m₀ Q₀') (mm m₀) (QQ' Q₀') (hEE m₀ Q₀') h.1, by
    rw [mem_soSub, FibreO.iota_val, det_cornerMat, one_mul]; exact h.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

/-- The matrix of $\iota(h)$ is $\mathrm{diag}(1, h)$. -/
@[simp] theorem mat_iotaSO (m₀ : 𝓞 F) (Q₀' : QuadForm (𝓞 F) n) (h : SOv v Q₀') :
    mat v (splitForm m₀ Q₀') (iotaSO v m₀ Q₀' h) = cornerMat 1 (mat v Q₀' h) := rfl

/-- `iotaSO` is compatible with `FibreO.iota`. -/
theorem iotaSO_val (m₀ : 𝓞 F) (Q₀' : QuadForm (𝓞 F) n) (h : SOv v Q₀') :
    (iotaSO v m₀ Q₀' h).1 = FibreO.iota v (QQ m₀ Q₀') (mm m₀) (QQ' Q₀') (hEE m₀ Q₀') h.1 := rfl

/-- `iotaSO` is injective. -/
theorem iotaSO_injective (m₀ : 𝓞 F) (Q₀' : QuadForm (𝓞 F) n) : Function.Injective (iotaSO v m₀ Q₀') := by
  intro a b hab
  have := congrArg (mat v (splitForm m₀ Q₀')) hab
  rw [mat_iotaSO, mat_iotaSO] at this
  exact mat_injective v Q₀' (cornerMat_injective_right this)

/-- **`iotaSO` is continuous.** -/
theorem continuous_iotaSO (m₀ : 𝓞 F) (Q₀' : QuadForm (𝓞 F) n) : Continuous (iotaSO v m₀ Q₀') := by
  refine Topology.IsInducing.subtypeVal.continuous_iff.2 ?_
  exact (FibreO.isEmbedding_iota v (QQ m₀ Q₀') (mm m₀) (QQ' Q₀') (hEE m₀ Q₀')).continuous.comp
    continuous_subtype_val

/-- **`iotaSO` is a topological embedding.** -/
theorem isEmbedding_iotaSO (m₀ : 𝓞 F) (Q₀' : QuadForm (𝓞 F) n) : Topology.IsEmbedding (iotaSO v m₀ Q₀') := by
  refine Topology.IsEmbedding.of_comp (continuous_iotaSO v m₀ Q₀') continuous_subtype_val ?_
  exact (FibreO.isEmbedding_iota v (QQ m₀ Q₀') (mm m₀) (QQ' Q₀') (hEE m₀ Q₀')).comp
    Topology.IsEmbedding.subtypeVal

end Corner

/-! ### The cone form over $F_v$ and the bridge -/

section Cone

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {k : ℕ}
  (c₀ : 𝓞 F) (Q₀' : QuadForm (𝓞 F) k)

/-- The middle form $Q_{m,0} = \langle -c_0\rangle \perp Q_0'$ over $\mathcal O_F$ ($k+1$ variables). -/
abbrev Qmid : QuadForm (𝓞 F) (k + 1) := splitForm (-c₀) Q₀'

/-- The cone form $Q_0 = \langle c_0\rangle \perp \langle -c_0\rangle \perp Q_0'$ over $\mathcal O_F$ ($k+2$ variables). -/
abbrev Qcone : QuadForm (𝓞 F) (k + 1 + 1) := splitForm c₀ (splitForm (-c₀) Q₀')

/-- The image $c$ of $c_0$ in $F_v$. -/
abbrev cv : v.adicCompletion F := algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F c₀)

/-- The form $Q_0'$ over $F_v$ (via $\mathcal O_F \to F \to F_v$). -/
abbrev QFv : QuadForm (v.adicCompletion F) k :=
  (Q₀'.map (algebraMap (𝓞 F) F)).map (algebraMap F (v.adicCompletion F))

/-- The cone form is nondegenerate. -/
theorem nondeg_cone (hc : c₀ ≠ 0) (hQ' : Q₀'.Nondegenerate) : (Qcone c₀ Q₀').Nondegenerate :=
  hQ0 c₀ (splitForm (-c₀) Q₀') hc (hQ0 (-c₀) Q₀' (neg_ne_zero.2 hc) hQ')

/-- The image of $c_0 \ne 0$ in $F_v$ is nonzero. -/
theorem cv_ne (hc : c₀ ≠ 0) : cv v c₀ ≠ 0 :=
  (map_ne_zero (algebraMap F (v.adicCompletion F))).2 (mm_ne c₀ hc)

/-- **The bridge.** The Hessian over $F_v$ of the cone form $Q_0 \otimes F$ is the Hessian of `coneForm c Q'_v`
(Hessians commute with base change and `splitForm` with `map`). Hence all of `ConeAlgebra` (with $K = F_v$) computes in
$SO(V)(F_v)$. -/
theorem hessV_cone :
    FibreO.hessV v ((Qcone c₀ Q₀').map (algebraMap (𝓞 F) F)) =
      (coneForm (cv v c₀) (QFv v Q₀')).hessian := by
  unfold FibreO.hessV
  rw [← QuadForm.hessian_map]
  congr 1
  simp only [Qcone, map_splitForm, map_neg, cv, QFv, coneForm]

/-- The Hessian over $F_v$ of $Q_0' \otimes F$ is the Hessian of $Q'_v$. -/
theorem hessV_base :
    FibreO.hessV v (Q₀'.map (algebraMap (𝓞 F) F)) = (QFv v Q₀').hessian :=
  (QuadForm.hessian_map _ _).symm

/-- The Hessian of the cone form over $F_v$ is invertible. -/
theorem det_hess_cone_ne (hc : c₀ ≠ 0) (hQ' : Q₀'.Nondegenerate) :
    (coneForm (cv v c₀) (QFv v Q₀')).hessian.det ≠ 0 := by
  rw [← hessV_cone]
  exact FibreO.det_hessV_ne_zero v _ (nondegenerate_QF _ (nondeg_cone c₀ Q₀' hc hQ'))

/-- Elements of $SO(Q_0')(F_v)$ are isometries of $Q'_v$. -/
theorem isometry_base (h : SOv v Q₀') :
    (mat v Q₀' h)ᵀ * (QFv v Q₀').hessian * mat v Q₀' h = (QFv v Q₀').hessian := by
  have := isometry_mat v Q₀' h
  rwa [hessV_base] at this

/-- **The element of $SO(V)(F_v)$ with a given matrix**, for an isometry of the cone form of determinant $1$. -/
def mkCone (A : Matrix (Fin (k + 1 + 1)) (Fin (k + 1 + 1)) (v.adicCompletion F))
    (hA : Aᵀ * (coneForm (cv v c₀) (QFv v Q₀')).hessian * A = (coneForm (cv v c₀) (QFv v Q₀')).hessian)
    (hd : A.det = 1) : SOv v (Qcone c₀ Q₀') :=
  mkSO v (Qcone c₀ Q₀') A (by rw [hessV_cone]; exact hA) hd

@[simp] theorem mat_mkCone (A : Matrix (Fin (k + 1 + 1)) (Fin (k + 1 + 1)) (v.adicCompletion F))
    (hA : Aᵀ * (coneForm (cv v c₀) (QFv v Q₀')).hessian * A = (coneForm (cv v c₀) (QFv v Q₀')).hessian)
    (hd : A.det = 1) : mat v (Qcone c₀ Q₀') (mkCone v c₀ Q₀' A hA hd) = A := rfl

/-! ### The elements $d(a)$, $n(w)$, $\mathrm{diag}(1,1,h)$ of $SO(V)(F_v)$ -/

/-- **The torus element** $d(a) \in SO(V)(F_v)$, $a \in F_v^\times$ ($p \mapsto ap$, $q \mapsto a^{-1}q$; $d(a)e = ae$). -/
def dG {a : v.adicCompletion F} (ha : a ≠ 0) : SOv v (Qcone c₀ Q₀') :=
  mkCone v c₀ Q₀' (dM a) (isometry_dM _ _ ha) (det_dM_eq_one ha)

@[simp] theorem mat_dG {a : v.adicCompletion F} (ha : a ≠ 0) :
    mat v (Qcone c₀ Q₀') (dG v c₀ Q₀' ha) = dM a := rfl

/-- **The Eichler transformation** $n(w) \in SO(V)(F_v)$, $w \in F_v^k$ (unipotent radical of the stabilizer of $e$). -/
def nG (hc : c₀ ≠ 0) (hQ' : Q₀'.Nondegenerate) (w : Fin k → v.adicCompletion F) : SOv v (Qcone c₀ Q₀') :=
  mkCone v c₀ Q₀' (nM (cv v c₀) (QFv v Q₀') w) (isometry_nM _ _ (cv_ne v c₀ hc) w)
    (det_nM _ _ (cv_ne v c₀ hc) (det_hess_cone_ne v c₀ Q₀' hc hQ') w)

@[simp] theorem mat_nG (hc : c₀ ≠ 0) (hQ' : Q₀'.Nondegenerate) (w : Fin k → v.adicCompletion F) :
    mat v (Qcone c₀ Q₀') (nG v c₀ Q₀' hc hQ' w) = nM (cv v c₀) (QFv v Q₀') w := rfl

/-- **The Levi factor** $SO(Q_0')(F_v) \to SO(Q_0)(F_v)$, $h \mapsto \mathrm{diag}(1, 1, h)$: the composite of the two
corner embeddings $SO(Q_0') \to SO(Q_{m,0}) \to SO(Q_0)$. -/
def mG : SOv v Q₀' →* SOv v (Qcone c₀ Q₀') :=
  (iotaSO v c₀ (Qmid c₀ Q₀')).comp (iotaSO v (-c₀) Q₀')

@[simp] theorem mat_mG (h : SOv v Q₀') :
    mat v (Qcone c₀ Q₀') (mG v c₀ Q₀' h) = mM (mat v Q₀' h) := rfl

/-- `mG` is the composite of the two corner embeddings. -/
theorem mG_eq (h : SOv v Q₀') :
    mG v c₀ Q₀' h = iotaSO v c₀ (Qmid c₀ Q₀') (iotaSO v (-c₀) Q₀' h) := rfl

/-- `mG` is injective. -/
theorem mG_injective : Function.Injective (mG v c₀ Q₀') :=
  (iotaSO_injective v c₀ (Qmid c₀ Q₀')).comp (iotaSO_injective v (-c₀) Q₀')

/-! ### Group laws -/

/-- $d(a)\,d(b) = d(ab)$. -/
theorem dG_mul {a b : v.adicCompletion F} (ha : a ≠ 0) (hb : b ≠ 0) :
    dG v c₀ Q₀' ha * dG v c₀ Q₀' hb = dG v c₀ Q₀' (mul_ne_zero ha hb) :=
  mat_injective v _ (by rw [mat_mul, mat_dG, mat_dG, mat_dG, dM_mul _ _ ha hb])

/-- $d(1) = 1$. -/
theorem dG_one : dG v c₀ Q₀' (one_ne_zero : (1 : v.adicCompletion F) ≠ 0) = 1 :=
  mat_injective v _ (by rw [mat_dG, mat_one, dM_one])

/-- $d(a)^{-1} = d(a^{-1})$. -/
theorem dG_inv {a : v.adicCompletion F} (ha : a ≠ 0) :
    (dG v c₀ Q₀' ha)⁻¹ = dG v c₀ Q₀' (inv_ne_zero ha) := by
  rw [inv_eq_iff_mul_eq_one, dG_mul]
  exact mat_injective v _ (by rw [mat_dG, mul_inv_cancel₀ ha, dM_one, mat_one])

/-- $\mathrm{diag}(1,1,h)$ commutes with $d(a)$. -/
theorem mG_mul_dG (h : SOv v Q₀') {a : v.adicCompletion F} (ha : a ≠ 0) :
    mG v c₀ Q₀' h * dG v c₀ Q₀' ha = dG v c₀ Q₀' ha * mG v c₀ Q₀' h :=
  mat_injective v _ (by rw [mat_mul, mat_mul, mat_dG, mat_mG, mM_mul_dM])

section NG

variable (hc : c₀ ≠ 0) (hQ' : Q₀'.Nondegenerate)
include hc hQ'

/-- $n(w)\,n(w') = n(w + w')$. -/
theorem nG_add (w w' : Fin k → v.adicCompletion F) :
    nG v c₀ Q₀' hc hQ' w * nG v c₀ Q₀' hc hQ' w' = nG v c₀ Q₀' hc hQ' (w + w') :=
  mat_injective v _ (by rw [mat_mul, mat_nG, mat_nG, mat_nG, nM_mul _ _ (cv_ne v c₀ hc)])

/-- $n(0) = 1$. -/
theorem nG_zero : nG v c₀ Q₀' hc hQ' (0 : Fin k → v.adicCompletion F) = 1 :=
  mat_injective v _ (by rw [mat_nG, nM_zero, mat_one])

/-- $n(w)^{-1} = n(-w)$. -/
theorem nG_neg (w : Fin k → v.adicCompletion F) :
    (nG v c₀ Q₀' hc hQ' w)⁻¹ = nG v c₀ Q₀' hc hQ' (-w) := by
  rw [inv_eq_iff_mul_eq_one, nG_add, add_neg_cancel, nG_zero]

/-- **Conjugation by the torus**: $d(a)\,n(w) = n(aw)\,d(a)$. -/
theorem dG_mul_nG {a : v.adicCompletion F} (ha : a ≠ 0) (w : Fin k → v.adicCompletion F) :
    dG v c₀ Q₀' ha * nG v c₀ Q₀' hc hQ' w = nG v c₀ Q₀' hc hQ' (a • w) * dG v c₀ Q₀' ha :=
  mat_injective v _ (by
    rw [mat_mul, mat_mul, mat_dG, mat_nG, mat_nG, dM_mul_nM _ _ (cv_ne v c₀ hc) ha])

/-- **The Levi factor normalizes $N$**: $\mathrm{diag}(1,1,h)\,n(w) = n(hw)\,\mathrm{diag}(1,1,h)$. -/
theorem mG_mul_nG (h : SOv v Q₀') (w : Fin k → v.adicCompletion F) :
    mG v c₀ Q₀' h * nG v c₀ Q₀' hc hQ' w = nG v c₀ Q₀' hc hQ' (mat v Q₀' h *ᵥ w) * mG v c₀ Q₀' h :=
  mat_injective v _ (by
    rw [mat_mul, mat_mul, mat_nG, mat_nG, mat_mG, mM_mul_nM _ _ (isometry_base v Q₀' h)])

/-- $w \mapsto n(w)$ is continuous. -/
theorem continuous_nG : Continuous (nG v c₀ Q₀' hc hQ') :=
  continuous_of_mat v (nondeg_cone c₀ Q₀' hc hQ') (continuous_nM (cv v c₀) (QFv v Q₀'))

end NG

/-- $a \mapsto d(a)$ is continuous on $\{a \ne 0\}$. -/
theorem continuous_dG (hc : c₀ ≠ 0) (hQ' : Q₀'.Nondegenerate) :
    Continuous fun a : {a : v.adicCompletion F // a ≠ 0} => dG v c₀ Q₀' a.2 :=
  continuous_of_mat v (nondeg_cone c₀ Q₀' hc hQ') (continuous_dM (k := k))

/-- **The Levi map `mG` is continuous.** -/
theorem continuous_mG : Continuous (mG v c₀ Q₀') :=
  (continuous_iotaSO v c₀ (Qmid c₀ Q₀')).comp (continuous_iotaSO v (-c₀) Q₀')

/-- **`mG` is a topological embedding.** -/
theorem isEmbedding_mG : Topology.IsEmbedding (mG v c₀ Q₀') :=
  (isEmbedding_iotaSO v c₀ (Qmid c₀ Q₀')).comp (isEmbedding_iotaSO v (-c₀) Q₀')

open scoped Classical in
/-- $d(a)$ for $a \ne 0$ and $1$ at the (null) point $a = 0$: a total function for integration. -/
def dGt (a : v.adicCompletion F) : SOv v (Qcone c₀ Q₀') :=
  if h : a = 0 then 1 else dG v c₀ Q₀' h

theorem dGt_of_ne {a : v.adicCompletion F} (h : a ≠ 0) : dGt v c₀ Q₀' a = dG v c₀ Q₀' h := by
  simp [dGt, h]

theorem dGt_zero : dGt v c₀ Q₀' (0 : v.adicCompletion F) = 1 := by
  simp [dGt]

/-- **`dGt` is measurable** (continuous off the point $0$). -/
theorem measurable_dGt (hc : c₀ ≠ 0) (hQ' : Q₀'.Nondegenerate) : Measurable (dGt v c₀ Q₀') := by
  refine measurable_of_continuousOn_compl_singleton 0 ?_
  rw [continuousOn_iff_continuous_domRestrict]
  have e : ({0}ᶜ : Set (v.adicCompletion F)).domRestrict (dGt v c₀ Q₀') =
      fun a : ({0}ᶜ : Set (v.adicCompletion F)) => dG v c₀ Q₀' a.2 := by
    funext a; exact dGt_of_ne v c₀ Q₀' a.2
  rw [e]
  exact (continuous_dG v c₀ Q₀' hc hQ').comp (continuous_subtype_val.subtype_mk fun a => a.2)

theorem mG_mul_dGt (h : SOv v Q₀') (a : v.adicCompletion F) :
    mG v c₀ Q₀' h * dGt v c₀ Q₀' a = dGt v c₀ Q₀' a * mG v c₀ Q₀' h := by
  by_cases ha : a = 0
  · subst ha; simp [dGt_zero]
  · rw [dGt_of_ne v c₀ Q₀' ha, mG_mul_dG]

/-! ### The stabilizer of $e$ -/

/-- **The stabilizer of the isotropic vector $e = e_0 + e_1$** in $SO(V)(F_v)$ (the parabolic subgroup
$P = N \rtimes SO(V')$). -/
def stabE : Subgroup (SOv v (Qcone c₀ Q₀')) where
  carrier := {g | mat v (Qcone c₀ Q₀') g *ᵥ (eV : Fin (k + 1 + 1) → v.adicCompletion F) = eV}
  mul_mem' {a b} ha hb := by
    have ha' : mat v (Qcone c₀ Q₀') a *ᵥ (eV : Fin (k + 1 + 1) → v.adicCompletion F) = eV := ha
    have hb' : mat v (Qcone c₀ Q₀') b *ᵥ (eV : Fin (k + 1 + 1) → v.adicCompletion F) = eV := hb
    show mat v (Qcone c₀ Q₀') (a * b) *ᵥ (eV : Fin (k + 1 + 1) → v.adicCompletion F) = eV
    rw [mat_mul, ← mulVec_mulVec, hb', ha']
  one_mem' := by
    show mat v (Qcone c₀ Q₀') 1 *ᵥ (eV : Fin (k + 1 + 1) → v.adicCompletion F) = eV
    rw [mat_one, one_mulVec]
  inv_mem' {g} hg := by
    have hg' : mat v (Qcone c₀ Q₀') g *ᵥ (eV : Fin (k + 1 + 1) → v.adicCompletion F) = eV := hg
    show mat v (Qcone c₀ Q₀') g⁻¹ *ᵥ (eV : Fin (k + 1 + 1) → v.adicCompletion F) = eV
    have h1 : mat v (Qcone c₀ Q₀') g⁻¹ *ᵥ (mat v (Qcone c₀ Q₀') g *ᵥ (eV : Fin (k + 1 + 1) → v.adicCompletion F)) =
        mat v (Qcone c₀ Q₀') g⁻¹ *ᵥ eV := by rw [hg']
    rw [mulVec_mulVec, ← mat_mul, inv_mul_cancel, mat_one, one_mulVec] at h1
    exact h1.symm

theorem mem_stabE_iff (g : SOv v (Qcone c₀ Q₀')) :
    g ∈ stabE v c₀ Q₀' ↔
      mat v (Qcone c₀ Q₀') g *ᵥ (eV : Fin (k + 1 + 1) → v.adicCompletion F) = eV := Iff.rfl

section PElem

variable (hc : c₀ ≠ 0) (hQ' : Q₀'.Nondegenerate)
include hc hQ'

theorem nG_mG_mem (w : Fin k → v.adicCompletion F) (h : SOv v Q₀') :
    nG v c₀ Q₀' hc hQ' w * mG v c₀ Q₀' h ∈ stabE v c₀ Q₀' := by
  rw [mem_stabE_iff, mat_mul, ← mulVec_mulVec, mat_mG, mM_mulVec_eV, mat_nG, nM_mulVec_eV]

/-- **The parametrization** $(w, h) \mapsto n(w)\,\mathrm{diag}(1,1,h)$ of $P = N \rtimes SO(V')$. -/
def pElem (p : (Fin k → v.adicCompletion F) × SOv v Q₀') : stabE v c₀ Q₀' :=
  ⟨nG v c₀ Q₀' hc hQ' p.1 * mG v c₀ Q₀' p.2, nG_mG_mem v c₀ Q₀' hc hQ' p.1 p.2⟩

theorem continuous_pElem : Continuous (pElem v c₀ Q₀' hc hQ') :=
  (((continuous_nG v c₀ Q₀' hc hQ').comp continuous_fst).mul
    ((continuous_mG v c₀ Q₀').comp continuous_snd)).subtype_mk _

omit hc hQ' in
theorem mG_mulVec_e₀ (h : SOv v Q₀') :
    mat v (Qcone c₀ Q₀') (mG v c₀ Q₀' h) *ᵥ (e₀ : Fin (k + 1 + 1) → v.adicCompletion F) = e₀ := by
  rw [mat_mG, e₀_eq_v3, mM_mulVec_v3, mulVec_zero]

/-- The $N$-coordinate of $n(w)\,\mathrm{diag}(1,1,h)$: $w = (g e_0)'$. -/
theorem tl_pElem (p : (Fin k → v.adicCompletion F) × SOv v Q₀') :
    tl (mat v (Qcone c₀ Q₀') ((pElem v c₀ Q₀' hc hQ' p : stabE v c₀ Q₀') : SOv v (Qcone c₀ Q₀')) *ᵥ
      (e₀ : Fin (k + 1 + 1) → v.adicCompletion F)) = p.1 := by
  show tl (mat v (Qcone c₀ Q₀') (nG v c₀ Q₀' hc hQ' p.1 * mG v c₀ Q₀' p.2) *ᵥ _) = _
  rw [mat_mul, ← mulVec_mulVec, mG_mulVec_e₀, mat_nG, nM_mulVec_e₀ _ _ (cv_ne v c₀ hc), tl_v3]

theorem pElem_injective : Function.Injective (pElem v c₀ Q₀' hc hQ') := by
  rintro ⟨w, h⟩ ⟨w', h'⟩ he
  have hw : w = w' := by
    have := congrArg (fun g : stabE v c₀ Q₀' =>
      tl (mat v (Qcone c₀ Q₀') (g : SOv v (Qcone c₀ Q₀')) *ᵥ (e₀ : Fin (k + 1 + 1) → v.adicCompletion F))) he
    simpa only [tl_pElem v c₀ Q₀' hc hQ'] using this
  subst hw
  have he' : nG v c₀ Q₀' hc hQ' w * mG v c₀ Q₀' h = nG v c₀ Q₀' hc hQ' w * mG v c₀ Q₀' h' := congrArg Subtype.val he
  rw [mul_right_inj] at he'
  rw [mG_injective v c₀ Q₀' he']

/-- **$P = \mathrm{Stab}(e) = N \rtimes SO(V')$**: every $g \in SO(V)(F_v)$ fixing $e$ is
$n(w)\,\mathrm{diag}(1,1,h)$ with $w = (ge_0)'$ and $h \in SO(V')(F_v)$. -/
@[kb "weil1982" "§2.4 (the stabilizer of an isotropic vector is SO(V') ⋉ V') [unverified]"]
theorem exists_pElem (g : stabE v c₀ Q₀') : ∃ p, pElem v c₀ Q₀' hc hQ' p = g := by
  have he : mat v (Qcone c₀ Q₀') (g : SOv v (Qcone c₀ Q₀')) *ᵥ (eV : Fin (k + 1 + 1) → v.adicCompletion F) = eV := g.2
  have hiso : (mat v (Qcone c₀ Q₀') (g : SOv v (Qcone c₀ Q₀')))ᵀ * (coneForm (cv v c₀) (QFv v Q₀')).hessian *
      mat v (Qcone c₀ Q₀') (g : SOv v (Qcone c₀ Q₀')) = (coneForm (cv v c₀) (QFv v Q₀')).hessian := by
    have := isometry_mat v (Qcone c₀ Q₀') (g : SOv v (Qcone c₀ Q₀'))
    rwa [hessV_cone] at this
  obtain ⟨M, hM, hgM⟩ := eq_nM_mul_mM_of_fix (cv v c₀) (QFv v Q₀') (cv_ne v c₀ hc) _ hiso he
  have hdet : M.det = 1 := by
    have := det_mat v (Qcone c₀ Q₀') (g : SOv v (Qcone c₀ Q₀'))
    rwa [hgM, det_mul, det_nM _ _ (cv_ne v c₀ hc) (det_hess_cone_ne v c₀ Q₀' hc hQ'), one_mul, det_mM] at this
  refine ⟨(tl (mat v (Qcone c₀ Q₀') (g : SOv v (Qcone c₀ Q₀')) *ᵥ (e₀ : Fin (k + 1 + 1) → v.adicCompletion F)),
    mkSO v Q₀' M (by rw [hessV_base]; exact hM) hdet), ?_⟩
  apply Subtype.ext
  apply mat_injective v (Qcone c₀ Q₀')
  show mat v (Qcone c₀ Q₀') (nG v c₀ Q₀' hc hQ' _ * mG v c₀ Q₀' (mkSO v Q₀' M _ hdet)) = _
  rw [mat_mul, mat_nG, mat_mG, mat_mkSO]
  exact hgM.symm

/-- The inverse coordinates $g \mapsto (w, h)$ of `pElem` (noncomputable). -/
def pInv (g : stabE v c₀ Q₀') : (Fin k → v.adicCompletion F) × SOv v Q₀' :=
  Classical.choose (exists_pElem v c₀ Q₀' hc hQ' g)

theorem pElem_pInv (g : stabE v c₀ Q₀') : pElem v c₀ Q₀' hc hQ' (pInv v c₀ Q₀' hc hQ' g) = g :=
  Classical.choose_spec (exists_pElem v c₀ Q₀' hc hQ' g)

theorem pInv_pElem (p : (Fin k → v.adicCompletion F) × SOv v Q₀') :
    pInv v c₀ Q₀' hc hQ' (pElem v c₀ Q₀' hc hQ' p) = p :=
  pElem_injective v c₀ Q₀' hc hQ' (pElem_pInv v c₀ Q₀' hc hQ' _)

theorem pInv_fst (g : stabE v c₀ Q₀') :
    (pInv v c₀ Q₀' hc hQ' g).1 = tl (mat v (Qcone c₀ Q₀') (g : SOv v (Qcone c₀ Q₀')) *ᵥ
      (e₀ : Fin (k + 1 + 1) → v.adicCompletion F)) := by
  conv_rhs => rw [← pElem_pInv v c₀ Q₀' hc hQ' g]
  exact (tl_pElem v c₀ Q₀' hc hQ' _).symm

omit hc hQ' in
theorem submatrix_mM (M : Matrix (Fin k) (Fin k) (v.adicCompletion F)) :
    ((mM M).submatrix Fin.succ Fin.succ).submatrix Fin.succ Fin.succ = M := by
  ext i j
  simp [mM]

/-- The matrix of the $SO(V')$-coordinate: $h = $ the lower $k \times k$ block of $n(-w)\,g$. -/
theorem mat_pInv_snd (g : stabE v c₀ Q₀') :
    mat v Q₀' (pInv v c₀ Q₀' hc hQ' g).2 =
      ((nM (cv v c₀) (QFv v Q₀') (-tl (mat v (Qcone c₀ Q₀') (g : SOv v (Qcone c₀ Q₀')) *ᵥ
        (e₀ : Fin (k + 1 + 1) → v.adicCompletion F))) * mat v (Qcone c₀ Q₀') (g : SOv v (Qcone c₀ Q₀'))).submatrix
          Fin.succ Fin.succ).submatrix Fin.succ Fin.succ := by
  have hp := pElem_pInv v c₀ Q₀' hc hQ' g
  have hw := pInv_fst v c₀ Q₀' hc hQ' g
  generalize pInv v c₀ Q₀' hc hQ' g = p at hp hw ⊢
  have hgm : mat v (Qcone c₀ Q₀') (g : SOv v (Qcone c₀ Q₀')) =
      nM (cv v c₀) (QFv v Q₀') p.1 * mM (mat v Q₀' p.2) :=
    (congrArg (fun x : stabE v c₀ Q₀' => mat v (Qcone c₀ Q₀') (x : SOv v (Qcone c₀ Q₀'))) hp).symm
  have h1 : nM (cv v c₀) (QFv v Q₀') (-tl (mat v (Qcone c₀ Q₀') (g : SOv v (Qcone c₀ Q₀')) *ᵥ
        (e₀ : Fin (k + 1 + 1) → v.adicCompletion F))) * mat v (Qcone c₀ Q₀') (g : SOv v (Qcone c₀ Q₀')) =
      mM (mat v Q₀' p.2) := by
    rw [← hw, hgm, ← Matrix.mul_assoc, nM_neg_mul _ _ (cv_ne v c₀ hc), Matrix.one_mul]
  rw [h1, submatrix_mM]

theorem continuous_pInv : Continuous (pInv v c₀ Q₀' hc hQ') := by
  have hmat : Continuous fun g : stabE v c₀ Q₀' => mat v (Qcone c₀ Q₀') (g : SOv v (Qcone c₀ Q₀')) :=
    (continuous_mat v).comp continuous_subtype_val
  have hw : Continuous fun g : stabE v c₀ Q₀' => tl (mat v (Qcone c₀ Q₀') (g : SOv v (Qcone c₀ Q₀')) *ᵥ
      (e₀ : Fin (k + 1 + 1) → v.adicCompletion F)) :=
    continuous_tl.comp (hmat.matrix_mulVec continuous_const)
  have h1 : Continuous fun g : stabE v c₀ Q₀' => (pInv v c₀ Q₀' hc hQ' g).1 := by
    have : (fun g : stabE v c₀ Q₀' => (pInv v c₀ Q₀' hc hQ' g).1) =
        fun g : stabE v c₀ Q₀' => tl (mat v (Qcone c₀ Q₀')
          (g : SOv v (Qcone c₀ Q₀')) *ᵥ (e₀ : Fin (k + 1 + 1) → v.adicCompletion F)) :=
      funext (pInv_fst v c₀ Q₀' hc hQ')
    rw [this]; exact hw
  have h2 : Continuous fun g : stabE v c₀ Q₀' => (pInv v c₀ Q₀' hc hQ' g).2 := by
    refine continuous_of_mat v hQ' (f := fun g : stabE v c₀ Q₀' => (pInv v c₀ Q₀' hc hQ' g).2) ?_
    simp_rw [mat_pInv_snd v c₀ Q₀' hc hQ']
    have hn : Continuous fun g : stabE v c₀ Q₀' => nM (cv v c₀) (QFv v Q₀') (-tl (mat v (Qcone c₀ Q₀')
        (g : SOv v (Qcone c₀ Q₀')) *ᵥ (e₀ : Fin (k + 1 + 1) → v.adicCompletion F))) :=
      (continuous_nM _ _).comp hw.neg
    exact ((hn.matrix_mul hmat).matrix_submatrix _ _).matrix_submatrix _ _
  exact h1.prodMk h2

/-- **`pElem` is a topological embedding** (with the continuous left inverse `pInv`). -/
theorem isEmbedding_pElem : Topology.IsEmbedding (pElem v c₀ Q₀' hc hQ') :=
  Function.LeftInverse.isEmbedding (pInv_pElem v c₀ Q₀' hc hQ') (continuous_pInv v c₀ Q₀' hc hQ')
    (continuous_pElem v c₀ Q₀' hc hQ')

/-- **`pElem` is a measurable embedding onto $P = \mathrm{Stab}(e)$** (injective, continuous, surjective). -/
@[kb "weil1982" "§2.4 (the stabilizer of an isotropic vector, Haar measure on SO(V') ⋉ V') [unverified]"]
theorem measurableEmbedding_pElem : MeasurableEmbedding (pElem v c₀ Q₀' hc hQ') := by
  refine (isEmbedding_pElem v c₀ Q₀' hc hQ').measurableEmbedding ?_
  have : Set.range (pElem v c₀ Q₀' hc hQ') = Set.univ := Set.range_eq_univ.2 (exists_pElem v c₀ Q₀' hc hQ')
  rw [this]; exact MeasurableSet.univ

end PElem

end Cone

/-! ### Unimodularity of $SO(V)(F_v)$ -/

section Unimodular

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {N : ℕ} (Q₀ : QuadForm (𝓞 F) N)

/-- The local measure `muLocSO` is left invariant. -/
instance isMulLeftInvariant_muLocSO (lam : ℝ) : (muLocSO v Q₀ lam).IsMulLeftInvariant := by
  unfold muLocSO; infer_instance

/-- The local measure `muLocSO` is finite on compact sets. -/
instance isFiniteMeasureOnCompacts_muLocSO (lam : ℝ) : IsFiniteMeasureOnCompacts (muLocSO v Q₀ lam) := by
  unfold muLocSO; infer_instance

/-- `muLocSO` is a Haar measure for nondegenerate $Q_0$ (its value on $SO(L_v)$ is $\alpha_v > 0$). -/
theorem isHaarMeasure_muLocSO (hQ : Q₀.Nondegenerate) : (muLocSO v Q₀ 1).IsHaarMeasure := by
  have h : Real.toNNReal (NF.siegelDensity v Q₀ Q₀ / 1) ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]
    exact div_pos (siegelDensity_pos v Q₀ hQ) one_pos
  unfold muLocSO haarNorm
  exact Measure.IsHaarMeasure.nnreal_smul _ h

/-- **$O(V)(F_v)$ is unimodular for `muLoc`**: the Haar measure is right invariant. For $x \in O(V)(F_v)$ the measure
$A \mapsto \mu(Ax^{-1})$ is a left invariant Haar measure, hence $c_x\mu$; evaluating at $xO(L_v)$, where
$\mu(xO(L_v)x^{-1}) = \mu(O(L_v))$ (`muLoc_conj_stdStab`), gives $c_x = 1$. -/
theorem isMulRightInvariant_muLoc (hQ : Q₀.Nondegenerate) : (muLoc v Q₀ 1).IsMulRightInvariant := by
  have hH : (muLoc v Q₀ 1).IsHaarMeasure := isHaarMeasure_muLoc v Q₀ hQ one_pos
  refine ⟨fun x => ?_⟩
  set μ := muLoc v Q₀ 1 with hμ
  set K := stdStab (Q₀.map (algebraMap (𝓞 F) F)) v with hK
  have hmeas : Measurable (fun y : orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F) => y * x) :=
    measurable_mul_const x
  have hinv : (μ.map (fun y => y * x)).IsMulLeftInvariant := ⟨fun g => by
    rw [Measure.map_map (measurable_const_mul g) hmeas]
    have e : ((fun y => g * y) ∘ (fun y => y * x)) = ((fun y => y * x) ∘ (fun y => g * y)) :=
      funext fun y => (mul_assoc g y x).symm
    rw [e, ← Measure.map_map hmeas (measurable_const_mul g), map_mul_left_eq_self]⟩
  have hfin : IsFiniteMeasureOnCompacts (μ.map (fun y => y * x)) := ⟨fun C hC => by
    rw [Measure.map_apply hmeas hC.measurableSet]
    exact ((Homeomorph.mulRight x).isCompact_preimage.2 hC).measure_lt_top⟩
  have hsm := Measure.isMulLeftInvariant_eq_smul (μ.map (fun y => y * x)) μ
  have hS : MeasurableSet (x • (K : Set (orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)))) :=
    ((isOpen_stdStab v _).smul x).measurableSet
  have hpre : (fun y => y * x) ⁻¹' (x • (K : Set (orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)))) =
      ((K.map (MulAut.conj x).toMonoidHom : Subgroup _) : Set _) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_smul_set, smul_eq_mul, SetLike.mem_coe, Subgroup.mem_map,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨k, hk, hky⟩
      exact ⟨k, hk, by rw [hky, mul_inv_cancel_right]⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k, hk, by group⟩
  have e1 : (μ.map (fun y => y * x)) (x • (K : Set (orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)))) =
      μ K := by
    rw [Measure.map_apply hmeas hS, hpre]
    exact muLoc_conj_stdStab v Q₀ hQ x
  have hK0 : μ K ≠ 0 := ((isOpen_stdStab v _).measure_pos μ ⟨1, K.one_mem⟩).ne'
  have hKt : μ K ≠ ⊤ := (isCompact_stdStab v _).measure_lt_top.ne
  have h1 : (Measure.haarScalarFactor (μ.map (fun y => y * x)) μ : ℝ≥0∞) * μ K = 1 * μ K := by
    have := congrArg (fun m : Measure _ => m (x • (K : Set (orthGroup (Q₀.map (algebraMap (𝓞 F) F))
      (v.adicCompletion F))))) hsm
    rw [e1, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, measure_smul] at this
    rw [one_mul]; exact this.symm
  have h2 := (ENNReal.mul_left_inj hK0 hKt).1 h1
  have h3 : Measure.haarScalarFactor (μ.map (fun y => y * x)) μ = 1 := by exact_mod_cast h2
  rw [h3, one_smul] at hsm
  exact hsm

/-- **$SO(V)(F_v)$ is unimodular for `muLocSO`**: the Haar measure is right invariant (the restriction of the right
invariant measure `muLoc` to the open subgroup $SO(V)(F_v)$). -/
@[kb "weil1982" "§2.1 (unimodularity of SO(V)(F_v)) [unverified]"]
theorem isMulRightInvariant_muLocSO (hQ : Q₀.Nondegenerate) (hN : 1 ≤ N) :
    (muLocSO v Q₀ 1).IsMulRightInvariant := by
  have := isMulRightInvariant_muLoc v Q₀ hQ
  have hE := measurableEmbedding_soSub v Q₀ hQ
  rw [muLocSO_eq_comap v Q₀ hQ (by omega) one_pos]
  refine ⟨fun s => ?_⟩
  ext B hB
  rw [Measure.map_apply (measurable_mul_const s) hB, hE.comap_apply, hE.comap_apply]
  have himg : Subtype.val '' ((fun y => y * s) ⁻¹' B) =
      (fun y => y * (s : orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F))) ⁻¹' (Subtype.val '' B) := by
    ext y
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b * s, hb, rfl⟩
    · rintro ⟨b, hb, hby⟩
      refine ⟨b * s⁻¹, by simpa using hb, ?_⟩
      show (b : orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)) *
        (s : orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F))⁻¹ = y
      rw [hby, mul_inv_cancel_right]
  rw [himg, ← Measure.map_apply (measurable_mul_const _) (hE.measurableSet_image.2 hB), map_mul_right_eq_self]

/-- **Inversion invariance**: $\int f(g^{-1})\,d\mu_v = \int f\,d\mu_v$ for the local measure on $SO(V)(F_v)$ (a
unimodular group; `ConeReal.inv_eq_self_of_unimodular`). -/
@[kb "weil1982" "§2.1 (unimodularity of SO(V)(F_v)) [unverified]"]
theorem lintegral_inv_muLocSO (hQ : Q₀.Nondegenerate) (hN : 1 ≤ N) {f : SOv v Q₀ → ℝ≥0∞}
    (hf : Measurable f) : ∫⁻ g, f g⁻¹ ∂muLocSO v Q₀ 1 = ∫⁻ g, f g ∂muLocSO v Q₀ 1 := by
  have := isHaarMeasure_muLocSO v Q₀ hQ
  have := isMulRightInvariant_muLocSO v Q₀ hQ hN
  have h := ConeReal.inv_eq_self_of_unimodular (muLocSO v Q₀ 1)
  rw [← lintegral_map hf measurable_inv, ← Measure.inv_def, h]

end Unimodular

/-! ### The sphere identity for an arbitrary section -/

section Sphere

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

/-- An element of $SO(\langle m_0\rangle \perp Q_0')(F_v)$ fixing $e_0$ is $\mathrm{diag}(1, t)$ with
$t \in SO(Q_0')(F_v)$. -/
theorem exists_iotaSO_eq (m₀ : 𝓞 F) (hm : m₀ ≠ 0) (Q₀' : QuadForm (𝓞 F) n) (g : SOv v (splitForm m₀ Q₀'))
    (hg : mat v (splitForm m₀ Q₀') g *ᵥ (e₀ : Fin (n + 1) → v.adicCompletion F) = e₀) :
    ∃ t : SOv v Q₀', iotaSO v m₀ Q₀' t = g := by
  obtain ⟨h, hh⟩ := FibreO.exists_iota_eq v (QQ m₀ Q₀') (mm m₀) (QQ' Q₀') (hEE m₀ Q₀') (mm_ne m₀ hm) g.1 hg
  have hd : (h : GL (Fin n) (v.adicCompletion F)).val.det = 1 := by
    have := g.2
    rw [mem_soSub, ← hh, FibreO.iota_val, det_cornerMat, one_mul] at this
    exact this
  exact ⟨⟨h, hd⟩, Subtype.ext hh⟩

/-- **The sphere identity for an arbitrary section.** Let $s$ be any map from the quadric
$\{Q = m\} \subset F_v^{n+1}$ to $SO(\langle m_0\rangle\perp Q_0')(F_v)$ with $s(x)e_0 = x$ for all $x$ (for instance any
measurable section of $g \mapsto ge_0$; measurability is not needed for the identity itself). Then for measurable
$f \ge 0$,
$$\int f\,d\mu_{SO(V)} = |2m_0|_v^{-n}\int_{\{Q = m\}}\int_{SO(Q_0')} f\big(s(x)\,\mathrm{diag}(1, h)\big)\,d\mu_{SO(Q_0')}(h)\,d\sigma_m(x).$$
This generalizes `FibreSO.lintegral_orbital_finitePlace`, which is the case of the reflection section. Proof: for each $x$,
$s(x)^{-1}\,\mathrm{orb}(x, 1)$ fixes $e_0$, so it is $\iota(t_x)$ (`exists_iotaSO_eq`), and left invariance of
$\mu_{SO(Q_0')}$ absorbs $t_x$. -/
@[kb "weil1982" "§2.4 Lemma 2.4.1 (sphere identity for an arbitrary section) [unverified]"]
theorem lintegral_orbital_section (m₀ : 𝓞 F) (hm : m₀ ≠ 0) (Q₀' : QuadForm (𝓞 F) n)
    (hQ' : Q₀'.Nondegenerate) (hn : 1 ≤ n)
    (s : FibreO.sphereSet v (QQ m₀ Q₀') (mm m₀) → SOv v (splitForm m₀ Q₀'))
    (hs : ∀ x, mat v (splitForm m₀ Q₀') (s x) *ᵥ (e₀ : Fin (n + 1) → v.adicCompletion F) =
      (x : Fin (n + 1) → v.adicCompletion F))
    {f : SOv v (splitForm m₀ Q₀') → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ g, f g ∂muLocSO v (splitForm m₀ Q₀') 1 =
      ENNReal.ofReal ((absTwoM v m₀ ^ n)⁻¹) *
        ∫⁻ x, ∫⁻ h, f (s x * iotaSO v m₀ Q₀' h) ∂muLocSO v Q₀' 1 ∂nuS v m₀ hm Q₀' hQ' := by
  rw [FibreSO.lintegral_orbital_finitePlace v m₀ hm Q₀' hQ' hn hf]
  congr 1
  refine lintegral_congr fun x => ?_
  -- the element `o = orb(x, 1)`
  have hrel : ∀ h : SOv v Q₀', FibreSO.orbSO v m₀ hm Q₀' hQ' hn (x, h) =
      FibreSO.orbSO v m₀ hm Q₀' hQ' hn (x, 1) * iotaSO v m₀ Q₀' h := by
    intro h
    apply Subtype.ext
    simp [FibreSO.orbSO, FibreO.orb, iotaSO_val]
  have hosec : ((FibreSO.orbSO v m₀ hm Q₀' hQ' hn (x, 1)).1 : orthGroup (QQ m₀ Q₀') (v.adicCompletion F)) =
      FibreO.secOrth v (QQ m₀ Q₀') (mm m₀) (QQ' Q₀') (hEE m₀ Q₀') (mm_ne m₀ hm) (QQ'_nondeg Q₀' hQ') hn x := by
    simp [FibreSO.orbSO, FibreO.orb]
  have hox : mat v (splitForm m₀ Q₀') (FibreSO.orbSO v m₀ hm Q₀' hQ' hn (x, 1)) *ᵥ
      (e₀ : Fin (n + 1) → v.adicCompletion F) = (x : Fin (n + 1) → v.adicCompletion F) := by
    have h1 := congrArg Subtype.val
      ((FibreO.orbitSection v (QQ m₀ Q₀') (mm m₀) (QQ' Q₀') (hEE m₀ Q₀') (mm_ne m₀ hm)
        (QQ'_nondeg Q₀' hQ') hn).sec_smul x)
    have h2 : mat v (splitForm m₀ Q₀') (FibreSO.orbSO v m₀ hm Q₀' hQ' hn (x, 1)) =
        ((FibreO.secOrth v (QQ m₀ Q₀') (mm m₀) (QQ' Q₀') (hEE m₀ Q₀') (mm_ne m₀ hm) (QQ'_nondeg Q₀' hQ') hn x :
          orthGroup (QQ m₀ Q₀') (v.adicCompletion F)) : GL (Fin (n + 1)) (v.adicCompletion F)).val :=
      congrArg (fun y : orthGroup (QQ m₀ Q₀') (v.adicCompletion F) => (y : GL (Fin (n + 1)) (v.adicCompletion F)).val) hosec
    rw [h2]
    exact h1
  have hu : mat v (splitForm m₀ Q₀') ((s x)⁻¹ * FibreSO.orbSO v m₀ hm Q₀' hQ' hn (x, 1)) *ᵥ
      (e₀ : Fin (n + 1) → v.adicCompletion F) = e₀ := by
    rw [mat_mul, ← mulVec_mulVec, hox, ← hs x, mulVec_mulVec, ← mat_mul, inv_mul_cancel, mat_one, one_mulVec]
  obtain ⟨t, ht⟩ := exists_iotaSO_eq v m₀ hm Q₀' _ hu
  have hoe : FibreSO.orbSO v m₀ hm Q₀' hQ' hn (x, 1) = s x * iotaSO v m₀ Q₀' t := by
    rw [ht, mul_inv_cancel_left]
  have key : ∀ h : SOv v Q₀', FibreSO.orbSO v m₀ hm Q₀' hQ' hn (x, h) = s x * iotaSO v m₀ Q₀' (t * h) := by
    intro h
    rw [hrel h, hoe, map_mul, mul_assoc]
  simp_rw [key]
  exact lintegral_mul_left_eq_self (fun h => f (s x * iotaSO v m₀ Q₀' h)) t

end Sphere

end QuadFormsKB.Tamagawa.Measure.ConeFinite
