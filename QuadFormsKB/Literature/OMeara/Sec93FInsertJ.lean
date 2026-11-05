/-
# O'Meara 93:28, sufficiency, step 8: the lattice $J \cong \langle \pi A(0,0) \rangle$

**Setting**: $R$ a discrete valuation ring with fraction field $F$, $2 \in F^\times$, $\pi \in R$ a prime element;
quadratic spaces over $F$, lattices `Submodule R _`, $A \perp B$ = `A.prod B`.

**Defines**
* `QJ π`: the quadratic form $Q(x, y) = 2\pi x y$ on $F \times F$, with $B((a, b), (c, d)) = \pi (a d + b c)$;
* `latJ`: the lattice $R \times R$, i.e. $J = \mathfrak o e_0 + \mathfrak o e_1$ with $Q(e_0) = Q(e_1) = 0$,
  $B(e_0, e_1) = \pi$ (a lattice $\pi A(0,0)$).

**Proves** (O'Meara 1963, §93F, proof of 93:28, sufficiency, step 8, p. 276)
* `bil_QJ`, `nondegenerate_QJ`, `latJ_fg`, `isLattice_latJ`, `scale_latJ`, `isModular_latJ`, `finrank_latJ`;
* `normGroup_latJ_le`, `normGroup_subA_latJ_le`, `subA_latJ_of_le`: the norm groups of $J$ and of $J^{\mathfrak a}$;
* `isometricLat_cancel_latJ`: $L \perp J \cong K \perp J$ implies $L \cong K$, by Theorem 93:14 applied to the
  hyperbolic plane $0 \perp J$ of the scaled form $\pi^{-1} Q$.
-/
import QuadFormsKB.Literature.OMeara.Sec93FSuffCancel
import QuadFormsKB.Literature.OMeara.Sec93FSuffGood

open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.InsertJ

open Adjoin28 SuffCancel

section Basic

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]

/-- **The form of $J$**: $Q_J(x, y) = 2\pi x y$ on $F \times F$ (so
$B_J((a, b), (c, d)) = \pi (a d + b c)$). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 8, p. 276 (the lattice J = πA(0,0))"]
def QJ (π : R) : QuadraticForm F (F × F) :=
  (2 * algebraMap R F π) • QuadraticMap.linMulLin (LinearMap.fst F F F) (LinearMap.snd F F F)

/-- **The lattice $J = R \times R$** of the form $Q_J$: spanned by $e_0 = (1, 0)$ and $e_1 = (0, 1)$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 8, p. 276 (the lattice J = πA(0,0))"]
def latJ : Submodule R (F × F) := span R {((1 : F), (0 : F)), ((0 : F), (1 : F))}

variable (π : R)

/-- $Q_J(x, y) = 2\pi x y$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 8, p. 276 (the lattice J = πA(0,0))"]
theorem QJ_apply (p : F × F) : QJ (F := F) π p = 2 * algebraMap R F π * (p.1 * p.2) := by
  simp [QJ]

/-- $B_J((a, b), (c, d)) = \pi (a d + b c)$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 8, p. 276 (the lattice J = πA(0,0))"]
theorem bil_QJ (a b c d : F) :
    bil (QJ (F := F) π) (a, b) (c, d) = algebraMap R F π * (a * d + b * c) := by
  apply adj_eq_bil_of
  simp only [QJ_apply, Prod.mk_add_mk]
  ring

/-- Membership in $J$: $(x, y) \in J$ iff $x, y \in R$. -/
theorem mem_latJ {p : F × F} : p ∈ (latJ : Submodule R (F × F)) ↔
    ∃ a b : R, p = (algebraMap R F a, algebraMap R F b) := by
  rw [latJ, mem_span_pair]
  constructor
  · rintro ⟨a, b, rfl⟩
    exact ⟨a, b, by ext <;> simp [Algebra.smul_def]⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨a, b, by ext <;> simp [Algebra.smul_def]⟩

/-- $J$ is finitely generated. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 8, p. 276 (the lattice J = πA(0,0))"]
theorem latJ_fg : (latJ : Submodule R (F × F)).FG :=
  fg_span (Set.toFinite _)

/-- $J$ is a lattice in $F \times F$: finitely generated and spanning over $F$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 8, p. 276 (the lattice J = πA(0,0))"]
theorem isLattice_latJ : (latJ : Submodule R (F × F)).IsLattice F := by
  refine ⟨latJ_fg, ?_⟩
  rw [eq_top_iff]
  rintro ⟨a, b⟩ -
  have h0 : ((1 : F), (0 : F)) ∈ span F ((latJ : Submodule R (F × F)) : Set (F × F)) :=
    subset_span ((mem_latJ).mpr ⟨1, 0, by simp⟩)
  have h1 : ((0 : F), (1 : F)) ∈ span F ((latJ : Submodule R (F × F)) : Set (F × F)) :=
    subset_span ((mem_latJ).mpr ⟨0, 1, by simp⟩)
  have := add_mem (smul_mem _ a h0) (smul_mem _ b h1)
  simpa using this

/-- **$Q_J$ is non-degenerate** when $\pi \ne 0$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 8, p. 276 (the lattice J = πA(0,0))"]
theorem nondegenerate_QJ (hπ0 : π ≠ 0) :
    (QuadraticMap.associated (R := F) (QJ (F := F) π)).Nondegenerate := by
  have hπ : algebraMap R F π ≠ 0 := by simpa using hπ0
  have hkey : ∀ x : F × F, (∀ y : F × F, bil (QJ (F := F) π) x y = 0) → x = 0 := by
    rintro ⟨a, b⟩ h
    have h1 := h (1, 0)
    have h2 := h (0, 1)
    rw [bil_QJ] at h1 h2
    simp [hπ] at h1 h2
    ext <;> simp [h1, h2]
  exact ⟨fun m hm => hkey m hm, fun m hm => hkey m fun y => by rw [bil_comm]; exact hm y⟩

/-- $J$ is $\pi R$-modular of rank $2$ (when $\pi \ne 0$): its Gram matrix in the base $e_0, e_1$ is
$\pi \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$. -/
theorem isModular_latJ_aux (hπ0 : π ≠ 0) :
    IsModular (QJ (F := F) π) (R ∙ algebraMap R F π) (latJ : Submodule R (F × F)) ∧
      finrank R (latJ : Submodule R (F × F)) = 2 := by
  have hπ : algebraMap R F π ≠ 0 := by simpa using hπ0
  let v : Fin 2 → F × F := ![((1 : F), (0 : F)), ((0 : F), (1 : F))]
  let U : Matrix (Fin 2) (Fin 2) R := !![0, 1; 1, 0]
  have hG : gram (QJ (F := F) π) v = algebraMap R F π • U.map (algebraMap R F) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [v, U, gram, bil_QJ, QJ_apply]
  have hU : IsUnit U.det := by
    simp [U, Matrix.det_fin_two]
  have hspan : span R (Set.range v) = (latJ : Submodule R (F × F)) := by
    rw [latJ]
    congr 1
    ext p
    simp [v]
    tauto
  have := isModular_span_of_gram (QJ (F := F) π) hπ hU hG
  rw [hspan] at this
  simpa using this

/-- **The scale of $J$**: $\mathfrak s J = \pi R$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 8, p. 276 (the lattice J = πA(0,0))"]
theorem scale_latJ (hπ0 : π ≠ 0) :
    scale (QJ (F := F) π) (latJ : Submodule R (F × F)) = R ∙ algebraMap R F π :=
  (isModular_latJ_aux π hπ0).1.2.1

/-- **$J$ is $\pi R$-modular.** -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 8, p. 276 (the lattice J = πA(0,0))"]
theorem isModular_latJ (hπ0 : π ≠ 0) :
    IsModular (QJ (F := F) π) (R ∙ algebraMap R F π) (latJ : Submodule R (F × F)) :=
  (isModular_latJ_aux π hπ0).1

/-- **$J$ has rank $2$.** -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 8, p. 276 (the lattice J = πA(0,0))"]
theorem finrank_latJ (hπ0 : π ≠ 0) : finrank R (latJ : Submodule R (F × F)) = 2 :=
  (isModular_latJ_aux π hπ0).2

/-- **The norm group of $J$**: every element of $\mathfrak g J$ lies in $2\pi R$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 8, p. 276 (the lattice J = πA(0,0))"]
theorem normGroup_latJ_le (hπ0 : π ≠ 0) :
    ∀ z ∈ normGroup (QJ (F := F) π) (latJ : Submodule R (F × F)),
      ∃ r : R, z = 2 * algebraMap R F π * algebraMap R F r := by
  rintro z ⟨x, hx, c, hc, rfl⟩
  rw [scale_latJ π hπ0, mem_span_singleton] at hc
  obtain ⟨r, rfl⟩ := hc
  obtain ⟨a, b, rfl⟩ := mem_latJ.mp hx
  refine ⟨a * b + r, ?_⟩
  simp only [QJ_apply, Algebra.smul_def, map_add, map_mul]
  ring

/-- **The norm group of $J^{\mathfrak s}$** for an $R$-submodule $\mathfrak s \subseteq \pi R$: every element is
$2c$ with $c \in \mathfrak s$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 8, p. 276 (the lattice J = πA(0,0))"]
theorem normGroup_subA_latJ_le (s : Submodule R F) (_hs : s ≤ R ∙ algebraMap R F π) :
    ∀ z ∈ normGroup (QJ (F := F) π) (subA (QJ (F := F) π) s (latJ : Submodule R (F × F))),
      ∃ c ∈ s, z = 2 * c := by
  rintro z ⟨x, hx, c, hc, rfl⟩
  have hcs : c ∈ s := scale_subA_le _ s _ hc
  obtain ⟨a, b, rfl⟩ := mem_latJ.mp hx.1
  have h1 := hx.2 ((1 : F), (0 : F)) (mem_latJ.mpr ⟨1, 0, by simp⟩)
  rw [bil_QJ] at h1
  simp only [mul_zero, mul_one, zero_add] at h1
  refine ⟨algebraMap R F a * (algebraMap R F π * algebraMap R F b) + c, ?_, ?_⟩
  · refine add_mem ?_ hcs
    have := s.smul_mem a h1
    simpa [Algebra.smul_def, mul_zero, mul_one] using this
  · simp only [QJ_apply]
    ring

/-- **$J^{\mathfrak a} = J$** when $\pi R \subseteq \mathfrak a$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 8, p. 276 (the lattice J = πA(0,0))"]
theorem subA_latJ_of_le (hπ0 : π ≠ 0) (s : Submodule R F) (hs : R ∙ algebraMap R F π ≤ s) :
    subA (QJ (F := F) π) s (latJ : Submodule R (F × F)) = latJ :=
  (subA_eq_self_iff _).2 ((scale_latJ π hπ0).le.trans hs)

end Basic

section Cancel

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]

/-- Isometry of lattices is unchanged by scaling the form by a non-zero constant. -/
theorem isometricLat_smul_iff (Q : QuadraticForm F V) {α : F} (hα : α ≠ 0) {L K : Submodule R V} :
    IsometricLat (α • Q) (α • Q) L K ↔ IsometricLat Q Q L K := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f, fun x => by
      have := hf x
      simp only [smul_apply, smul_eq_mul] at this
      exact mul_left_cancel₀ hα this⟩
  · rintro ⟨f, hf⟩
    exact ⟨f, fun x => by simp only [smul_apply, smul_eq_mul, hf x]⟩

/-- Orthogonal splittings are unchanged by scaling the form. -/
theorem isOrthSum_smul (Q : QuadraticForm F V) (α : F) {L J K : Submodule R V} (h : IsOrthSum Q L J K) :
    IsOrthSum (α • Q) L J K :=
  ⟨fun x hx y hy => by rw [bil_smul_form, h.orth x hx y hy, mul_zero], h.disjoint, h.sup_eq⟩

/-- The image of a span of two vectors under an isometry is the span of the images. -/
theorem imgLat_span_pair {L K : Submodule R V} (f : L ≃ₗ[R] K) {x y : V} (hx : x ∈ L) (hy : y ∈ L) :
    imgLat f (span R {x, y}) = span R {(f ⟨x, hx⟩ : V), (f ⟨y, hy⟩ : V)} := by
  ext z
  rw [mem_imgLat]
  constructor
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨a, b, hab⟩ := mem_span_pair.mp hm
    have : m = a • (⟨x, hx⟩ : L) + b • (⟨y, hy⟩ : L) := Subtype.ext (by simp [← hab])
    rw [this, map_add, map_smul, map_smul]
    simp only [Submodule.coe_add, Submodule.coe_smul]
    exact mem_span_pair.mpr ⟨a, b, rfl⟩
  · intro hz
    obtain ⟨a, b, rfl⟩ := mem_span_pair.mp hz
    refine ⟨a • (⟨x, hx⟩ : L) + b • (⟨y, hy⟩ : L), ?_, ?_⟩
    · simp only [Submodule.coe_add, Submodule.coe_smul]
      exact mem_span_pair.mpr ⟨a, b, rfl⟩
    · have : (⟨a • x + b • y, add_mem (L.smul_mem a hx) (L.smul_mem b hy)⟩ : L) =
          a • (⟨x, hx⟩ : L) + b • (⟨y, hy⟩ : L) := Subtype.ext rfl
      simp only [Submodule.coe_add, Submodule.coe_smul, map_add, map_smul]

/-- The plane $0 \perp J$ is spanned by $(0, e_0)$ and $(0, e_1)$. -/
theorem bot_prod_latJ_eq_span :
    (⊥ : Submodule R V).prod (latJ : Submodule R (F × F)) =
      span R {((0 : V), ((1 : F), (0 : F))), ((0 : V), ((0 : F), (1 : F)))} := by
  ext ⟨v, p⟩
  constructor
  · rintro ⟨hv, hp⟩
    obtain rfl : v = 0 := (mem_bot R).mp hv
    obtain ⟨a, b, rfl⟩ := mem_latJ.mp hp
    exact mem_span_pair.mpr ⟨a, b, by ext <;> simp [Algebra.smul_def]⟩
  · intro h
    obtain ⟨a, b, hab⟩ := mem_span_pair.mp h
    rw [← hab]
    refine ⟨by simp, mem_latJ.mpr ⟨a, b, ?_⟩⟩
    ext <;> simp [Algebra.smul_def]

/-- **Cancelling $J$ by Theorem 93:14** (O'Meara 1963, §93F, proof of 93:28, step 8, p. 276): if
$L \perp J \cong K \perp J$ with $J = \pi A(0,0)$, then $L \cong K$. For the form $\pi^{-1}Q$ the plane $0 \perp J$ is a
unimodular hyperbolic plane $A(0,0)$, so 93:14 applies to the two splittings $K \perp J = (K \perp 0) \perp (0 \perp J)
= \varphi(L \perp 0) \perp \varphi(0 \perp J)$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 8, p. 276 (cancelling J by 93:14)"]
theorem isometricLat_cancel_latJ (Q : QuadraticForm F V) {π : R} (hπ0 : π ≠ 0) {L K : Submodule R V}
    (h : IsometricLat (Q.prod (QJ (F := F) π)) (Q.prod (QJ (F := F) π)) (L.prod latJ) (K.prod latJ)) :
    IsometricLat Q Q L K := by
  have hc : algebraMap R F π ≠ 0 := by simpa using hπ0
  have hci : (algebraMap R F π)⁻¹ ≠ 0 := inv_ne_zero hc
  set P := Q.prod (QJ (F := F) π) with hP
  set Q2 := (algebraMap R F π)⁻¹ • P with hQ2
  obtain ⟨f, hf⟩ := (isometricLat_smul_iff P hci).mpr h
  have hsK : IsOrthSum Q2 (K.prod latJ) ((⊥ : Submodule R V).prod latJ) (K.prod ⊥) :=
    adj_isOrthSum_symm Q2 (isOrthSum_smul P _ (adj_isOrthSum_prod_split Q (QJ π) K latJ))
  have hsL : IsOrthSum Q2 (L.prod latJ) ((⊥ : Submodule R V).prod latJ) (L.prod ⊥) :=
    adj_isOrthSum_symm Q2 (isOrthSum_smul P _ (adj_isOrthSum_prod_split Q (QJ π) L latJ))
  have h2 := isOrthSum_imgLat Q2 Q2 f hf hsL
  have hex : ((0 : V), ((1 : F), (0 : F))) ∈ L.prod (latJ : Submodule R (F × F)) :=
    ⟨zero_mem _, mem_latJ.mpr ⟨1, 0, by simp⟩⟩
  have hey : ((0 : V), ((0 : F), (1 : F))) ∈ L.prod (latJ : Submodule R (F × F)) :=
    ⟨zero_mem _, mem_latJ.mpr ⟨0, 1, by simp⟩⟩
  have hbil0 : bil Q (0 : V) 0 = 0 := by simp [bil]
  have hQx : Q2 ((0 : V), ((1 : F), (0 : F))) = 0 := by simp [hQ2, hP, QJ_apply]
  have hQy : Q2 ((0 : V), ((0 : F), (1 : F))) = 0 := by simp [hQ2, hP, QJ_apply]
  have hxy : bil Q2 ((0 : V), ((1 : F), (0 : F))) ((0 : V), ((0 : F), (1 : F))) = 1 := by
    rw [hQ2, bil_smul_form, hP, adj_bil_prod, hbil0, bil_QJ]
    field_simp
    simp
  have hQx' : Q2 (f ⟨_, hex⟩ : V × (F × F)) = 0 := by rw [hf]; exact hQx
  have hQy' : Q2 (f ⟨_, hey⟩ : V × (F × F)) = 0 := by rw [hf]; exact hQy
  have hxy' : bil Q2 (f ⟨_, hex⟩ : V × (F × F)) (f ⟨_, hey⟩ : V × (F × F)) = 1 := by
    rw [bil_eq_of_isometricLat Q2 Q2 f hf]; exact hxy
  have hcancel : IsometricLat Q2 Q2 (K.prod ⊥) (imgLat f (L.prod ⊥)) :=
    isometricLat_of_cancel_hyperbolic Q2 hsK h2 bot_prod_latJ_eq_span
      (by rw [← imgLat_span_pair f hex hey, ← bot_prod_latJ_eq_span]) hQx hQy hxy hQx' hQy' hxy'
  have hcancelP := (isometricLat_smul_iff P hci).mp hcancel
  have hLP : L.prod (⊥ : Submodule R (F × F)) ≤ L.prod latJ := Submodule.prod_mono le_rfl bot_le
  have himgP := (isometricLat_smul_iff P hci).mp (isometricLat_imgLat Q2 Q2 f hf hLP)
  exact adj_isometricLat_trans Q P Q (adj_isometricLat_prod_bot Q (QJ π) L)
    (adj_isometricLat_trans P P Q (adj_isometricLat_trans P P P himgP (adj_isometricLat_symm P P hcancelP))
      (adj_isometricLat_symm Q P (adj_isometricLat_prod_bot Q (QJ π) K)))

end Cancel

end QuadFormsKB.OMeara.InsertJ
