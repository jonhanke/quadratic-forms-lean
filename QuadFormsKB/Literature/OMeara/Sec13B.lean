/-
# O'Meara §13B–§13C: the invariants $e$ and $f$ (13:4 (2), (3), 13:5 (2), 13:6) and prolongation from a subring

**Setting.** As in `Sec13A.lean`: valuations are Mathlib `AbsoluteValue`s, `integers v hv` and `maximalIdealOf v hv`
are O'Meara's $\mathfrak o(\mathfrak p)$ and $\mathfrak m(\mathfrak p)$. For an extension $E/F$ (`[Algebra F E]`) and
a non-archimedean valuation $w$ of $E$ (the spot $\mathfrak P$), the induced valuation on $F$ is `w.under _`
(`Sec11E.lean`; the spot $\mathfrak p$ with $\mathfrak P \mid \mathfrak p$).

**Defines**
* `absValueGroup v` (§11A, p. 2): the value group $|F| = \{|\alpha| : \alpha \ne 0\}$, a subgroup of $\mathbb R^\times$;
* `residueFieldOf v hv` (§13A, p. 21): the residue class field $\mathfrak o/\mathfrak m$ (a field, since $\mathfrak m$
  is the maximal ideal, `maximalIdealOf_isMaximal`), and `residueMap w hw` the natural embedding
  $F(\mathfrak p) \to E(\mathfrak P)$ obtained by restriction (§13B, p. 23);
* `ramificationIndexAbs w` (§13B, p. 22): $e(\mathfrak P|\mathfrak p) = (|E| : |F|)$;
* `inertiaDegAbs w hw` (§13B, p. 24): $f(\mathfrak P|\mathfrak p) = [E(\mathfrak P) : F(\mathfrak P)]$.
O'Meara allows the value $\infty$ for $e$ and $f$; Mathlib's `Subgroup.relIndex` and `Module.finrank` take the value
$0$ for an infinite index or degree.

**Proves**
* `ramificationIndexAbs_congr`, `inertiaDegAbs_congr` (**13:4 (3)** and the remark after it): $e$ and $f$ do not
  depend on the choice of the valuation in the spot $\mathfrak P$;
* `ramificationIndexAbs_completion` (**13:4 (2)**) and `inertiaDegAbs_completion` (**13:5 (2)**): $e$ and $f$ are
  the same for $E_{\mathfrak P}/F_{\mathfrak P}$, where $F_{\mathfrak P}$ is the closure of $F$ in a completion
  $E_{\mathfrak P}$ of $E$;
* `ramificationIndexAbs_mul_inertiaDegAbs_le` (**13:6**): $e$ and $f$ are finite and $ef \le n = [E:F]$;
* `exists_unique_extend_of_isFractionRing` (§13C, p. 25): a function on a subring $Z$ satisfying the valuation axioms
  prolongs uniquely to a valuation of the quotient field, non-archimedean if the function satisfies the strong
  triangle law.
-/
import QuadFormsKB.Citation
import Mathlib.GroupTheory.Index
import Mathlib.Topology.Algebra.Field
import Mathlib.RingTheory.Localization.FractionRing
import QuadFormsKB.Literature.OMeara.Sec11E
import QuadFormsKB.Literature.OMeara.Sec13A

namespace QuadFormsKB.OMeara

section ValueGroup

variable {F : Type*} [Field F]

/-- The *value group* $|F| = \{|\alpha| : \alpha \in F^\times\}$ of the valuation $v$ (§11A, p. 2), as a subgroup of
the multiplicative group $\mathbb R^\times$ (it lies in the positive reals). -/
@[kb "omeara1963" "§11A, p. 2 (the value group |F| of a valuation)"]
def absValueGroup (v : AbsoluteValue F ℝ) : Subgroup ℝˣ where
  carrier := {u | ∃ x : F, x ≠ 0 ∧ v x = (u : ℝ)}
  one_mem' := ⟨1, one_ne_zero, by simp⟩
  mul_mem' := by
    rintro a b ⟨x, hx, hxa⟩ ⟨y, hy, hyb⟩
    exact ⟨x * y, mul_ne_zero hx hy, by simp [hxa, hyb]⟩
  inv_mem' := by
    rintro a ⟨x, hx, hxa⟩
    exact ⟨x⁻¹, inv_ne_zero hx, by simp [hxa]⟩

/-- Membership in the value group. -/
theorem mem_absValueGroup (v : AbsoluteValue F ℝ) (u : ℝˣ) :
    u ∈ absValueGroup v ↔ ∃ x : F, x ≠ 0 ∧ v x = (u : ℝ) := Iff.rfl

variable (v : AbsoluteValue F ℝ) (hv : IsNonarchimedean v)

/-- The maximal ideal $\mathfrak m(\mathfrak p)$ is a maximal ideal of $\mathfrak o(\mathfrak p)$ (§13A, p. 21: "the
absolutely largest proper ideal"). -/
@[kb "omeara1963" "§13A, p. 21 (m(p) is the largest proper ideal of o(p))"]
theorem maximalIdealOf_isMaximal : (maximalIdealOf v hv).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨?_, ?_⟩
  · show ¬ v ((1 : integers v hv) : F) < 1
    simp
  · intro J b hIJ hbI hbJ
    have hb1 : v (b : F) ≤ 1 := b.2
    have hb2 : ¬ v (b : F) < 1 := hbI
    have hbeq : v (b : F) = 1 := le_antisymm hb1 (not_lt.1 hb2)
    have hb0 : (b : F) ≠ 0 := by
      intro h; rw [h] at hbeq; simp at hbeq
    have hinv : (b : F)⁻¹ ∈ integers v hv := by
      show v ((b : F)⁻¹) ≤ 1
      simp [hbeq]
    have : (1 : integers v hv) = ⟨(b : F)⁻¹, hinv⟩ * b := by
      apply Subtype.ext
      simp [hb0]
    rw [this]
    exact J.mul_mem_left _ hbJ

instance : (maximalIdealOf v hv).IsMaximal := maximalIdealOf_isMaximal v hv

/-- The residue class field $\mathfrak o(\mathfrak p)/\mathfrak m(\mathfrak p)$ of $F$ at $v$ (§13A, p. 21; by
`IsResidueClassField` any other residue class field is isomorphic to it). -/
abbrev residueFieldOf : Type _ := integers v hv ⧸ maximalIdealOf v hv

noncomputable instance : Field (residueFieldOf v hv) := Ideal.Quotient.field _

/-- The quotient map makes `residueFieldOf v hv` a residue class field in O'Meara's sense. -/
theorem isResidueClassField_residueFieldOf :
    IsResidueClassField v hv (residueFieldOf v hv) (Ideal.Quotient.mk _) :=
  ⟨Ideal.Quotient.mk_surjective, Ideal.mk_ker⟩

end ValueGroup

section Extension

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- The valuation induced on $F$ by a non-archimedean valuation of $E$ is non-archimedean. -/
theorem isNonarchimedean_under {w : AbsoluteValue E ℝ} (hw : IsNonarchimedean w) :
    IsNonarchimedean (w.under F) := fun a b => by
  simpa [under_apply_eq] using hw (algebraMap F E a) (algebraMap F E b)

/-- The natural map $\mathfrak o(\mathfrak p) \to \mathfrak o(\mathfrak P)$ of the integers of $F$ into those of $E$
($\mathfrak o(\mathfrak P) \cap F = \mathfrak o(\mathfrak p)$, §13B, p. 22). -/
def integersRestrictMap (w : AbsoluteValue E ℝ) (hw : IsNonarchimedean w) :
    integers (w.under F) (isNonarchimedean_under hw) →+* integers w hw where
  toFun a := ⟨algebraMap F E a, a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

/-- The natural embedding of the residue class field of $F$ at $\mathfrak p$ into that of $E$ at $\mathfrak P$,
induced by restriction ("natural restriction", §13B, p. 23). -/
@[kb "omeara1963" "§13B, p. 23 (residue class field of F at p obtained by natural restriction)"]
noncomputable def residueMap (w : AbsoluteValue E ℝ) (hw : IsNonarchimedean w) :
    residueFieldOf (w.under F) (isNonarchimedean_under hw) →+* residueFieldOf w hw :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (integersRestrictMap w hw)) (by
    intro a ha
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact ha)

/-- The image of the residue class $\bar\alpha$ of $\alpha \in \mathfrak o(\mathfrak p)$ is the residue class of
$\alpha$ in $E(\mathfrak P)$. -/
theorem residueMap_mk (w : AbsoluteValue E ℝ) (hw : IsNonarchimedean w)
    (a : integers (w.under F) (isNonarchimedean_under hw)) :
    residueMap w hw (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (integersRestrictMap w hw a) :=
  rfl

/-- The *ramification index* $e(\mathfrak P|\mathfrak p) = (|E|_{\mathfrak P} : |F|_{\mathfrak P})$ of $E/F$ at the
valuation $w$ of $E$ (§13B, p. 22): the index of the value group of the induced valuation of $F$ in that of $w$.
(It is $0$ when O'Meara's index is $\infty$.) -/
@[kb "omeara1963" "§13B, p. 22 (ramification index e(P|p))"]
noncomputable def ramificationIndexAbs (w : AbsoluteValue E ℝ) : ℕ :=
  (absValueGroup (w.under F)).relIndex (absValueGroup w)

/-- The *degree of inertia* $f(\mathfrak P|\mathfrak p) = [E(\mathfrak P) : F(\mathfrak P)]$ of $E/F$ at the
non-archimedean valuation $w$ (§13B, p. 24): the degree of the residue class field of $E$ over that of $F$, embedded
by natural restriction (`residueMap`). (It is $0$ when O'Meara's degree is $\infty$.) -/
@[kb "omeara1963" "§13B, p. 24 (degree of inertia f(P|p))"]
noncomputable def inertiaDegAbs (w : AbsoluteValue E ℝ) (hw : IsNonarchimedean w) : ℕ :=
  @Module.finrank (residueFieldOf (w.under F) (isNonarchimedean_under hw)) (residueFieldOf w hw) _ _
    (residueMap w hw).toAlgebra.toModule


section RpowGroup

/-- The group homomorphism $u \mapsto |u|^c$ of $\mathbb R^\times$ (injective on the positive units for $c \ne 0$). -/
noncomputable def rpowUnitHom (c : ℝ) : ℝˣ →* ℝˣ where
  toFun u := Units.mk0 (|(u : ℝ)| ^ c) (Real.rpow_pos_of_pos (abs_pos.2 u.ne_zero) c).ne'
  map_one' := Units.ext (by simp)
  map_mul' a b := Units.ext (by
    simp [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)])

theorem rpowUnitHom_val (c : ℝ) (u : ℝˣ) : ((rpowUnitHom c u : ℝˣ) : ℝ) = |(u : ℝ)| ^ c := rfl

theorem rpowUnitHom_injOn {c : ℝ} (hc : c ≠ 0) :
    Function.Injective ((rpowUnitHom c).comp (Units.posSubgroup ℝ).subtype) := by
  intro a b hab
  have h : |((a : ℝˣ) : ℝ)| ^ c = |((b : ℝˣ) : ℝ)| ^ c := by
    have := congrArg (fun u : ℝˣ => (u : ℝ)) hab
    simpa [rpowUnitHom_val] using this
  have h2 := congrArg (fun t : ℝ => t ^ c⁻¹) h
  simp only [Real.rpow_rpow_inv (abs_nonneg _) hc] at h2
  have ha : (0 : ℝ) < ((a : ℝˣ) : ℝ) := a.2
  have hb : (0 : ℝ) < ((b : ℝˣ) : ℝ) := b.2
  rw [abs_of_pos ha, abs_of_pos hb] at h2
  exact Subtype.ext (Units.ext h2)

theorem relIndex_map_rpowUnitHom {c : ℝ} (hc : c ≠ 0) (H K : Subgroup ℝˣ)
    (hH : H ≤ Units.posSubgroup ℝ) (hK : K ≤ Units.posSubgroup ℝ) :
    (H.map (rpowUnitHom c)).relIndex (K.map (rpowUnitHom c)) = H.relIndex K := by
  have e : ∀ A : Subgroup ℝˣ, A ≤ Units.posSubgroup ℝ →
      A.map (rpowUnitHom c) =
        (A.subgroupOf (Units.posSubgroup ℝ)).map ((rpowUnitHom c).comp (Units.posSubgroup ℝ).subtype) := by
    intro A hA
    rw [← Subgroup.map_map, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hA]
  rw [e H hH, e K hK, Subgroup.relIndex_map_map_of_injective _ _ (rpowUnitHom_injOn hc),
    Subgroup.relIndex_subgroupOf hK]

theorem absValueGroup_le_pos {F : Type*} [Field F] (v : AbsoluteValue F ℝ) :
    absValueGroup v ≤ Units.posSubgroup ℝ := by
  rintro u ⟨x, hx, hxu⟩
  show (0 : ℝ) < u
  rw [← hxu]; exact v.pos hx

theorem absValueGroup_rpow {F : Type*} [Field F] (v v' : AbsoluteValue F ℝ) {c : ℝ}
    (h : ∀ x, v' x = v x ^ c) :
    absValueGroup v' = (absValueGroup v).map (rpowUnitHom c) := by
  ext u
  constructor
  · rintro ⟨x, hx, hxu⟩
    refine ⟨Units.mk0 (v x) (v.pos hx).ne', ⟨x, hx, rfl⟩, ?_⟩
    apply Units.ext
    rw [rpowUnitHom_val, ← hxu, h]
    simp [abs_of_nonneg (v.nonneg x)]
  · rintro ⟨u0, ⟨x, hx, hxu⟩, rfl⟩
    refine ⟨x, hx, ?_⟩
    rw [rpowUnitHom_val, h, hxu]
    simp [← hxu, abs_of_nonneg (v.nonneg x)]

end RpowGroup

section ResidueEquiv

variable {K L : Type*} [Field K] [Field L]

/-- Compatibility of a ring homomorphism $\rho\colon K \to L$ of valued fields with integers, maximal ideals and
residue classes (used to compare residue class fields). -/
structure ResidueData (v : AbsoluteValue K ℝ) (u : AbsoluteValue L ℝ) (ρ : K →+* L) : Prop where
  le : ∀ x, v x ≤ 1 ↔ u (ρ x) ≤ 1
  lt : ∀ x, v x < 1 ↔ u (ρ x) < 1
  dense : ∀ y, u y ≤ 1 → ∃ x, v x ≤ 1 ∧ u (y - ρ x) < 1

variable {v : AbsoluteValue K ℝ} {u : AbsoluteValue L ℝ} {ρ : K →+* L}

/-- The map of integers induced by $\rho$. -/
def ResidueData.intMap (hd : ResidueData v u ρ) (hv : IsNonarchimedean v) (hu : IsNonarchimedean u) :
    integers v hv →+* integers u hu where
  toFun a := ⟨ρ a, (hd.le a).1 a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

/-- The induced map of residue class fields. -/
noncomputable def ResidueData.resMap (hd : ResidueData v u ρ) (hv : IsNonarchimedean v)
    (hu : IsNonarchimedean u) : residueFieldOf v hv →+* residueFieldOf u hu :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (hd.intMap hv hu)) (by
    intro a ha
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact (hd.lt a).1 ha)

theorem ResidueData.resMap_bijective (hd : ResidueData v u ρ) (hv : IsNonarchimedean v)
    (hu : IsNonarchimedean u) : Function.Bijective (hd.resMap hv hu) := by
  refine ⟨RingHom.injective _, fun y => ?_⟩
  obtain ⟨y', rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨x, hx1, hx2⟩ := hd.dense y' y'.2
  refine ⟨Ideal.Quotient.mk _ ⟨x, hx1⟩, ?_⟩
  show Ideal.Quotient.mk _ (hd.intMap hv hu ⟨x, hx1⟩) = Ideal.Quotient.mk _ y'
  rw [Ideal.Quotient.eq]
  show u (ρ x - (y' : L)) < 1
  rw [AbsoluteValue.map_sub]
  exact hx2

/-- The induced isomorphism of residue class fields. -/
noncomputable def ResidueData.resEquiv (hd : ResidueData v u ρ) (hv : IsNonarchimedean v)
    (hu : IsNonarchimedean u) : residueFieldOf v hv ≃+* residueFieldOf u hu :=
  RingEquiv.ofBijective _ (hd.resMap_bijective hv hu)

theorem ResidueData.resEquiv_mk (hd : ResidueData v u ρ) (hv : IsNonarchimedean v)
    (hu : IsNonarchimedean u) (a : integers v hv) :
    hd.resEquiv hv hu (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (hd.intMap hv hu a) := rfl

end ResidueEquiv

/-- Degrees of inertia agree when the two extensions are related by compatible isomorphic residue data. -/
theorem inertiaDegAbs_eq_of {F E F' E' : Type*} [Field F] [Field E] [Algebra F E] [Field F'] [Field E']
    [Algebra F' E'] (w : AbsoluteValue E ℝ) (hw : IsNonarchimedean w) (w' : AbsoluteValue E' ℝ)
    (hw' : IsNonarchimedean w') (ρF : F →+* F') (ρE : E →+* E')
    (hcomm : ∀ a, ρE (algebraMap F E a) = algebraMap F' E' (ρF a))
    (hE : ResidueData w w' ρE)
    (hF : ResidueData (w.under F) (w'.under F') ρF) :
    inertiaDegAbs (F := F) w hw = inertiaDegAbs (F := F') w' hw' := by
  unfold inertiaDegAbs
  let _ := (residueMap (F := F) w hw).toAlgebra
  let _ := (residueMap (F := F') w' hw').toAlgebra
  refine Algebra.finrank_eq_of_equiv_equiv (hF.resEquiv _ _) (hE.resEquiv hw hw') ?_
  apply Ideal.Quotient.ringHom_ext
  ext a
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingHom.algebraMap_toAlgebra, hF.resEquiv_mk, hE.resEquiv_mk, residueMap_mk]
  congr 1
  apply Subtype.ext
  exact (hcomm a).symm

theorem ResidueData.of_isEquiv {K : Type*} [Field K] {w w' : AbsoluteValue K ℝ} (h : w.IsEquiv w') :
    ResidueData w w' (RingHom.id K) := by
  refine ⟨fun x => ?_, fun x => ?_, fun y hy => ⟨y, ?_, ?_⟩⟩
  · simpa using h x 1
  · have := h 1 x
    simp only [map_one] at this
    simpa [not_le] using this.not
  · simpa using (h y 1).2 (by simpa using hy)
  · simp


section Ineq

/-- The residue class field extension `residueMap` as an algebra structure. -/
noncomputable abbrev residueAlgebra {F E : Type*} [Field F] [Field E] [Algebra F E]
    (w : AbsoluteValue E ℝ) (hw : IsNonarchimedean w) :
    Algebra (residueFieldOf (w.under F) (isNonarchimedean_under hw))
      (residueFieldOf w hw) :=
  (residueMap w hw).toAlgebra

variable {E : Type*} [Field E] {w : AbsoluteValue E ℝ}

theorem sum_le_of_nonarch (hw : IsNonarchimedean w) {κ : Type*} (s : Finset κ) (t : κ → E)
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ k ∈ s, w (t k) ≤ C) : w (∑ k ∈ s, t k) ≤ C := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hC
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hw _ _).trans (max_le (h a (by simp)) (ih fun k hk => h k (by simp [hk])))

theorem sum_lt_of_nonarch (hw : IsNonarchimedean w) {κ : Type*} (s : Finset κ) (t : κ → E)
    {C : ℝ} (hC : 0 < C) (h : ∀ k ∈ s, w (t k) < C) : w (∑ k ∈ s, t k) < C := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hC
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hw _ _).trans_lt (max_lt (h a (by simp)) (ih fun k hk => h k (by simp [hk])))

/-- A sum of elements with pairwise distinct non-zero values is non-zero (if some term is non-zero). -/
theorem sum_ne_zero_of_distinct (hw : IsNonarchimedean w) {κ : Type*} [Fintype κ] (t : κ → E)
    (hne : ∃ j, t j ≠ 0)
    (hd : ∀ j k, j ≠ k → t j ≠ 0 → t k ≠ 0 → w (t j) ≠ w (t k)) : ∑ j, t j ≠ 0 := by
  classical
  obtain ⟨j0, hj0, hmax⟩ := Finset.exists_max_image (Finset.univ.filter (fun j => t j ≠ 0))
    (fun j => w (t j)) (by obtain ⟨j, hj⟩ := hne; exact ⟨j, by simp [hj]⟩)
  have hj0' : t j0 ≠ 0 := by simpa using hj0
  have hpos : 0 < w (t j0) := w.pos hj0'
  have hrest : w (∑ k ∈ Finset.univ.erase j0, t k) < w (t j0) := by
    apply sum_lt_of_nonarch hw _ _ hpos
    intro k hk
    by_cases htk : t k = 0
    · simpa [htk] using hpos
    · have hkj : k ≠ j0 := Finset.ne_of_mem_erase hk
      have hle := hmax k (by simp [htk])
      exact lt_of_le_of_ne hle (hd k j0 hkj htk hj0')
  intro hsum
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j0)] at hsum
  have h1 : t j0 = -(∑ k ∈ Finset.univ.erase j0, t k) := eq_neg_of_add_eq_zero_left hsum
  have h2 : w (t j0) = w (∑ k ∈ Finset.univ.erase j0, t k) := by
    rw [h1, AbsoluteValue.map_neg]
  linarith

variable {F : Type*} [Field F] [Algebra F E]

/-- Principle of domination for sums `∑ bᵢ ωᵢ` with independent residues. -/
theorem sum_dominated (hw : IsNonarchimedean w) {ι : Type*} [Fintype ι] (ω : ι → E)
    (hω1 : ∀ i, w (ω i) ≤ 1)
    (hω : ∀ b : ι → F, (∀ i, w (algebraMap F E (b i)) ≤ 1) →
      w (∑ i, algebraMap F E (b i) * ω i) < 1 → ∀ i, w (algebraMap F E (b i)) < 1)
    (b : ι → F) (hb : ∃ i, b i ≠ 0) :
    ∃ i0, b i0 ≠ 0 ∧ w (∑ i, algebraMap F E (b i) * ω i) = w (algebraMap F E (b i0)) := by
  classical
  obtain ⟨i1, hi1⟩ := hb
  obtain ⟨i0, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun i => w (algebraMap F E (b i))) ⟨i1, Finset.mem_univ _⟩
  have hmax' : ∀ i, w (algebraMap F E (b i)) ≤ w (algebraMap F E (b i0)) :=
    fun i => hmax i (Finset.mem_univ _)
  have hb0 : b i0 ≠ 0 := by
    intro h0
    have : w (algebraMap F E (b i1)) ≤ 0 := by simpa [h0] using hmax' i1
    exact hi1 (by simpa using this)
  have ha0 : algebraMap F E (b i0) ≠ 0 := by simpa using hb0
  have hwpos : 0 < w (algebraMap F E (b i0)) := w.pos ha0
  refine ⟨i0, hb0, ?_⟩
  set S := ∑ i, algebraMap F E (b i) * ω i with hS
  set c : ι → F := fun i => b i / b i0 with hc
  have hcv : ∀ i, w (algebraMap F E (c i)) = w (algebraMap F E (b i)) / w (algebraMap F E (b i0)) := by
    intro i
    simp [hc, map_div₀]
  have hcle : ∀ i, w (algebraMap F E (c i)) ≤ 1 := by
    intro i
    rw [hcv, div_le_one hwpos]
    exact hmax' i
  have hsum : ∑ i, algebraMap F E (c i) * ω i = S / algebraMap F E (b i0) := by
    rw [hS, div_eq_mul_inv, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hc, map_div₀]
    field_simp
  have hle : w (S / algebraMap F E (b i0)) ≤ 1 := by
    rw [← hsum]
    apply sum_le_of_nonarch hw _ _ zero_le_one
    intro i _
    rw [map_mul]
    calc w (algebraMap F E (c i)) * w (ω i) ≤ 1 * 1 :=
          mul_le_mul (hcle i) (hω1 i) (w.nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hle2 : w S ≤ w (algebraMap F E (b i0)) := by
    rw [map_div₀, div_le_one hwpos] at hle
    exact hle
  refine le_antisymm hle2 ?_
  by_contra hlt
  push Not at hlt
  have h1 : w (∑ i, algebraMap F E (c i) * ω i) < 1 := by
    rw [hsum, map_div₀, div_lt_one hwpos]
    exact hlt
  have h2 := hω c hcle h1 i0
  rw [hcv, div_self hwpos.ne'] at h2
  exact lt_irrefl _ h2

/-- Independence of the products `ωᵢ xⱼ` (the heart of 13:6). -/
theorem linearIndependent_mul_of_residues (hw : IsNonarchimedean w) {ι κ : Type*} [Fintype ι]
    [Fintype κ] (ω : ι → E) (hω1 : ∀ i, w (ω i) ≤ 1)
    (hω : ∀ b : ι → F, (∀ i, w (algebraMap F E (b i)) ≤ 1) →
      w (∑ i, algebraMap F E (b i) * ω i) < 1 → ∀ i, w (algebraMap F E (b i)) < 1)
    (x : κ → E) (hx0 : ∀ j, x j ≠ 0)
    (hxd : ∀ j k, j ≠ k → ∀ y : F, y ≠ 0 → w (x j) ≠ w (algebraMap F E y) * w (x k)) :
    LinearIndependent F (fun p : ι × κ => ω p.1 * x p.2) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hcon
  push Not at hcon
  obtain ⟨p0, hp0⟩ := hcon
  set t : κ → E := fun j => (∑ i, algebraMap F E (g (i, j)) * ω i) * x j with ht
  have hsum : ∑ j, t j = 0 := by
    rw [← hg, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [ht]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Algebra.smul_def, mul_assoc]
  have hzero : ∀ j, (∀ i, g (i, j) = 0) → t j = 0 := by
    intro j hj
    simp [ht, hj]
  have hkey : ∀ j, (∃ i, g (i, j) ≠ 0) → ∃ a : F, a ≠ 0 ∧ t j ≠ 0 ∧
      w (t j) = w (algebraMap F E a) * w (x j) := by
    intro j hj
    obtain ⟨i0, hi0, hv⟩ := sum_dominated hw ω hω1 hω (fun i => g (i, j)) hj
    refine ⟨g (i0, j), hi0, ?_, ?_⟩
    · intro h0
      have : w (t j) = 0 := by rw [h0]; simp
      rw [ht] at this
      simp only [map_mul, hv] at this
      have h1 : 0 < w (algebraMap F E (g (i0, j))) := w.pos (by simpa using hi0)
      have h2 : 0 < w (x j) := w.pos (hx0 j)
      nlinarith
    · simp only [ht, map_mul, hv]
  have hne : ∃ j, t j ≠ 0 := by
    have hj : ∃ i, g (i, p0.2) ≠ 0 := ⟨p0.1, hp0⟩
    obtain ⟨a, -, h, -⟩ := hkey p0.2 hj
    exact ⟨p0.2, h⟩
  have hcase : ∀ j, t j ≠ 0 → ∃ a : F, a ≠ 0 ∧ w (t j) = w (algebraMap F E a) * w (x j) := by
    intro j hj
    by_cases h : ∃ i, g (i, j) ≠ 0
    · obtain ⟨a, ha, -, h2⟩ := hkey j h
      exact ⟨a, ha, h2⟩
    · push Not at h
      exact absurd (hzero j h) hj
  refine sum_ne_zero_of_distinct hw t hne ?_ hsum
  intro j k hjk htj htk heq
  obtain ⟨a, ha, h1⟩ := hcase j htj
  obtain ⟨a', ha', h2⟩ := hcase k htk
  have hwa : 0 < w (algebraMap F E a) := w.pos (by simpa using ha)
  have hwa' : 0 < w (algebraMap F E a') := w.pos (by simpa using ha')
  apply hxd j k hjk (a' / a) (div_ne_zero ha' ha)
  rw [h1, h2] at heq
  rw [map_div₀, map_div₀]
  field_simp
  linarith

end Ineq

/-- **13:4 (3).** The ramification index does not depend on the choice of the valuation in the spot: equivalent
valuations $w$, $w'$ of $E$ give the same index (O'Meara: $(G : H) = (G^{\varrho} : H^{\varrho})$). -/
@[kb "omeara1963" "§13B, 13:4 (3), p. 22"]
theorem ramificationIndexAbs_congr {w w' : AbsoluteValue E ℝ} (h : w.IsEquiv w') :
    ramificationIndexAbs (F := F) w = ramificationIndexAbs (F := F) w' := by
  obtain ⟨c, hc, hcw⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 h
  have h1 : ∀ x, w' x = w x ^ c := fun x => (congrFun hcw x).symm
  unfold ramificationIndexAbs
  rw [absValueGroup_rpow w w' h1, absValueGroup_rpow (w.under F) (w'.under _)
    (fun x => h1 _)]
  exact (relIndex_map_rpowUnitHom hc.ne' _ _ (absValueGroup_le_pos _) (absValueGroup_le_pos _)).symm

/-- The degree of inertia does not depend on the choice of the valuation in the spot (§13B, p. 24): equivalent
valuations have the same integers and maximal ideals. -/
@[kb "omeara1963" "§13B, p. 24 (f(P|p) is independent of the valuation in P)"]
theorem inertiaDegAbs_congr {w w' : AbsoluteValue E ℝ} (hw : IsNonarchimedean w)
    (hw' : IsNonarchimedean w') (h : w.IsEquiv w') :
    inertiaDegAbs (F := F) w hw = inertiaDegAbs (F := F) w' hw' :=
  inertiaDegAbs_eq_of w hw w' hw' (RingHom.id F) (RingHom.id E) (fun _ => rfl)
    (ResidueData.of_isEquiv h) (ResidueData.of_isEquiv (under_isEquiv h))


section CompletionHelpers

variable {Ê : Type*} [NormedField Ê]

/-- Principle of domination in a non-archimedean normed field. -/
theorem norm_eq_of_norm_sub_lt (hna : IsNonarchimedean (norm : Ê → ℝ)) {y b : Ê}
    (h : ‖y - b‖ < ‖y‖) : ‖b‖ = ‖y‖ := by
  have hlt : ‖b - y‖ < ‖y‖ := by rwa [norm_sub_rev]
  have := hna.add_eq_left_of_lt (f := (norm : Ê → ℝ)) (fun x => norm_neg x) (a := b - y)
    (b := y) hlt
  simpa using this

theorem norm_le_one_of_norm_sub_lt (hna : IsNonarchimedean (norm : Ê → ℝ)) {y b : Ê}
    (hy : ‖y‖ ≤ 1) (h : ‖y - b‖ < 1) : ‖b‖ ≤ 1 := by
  have h1 := hna y (b - y)
  have h2 : ‖b - y‖ < 1 := by rwa [norm_sub_rev]
  calc ‖b‖ = ‖y + (b - y)‖ := by simp
    _ ≤ max ‖y‖ ‖b - y‖ := h1
    _ ≤ 1 := max_le hy h2.le

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

theorem absValueGroup_norm_completion (w : AbsoluteValue E ℝ) (hw : IsNonarchimedean w)
    {ι : E →+* Ê} (hc : IsCompletion w Ê ι) :
    absValueGroup (NormedField.toAbsoluteValue Ê) = absValueGroup w := by
  ext u
  constructor
  · rintro ⟨y, hy, hyu⟩
    obtain ⟨x, hx, hxy⟩ := valueGroup_completion w hw hc hy
    exact ⟨x, hx, by rw [hxy]; exact hyu⟩
  · rintro ⟨x, hx, hxu⟩
    exact ⟨ι x, (map_ne_zero ι).2 hx, by
      show ‖ι x‖ = _
      rw [hc.norm_eq]; exact hxu⟩

theorem absValueGroup_closure_completion (w : AbsoluteValue E ℝ) (hw : IsNonarchimedean w)
    {ι : E →+* Ê} (hc : IsCompletion w Ê ι) :
    absValueGroup ((NormedField.toAbsoluteValue Ê).under
        ((ι.comp (algebraMap F E)).fieldRange.topologicalClosure)) = absValueGroup (w.under F) := by
  have hna : IsNonarchimedean (norm : Ê → ℝ) := hc.isNonarchimedean_of w hw
  ext u
  constructor
  · rintro ⟨y, hy, hyu⟩
    have hy0 : (y : Ê) ≠ 0 := fun h => hy (Subtype.ext h)
    have hypos : 0 < ‖(y : Ê)‖ := norm_pos_iff.2 hy0
    have hmem : (y : Ê) ∈ closure ((ι.comp (algebraMap F E)).fieldRange : Set Ê) := y.2
    obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.1 hmem ‖(y : Ê)‖ hypos
    rw [dist_eq_norm] at hdist
    obtain ⟨x, rfl⟩ := hb
    have hbn := norm_eq_of_norm_sub_lt hna hdist
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hbn
      exact hypos.ne' hbn.symm
    refine ⟨x, hx0, ?_⟩
    rw [← hyu]
    show w (algebraMap F E x) = ‖(y : Ê)‖
    rw [← hc.norm_eq]
    exact hbn
  · rintro ⟨x, hx, hxu⟩
    refine ⟨⟨ι (algebraMap F E x), Subfield.le_topologicalClosure _ ⟨x, rfl⟩⟩, ?_, ?_⟩
    · intro h
      have : ι (algebraMap F E x) = 0 := congrArg Subtype.val h
      exact hx ((map_eq_zero_iff _ (RingHom.injective _)).1 ((map_eq_zero_iff _ (RingHom.injective _)).1 this))
    · rw [← hxu]
      show ‖ι (algebraMap F E x)‖ = w (algebraMap F E x)
      exact hc.norm_eq _

end CompletionHelpers

/-- **13:4 (2).** Let $E_{\mathfrak P}$ be a completion of $E$ at the non-archimedean valuation $w$ (`IsCompletion`)
and $F_{\mathfrak P}$ the closure of $F$ in $E_{\mathfrak P}$. Then the ramification index of
$E_{\mathfrak P}/F_{\mathfrak P}$ (for the norm of $E_{\mathfrak P}$) equals $e(\mathfrak P|\mathfrak p)$ for $E/F$:
$(|E_{\mathfrak P}| : |F_{\mathfrak P}|) = (|E| : |F|)$. -/
@[kb "omeara1963" "§13B, 13:4 (2), p. 22"]
theorem ramificationIndexAbs_completion (w : AbsoluteValue E ℝ) (hw : IsNonarchimedean w)
    {Ê : Type*} [NormedField Ê] {ι : E →+* Ê} (hc : IsCompletion w Ê ι) :
    ramificationIndexAbs (F := ((ι.comp (algebraMap F E)).fieldRange.topologicalClosure))
        (NormedField.toAbsoluteValue Ê) =
      ramificationIndexAbs (F := F) w := by
  unfold ramificationIndexAbs
  rw [absValueGroup_norm_completion w hw hc, absValueGroup_closure_completion w hw hc]

/-- **13:5 (2).** In the situation of 13:4 (2), the degree of inertia of $E_{\mathfrak P}/F_{\mathfrak P}$ equals
$f(\mathfrak P|\mathfrak p)$ for $E/F$: $[E_{\mathfrak P}(\mathfrak P) : F_{\mathfrak P}(\mathfrak P)] =
[E(\mathfrak P) : F(\mathfrak P)]$. -/
@[kb "omeara1963" "§13B, 13:5 (2), p. 23"]
theorem inertiaDegAbs_completion (w : AbsoluteValue E ℝ) (hw : IsNonarchimedean w)
    {Ê : Type*} [NormedField Ê] {ι : E →+* Ê} (hc : IsCompletion w Ê ι) :
    inertiaDegAbs (F := ((ι.comp (algebraMap F E)).fieldRange.topologicalClosure))
        (NormedField.toAbsoluteValue Ê) (hc.isNonarchimedean_of w hw) =
      inertiaDegAbs (F := F) w hw := by
  have hna : IsNonarchimedean (norm : Ê → ℝ) := hc.isNonarchimedean_of w hw
  let ρF : F →+* ((ι.comp (algebraMap F E)).fieldRange.topologicalClosure) :=
    (ι.comp (algebraMap F E)).codRestrict _ (fun x => Subfield.le_topologicalClosure _ ⟨x, rfl⟩)
  have hρF : ∀ x, (NormedField.toAbsoluteValue Ê).under
      ((ι.comp (algebraMap F E)).fieldRange.topologicalClosure) (ρF x) = w.under F x := by
    intro x
    show ‖ι (algebraMap F E x)‖ = w (algebraMap F E x)
    exact hc.norm_eq _
  refine (inertiaDegAbs_eq_of w hw (NormedField.toAbsoluteValue Ê) (hc.isNonarchimedean_of w hw)
    ρF ι (fun a => rfl) ?_ ?_).symm
  · refine ⟨fun x => ?_, fun x => ?_, fun y hy => ?_⟩
    · show _ ↔ ‖ι x‖ ≤ 1
      rw [hc.norm_eq]
    · show _ ↔ ‖ι x‖ < 1
      rw [hc.norm_eq]
    · obtain ⟨x, hx⟩ := Metric.denseRange_iff.1 hc.dense y 1 one_pos
      rw [dist_eq_norm] at hx
      have hy' : ‖y‖ ≤ 1 := hy
      refine ⟨x, ?_, hx⟩
      rw [← hc.norm_eq]
      exact norm_le_one_of_norm_sub_lt hna hy' hx
  · refine ⟨fun x => ?_, fun x => ?_, fun y hy => ?_⟩
    · rw [hρF]
    · rw [hρF]
    · have hmem : (y : Ê) ∈ closure ((ι.comp (algebraMap F E)).fieldRange : Set Ê) := y.2
      obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.1 hmem 1 one_pos
      rw [dist_eq_norm] at hdist
      obtain ⟨x, rfl⟩ := hb
      refine ⟨x, ?_, ?_⟩
      · rw [← hρF]
        have hy' : ‖(y : Ê)‖ ≤ 1 := hy
        exact norm_le_one_of_norm_sub_lt hna hy' hdist
      · exact hdist


/-- Independent residues give the elementary independence condition used in `linearIndependent_mul_of_residues`. -/
theorem elem_of_linearIndependent {F E : Type*} [Field F] [Field E] [Algebra F E]
    (w : AbsoluteValue E ℝ) (hw : IsNonarchimedean w) {ι : Type*} [Fintype ι]
    (ω : ι → integers w hw)
    (h : @LinearIndependent ι (residueFieldOf (w.under F) (isNonarchimedean_under hw))
      (residueFieldOf w hw) (fun i => Ideal.Quotient.mk (maximalIdealOf w hw) (ω i)) _ _
      (residueAlgebra (F := F) w hw).toModule)
    (b : ι → F) (hb1 : ∀ i, w (algebraMap F E (b i)) ≤ 1)
    (hb2 : w (∑ i, algebraMap F E (b i) * (ω i : E)) < 1) : ∀ i, w (algebraMap F E (b i)) < 1 := by
  let _ := residueAlgebra (F := F) w hw
  rw [Fintype.linearIndependent_iff] at h
  have key := h (fun i => Ideal.Quotient.mk (maximalIdealOf (w.under F) (isNonarchimedean_under hw))
    (⟨b i, hb1 i⟩ : integers (w.under F) (isNonarchimedean_under hw))) ?_
  · intro i
    have := key i
    rw [Ideal.Quotient.eq_zero_iff_mem] at this
    exact this
  · have e : ∀ i, (Ideal.Quotient.mk (maximalIdealOf (w.under F) (isNonarchimedean_under hw))
        (⟨b i, hb1 i⟩ : integers (w.under F) (isNonarchimedean_under hw))) •
          Ideal.Quotient.mk (maximalIdealOf w hw) (ω i) =
        Ideal.Quotient.mk (maximalIdealOf w hw) (integersRestrictMap w hw ⟨b i, hb1 i⟩ * ω i) := by
      intro i
      rw [Algebra.smul_def]
      show residueMap w hw _ * _ = _
      rw [residueMap_mk, map_mul]
    simp_rw [e]
    rw [← map_sum, Ideal.Quotient.eq_zero_iff_mem]
    show w ((∑ i, integersRestrictMap w hw ⟨b i, hb1 i⟩ * ω i : integers w hw) : E) < 1
    simpa [integersRestrictMap] using hb2

/-- Elements of `E` whose values represent given distinct cosets of `|E|` modulo `|F|`. -/
theorem exists_coset_reps {F E : Type*} [Field F] [Field E] [Algebra F E] (w : AbsoluteValue E ℝ)
    {κ : Type*}
    (q : κ → (absValueGroup w) ⧸ (absValueGroup (w.under F)).subgroupOf (absValueGroup w))
    (hq : Function.Injective q) :
    ∃ x : κ → E, (∀ j, x j ≠ 0) ∧
      ∀ j k, j ≠ k → ∀ y : F, y ≠ 0 → w (x j) ≠ w (algebraMap F E y) * w (x k) := by
  classical
  have hrep : ∀ j, ∃ x : E, x ≠ 0 ∧ w x = ((((q j).out : absValueGroup w) : ℝˣ) : ℝ) :=
    fun j => ((q j).out).2
  choose x hx0 hxv using hrep
  refine ⟨x, hx0, fun j k hjk y hy heq => hjk (hq ?_)⟩
  rw [← QuotientGroup.out_eq' (q j), ← QuotientGroup.out_eq' (q k), QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  refine ⟨y⁻¹, inv_ne_zero hy, ?_⟩
  have hk : ((((q k).out : absValueGroup w) : ℝˣ) : ℝ) ≠ 0 := Units.ne_zero _
  have hy' : w (algebraMap F E y) ≠ 0 := (w.pos (by simpa using hy)).ne'
  rw [hxv j, hxv k] at heq
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  rw [under_apply_eq, map_inv₀, map_inv₀, heq]
  field_simp

/-- **13:6.** Let $E/F$ be a finite extension of degree $n$ and $w$ a non-archimedean valuation of $E$. Then the
ramification index $e$ and the degree of inertia $f$ of $E/F$ at $w$ are finite (non-zero in Mathlib's convention,
and the residue class field extension is finite-dimensional) and $ef \le n$. -/
@[kb "omeara1963" "§13B, 13:6, p. 24"]
theorem ramificationIndexAbs_mul_inertiaDegAbs_le [FiniteDimensional F E] (w : AbsoluteValue E ℝ)
    (hw : IsNonarchimedean w) :
    ramificationIndexAbs (F := F) w ≠ 0 ∧ inertiaDegAbs (F := F) w hw ≠ 0 ∧
      ramificationIndexAbs (F := F) w * inertiaDegAbs (F := F) w hw ≤ Module.finrank F E := by
  classical
  let _ := residueAlgebra (F := F) w hw
  have hbound : ∀ s : Finset (residueFieldOf w hw),
      (LinearIndependent (residueFieldOf (w.under F) (isNonarchimedean_under hw))
        fun i : s => (i : residueFieldOf w hw)) → s.card ≤ Module.finrank F E := by
    intro s hs
    choose ω hω using fun i : s =>
      Ideal.Quotient.mk_surjective (I := maximalIdealOf w hw) (i : residueFieldOf w hw)
    have hs' : LinearIndependent (residueFieldOf (w.under F)
        (isNonarchimedean_under hw))
        (fun i : s => Ideal.Quotient.mk (maximalIdealOf w hw) (ω i)) := by
      have : (fun i : s => Ideal.Quotient.mk (maximalIdealOf w hw) (ω i)) =
          fun i : s => (i : residueFieldOf w hw) := funext hω
      rw [this]; exact hs
    have := (linearIndependent_mul_of_residues (F := F) hw (fun i : s => ((ω i : integers w hw) : E))
      (fun i => (ω i).2) (fun b hb1 hb2 => elem_of_linearIndependent w hw ω hs' b hb1 hb2)
      (fun _ : Unit => (1 : E)) (fun _ => one_ne_zero)
      (by intro j k hjk; exact absurd (Subsingleton.elim j k) hjk)).fintype_card_le_finrank
    simpa using this
  have hrank : Module.rank (residueFieldOf (w.under F) (isNonarchimedean_under hw))
      (residueFieldOf w hw) ≤ (Module.finrank F E : ℕ) := rank_le hbound
  have hfinmod : Module.Finite (residueFieldOf (w.under F) (isNonarchimedean_under hw))
      (residueFieldOf w hw) :=
    Module.rank_lt_aleph0_iff.1 (hrank.trans_lt (Cardinal.natCast_lt_aleph0))
  have hfin : Finite (absValueGroup w ⧸
      (absValueGroup (w.under F)).subgroupOf (absValueGroup w)) := by
    by_contra hinf
    rw [not_finite_iff_infinite] at hinf
    let q : Fin (Module.finrank F E + 1) → (absValueGroup w ⧸
      (absValueGroup (w.under F)).subgroupOf (absValueGroup w)) :=
      fun j => Infinite.natEmbedding _ j.val
    have hq : Function.Injective q := fun a b h => Fin.ext ((Infinite.natEmbedding _).injective h)
    obtain ⟨x, hx0, hxd⟩ := exists_coset_reps (F := F) w q hq
    have := (linearIndependent_mul_of_residues (F := F) hw (fun _ : Unit => (1 : E)) (by simp)
      (fun b _ h i => by cases i; simpa using h) x hx0 hxd).fintype_card_le_finrank
    simp at this
  let _ : Fintype (absValueGroup w ⧸
      (absValueGroup (w.under F)).subgroupOf (absValueGroup w)) := Fintype.ofFinite _
  have hs : ramificationIndexAbs (F := F) w = Fintype.card (absValueGroup w ⧸
      (absValueGroup (w.under F)).subgroupOf (absValueGroup w)) := by
    unfold ramificationIndexAbs
    exact Nat.card_eq_fintype_card
  have hf : inertiaDegAbs (F := F) w hw = Module.finrank
      (residueFieldOf (w.under F) (isNonarchimedean_under hw))
      (residueFieldOf w hw) := rfl
  obtain ⟨x, hx0, hxd⟩ := exists_coset_reps (F := F) w
    (id : (absValueGroup w ⧸
      (absValueGroup (w.under F)).subgroupOf (absValueGroup w)) → _) Function.injective_id
  let bas := Module.finBasis (residueFieldOf (w.under F) (isNonarchimedean_under hw))
      (residueFieldOf w hw)
  choose ω hω using fun i => Ideal.Quotient.mk_surjective (I := maximalIdealOf w hw) (bas i)
  have hlin : LinearIndependent (residueFieldOf (w.under F)
      (isNonarchimedean_under hw))
      (fun i => Ideal.Quotient.mk (maximalIdealOf w hw) (ω i)) := by
    have : (fun i => Ideal.Quotient.mk (maximalIdealOf w hw) (ω i)) = fun i => bas i := funext hω
    rw [this]; exact bas.linearIndependent
  have hmain := (linearIndependent_mul_of_residues (F := F) hw (fun i => ((ω i : integers w hw) : E))
    (fun i => (ω i).2) (fun b hb1 hb2 => elem_of_linearIndependent w hw ω hlin b hb1 hb2)
    x hx0 hxd).fintype_card_le_finrank
  rw [Fintype.card_prod, Fintype.card_fin] at hmain
  have hne : Module.finrank (residueFieldOf (w.under F) (isNonarchimedean_under hw))
      (residueFieldOf w hw) ≠ 0 := (Module.finrank_pos).ne'
  refine ⟨?_, ?_, ?_⟩
  · exact (Subgroup.index_ne_zero_iff_finite.2 hfin)
  · rw [hf]; exact hne
  · rw [hs, hf, mul_comm]; exact hmain

end Extension

/-- **Prolongation from a subring** (§13C, p. 25). Let $F$ be the quotient field of its subring $Z$ (more generally of
a domain $Z$, `IsFractionRing Z F`), and let $f\colon Z \to \mathbb R$ satisfy the valuation axioms on $Z$:
$f(a) > 0$ for $a \ne 0$, $f(0) = 0$, $f(ab) = f(a)f(b)$ and $f(a + b) \le f(a) + f(b)$. Then there is a unique
valuation $v$ of $F$ prolonging $f$, namely $v(a/b) = f(a)/f(b)$; if moreover $f(a + b) \le \max(f(a), f(b))$ on $Z$
then $v$ is non-archimedean.

The machine-read text of the book lists the axioms as "(V₁), (V₂), (V₃)" and calls the prolongation
non-archimedean; non-archimedean requires the strong triangle law (V₄) on $Z$, so both versions are stated. -/
@[kb "omeara1963" "§13C, p. 25 (prolongation of a valuation from a subring Z to its quotient field)"]
theorem exists_unique_extend_of_isFractionRing {Z F : Type*} [CommRing Z] [IsDomain Z] [Field F]
    [Algebra Z F] [IsFractionRing Z F] (f : Z → ℝ) (hpos : ∀ a, a ≠ 0 → 0 < f a) (h0 : f 0 = 0)
    (hmul : ∀ a b, f (a * b) = f a * f b) (hadd : ∀ a b, f (a + b) ≤ f a + f b) :
    (∃! v : AbsoluteValue F ℝ, ∀ a : Z, v (algebraMap Z F a) = f a) ∧
      ((∀ a b, f (a + b) ≤ max (f a) (f b)) →
        ∀ v : AbsoluteValue F ℝ, (∀ a : Z, v (algebraMap Z F a) = f a) → IsNonarchimedean v) := by
  classical
  have hf1 : f 1 = 1 := by
    have h := hmul 1 1
    have hp := hpos 1 one_ne_zero
    simp only [mul_one] at h
    have h2 : f 1 * (f 1 - 1) = 0 := by linarith
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd h3 hp.ne'
    · linarith
  have hnn : ∀ a, 0 ≤ f a := fun a => by
    by_cases h : a = 0
    · simp [h, h0]
    · exact (hpos a h).le
  have hZ : ∀ a : Z, a ≠ 0 → algebraMap Z F a ≠ 0 := fun a ha =>
    (map_ne_zero_iff _ (IsFractionRing.injective Z F)).2 ha
  have rep : ∀ x : F, ∃ a b : Z, b ≠ 0 ∧ x = algebraMap Z F a / algebraMap Z F b := by
    intro x
    obtain ⟨a, b, hb, h⟩ := IsFractionRing.div_surjective (A := Z) x
    exact ⟨a, b, nonZeroDivisors.ne_zero hb, h.symm⟩
  have cross : ∀ a b c d : Z, b ≠ 0 → d ≠ 0 →
      algebraMap Z F a / algebraMap Z F b = algebraMap Z F c / algebraMap Z F d →
      f a / f b = f c / f d := by
    intro a b c d hb hd h
    have hb' := hZ b hb
    have hd' := hZ d hd
    rw [div_eq_div_iff hb' hd'] at h
    have h' : a * d = c * b := by
      apply IsFractionRing.injective Z F
      simpa using h
    rw [div_eq_div_iff (hpos b hb).ne' (hpos d hd).ne']
    have := congrArg f h'
    rwa [hmul, hmul] at this
  let g : F → ℝ := fun x => f (Classical.choose (rep x)) /
    f (Classical.choose (Classical.choose_spec (rep x)))
  have hg : ∀ a b : Z, b ≠ 0 → g (algebraMap Z F a / algebraMap Z F b) = f a / f b := by
    intro a b hb
    have hsp := Classical.choose_spec (Classical.choose_spec
      (rep (algebraMap Z F a / algebraMap Z F b)))
    exact cross _ _ _ _ hsp.1 hb hsp.2.symm
  have hgmul : ∀ x y, g (x * y) = g x * g y := by
    intro x y
    obtain ⟨a, b, hb, rfl⟩ := rep x
    obtain ⟨c, d, hd, rfl⟩ := rep y
    rw [div_mul_div_comm, ← map_mul, ← map_mul, hg _ _ (mul_ne_zero hb hd), hg a b hb, hg c d hd,
      hmul, hmul, div_mul_div_comm]
  have hgadd : ∀ x y, g (x + y) ≤ g x + g y := by
    intro x y
    obtain ⟨a, b, hb, rfl⟩ := rep x
    obtain ⟨c, d, hd, rfl⟩ := rep y
    have hbp := hpos b hb
    have hdp := hpos d hd
    have hxy : algebraMap Z F a / algebraMap Z F b + algebraMap Z F c / algebraMap Z F d =
        algebraMap Z F (a * d + b * c) / algebraMap Z F (b * d) := by
      rw [div_add_div _ _ (hZ b hb) (hZ d hd), map_add, map_mul, map_mul, map_mul]
    rw [hxy, hg _ _ (mul_ne_zero hb hd), hg a b hb, hg c d hd, hmul b d]
    calc f (a * d + b * c) / (f b * f d) ≤ (f (a * d) + f (b * c)) / (f b * f d) := by
          gcongr; exact hadd _ _
      _ = f a / f b + f c / f d := by rw [hmul, hmul]; field_simp
  have hgnn : ∀ x, 0 ≤ g x := by
    intro x
    obtain ⟨a, b, hb, rfl⟩ := rep x
    rw [hg a b hb]
    exact div_nonneg (hnn a) (hpos b hb).le
  have hgz : ∀ x, g x = 0 ↔ x = 0 := by
    intro x
    obtain ⟨a, b, hb, rfl⟩ := rep x
    rw [hg a b hb, div_eq_zero_iff, div_eq_zero_iff]
    constructor
    · rintro (h | h)
      · left
        by_contra ha
        exact (hpos a (fun h' => ha (by simp [h']))).ne' h
      · exact absurd h (hpos b hb).ne'
    · rintro (h | h)
      · left
        have : a = 0 := (map_eq_zero_iff _ (IsFractionRing.injective Z F)).1 h
        rw [this, h0]
      · exact absurd h (hZ b hb)
  let v : AbsoluteValue F ℝ :=
    { toFun := g
      map_mul' := hgmul
      nonneg' := hgnn
      eq_zero' := hgz
      add_le' := hgadd }
  have hv' : ∀ v' : AbsoluteValue F ℝ, (∀ a : Z, v' (algebraMap Z F a) = f a) →
      ∀ a b : Z, b ≠ 0 → v' (algebraMap Z F a / algebraMap Z F b) = f a / f b := by
    intro v' hv' a b hb
    rw [map_div₀, hv', hv']
  have hvalg : ∀ a : Z, v (algebraMap Z F a) = f a := by
    intro a
    have h := hg a 1 one_ne_zero
    rw [map_one, div_one, hf1, div_one] at h
    exact h
  refine ⟨⟨v, hvalg, fun v' hv'' => ?_⟩, fun hmax v' hv'' => ?_⟩
  · ext x
    obtain ⟨a, b, hb, rfl⟩ := rep x
    rw [hv' v' hv'' a b hb]
    exact (hg a b hb).symm
  · intro x y
    obtain ⟨a, b, hb, rfl⟩ := rep x
    obtain ⟨c, d, hd, rfl⟩ := rep y
    have hbp := hpos b hb
    have hdp := hpos d hd
    have hxy : algebraMap Z F a / algebraMap Z F b + algebraMap Z F c / algebraMap Z F d =
        algebraMap Z F (a * d + b * c) / algebraMap Z F (b * d) := by
      rw [div_add_div _ _ (hZ b hb) (hZ d hd), map_add, map_mul, map_mul, map_mul]
    rw [hxy, hv' v' hv'' _ _ (mul_ne_zero hb hd), hv' v' hv'' a b hb, hv' v' hv'' c d hd, hmul b d]
    have := hmax (a * d) (b * c)
    rw [hmul, hmul] at this
    rcases le_total (f a * f d) (f b * f c) with h | h
    · rw [max_eq_right h] at this
      refine le_sup_of_le_right ?_
      calc f (a * d + b * c) / (f b * f d) ≤ (f b * f c) / (f b * f d) := by gcongr
        _ = f c / f d := by field_simp
    · rw [max_eq_left h] at this
      refine le_sup_of_le_left ?_
      calc f (a * d + b * c) / (f b * f d) ≤ (f a * f d) / (f b * f d) := by gcongr
        _ = f a / f b := by field_simp

end QuadFormsKB.OMeara
