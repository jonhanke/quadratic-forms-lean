import QuadFormsKB.Tamagawa.Measure.Weil.SphereBlock
import QuadFormsKB.Tamagawa.Measure.ConeAlgebra

/-!
# Isotropic frames and a two-reflection section of the cone

The adelic cone needs a section $s$ of the orbit map $g\mapsto g\,e$ of $SO(V)$ on the punctured cone
$C^\circ = \{x\ne0 : Q(x) = 0\}$ which is integral at almost every place on primitive vectors. This file gives the
place-independent algebra.

* **Two reflections** (`coneSec2`): for isotropic $e, \zeta, x$ with $B(\zeta, e)\ne0$ and $B(x,\zeta)\ne0$,
  $s = \tau_{x-\zeta}\tau_{\zeta-e}$ is in $SO(H)$ and $s\,e = x$ (`coneSec2_mulVec`, `coneSec2_mem`); here $q = x^{\mathsf T}Hx$,
  $B(x,y) = x^{\mathsf T}Hy$, and $\tau_{\zeta - e}e = \zeta$, $\tau_{x-\zeta}\zeta = x$ because $q(x - \zeta) = -2B(x,\zeta)$.
* **The branch** (`bestIdx`): for a finite family $(\zeta_j)$ and a normed field, the first index maximizing
  $\|B(x,\zeta_j)\|$; it is a measurable function of $x$ (`measurable_bestIdx`).
* **Isotropic frames** (`IsoFrame`): isotropic vectors $\zeta_0,\dots,\zeta_{n-1}$ with $B(\zeta_j, e)\ne0$ and a matrix $Y$ with
  $Y\,M = 1$, $M_{ji} = (H\zeta_j)_i$ (so $x = Y\,(B(x,\zeta_j))_j$): if $x\ne0$ some $B(x,\zeta_j)\ne0$, and at a place where
  $Y$ is integral a primitive $x$ has some $B(x,\zeta_j)$ a unit.
* **`exists_isoFrame_cone`**: the cone form $\langle c\rangle\perp\langle -c\rangle\perp Q'$ ($c\ne0$, $Q'$ nondegenerate in
  $k\ge1$ variables, characteristic $0$) has an isotropic frame for $e = e_0 + e_1$, with
  $\zeta = \iota(1, 0), \iota(1, y^*), \iota(1, \varepsilon_0), \dots, \iota(1,\varepsilon_{k-1})$, where
  $\iota(t, y) = \big(\tfrac{t - q'(y)/(2ct)}2, \tfrac{-t - q'(y)/(2ct)}2, y\big)$ (`isoVec`) and $y^* = \varepsilon_a + \varepsilon_b$ for an
  entry $H'_{ab}\ne0$ of the Hessian of $Q'$.
Indices are $0$-based.
-/

open Matrix MeasureTheory
open scoped Matrix

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

/-! ### Two reflections -/

section TwoRefl

variable {R : Type*} [Field R] {n : ℕ} (H : Matrix (Fin n) (Fin n) R)

/-- **The two-reflection section** $s = \tau_{x-\zeta}\tau_{\zeta-e}$ (sends $e\mapsto\zeta\mapsto x$). -/
def coneSec2 (e ζ x : Fin n → R) : Matrix (Fin n) (Fin n) R := refl H (x - ζ) * refl H (ζ - e)

/-- Its inverse $\tau_{\zeta-e}\tau_{x-\zeta}$. -/
def coneSec2Inv (e ζ x : Fin n → R) : Matrix (Fin n) (Fin n) R := refl H (ζ - e) * refl H (x - ζ)

variable {H}

/-- For isotropic $x, y$: $q(x - y) = -2B(x, y)$. -/
theorem qH_sub_of_iso (hH : Hᵀ = H) {x y : Fin n → R} (hx : qH H x = 0) (hy : qH H y = 0) :
    qH H (x - y) = -2 * bH H x y := by
  rw [qH_sub hH, hx, hy]; ring

theorem qH_sub_ne_zero_of_iso (hH : Hᵀ = H) (h2 : (2 : R) ≠ 0) {x y : Fin n → R} (hx : qH H x = 0)
    (hy : qH H y = 0) (hb : bH H x y ≠ 0) : qH H (x - y) ≠ 0 := by
  rw [qH_sub_of_iso hH hx hy]
  exact mul_ne_zero (neg_ne_zero.mpr h2) hb

/-- **$\tau_{x-y}\,y = x$** for isotropic $x, y$ with $B(x,y)\ne0$. -/
theorem refl_sub_mulVec_iso (hH : Hᵀ = H) (h2 : (2 : R) ≠ 0) {x y : Fin n → R} (hx : qH H x = 0)
    (hy : qH H y = 0) (hb : bH H x y ≠ 0) : refl H (x - y) *ᵥ y = x := by
  rw [refl_mulVec hH, qH_sub_of_iso hH hx hy, bH_sub_left, ← qH_eq_bH, hy, sub_zero, bH_comm hH x y]
  rw [bH_comm hH x y] at hb
  rw [show 2 * bH H y x / (-2 * bH H y x) = -1 by
    rw [div_eq_iff (mul_ne_zero (neg_ne_zero.mpr h2) hb)]; ring]
  rw [neg_one_smul, sub_neg_eq_add, add_sub_cancel]

variable {e ζ x : Fin n → R}

/-- **$s\,e = x$.** -/
theorem coneSec2_mulVec (hH : Hᵀ = H) (h2 : (2 : R) ≠ 0) (hx : qH H x = 0) (hζ : qH H ζ = 0)
    (he : qH H e = 0) (hxζ : bH H x ζ ≠ 0) (hζe : bH H ζ e ≠ 0) : coneSec2 H e ζ x *ᵥ e = x := by
  rw [coneSec2, ← mulVec_mulVec, refl_sub_mulVec_iso hH h2 hζ he hζe, refl_sub_mulVec_iso hH h2 hx hζ hxζ]

/-- **$s\in SO(H)$.** -/
theorem coneSec2_mem (hH : Hᵀ = H) (h2 : (2 : R) ≠ 0) (hx : qH H x = 0) (hζ : qH H ζ = 0)
    (he : qH H e = 0) (hxζ : bH H x ζ ≠ 0) (hζe : bH H ζ e ≠ 0) :
    (coneSec2 H e ζ x)ᵀ * H * coneSec2 H e ζ x = H ∧ (coneSec2 H e ζ x).det = 1 :=
  refl_mul_refl_mem H hH (qH_sub_ne_zero_of_iso hH h2 hx hζ hxζ) (qH_sub_ne_zero_of_iso hH h2 hζ he hζe)

/-- $s\,s^{-1} = 1 = s^{-1}s$. -/
theorem coneSec2_mul_inv (hH : Hᵀ = H) (h2 : (2 : R) ≠ 0) (hx : qH H x = 0) (hζ : qH H ζ = 0)
    (he : qH H e = 0) (hxζ : bH H x ζ ≠ 0) (hζe : bH H ζ e ≠ 0) :
    coneSec2 H e ζ x * coneSec2Inv H e ζ x = 1 ∧ coneSec2Inv H e ζ x * coneSec2 H e ζ x = 1 := by
  have h1 := qH_sub_ne_zero_of_iso hH h2 hx hζ hxζ
  have h1' := qH_sub_ne_zero_of_iso hH h2 hζ he hζe
  constructor
  · rw [coneSec2, coneSec2Inv, show refl H (x - ζ) * refl H (ζ - e) * (refl H (ζ - e) * refl H (x - ζ)) =
      refl H (x - ζ) * (refl H (ζ - e) * refl H (ζ - e)) * refl H (x - ζ) by simp only [Matrix.mul_assoc],
      refl_mul_refl_self H hH h1', Matrix.mul_one, refl_mul_refl_self H hH h1]
  · rw [coneSec2, coneSec2Inv, show refl H (ζ - e) * refl H (x - ζ) * (refl H (x - ζ) * refl H (ζ - e)) =
      refl H (ζ - e) * (refl H (x - ζ) * refl H (x - ζ)) * refl H (ζ - e) by simp only [Matrix.mul_assoc],
      refl_mul_refl_self H hH h1, Matrix.mul_one, refl_mul_refl_self H hH h1']

end TwoRefl

/-! ### The branch: the first index maximizing $\|B(x,\zeta_j)\|$ -/

section Best

variable {R : Type*} [NormedField R] {n m : ℕ} (H : Matrix (Fin n) (Fin n) R) (ζ : Fin (m + 1) → Fin n → R)

/-- The set of indices maximizing $\|B(x,\zeta_j)\|$ (nonempty). -/
def bestSet (x : Fin n → R) : Finset (Fin (m + 1)) :=
  Finset.univ.filter fun j => ∀ l, ‖bH H x (ζ l)‖ ≤ ‖bH H x (ζ j)‖

theorem bestSet_nonempty (x : Fin n → R) : (bestSet H ζ x).Nonempty := by
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun j => ‖bH H x (ζ j)‖) Finset.univ_nonempty
  exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun l => hj l (Finset.mem_univ l)⟩⟩

/-- **The branch index**: the first $j$ maximizing $\|B(x,\zeta_j)\|$. -/
def bestIdx (x : Fin n → R) : Fin (m + 1) := (bestSet H ζ x).min' (bestSet_nonempty H ζ x)

theorem bestIdx_spec (x : Fin n → R) (l : Fin (m + 1)) : ‖bH H x (ζ l)‖ ≤ ‖bH H x (ζ (bestIdx H ζ x))‖ :=
  (Finset.mem_filter.mp (Finset.min'_mem _ (bestSet_nonempty H ζ x))).2 l

/-- If some $B(x,\zeta_l)\ne0$ then $B(x,\zeta_{\mathrm{best}})\ne0$. -/
theorem bH_bestIdx_ne_zero {x : Fin n → R} {l : Fin (m + 1)} (hl : bH H x (ζ l) ≠ 0) :
    bH H x (ζ (bestIdx H ζ x)) ≠ 0 := by
  have h := bestIdx_spec H ζ x l
  intro h0
  rw [h0, norm_zero] at h
  exact hl (norm_le_zero_iff.mp h)

theorem bestIdx_eq_iff (x : Fin n → R) (j : Fin (m + 1)) :
    bestIdx H ζ x = j ↔ (∀ l, ‖bH H x (ζ l)‖ ≤ ‖bH H x (ζ j)‖) ∧
      ∀ l, (∀ l', ‖bH H x (ζ l')‖ ≤ ‖bH H x (ζ l)‖) → j ≤ l := by
  have hmem : ∀ l, l ∈ bestSet H ζ x ↔ ∀ l', ‖bH H x (ζ l')‖ ≤ ‖bH H x (ζ l)‖ := fun l => by
    simp [bestSet]
  constructor
  · rintro rfl
    exact ⟨bestIdx_spec H ζ x, fun l hl => Finset.min'_le _ _ ((hmem l).mpr hl)⟩
  · rintro ⟨h1, h2⟩
    refine le_antisymm (Finset.min'_le _ _ ((hmem j).mpr h1)) ?_
    exact h2 _ ((hmem _).mp (Finset.min'_mem _ _))

variable [MeasurableSpace R] [MeasurableAdd₂ R] [MeasurableMul₂ R] [OpensMeasurableSpace R]

theorem measurable_bH_left (y : Fin n → R) : Measurable fun x : Fin n → R => bH H x y := by
  unfold bH dotProduct
  exact Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).mul measurable_const

theorem measurable_norm_bH (y : Fin n → R) : Measurable fun x : Fin n → R => ‖bH H x y‖ :=
  continuous_norm.measurable.comp (measurable_bH_left H y)

theorem measurableSet_bestIdx_eq (j : Fin (m + 1)) : MeasurableSet {x | bestIdx H ζ x = j} := by
  have hle : ∀ l l' : Fin (m + 1), MeasurableSet {x : Fin n → R | ‖bH H x (ζ l')‖ ≤ ‖bH H x (ζ l)‖} :=
    fun l l' => measurableSet_le (measurable_norm_bH H _) (measurable_norm_bH H _)
  have heq : {x | bestIdx H ζ x = j} = (⋂ l : Fin (m + 1), {x | ‖bH H x (ζ l)‖ ≤ ‖bH H x (ζ j)‖}) ∩
      ⋂ l : Fin (m + 1), ((⋂ l' : Fin (m + 1), {x | ‖bH H x (ζ l')‖ ≤ ‖bH H x (ζ l)‖})ᶜ ∪ {_x | j ≤ l}) := by
    ext x
    simp only [Set.mem_setOf_eq, bestIdx_eq_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_union,
      Set.mem_compl_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun l => by by_cases h : ∀ l', ‖bH H x (ζ l')‖ ≤ ‖bH H x (ζ l)‖
                             · exact Or.inr (h2 l h)
                             · exact Or.inl h⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun l hl => (h2 l).resolve_left (not_not.mpr hl)⟩
  rw [heq]
  exact (MeasurableSet.iInter fun l => hle j l).inter (MeasurableSet.iInter fun l =>
    (MeasurableSet.iInter fun l' => hle l l').compl.union (MeasurableSet.const _))

/-- **The branch index is measurable.** -/
theorem measurable_bestIdx : Measurable (bestIdx H ζ) :=
  measurable_to_countable' fun j => measurableSet_bestIdx_eq H ζ j

/-- A function chosen by the branch, $x\mapsto G_{\mathrm{best}(x)}(x)$, is measurable if every $G_j$ is. -/
theorem measurable_comp_bestIdx {Y : Type*} [MeasurableSpace Y] {G : Fin (m + 1) → (Fin n → R) → Y}
    (hG : ∀ j, Measurable (G j)) : Measurable fun x => G (bestIdx H ζ x) x := by
  have h : Measurable fun p : Fin (m + 1) × (Fin n → R) => G p.1 p.2 :=
    measurable_from_prod_countable_right (f := fun p : Fin (m + 1) × (Fin n → R) => G p.1 p.2) fun j => hG j
  exact h.comp ((measurable_bestIdx H ζ).prodMk measurable_id)

end Best

/-! ### Isotropic frames -/

section Frame

variable {R : Type*} [Field R] {n : ℕ}

/-- The matrix $M_{ji} = (H\zeta_j)_i$, so that $(Mx)_j = B(\zeta_j, x)$. -/
def isoFrameMat (H : Matrix (Fin n) (Fin n) R) (ζ : Fin n → Fin n → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun j i => (H *ᵥ ζ j) i

theorem isoFrameMat_mulVec (H : Matrix (Fin n) (Fin n) R) (hH : Hᵀ = H) (ζ : Fin n → Fin n → R) (x : Fin n → R) (j : Fin n) :
    (isoFrameMat H ζ *ᵥ x) j = bH H x (ζ j) := by
  rw [bH, dotProduct_comm]; rfl

/-- **An isotropic frame for $e$**: isotropic vectors $\zeta_j$ with $B(\zeta_j, e)\ne0$ and a left inverse $Y$ of
$M = $ `isoFrameMat H ζ`. Fields: `ζ`, `Y`, `iso`, `pair_ne`, `inv`. -/
structure IsoFrame (H : Matrix (Fin n) (Fin n) R) (e : Fin n → R) where
  /-- The isotropic vectors $\zeta_j$. -/
  ζ : Fin n → Fin n → R
  /-- A left inverse of $M$. -/
  Y : Matrix (Fin n) (Fin n) R
  /-- $q(\zeta_j) = 0$. -/
  iso : ∀ j, qH H (ζ j) = 0
  /-- $B(\zeta_j, e)\ne 0$. -/
  pair_ne : ∀ j, bH H (ζ j) e ≠ 0
  /-- $YM = 1$. -/
  inv : Y * isoFrameMat H ζ = 1

variable {H : Matrix (Fin n) (Fin n) R} {e : Fin n → R}

/-- $x = Y\,(B(x,\zeta_j))_j$. -/
theorem IsoFrame.eq_Y_mulVec (Z : IsoFrame H e) (hH : Hᵀ = H) (x : Fin n → R) :
    Z.Y *ᵥ (fun j => bH H x (Z.ζ j)) = x := by
  have : (fun j => bH H x (Z.ζ j)) = isoFrameMat H Z.ζ *ᵥ x := funext fun j => (isoFrameMat_mulVec H hH Z.ζ x j).symm
  rw [this, mulVec_mulVec, Z.inv, one_mulVec]

/-- **A nonzero vector pairs nontrivially with some $\zeta_j$.** -/
theorem IsoFrame.exists_bH_ne_zero (Z : IsoFrame H e) (hH : Hᵀ = H) {x : Fin n → R} (hx : x ≠ 0) :
    ∃ j, bH H x (Z.ζ j) ≠ 0 := by
  by_contra h
  push Not at h
  apply hx
  rw [← Z.eq_Y_mulVec hH x]
  have : (fun j => bH H x (Z.ζ j)) = 0 := funext h
  rw [this, mulVec_zero]

/-- **Base change of a frame** along a ring homomorphism of fields. -/
def IsoFrame.map {S : Type*} [Field S] (Z : IsoFrame H e) (σ : R →+* S) :
    IsoFrame (H.map σ) (fun i => σ (e i)) where
  ζ j i := σ (Z.ζ j i)
  Y := Z.Y.map σ
  iso j := by
    have := congrArg σ (Z.iso j)
    rw [map_zero] at this
    rw [← this]
    simp only [qH, dotProduct, mulVec, map_sum, map_mul, Matrix.map_apply]
  pair_ne j := by
    have h := Z.pair_ne j
    have : bH (H.map σ) (fun i => σ (Z.ζ j i)) (fun i => σ (e i)) = σ (bH H (Z.ζ j) e) := by
      simp only [bH, dotProduct, mulVec, map_sum, map_mul, Matrix.map_apply]
    rw [this]
    exact (map_ne_zero σ).mpr h
  inv := by
    have : isoFrameMat (H.map σ) (fun j i => σ (Z.ζ j i)) = (isoFrameMat H Z.ζ).map σ := by
      ext j i
      simp [isoFrameMat, mulVec, dotProduct, map_sum, map_mul]
    rw [this, ← Matrix.map_mul, Z.inv, Matrix.map_one _ (map_zero σ) (map_one σ)]

end Frame

/-! ### The frame of the cone form -/

section ConeFrame

open ConeAlgebra

variable {K : Type*} [Field K] [CharZero K] {k : ℕ} (c : K) (Q' : QuadForm K k)

/-- **Isotropic vectors of the cone form**: $\iota(t, y) = \big(\frac{t - q'(y)/(2ct)}2, \frac{-t - q'(y)/(2ct)}2, y\big)$,
$q' = y^{\mathsf T}H'y$. -/
def isoVec (t : K) (y : Fin k → K) : Fin (k + 1 + 1) → K :=
  v3 ((t - qH Q'.hessian y / (2 * c * t)) / 2) ((-t - qH Q'.hessian y / (2 * c * t)) / 2) y

theorem bH_cone_v3 (x0 x1 a b : K) (x y : Fin k → K) :
    bH (coneForm c Q').hessian (v3 x0 x1 x) (v3 a b y) = 2 * c * a * x0 - 2 * c * b * x1 + bH Q'.hessian x y := by
  rw [bH, hessian_coneForm_mulVec_v3, dotProduct_v3, bH]; ring

variable {c}

theorem qH_isoVec (hc : c ≠ 0) {t : K} (ht : t ≠ 0) (y : Fin k → K) :
    qH (coneForm c Q').hessian (isoVec c Q' t y) = 0 := by
  rw [qH_eq_bH, isoVec, bH_cone_v3, ← qH_eq_bH]
  field_simp
  ring

/-- $B(x, \iota(t, y)) = ct(x_0 + x_1) - \frac{q'(y)}{2t}(x_0 - x_1) + B'(x', y)$. -/
theorem bH_isoVec (hc : c ≠ 0) {t : K} (ht : t ≠ 0) (x0 x1 : K) (x y : Fin k → K) :
    bH (coneForm c Q').hessian (v3 x0 x1 x) (isoVec c Q' t y) =
      c * t * (x0 + x1) - qH Q'.hessian y / (2 * t) * (x0 - x1) + bH Q'.hessian x y := by
  rw [isoVec, bH_cone_v3]
  field_simp
  ring

theorem bH_isoVec_eV (hc : c ≠ 0) {t : K} (ht : t ≠ 0) (y : Fin k → K) :
    bH (coneForm c Q').hessian (isoVec c Q' t y) eV = 2 * c * t := by
  have hs : (coneForm c Q').hessianᵀ = (coneForm c Q').hessian := QuadForm.hessian_transpose _
  rw [bH_comm hs, eV, bH_isoVec Q' hc ht]
  simp [bH]
  ring

/-- The frame vectors: $\iota(1,0)$, $\iota(1,y^*)$, $\iota(1,\varepsilon_j)$. -/
def coneFrameVec (ystar : Fin k → K) : Fin (k + 1 + 1) → Fin (k + 1 + 1) → K :=
  Fin.cons (isoVec c Q' 1 0) (Fin.cons (isoVec c Q' 1 ystar) fun j => isoVec c Q' 1 (Pi.single j 1))

theorem exists_hessian_entry_ne (hk : 1 ≤ k) (hQ' : Q'.hessian.det ≠ 0) : ∃ a b, Q'.hessian a b ≠ 0 := by
  by_contra h
  push Not at h
  apply hQ'
  have : Q'.hessian = 0 := Matrix.ext h
  rw [this]
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact Matrix.det_zero

/-- **Injectivity of the frame pairing**: if $B(x,\zeta_j) = 0$ for every frame vector, then $x = 0$. -/
theorem eq_zero_of_bH_coneFrameVec (hc : c ≠ 0) (hQ' : Q'.hessian.det ≠ 0) {a b : Fin k}
    (hab : Q'.hessian a b ≠ 0) (x : Fin (k + 1 + 1) → K)
    (hx : ∀ j, bH (coneForm c Q').hessian x (coneFrameVec (c := c) Q' (Pi.single a 1 + Pi.single b 1) j) = 0) : x = 0 := by
  have hs' : Q'.hessianᵀ = Q'.hessian := QuadForm.hessian_transpose _
  rw [← v3_eta x] at hx ⊢
  set x0 := x 0
  set x1 := x 1
  set x' := tl x
  have h0 := hx 0
  have h1 := hx 1
  have hj : ∀ j : Fin k, bH (coneForm c Q').hessian (v3 x0 x1 x') (isoVec c Q' 1 (Pi.single j 1)) = 0 := fun j =>
    hx j.succ.succ
  simp only [coneFrameVec, Fin.cons_zero, Fin.cons_one] at h0 h1
  rw [bH_isoVec Q' hc one_ne_zero] at h0 h1
  simp_rw [bH_isoVec Q' hc one_ne_zero] at hj
  have hq0 : qH Q'.hessian (0 : Fin k → K) = 0 := by simp [qH]
  have hb0 : bH Q'.hessian x' 0 = 0 := by simp [bH]
  rw [hq0, hb0] at h0
  -- x0 + x1 = 0
  have hsum : x0 + x1 = 0 := by
    have : c * (x0 + x1) = 0 := by linear_combination h0
    exact (mul_eq_zero.mp this).resolve_left hc
  -- the y* equation gives x0 = x1
  have hqy : qH Q'.hessian (Pi.single a 1 + Pi.single b 1) =
      qH Q'.hessian (Pi.single a 1) + 2 * Q'.hessian a b + qH Q'.hessian (Pi.single b 1) := by
    rw [qH_add hs']
    congr 2
    simp [bH, mulVec, dotProduct, Pi.single_apply]
  have hby : bH Q'.hessian x' (Pi.single a 1 + Pi.single b 1) =
      bH Q'.hessian x' (Pi.single a 1) + bH Q'.hessian x' (Pi.single b 1) := bH_add_right _ _ _
  have ha := hj a
  have hb := hj b
  rw [hqy, hby, hsum] at h1
  rw [hsum] at ha hb
  have hdiff : Q'.hessian a b * (x0 - x1) = 0 := by linear_combination -h1 + ha + hb
  have hd : x0 - x1 = 0 := (mul_eq_zero.mp hdiff).resolve_left hab
  have hx0 : x0 = 0 := by linear_combination (hsum + hd) / 2
  have hx1 : x1 = 0 := by linear_combination (hsum - hd) / 2
  -- then x' ⬝ H' ε_j = 0 for all j, so x' = 0
  have hx' : x' = 0 := by
    have hv : x' ᵥ* Q'.hessian = 0 := by
      funext j
      have := hj j
      rw [hx0, hx1] at this
      simp only [add_zero, sub_zero, mul_zero, zero_sub, neg_zero, zero_add] at this
      simpa [bH, mulVec, vecMul, dotProduct, Pi.single_apply] using this
    have hinj := Matrix.vecMul_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr (Ne.isUnit hQ'))
    exact hinj (show x' ᵥ* Q'.hessian = 0 ᵥ* Q'.hessian by rw [hv, zero_vecMul])
  rw [hx0, hx1, hx']
  ext i
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;> simp [v3]

/-- **The cone form has an isotropic frame for $e = e_0 + e_1$** ($c\ne0$, $Q'$ nondegenerate, $k\ge1$). -/
theorem exists_isoFrame_cone (hc : c ≠ 0) (hQ' : Q'.hessian.det ≠ 0) (hk : 1 ≤ k) :
    Nonempty (IsoFrame (coneForm c Q').hessian eV) := by
  have hs : (coneForm c Q').hessianᵀ = (coneForm c Q').hessian := QuadForm.hessian_transpose _
  obtain ⟨a, b, hab⟩ := exists_hessian_entry_ne Q' hk hQ'
  set ζ := coneFrameVec Q' (c := c) (Pi.single a 1 + Pi.single b 1)
  have hinj : Function.Injective (isoFrameMat (coneForm c Q').hessian ζ).mulVec := by
    intro x y hxy
    have : x - y = 0 := by
      refine eq_zero_of_bH_coneFrameVec Q' hc hQ' hab (x - y) fun j => ?_
      rw [← isoFrameMat_mulVec _ hs, mulVec_sub, hxy, sub_self, Pi.zero_apply]
    exact sub_eq_zero.mp this
  have hU : IsUnit (isoFrameMat (coneForm c Q').hessian ζ) := Matrix.mulVec_injective_iff_isUnit.mp hinj
  have hiso : ∀ j, qH (coneForm c Q').hessian (ζ j) = 0 := fun j => by
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j
    · exact qH_isoVec Q' hc one_ne_zero _
    · exact qH_isoVec Q' hc one_ne_zero _
    · exact qH_isoVec Q' hc one_ne_zero _
  have hpair : ∀ j, bH (coneForm c Q').hessian (ζ j) eV ≠ 0 := fun j => by
    have h2c : (2 : K) * c * 1 ≠ 0 := by simp [hc]
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j
    · show bH _ (isoVec c Q' 1 0) eV ≠ 0; rw [bH_isoVec_eV Q' hc one_ne_zero]; exact h2c
    · show bH _ (isoVec c Q' 1 _) eV ≠ 0; rw [bH_isoVec_eV Q' hc one_ne_zero]; exact h2c
    · show bH _ (isoVec c Q' 1 _) eV ≠ 0; rw [bH_isoVec_eV Q' hc one_ne_zero]; exact h2c
  exact ⟨⟨ζ, (isoFrameMat (coneForm c Q').hessian ζ)⁻¹, hiso, hpair,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hU)⟩⟩

end ConeFrame

end

end QuadFormsKB.Tamagawa.Measure.Weil
