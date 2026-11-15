/-
# The Eichler symbol and the radical of a local Eichler order (Voight, 23.4.15, 24.3)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021 (key `voight2021`): 23.4.15 and (23.4.17) (p. 385),
24.3.1, Definition 24.3.2, Lemma 24.3.6 (pp. 400–401), Definition 24.3.13 (p. 403).

**Setting.** $R$ a local ring with maximal ideal $\mathfrak p$ and residue field $k = R/\mathfrak p$
(`IsLocalRing.ResidueField R`), $B$ an $R$-algebra and $\mathcal O \subseteq B$ an $R$-subalgebra (in the book an
$R$-order in a quaternion algebra over the fraction field $F$ of a complete discrete valuation ring $R$).
$J = \operatorname{rad}\mathcal O$ is the Jacobson radical (Mathlib's `Ring.jacobson`, the intersection of the maximal
left ideals; it is two-sided).

**Contents.**
* `EichlerSym`, `HasEichlerSymbol R O s` (**Definition 24.3.2**): the Eichler symbol $(\mathcal O \mid \mathfrak p)$ is
  $*$, $1$, $0$ or $-1$ according as $\mathcal O/J$ is a quaternion algebra over $k$, $k \times k$, $k$, or a separable
  quadratic field extension of $k$. Definition.
* `jacobson_stdEichlerOrder` (**23.4.15, (23.4.17)**): for $e \ge 1$ the radical of the standard Eichler order
  $\mathcal O_0(\pi^e) = \begin{pmatrix} R & R \\ \pi^e R & R \end{pmatrix}$ is
  $J = \begin{pmatrix} \mathfrak p & R \\ \pi^e R & \mathfrak p \end{pmatrix}$, the kernel of the residue map
  $\mathcal O_0(\pi^e) \to k \times k$ (`Wave5.eichlerRes`). Proved (closes the gap left in wave 5).
* `hasEichlerSymbol_one_stdEichlerOrder`: $\mathcal O_0(\pi^e)$, $e \ge 1$, is residually split. Proved.
* `IsEichler.hasEichlerSymbol_one` (**Lemma 24.3.6**, "only if"): over a discrete valuation ring, a non-maximal
  Eichler order of $\mathrm M_2(F)$ is residually split. Proved (completeness of $R$ is not used).
* `ResiduallySplitIsEichler` (**Lemma 24.3.6**, "if"): a residually split order is Eichler. Stated (the book's proof
  lifts idempotents, which needs completeness).
* `HasEichlerSymbol.of_algEquiv`: the symbol is an isomorphism invariant of $R$-algebras. Proved.
-/
import QuadFormsKB.Literature.Voight.Wave5.EichlerResidue
import QuadFormsKB.Literature.Voight.Correspondence

set_option linter.unusedSectionVars false

open Matrix

noncomputable section

namespace QuadFormsKB.Voight.Wave6

open QuadFormsKB.QuatOrder QuadFormsKB.Voight.Wave3 QuadFormsKB.Voight.Wave4 QuadFormsKB.Voight.Wave5 IsLocalization

/-! ## Jacobson radicals: elementary facts -/

section Jacobson

variable {A A' : Type*} [Ring A] [Ring A']

/-- $x \in \operatorname{rad}A$ iff $1 + yx$ has a left inverse for every $y$. -/
theorem mem_jacobson_iff_exists {x : A} : x ∈ Ring.jacobson A ↔ ∀ y, ∃ z, z * y * x + z = 1 := by
  rw [← Ideal.jacobson_bot, Ideal.mem_jacobson_iff]
  simp only [Submodule.mem_bot, sub_eq_zero]

/-- A ring isomorphism maps the Jacobson radical onto the Jacobson radical. -/
theorem map_mem_jacobson_iff (f : A ≃+* A') (x : A) : f x ∈ Ring.jacobson A' ↔ x ∈ Ring.jacobson A := by
  rw [mem_jacobson_iff_exists, mem_jacobson_iff_exists]
  constructor
  · intro h y
    obtain ⟨z, hz⟩ := h (f y)
    refine ⟨f.symm z, f.injective ?_⟩
    simpa only [map_add, map_mul, RingEquiv.apply_symm_apply, map_one] using hz
  · intro h y
    obtain ⟨z, hz⟩ := h (f.symm y)
    refine ⟨f z, ?_⟩
    have := congrArg f hz
    simpa only [map_add, map_mul, RingEquiv.apply_symm_apply, map_one] using this

theorem jacobson_eq_map (f : A ≃+* A') : Ring.jacobson A' = (Ring.jacobson A).map (f : A →+* A') := by
  ext x
  rw [Ideal.map_comap_of_equiv, Ideal.mem_comap, ← map_mem_jacobson_iff f, RingEquiv.apply_symm_apply]

/-- A surjective ring map to a ring with zero radical kills the radical. -/
theorem map_eq_zero_of_mem_jacobson (f : A →+* A') (hf : Function.Surjective f) (h : Ring.jacobson A' = ⊥)
    {x : A} (hx : x ∈ Ring.jacobson A) : f x = 0 := by
  have : f x ∈ Ring.jacobson A' := by
    rw [mem_jacobson_iff_exists] at hx ⊢
    intro y
    obtain ⟨y', rfl⟩ := hf y
    obtain ⟨z, hz⟩ := hx y'
    exact ⟨f z, by simpa only [map_add, map_mul, map_one] using congrArg f hz⟩
  rw [h] at this
  exact this

/-- $\operatorname{rad}(k \times k) = 0$ for a field $k$. -/
theorem jacobson_prod_field (k : Type*) [Field k] : Ring.jacobson (k × k) = ⊥ := by
  rw [eq_bot_iff]
  rintro ⟨a, b⟩ hx
  rw [mem_jacobson_iff_exists] at hx
  rw [Submodule.mem_bot]
  have ha : a = 0 := by
    by_contra h
    obtain ⟨z, hz⟩ := hx (-a⁻¹, 0)
    have h1 := congrArg Prod.fst hz
    simp only [Prod.fst_add, Prod.fst_mul, Prod.fst_one] at h1
    rw [mul_assoc, neg_mul, inv_mul_cancel₀ h, mul_neg, mul_one, neg_add_cancel] at h1
    exact zero_ne_one h1
  have hb : b = 0 := by
    by_contra h
    obtain ⟨z, hz⟩ := hx (0, -b⁻¹)
    have h1 := congrArg Prod.snd hz
    simp only [Prod.snd_add, Prod.snd_mul, Prod.snd_one] at h1
    rw [mul_assoc, neg_mul, inv_mul_cancel₀ h, mul_neg, mul_one, neg_add_cancel] at h1
    exact zero_ne_one h1
  rw [ha, hb]
  rfl

end Jacobson

/-! ## The Eichler symbol -/

/-- The four values $*, 1, 0, -1$ of the Eichler symbol (Voight 2021, Definition 24.3.2). -/
inductive EichlerSym where
  /-- $(\mathcal O \mid \mathfrak p) = *$: $\mathcal O/\operatorname{rad}\mathcal O$ is a quaternion algebra. -/
  | star
  /-- $(\mathcal O \mid \mathfrak p) = 1$: residually split. -/
  | one
  /-- $(\mathcal O \mid \mathfrak p) = 0$: residually ramified. -/
  | zero
  /-- $(\mathcal O \mid \mathfrak p) = -1$: residually inert. -/
  | negOne
  deriving DecidableEq

section Def

variable (R : Type) [CommRing R] [IsLocalRing R] {B : Type} [Ring B] [Algebra R B]

/-- $\mathcal O/\operatorname{rad}\mathcal O \cong A$ as algebras over $R$, where the $k$-algebra $A$ is an $R$-algebra through
$R \to k$: a ring isomorphism $\varphi : \mathcal O/J \to A$ with $\varphi(r \bmod J) = (r \bmod \mathfrak p) \cdot 1_A$. -/
def ResIso (O : Subalgebra R B) (A : Type) [Ring A] [Algebra (IsLocalRing.ResidueField R) A] : Prop :=
  ∃ φ : O ⧸ Ring.jacobson O ≃+* A, ∀ r : R,
    φ (algebraMap R (O ⧸ Ring.jacobson O) r) =
      algebraMap (IsLocalRing.ResidueField R) A (IsLocalRing.residue R r)

/-- **The Eichler symbol** (Voight 2021, Definition 24.3.2): for an $R$-order $\mathcal O$ over the local ring $R$ with
residue field $k$ and $J = \operatorname{rad}\mathcal O$, `HasEichlerSymbol R O s` says $(\mathcal O \mid \mathfrak p) = s$:
* $s = *$: $\mathcal O/J$ is a quaternion algebra over $k$ (`Voight.IsQuaternionAlgebra`);
* $s = 1$: $\mathcal O/J \cong k \times k$ ($\mathcal O$ is **residually split**);
* $s = 0$: $\mathcal O/J \cong k$ ($\mathcal O$ is **residually ramified**);
* $s = -1$: $\mathcal O/J$ is a separable quadratic field extension of $k$ ($\mathcal O$ is **residually inert**).
All isomorphisms are of algebras over $R$ (`ResIso`). By 24.3.1 exactly one case occurs for a quaternion order; that
classification is not formalized here. Global version (Definition 24.3.13): apply this to the completion
$\mathcal O_{\mathfrak p}$. -/
@[kb "voight2021" "Definition 24.3.2, p. 400"]
def HasEichlerSymbol (O : Subalgebra R B) : EichlerSym → Prop
  | .star => ∃ (A : Type) (_ : Ring A) (_ : Algebra (IsLocalRing.ResidueField R) A),
      Voight.IsQuaternionAlgebra (IsLocalRing.ResidueField R) A ∧ ResIso R O A
  | .one => ResIso R O (IsLocalRing.ResidueField R × IsLocalRing.ResidueField R)
  | .zero => ResIso R O (IsLocalRing.ResidueField R)
  | .negOne => ∃ (L : Type) (_ : Field L) (_ : Algebra (IsLocalRing.ResidueField R) L),
      Module.finrank (IsLocalRing.ResidueField R) L = 2 ∧ Algebra.IsSeparable (IsLocalRing.ResidueField R) L ∧
        ResIso R O L

variable {R}

/-- `ResIso` is invariant under isomorphisms of $R$-algebras. -/
theorem ResIso.of_algEquiv {O : Subalgebra R B} {B' : Type} [Ring B'] [Algebra R B'] {O' : Subalgebra R B'}
    (f : O ≃ₐ[R] O') {A : Type} [Ring A] [Algebra (IsLocalRing.ResidueField R) A] (h : ResIso R O A) :
    ResIso R O' A := by
  obtain ⟨φ, hφ⟩ := h
  let g : (O ⧸ Ring.jacobson O) ≃ₐ[R] (O' ⧸ Ring.jacobson O') :=
    Ideal.quotientEquivAlg (Ring.jacobson O) (Ring.jacobson O') f (jacobson_eq_map (f : O ≃+* O'))
  refine ⟨(g.symm : (O' ⧸ Ring.jacobson O') ≃+* (O ⧸ Ring.jacobson O)).trans φ, fun r => ?_⟩
  rw [RingEquiv.trans_apply, ← hφ r]
  congr 1
  exact g.symm.commutes r

/-- **The Eichler symbol is an isomorphism invariant** of $R$-algebras. -/
theorem HasEichlerSymbol.of_algEquiv {O : Subalgebra R B} {B' : Type} [Ring B'] [Algebra R B']
    {O' : Subalgebra R B'} (f : O ≃ₐ[R] O') {s : EichlerSym} (h : HasEichlerSymbol R O s) :
    HasEichlerSymbol R O' s := by
  cases s with
  | star => obtain ⟨A, _, _, hA, hi⟩ := h; exact ⟨A, _, _, hA, hi.of_algEquiv f⟩
  | one => exact ResIso.of_algEquiv f h
  | zero => exact ResIso.of_algEquiv f h
  | negOne => obtain ⟨L, _, _, h2, hs, hi⟩ := h; exact ⟨L, _, _, h2, hs, hi.of_algEquiv f⟩

end Def

/-! ## The radical of the standard Eichler order -/

section Standard

variable {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- An element of $\mathcal O_0(\pi^e)$ whose determinant is a unit of $R$ is a unit of $\mathcal O_0(\pi^e)$ (the inverse
$\det(x)^{-1}\operatorname{adj}(x)$ has lower left entry $-\det(x)^{-1}x_{10} \in \pi^eR$). -/
theorem isUnit_of_isUnit_det {π : R} {e : ℕ} (x : stdEichlerOrder R K π e) (h : IsUnit (intMat x).det) :
    IsUnit x := by
  set A := intMat x with hA
  set u := h.unit
  set A' : Matrix (Fin 2) (Fin 2) R := ((u⁻¹ : Rˣ) : R) • A.adjugate
  have hAA' : A * A' = 1 := by
    simp only [A', Matrix.mul_smul, Matrix.mul_adjugate, smul_smul]
    rw [show ((u⁻¹ : Rˣ) : R) * A.det = 1 by rw [show A.det = (u : R) from h.unit_spec.symm]; exact u.inv_mul]
    exact one_smul _ _
  have hA'A : A' * A = 1 := by
    simp only [A', Matrix.smul_mul, Matrix.adjugate_mul, smul_smul]
    rw [show ((u⁻¹ : Rˣ) : R) * A.det = 1 by rw [show A.det = (u : R) from h.unit_spec.symm]; exact u.inv_mul]
    exact one_smul _ _
  obtain ⟨c, hc⟩ := pow_dvd_intMat_one_zero x
  have hmem : A'.map (algebraMap R K) ∈ stdEichlerOrder R K π e := by
    rw [mem_stdEichlerOrder]
    refine ⟨fun i j => ⟨A' i j, rfl⟩, -(((u⁻¹ : Rˣ) : R) * c), ?_⟩
    simp only [A', Matrix.map_apply, Matrix.smul_apply, Matrix.adjugate_fin_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
      smul_eq_mul]
    have hc' : A 1 0 = π ^ e * c := hc
    rw [hc']
    congr 1
    ring
  have hx : (x : Matrix (Fin 2) (Fin 2) K) = A.map (algebraMap R K) := (intMat_map x).symm
  refine ⟨⟨x, ⟨_, hmem⟩, ?_, ?_⟩, rfl⟩
  · apply Subtype.ext
    change (x : Matrix (Fin 2) (Fin 2) K) * A'.map (algebraMap R K) = 1
    rw [hx, ← Matrix.map_mul, hAA', Matrix.map_one _ (map_zero _) (map_one _)]
  · apply Subtype.ext
    change A'.map (algebraMap R K) * (x : Matrix (Fin 2) (Fin 2) K) = 1
    rw [hx, ← Matrix.map_mul, hA'A, Matrix.map_one _ (map_zero _) (map_one _)]

variable [IsLocalRing R]

/-- The integral matrix of $1 \in \mathcal O_0(\pi^e)$ is the identity. -/
theorem intMat_add_one {π : R} {e : ℕ} (x : stdEichlerOrder R K π e) : intMat (x + 1) = intMat x + 1 := by
  rw [intMat_add, intMat_one]

/-- **The radical of the standard Eichler order** (Voight 2021, 23.4.15 and (23.4.17)): for $e \ge 1$ and $\pi$ in the
maximal ideal $\mathfrak p$ of the local domain $R$,
$$\operatorname{rad}\mathcal O_0(\pi^e) = J = \begin{pmatrix} \mathfrak p & R \\ \pi^eR & \mathfrak p\end{pmatrix}
= \ker\bigl(\mathcal O_0(\pi^e) \to k \times k\bigr),$$
the kernel of the residue map `eichlerRes` (so $\mathcal O_0(\pi^e)/\operatorname{rad} \cong k \times k$). -/
@[kb "voight2021" "23.4.15, (23.4.17), p. 385"]
theorem jacobson_stdEichlerOrder {π : R} (hπ : π ∈ IsLocalRing.maximalIdeal R) {e : ℕ} (he : 1 ≤ e) :
    Ring.jacobson (stdEichlerOrder R K π e) = RingHom.ker (eichlerRes (K := K) hπ he) := by
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker]
    exact map_eq_zero_of_mem_jacobson (A' := IsLocalRing.ResidueField R × IsLocalRing.ResidueField R)
      (eichlerRes (K := K) hπ he) (eichlerRes_surjective hπ he) (jacobson_prod_field (IsLocalRing.ResidueField R)) hx
  · intro x hx
    rw [mem_jacobson_iff_exists]
    intro y
    have hw : y * x ∈ RingHom.ker (eichlerRes (K := K) hπ he) := Ideal.mul_mem_left _ y hx
    rw [RingHom.mem_ker, eichlerRes_eq_zero_iff] at hw
    obtain ⟨h00, h11⟩ := hw
    obtain ⟨c, hc⟩ := pow_dvd_intMat_one_zero (y * x)
    have h10 : intMat (y * x) 1 0 ∈ IsLocalRing.maximalIdeal R := by
      rw [hc]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hπ _ (by omega))
    have hdet : IsUnit (intMat (y * x + 1)).det := by
      rw [intMat_add_one, Matrix.det_fin_two]
      simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
        Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), add_zero]
      set w := intMat (y * x)
      have ht : -(w 0 0 + w 1 1 + w 0 0 * w 1 1 - w 0 1 * w 1 0) ∈ IsLocalRing.maximalIdeal R := by
        refine neg_mem (Ideal.sub_mem _ (Ideal.add_mem _ (Ideal.add_mem _ h00 h11)
          (Ideal.mul_mem_right _ _ h00)) (Ideal.mul_mem_left _ _ h10))
      have := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ ht
      convert this using 1
      ring
    obtain ⟨v, hv⟩ := isUnit_of_isUnit_det (y * x + 1) hdet
    refine ⟨(↑v⁻¹ : stdEichlerOrder R K π e), ?_⟩
    rw [mul_assoc, ← mul_add_one, ← hv, Units.inv_mul]

/-- The residue map `eichlerRes` is compatible with the structure maps from $R$. -/
theorem eichlerRes_algebraMap {π : R} (hπ : π ∈ IsLocalRing.maximalIdeal R) {e : ℕ} (he : 1 ≤ e) (r : R) :
    eichlerRes (K := K) hπ he (algebraMap R (stdEichlerOrder R K π e) r) =
      algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R × IsLocalRing.ResidueField R)
        (IsLocalRing.residue R r) := by
  have h : ∀ i, intMat (algebraMap R (stdEichlerOrder R K π e) r) i i = r := fun i =>
    IsFractionRing.injective R K (by
      rw [algebraMap_intMat]
      simp [Matrix.algebraMap_matrix_apply])
  rw [eichlerRes_apply, h, h]
  rfl

/-- **The standard Eichler order of level $\pi^e$, $e \ge 1$, is residually split** (Voight 2021, (23.4.17) and
Definition 24.3.2): $(\mathcal O_0(\pi^e) \mid \mathfrak p) = 1$. -/
@[kb "voight2021" "(23.4.17), p. 385; Definition 24.3.2, p. 400"]
theorem hasEichlerSymbol_one_stdEichlerOrder {π : R} (hπ : π ∈ IsLocalRing.maximalIdeal R) {e : ℕ} (he : 1 ≤ e) :
    HasEichlerSymbol R (stdEichlerOrder R K π e) .one := by
  show ResIso R (stdEichlerOrder R K π e) (IsLocalRing.ResidueField R × IsLocalRing.ResidueField R)
  let φ₁ := Ideal.quotEquivOfEq (jacobson_stdEichlerOrder (K := K) hπ he)
  let φ₂ := RingHom.quotientKerEquivOfSurjective (eichlerRes_surjective (K := K) hπ he)
  refine ⟨φ₁.trans φ₂, fun r => ?_⟩
  rw [RingEquiv.trans_apply]
  change φ₂ (φ₁ (Ideal.Quotient.mk _ (algebraMap R (stdEichlerOrder R K π e) r))) = _
  rw [Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]
  exact eichlerRes_algebraMap hπ he r

/-- $\mathcal O_0(\pi^0) = \mathrm M_2(R)$. -/
theorem stdEichlerOrder_zero (π : R) : stdEichlerOrder R K π 0 = matOrder R K := by
  ext x
  rw [mem_stdEichlerOrder, mem_matOrder]
  constructor
  · exact fun h => h.1
  · intro h
    obtain ⟨r, hr⟩ := h 1 0
    exact ⟨h, r, by rw [pow_zero, one_mul, hr]⟩

end Standard

section DVR

variable {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- **Lemma 24.3.6, "only if"** (Voight 2021): over a discrete valuation ring $R$, an Eichler order
$\mathcal O \subseteq \mathrm M_2(F)$ which is not maximal is residually split, $(\mathcal O \mid \mathfrak p) = 1$.
(Proof as in the book: $\mathcal O$ is conjugate to $\mathcal O_0(\pi^e)$, Proposition 23.4.3, with $e \ge 1$ as
$\mathcal O$ is not maximal, and then (23.4.17).) Completeness of $R$ is not needed. -/
@[kb "voight2021" "Lemma 24.3.6, p. 401"]
theorem IsEichler.hasEichlerSymbol_one {π : R} (hπ : Irreducible π)
    {O : Subalgebra R (Matrix (Fin 2) (Fin 2) K)} (hO : IsEichler R K O) (hmax : ¬ IsMaximalOrder R K O) :
    HasEichlerSymbol R O .one := by
  obtain ⟨e, P, Q, hPQ, hQP, rfl⟩ := (isEichler_iff_exists_conj hπ O).1 hO
  rcases Nat.eq_zero_or_pos e with rfl | he
  · exfalso
    apply hmax
    rw [stdEichlerOrder_zero]
    exact isMaximalOrder_matOrder.map (conjAlgEquiv P Q hPQ hQP)
  · have hπm : π ∈ IsLocalRing.maximalIdeal R := by
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ]
      exact Ideal.mem_span_singleton_self π
    exact (hasEichlerSymbol_one_stdEichlerOrder (K := K) hπm he).of_algEquiv
      (Subalgebra.equivMapOfInjective _ _ (conjAlgEquiv P Q hPQ hQP).injective)

end DVR

/-- **Lemma 24.3.6, "if"** (Voight 2021), as a named proposition about a complete discrete valuation ring $R$ with
fraction field $F$ and a quaternion algebra $B$ over $F$: every residually split $R$-order $\mathcal O \subseteq B$ is an
Eichler order. Stated, not proved: the book's proof lifts the orthogonal idempotents of $k \times k$ to $\mathcal O$
(Lemma 20.6.8, Hensel), which is not formalized here. -/
@[kb "voight2021" "Lemma 24.3.6, p. 401"]
def ResiduallySplitIsEichler (R F B : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Field F] [Algebra R F] [IsFractionRing R F] [Ring B] [Algebra F B] [Algebra R B] [IsScalarTower R F B] : Prop :=
  Voight.IsQuaternionAlgebra F B → ∀ O : Subalgebra R B, IsOrder R F O → HasEichlerSymbol R O .one → IsEichler R F O

end QuadFormsKB.Voight.Wave6
