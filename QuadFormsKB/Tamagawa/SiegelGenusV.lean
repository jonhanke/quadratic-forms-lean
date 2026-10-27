/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.SiegelQuadSpace
import QuadFormsKB.Lattices.FreeBridge

/-!
# The genus of a lattice intrinsically in a quadratic space, and Siegel's formula

**Layer:** $F$ a number field; $(V, q)$ a finite-dimensional quadratic space over $F$ (Mathlib's
`q : QuadraticForm F V`); $\mathcal O_F$-lattices $L, M \subseteq V$ (Mathlib's `Submodule.IsLattice F`).

**Definitions (no coordinates).**
* Classes: $L \cong M$ iff some isometry $\sigma \in O(V, q)$ has $\sigma L = M$ (`IsometricLattices q q`, reused from
  `Lattices/Basic.lean`); the classes form `LatClassV q`, a quotient of the type `LatV F V` of lattices in $V$.
* Completions: $V_\mathfrak p = F_\mathfrak p \otimes_F V$ with the base-changed form $q_\mathfrak p$ = `locFormV v q`
  (Mathlib's `QuadraticForm.baseChange`), and $L_\mathfrak p$ = `locLatV v L`, the $\mathfrak o_\mathfrak p$-span of
  $\{1 \otimes x : x \in L\}$ (the same construction as `Lattices.loc` on $F^n$).
* Genus (`SameGenusV`): for every finite prime $\mathfrak p$ some $\sigma_\mathfrak p \in O(V_\mathfrak p, q_\mathfrak p)$ has
  $\sigma_\mathfrak p L_\mathfrak p = M_\mathfrak p$ (O'Meara §102A, p. 297).
* $O(M)$ = `autLatV q M` (reused), $r_M(t) = \#\{x \in M : q(x) = t\}$ = `repCountV`, the classes in the genus
  `genusClassesV q L`, and
  $$\mathtt{massGenV}\ q\ L = \sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac1{|O(M)|},\qquad
  \mathtt{repMassGenV}\ q\ L\ t = \sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{r_M(t)}{|O(M)|}.$$
  As everywhere in the library (`Lattices.mass`), classes and weights use the **full** orthogonal group: improper
  isometries
  are included both in the class relation and in $O(M)$.

**Proves.** For every basis $e$ of $V$, $M \mapsto$ `coordLat e M` induces a bijection (`genusClassesV_bijOn`) from the
intrinsic classes in the genus of $L$ onto `genusClasses (coordForm q e) (coordLat e L)`, preserving $|O(M)|$
(`autCard_classCoord`) and $r_M(t)$ (`repCount_classCoord`); finiteness transfers (`genusClassesV_finite`). Hence
`massGenV_eq_massV`, `repMassGenV_eq_repMassV` (no hypotheses), and the Siegel headlines restated with the
intrinsic quantities: `siegelFormula_quadraticSpace_intrinsic` ($\dim V \ge 4$),
`siegelFormula{3,2,1}_quadraticSpace_intrinsic`, `siegelFormula{3,2}_quadraticSpace_natural_intrinsic`.

The coordinate dictionary: an isometry $\sigma$ of $(W, q_W)$ and a $K$-linear iso $\varphi : W \cong K^n$ with
$q_W = Q \circ \varphi$ give the matrix $\varphi\sigma\varphi^{-1} \in O(Q)(K)$ and back (`coordOrth`, `orthIso`), used for
$K = F$ (global classes, $O(M)$) and $K = F_\mathfrak p$ (genus; $\varphi$ = the base change of $e$).

Source: O'Meara 1963, §82C, pp. 222–223 (cls, O(L)), §102A, p. 297 (gen); Siegel 1935 [unverified].
-/

open NumberField IsDedekindDomain Module Matrix TensorProduct

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.SiegelSpace

open QuadFormsKB.Lattices QuadFormsKB.QuadForm QuadFormsKB.NFEuler QuadFormsKB.RegProd QuadFormsKB.LocalDensity
open QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F]

/-! ### The coordinate dictionary for isometries -/

section CoordIso

variable {n : ℕ} {K : Type*} [Field K] [CharZero K] [Algebra F K]

/-- The matrix (as an element of $\mathrm{GL}_n(K)$) of a linear automorphism of $K^n$. -/
def glOfEquiv (f : (Fin n → K) ≃ₗ[K] (Fin n → K)) : GL (Fin n) K :=
  ⟨LinearMap.toMatrix' f.toLinearMap, LinearMap.toMatrix' f.symm.toLinearMap,
    by rw [← LinearMap.toMatrix'_comp]; simp, by rw [← LinearMap.toMatrix'_comp]; simp⟩

theorem glOfEquiv_mulVec (f : (Fin n → K) ≃ₗ[K] (Fin n → K)) (x : Fin n → K) :
    (glOfEquiv f).val *ᵥ x = f x :=
  LinearMap.toMatrix'_mulVec _ _

/-- The linear automorphism $x \mapsto \gamma x$ of $K^n$. -/
def equivOfGL (γ : GL (Fin n) K) : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
  { Matrix.mulVecLin γ.val with
    invFun := fun x => γ⁻¹.val *ᵥ x
    left_inv := fun x => by simp [mulVec_mulVec]
    right_inv := fun x => by simp [mulVec_mulVec] }

theorem equivOfGL_apply (γ : GL (Fin n) K) (x : Fin n → K) : equivOfGL γ x = γ.val *ᵥ x := rfl

variable {W : Type*} [AddCommGroup W] [Module K W] {Q : QuadForm F n} {qW : QuadraticForm K W}
  {φ : W ≃ₗ[K] (Fin n → K)}

/-- **The matrix of an isometry** in coordinates $\varphi$ with $q_W = Q\circ\varphi$: $\varphi\sigma\varphi^{-1} \in O(Q)(K)$. -/
def coordOrth (hφ : ∀ w, qW w = Q.evalIn K (φ w)) (σ : qW.IsometryEquiv qW) : orthGroup Q K :=
  ⟨glOfEquiv (φ.symm ≪≫ₗ σ.toLinearEquiv ≪≫ₗ φ), mem_orthGroup_of_evalIn Q fun z => by
    rw [glOfEquiv_mulVec, LinearEquiv.trans_apply, LinearEquiv.trans_apply, ← hφ]
    conv_rhs => rw [← φ.apply_symm_apply z, ← hφ]
    exact σ.map_app (φ.symm z)⟩

theorem coordOrth_mulVec (hφ : ∀ w, qW w = Q.evalIn K (φ w)) (σ : qW.IsometryEquiv qW) (w : W) :
    (coordOrth hφ σ : GL (Fin n) K).val *ᵥ φ w = φ (σ w) := by
  simp [coordOrth, glOfEquiv_mulVec]

/-- **The isometry of a matrix** $\gamma \in O(Q)(K)$ in coordinates $\varphi$: $\varphi^{-1}\gamma\varphi$. -/
def orthIso (hφ : ∀ w, qW w = Q.evalIn K (φ w)) (γ : orthGroup Q K) : qW.IsometryEquiv qW where
  toLinearEquiv := φ ≪≫ₗ equivOfGL (γ : GL (Fin n) K) ≪≫ₗ φ.symm
  map_app' w := by
    change qW (φ.symm ((γ : GL (Fin n) K).val *ᵥ φ w)) = qW w
    rw [hφ, hφ, φ.apply_symm_apply, evalIn_mulVec_of_mem Q γ.2]

theorem orthIso_apply (hφ : ∀ w, qW w = Q.evalIn K (φ w)) (γ : orthGroup Q K) (w : W) :
    φ (orthIso hφ γ w) = (γ : GL (Fin n) K).val *ᵥ φ w := by
  change φ (φ.symm _) = _
  rw [φ.apply_symm_apply]; rfl

/-- **Transport of submodules:** if $\gamma\varphi = \varphi f$ then $\varphi(fN) = \gamma\varphi(N)$, over any coefficient
ring $S$ of $K$. -/
theorem map_coord_conj {S : Type*} [CommRing S] [Algebra S K] [Module S W] [IsScalarTower S K W]
    (N : Submodule S W) (f : W ≃ₗ[K] W) (γ : GL (Fin n) K) (h : ∀ w, γ.val *ᵥ φ w = φ (f w)) :
    (N.map (f.toLinearMap.restrictScalars S)).map (φ.toLinearMap.restrictScalars S) =
      (N.map (φ.toLinearMap.restrictScalars S)).map ((Matrix.mulVecLin γ.val).restrictScalars S) := by
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  refine LinearMap.ext fun w => ?_
  simp [h]

theorem map_coord_injective {S : Type*} [CommRing S] [Algebra S K] [Module S W] [IsScalarTower S K W] :
    Function.Injective (Submodule.map (φ.toLinearMap.restrictScalars S)) :=
  Submodule.map_injective_of_injective (f := φ.toLinearMap.restrictScalars S) φ.injective

end CoordIso

variable {V : Type*} [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V]

/-! ### Completions of an abstract quadratic space and the intrinsic genus -/

section Genus

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **The completed quadratic space** $(V_\mathfrak p, q_\mathfrak p) = (F_\mathfrak p \otimes_F V,\ q \otimes F_\mathfrak p)$ at a
finite prime $\mathfrak p$ (Mathlib's `QuadraticForm.baseChange`; O'Meara §66, p. 186). -/
@[kb "omeara1963" "§66, p. 186 (localization V_𝔭)"]
def locFormV (q : QuadraticForm F V) : QuadraticForm Fv (Fv ⊗[F] V) := q.baseChange Fv

/-- **The localization** $L_\mathfrak p = \mathfrak o_\mathfrak p L \subseteq V_\mathfrak p$: the $\mathfrak o_\mathfrak p$-span of
$\{1 \otimes x : x \in L\}$ (the intrinsic version of `Lattices.loc`; O'Meara §81E, p. 217). -/
@[kb "omeara1963" "§81E, p. 217 (localization L_𝔭)"]
def locLatV (L : Submodule (𝓞 F) V) : Submodule 𝔬 (Fv ⊗[F] V) :=
  Submodule.span 𝔬 ((fun x : V => (1 : Fv) ⊗ₜ[F] x) '' L)

variable {v} in
/-- **Same genus, intrinsically in $V$:** for every finite prime $\mathfrak p$ of the number field $F$ some isometry
$\sigma_\mathfrak p \in O(V_\mathfrak p, q_\mathfrak p)$ (proper or improper) carries $L_\mathfrak p$ onto $M_\mathfrak p$
(O'Meara §102A, p. 297). At the infinite places $L$ and $M$ span the same space, so nothing is required there. -/
@[kb "omeara1963" "§102A, p. 297 (gen L)"]
def SameGenusV (q : QuadraticForm F V) (L M : Submodule (𝓞 F) V) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F), ∃ σ : (locFormV v q).IsometryEquiv (locFormV v q),
    (locLatV v L).map (σ.toLinearEquiv.toLinearMap.restrictScalars (v.adicCompletionIntegers F)) = locLatV v M

variable {n : ℕ}

theorem baseChange_equivFun_tmul (e : Basis (Fin n) F V) (x : V) :
    (e.baseChange Fv).equivFun ((1 : Fv) ⊗ₜ[F] x) = locVec v (e.equivFun x) := by
  funext i
  simp [Basis.equivFun_apply, Algebra.algebraMap_eq_smul_one]

/-- **The completed form in coordinates:** $q_\mathfrak p(w) = Q_e(\varphi_e(w))$ with $\varphi_e$ the base change of $e$. -/
theorem locFormV_eq_coord (q : QuadraticForm F V) (e : Basis (Fin n) F V) (w : Fv ⊗[F] V) :
    locFormV v q w = (coordForm q e).evalIn Fv ((e.baseChange Fv).equivFun w) := by
  have h : locFormV v q = ((coordForm q e).map (algebraMap F Fv)).toQuadraticForm.comp
      (e.baseChange Fv).equivFun.toLinearMap := by
    apply baseChange_ext
    intro x
    rw [locFormV, QuadraticForm.baseChange_tmul, QuadraticMap.comp_apply, LinearEquiv.coe_coe,
      toQuadraticForm_apply, ← evalIn_eq_eval_map, baseChange_equivFun_tmul, evalIn_locVec, eval_coordForm,
      LinearEquiv.symm_apply_apply, mul_one, Algebra.algebraMap_eq_smul_one]
  rw [h, QuadraticMap.comp_apply, LinearEquiv.coe_coe, toQuadraticForm_apply, ← evalIn_eq_eval_map]

/-- **Localization in coordinates:** $\varphi_e(L_\mathfrak p) = (e^*L)_\mathfrak p$. -/
theorem locLatV_map_coord (e : Basis (Fin n) F V) (L : Submodule (𝓞 F) V) :
    (locLatV v L).map ((e.baseChange Fv).equivFun.toLinearMap.restrictScalars 𝔬) = loc v (coordLatSub e L) := by
  rw [locLatV, Submodule.map_span, loc, coordLatSub, Submodule.map_coe, Set.image_image, Set.image_image]
  congr 1
  refine Set.image_congr fun x _ => ?_
  exact baseChange_equivFun_tmul v e x

variable {q : QuadraticForm F V}

/-- **The intrinsic genus is the coordinate genus** (any basis $e$). -/
theorem sameGenusV_iff_coord (e : Basis (Fin n) F V) (L M : Submodule (𝓞 F) V) :
    SameGenusV q L M ↔ SameGenus (coordForm q e) (coordLatSub e L) (coordLatSub e M) := by
  constructor
  · intro h v
    obtain ⟨σ, hσ⟩ := h v
    have hφ := locFormV_eq_coord v q e
    set γ : orthGroup (coordForm q e) (v.adicCompletion F) := coordOrth hφ σ with hγ
    refine ⟨γ.1, γ.2, ?_⟩
    rw [← locLatV_map_coord, ← locLatV_map_coord, locAct, ← map_coord_conj _ _ _ (coordOrth_mulVec hφ σ)]
    rw [← hσ]
  · intro h v
    obtain ⟨g, hg, hgL⟩ := h v
    have hφ := locFormV_eq_coord v q e
    refine ⟨orthIso hφ ⟨g, hg⟩, map_coord_injective (φ := (e.baseChange (v.adicCompletion F)).equivFun) ?_⟩
    rw [map_coord_conj _ _ g (fun w => (orthIso_apply hφ ⟨g, hg⟩ w).symm), locLatV_map_coord,
      locLatV_map_coord]
    exact hgL

end Genus

/-! ### Global isometries, automorphism groups, representation numbers in coordinates -/

section Global

variable {n : ℕ} {q : QuadraticForm F V}

theorem coordForm_hφ (q : QuadraticForm F V) (e : Basis (Fin n) F V) (x : V) :
    q x = (coordForm q e).evalIn F (e.equivFun x) := by
  rw [← QuadForm.eval, eval_coordForm, LinearEquiv.symm_apply_apply]

/-- **Isometric in $V$ iff isometric in coordinates** (any basis $e$). -/
theorem isometricLattices_iff_coord (e : Basis (Fin n) F V) (L M : Submodule (𝓞 F) V) :
    IsometricLattices q q L M ↔ IsIsometric (coordForm q e) (coordLatSub e L) (coordLatSub e M) := by
  have hφ := coordForm_hφ q e
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨(coordOrth hφ σ : GL (Fin n) F), (coordOrth hφ σ).2,
      (map_coord_conj _ _ _ (coordOrth_mulVec hφ σ)).symm⟩
  · rintro ⟨g, hg, hgL⟩
    refine ⟨orthIso hφ ⟨g, hg⟩, map_coord_injective (φ := e.equivFun) ?_⟩
    exact (map_coord_conj _ _ g (fun w => (orthIso_apply hφ ⟨g, hg⟩ w).symm)).trans hgL

theorem IsometricLattices.trans' {L M N : Submodule (𝓞 F) V} (h₁ : IsometricLattices q q L M)
    (h₂ : IsometricLattices q q M N) : IsometricLattices q q L N := by
  obtain ⟨σ, rfl⟩ := h₁
  obtain ⟨τ, rfl⟩ := h₂
  exact ⟨σ.trans τ, by rw [← Submodule.map_comp]; rfl⟩

/-- **$O(V, q)$ in coordinates:** $g \mapsto [g]_e \in O(Q_e)(F)$, a bijection. -/
def orthVEquiv (e : Basis (Fin n) F V) : orthGroupV q ≃ orthGroup (coordForm q e) F where
  toFun g := coordOrth (coordForm_hφ q e) { toLinearEquiv := g.1, map_app' := g.2 }
  invFun γ := ⟨(orthIso (coordForm_hφ q e) γ).toLinearEquiv, (orthIso (coordForm_hφ q e) γ).map_app⟩
  left_inv g := by
    refine Subtype.ext (LinearEquiv.ext fun x => e.equivFun.injective ?_)
    exact (orthIso_apply (coordForm_hφ q e) _ x).trans (coordOrth_mulVec (coordForm_hφ q e) _ x)
  right_inv γ := by
    refine Subtype.ext (Units.ext (Matrix.toLin'.injective (LinearMap.ext fun y => ?_)))
    obtain ⟨x, rfl⟩ := e.equivFun.surjective y
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
    exact (coordOrth_mulVec (coordForm_hφ q e) _ x).trans (orthIso_apply (coordForm_hφ q e) γ x)

theorem orthVEquiv_mulVec (e : Basis (Fin n) F V) (g : orthGroupV q) (x : V) :
    ((orthVEquiv e g : orthGroup (coordForm q e) F) : GL (Fin n) F).val *ᵥ e.equivFun x = e.equivFun (g.1 x) :=
  coordOrth_mulVec (coordForm_hφ q e) _ x

/-- **$|O(M)|$ in coordinates:** $O(M) \cong O(e^*M)$. -/
theorem card_autLatV_eq_coord (e : Basis (Fin n) F V) (M : Submodule (𝓞 F) V) :
    Nat.card (autLatV q M) = Nat.card (autLat (coordForm q e) (coordLatSub e M)) := by
  refine Nat.card_congr (Equiv.subtypeEquiv (orthVEquiv e) fun g => ?_)
  change M.map ((g.1 : V ≃ₗ[F] V).toLinearMap.restrictScalars (𝓞 F)) = M ↔
    glImage _ (coordLatSub e M) = coordLatSub e M
  rw [glImage, coordLatSub, ← map_coord_conj M g.1 _ (orthVEquiv_mulVec e g)]
  exact ⟨fun h => by rw [h], fun h => map_coord_injective (φ := e.equivFun) h⟩

/-- **$r_M(t)$ in coordinates.** -/
theorem repCountV_eq_coord (e : Basis (Fin n) F V) (M : Submodule (𝓞 F) V) [M.IsLattice F] (t : F) :
    Nat.card {x : V // x ∈ M ∧ q x = t} = repCount (coordForm q e) (coordLat e M) t := by
  refine Nat.card_congr
    { toFun := fun x => ⟨e.equivFun x.1, ⟨x.1, x.2.1, rfl⟩, (coordForm_hφ q e x.1).symm.trans x.2.2⟩
      invFun := fun y => ⟨e.equivFun.symm y.1, ?_, ?_⟩
      left_inv := fun x => Subtype.ext (e.equivFun.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (e.equivFun.apply_symm_apply y.1) }
  · obtain ⟨x, hx, hxy⟩ := y.2.1
    rw [← hxy]
    simpa using hx
  · rw [coordForm_hφ q e, e.equivFun.apply_symm_apply]; exact y.2.2

/-- Every coordinate lattice comes from a lattice of $V$. -/
theorem exists_coordLatSub_eq (e : Basis (Fin n) F V) (M' : Lat F n) :
    ∃ M : Submodule (𝓞 F) V, ∃ _ : M.IsLattice F, coordLatSub e M = M'.1 := by
  refine ⟨M'.1.map (e.equivFun.symm.toLinearMap.restrictScalars (𝓞 F)), ?_, ?_⟩
  · refine ⟨M'.2.fg.map _, ?_⟩
    rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, M'.2.span_eq_top,
      Submodule.map_top, LinearMap.range_eq_top]
    exact e.equivFun.symm.surjective
  · rw [coordLatSub, ← Submodule.map_comp]
    convert Submodule.map_id M'.1
    exact LinearMap.ext fun y => e.equivFun.apply_symm_apply y

end Global

/-! ### Classes in the genus, the intrinsic mass and representation mass -/

section Classes

variable (F V) in
/-- **The lattices of $V$:** $\mathcal O_F$-submodules $L \subseteq V$ with `Submodule.IsLattice F L`. -/
abbrev LatV : Type _ := {L : Submodule (𝓞 F) V // L.IsLattice F}

/-- **Isometry of lattices of $(V, q)$** (`IsometricLattices q q`, full orthogonal group) as a setoid on `LatV F V`. -/
def latSetoidV (q : QuadraticForm F V) : Setoid (LatV F V) where
  r L M := IsometricLattices q q L.1 M.1
  iseqv := ⟨fun L => IsometricLattices.refl q L.1, fun h => IsometricLattices.symm h,
    fun h h' => IsometricLattices.trans' h h'⟩

/-- **Classes of lattices** of $(V, q)$: lattices up to isometry by $O(V, q)$ (improper isometries included). -/
abbrev LatClassV (q : QuadraticForm F V) : Type _ := Quotient (latSetoidV q)

/-- **The classes in the genus of $L$** in $(V, q)$: $\{\mathrm{cls}(M) : M \in \mathrm{gen}(L)\}$ (O'Meara §102A,
p. 297). -/
@[kb "omeara1963" "§102A, p. 298"]
def genusClassesV (q : QuadraticForm F V) (L : Submodule (𝓞 F) V) : Set (LatClassV q) :=
  {c | ∃ M : LatV F V, Quotient.mk _ M = c ∧ SameGenusV q L M.1}

/-- **The representation number** $r_M(t) = \#\{x \in M : q(x) = t\}$ (a `Nat.card`; finite for totally positive definite
$q$ and integral $M$). -/
@[kb "omeara1963" "§82A, p. 220 (representations)"]
def repCountV (q : QuadraticForm F V) (M : Submodule (𝓞 F) V) (t : F) : ℕ :=
  Nat.card {x : V // x ∈ M ∧ q x = t}

variable {n : ℕ} {q : QuadraticForm F V}

/-- The coordinate lattice of a lattice of $V$ (`coordLat` with the lattice proof carried along). -/
def coordLatV (e : Basis (Fin n) F V) (M : LatV F V) : Lat F n :=
  ⟨coordLatSub e M.1, coordLatSub_isLattice e M.1 (hL := M.2)⟩

theorem card_autLatV_eq_of_isometric [FiniteDimensional F V] {M M' : Submodule (𝓞 F) V}
    (h : IsometricLattices q q M M') : Nat.card (autLatV q M) = Nat.card (autLatV q M') := by
  rw [card_autLatV_eq_coord (finBasis F V), card_autLatV_eq_coord (finBasis F V)]
  exact card_autLat_eq_of_isIsometric _ ((isometricLattices_iff_coord (finBasis F V) M M').mp h)

theorem repCountV_eq_coordLatV (e : Basis (Fin n) F V) (M : LatV F V) (t : F) :
    repCountV q M.1 t = repCount (coordForm q e) (coordLatV e M) t :=
  haveI := M.2
  repCountV_eq_coord e M.1 t

theorem repCountV_eq_of_isometric [FiniteDimensional F V] {M M' : LatV F V} (h : IsometricLattices q q M.1 M'.1)
    (t : F) : repCountV q M.1 t = repCountV q M'.1 t := by
  rw [repCountV_eq_coordLatV (finBasis F V), repCountV_eq_coordLatV (finBasis F V)]
  exact repCount_of_isIsometric _ ((isometricLattices_iff_coord (finBasis F V) M.1 M'.1).mp h) t

variable [FiniteDimensional F V]

variable (q) in
/-- **$|O(M)|$ of a class** of $(V, q)$, $O(M)$ = `autLatV q M` including improper automorphisms (well defined by
`card_autLatV_eq_of_isometric`). -/
def LatClassV.autCard (c : LatClassV q) : ℕ :=
  Quotient.lift (fun M : LatV F V => Nat.card (autLatV q M.1)) (fun _ _ h => card_autLatV_eq_of_isometric h) c

variable (q) in
/-- **$r_M(t)$ of a class** of $(V, q)$ (well defined by `repCountV_eq_of_isometric`). -/
def LatClassV.repCount (c : LatClassV q) (t : F) : ℕ :=
  Quotient.lift (fun M : LatV F V => repCountV q M.1 t) (fun _ _ h => repCountV_eq_of_isometric h t) c

variable (q) in
/-- **The mass of the genus of $L$, intrinsically in $(V, q)$:**
$$\mathtt{massGenV}\ q\ L = \sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac1{|O(M)|},$$
a `finsum` over the intrinsic classes in the intrinsic genus (`genusClassesV`), with $O(M)$ the full automorphism group
(improper isometries included, as in `Lattices.mass`). Equal to the coordinate `massV` (`massGenV_eq_massV`). O'Meara
(§102A, p. 298) counts the classes, $h(L)$, but does not treat the mass. -/
@[kb "omeara1963" "§102A, p. 298"]
def massGenV (L : Submodule (𝓞 F) V) : ℝ :=
  ∑ᶠ c ∈ genusClassesV q L, ((LatClassV.autCard q c : ℝ))⁻¹

variable (q) in
/-- **The weighted representation number of the genus of $L$, intrinsically in $(V, q)$:**
$$\mathtt{repMassGenV}\ q\ L\ t = \sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{r_M(t)}{|O(M)|}$$
(full $O(M)$, as in `Tamagawa.repMass`). Equal to the coordinate `repMassV` (`repMassGenV_eq_repMassV`). -/
@[kb "siegel1935" "§1 (genus average) [unverified]"]
def repMassGenV (L : Submodule (𝓞 F) V) (t : F) : ℝ :=
  ∑ᶠ c ∈ genusClassesV q L, (LatClassV.repCount q c t : ℝ) / LatClassV.autCard q c

/-- **The coordinate map on classes**, $\mathrm{cls}(M) \mapsto \mathrm{cls}(e^*M)$. -/
def classCoord (e : Basis (Fin n) F V) : LatClassV q → LatClass (coordForm q e) :=
  Quotient.map (coordLatV e) fun M M' h => (isometricLattices_iff_coord e M.1 M'.1).mp h

theorem classCoord_mk (e : Basis (Fin n) F V) (M : LatV F V) :
    classCoord e (Quotient.mk _ M : LatClassV q) = Quotient.mk _ (coordLatV e M) := rfl

theorem classCoord_injective (e : Basis (Fin n) F V) : Function.Injective (classCoord (q := q) e) := by
  intro c c' h
  induction c using Quotient.inductionOn
  induction c' using Quotient.inductionOn
  rw [classCoord_mk, classCoord_mk] at h
  exact Quotient.sound ((isometricLattices_iff_coord e _ _).mpr (Quotient.exact h))

theorem autCard_classCoord (e : Basis (Fin n) F V) (c : LatClassV q) :
    LatClass.autCard (coordForm q e) (classCoord e c) = LatClassV.autCard q c := by
  induction c using Quotient.inductionOn with
  | h M => exact (card_autLatV_eq_coord e M.1).symm

theorem repCount_classCoord (e : Basis (Fin n) F V) (c : LatClassV q) (t : F) :
    LatClass.repCount (coordForm q e) (classCoord e c) t = LatClassV.repCount q c t := by
  induction c using Quotient.inductionOn with
  | h M => exact (repCountV_eq_coordLatV e M t).symm

/-- **The classes in the intrinsic genus correspond to the coordinate classes in the genus** (any basis $e$). -/
theorem image_genusClassesV (e : Basis (Fin n) F V) (L : Submodule (𝓞 F) V) [L.IsLattice F] :
    classCoord e '' genusClassesV q L = genusClasses (coordForm q e) (coordLat e L) := by
  ext c
  constructor
  · rintro ⟨_, ⟨M, rfl, hM⟩, rfl⟩
    exact ⟨coordLatV e M, rfl, (sameGenusV_iff_coord e L M.1).mp hM⟩
  · rintro ⟨M', rfl, hM'⟩
    obtain ⟨M, hM, hMe⟩ := exists_coordLatSub_eq e M'
    have hc : coordLatV e ⟨M, hM⟩ = M' := Subtype.ext hMe
    refine ⟨Quotient.mk _ ⟨M, hM⟩, ⟨⟨M, hM⟩, rfl, ?_⟩, by rw [classCoord_mk, hc]⟩
    exact (sameGenusV_iff_coord e L M).mpr (by rw [hMe]; exact hM')

/-- **The bijection of genus classes** $\mathrm{cls}(M) \mapsto \mathrm{cls}(e^*M)$ from the intrinsic classes in the genus of
$L$ onto `genusClasses (coordForm q e) (coordLat e L)`, for any basis $e$ of $V$. -/
theorem genusClassesV_bijOn (e : Basis (Fin n) F V) (L : Submodule (𝓞 F) V) [L.IsLattice F] :
    Set.BijOn (classCoord e) (genusClassesV q L) (genusClasses (coordForm q e) (coordLat e L)) := by
  rw [← image_genusClassesV e L]
  exact (classCoord_injective e).injOn.bijOn_image

/-- **Finiteness of the intrinsic class number** (O'Meara 103:4, p. 309) for a totally positive definite space and
an integral lattice, transported from `genusClasses_finite`. -/
@[kb "omeara1963" "§103, 103:4, p. 309"]
theorem genusClassesV_finite (hq : IsTotallyPosDefV q) {L : Submodule (𝓞 F) V} [L.IsLattice F]
    (hLi : IsIntegralLattice q L) : (genusClassesV q L).Finite := by
  refine Set.Finite.of_finite_image ?_ (classCoord_injective (q := q) (finBasis F V)).injOn
  rw [image_genusClassesV]
  exact genusClasses_finite (isTotallyPosDef_coordForm hq _) _ (isIntegral_coordLat hLi _)

/-- **The intrinsic mass is the coordinate mass** in any basis $e$. -/
theorem massGenV_eq_mass (e : Basis (Fin n) F V) (L : Submodule (𝓞 F) V) [L.IsLattice F] :
    massGenV q L = mass (coordForm q e) (coordLat e L) := by
  rw [mass, ← image_genusClassesV e L, finsum_mem_image (classCoord_injective e).injOn, massGenV]
  exact finsum_mem_congr rfl fun c _ => by rw [autCard_classCoord]

/-- **The intrinsic representation mass is the coordinate one** in any basis $e$. -/
theorem repMassGenV_eq_repMass (e : Basis (Fin n) F V) (L : Submodule (𝓞 F) V) [L.IsLattice F] (t : F) :
    repMassGenV q L t = repMass (coordForm q e) (coordLat e L) t := by
  rw [repMass, ← image_genusClassesV e L, finsum_mem_image (classCoord_injective e).injOn, repMassGenV]
  exact finsum_mem_congr rfl fun c _ => by rw [autCard_classCoord, repCount_classCoord]

/-- **`massGenV = massV`:** the mass of the intrinsic genus of $L$ in $(V, q)$ is the `massV`. -/
theorem massGenV_eq_massV (L : Submodule (𝓞 F) V) [L.IsLattice F] : massGenV q L = massV q L :=
  massGenV_eq_mass (finBasis F V) L

/-- **`repMassGenV = repMassV`:** the intrinsic weighted representation number is the `repMassV`. -/
theorem repMassGenV_eq_repMassV (L : Submodule (𝓞 F) V) [L.IsLattice F] (t : F) :
    repMassGenV q L t = repMassV q L t :=
  repMassGenV_eq_repMass (finBasis F V) L t

end Classes

/-! ### The headlines with the intrinsic genus -/

section Headlines

variable [IsTotallyReal F] [FiniteDimensional F V] {q : QuadraticForm F V} {L : Submodule (𝓞 F) V} [L.IsLattice F]

/-- **Siegel's formula for an abstract quadratic space, intrinsic genus, $\dim V \ge 4$** (unconditional; Siegel 1935,
Hauptsatz; over a totally real number field $F$: Siegel 1937 [unverified]): for every totally positive definite quadratic
space $(V, q)$ over $F$ of dimension $\ge 4$, every $\mathcal O_F$-lattice $L \subseteq V$ with $q$ integral on $L$ and every
totally positive $m \in \mathcal O_F$,
$$\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{r_M(m)}{|O(M)|}
  = \Big(\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac1{|O(M)|}\Big)\cdot S(L, m),$$
where classes, genus and $O(M)$ are defined in $V$ itself (`genusClassesV`, `SameGenusV` via
$V_\mathfrak p = F_\mathfrak p\otimes_F V$, `autLatV`; improper isometries included). From
`siegelFormula_quadraticSpace_totallyReal` and `massGenV_eq_massV`, `repMassGenV_eq_repMassV`. -/
@[kb "siegel1935" "Hauptsatz, abstract quadratic space, intrinsic genus, totally real field [unverified for F]"]
theorem siegelFormula_quadraticSpace_intrinsic (hN : 4 ≤ finrank F V) (hq : IsTotallyPosDefV q)
    (hLi : IsIntegralLattice q L) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    repMassGenV q L (algebraMap (𝓞 F) F m) = massGenV q L * siegelProductV q L m := by
  rw [repMassGenV_eq_repMassV, massGenV_eq_massV]
  exact siegelFormula_quadraticSpace_totallyReal hN hq hLi hm

/-- **Ternary, intrinsic genus** (unconditional; regularized with $\chi_m$):
$\mathtt{repMassGenV} = \mathtt{massGenV}\cdot S_3(L, m)$. -/
@[kb "siegel1935" "Hauptsatz, n = 3, abstract quadratic space, intrinsic genus [unverified for F]"]
theorem siegelFormula3_quadraticSpace_intrinsic (h : finrank F V = 3) (hq : IsTotallyPosDefV q)
    (hLi : IsIntegralLattice q L) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    repMassGenV q L (algebraMap (𝓞 F) F m) = massGenV q L * siegelProduct3V q L h m := by
  rw [repMassGenV_eq_repMassV, massGenV_eq_massV]
  exact siegelFormula3_quadraticSpace_totallyReal h hq hLi hm

/-- **Binary, intrinsic genus** (unconditional; $\varepsilon = \tfrac12$, regularized with $\chi_q$):
$\mathtt{repMassGenV} = \tfrac12\,\mathtt{massGenV}\cdot S^{\mathrm{reg}}_2(L, m)$. -/
@[kb "siegel1935" "Hauptsatz, n = 2 (ε = 1/2), abstract quadratic space, intrinsic genus [unverified for F]"]
theorem siegelFormula2_quadraticSpace_intrinsic (h : finrank F V = 2) (hq : IsTotallyPosDefV q)
    (hLi : IsIntegralLattice q L) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    repMassGenV q L (algebraMap (𝓞 F) F m) = (1 / 2 : ℝ) * massGenV q L * siegelProduct2RegV q L h m := by
  rw [repMassGenV_eq_repMassV, massGenV_eq_massV]
  exact siegelFormula2_quadraticSpace_totallyReal h hq hLi hm

/-- **Unary, intrinsic genus** (unconditional; $\varepsilon = \tfrac12$):
$\mathtt{repMassGenV} = \mathtt{massGenV}\cdot 2\,\mathcal S_1(L, m)$. -/
@[kb "siegel1935" "Hauptsatz, n = 1 (ε = 1/2), abstract quadratic space, intrinsic genus [unverified for F]"]
theorem siegelFormula1_quadraticSpace_intrinsic (h : finrank F V = 1) (hq : IsTotallyPosDefV q)
    (hLi : IsIntegralLattice q L) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    repMassGenV q L (algebraMap (𝓞 F) F m) = massGenV q L * (2 * siegelProductOneV q L h m) := by
  rw [repMassGenV_eq_repMassV, massGenV_eq_massV]
  exact siegelFormula1_quadraticSpace_totallyReal h hq hLi hm

/-- **Ternary, natural order, intrinsic genus** (Hanke 2004, (5.3), p. 368, over $F$): in any basis $e$ of $V$, given
`NaturalOrderEulerOne` of $\chi_m$ (convention input), the natural-order Euler product converges to the regularized value
and Siegel's formula holds with the intrinsic mass and representation mass. -/
@[kb "hanke2004" "(5.3), p. 368 (n = 3, natural order), abstract quadratic space, intrinsic genus"]
theorem siegelFormula3_quadraticSpace_natural_intrinsic (h : finrank F V = 3) (hq : IsTotallyPosDefV q)
    (hLi : IsIntegralLattice q L) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m))
    (e : Basis (Fin 3) F V) (hN : NaturalOrderEulerOne (spaceChar3 (coordForm q e) m)) :
    HasProd (fun v => spaceBeta v (coordForm q e) (coordLat e L) m)
        (regProd (spaceChar3 (coordForm q e) m) 1 fun v => spaceBeta v (coordForm q e) (coordLat e L) m) (normOrder F) ∧
      repMassGenV q L (algebraMap (𝓞 F) F m) = massGenV q L * siegelProduct3V q L h m := by
  rw [repMassGenV_eq_repMassV, massGenV_eq_massV]
  exact siegelFormula3_quadraticSpace_natural h hq hLi hm e hN

/-- **Binary, natural order, intrinsic genus**: in any basis $e$ of $V$, given `NaturalOrderEulerOne` of $\chi_q$, the
natural-order Euler product converges to the regularized value and Siegel's formula holds with the intrinsic quantities. -/
@[kb "siegel1935" "Hauptsatz, n = 2 (natural order), abstract quadratic space, intrinsic genus [unverified]"]
theorem siegelFormula2_quadraticSpace_natural_intrinsic (h : finrank F V = 2) (hq : IsTotallyPosDefV q)
    (hLi : IsIntegralLattice q L) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m))
    (e : Basis (Fin 2) F V) (hN : NaturalOrderEulerOne (spaceChar2 (coordForm q e))) :
    HasProd (fun v => spaceBeta v (coordForm q e) (coordLat e L) m)
        (regProd (spaceChar2 (coordForm q e)) (-1) fun v => spaceBeta v (coordForm q e) (coordLat e L) m)
        (normOrder F) ∧
      repMassGenV q L (algebraMap (𝓞 F) F m) = (1 / 2 : ℝ) * massGenV q L * siegelProduct2RegV q L h m := by
  rw [repMassGenV_eq_repMassV, massGenV_eq_massV]
  exact siegelFormula2_quadraticSpace_natural h hq hLi hm e hN

end Headlines

end QuadFormsKB.Tamagawa.SiegelSpace
