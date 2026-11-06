/-
# O'Meara 93:28: adjoining an orthogonal lattice to two Jordan splittings

**Setting** (as in `Sec93Adj.lean`): $R$ a discrete valuation ring with fraction field $F$, $2 \in F^\times$; quadratic
spaces $(V, Q)$, $(W, Q_W)$ and their orthogonal sum $V \perp W$ = `V × W` with `Q.prod QW`; lattices
`Submodule R _`; $A \perp B$ for $A \subseteq V$, $B \subseteq W$ is `A.prod B`.

**Proves** (the adjunctions in the proof of 93:28, O'Meara 1963, pp. 270–272: "by making suitable hyperbolic
adjunctions ...", "make the adjunction of $J_1 \perp \cdots \perp J_t$", "the adjunction of the lattice $L^{-1}$")
* `scale_prod`, `normGroup_prod`, `subA_prod`, `isModular_prod`, `iSup_prod`: the invariants of $A \perp B$;
* `isJordanSplitting_prod`: if $L = L_1 \perp \cdots \perp L_t$ is a Jordan splitting and $H = H_1 \perp \cdots
  \perp H_t$ with $H_k$ $\mathfrak sL_k$-modular, then $L \perp H = (L_1 \perp H_1) \perp \cdots$ is a Jordan
  splitting;
* `fundNormGroup_prod`: if moreover $\mathfrak g(H^{\mathfrak s_k}) \subseteq \mathfrak g(L^{\mathfrak s_k})$, the
  fundamental norm groups (hence all fundamental invariants but the dimensions) are unchanged.
-/
import QuadFormsKB.Literature.OMeara.Sec93FTransfer
import QuadFormsKB.Literature.OMeara.Sec93SatProof

open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.Adjoin28

open Sat93 Transfer28

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {W : Type*} [AddCommGroup W] [Module F W] [Module R W] [IsScalarTower R F W]
variable (Q : QuadraticForm F V) (QW : QuadraticForm F W)

theorem prod_eq_sup (A : Submodule R V) (B : Submodule R W) :
    A.prod B = A.prod ⊥ ⊔ (⊥ : Submodule R V).prod B := by
  rw [Submodule.prod_sup_prod, sup_bot_eq, bot_sup_eq]

theorem bil_prod_bot (A : Submodule R V) (B : Submodule R W) :
    ∀ x ∈ A.prod (⊥ : Submodule R W), ∀ y ∈ (⊥ : Submodule R V).prod B, bil (Q.prod QW) x y = 0 :=
  (adj_isOrthSum_prod_split Q QW A B).orth

/-- $\mathfrak s(A \perp B) = \mathfrak sA + \mathfrak sB$. -/
theorem scale_prod (A : Submodule R V) (B : Submodule R W) :
    scale (Q.prod QW) (A.prod B) = scale Q A ⊔ scale QW B := by
  rw [prod_eq_sup, scale_sup_of_orth _ (bil_prod_bot Q QW A B)]
  have h1 := adj_isometricLat_prod_bot Q QW A
  have h2 := adj_isometricLat_bot_prod Q QW B
  rw [le_antisymm (adj_scale_le _ _ (adj_isometricLat_symm _ _ h1)) (adj_scale_le _ _ h1),
    le_antisymm (adj_scale_le _ _ (adj_isometricLat_symm _ _ h2)) (adj_scale_le _ _ h2)]

/-- $\mathfrak g(A \perp B) = \mathfrak gA + \mathfrak gB$ (O'Meara 1963, §93A, p. 252). -/
theorem normGroup_prod (A : Submodule R V) (B : Submodule R W) :
    normGroup (Q.prod QW) (A.prod B) = normGroup Q A ⊔ normGroup QW B := by
  rw [prod_eq_sup, normGroup_sup_of_orth _ (bil_prod_bot Q QW A B),
    ← adj_normGroup_eq _ _ (adj_isometricLat_prod_bot Q QW A),
    ← adj_normGroup_eq _ _ (adj_isometricLat_bot_prod Q QW B)]

/-- $(A \perp B)^{\mathfrak a} = A^{\mathfrak a} \perp B^{\mathfrak a}$. -/
theorem subA_prod (a : Submodule R F) (A : Submodule R V) (B : Submodule R W) :
    subA (Q.prod QW) a (A.prod B) = (subA Q a A).prod (subA QW a B) := by
  ext ⟨x, y⟩
  constructor
  · rintro ⟨⟨hx, hy⟩, h⟩
    refine ⟨⟨hx, fun x' hx' => ?_⟩, ⟨hy, fun y' hy' => ?_⟩⟩
    · have := h (x', 0) ⟨hx', zero_mem _⟩
      rwa [adj_bil_prod, show bil QW y 0 = 0 by simp [bil], add_zero] at this
    · have := h (0, y') ⟨zero_mem _, hy'⟩
      rwa [adj_bil_prod, show bil Q x 0 = 0 by simp [bil], zero_add] at this
  · rintro ⟨⟨hx, hxa⟩, ⟨hy, hya⟩⟩
    refine ⟨⟨hx, hy⟩, fun ⟨x', y'⟩ ⟨hx', hy'⟩ => ?_⟩
    rw [adj_bil_prod]
    exact add_mem (hxa x' hx') (hya y' hy')

/-- $A \perp B$ is $\mathfrak a$-modular when $A$ and $B$ are, of rank $\operatorname{rank} A + \operatorname{rank} B$. -/
theorem isModular_prod {a : Submodule R F} {A : Submodule R V} {B : Submodule R W} (hA : IsModular Q a A)
    (hB : IsModular QW a B) (hAfg : A.FG) (hBfg : B.FG) :
    IsModular (Q.prod QW) a (A.prod B) ∧ finrank R (A.prod B) = finrank R A + finrank R B := by
  have h1 := adj_isometricLat_prod_bot Q QW A
  have h2 := adj_isometricLat_bot_prod Q QW B
  have hA' := IsometricLat.isModular Q (Q.prod QW) h1 hAfg hA
  have hB' := IsometricLat.isModular QW (Q.prod QW) h2 hBfg hB
  have hA'fg : (A.prod (⊥ : Submodule R W)).FG := by rw [← Submodule.map_inl]; exact hAfg.map _
  have hB'fg : ((⊥ : Submodule R V).prod B).FG := by rw [← Submodule.map_inr]; exact hBfg.map _
  obtain ⟨hmod, hrk⟩ := isModular_sup (Q.prod QW) hA' hB' hA'fg hB'fg (bil_prod_bot Q QW A B)
  rw [← prod_eq_sup] at hmod hrk
  refine ⟨hmod, ?_⟩
  rw [hrk]
  obtain ⟨f₁, -⟩ := h1
  obtain ⟨f₂, -⟩ := h2
  rw [← f₁.finrank_eq, ← f₂.finrank_eq]

/-- $\bigvee_k (A_k \perp B_k) = (\bigvee_k A_k) \perp (\bigvee_k B_k)$. -/
theorem iSup_prod {ι : Sort*} (A : ι → Submodule R V) (B : ι → Submodule R W) :
    ⨆ k, (A k).prod (B k) = (⨆ k, A k).prod (⨆ k, B k) := by
  apply le_antisymm
  · exact iSup_le fun k => Submodule.prod_mono (le_iSup A k) (le_iSup B k)
  · rw [prod_eq_sup, ← Submodule.map_inl, ← Submodule.map_inr, Submodule.map_iSup, Submodule.map_iSup]
    refine sup_le (iSup_le fun k => ?_) (iSup_le fun k => ?_)
    · rw [Submodule.map_inl]
      exact (Submodule.prod_mono le_rfl bot_le).trans (le_iSup (fun k => (A k).prod (B k)) k)
    · rw [Submodule.map_inr]
      exact (Submodule.prod_mono bot_le le_rfl).trans (le_iSup (fun k => (A k).prod (B k)) k)

/-- **Adjoining a lattice with matching modular components** (O'Meara 1963, p. 270): if $L = L_1 \perp \cdots \perp
L_t$ is a Jordan splitting and $H = H_1 \perp \cdots \perp H_t$ is an orthogonal splitting with $H_k$
$\mathfrak sL_k$-modular, then $L \perp H = (L_1 \perp H_1) \perp \cdots \perp (L_t \perp H_t)$ is a Jordan splitting,
with $\dim(L_k \perp H_k) = \dim L_k + \dim H_k$. -/
theorem isJordanSplitting_prod {L : Submodule R V} {H : Submodule R W} (hLfg : L.FG) (hHfg : H.FG) {t : ℕ}
    {Ls : Fin t → Submodule R V} {Hs : Fin t → Submodule R W} (hL : IsJordanSplitting Q L Ls)
    (hH : IsOrthSplit QW H Hs) (hHmod : ∀ k, IsModular QW (scale Q (Ls k)) (Hs k)) :
    IsJordanSplitting (Q.prod QW) (L.prod H) (fun k => (Ls k).prod (Hs k)) ∧
      ∀ k, finrank R ((Ls k).prod (Hs k)) = finrank R (Ls k) + finrank R (Hs k) := by
  have hLk : ∀ k, (Ls k).FG := fun k => FG.of_le hLfg (hL.split.iSup_eq ▸ le_iSup Ls k)
  have hHk : ∀ k, (Hs k).FG := fun k => FG.of_le hHfg (hH.iSup_eq ▸ le_iSup Hs k)
  have hmod : ∀ k, IsModular (Q.prod QW) (scale Q (Ls k)) ((Ls k).prod (Hs k)) ∧
      finrank R ((Ls k).prod (Hs k)) = finrank R (Ls k) + finrank R (Hs k) := fun k =>
    isModular_prod Q QW (hL.modular k) (hHmod k) (hLk k) (hHk k)
  have hsc : ∀ k, scale (Q.prod QW) ((Ls k).prod (Hs k)) = scale Q (Ls k) := fun k => (hmod k).1.2.1
  have hor : ∀ j k, j ≠ k → ∀ x ∈ (Ls j).prod (Hs j), ∀ y ∈ (Ls k).prod (Hs k), bil (Q.prod QW) x y = 0 := by
    rintro j k hjk ⟨x₁, x₂⟩ ⟨hx₁, hx₂⟩ ⟨y₁, y₂⟩ ⟨hy₁, hy₂⟩
    rw [adj_bil_prod, hL.split.orth j k hjk _ hx₁ _ hy₁, hH.orth j k hjk _ hx₂ _ hy₂, add_zero]
  have hfg : (L.prod H).FG := by
    rw [prod_eq_sup, ← Submodule.map_inl, ← Submodule.map_inr]; exact (hLfg.map _).sup (hHfg.map _)
  have hle : ∀ k, (Ls k).prod (Hs k) ≤ L.prod H := fun k =>
    Submodule.prod_mono (hL.split.iSup_eq ▸ le_iSup Ls k) (hH.iSup_eq ▸ le_iSup Hs k)
  refine ⟨⟨⟨hor, iSupIndep_of_orth _ hor fun k => ?_, ?_⟩, fun k => ?_, ?_⟩, fun k => (hmod k).2⟩
  · exact (hmod k).1.isRegular _ (FG.of_le hfg (hle k))
  · rw [iSup_prod, hL.split.iSup_eq, hH.iSup_eq]
  · rw [hsc k]; exact (hmod k).1
  · have : (fun k => scale (Q.prod QW) ((Ls k).prod (Hs k))) = fun k => scale Q (Ls k) := funext hsc
    rw [this]; exact hL.scale_strictAnti

/-- **The fundamental norm groups are unchanged by the adjunction** when $\mathfrak g(H^{\mathfrak s_k}) \subseteq
\mathfrak g(L^{\mathfrak s_k})$: $\mathfrak g((L \perp H)^{\mathfrak s_k}) = \mathfrak g(L^{\mathfrak s_k}) +
\mathfrak g(H^{\mathfrak s_k})$. -/
theorem fundNormGroup_prod {L : Submodule R V} {H : Submodule R W} {t : ℕ} (Ls : Fin t → Submodule R V)
    (Hs : Fin t → Submodule R W)
    (hg : ∀ k, normGroup QW (subA QW (scale Q (Ls k)) H) ≤ normGroup Q (subA Q (scale Q (Ls k)) L)) (k : Fin t)
    (hsc : scale (Q.prod QW) ((Ls k).prod (Hs k)) = scale Q (Ls k)) :
    fundNormGroup (Q.prod QW) (L.prod H) (fun k => (Ls k).prod (Hs k)) k = fundNormGroup Q L Ls k := by
  simp only [fundNormGroup, fundSub]
  rw [hsc, subA_prod, normGroup_prod]
  exact sup_eq_left.mpr (hg k)

/-- The Jordan chains of $L \perp H$: $(L \perp H)_{(i)} = L_{(i)} \perp H_{(i)}$. -/
theorem jordanChain_prod {t : ℕ} (Ls : Fin t → Submodule R V) (Hs : Fin t → Submodule R W) (i : Fin t) :
    jordanChain (fun k => (Ls k).prod (Hs k)) i = (jordanChain Ls i).prod (jordanChain Hs i) := by
  simp only [jordanChain]
  rw [← iSup_prod]
  exact iSup_congr fun k => iSup_prod (fun _ : k ≤ i => Ls k) (fun _ => Hs k)

/-- $A \perp 0$ is regular when $A$ is. -/
theorem isRegular_prod_bot {A : Submodule R V} (hA : IsRegular Q A) :
    IsRegular (Q.prod QW) (A.prod (⊥ : Submodule R W)) := by
  rintro ⟨a, w⟩ ⟨ha, hw⟩ h
  have hw' : w = 0 := (mem_bot R).mp hw
  subst hw'
  have : a = 0 := hA a ha fun a' ha' => by
    have := h (a', 0) ⟨ha', zero_mem _⟩
    rwa [adj_bil_prod, show bil QW (0 : W) 0 = 0 by simp [bil], add_zero] at this
  rw [this]; rfl

/-- $0 \perp B$ is regular when $B$ is. -/
theorem isRegular_bot_prod {B : Submodule R W} (hB : IsRegular QW B) :
    IsRegular (Q.prod QW) ((⊥ : Submodule R V).prod B) := by
  rintro ⟨v, b⟩ ⟨hv, hb⟩ h
  have hv' : v = 0 := (mem_bot R).mp hv
  subst hv'
  have : b = 0 := hB b hb fun b' hb' => by
    have := h (0, b') ⟨zero_mem _, hb'⟩
    rwa [adj_bil_prod, show bil Q (0 : V) 0 = 0 by simp [bil], zero_add] at this
  rw [this]; rfl

/-- **Condition (i) survives cancelling a common adjoined lattice** (O'Meara 1963, p. 270): for lattices
$M, N \subseteq V$ and $H \subseteq W$ (finitely generated, $N$, $H$ regular), $d(M \perp H)/d(N \perp H) \cong 1
\bmod \mathfrak a$ if and only if $dM/dN \cong 1 \bmod \mathfrak a$. -/
theorem discQuot_prod_iff {M N : Submodule R V} {H : Submodule R W} (hMfg : M.FG) (hNfg : N.FG) (hHfg : H.FG)
    (hNreg : IsRegular Q N) (hHreg : IsRegular QW H) {X : Submodule R F} :
    DiscQuotSqEquivMod (Q.prod QW) (M.prod H) (N.prod H) X ↔ DiscQuotSqEquivMod Q M N X := by
  have hM'fg : (M.prod (⊥ : Submodule R W)).FG := by rw [← Submodule.map_inl]; exact hMfg.map _
  have hN'fg : (N.prod (⊥ : Submodule R W)).FG := by rw [← Submodule.map_inl]; exact hNfg.map _
  have hH'fg : ((⊥ : Submodule R V).prod H).FG := by rw [← Submodule.map_inr]; exact hHfg.map _
  rw [discQuot_isOrthSum_iff (Q.prod QW) (adj_isOrthSum_prod_split Q QW M H) (adj_isOrthSum_prod_split Q QW N H)
    (adj_isometricLat_refl _ _) hM'fg hN'fg hH'fg (isRegular_prod_bot Q QW hNreg) (isRegular_bot_prod Q QW hHreg)
    (isRegular_bot_prod Q QW hHreg)]
  exact ⟨discQuot_of_isometricLat _ _ (adj_isometricLat_symm _ _ (adj_isometricLat_prod_bot Q QW M))
      (adj_isometricLat_symm _ _ (adj_isometricLat_prod_bot Q QW N)),
    discQuot_of_isometricLat _ _ (adj_isometricLat_prod_bot Q QW M) (adj_isometricLat_prod_bot Q QW N)⟩

end QuadFormsKB.OMeara.Adjoin28
