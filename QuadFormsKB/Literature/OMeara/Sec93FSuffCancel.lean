/-
# O'Meara 93:28, sufficiency, step 2: cancelling the adjoined lattice

**Setting** (as in `Sec93FAdjoin.lean`).

**Proves** (O'Meara 1963, §93F, proof of 93:28, sufficiency, step 2, p. 272: "if we can prove that $L \perp L$ and
$L \perp K$ are isometric, then we can obtain an isometry of $L$ onto $K$ using Corollary 93:14a to cancel one $J_i$ at
a time")
* `normGroup_subA_of_isometricLat`, `isOrthSum_imgLat`: invariance lemmas;
* `isometricLat_cancel_prod`: if $L \perp H \cong K \perp H$ where $H = H_1 \perp \cdots \perp H_t$ with $H_k$
  $\mathfrak s_k$-modular and $\mathfrak gH_k \subseteq \mathfrak g_k$ (the fundamental norm groups of $L$ and of $K$),
  then $L \cong K$.
-/
import QuadFormsKB.Literature.OMeara.Sec93FAdjoin

open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.SuffCancel

open Adjoin28

section Inv

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {V' : Type*} [AddCommGroup V'] [Module F V'] [Module R V'] [IsScalarTower R F V']
variable (Q : QuadraticForm F V) (Q' : QuadraticForm F V')

/-- Isometric lattices have the same $\mathfrak g(X^{\mathfrak a})$. -/
theorem normGroup_subA_of_isometricLat {X : Submodule R V} {Y : Submodule R V'} (h : IsometricLat Q Q' X Y)
    (a : Submodule R F) : normGroup Q' (subA Q' a Y) = normGroup Q (subA Q a X) := by
  obtain ⟨f, hf⟩ := h
  rw [subA_imgLat Q Q' f hf a]
  exact normGroup_imgLat Q Q' f hf (fun x hx => hx.1)

/-- An isometry carries an orthogonal sum to an orthogonal sum. -/
theorem isOrthSum_imgLat {M J X : Submodule R V} {M' : Submodule R V'} (f : M ≃ₗ[R] M')
    (hf : ∀ x : M, Q' (f x : V') = Q (x : V)) (h : IsOrthSum Q M J X) :
    IsOrthSum Q' M' (imgLat f J) (imgLat f X) := by
  have hJM : J ≤ M := h.sup_eq ▸ le_sup_left
  have hXM : X ≤ M := h.sup_eq ▸ le_sup_right
  refine ⟨fun u hu v hv => ?_, ?_, ?_⟩
  · obtain ⟨a, ha, rfl⟩ := (mem_imgLat f).mp hu
    obtain ⟨b, hb, rfl⟩ := (mem_imgLat f).mp hv
    rw [bil_eq_of_isometricLat Q Q' f hf]; exact h.orth _ ha _ hb
  · rw [disjoint_def]
    intro v hv1 hv2
    obtain ⟨a, ha, rfl⟩ := (mem_imgLat f).mp hv1
    obtain ⟨b, hb, hab⟩ := (mem_imgLat f).mp hv2
    have : a = b := f.injective (Subtype.ext hab.symm)
    subst this
    have h0 : (a : V) = 0 := (disjoint_def.mp h.disjoint) _ ha hb
    have : a = 0 := Subtype.ext h0
    rw [this, map_zero]; rfl
  · apply le_antisymm (sup_le (imgLat_le f J) (imgLat_le f X))
    intro y hy
    obtain ⟨m, hmy⟩ := f.surjective ⟨y, hy⟩
    have hyv : y = (f m : V') := by rw [hmy]
    rw [hyv]
    have hm : (m : V) ∈ J ⊔ X := h.sup_eq ▸ m.2
    obtain ⟨j, hj, x, hx, hjx⟩ := mem_sup.mp hm
    have hm' : m = ⟨j, hJM hj⟩ + ⟨x, hXM hx⟩ := Subtype.ext (by rw [Submodule.coe_add]; exact hjx.symm)
    rw [hm', map_add, Submodule.coe_add]
    exact add_mem (mem_sup_left ((mem_imgLat f).mpr ⟨_, hj, rfl⟩))
      (mem_sup_right ((mem_imgLat f).mpr ⟨_, hx, rfl⟩))

end Inv

section Cancel

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {W : Type*} [AddCommGroup W] [Module F W] [Module R W] [IsScalarTower R F W]
variable (Q : QuadraticForm F V) (QW : QuadraticForm F W)

/-- **Cancelling an adjoined lattice one modular component at a time** (O'Meara 1963, p. 272, by Corollary 93:14a):
if $L \perp H \cong K \perp H$ where $H = H_1 \perp \cdots \perp H_t$, $H_k$ is $\mathfrak s_k$-modular and
$\mathfrak gH_k \subseteq \mathfrak g(L^{\mathfrak s_k}) \cap \mathfrak g(K^{\mathfrak s_k})$, then $L \cong K$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (cancel one J_i at a time by 93:14a)"]
theorem isometricLat_cancel_prod {L K : Submodule R V} {H : Submodule R W} (hLfg : L.FG) (hKfg : K.FG)
    (hHfg : H.FG) {t : ℕ} {Hs : Fin t → Submodule R W} (hH : IsOrthSplit QW H Hs) {s : Fin t → Submodule R F}
    (hmod : ∀ k, IsModular QW (s k) (Hs k))
    (hgL : ∀ k, normGroup QW (Hs k) ≤ normGroup Q (subA Q (s k) L))
    (hgK : ∀ k, normGroup QW (Hs k) ≤ normGroup Q (subA Q (s k) K))
    (h : IsometricLat (Q.prod QW) (Q.prod QW) (L.prod H) (K.prod H)) : IsometricLat Q Q L K := by
  classical
  set Q' := Q.prod QW with hQ'
  have hHk : ∀ k, (Hs k).FG := fun k => FG.of_le hHfg (hH.iSup_eq ▸ le_iSup Hs k)
  set HS : Finset (Fin t) → Submodule R W := fun S => ⨆ k ∈ S, Hs k with hHS
  have hHSfg : ∀ S, (HS S).FG := fun S => FG.of_le hHfg (iSup₂_le fun k _ => hH.iSup_eq ▸ le_iSup Hs k)
  have hfgp : ∀ {A : Submodule R V} {B : Submodule R W}, A.FG → B.FG → (A.prod B).FG := fun hA hB => by
    rw [prod_eq_sup, ← Submodule.map_inl, ← Submodule.map_inr]; exact (hA.map _).sup (hB.map _)
  have key : ∀ S : Finset (Fin t), IsometricLat Q' Q' (L.prod (HS S)) (K.prod (HS S)) →
      IsometricLat Q' Q' (L.prod (HS ∅)) (K.prod (HS ∅)) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact id
    | insert k S hkS ih =>
      intro hiso
      apply ih
      have hins : HS (insert k S) = Hs k ⊔ HS S := by simp [hHS, Finset.iSup_insert]
      rw [hins] at hiso
      obtain ⟨f, hf⟩ := hiso
      -- the two splittings of `M = K ⊥ (H_k ⊥ H_S)`
      have horthkS : ∀ x ∈ Hs k, ∀ y ∈ HS S, bil QW x y = 0 := by
        intro x hx y hy
        refine Submodule.iSup_induction (fun l => ⨆ (_ : l ∈ S), Hs l) (motive := fun y => bil QW x y = 0) hy
          (fun l y hy => ?_) (by simp [bil]) (fun y y' h1 h2 => by rw [bil_add_right, h1, h2, add_zero])
        refine Submodule.iSup_induction (fun _ : l ∈ S => Hs l) (motive := fun y => bil QW x y = 0) hy
          (fun hl y hy => hH.orth k l (fun h => hkS (h ▸ hl)) x hx y hy) (by simp [bil])
          (fun y y' h1 h2 => by rw [bil_add_right, h1, h2, add_zero])
      have hsplit : ∀ (A : Submodule R V), IsOrthSum Q' (A.prod (Hs k ⊔ HS S)) ((⊥ : Submodule R V).prod (Hs k))
          (A.prod (HS S)) := by
        intro A
        have horth : ∀ x ∈ (⊥ : Submodule R V).prod (Hs k), ∀ y ∈ A.prod (HS S), bil Q' x y = 0 := by
          rintro ⟨x₁, x₂⟩ ⟨hx₁, hx₂⟩ ⟨y₁, y₂⟩ ⟨-, hy₂⟩
          have : x₁ = 0 := (mem_bot R).mp hx₁
          subst this
          rw [hQ', adj_bil_prod, horthkS x₂ hx₂ y₂ hy₂]; simp [bil]
        refine ⟨horth, ?_, ?_⟩
        · exact Sat93.disjoint_of_orth Q' (Adjoin28.isRegular_bot_prod Q QW ((hmod k).isRegular QW (hHk k))) horth
        · rw [Submodule.prod_sup_prod, bot_sup_eq]
      have h₁ := isOrthSum_imgLat Q' Q' f hf (hsplit L)
      have hJ : IsometricLat Q' Q' ((⊥ : Submodule R V).prod (Hs k)) (imgLat f ((⊥ : Submodule R V).prod (Hs k))) :=
        isometricLat_imgLat Q' Q' f hf (by rw [← (hsplit L).sup_eq]; exact le_sup_left)
      have hX : IsometricLat Q' Q' (L.prod (HS S)) (imgLat f (L.prod (HS S))) :=
        isometricLat_imgLat Q' Q' f hf (by rw [← (hsplit L).sup_eq]; exact le_sup_right)
      have hJmod : IsModular Q' (s k) ((⊥ : Submodule R V).prod (Hs k)) :=
        IsometricLat.isModular QW Q' (adj_isometricLat_bot_prod Q QW (Hs k)) (hHk k) (hmod k)
      have hgJ : normGroup Q' ((⊥ : Submodule R V).prod (Hs k)) = normGroup QW (Hs k) :=
        (adj_normGroup_eq QW Q' (adj_isometricLat_bot_prod Q QW (Hs k))).symm
      have hsfg : (s k).FG := (hmod k).2.1 ▸ scale_fg QW (hHk k)
      have hcancel := isometricLat_of_cancel_modular Q' (hfgp hKfg ((hHk k).sup (hHSfg S))) (hsplit K) h₁ hJ hsfg
        hJmod (by
          rw [hgJ, hQ', subA_prod, normGroup_prod]
          exact (hgK k).trans le_sup_left) (by
          rw [← adj_normGroup_eq Q' Q' hJ, hgJ, normGroup_subA_of_isometricLat Q' Q' hX,
            hQ', subA_prod, normGroup_prod]
          exact (hgL k).trans le_sup_left)
      exact adj_isometricLat_symm Q' Q' (adj_isometricLat_trans Q' Q' Q' hcancel (adj_isometricLat_symm Q' Q' hX))
  have hall : HS Finset.univ = H := by
    rw [← hH.iSup_eq]; simp [hHS]
  have h0 := key Finset.univ (hall ▸ h)
  have hempty : HS ∅ = ⊥ := by simp [hHS]
  rw [hempty] at h0
  exact adj_isometricLat_trans Q Q' Q (adj_isometricLat_prod_bot Q QW L)
    (adj_isometricLat_trans Q' Q' Q h0 (adj_isometricLat_symm Q Q' (adj_isometricLat_prod_bot Q QW K)))

end Cancel

end QuadFormsKB.OMeara.SuffCancel
