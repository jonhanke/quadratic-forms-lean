/-
# O'Meara 93:28, the necessity of condition (ii): transfers

**Setting** (as in `Sec93FNecI.lean`).

**Proves** the bookkeeping for condition (ii) of 93:28 along the reductions of O'Meara's step 2 (pp. 270–271):
* `fIdeal_prod_eq`, `fundWeight_prod_eq`: the adjunctions do not change $\mathfrak f_i$ and $\mathfrak w_i$;
* `rep_of_prod`: $F(L \perp H)_{(i)} \to F(K \perp H)_{(i)} \perp \langle c\rangle$ implies $FL_{(i)} \to FK_{(i)} \perp
  \langle c\rangle$ (Witt cancellation, `RepTransfer.spanRepresents_prod_iff`);
* `spanRepresents_smul_iff`: $FM \to FN \perp \langle c\rangle$ on $V$ iff $FM^\alpha \to FN^\alpha \perp
  \langle\alpha c\rangle$ on $V^\alpha$.
-/
import QuadFormsKB.Literature.OMeara.Sec93FNecI
import QuadFormsKB.Literature.OMeara.Sec93FRepTransfer

open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.NecII

open Sat93 Transfer28 Adjoin28 NecI RepTransfer

section Adjoin

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {W : Type*} [AddCommGroup W] [Module F W] [Module R W] [IsScalarTower R F W]
variable (Q : QuadraticForm F V) (QW : QuadraticForm F W)

/-- The fundamental sublattices of $L \perp H$ have the norm groups and scales of those of $L$ when
$\mathfrak g(H^{\mathfrak s_k}) \subseteq \mathfrak g(L^{\mathfrak s_k})$ (so the same weights). -/
theorem fundWeight_prod_eq {L : Submodule R V} {H : Submodule R W} (hLfg : L.FG) (hHfg : H.FG) {t : ℕ}
    {Ls : Fin t → Submodule R V} {Hs : Fin t → Submodule R W} (hL : IsJordanSplitting Q L Ls)
    (hH : IsOrthSplit QW H Hs) (hHmod : ∀ k, IsModular QW (scale Q (Ls k)) (Hs k))
    (hg : ∀ k, normGroup QW (subA QW (scale Q (Ls k)) H) ≤ normGroup Q (subA Q (scale Q (Ls k)) L)) (k : Fin t) :
    fundWeight (Q.prod QW) (L.prod H) (fun k => (Ls k).prod (Hs k)) k = fundWeight Q L Ls k := by
  have hLk : ∀ k, (Ls k).FG := fun k => FG.of_le hLfg (hL.split.iSup_eq ▸ le_iSup Ls k)
  have hHk : ∀ k, (Hs k).FG := fun k => FG.of_le hHfg (hH.iSup_eq ▸ le_iSup Hs k)
  have hsc : scale (Q.prod QW) ((Ls k).prod (Hs k)) = scale Q (Ls k) :=
    (isModular_prod Q QW (hL.modular k) (hHmod k) (hLk k) (hHk k)).1.2.1
  have hgk := fundNormGroup_prod Q QW Ls Hs hg k hsc
  simp only [fundNormGroup, fundSub, hsc] at hgk
  have hs : scale (Q.prod QW) (subA (Q.prod QW) (scale Q (Ls k)) (L.prod H)) =
      scale Q (subA Q (scale Q (Ls k)) L) := by
    rw [subA_prod, scale_prod]
    have h1 := scale_fundSub Q hLfg hL k
    simp only [fundSub] at h1
    rw [h1]
    exact sup_eq_left.mpr (scale_subA_le QW _ H)
  simp only [fundWeight, fundSub, hsc]
  exact weight_congr (Q.prod QW) Q hgk hs

/-- The ideals $\mathfrak f_i$ are unchanged by the adjunction. -/
theorem fIdeal_prod_eq {L : Submodule R V} {H : Submodule R W} (hLfg : L.FG) (hHfg : H.FG) {t : ℕ}
    {Ls : Fin t → Submodule R V} {Hs : Fin t → Submodule R W} (hL : IsJordanSplitting Q L Ls)
    (hH : IsOrthSplit QW H Hs) (hHmod : ∀ k, IsModular QW (scale Q (Ls k)) (Hs k))
    (hg : ∀ k, normGroup QW (subA QW (scale Q (Ls k)) H) ≤ normGroup Q (subA Q (scale Q (Ls k)) L))
    (i j : Fin t) :
    fIdeal (Q.prod QW) (L.prod H) (fun k => (Ls k).prod (Hs k)) i j = fIdeal Q L Ls i j := by
  have hLk : ∀ k, (Ls k).FG := fun k => FG.of_le hLfg (hL.split.iSup_eq ▸ le_iSup Ls k)
  have hHk : ∀ k, (Hs k).FG := fun k => FG.of_le hHfg (hH.iSup_eq ▸ le_iSup Hs k)
  have hsc : ∀ k, scale (Q.prod QW) ((Ls k).prod (Hs k)) = scale Q (Ls k) := fun k =>
    (isModular_prod Q QW (hL.modular k) (hHmod k) (hLk k) (hHk k)).1.2.1
  have hfg : ∀ k, fundNormGroup (Q.prod QW) (L.prod H) (fun k => (Ls k).prod (Hs k)) k = fundNormGroup Q L Ls k :=
    fun k => fundNormGroup_prod Q QW Ls Hs hg k (hsc k)
  simp only [fIdeal, fIdeal_fundNormIdeal_eq_span, hfg, hsc]

/-- **Condition (ii) survives the adjunction** (O'Meara 1963, p. 270, with Witt's theorem): for $c \ne 0$,
$F(L_{(i)} \perp H_{(i)}) \to F(K_{(i)} \perp H_{(i)}) \perp \langle c\rangle$ implies $FL_{(i)} \to FK_{(i)} \perp
\langle c\rangle$. -/
theorem rep_of_prod [FiniteDimensional F V] [FiniteDimensional F W] {L : Submodule R V} {H : Submodule R W}
    (hLfg : L.FG) (hHfg : H.FG) {t : ℕ} {Ls Ks : Fin t → Submodule R V} {Hs : Fin t → Submodule R W}
    (hL : IsJordanSplitting Q L Ls) (hK : IsJordanSplitting Q L Ks) (hH : IsOrthSplit QW H Hs)
    (hHmod : ∀ k, IsModular QW (scale Q (Ls k)) (Hs k)) (i : Fin t) {c : F} (hc : c ≠ 0)
    (h : SpanRepresents (Q.prod QW) (jordanChain (fun k => (Ls k).prod (Hs k)) i)
      (jordanChain (fun k => (Ks k).prod (Hs k)) i) c) :
    SpanRepresents Q (jordanChain Ls i) (jordanChain Ks i) c := by
  have hJH : IsJordanSplitting QW H Hs := isJordanSplitting_of_scales QW hH hL.scale_strictAnti hHmod
  rw [jordanChain_prod, jordanChain_prod] at h
  have hKfg' : (jordanChain Ks i).FG := FG.of_le hLfg (jordanChain_le hK.split i)
  have hHfg' : (jordanChain Hs i).FG := FG.of_le hHfg (jordanChain_le hH i)
  exact (spanRepresents_prod_iff Q QW
    (isRegular_of_isJordanSplitting Q hKfg' (isJordanSplitting_jordanChain Q hK i))
    (isRegular_of_isJordanSplitting QW hHfg' (isJordanSplitting_jordanChain QW hJH i)) hc).mp h

end Adjoin

section Scale

variable {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **Representations under scaling** (O'Meara 1963, 93:23): $FM \to FN \perp \langle c\rangle$ on $V$ iff
$FM \to FN \perp \langle \alpha c\rangle$ on $V^\alpha$. -/
theorem spanRepresents_smul_iff {α : F} (hα : α ≠ 0) (M N : Submodule R V) (c : F) :
    SpanRepresents (α • Q) M N (α * c) ↔ SpanRepresents Q M N c := by
  constructor
  · rintro ⟨f, hf, h⟩
    refine ⟨f, hf, fun x => ?_⟩
    have := h x
    simp only [smul_apply, smul_eq_mul] at this
    apply mul_left_cancel₀ hα
    linear_combination this
  · rintro ⟨f, hf, h⟩
    refine ⟨f, hf, fun x => ?_⟩
    simp only [smul_apply, smul_eq_mul]
    rw [← h x]; ring

end Scale

end QuadFormsKB.OMeara.NecII
