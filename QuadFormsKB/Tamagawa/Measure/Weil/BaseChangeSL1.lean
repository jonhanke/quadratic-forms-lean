import QuadFormsKB.Tamagawa.Measure.Weil.BaseChangeQuat

/-!
# Transport of covolumes for $\mathrm{SL}_1$

A generic statement for a subgroup $H\le G$ mapped by $\Phi : G\cong G'$ onto $H' = \Phi(H)$
(`covolume_map_subgroup`), then its instance for $\mathrm{SL}_1(D_E\otimes\mathbb A_k)\cong\mathrm{SL}_1(D'\otimes\mathbb A_K)$
(`covolume_quatSL1_baseChange`): the covolume of $\mathrm{SL}_1(D_E)(k)$ in $\mathrm{SL}_1(D_E)(\mathbb A_k)$ for the transported
measure equals the covolume of $\mathrm{SL}_1(D')(K)$ in $\mathrm{SL}_1(D')(\mathbb A_K)$.

Uses only `MulEquiv.subgroupMap` (Mathlib) and `covolume_map_continuousMulEquiv`; the idea is the
Weil-restriction viewpoint $R_{K/k}\mathrm{SL}_1(D')(\mathbb A_k) = \mathrm{SL}_1(D')(\mathbb A_K)$ of Weil 1982 §1.3
[unverified page].
-/

open MeasureTheory

set_option synthInstance.maxHeartbeats 400000

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

section Generic

variable {G G' : Type*} [Group G] [Group G'] [TopologicalSpace G] [TopologicalSpace G']
  [IsTopologicalGroup G] [IsTopologicalGroup G']
  [MeasurableSpace G] [BorelSpace G] [MeasurableSpace G'] [BorelSpace G']

/-- A subgroup $H$ and a subgroup $H' = \Phi(H)$ are isomorphic as topological groups via $\Phi$. -/
def subgroupMapContinuousMulEquiv (Φ : G ≃ₜ* G') (H : Subgroup G) (H' : Subgroup G')
    (hH : H.map Φ.toMulEquiv.toMonoidHom = H') : H ≃ₜ* H' :=
  { (MulEquiv.subgroupMap Φ.toMulEquiv H).trans (MulEquiv.subgroupCongr hH) with
    continuous_toFun := by
      refine Continuous.subtype_mk ?_ _
      exact (map_continuous Φ).comp continuous_subtype_val
    continuous_invFun := by
      refine Continuous.subtype_mk ?_ _
      have : Continuous fun y : H' => Φ.symm (y : G') :=
        (map_continuous Φ.symm).comp continuous_subtype_val
      exact this }

theorem subgroupMapContinuousMulEquiv_coe (Φ : G ≃ₜ* G') (H : Subgroup G) (H' : Subgroup G')
    (hH : H.map Φ.toMulEquiv.toMonoidHom = H') (x : H) :
    ((subgroupMapContinuousMulEquiv Φ H H' hH x : H') : G') = Φ (x : G) := rfl

/-- **Transport of covolumes for a subgroup.** If $\Phi : G\cong G'$ is an isomorphism of topological groups,
$H,\Lambda\le G$, $\Phi(H) = H'$, $\Phi(\Lambda) = \Lambda'$, and $s$ is a fundamental domain for $\Lambda\cap H$ in $H$
(for a left-invariant $\mu$), then
$\operatorname{covol}(\Lambda'\cap H'\subset H',\ (\Phi|_H)_*\mu) = \operatorname{covol}(\Lambda\cap H\subset H,\mu)$.
Proof: apply `covolume_map_continuousMulEquiv` to $\Phi|_H : H\cong H'$. -/
@[kb "weil1982" "§1.3 (restriction of scalars) [unverified page]"]
theorem covolume_map_subgroup (Φ : G ≃ₜ* G') (H Λ : Subgroup G) (H' Λ' : Subgroup G')
    (hH : H.map Φ.toMulEquiv.toMonoidHom = H') (hΛ : Λ.map Φ.toMulEquiv.toMonoidHom = Λ')
    [Countable (Λ.subgroupOf H)]
    (μ : Measure H) [μ.IsMulLeftInvariant] {s : Set H} (hs : IsFundamentalDomain (Λ.subgroupOf H) s μ) :
    covolume (Λ'.subgroupOf H') H' (μ.map (subgroupMapContinuousMulEquiv Φ H H' hH)) =
      covolume (Λ.subgroupOf H) H μ := by
  have h := covolume_map_continuousMulEquiv (subgroupMapContinuousMulEquiv Φ H H' hH) (Λ.subgroupOf H) μ hs
  have hsub : (Λ.subgroupOf H).map (subgroupMapContinuousMulEquiv Φ H H' hH).toMulEquiv.toMonoidHom =
      Λ'.subgroupOf H' := by
    ext y
    obtain ⟨x, rfl⟩ := (subgroupMapContinuousMulEquiv Φ H H' hH).surjective y
    rw [Subgroup.mem_map, Subgroup.mem_subgroupOf, ← hΛ, Subgroup.mem_map]
    constructor
    · rintro ⟨z, hz, hzx⟩
      have : z = x := (subgroupMapContinuousMulEquiv Φ H H' hH).injective hzx
      subst this
      exact ⟨z, hz, rfl⟩
    · rintro ⟨g, hg, hgx⟩
      refine ⟨x, ?_, rfl⟩
      have : g = (x : G) := Φ.injective hgx
      rw [Subgroup.mem_subgroupOf, ← this]; exact hg
  rw [← hsub]
  exact h

end Generic

section Quaternion

open scoped Quaternion

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  {d : k} {b : Module.Basis (Fin 2) k K} (hb0 : b 0 = 1) (hb1 : b 1 * b 1 = algebraMap k K d) (α β : k)

/-- $\mathrm{SL}_1(D'\otimes\mathbb A_K)$ as a subgroup of units. -/
abbrev slK : Subgroup (QuatAdele (F := K) (algebraMap k K α) (algebraMap k K β))ˣ :=
  quatSL1 (diag K (algebraMap k K α)) (diag K (algebraMap k K β))

/-- $\mathrm{SL}_1(D_E\otimes\mathbb A_k)$ as a subgroup of units. -/
abbrev slE : Subgroup (QuatQuadAdele k d α β)ˣ :=
  quatSL1 (⟨diagRing k α, 0⟩ : QuadAdele k d) ⟨diagRing k β, 0⟩

/-- **$\mathrm{SL}_1(D_E\otimes\mathbb A_k)\cong\mathrm{SL}_1(D'\otimes\mathbb A_K)$ as topological groups** (the inverse of
`quatUnitsBaseChange` restricted to $\mathrm{SL}_1$). -/
def slBaseChange : slK (K := K) α β ≃ₜ* slE (d := d) α β :=
  subgroupMapContinuousMulEquiv (quatUnitsBaseChange hb0 hb1 α β).symm _ _
    (by
      have h := map_quatSL1_quatUnitsBaseChange hb0 hb1 α β
      unfold slK slE
      rw [← h]
      ext x
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        have : (quatUnitsBaseChange hb0 hb1 α β).symm.toMulEquiv.toMonoidHom
            ((quatUnitsBaseChange hb0 hb1 α β).toMulEquiv.toMonoidHom z) = z :=
          ContinuousMulEquiv.symm_apply_apply _ _
        rw [this]; exact hz
      · intro hx
        exact ⟨_, ⟨x, hx, rfl⟩, ContinuousMulEquiv.symm_apply_apply _ _⟩)

theorem slBaseChange_coe (x : slK (K := K) α β) :
    ((slBaseChange hb0 hb1 α β x : slE (d := d) α β) : (QuatQuadAdele k d α β)ˣ) =
      (quatUnitsBaseChange hb0 hb1 α β).symm (x : (QuatAdele (F := K) _ _)ˣ) := rfl

include hb0 hb1 in
/-- **SL$_1$ covolume glue.** For a left-invariant measure $\mu$ on
$\mathrm{SL}_1(D'\otimes\mathbb A_K)$ with a fundamental domain for $\mathrm{SL}_1(D')(K)$, the covolume of
$\mathrm{SL}_1(D_E)(k) = D_E^\times\cap\mathrm{SL}_1$ in $\mathrm{SL}_1(D_E\otimes\mathbb A_k)$ for the transported measure
$(\Theta^{-1}|_{\mathrm{SL}_1})_*\mu$ equals the covolume of $\mathrm{SL}_1(D')(K)$ in $\mathrm{SL}_1(D'\otimes\mathbb A_K)$. -/
@[kb "weil1982" "§1.3 (restriction of scalars) [unverified page]"]
theorem covolume_slBaseChange
    (μ : Measure (slK (K := K) α β)) [μ.IsMulLeftInvariant] {s : Set (slK (K := K) α β)}
    (hs : IsFundamentalDomain
      ((quatUnitsSub (F := K) (algebraMap k K α) (algebraMap k K β)).subgroupOf (slK α β)) s μ) :
    covolume ((quatQuadUnitsSub d α β).subgroupOf (slE α β)) (slE (d := d) α β)
        (μ.map (slBaseChange hb0 hb1 α β)) =
      covolume ((quatUnitsSub (F := K) (algebraMap k K α) (algebraMap k K β)).subgroupOf (slK α β))
        (slK (K := K) α β) μ := by
  have : Countable ((quatUnitsSub (F := K) (algebraMap k K α) (algebraMap k K β)).subgroupOf (slK α β)) :=
    Function.Injective.countable (f := fun x => (⟨(x : slK (K := K) α β).1, x.2⟩ :
      quatUnitsSub (F := K) (algebraMap k K α) (algebraMap k K β)))
      (fun x y h => Subtype.ext (Subtype.ext (by have := congrArg Subtype.val h; exact this)))
  exact covolume_map_subgroup (quatUnitsBaseChange hb0 hb1 α β).symm _ _ _ _ _
    (map_quatUnitsSub_quatUnitsBaseChange_symm hb0 hb1 α β) μ hs

end Quaternion


end

end QuadFormsKB.Tamagawa.Measure.Weil
