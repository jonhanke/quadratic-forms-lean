/-
# O'Meara 93:28, sufficiency, steps 4–7: making $FK_1$ hyperbolic once $dK_1 = dL_1$

**Setting** (as in `Sec93FCoreGen.lean`): rank-$8$ components, $K_1' = \langle A(0,0)\rangle \perp D$ with
$dL_1/dK_1'$ the square of a unit (`CoreGen.exists_sat_sq`), indices $0$-based.

**Proves** (O'Meara 1963, §93F, proof of 93:28, sufficiency, steps 4–7, pp. 274–275)
* `regroup`: $N = P \perp D$, $D = P_2 \perp M$ gives $N = M \perp (P + P_2)$;
* `isBlockBase_blk`: a base with matrix $A(\alpha, 0) \perp A(\gamma, 0)$ is a block base;
* `lagr_of_planes_blk`: $M \perp \langle A(0,0)\rangle \perp \langle A(0,0)\rangle$ with $M \cong A(\alpha,0) \perp
  A(\gamma,0)$ spans a hyperbolic space;
* `route_aniso`: if neither (ii) nor (iii) applies at the first index, then $K$ has a saturated splitting with $FK_1$
  hyperbolic: split $K_1' = \langle A(0,0)\rangle \perp \langle A(0,0)\rangle \perp M$ (93:18 (v) twice), $dM = 1$, so by
  93:18 (vi) $M \cong A(a_1,0) \perp A(b_1,0)$ or $M \cong A(a_1, 4a_1^{-1}\rho) \perp A(b_1, 4b_1^{-1}\rho)$; in the
  second case $4\rho/a_1, 4\rho/b_1 \in \mathfrak g_2$ (`CoreFactor.mem_fundNormGroup_of_not_cond`) and two moves of
  93:19 (`CoreAniso.kill_aniso`) give $A(a_1,0) \perp A(b_1,0)$ (O'Meara: "there is a splitting
  $K_1 \perp K_2 \cong \langle A(a_1,0)\rangle \perp \langle A(b_1,0)\rangle \perp K_2'$"); saturation is kept since
  $\mathfrak g\,(A(a_1,0) \perp A(b_1,0)) = \mathfrak gM$ (`D18.normGroup_eq_of_blk2`).
-/
import QuadFormsKB.Literature.OMeara.Sec93FCoreGen
import QuadFormsKB.Literature.OMeara.Sec93FCoreAniso
import QuadFormsKB.Literature.OMeara.Sec93FCoreTwoLast
import QuadFormsKB.Literature.OMeara.Sec93Gap2

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.CoreRouteD

section Blocks

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

open Sat93

/-- **Regrouping** $N = P \perp (P_2 \perp M)$ as $N = M \perp (P + P_2)$, with $P \perp P_2$. -/
theorem regroup {N P D P₂ M : Submodule R V} (h1 : IsOrthSum Q N P D) (h2 : IsOrthSum Q D P₂ M)
    (hMreg : IsRegular Q M) :
    IsOrthSum Q N M (P ⊔ P₂) ∧ ∀ u ∈ P, ∀ v ∈ P₂, bil Q u v = 0 := by
  have hP₂D : P₂ ≤ D := h2.sup_eq ▸ le_sup_left
  have hMD : M ≤ D := h2.sup_eq ▸ le_sup_right
  have horth : ∀ u ∈ M, ∀ v ∈ P ⊔ P₂, bil Q u v = 0 := by
    intro u hu v hv
    obtain ⟨p, hp, p₂, hp₂, rfl⟩ := mem_sup.mp hv
    rw [bil_add_right, bil_comm Q u p, h1.orth p hp u (hMD hu), bil_comm Q u p₂, h2.orth p₂ hp₂ u hu, add_zero]
  refine ⟨⟨horth, disjoint_of_orth Q hMreg horth, ?_⟩, fun u hu v hv => h1.orth u hu v (hP₂D hv)⟩
  rw [← h1.sup_eq, ← h2.sup_eq]
  ac_rfl

include Q in
lemma blk2_apply_eq {e : Fin 4 → V} {α γ : F} (he : gram Q e = D18.blk2 α 0 γ 0) (i j : Fin 4) :
    bil Q (e i) (e j) = D18.blk2 α 0 γ 0 i j := by
  rw [← he]; rfl

/-- **A base with matrix $A(\alpha, 0) \perp A(\gamma, 0)$ is a block base** (`IsBlockBase`, pairs
$(e_0, e_1)$, $(e_2, e_3)$). -/
theorem isBlockBase_blk {M : Submodule R V} (e : Basis (Fin 4) R M) {α γ : F}
    (he : gram Q (fun i => (e i : V)) = D18.blk2 α 0 γ 0) :
    Merge28.IsBlockBase Q M ![((e 0 : V), (e 1 : V)), ((e 2 : V), (e 3 : V))] := by
  have hg := blk2_apply_eq Q he
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine Eq.trans ?_ (span_basis_eq e)
    rw [NecBlock.pairSpan]
    congr 1
    ext v
    simp only [Set.mem_union, Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    constructor
    · rintro ((h | h) | (h | h)) <;> exact ⟨_, h⟩
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
  · intro k; fin_cases k
    · show Q (e 1 : V) = 0; rw [← bil_self, hg]; simp [D18.blk2]
    · show Q (e 3 : V) = 0; rw [← bil_self, hg]; simp [D18.blk2]
  · intro k; fin_cases k
    · show bil Q (e 0 : V) (e 1 : V) = 1; rw [hg]; simp [D18.blk2]
    · show bil Q (e 2 : V) (e 3 : V) = 1; rw [hg]; simp [D18.blk2]
  all_goals intro k l hkl; fin_cases k <;> fin_cases l <;> simp_all [hg, D18.blk2]

/-- **$M \perp \langle A(0,0)\rangle \perp \langle A(0,0)\rangle$ spans a hyperbolic space** when
$M \cong A(\alpha, 0) \perp A(\gamma, 0)$: the four pairs form a block base (`CoreTwo.isBlockBase_cons`,
`isBlockBase_blk`), which gives a totally isotropic subspace of half the dimension
(`CoreTwo.exists_lagrangian_of_blockBase`). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, steps 4–7, pp. 274–275 (K₁ ≅ A(a₁,0) ⊥ A(b₁,0) is hyperbolic)"]
theorem lagr_of_planes_blk {N M : Submodule R V} {x y x₂ y₂ : V}
    (hN : IsOrthSum Q N M (span R {x, y} ⊔ span R {x₂, y₂}))
    (hPP : ∀ u ∈ span R {x, y}, ∀ v ∈ span R {x₂, y₂}, bil Q u v = 0) (hQy : Q y = 0) (hxy : bil Q x y = 1)
    (hQy₂ : Q y₂ = 0) (hxy₂ : bil Q x₂ y₂ = 1) {α γ : F} (hM : D18.HasBlk Q M α 0 γ 0) :
    ∃ T : Submodule F V, (∀ v ∈ T, Q v = 0) ∧ (∀ v ∈ T, v ∈ span F (N : Set V)) ∧
      finrank R N ≤ 2 * finrank F T := by
  obtain ⟨e, he⟩ := hM
  have h0 := isBlockBase_blk Q e he
  have hMorth : ∀ u ∈ M, ∀ v ∈ span R {x, y} ⊔ span R {x₂, y₂}, bil Q u v = 0 := hN.orth
  have h1 := CoreTwo.isBlockBase_cons Q h0 hQy₂ hxy₂ (fun u hu v hv => by
    rw [bil_comm]; exact hMorth v hv u (mem_sup_right hu))
  have h2 := CoreTwo.isBlockBase_cons Q h1 hQy hxy (fun u hu v hv => by
    obtain ⟨p, hp, m, hm, rfl⟩ := mem_sup.mp hv
    rw [bil_add_right, hPP u hu p hp, bil_comm, hMorth m hm u (mem_sup_left hu), add_zero])
  have hNeq : span R {x, y} ⊔ (span R {x₂, y₂} ⊔ M) = N := by
    rw [← hN.sup_eq]; ac_rfl
  rw [← hNeq]
  exact CoreTwo.exists_lagrangian_of_blockBase Q h2

include Q in
/-- $4\rho/c \in \mathfrak p$ when $\operatorname{ord} c \le \operatorname{ord} 2$ (in a dyadic ring). -/
lemma exists_max_four_div {π : R} (hπ : Irreducible π) (h2p : ¬ IsUnit (2 : R)) {c : F} (hc : c ≠ 0)
    (hcd : dord hπ c ≤ dord hπ (2 : F)) (ρ : R) :
    ∃ r ∈ maximalIdeal R, algebraMap R F r = 4 * algebraMap R F ρ / c := by
  by_cases hx : 4 * algebraMap R F ρ / c = 0
  · exact ⟨0, zero_mem _, by rw [hx, map_zero]⟩
  have hρ : algebraMap R F ρ ≠ 0 := fun h => hx (by rw [h]; simp)
  have h2F : (2 : F) ≠ 0 := two_ne_zero' F
  have h4F : (4 : F) ≠ 0 := by rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2F h2F
  -- `ord 2 ≥ 1`
  have he : 1 ≤ dord hπ (2 : F) := by
    have h2m : (2 : R) ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr h2p
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ] at h2m
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp h2m
    have h2R : (2 : R) ≠ 0 := fun h => h2F (by rw [← map_ofNat (algebraMap R F) 2, h, map_zero])
    have hr0 : r ≠ 0 := by rintro rfl; rw [zero_mul] at hr; exact h2R hr.symm
    have : (2 : F) = algebraMap R F r * algebraMap R F π := by rw [← map_mul, hr, map_ofNat]
    rw [this, dord_mul hπ ((map_ne_zero_iff _ (IsFractionRing.injective R F)).2 hr0) (alg_pi_ne_zero hπ),
      dord_pi hπ]
    have := dord_alg_nonneg (F := F) hπ hr0
    omega
  refine exists_max_of_pos hπ hx ?_
  have hcinv : dord hπ c⁻¹ = -dord hπ c := by
    have := dord_mul hπ hc (inv_ne_zero hc)
    rw [mul_inv_cancel₀ hc, CoreFactor.dord_one Q hπ] at this; omega
  rw [div_eq_mul_inv, dord_mul hπ (mul_ne_zero h4F hρ) (inv_ne_zero hc), dord_mul hπ h4F hρ, hcinv,
    show (4 : F) = 2 * 2 by norm_num, dord_mul hπ h2F h2F]
  have := dord_alg_nonneg (F := F) hπ (fun h : ρ = 0 => hρ (by rw [h, map_zero]))
  omega

end Blocks

section Route

universe u

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type u} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

open Sat93 Suff28 SuffStep SuffMain FundAux FIdealAux

/-- **Steps 4–7 when neither (ii) nor (iii) applies: $FK_1$ made hyperbolic** (O'Meara 1963, §93F, proof of 93:28,
sufficiency, pp. 274–275: "By Example 93:18 (vi) there is a splitting $K_1 \cong \langle A(a_1, 4a_1^{-1}\lambda)\rangle
\perp \langle A(b_1, 4b_1^{-1}\lambda)\rangle$ … Otherwise $\mathfrak w_2 \supseteq 4\mathfrak w_1^{-1}$ … there is a
splitting $K_1 \perp K_2 \cong \langle A(a_1,0)\rangle \perp \langle A(b_1,0)\rangle \perp K_2'$"). In the rank-$8$
situation of `Core8`, given a saturated splitting $K'$ (`hKs'`) with $dL_1/dK_1'$ a unit square and
$K_1' = \langle A(0,0)\rangle \perp D$ (`CoreGen.exists_sat_sq`), outside step 8 (`hcase`) and with neither (ii)
(`hnii`) nor (iii) (`hniii`) applicable at the first index, $K$ has a saturated splitting whose first space is
hyperbolic. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, steps 4–7, pp. 274–275 (killing λ in 93:18 (vi))"]
theorem route_aniso (hHil : PadicClass.LocalHilbertField F) (h2p : ¬ IsUnit (2 : R))
    (hQ : (QuadraticMap.associated Q).Nondegenerate) {L K : Submodule R V} [L.IsLattice F] [K.IsLattice F] {m : ℕ}
    {Ls Ks' : Fin (m + 2) → Submodule R V} {a : Fin (m + 2) → F} (hLs : IsSaturated Q L Ls)
    (hKs' : IsSaturated Q K Ks') (hd : ∀ k, finrank R (Ls k) = 8)
    (hT0 : ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ls 0 : Set V)) ∧
      finrank R (Ls 0) ≤ 2 * finrank F T)
    (hsc : scale Q (Ls 0) = 1) (hS : SameFundamentalInvariants Q Q L K Ls Ks' a) {π : R} (hπ : Irreducible π)
    (hcase : (dord hπ (a 1) = dord hπ (a 0) ∨ dord hπ (a 1) = dord hπ (a 0) + 1 ∨
        ∃ τ : F, scale Q (Ls 1) = R ∙ τ ∧ dord hπ τ = 1 ∧ dord hπ (a 1) = dord hπ (a 0) + 2) ∨
      (dord hπ (a 0) = dord hπ (2 : F) ∧ dord hπ (a 0) + 1 ≤ dord hπ (a 1)))
    (hnii : ¬ fIdeal Q L Ls 0 1 < (4 * a 1) • (1 / fundWeight Q L Ls 1))
    (hniii : ¬ fIdeal Q L Ls 0 1 < (4 * a 0) • (1 / fundWeight Q L Ls 0))
    (hsq : DiscQuotSqEquivMod Q (Ls 0) (Ks' 0) ⊥) {x y : V} {D : Submodule R V} (hQx : Q x = 0) (hQy : Q y = 0)
    (hxy : bil Q x y = 1) (hPD : IsOrthSum Q (Ks' 0) (span R {x, y}) D) :
    ∃ Ks'' : Fin (m + 2) → Submodule R V, IsSaturated Q K Ks'' ∧
      ∃ T : Submodule F V, (∀ v ∈ T, Q v = 0) ∧ (∀ v ∈ T, v ∈ span F (Ks'' 0 : Set V)) ∧
        finrank R (Ks'' 0) ≤ 2 * finrank F T := by
  classical
  have hLfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hKfg : K.FG := Submodule.IsLattice.fg (A := F)
  have hregL := isRegular_of_lattice_max Q hQ ‹L.IsLattice F›
  obtain ⟨⟨h0, hTy⟩, haL, -⟩ := id hS
  have hc0 : ∀ k : Fin (m + 2), Fin.cast h0 k = k := fun k => Fin.ext rfl
  have hscK : ∀ k, scale Q (Ks' k) = scale Q (Ls k) := fun k => by
    have := (hTy k).2.1; rw [hc0] at this; exact this.symm
  have hrkK : ∀ k, finrank R (Ks' k) = 8 := fun k => by
    have := (hTy k).1; rw [hc0] at this; rw [← this]; exact hd k
  have hfund : ∀ k, fundNormGroup Q K Ks' k = fundNormGroup Q L Ls k := fun k => by
    have := (hTy k).2.2; rw [hc0] at this; exact this.symm
  have hKle : ∀ k, Ks' k ≤ K := fun k => hKs'.1.split.iSup_eq ▸ le_iSup Ks' k
  have hLle : ∀ k, Ls k ≤ L := fun k => hLs.1.split.iSup_eq ▸ le_iSup Ls k
  have hK0fg : (Ks' 0).FG := FG.of_le hKfg (hKle 0)
  have hL0fg : (Ls 0).FG := FG.of_le hLfg (hLle 0)
  have hs0K : scale Q (Ks' 0) = 1 := (hscK 0).trans hsc
  have hK0U : IsUnimodular Q (Ks' 0) := by have := hKs'.1.modular 0; rwa [hs0K] at this
  have hL0U : IsUnimodular Q (Ls 0) := by have := hLs.1.modular 0; rwa [hsc] at this
  -- `D` is unimodular of rank 6
  have hPle : span R {x, y} ≤ Ks' 0 := hPD.sup_eq ▸ le_sup_left
  have hDle : D ≤ Ks' 0 := hPD.sup_eq ▸ le_sup_right
  have hDfg : D.FG := FG.of_le hK0fg hDle
  have hPfg : (span R {x, y}).FG := FG.of_le hK0fg hPle
  have hdet2 : Q x * Q y - bil Q x y ^ 2 ≠ 0 := by rw [hQx, hQy, hxy]; norm_num
  obtain ⟨bP, -⟩ := CoreMove.exists_basis_pair (R := R) Q hdet2
  have hrkP : finrank R (span R {x, y}) = 2 := by rw [finrank_eq_card_basis bP]; simp
  have hrkD : finrank R D = 6 := by
    have := isOrthSum_finrank Q hPD hK0fg; rw [hrkP, hrkK 0] at this; omega
  have hP0 : span R {x, y} ≠ ⊥ := fun h => by rw [h, finrank_bot] at hrkP; omega
  have hD0 : D ≠ ⊥ := fun h => by rw [h, finrank_bot] at hrkD; omega
  have hDU : IsUnimodular Q D := ((Dedekind.isModular_iff_of_isOrthSum Q hPD hPfg hDfg hP0 hD0).mp hK0U).2
  -- `D = ⟨A(0,0)⟩ ⊥ M`
  obtain ⟨x₂, y₂, M, hQx₂, hQy₂, hxy₂, hDM⟩ :=
    D18.omeara93_18_v_splitting Q hHil h2p hDfg hDU (by rw [hrkD]; norm_num)
  have hP₂le : span R {x₂, y₂} ≤ D := hDM.sup_eq ▸ le_sup_left
  have hMle : M ≤ D := hDM.sup_eq ▸ le_sup_right
  have hMfg : M.FG := FG.of_le hDfg hMle
  have hP₂fg : (span R {x₂, y₂}).FG := FG.of_le hDfg hP₂le
  have hdet2' : Q x₂ * Q y₂ - bil Q x₂ y₂ ^ 2 ≠ 0 := by rw [hQx₂, hQy₂, hxy₂]; norm_num
  obtain ⟨bP₂, -⟩ := CoreMove.exists_basis_pair (R := R) Q hdet2'
  have hrkP₂ : finrank R (span R {x₂, y₂}) = 2 := by rw [finrank_eq_card_basis bP₂]; simp
  have hrkM : finrank R M = 4 := by
    have := isOrthSum_finrank Q hDM hDfg; rw [hrkP₂, hrkD] at this; omega
  have hP₂0 : span R {x₂, y₂} ≠ ⊥ := fun h => by rw [h, finrank_bot] at hrkP₂; omega
  have hM0 : M ≠ ⊥ := fun h => by rw [h, finrank_bot] at hrkM; omega
  have hMU : IsUnimodular Q M := ((Dedekind.isModular_iff_of_isOrthSum Q hDM hP₂fg hMfg hP₂0 hM0).mp hDU).2
  have hMreg : IsRegular Q M := hMU.isRegular Q hMfg
  obtain ⟨hNMC, hPP⟩ := regroup Q hPD hDM hMreg
  -- `𝔤M = 𝔤₁`
  have hPs : scale Q (span R {x, y}) ≤ 1 := hs0K ▸ scale_mono Q hPle
  have hP₂s : scale Q (span R {x₂, y₂}) ≤ 1 := hs0K ▸ scale_mono Q (hP₂le.trans hDle)
  have hgM : normGroup Q M = fundNormGroup Q L Ls 0 := by
    rw [← hfund 0, ← hKs'.2 0, ← hNMC.sup_eq, normGroup_sup_of_orth Q hNMC.orth,
      normGroup_sup_of_orth Q hPP]
    refine le_antisymm le_sup_left (sup_le le_rfl (sup_le ?_ ?_))
    · exact CoreGen.normGroup_plane_le Q hQx hQy hxy hPs hMU.2.1
    · exact CoreGen.normGroup_plane_le Q hQx₂ hQy₂ hxy₂ hP₂s hMU.2.1
  -- norm and weight generators of `M`
  have hscF : scale Q (fundSub Q L Ls 0) = scale Q M := by rw [scale_fundSub Q hLfg hLs.1 0, hsc, hMU.2.1]
  have hnM : IsNormGenerator Q M (a 0) := by
    refine ⟨by rw [hgM]; exact (haL 0).1, ?_⟩
    rw [(haL 0).2, normIdeal_eq_span_normGroup, normIdeal_eq_span_normGroup, hgM]; rfl
  obtain ⟨b, hb⟩ := Sat93.exists_weightGen Q h2p (fundSub_fg Q hLfg Ls 0) (isRegular_fundSub Q hLfg hregL hLs.1 0)
    (fundSub_ne_bot Q hLfg hLs.1 0)
  have hbM : IsWeightGenerator Q M b := by
    unfold IsWeightGenerator at hb ⊢
    rw [hb]; exact weight_congr Q Q hgM.symm hscF
  have hb' : fundWeight Q L Ls 0 = R ∙ b := hb.symm
  obtain ⟨bj, hbj⟩ := Sat93.exists_weightGen Q h2p (fundSub_fg Q hLfg Ls 1) (isRegular_fundSub Q hLfg hregL hLs.1 1)
    (fundSub_ne_bot Q hLfg hLs.1 1)
  have ha0 : a 0 ≠ 0 := (haL 0).ne_zero Q (isRegular_fundSub Q hLfg hregL hLs.1 0) (fundSub_ne_bot Q hLfg hLs.1 0)
  have ha1 : a 1 ≠ 0 := (haL 1).ne_zero Q (isRegular_fundSub Q hLfg hregL hLs.1 1) (fundSub_ne_bot Q hLfg hLs.1 1)
  have hb0 : b ≠ 0 := weight_gen_ne_zero Q (haL 0) ha0 hb
  have hbj0 : bj ≠ 0 := weight_gen_ne_zero Q (haL 1) ha1 hbj
  -- `dM = 1` for a suitable base of `M`
  obtain ⟨bL, hbL0⟩ := CoreAniso.exists_basis_det_of_hyp Q hQ hL0fg hL0U hT0
  have hbL : (gram Q fun i => (bL i : V)).det = 1 := by rw [hbL0, hd 0]; norm_num
  obtain ⟨bM0⟩ := exists_basis (R := R) (F := F) hMfg
  let bM : Basis (Fin 4) R M := bM0.reindex (finCongr hrkM)
  obtain ⟨eD, heD⟩ := CoreGen.exists_basis_plane_sum Q hQx₂ hQy₂ hxy₂ hDM bM
  obtain ⟨eK, heK⟩ := CoreGen.exists_basis_plane_sum Q hQx hQy hxy hPD eD
  have hK0reg : IsRegular Q (Ks' 0) := hK0U.isRegular Q hK0fg
  have hdK : (gram Q fun i => (eK i : V)).det ≠ 0 := Transfer28.det_gram_ne_zero_of_isRegular Q hK0reg eK
  obtain ⟨-, η, hη, hmem⟩ := Transfer28.discQuot_bases Q hsq bL eK hdK
  have hηd : (gram Q fun i => (bM i : V)).det = (algebraMap R F η ^ 2)⁻¹ := by
    have h0' : (gram Q fun i => (bL i : V)).det / (gram Q fun i => (eK i : V)).det -
        1 * algebraMap R F η ^ 2 = 0 := (Submodule.mem_bot R).mp hmem
    rw [hbL, heK, heD] at h0'
    norm_num at h0'
    have hη0 : algebraMap R F η ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).2 hη.ne_zero
    rw [sub_eq_zero] at h0'
    rw [← h0', inv_inv]
  obtain ⟨bM', hbM'⟩ := CoreTwoLast.exists_basis_det_scale Q bM hη
  have hdet1 : (gram Q fun i => (bM' i : V)).det = 1 := by
    have hη0 : algebraMap R F η ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).2 hη.ne_zero
    rw [hbM', hηd]; field_simp
  -- 93:18 (vi) on `FM`
  have hV : finrank F (D18.spanF F M) = 4 := D18.finrank_spanF_of_isUnimodular Q hMfg hMU hrkM
  have hfgS := D18.fg_subLat (F := F) M hMfg
  have hUS := (D18.isUnimodular_subLat Q M).mpr hMU
  have hrkS : finrank R (D18.subLat F M) = 4 := by rw [D18.finrank_subLat]; exact hrkM
  have hnS := (D18.isNormGenerator_subLat Q M).mpr hnM
  have hbS := (D18.isWeightGenerator_subLat Q M).mpr hbM
  have hdS := (D18.exists_det_subLat Q M).mpr ⟨bM', hdet1⟩
  -- the case `M ≅ A(a₁, 0) ⊥ A(b₁, 0)`: done with `K'` itself
  have hdone : D18.HasBlk Q M (a 0) 0 b 0 → ∃ Ks'' : Fin (m + 2) → Submodule R V, IsSaturated Q K Ks'' ∧
      ∃ T : Submodule F V, (∀ v ∈ T, Q v = 0) ∧ (∀ v ∈ T, v ∈ span F (Ks'' 0 : Set V)) ∧
        finrank R (Ks'' 0) ≤ 2 * finrank F T := fun hblk =>
    ⟨Ks', hKs', lagr_of_planes_blk Q hNMC hPP hQy hxy hQy₂ hxy₂ hblk⟩
  rcases Int.even_or_odd (dord hπ (a 0) + dord hπ b) with hev | hodd
  · obtain ⟨-, -, hblk⟩ := D18.omeara93_18_vi_even (D18.subQ Q M) hHil h2p hπ hV hfgS hUS hrkS hnS hbS hev hdS
    exact hdone ((D18.hasBlk_subLat Q M).mp hblk)
  have h2 : (2 : R) ≠ 0 := fun h => two_ne_zero' F (by rw [← map_ofNat (algebraMap R F) 2, h, map_zero])
  obtain ⟨ρ, -, hρ⟩ := G93.exists_delta (F := F) h2 h2p hπ
  obtain ⟨hx, -⟩ := D18.omeara93_18_vi_odd (D18.subQ Q M) hHil h2p hπ hV hfgS hUS hrkS hnS hbS hodd hdS hρ
  rcases hx with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact hdone ((D18.hasBlk_subLat Q M).mp h1)
  have hblk := (D18.hasBlk_subLat Q M).mp h1
  -- orders: `u₁ ≤ ord b ≤ e`, and `u₁ < e` (else the sum `u₁ + ord b = 2e` is even)
  have h1F : (1 : F) ∈ scale Q (fundSub Q L Ls 0) := by
    rw [scale_fundSub Q hLfg hLs.1 0, hsc]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  have h2w : (2 : F) ∈ fundWeight Q L Ls 0 :=
    (weight_bounds Q _).2.2.1 (by simpa using Submodule.smul_mem_pointwise_smul (1 : F) (2 : F) _ h1F)
  have h2F : (2 : F) ≠ 0 := two_ne_zero' F
  have hdbe : dord hπ b ≤ dord hπ (2 : F) := (mem_span_iff hπ h2F hb0).1 (hb' ▸ h2w)
  have hbn : b ∈ R ∙ a 0 := by
    have hbw : R ∙ b = weight Q (fundSub Q L Ls 0) := hb
    rw [(haL 0).2]; exact (weight_bounds Q _).2.2.2 (by rw [← hbw]; exact mem_span_singleton_self b)
  have hab : dord hπ (a 0) ≤ dord hπ b := (mem_span_iff hπ hb0 ha0).1 hbn
  have hu0e : dord hπ (a 0) < dord hπ (2 : F) := by
    by_contra hc
    obtain ⟨k, hk⟩ := hodd
    omega
  have hcase' : dord hπ (a 1) = dord hπ (a 0) ∨
      (dord hπ (a 1) = dord hπ (a 0) + 1 ∧ dord hπ (a 0) < dord hπ (2 : F)) ∨
      ∃ τ : F, scale Q (Ls 1) = R ∙ τ ∧ dord hπ τ = 1 ∧ dord hπ (a 1) = dord hπ (a 0) + 2 := by
    rcases hcase with (h | h | h) | ⟨he, -⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h, hu0e⟩)
    · exact Or.inr (Or.inr h)
    · omega
  obtain ⟨hmq, hms⟩ := CoreFactor.mem_fundNormGroup_of_not_cond Q hπ h2p hLfg hregL hLs.1 haL 0 1 (by simp) hsc hb0
    hb' hbj0 hbj.symm hcase' hnii hniii (-ρ)
  -- integral entries
  obtain ⟨a₀, ha₀⟩ := CoreGen.exists_alg_of_mem_normGroup Q hMU.2.1.le hnM.1
  have hbg : b ∈ normGroup Q M :=
    normGroupIdeal_subset Q _ ((weight_bounds Q _).2.1 (by rw [← hbM]; exact mem_span_singleton_self b))
  obtain ⟨b₀, hb₀⟩ := CoreGen.exists_alg_of_mem_normGroup Q hMU.2.1.le hbg
  obtain ⟨q₀, hq₀p, hq₀⟩ := exists_max_four_div Q hπ h2p ha0 hu0e.le ρ
  obtain ⟨s₀, hs₀p, hs₀⟩ := exists_max_four_div Q hπ h2p hb0 hdbe ρ
  obtain ⟨e, he⟩ := hblk
  have he₀ : gram Q (fun i => (e i : V)) =
      D18.blk2 (algebraMap R F a₀) (algebraMap R F q₀) (algebraMap R F b₀) (algebraMap R F s₀) := by
    rw [he, ha₀, hq₀, hb₀, hs₀]
  have hqg : -algebraMap R F q₀ ∈ normGroup Q (Ks' 1) := by
    rw [hKs'.2 1, hfund 1, hq₀]; convert hmq using 1; rw [map_neg]; ring
  have hsg : -algebraMap R F s₀ ∈ normGroup Q (Ks' 1) := by
    rw [hKs'.2 1, hfund 1, hs₀]; convert hms using 1; rw [map_neg]; ring
  obtain ⟨Ks'', hJ'', hfix, hg1, hscr, M', hM'C, e', he'⟩ :=
    CoreAniso.kill_aniso Q hHil h2p hKfg hKs'.1 hs0K (by rw [hrkK 1]; norm_num) hNMC e he₀ hq₀p hs₀p hqg hsg
  rw [ha₀, hb₀] at he'
  -- `𝔤M' = 𝔤M`
  have hK''0 : scale Q (Ks'' 0) = 1 := (hscr 0).1.trans hs0K
  have hK''U : IsUnimodular Q (Ks'' 0) := by have := hJ''.modular 0; rwa [hK''0] at this
  have hK''fg : (Ks'' 0).FG := FG.of_le hKfg (hJ''.split.iSup_eq ▸ le_iSup Ks'' 0)
  have hM'le : M' ≤ Ks'' 0 := hM'C.sup_eq ▸ le_sup_left
  have hCle : span R {x, y} ⊔ span R {x₂, y₂} ≤ Ks'' 0 := hM'C.sup_eq ▸ le_sup_right
  have hM'0 : M' ≠ ⊥ := by
    intro h
    have := finrank_eq_card_basis e'
    rw [h, finrank_bot] at this; simp at this
  have hC0 : span R {x, y} ⊔ span R {x₂, y₂} ≠ ⊥ := fun h => hP0 (eq_bot_iff.2 (h ▸ le_sup_left))
  have hM'U : IsUnimodular Q M' := ((Dedekind.isModular_iff_of_isOrthSum Q hM'C (FG.of_le hK''fg hM'le)
    (FG.of_le hK''fg hCle) hM'0 hC0).mp hK''U).1
  have hspan' : span R (Set.range fun i => (e' i : V)) = M' := span_basis_eq e'
  have hgM' : normGroup Q M = normGroup Q M' := by
    rw [← hspan']
    exact D18.normGroup_eq_of_blk2 Q h2p hπ hMfg hMU hnM hbM hodd (zero_mem _) (zero_mem _) he'
      (by rw [hspan']; exact hM'U)
  have hfundK'' : ∀ i, fundNormGroup Q K Ks'' i = fundNormGroup Q K Ks' i := fun i =>
    fundNormGroup_eq_of_isJordanSplitting hKfg hKs'.1 hJ'' i i rfl
  refine ⟨Ks'', ⟨hJ'', fun i => ?_⟩, lagr_of_planes_blk Q hM'C hPP hQy hxy hQy₂ hxy₂ ⟨e', he'⟩⟩
  refine le_antisymm (normGroup_le_fundNormGroup Q hKfg hJ'' i) ?_
  rw [hfundK'' i]
  by_cases hi0 : (i : ℕ) = 0
  · have : i = 0 := Fin.ext hi0
    subst this
    rw [hfund 0, ← hgM, hgM']; exact normGroup_mono Q hM'le
  by_cases hi1 : (i : ℕ) = 1
  · have : i = 1 := Fin.ext hi1
    subst this; rw [← hKs'.2 1]; exact hg1
  · rw [hfix i (by omega), ← hKs'.2 i]

end Route

end QuadFormsKB.OMeara.CoreRouteD
