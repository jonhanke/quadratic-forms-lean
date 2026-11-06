/-
# O'Meara 93:29 over a 2-adic field: transfers of conditions (i), (ii)

**Setting** (as in `Sec93G29Nec.lean`): $R$ a Henselian discrete valuation ring with finite residue field, $2$ prime in $R$.

**Proves** (O'Meara 1963, §93G, proof of 93:29, sufficiency, pp. 277–279: "proved in essentially the same way as the
sufficiency of Theorem 93:28"): the conditions `Cond29` pass through the constructions of the induction of 93:28:
* `cond29_prod`: adjoining a lattice $H$ (`cond29_prod`), scaling the space by $2^k$ (`cond29_smul`);
* `cond29_map`, `cond29_subLatIn`, `cond29_latMap`, `cond29_congr_right`: isometries, subspaces, moving $K$ by
  $\sigma \in O(V)$, replacing the Jordan chain of $K$ by an isometric one;
* `cond29_tail`: the tails $L^*$, $K^*$ when $L_1 = K_1$;
* `cond29_repl`: removing a common hyperbolic plane from the component $k_0$;
* `resplit29`: the conditions do not depend on the Jordan splitting of $K$ (necessity of 93:28 for $K$ against $K'$).
The moduli $\mathfrak n_i\mathfrak n_{i+1}/\mathfrak s_i^2$ and the numbers $2^{u_i}$ depend only on the components,
so these transfers are simpler than those for conditions (i)–(iii) of 93:28.
-/
import QuadFormsKB.Literature.OMeara.Sec93G29Nec
import QuadFormsKB.Literature.OMeara.Sec82Scaling

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.G29

universe u v

section Prod

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {W : Type*} [AddCommGroup W] [Module F W] [Module R W] [IsScalarTower R F W]
variable (Q : QuadraticForm F V) (QW : QuadraticForm F W)

open Adjoin28 Transfer28 NecI NecII RepTransfer

/-- $\mathfrak n(A \perp B) = \mathfrak nA + \mathfrak nB$ for lattices in the orthogonal sum of spaces. -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, pp. 277–279 (transfers of conditions (i), (ii))"]
theorem normIdeal_prod (A : Submodule R V) (B : Submodule R W) :
    normIdeal (Q.prod QW) (A.prod B) = normIdeal Q A ⊔ normIdeal QW B := by
  rw [normIdeal_eq_span_normGroup, normGroup_prod, normIdeal_eq_span_normGroup, normIdeal_eq_span_normGroup]
  apply le_antisymm
  · rw [span_le]
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.mp hz
    exact add_mem (mem_sup_left (subset_span ha)) (mem_sup_right (subset_span hb))
  · exact sup_le (span_mono (by intro z hz; exact AddSubgroup.mem_sup_left hz))
      (span_mono (by intro z hz; exact AddSubgroup.mem_sup_right hz))

/-- **Conditions (i), (ii) of 93:29 pass to $L \perp H$, $K \perp H$** (O'Meara 1963, §93G, p. 278, "the same way as in
93:28"): when the components $H_k$ are $\mathfrak sL_k$-modular with $\mathfrak nH_k \subseteq \mathfrak nL_k$, the scales
and norms of $L_k \perp H_k$ are those of $L_k$ (and of $K_k \perp H_k$ those of $K_k$). -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, pp. 277–279 (transfers of conditions (i), (ii))"]
theorem cond29_prod [FiniteDimensional F V] [FiniteDimensional F W] {L K : Submodule R V} {H : Submodule R W}
    (hLfg : L.FG) (hKfg : K.FG) (hHfg : H.FG) {t : ℕ} {Ls Ks : Fin t → Submodule R V} {Hs : Fin t → Submodule R W}
    (hL : IsJordanSplitting Q L Ls) (hK : IsJordanSplitting Q K Ks) (hH : IsOrthSplit QW H Hs)
    (hHmodL : ∀ k, IsModular QW (scale Q (Ls k)) (Hs k)) (hHmodK : ∀ k, IsModular QW (scale Q (Ks k)) (Hs k))
    (hnL : ∀ k, normIdeal QW (Hs k) ≤ normIdeal Q (Ls k)) (hnK : ∀ k, normIdeal QW (Hs k) ≤ normIdeal Q (Ks k))
    (hC : Cond29 Q Ls Ks) :
    Cond29 (Q.prod QW) (fun k => (Ls k).prod (Hs k)) (fun k => (Ks k).prod (Hs k)) := by
  intro i j hij
  have hJH : IsJordanSplitting QW H Hs := isJordanSplitting_of_scales QW hH hL.scale_strictAnti hHmodL
  have hLk : ∀ k, (Ls k).FG := fun k => FG.of_le hLfg (hL.split.iSup_eq ▸ le_iSup Ls k)
  have hKk : ∀ k, (Ks k).FG := fun k => FG.of_le hKfg (hK.split.iSup_eq ▸ le_iSup Ks k)
  have hHk : ∀ k, (Hs k).FG := fun k => FG.of_le hHfg (hH.iSup_eq ▸ le_iSup Hs k)
  have hscL : ∀ k, scale (Q.prod QW) ((Ls k).prod (Hs k)) = scale Q (Ls k) := fun k =>
    (isModular_prod Q QW (hL.modular k) (hHmodL k) (hLk k) (hHk k)).1.2.1
  have hnL' : ∀ k, normIdeal (Q.prod QW) ((Ls k).prod (Hs k)) = normIdeal Q (Ls k) := fun k => by
    rw [normIdeal_prod]; exact sup_eq_left.mpr (hnL k)
  obtain ⟨h1, h2⟩ := hC i j hij
  have hLfg' : (jordanChain Ls i).FG := FG.of_le hLfg (jordanChain_le hL.split i)
  have hKfg' : (jordanChain Ks i).FG := FG.of_le hKfg (jordanChain_le hK.split i)
  have hHfg' : (jordanChain Hs i).FG := FG.of_le hHfg (jordanChain_le hH i)
  have hKreg := isRegular_of_isJordanSplitting Q hKfg' (isJordanSplitting_jordanChain Q hK i)
  have hHreg := isRegular_of_isJordanSplitting QW hHfg' (isJordanSplitting_jordanChain QW hJH i)
  simp only [hscL, hnL', jordanChain_prod]
  refine ⟨(discQuot_prod_iff Q QW hLfg' hKfg' hHfg' hKreg hHreg).mpr h1, fun hle u hu => ?_⟩
  have hc : ((2 : F) ^ u) ≠ 0 := zpow_ne_zero _ (two_ne_zero' F)
  exact (spanRepresents_prod_iff Q QW hKreg hHreg hc).mpr (h2 hle u hu)

end Prod

section Scale

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

open NecI NecII Nec93

/-- Cancelling a common nonzero scalar in a `Submodule` quotient: $(cI)/(cJ) = I/J$. -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, pp. 277–279 (transfers of conditions (i), (ii))"]
theorem smul_div_smul {c : F} (hc : c ≠ 0) (I J : Submodule R F) : (c • I) / (c • J) = I / J := by
  ext z
  rw [Submodule.mem_div_iff_forall_mul_mem, Submodule.mem_div_iff_forall_mul_mem]
  constructor
  · intro h j hj
    have := h (c * j) (by simpa using Submodule.smul_mem_pointwise_smul j c J hj)
    obtain ⟨i, hi, he⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 this
    have : i = z * j := by
      have h' : c * i = c * (z * j) := by simpa [mul_left_comm] using he
      exact mul_left_cancel₀ hc h'
    rwa [← this]
  · intro h y hy
    obtain ⟨j, hj, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨z * j, h j hj, by simp [mul_left_comm]⟩

/-- **Conditions (i), (ii) of 93:29 under scaling of the space by $2^k$** (O'Meara 1963, 93:23, as used in §93G,
p. 278 "By scaling $V$ we can assume that $L_1$ and $K_1$ are unimodular"). -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, pp. 277–279 (transfers of conditions (i), (ii))"]
theorem cond29_smul (h2 : IsTwoAdic R) (k : ℤ) {t : ℕ} {Ls Ks : Fin t → Submodule R V}
    (hrk : ∀ i, finrank R (jordanChain Ls i) = finrank R (jordanChain Ks i)) (hC : Cond29 Q Ls Ks) :
    Cond29 (((2 : F) ^ k) • Q) Ls Ks := by
  have hα : (2 : F) ^ k ≠ 0 := two_zpow_ne_zero k
  intro i j hij
  obtain ⟨h1, h2'⟩ := hC i j hij
  have hmul : ∀ A B S : Submodule R F, ((R ∙ ((2 : F) ^ k)) * A * ((R ∙ ((2 : F) ^ k)) * B)) /
      (((R ∙ ((2 : F) ^ k)) * S) * ((R ∙ ((2 : F) ^ k)) * S)) = (A * B) / (S * S) := by
    intro A B S
    simp only [← FundAux.smul_eq_span_mul, smul_mul_assoc, mul_smul_comm, smul_smul]
    exact smul_div_smul (mul_ne_zero hα hα) _ _
  simp only [normIdeal_smul_form, scale_smul_form, hmul]
  refine ⟨(discQuot_smul_iff Q hα (hrk i)).mpr h1, fun hle u hu => ?_⟩
  have hle' : normIdeal Q (Ls j) ≤ (4 : F) • normIdeal Q (Ls i) := by
    rw [← (mul_smul_comm (4 : F) (R ∙ ((2 : F) ^ k)) (normIdeal Q (Ls i)))] at hle
    exact (span_singleton_mul_le_iff hα).1 hle
  have hu0 : R ∙ ((2 : F) ^ (u - k)) = normIdeal Q (Ls i) := by
    have h3 : (R ∙ ((2 : F) ^ (-k))) * (R ∙ ((2 : F) ^ u)) = normIdeal Q (Ls i) := by
      rw [hu, ← mul_assoc, span_singleton_mul_span_singleton', ← zpow_add₀ (two_ne_zero' F), neg_add_cancel,
        zpow_zero, ← Submodule.one_eq_span, one_mul]
    rw [← h3, span_singleton_mul_span_singleton', ← zpow_add₀ (two_ne_zero' F)]
    congr 2; ring
  have := h2' hle' (u - k) hu0
  have e : (2 : F) ^ u = (2 : F) ^ k * (2 : F) ^ (u - k) := by
    rw [← zpow_add₀ (two_ne_zero' F)]; congr 1; ring
  rw [e]
  exact (spanRepresents_smul_iff Q hα _ _ _).mpr this

end Scale

section Map

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {V' : Type*} [AddCommGroup V'] [Module F V'] [Module R V'] [IsScalarTower R F V']
variable (Q : QuadraticForm F V) (Q' : QuadraticForm F V') {φ : V' →ₗ[F] V}

/-- **Conditions (i), (ii) of 93:29 are invariant under an injective isometry $\varphi : V' \to V$.** -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, pp. 277–279 (transfers of conditions (i), (ii))"]
theorem cond29_map (hinj : Function.Injective φ) (hφ : ∀ x, Q (φ x) = Q' x) {X' Y' : Submodule R V'} {t : ℕ}
    {Ls Ks : Fin t → Submodule R V'} (hLs : ∀ i, Ls i ≤ X') (hKs : ∀ i, Ks i ≤ Y') (hXfg : X'.FG) (hYfg : Y'.FG) :
    Cond29 Q (fun i => SuffSub.mapLat φ (Ls i)) (fun i => SuffSub.mapLat φ (Ks i)) ↔ Cond29 Q' Ls Ks := by
  have hcL : ∀ i, jordanChain Ls i ≤ X' := fun i => iSup₂_le fun j _ => hLs j
  have hcK : ∀ i, jordanChain Ks i ≤ Y' := fun i => iSup₂_le fun j _ => hKs j
  unfold Cond29
  refine forall_congr' fun i => forall_congr' fun j => forall_congr' fun _ => ?_
  rw [← SuffSub.jordanChain_map Ls i, ← SuffSub.jordanChain_map Ks i,
    SuffSub.normIdeal_map Q Q' hinj hφ (hLs i), SuffSub.normIdeal_map Q Q' hinj hφ (hLs j),
    SuffSub.scale_map Q Q' hinj hφ (hLs i)]
  refine and_congr (SuffSub.discQuot_map Q Q' hinj hφ _) (imp_congr_right fun _ => forall_congr' fun u =>
    imp_congr_right fun _ => ?_)
  exact SuffSub.spanRepresents_map Q Q' hinj hφ (Submodule.FG.of_le hXfg (hcL i))
    (Submodule.FG.of_le hYfg (hcK i)) _

/-- Conditions (i), (ii) of 93:29 on a subspace $W$ and on $V$ agree. -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, pp. 277–279 (transfers of conditions (i), (ii))"]
theorem cond29_subLatIn {W : Submodule F V} {X Y : Submodule R V} {t : ℕ} {Ls Ks : Fin t → Submodule R V}
    (hX : X ≤ W.restrictScalars R) (hY : Y ≤ W.restrictScalars R) (hLs : ∀ i, Ls i ≤ X) (hKs : ∀ i, Ks i ≤ Y)
    (hXfg : X.FG) (hYfg : Y.FG) :
    Cond29 Q Ls Ks ↔ Cond29 (SuffSub.QW Q W) (fun i => SuffSub.subLatIn W (Ls i))
      (fun i => SuffSub.subLatIn W (Ks i)) := by
  have h := cond29_map Q (SuffSub.QW Q W) (φ := W.subtype) W.injective_subtype (fun x => rfl)
    (X' := SuffSub.subLatIn W X) (Y' := SuffSub.subLatIn W Y) (Ls := fun i => SuffSub.subLatIn W (Ls i))
    (Ks := fun i => SuffSub.subLatIn W (Ks i)) (fun i => SuffSub.subLatIn_mono (hLs i))
    (fun i => SuffSub.subLatIn_mono (hKs i)) (SuffSub.fg_subLatIn hX hXfg) (SuffSub.fg_subLatIn hY hYfg)
  have e1 : (fun i => SuffSub.mapLat W.subtype (SuffSub.subLatIn W (Ls i))) = Ls :=
    funext fun i => SuffSub.map_subLatIn ((hLs i).trans hX)
  have e2 : (fun i => SuffSub.mapLat W.subtype (SuffSub.subLatIn W (Ks i))) = Ks :=
    funext fun i => SuffSub.map_subLatIn ((hKs i).trans hY)
  rw [e1, e2] at h
  exact h

/-- Conditions (i), (ii) of 93:29 are invariant under moving both lattices by $\sigma \in O(V)$. -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, pp. 277–279 (transfers of conditions (i), (ii))"]
theorem cond29_latMap {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q) {X Y : Submodule R V} {t : ℕ} {Ls Ks : Fin t → Submodule R V}
    (hLs : ∀ i, Ls i ≤ X) (hKs : ∀ i, Ks i ≤ Y) (hXfg : X.FG) (hYfg : Y.FG) :
    Cond29 Q (fun i => latMap σ (Ls i)) (fun i => latMap σ (Ks i)) ↔ Cond29 Q Ls Ks :=
  cond29_map Q Q (φ := (σ : V →ₗ[F] V)) σ.injective (SuffSub.latMap_hφ Q hσ) hLs hKs hXfg hYfg

end Map

section Congr

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **Conditions (i), (ii) of 93:29 depend on $K$ only through the isometry classes of its Jordan chain.** -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, pp. 277–279 (transfers of conditions (i), (ii))"]
theorem cond29_congr_right {t : ℕ} {Ls Ks Ks' : Fin t → Submodule R V}
    (hLfg : ∀ i, (jordanChain Ls i).FG) (hKfg : ∀ i, (jordanChain Ks i).FG)
    (hiso : ∀ i, IsometricLat Q Q (jordanChain Ks i) (jordanChain Ks' i)) (hC : Cond29 Q Ls Ks) :
    Cond29 Q Ls Ks' := by
  intro i j hij
  obtain ⟨h1, h2⟩ := hC i j hij
  have hrefl : IsometricLat Q Q (jordanChain Ls i) (jordanChain Ls i) := ⟨LinearEquiv.refl R _, fun x => rfl⟩
  exact ⟨Transfer28.discQuot_of_isometricLat Q Q hrefl (hiso i) h1, fun hle u hu =>
    (RepTransfer.spanRepresents_iff_of_isometricLat Q Q (hLfg i) (hKfg i) hrefl (hiso i) _).mp (h2 hle u hu)⟩

end Congr

section Tail

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

open SuffStep

/-- **Conditions (i), (ii) of 93:29 for the tails** (O'Meara 1963, p. 273, step 3): with $L_1 = K_1$, the conditions for
$L = L_1 \perp L^*$, $K = K_1 \perp K^*$ give those for $L^*$, $K^*$ (the moduli and the numbers $2^u$ depend only on the
components). -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, pp. 277–279 (transfers of conditions (i), (ii))"]
theorem cond29_tail {m : ℕ} {L K : Submodule R V} {Ls Ks : Fin (m + 1) → Submodule R V}
    (h : TailData Q L K Ls Ks) (hC : Cond29 Q Ls Ks) :
    Cond29 Q (fun j : Fin m => Ls j.succ) (fun j : Fin m => Ks j.succ) := by
  intro k l hkl
  obtain ⟨h1, h2⟩ := hC k.succ l.succ (by simp [hkl])
  obtain ⟨hM, hN⟩ := h.orthSums Q k
  obtain ⟨hMfg, hNfg⟩ := h.fgChain Q k
  obtain ⟨hMreg, hNreg⟩ := h.regChain Q k
  refine ⟨(Transfer28.discQuot_isOrthSum_iff Q hM hN (h.iso Q) hMfg hNfg (h.fgFirst Q) hNreg (h.regFirst Q)
    (h.regFirst' Q)).mp h1, fun hle u hu => ?_⟩
  have hc : ((2 : F) ^ u) ≠ 0 := zpow_ne_zero _ (two_ne_zero' F)
  exact (RepTransfer.spanRepresents_iff_of_orthSum Q hM hN hMreg hNreg (h.regFirst Q) (h.fgFirst Q) (h.iso Q) hc).mp
    (h2 hle u hu)

end Tail

section Repl

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

open Dim4

/-- Removing a hyperbolic plane from the component $k_0$ does not change the norms $\mathfrak nL_k$. -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, pp. 277–279 (transfers of conditions (i), (ii))"]
theorem normIdeal_repl_eq {t : ℕ} {Ls : Fin t → Submodule R V} {k0 : Fin t} {P L' : Submodule R V}
    {s0 : Submodule R F} (hPL : IsOrthSum Q (Ls k0) P L') (hP : IsPlane Q P s0)
    (hL'mod : IsModular Q (scale Q (Ls k0)) L') (k : Fin t) :
    normIdeal Q (repl Ls k0 L' k) = normIdeal Q (Ls k) := by
  by_cases h : k = k0
  · subst h
    rw [repl_self, normIdeal_eq_span_normGroup, normIdeal_eq_span_normGroup,
      normGroup_split_plane Q hPL hP hL'mod]
  · rw [repl_of_ne Ls L' h]

/-- **Conditions (i), (ii) of 93:29 after removing a common hyperbolic plane** (O'Meara 1963, p. 272, "by making suitable
cancellations"). -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, pp. 277–279 (transfers of conditions (i), (ii))"]
theorem cond29_repl {t : ℕ} {L K P L' K' : Submodule R V} {Ls Ks : Fin t → Submodule R V} {k0 : Fin t}
    {s0 : Submodule R F} (hLfg : L.FG) (hKfg : K.FG) (hL : IsJordanSplitting Q L Ls)
    (hK : IsJordanSplitting Q K Ks) (hPL : IsOrthSum Q (Ls k0) P L') (hPK : IsOrthSum Q (Ks k0) P K')
    (hP : IsPlane Q P s0) (hL'mod : IsModular Q (scale Q (Ls k0)) L')
    (hK'mod : IsModular Q (scale Q (Ks k0)) K') (hC : Cond29 Q Ls Ks) :
    Cond29 Q (repl Ls k0 L') (repl Ks k0 K') := by
  intro i j hij
  obtain ⟨h1, h2⟩ := hC i j hij
  simp only [normIdeal_repl_eq Q hPL hP hL'mod, scale_repl_eq Q hL'mod]
  refine ⟨(chain_transfer Q hLfg hKfg hL hK hPL hPK hP hL'mod hK'mod i (normIdeal Q (Ls i) * normIdeal Q (Ls j) / (scale Q (Ls i) * scale Q (Ls i)))
    (c := 1) one_ne_zero).1.1 h1,
    fun hle u hu => ?_⟩
  have hc : ((2 : F) ^ u) ≠ 0 := zpow_ne_zero _ (two_ne_zero' F)
  exact (chain_transfer Q hLfg hKfg hL hK hPL hPK hP hL'mod hK'mod i (normIdeal Q (Ls i) * normIdeal Q (Ls j) / (scale Q (Ls i) * scale Q (Ls i)))
    hc).2.1 (h2 hle u hu)

end Repl

section Resplit

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type u} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

open Nec93

/-- The modulus $\mathfrak n_i\mathfrak n_{i+1}/\mathfrak s_i^2$ of condition (i) of 93:29 lies in $\mathfrak f_i$
(O'Meara 1963, §93G, p. 277: $\mathfrak s_i^2\mathfrak f_i \supseteq \mathfrak n_i\mathfrak n_{i+1}$). -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, pp. 277–279 (transfers of conditions (i), (ii))"]
theorem modX_le_fIdeal (h2 : IsTwoAdic R) {L : Submodule R V} (hfg : L.FG) (hreg : IsRegular Q L) {t : ℕ}
    {Ls : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls) (i j : Fin t) (hij : (j : ℕ) = i + 1) :
    normIdeal Q (Ls i) * normIdeal Q (Ls j) / (scale Q (Ls i) * scale Q (Ls i)) ≤ fIdeal Q L Ls i j := by
  obtain ⟨σ, hσ0, hσ⟩ := scale_gen Q hfg hL i
  have hle := normIdeal_mul_le_scale_sq_mul_fIdeal Q h2 hfg hreg hL i j hij
  rw [hσ, FIdealAux.span_mul_span'] at hle ⊢
  intro z hz
  rw [FIdealAux.mem_div_span_iff] at hz
  have h1 := hle hz
  rw [mul_comm z (σ * σ)] at h1
  exact (FundAux.mul_mem_span_mul_iff (mul_ne_zero hσ0 hσ0)).1 h1

/-- $\mathfrak d M/\mathfrak d N \cong 1 \bmod \mathfrak a$ is weaker for a larger ideal. -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, pp. 277–279 (transfers of conditions (i), (ii))"]
theorem discQuot_mono {M N : Submodule R V} {X Y : Submodule R F} (hXY : X ≤ Y)
    (h : DiscQuotSqEquivMod Q M N X) : DiscQuotSqEquivMod Q M N Y := by
  obtain ⟨b, b', ⟨hu, ε, hε, hmem⟩⟩ := h
  exact ⟨b, b', hu, ε, hε, hXY hmem⟩

/-- **Conditions (i), (ii) of 93:29 do not depend on the Jordan splitting of $K$** (O'Meara 1963, §93G, p. 278, "by
(iii) of 93:28"; the analogue of `Resplit.cond93_resplit`): the conditions for $(L_\bullet, K_\bullet)$ give those for
$(L_\bullet, K'_\bullet)$ for another Jordan splitting $K'_\bullet$ of $K$. Condition (i) composes the discriminant
quotients; (ii) is `Resplit.resplit_rep` (necessity of 93:28 for $K$ against $K'$, the discriminant adjusting
$a$ to a fundamental norm generator). -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, pp. 277–279 (transfers of conditions (i), (ii))"]
theorem resplit29 (hHil : PadicClass.LocalHilbertField F) (hDC : DyadicClassification R Q) (h2 : IsTwoAdic R)
    (hQ : (QuadraticMap.associated Q).Nondegenerate) {L K : Submodule R V} [hLl : L.IsLattice F]
    [hKl : K.IsLattice F] {t : ℕ} {Ls Ks Ks' : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls)
    (hK : IsJordanSplitting Q K Ks) (hK' : IsJordanSplitting Q K Ks') (hJ : SameJordanInvariants Q Q Ls Ks)
    (hC : Cond29 Q Ls Ks) : Cond29 Q Ls Ks' := by
  have hπ := twoAdic_irreducible h2
  have h2p : ¬ IsUnit (2 : R) := hπ.not_isUnit
  have hLfg : L.FG := hLl.fg
  have hKfg : K.FG := hKl.fg
  have hLreg := isRegular_of_isLattice Q hQ hLl
  have hKreg := isRegular_of_isLattice Q hQ hKl
  have hJK : SameJordanInvariants Q Q Ks Ks' :=
    (sameJordanInvariants_iff_sameJordanType Q Q h2 hKfg hKfg hK hK').2 (hK.sameJordanType Q hKfg hK')
  have hCK := cond29_of_cls_eq Q hDC h2 hQ K K Ks Ks' hK hK' hJK rfl
  obtain ⟨uu, huu⟩ : ∃ u : Fin t → ℤ, ∀ k, R ∙ ((2 : F) ^ u k) = normIdeal Q (Ls k) :=
    ⟨fun k => (exists_two_pow_eq Q h2 hLfg hL k).choose,
      fun k => (exists_two_pow_eq Q h2 hLfg hL k).choose_spec⟩
  have hS := sameFundamentalInvariants_of_sameJordanInvariants Q Q h2 hLfg hKfg hLreg hKreg hL hK hJ huu
  obtain ⟨h0, hJi⟩ := hJ
  have hc : ∀ k : Fin t, Fin.cast h0 k = k := fun k => Fin.ext rfl
  intro i j hij
  obtain ⟨h1, h2'⟩ := hC i j hij
  obtain ⟨h1K, -⟩ := hCK i j hij
  have hAfg : (jordanChain Ls i).FG := FG.of_le hLfg (NecI.jordanChain_le hL.split i)
  have hBfg : (jordanChain Ks i).FG := FG.of_le hKfg (NecI.jordanChain_le hK.split i)
  have hB'fg : (jordanChain Ks' i).FG := FG.of_le hKfg (NecI.jordanChain_le hK'.split i)
  have hBreg := isRegular_of_isJordanSplitting Q hBfg (isJordanSplitting_jordanChain Q hK i)
  have hB'reg := isRegular_of_isJordanSplitting Q hB'fg (isJordanSplitting_jordanChain Q hK' i)
  have hnI : ∀ k, normIdeal Q (Ks k) = normIdeal Q (Ls k) := fun k => by
    have := (hJi k).2.2; rw [hc] at this; exact this.symm
  have hsI : ∀ k, scale Q (Ks k) = scale Q (Ls k) := fun k => by
    have := (hJi k).2.1; rw [hc] at this; exact this.symm
  refine ⟨?_, fun hle u hu => ?_⟩
  · rw [hnI i, hnI j, hsI i] at h1K
    exact Resplit.discQuot_trans Q hAfg hBfg hB'fg hBreg hB'reg h1 h1K
  · have z2 : ∀ w : ℤ, (2 : F) ^ w ≠ 0 := fun w => two_zpow_ne_zero w
    have hui : u = uu i := by
      have := (FIdealAux.span_eq_iff_dord hπ (z2 u) (z2 (uu i))).1 (hu.trans (huu i).symm)
      rwa [dord_two_zpow h2, dord_two_zpow h2] at this
    subst hui
    have hlt := fIdeal_lt_four_mul_of_normIdeal_le Q h2 hLfg hLreg hL i j hij (a := (2 : F) ^ (uu i)) hu hle
    have hdisc := discQuot_mono Q (modX_le_fIdeal Q h2 hLfg hLreg hL i j hij) h1
    exact Resplit.resplit_rep Q hHil h2p hQ hL hK hK' hS i j i (fun h hl => (h i j hij).2.2 hl) hlt
      (h2' hle (uu i) hu) hdisc

end Resplit

end QuadFormsKB.OMeara.G29
