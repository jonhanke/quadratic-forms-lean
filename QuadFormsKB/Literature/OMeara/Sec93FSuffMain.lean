/-
# O'Meara 93:28, sufficiency: the induction

**Setting** (as in `Sec93FSuffGood.lean`).

**Proves** (O'Meara 1963, §93F, proof of 93:28, sufficiency, pp. 272–273)
* `suff_zero`, `suff_one`: the cases $t = 0$ and $t = 1$ (step 1, 93:16);
* `isOrthSum_zero_tail`, `span_tail_eq_perp`: $L = L_1 \perp L^*$ and $FL^* = (FL_1)^\perp$;
* `sameFund_resplit`: the fundamental invariants do not depend on the Jordan splitting of $K$.
-/
import QuadFormsKB.Literature.OMeara.Sec93FSuffGood
import QuadFormsKB.Literature.OMeara.Sec93FSuffWitt
import QuadFormsKB.Literature.OMeara.Sec93FSuffStep
import QuadFormsKB.Literature.OMeara.Sec93FSuffSub

open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.SuffMain

open Sat93 Adjoin28 NecI Suff28 SuffRed SuffGood SuffStep

section Basic

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- The orthogonal complement $(FA)^\perp$ of a lattice $A$, as a subspace. -/
def perpF (A : Submodule R V) : Submodule F V where
  carrier := {x | ∀ y ∈ A, bil Q x y = 0}
  add_mem' hx hy z hz := by rw [Set.mem_setOf_eq] at *; rw [bil_add_left, hx z hz, hy z hz, add_zero]
  zero_mem' z _ := by simp [bil]
  smul_mem' c x hx z hz := by rw [Set.mem_setOf_eq] at *; rw [bil_smul_left, hx z hz, mul_zero]

/-- $L = L_1 \perp L^*$ for a Jordan splitting. -/
theorem isOrthSum_zero_tail {m : ℕ} {L : Submodule R V} (hfg : L.FG) {Ls : Fin (m + 1) → Submodule R V}
    (hL : IsJordanSplitting Q L Ls) : IsOrthSum Q L (Ls 0) (tailLat Ls) := by
  have hreg : IsRegular Q (Ls 0) :=
    (hL.modular 0).isRegular Q (Submodule.FG.of_le hfg (hL.split.iSup_eq ▸ le_iSup Ls 0))
  refine ⟨fun x hx y hy => orth_zero_tail Q hL.split hx hy, ?_, ?_⟩
  · rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    exact (mem_bot R).mpr (hreg x hx1 fun y hy => orth_tail_zero Q hL.split hx2 hy)
  · rw [← hL.split.iSup_eq, iSup_eq_zero_sup]

/-- **$FL^* = (FL_1)^\perp$**: if a lattice $L$ on $V$ is $A \perp T$ with $A$ regular, then $FT = (FA)^\perp$. -/
theorem span_eq_perpF {L A T : Submodule R V} [L.IsLattice F] (hA : IsRegular Q A) (h : IsOrthSum Q L A T) :
    span F (T : Set V) = perpF Q A := by
  have hle : span F (T : Set V) ≤ perpF Q A := span_le.mpr fun x hx y hy => by
    rw [bil_comm]; exact h.orth y hy x hx
  refine le_antisymm hle fun x hx => ?_
  have htop : x ∈ span F (L : Set V) := by rw [Submodule.IsLattice.span_eq_top (A := F)]; trivial
  have hsup : span F (L : Set V) ≤ span F (A : Set V) ⊔ span F (T : Set V) := by
    refine span_le.mpr fun v hv => ?_
    rw [← h.sup_eq] at hv
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup.mp hv
    exact add_mem (mem_sup_left (subset_span ha)) (mem_sup_right (subset_span hb))
  obtain ⟨a, ha, s, hs, rfl⟩ := mem_sup.mp (hsup htop)
  have hap : a ∈ perpF Q A := by
    have := sub_mem hx (hle hs); simpa using this
  have ha0 : a = 0 := by
    obtain ⟨d, hd0, hd⟩ := exists_smul_mem_of_mem_span (F := F) (S := A) ha
    have h0 : d • a = 0 := hA _ hd fun z hz => by
      rw [bil_rsmul_left, hap z hz, mul_zero]
    have hdF : algebraMap R F d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).2 hd0
    rw [← algebraMap_smul F d a] at h0
    exact (smul_eq_zero.mp h0).resolve_left hdF
  rw [ha0, zero_add]; exact hs

/-- $K \in \operatorname{cls} L$ gives $L \cong K$. -/
theorem isometricLat_of_cls_eq {L K : Submodule R V} (h : cls Q L = cls Q K) : IsometricLat Q Q L K := by
  have hL : L ∈ cls Q K := h ▸ mem_cls_self Q L
  obtain ⟨σ, hσ, rfl⟩ := hL
  exact adj_isometricLat_symm Q Q (isometricLat_latMap Q hσ K)

/-- **The fundamental invariants do not depend on the Jordan splitting of $K$**: if `Ks`, `Ks'` are Jordan splittings
of $K$ and $L$, $K$ have the same fundamental invariants for `Ls`, `Ks`, then also for `Ls`, `Ks'`. -/
theorem sameFund_resplit {L K : Submodule R V} (hKfg : K.FG) {t : ℕ} {Ls Ks Ks' : Fin t → Submodule R V}
    (hK : IsJordanSplitting Q K Ks) (hK' : IsJordanSplitting Q K Ks') {a : Fin t → F}
    (hS : SameFundamentalInvariants Q Q L K Ls Ks a) : SameFundamentalInvariants Q Q L K Ls Ks' a := by
  obtain ⟨⟨h0, hT⟩, haL, haK⟩ := hS
  obtain ⟨h1, hJ⟩ := hK.sameJordanType Q hKfg hK'
  have hc : ∀ k : Fin t, Fin.cast h0 k = k := fun k => Fin.ext (by simp)
  have hc1 : ∀ k : Fin t, Fin.cast h1 k = k := fun k => Fin.ext (by simp)
  have hsc : ∀ k, scale Q (Ks' k) = scale Q (Ks k) := fun k => by have := (hJ k).1; rw [hc1] at this; exact this.symm
  have hfs : ∀ k, fundSub Q K Ks' k = fundSub Q K Ks k := fun k => by simp only [fundSub, hsc k]
  refine ⟨⟨h0, fun k => ⟨?_, ?_, ?_⟩⟩, haL, fun k => ?_⟩
  · have := (hT k).1; have h2 := (hJ k).2.1; rw [hc] at this ⊢; rw [hc1] at h2; rw [this, h2]
  · have := (hT k).2.1; rw [hc] at this ⊢; rw [this, hsc]
  · have := (hT k).2.2; rw [hc] at this ⊢; rw [this]; simp only [fundNormGroup, hfs]
  · rw [IsFundNormGenerators] at haK; have := haK k; rwa [← hfs k] at this

/-- $FA \perp (FA)^\perp$. -/
theorem perpF_orth_span {A : Submodule R V} {w : V} (hw : w ∈ perpF Q A) {u : V} (hu : u ∈ span F (A : Set V)) :
    bil Q w u = 0 := by
  refine span_induction (p := fun u _ => bil Q w u = 0) (fun x hx => hw x hx) (by simp [bil])
    (fun x y _ _ hx hy => by rw [bil_add_right, hx, hy, add_zero])
    (fun c x _ hx => by rw [bil_smul_right, hx, mul_zero]) hu

/-- $FA + (FA)^\perp = V$ when $L = A \perp T$ is a lattice on $V$. -/
theorem span_sup_perpF {L A T : Submodule R V} [L.IsLattice F] (hA : IsRegular Q A) (h : IsOrthSum Q L A T) :
    span F (A : Set V) ⊔ perpF Q A = ⊤ := by
  rw [← span_eq_perpF Q hA h, eq_top_iff, ← Submodule.IsLattice.span_eq_top (A := F) (M := L)]
  refine span_le.mpr fun v hv => ?_
  rw [← h.sup_eq] at hv
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup.mp hv
  exact add_mem (mem_sup_left (subset_span ha)) (mem_sup_right (subset_span hb))

/-- **Conditions (i)–(iii) depend on $K$ only through the isometry classes of its Jordan chain.** -/
theorem cond93_congr_right {L : Submodule R V} {t : ℕ} {Ls Ks Ks' : Fin t → Submodule R V} {a : Fin t → F}
    (hLfg : ∀ i, (jordanChain Ls i).FG) (hKfg : ∀ i, (jordanChain Ks i).FG)
    (hiso : ∀ i, IsometricLat Q Q (jordanChain Ks i) (jordanChain Ks' i)) (hC : Cond93 Q L Ls Ks a) :
    Cond93 Q L Ls Ks' a := by
  intro i j hij
  obtain ⟨h1, h2, h3⟩ := hC i j hij
  have hrefl : IsometricLat Q Q (jordanChain Ls i) (jordanChain Ls i) := ⟨LinearEquiv.refl R _, fun x => rfl⟩
  exact ⟨Transfer28.discQuot_of_isometricLat Q Q hrefl (hiso i) h1,
    fun h => (RepTransfer.spanRepresents_iff_of_isometricLat Q Q (hLfg i) (hKfg i) hrefl (hiso i) _).mp (h2 h),
    fun h => (RepTransfer.spanRepresents_iff_of_isometricLat Q Q (hLfg i) (hKfg i) hrefl (hiso i) _).mp (h3 h)⟩

/-- **The fundamental invariants after moving $K$ by $\sigma \in O(V)$.** -/
theorem sameFund_moveK {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q) {L K : Submodule R V} {t : ℕ}
    {Ls Ks : Fin t → Submodule R V} (hKs : ∀ i, Ks i ≤ K) {a : Fin t → F}
    (hS : SameFundamentalInvariants Q Q L K Ls Ks a) :
    SameFundamentalInvariants Q Q L (latMap σ K) Ls (fun i => latMap σ (Ks i)) a := by
  have hinj : Function.Injective (σ : V →ₗ[F] V) := σ.injective
  have hφ : ∀ x, Q ((σ : V →ₗ[F] V) x) = Q x := fun x => hσ x
  obtain ⟨⟨h0, hT⟩, haL, haK⟩ := hS
  refine ⟨⟨h0, fun k => ⟨?_, ?_, ?_⟩⟩, haL, (SuffSub.isFundNormGenerators_map Q Q hinj hφ hKs a).mpr haK⟩
  · rw [(hT k).1]; exact (SuffSub.finrank_map Q Q hinj hφ (hKs _)).symm
  · rw [(hT k).2.1]; exact (SuffSub.scale_map Q Q hinj hφ (hKs _)).symm
  · rw [(hT k).2.2]; exact (SuffSub.fundNormGroup_map Q Q hinj hφ hKs _).symm

end Basic

section Base

universe u v

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type u} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]

/-- **The case $t = 0$**: $L = K = 0$. -/
theorem suff_zero : Suff.{u, v} R F 0 := by
  intro V _ _ _ _ _ Q _ _ L K _ _ Ls Ks a hL hK _ _
  have h1 := hL.split.iSup_eq; have h2 := hK.split.iSup_eq
  rw [iSup_of_empty] at h1 h2
  rw [← h1, ← h2]; exact ⟨LinearEquiv.refl R _, fun x => rfl⟩

/-- **The case $t = 1$** (O'Meara 1963, p. 272, step 1): two $\mathfrak s$-modular lattices with the same norm group
are isometric (93:16). -/
theorem suff_one : Suff.{u, v} R F 1 := by
  intro V _ _ _ _ _ Q _ _ L K _ _ Ls Ks a hL hK hS _
  have hL0 : Ls 0 = L := by have := hL.split.iSup_eq; rwa [iSup_unique] at this
  have hK0 : Ks 0 = K := by have := hK.split.iSup_eq; rwa [iSup_unique] at this
  obtain ⟨⟨h0, hT⟩, -, -⟩ := hS
  have hsc : scale Q (Ls 0) = scale Q (Ks 0) := (hT 0).2.1
  have hfg : fundNormGroup Q L Ls 0 = fundNormGroup Q K Ks 0 := (hT 0).2.2
  have hLfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hKfg : K.FG := Submodule.IsLattice.fg (A := F)
  simp only [fundNormGroup, fundSub] at hfg
  rw [← hL0, NecMerge.subA_eq_self Q le_rfl, ← hK0, NecMerge.subA_eq_self Q le_rfl, hK0, hL0] at hfg
  obtain ⟨x, -, y, -, hxy⟩ := exists_scale_eq Q (hL0 ▸ hLfg)
  have hmL := hL.modular 0
  have hmK := hK.modular 0
  rw [hL0] at hmL; rw [hK0] at hmK
  have hne : bil Q x y ≠ 0 := fun h => hmL.1 (by rw [← hL0, hxy, h, span_singleton_eq_bot])
  rw [hL0] at hxy hsc; rw [hK0] at hsc
  rw [← hsc, hxy] at hmK; rw [hxy] at hmL
  exact isometricLat_of_cls_eq Q (suff_base Q hne hmL hmK hfg)

/-- **The tail data** (O'Meara 1963, p. 273, step 3): if $L = L_1 \perp L^*$, $K = L_1 \perp K^*$ with saturated
splittings and the same fundamental invariants and conditions, the tails have the same fundamental invariants and
satisfy the conditions. -/
theorem tail_conds {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
    [FiniteDimensional F V] (Q : QuadraticForm F V) {L K : Submodule R V} (hLfg : L.FG) (hKfg : K.FG) {m : ℕ}
    {Ls Ks : Fin (m + 2) → Submodule R V} (hL : IsSaturated Q L Ls) (hK : IsSaturated Q K Ks) (h0 : Ls 0 = Ks 0)
    {a : Fin (m + 2) → F} (ha0 : ∀ k, a k ≠ 0) (hS : SameFundamentalInvariants Q Q L K Ls Ks a)
    (hC : Cond93 Q L Ls Ks a) :
    SameFundamentalInvariants Q Q (tailLat Ls) (tailLat Ks) (fun k : Fin (m + 1) => Ls k.succ)
      (fun k : Fin (m + 1) => Ks k.succ) (fun k => a k.succ) ∧
    Cond93 Q (tailLat Ls) (fun k : Fin (m + 1) => Ls k.succ) (fun k : Fin (m + 1) => Ks k.succ)
      (fun k => a k.succ) := by
  have htd : TailData Q L K Ls Ks := ⟨hL, hK.1, hLfg, hKfg, h0⟩
  obtain ⟨⟨hh, hT⟩, haL, haK⟩ := hS
  have hc : ∀ k : Fin (m + 2), Fin.cast hh k = k := fun k => Fin.ext (by simp)
  refine ⟨⟨⟨rfl, fun k => ⟨?_, ?_, ?_⟩⟩, isFundNormGenerators_tail Q hL a haL, isFundNormGenerators_tail Q hK a haK⟩,
    fun i j hij => ?_⟩
  · have := (hT k.succ).1; rw [hc] at this; exact this
  · have := (hT k.succ).2.1; rw [hc] at this; exact this
  · have := (hT k.succ).2.2; rw [hc] at this
    simp only [Fin.cast_eq_self]
    rw [fund_tail Q hL k, fund_tail Q hK k]; exact this
  · obtain ⟨h1, h2, h3⟩ := hC i.succ j.succ (by simp [hij])
    exact ⟨(cond1_tail Q htd i j).mp h1, (cond2_tail Q htd a i j (ha0 _)).mp h2,
      (cond3_tail Q htd a i j (ha0 _)).mp h3⟩

/-- **The induction step of the sufficiency** (O'Meara 1963, §93F, proof of 93:28, sufficiency, step 3, p. 273):
granted the core (`SuffCore`, steps 4–8), the sufficiency for $t - 1$ components gives it for good lattices with
$t$ components. The core gives a new saturated splitting of $K$ with $K_1' \cong L_1$; by Witt's theorem we can take
$K_1' = L_1$; the tails $L^*$, $K^*$ lie on $W = (FL_1)^\perp$ and satisfy the hypotheses there, so $L^* \cong K^*$
and $L = L_1 \perp L^* \cong L_1 \perp K^* = K$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 3, p. 273 (the induction step)"]
theorem good_succ (hcore : SuffCore.{u, v} R F) {m : ℕ} (ih : Suff.{u, v} R F (m + 1)) :
    GoodSuff.{u, v} R F (m + 2) := by
  intro V _ _ _ _ _ Q h2p hQ L K _ _ Ls Ks a hLs hKs hd hT hsc hS hC
  have hLfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hKfg : K.FG := Submodule.IsLattice.fg (A := F)
  have hregL := isRegular_of_lattice_max Q hQ ‹L.IsLattice F›
  have ha0 : ∀ k, a k ≠ 0 := fun k =>
    (hS.2.1 k).ne_zero Q (isRegular_fundSub Q hLfg hregL hLs.1 k) (fundSub_ne_bot Q hLfg hLs.1 k)
  obtain ⟨Ks', hKs', hiso0, hC'⟩ := hcore.core Q h2p hQ L K m Ls Ks a hLs hKs hd hT (hsc 0 rfl) hS hC
  have hS' := sameFund_resplit Q hKfg hKs.1 hKs'.1 hS
  have hKle : ∀ k, Ks' k ≤ K := fun k => hKs'.1.split.iSup_eq ▸ le_iSup Ks' k
  have hLle : ∀ k, Ls k ≤ L := fun k => hLs.1.split.iSup_eq ▸ le_iSup Ls k
  have hK0fg : (Ks' 0).FG := FG.of_le hKfg (hKle 0)
  have hK0reg : IsRegular Q (Ks' 0) := (hKs'.1.modular 0).isRegular Q hK0fg
  obtain ⟨σ, hσ, hσK⟩ := SuffWitt.exists_orth_latMap_eq Q hQ hK0fg hK0reg (adj_isometricLat_symm Q Q hiso0)
  set Ks'' : Fin (m + 2) → Submodule R V := fun k => latMap σ (Ks' k) with hKs''
  have hK'lat : (latMap σ K).IsLattice F := SuffSub.isLattice_latMap
  have hK'fg : (latMap σ K).FG := Submodule.IsLattice.fg (A := F)
  have hK'sat : IsSaturated Q (latMap σ K) Ks'' := SuffSub.isSaturated_latMap Q hσ hKle hKfg hKs'
  have hS'' : SameFundamentalInvariants Q Q L (latMap σ K) Ls Ks'' a := sameFund_moveK Q hσ hKle hS'
  have hchfg : ∀ {X : Submodule R V} {Xs : Fin (m + 2) → Submodule R V}, X.FG → (∀ k, Xs k ≤ X) →
      ∀ i, (jordanChain Xs i).FG := fun hX hle i => FG.of_le hX (iSup₂_le fun j _ => hle j)
  have hC'' : Cond93 Q L Ls Ks'' a := cond93_congr_right Q (hchfg hLfg hLle) (hchfg hKfg hKle)
    (fun i => by rw [hKs'', ← SuffSub.jordanChain_latMap]; exact isometricLat_latMap Q hσ _) hC'
  have h0 : Ls 0 = Ks'' 0 := hσK.symm
  obtain ⟨hSt, hCt⟩ := tail_conds Q hLfg hK'fg hLs hK'sat h0 ha0 hS'' hC''
  -- the subspace `W = (F L₁)^⊥`
  have hL0fg : (Ls 0).FG := FG.of_le hLfg (hLle 0)
  have hLreg0 : IsRegular Q (Ls 0) := (hLs.1.modular 0).isRegular Q hL0fg
  have hoL := isOrthSum_zero_tail Q hLfg hLs.1
  have hoK := isOrthSum_zero_tail Q hK'fg hK'sat.1
  rw [← h0] at hoK
  set W := perpF Q (Ls 0) with hW
  have hspL : span F (tailLat Ls : Set V) = W := span_eq_perpF Q hLreg0 hoL
  have hspK : span F (tailLat Ks'' : Set V) = W := span_eq_perpF Q hLreg0 hoK
  have hLW : tailLat Ls ≤ W.restrictScalars R := fun x hx => hspL ▸ subset_span hx
  have hKW : tailLat Ks'' ≤ W.restrictScalars R := fun x hx => hspK ▸ subset_span hx
  have hLtfg : (tailLat Ls).FG := FG.of_le hLfg (tailLat_le Q hLs.1.split)
  have hKtfg : (tailLat Ks'').FG := FG.of_le hK'fg (tailLat_le Q hK'sat.1.split)
  have hLWl := SuffSub.isLattice_subLatIn hLW hLtfg hspL
  have hKWl := SuffSub.isLattice_subLatIn hKW hKtfg hspK
  have hQW : (QuadraticMap.associated (SuffSub.QW Q W)).Nondegenerate :=
    SuffSub.nondegenerate_QW Q hQ (span_sup_perpF Q hLreg0 hoL) fun w hw u hu => perpF_orth_span Q hw hu
  have hsLs : ∀ i : Fin (m + 1), Ls i.succ ≤ tailLat Ls := fun i => le_iSup (fun k : Fin (m + 1) => Ls k.succ) i
  have hsKs : ∀ i : Fin (m + 1), Ks'' i.succ ≤ tailLat Ks'' := fun i =>
    le_iSup (fun k : Fin (m + 1) => Ks'' k.succ) i
  have hJL := SuffSub.isJordanSplitting_subLatIn Q hLW hsLs hLtfg (isJordanSplitting_tail Q hLs.1)
  have hJK := SuffSub.isJordanSplitting_subLatIn Q hKW hsKs hKtfg (isJordanSplitting_tail Q hK'sat.1)
  have hSW := (SuffSub.sameFundamentalInvariants_subLatIn Q hLW hKW hsLs hsKs _).mp hSt
  have hCW := (SuffSub.cond93_subLatIn Q hLW hKW hsLs hsKs hLtfg hKtfg _).mp hCt
  have hisoW := ih (SuffSub.QW Q W) h2p hQW _ _ _ _ _ hJL hJK hSW hCW
  have hisoT := (SuffSub.isometricLat_subLatIn Q hLW hKW).mpr hisoW
  have hLK' := isometricLat_of_tail Q hL0fg hLtfg hoL hoK hisoT
  exact adj_isometricLat_trans Q Q Q hLK' (adj_isometricLat_symm Q Q (isometricLat_latMap Q hσ K))

/-- **The sufficiency in 93:28, granted the core** (O'Meara 1963, §93F, proof of the sufficiency, pp. 272–273):
for every number of Jordan components $t$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, pp. 272–273"]
theorem suff_all (hHil : PadicClass.LocalHilbertField F) (hcore : SuffCore.{u, v} R F) : ∀ t, Suff.{u, v} R F t
  | 0 => suff_zero
  | 1 => suff_one
  | m + 2 => suff_of_good hHil (good_succ hcore (suff_all hHil hcore (m + 1)))

end Base

end QuadFormsKB.OMeara.SuffMain
