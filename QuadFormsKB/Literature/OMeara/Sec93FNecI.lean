/-
# O'Meara 93:28, the necessity of condition (i)

**Setting** (as in `Sec93FNecMerge.lean`).

**Proves** (O'Meara 1963, §93F, proof of 93:28, necessity, step 2, p. 270: "By making suitable hyperbolic
adjunctions ... we can assume that all fundamental dimensions are $\ge 3$ ... that the given Jordan splittings are
saturated ... that each space $FL_i$ is hyperbolic")
* `disc_of_prod`: condition (i) for $L \perp H$ with the splittings $(L_k \perp H_k)$, $(K_k \perp H_k)$ implies it for
  $L$ when the adjunction does not change the fundamental norm groups;
-/
import QuadFormsKB.Literature.OMeara.Sec93FNecMerge
import QuadFormsKB.Literature.OMeara.Sec93FAdjoin

open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.NecI

open Sat93 Transfer28 NecBase NecBlock Merge28 NecDual NecMerge Adjoin28

section Adjoin

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {W : Type*} [AddCommGroup W] [Module F W] [Module R W] [IsScalarTower R F W]
variable (Q : QuadraticForm F V) (QW : QuadraticForm F W)

theorem jordanChain_le {X : Type*} [AddCommGroup X] [Module F X] [Module R X] [IsScalarTower R F X]
    {Qx : QuadraticForm F X} {L : Submodule R X} {t : ℕ} {Ls : Fin t → Submodule R X} (hL : IsOrthSplit Qx L Ls)
    (i : Fin t) : jordanChain Ls i ≤ L :=
  iSup₂_le fun k _ => hL.iSup_eq ▸ le_iSup Ls k

/-- An orthogonal splitting into modular components with the scales of a Jordan splitting is a Jordan splitting. -/
theorem isJordanSplitting_of_scales {H : Submodule R W} {t : ℕ} {Hs : Fin t → Submodule R W}
    (hH : IsOrthSplit QW H Hs) {s : Fin t → Submodule R F} (hs : StrictAnti s)
    (hmod : ∀ k, IsModular QW (s k) (Hs k)) : IsJordanSplitting QW H Hs := by
  have hsc : ∀ k, scale QW (Hs k) = s k := fun k => (hmod k).2.1
  refine ⟨hH, fun k => (hsc k).symm ▸ hmod k, ?_⟩
  have : (fun k => scale QW (Hs k)) = s := funext hsc
  rw [this]; exact hs

/-- **Condition (i) survives the adjunction** (O'Meara 1963, p. 270): if $H = H_1 \perp \cdots \perp H_t$ with $H_k$
$\mathfrak sL_k$-modular and $\mathfrak g(H^{\mathfrak s_k}) \subseteq \mathfrak g(L^{\mathfrak s_k})$, then
condition (i) at $i$ for $L \perp H$ with the splittings $(L_k \perp H_k)$, $(K_k \perp H_k)$ implies condition (i)
at $i$ for $L$ with $(L_k)$, $(K_k)$. -/
theorem disc_of_prod {L : Submodule R V} {H : Submodule R W} (hLfg : L.FG) (hHfg : H.FG) {t : ℕ}
    {Ls Ks : Fin t → Submodule R V} {Hs : Fin t → Submodule R W} (hL : IsJordanSplitting Q L Ls)
    (hK : IsJordanSplitting Q L Ks) (hH : IsOrthSplit QW H Hs)
    (hHmod : ∀ k, IsModular QW (scale Q (Ls k)) (Hs k))
    (hg : ∀ k, normGroup QW (subA QW (scale Q (Ls k)) H) ≤ normGroup Q (subA Q (scale Q (Ls k)) L))
    (i j : Fin t)
    (h : DiscQuotSqEquivMod (Q.prod QW) (jordanChain (fun k => (Ls k).prod (Hs k)) i)
      (jordanChain (fun k => (Ks k).prod (Hs k)) i)
      (fIdeal (Q.prod QW) (L.prod H) (fun k => (Ls k).prod (Hs k)) i j)) :
    DiscQuotSqEquivMod Q (jordanChain Ls i) (jordanChain Ks i) (fIdeal Q L Ls i j) := by
  have hJH : IsJordanSplitting QW H Hs := isJordanSplitting_of_scales QW hH hL.scale_strictAnti hHmod
  have hLk : ∀ k, (Ls k).FG := fun k => FG.of_le hLfg (hL.split.iSup_eq ▸ le_iSup Ls k)
  have hHk : ∀ k, (Hs k).FG := fun k => FG.of_le hHfg (hH.iSup_eq ▸ le_iSup Hs k)
  have hsc : ∀ k, scale (Q.prod QW) ((Ls k).prod (Hs k)) = scale Q (Ls k) := fun k =>
    (isModular_prod Q QW (hL.modular k) (hHmod k) (hLk k) (hHk k)).1.2.1
  have hfg : ∀ k, fundNormGroup (Q.prod QW) (L.prod H) (fun k => (Ls k).prod (Hs k)) k = fundNormGroup Q L Ls k :=
    fun k => fundNormGroup_prod Q QW Ls Hs hg k (hsc k)
  have hfI : fIdeal (Q.prod QW) (L.prod H) (fun k => (Ls k).prod (Hs k)) i j = fIdeal Q L Ls i j := by
    simp only [fIdeal, fIdeal_fundNormIdeal_eq_span, hfg, hsc]
  rw [hfI, jordanChain_prod, jordanChain_prod] at h
  have hLfg' : (jordanChain Ls i).FG := FG.of_le hLfg (jordanChain_le hL.split i)
  have hKfg' : (jordanChain Ks i).FG := FG.of_le hLfg (jordanChain_le hK.split i)
  have hHfg' : (jordanChain Hs i).FG := FG.of_le hHfg (jordanChain_le hH i)
  refine (discQuot_prod_iff Q QW hLfg' hKfg' hHfg'
    (isRegular_of_isJordanSplitting Q hKfg' (isJordanSplitting_jordanChain Q hK i))
    (isRegular_of_isJordanSplitting QW hHfg' (isJordanSplitting_jordanChain QW hJH i))).mp h

/-- Orthogonal sums of regular spaces are regular. -/
theorem nondegenerate_prod (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hQW : (QuadraticMap.associated QW).Nondegenerate) :
    (QuadraticMap.associated (Q.prod QW)).Nondegenerate := by
  have key : ∀ v w, (∀ v' w', bil (Q.prod QW) (v, w) (v', w') = 0) → (v, w) = 0 := by
    intro v w h
    have hv : v = 0 := hQ.1 v fun v' => by
      have := h v' 0
      rw [adj_bil_prod, show bil QW w 0 = 0 by simp [bil], add_zero] at this
      exact this
    have hw : w = 0 := hQW.1 w fun w' => by
      have := h 0 w'
      rw [adj_bil_prod, show bil Q v 0 = 0 by simp [bil], zero_add] at this
      exact this
    rw [hv, hw]; rfl
  refine ⟨fun ⟨v, w⟩ h => key v w fun v' w' => h (v', w'), fun ⟨v, w⟩ h => key v w fun v' w' => ?_⟩
  have := h (v', w')
  change bil (Q.prod QW) (v', w') (v, w) = 0 at this
  rw [bil_comm]; exact this

/-- The inverse Jordan chains of $L \perp H$. -/
theorem invJordanChain_prod {t : ℕ} (Ls : Fin t → Submodule R V) (Hs : Fin t → Submodule R W) (i : Fin t) :
    invJordanChain (fun k => (Ls k).prod (Hs k)) i = (invJordanChain Ls i).prod (invJordanChain Hs i) := by
  simp only [invJordanChain]
  rw [← Adjoin28.iSup_prod]
  exact iSup_congr fun k => Adjoin28.iSup_prod (fun _ : i ≤ k => Ls k) (fun _ => Hs k)

/-- $L \perp H$ is a lattice on $V \perp W$ when $L$ and $H$ are lattices on $V$ and $W$. -/
theorem isLattice_prod [FiniteDimensional F V] [FiniteDimensional F W] {L : Submodule R V} {H : Submodule R W}
    (hL : L.IsLattice F) (hH : H.IsLattice F) : (L.prod H).IsLattice F := by
  refine ⟨by rw [prod_eq_sup, ← Submodule.map_inl, ← Submodule.map_inr]; exact (hL.fg.map _).sup (hH.fg.map _),
    eq_top_iff.2 fun ⟨v, w⟩ _ => ?_⟩
  have hv : (v, (0 : W)) ∈ span F ((L.prod H : Submodule R (V × W)) : Set (V × W)) := by
    have : v ∈ span F (L : Set V) := by rw [hL.span_eq_top]; trivial
    refine span_induction (p := fun v _ => (v, (0 : W)) ∈ span F ((L.prod H : Submodule R (V × W)) : Set (V × W)))
      (fun x hx => subset_span ⟨hx, zero_mem _⟩) (zero_mem _) (fun a b _ _ ha hb => by
        simpa using add_mem ha hb) (fun c a _ ha => by simpa using smul_mem _ c ha) this
  have hw : ((0 : V), w) ∈ span F ((L.prod H : Submodule R (V × W)) : Set (V × W)) := by
    have : w ∈ span F (H : Set W) := by rw [hH.span_eq_top]; trivial
    refine span_induction (p := fun w _ => ((0 : V), w) ∈ span F ((L.prod H : Submodule R (V × W)) : Set (V × W)))
      (fun x hx => subset_span ⟨zero_mem _, hx⟩) (zero_mem _) (fun a b _ _ ha hb => by
        simpa using add_mem ha hb) (fun c a _ ha => by simpa using smul_mem _ c ha) this
  simpa using add_mem hv hw

end Adjoin

section Scale

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **Condition (i) is unchanged by scaling the space** (O'Meara 1963, 93:23): for lattices of the same rank,
$d(M^\alpha)/d(N^\alpha) = dM/dN$. -/
theorem discQuot_smul_iff {α : F} (hα : α ≠ 0) {M N : Submodule R V} (hrk : finrank R M = finrank R N)
    {X : Submodule R F} : DiscQuotSqEquivMod (α • Q) M N X ↔ DiscQuotSqEquivMod Q M N X := by
  have hg : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (x : ι → V),
      (gram (α • Q) x).det = α ^ Fintype.card ι * (gram Q x).det := by
    intro ι _ _ x
    have : gram (α • Q) x = α • gram Q x := by ext i j; simp [gram, bil_smul_form]
    rw [this, Matrix.det_smul]
  have hpow : α ^ finrank R M = α ^ finrank R N := by rw [hrk]
  constructor
  · rintro ⟨b, b', h⟩
    refine ⟨b, b', ?_⟩
    rw [hg, hg, Fintype.card_fin, Fintype.card_fin, hpow, mul_div_mul_left _ _ (pow_ne_zero _ hα)] at h
    exact h
  · rintro ⟨b, b', h⟩
    refine ⟨b, b', ?_⟩
    rw [hg, hg, Fintype.card_fin, Fintype.card_fin, hpow, mul_div_mul_left _ _ (pow_ne_zero _ hα)]
    exact h

/-- A nonzero multiple of a regular form is regular. -/
theorem nondegenerate_smul {α : F} (hα : α ≠ 0) (hQ : (QuadraticMap.associated Q).Nondegenerate) :
    (QuadraticMap.associated (α • Q)).Nondegenerate := by
  refine ⟨fun x hx => hQ.1 x fun y => ?_, fun x hx => hQ.2 x fun y => ?_⟩
  · have := hx y
    change bil (α • Q) x y = 0 at this
    rw [bil_smul_form] at this
    exact (mul_eq_zero.mp this).resolve_left hα
  · have := hx y
    change bil (α • Q) y x = 0 at this
    rw [bil_smul_form] at this
    exact (mul_eq_zero.mp this).resolve_left hα

end Scale

section Main

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]

set_option maxHeartbeats 1000000 in
/-- **The hyperbolic step** (O'Meara 1963, p. 270, "the adjunction of the lattice $L^{-1}$"): for a saturated Jordan
splitting with all dimensions $\ge 3$, condition (i) holds at every index $i$. (Adjoin $L$ with the form $-Q$: then
$FL^{(j)} \perp F(L^{-1})^{(j)}$ contains the totally isotropic diagonal; scale; apply `nec_disc_merge`.) -/
theorem nec_disc_sat {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
    [FiniteDimensional F V] (Q : QuadraticForm F V) (hK : PadicClass.LocalHilbertField F) (h2p : ¬ IsUnit (2 : R))
    (h2 : (2 : R) ≠ 0) (hQ : (QuadraticMap.associated Q).Nondegenerate) {L : Submodule R V} [hLl : L.IsLattice F]
    {t : ℕ} {Ls Ks : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls) (hK' : IsJordanSplitting Q L Ks)
    (hdim : ∀ k, 3 ≤ finrank R (Ls k)) (hsat : IsSaturated Q L Ls) (i j : Fin t) (hij : i.val + 1 = j.val) :
    DiscQuotSqEquivMod Q (jordanChain Ls i) (jordanChain Ks i) (fIdeal Q L Ls i j) := by
  classical
  have hfg : L.FG := hLl.fg
  set Qn : QuadraticForm F V := (-1 : F) • Q with hQn
  have hm1 : (-1 : F) ≠ 0 := by norm_num
  have hspan1 : (R ∙ (-1 : F)) = 1 := by
    rw [Submodule.one_eq_span]; apply le_antisymm
    · rw [span_singleton_le_iff_mem]; exact mem_span_singleton.2 ⟨-1, by simp⟩
    · rw [span_singleton_le_iff_mem]; exact mem_span_singleton.2 ⟨-1, by simp⟩
  -- `L` with the form `-Q`
  have hLn : IsJordanSplitting Qn L Ls := isJordanSplitting_smul_form Q hm1 hL
  have hscn : ∀ k, scale Qn (Ls k) = scale Q (Ls k) := fun k => by
    rw [hQn, scale_smul_form, hspan1, one_mul]
  have hmodn : ∀ k, IsModular Qn (scale Q (Ls k)) (Ls k) := fun k => (hscn k) ▸ hLn.modular k
  have hgn : ∀ s : Submodule R F, normGroup Qn (subA Qn s L) ≤ normGroup Q (subA Q s L) := by
    intro s
    have h1 := FundAux.subA_smul_form Q hm1 s L
    rw [hspan1, one_mul] at h1
    rw [h1, hQn, normGroup_neg_form]
  -- the adjunction `L ⊥ L⁻¹`
  set Q₃ : QuadraticForm F (V × V) := Q.prod Qn with hQ₃
  set L₃ := L.prod L with hL₃
  set Ls₃ : Fin t → Submodule R (V × V) := fun k => (Ls k).prod (Ls k) with hLs₃
  set Ks₃ : Fin t → Submodule R (V × V) := fun k => (Ks k).prod (Ls k) with hKs₃
  obtain ⟨hJ₃, hrk₃⟩ := isJordanSplitting_prod Q Qn hfg hfg hL hLn.split hmodn
  obtain ⟨hJK₃, -⟩ := isJordanSplitting_prod Q Qn hfg hfg hK' hLn.split (fun k => by
    obtain ⟨hT, hJT⟩ := hL.sameJordanType Q hfg hK'
    have := (hJT k).1; rw [show Fin.cast hT k = k from Fin.ext (by simp)] at this
    rw [← this]; exact hmodn k)
  have hsc₃ : ∀ k, scale Q₃ (Ls₃ k) = scale Q (Ls k) := fun k =>
    (isModular_prod Q Qn (hL.modular k) (hmodn k) (FG.of_le hfg (hL.split.iSup_eq ▸ le_iSup Ls k))
      (FG.of_le hfg (hL.split.iSup_eq ▸ le_iSup Ls k))).1.2.1
  have hfund₃ : ∀ k, fundNormGroup Q₃ L₃ Ls₃ k = fundNormGroup Q L Ls k := fun k =>
    fundNormGroup_prod Q Qn Ls Ls (fun k => hgn _) k (hsc₃ k)
  have hQnd : (QuadraticMap.associated Qn).Nondegenerate := nondegenerate_smul Q hm1 hQ
  have hQ₃nd : (QuadraticMap.associated Q₃).Nondegenerate := nondegenerate_prod Q Qn hQ hQnd
  have hL₃l : L₃.IsLattice F := isLattice_prod hLl hLl
  have hL₃fg : L₃.FG := hL₃l.fg
  have hLk : ∀ k, 1 ≤ finrank R (Ls k) := fun k => by have := hdim k; omega
  have hdim₃ : ∀ k, 3 ≤ finrank R (Ls₃ k) := fun k => by rw [hrk₃ k]; have := hdim k; omega
  have hsat₃ : IsSaturated Q₃ L₃ Ls₃ := by
    refine ⟨hJ₃, fun k => ?_⟩
    rw [hfund₃, ← hsat.2 k, hLs₃, normGroup_prod, hQn, normGroup_neg_form, sup_idem]
  -- scale so that `𝔰_j = 𝔬`
  obtain ⟨σ, hσ0, hσ⟩ := exists_eq_span_singleton (R := R)
    ((hL.modular j).2.1 ▸ scale_fg Q (FG.of_le hfg (hL.split.iSup_eq ▸ le_iSup Ls j))) (hL.modular j).1
  have hσi : σ⁻¹ ≠ 0 := inv_ne_zero hσ0
  set Q₄ : QuadraticForm F (V × V) := σ⁻¹ • Q₃ with hQ₄
  have hJ₄ : IsJordanSplitting Q₄ L₃ Ls₃ := isJordanSplitting_smul_form Q₃ hσi hJ₃
  have hJK₄ : IsJordanSplitting Q₄ L₃ Ks₃ := isJordanSplitting_smul_form Q₃ hσi hJK₃
  have hsat₄ : IsSaturated Q₄ L₃ Ls₃ := (isSaturated_smul_form_iff Q₃ hσi).mpr hsat₃
  have hU₄ : scale Q₄ (Ls₃ j) = 1 := by
    rw [hQ₄, scale_smul_form, hsc₃, hσ, FIdealAux.span_mul_span', inv_mul_cancel₀ hσ0,
      ← Submodule.one_eq_span]
  have hQ₄nd : (QuadraticMap.associated Q₄).Nondegenerate := nondegenerate_smul Q₃ hσi hQ₃nd
  -- the totally isotropic diagonal of `FL^(j) ⊥ F(L⁻¹)^(j)`
  set M := invJordanChain Ls j with hM
  have htail : invJordanChain Ls₃ j = M.prod M := invJordanChain_prod Ls Ls j
  set T : Submodule F (V × V) := (span F (M : Set V)).map (LinearMap.prod LinearMap.id LinearMap.id) with hT
  have hTiso : ∀ x ∈ T, Q₄ x = 0 := by
    intro x hx
    obtain ⟨v, -, rfl⟩ := Submodule.mem_map.mp hx
    show (σ⁻¹ • Q.prod ((-1 : F) • Q)) (v, v) = 0
    rw [smul_apply, QuadraticMap.prod_apply, smul_apply]
    simp
  have hTL : ∀ x ∈ T, x ∈ span F (invJordanChain Ls₃ j : Set (V × V)) := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hx
    rw [htail]
    have h1 : ∀ v ∈ span F (M : Set V), (v, (0 : V)) ∈ span F ((M.prod M : Submodule R (V × V)) : Set (V × V)) :=
      fun v hv => span_induction (p := fun v _ => (v, (0 : V)) ∈ span F ((M.prod M : Submodule R (V × V)) : Set _))
        (fun x hx => subset_span (show (x, (0 : V)) ∈ ((M.prod M : Submodule R (V × V)) : Set (V × V)) from
          ⟨hx, zero_mem _⟩)) (zero_mem _) (fun a b _ _ ha hb => by simpa using add_mem ha hb)
        (fun c a _ ha => by simpa using smul_mem _ c ha) hv
    have h2 : ∀ v ∈ span F (M : Set V), ((0 : V), v) ∈ span F ((M.prod M : Submodule R (V × V)) : Set (V × V)) :=
      fun v hv => span_induction (p := fun v _ => ((0 : V), v) ∈ span F ((M.prod M : Submodule R (V × V)) : Set _))
        (fun x hx => subset_span (show ((0 : V), x) ∈ ((M.prod M : Submodule R (V × V)) : Set (V × V)) from
          ⟨zero_mem _, hx⟩)) (zero_mem _) (fun a b _ _ ha hb => by simpa using add_mem ha hb)
        (fun c a _ ha => by simpa using smul_mem _ c ha) hv
    simpa using add_mem (h1 v hv) (h2 v hv)
  have hTdim : finrank R (invJordanChain Ls₃ j) ≤ 2 * finrank F T := by
    rw [htail]
    have hMfg : M.FG := FG.of_le hfg (iSup₂_le fun k _ => hL.split.iSup_eq ▸ le_iSup Ls k)
    have hprod : finrank R (M.prod M) = finrank R M + finrank R M := by
      have h := isOrthSum_finrank Q₃ (adj_isOrthSum_prod_split Q Qn M M) (by
        rw [prod_eq_sup, ← Submodule.map_inl, ← Submodule.map_inr]; exact (hMfg.map _).sup (hMfg.map _))
      obtain ⟨f₁, -⟩ := adj_isometricLat_prod_bot Q Qn M
      obtain ⟨f₂, -⟩ := adj_isometricLat_bot_prod Q Qn M
      rw [h, ← f₁.finrank_eq, ← f₂.finrank_eq]
    have hTr : finrank F T = finrank R M := by
      have hinj : Function.Injective (LinearMap.prod (LinearMap.id : V →ₗ[F] V) LinearMap.id) :=
        fun a b h => by simpa using congrArg Prod.fst h
      rw [hT, ← (Submodule.equivMapOfInjective _ hinj (span F (M : Set V))).finrank_eq,
        ← finrank_eq_finrank_span (F := F) M]
    omega
  -- fundamental norm generators of the new lattice
  have ha₄ : ∃ a : Fin t → F, IsFundNormGenerators Q₄ L₃ Ls₃ a := by
    choose x _ hx using fun k => exists_isNormGenerator_Q Q₄ (fundSub_fg Q₄ hL₃fg Ls₃ k)
    exact ⟨fun k => Q₄ (x k), hx⟩
  obtain ⟨a₄, ha₄⟩ := ha₄
  have h₄ := NecMerge.nec_disc_merge Q₄ hK h2p h2 hQ₄nd hJ₄ hJK₄ i j hij hdim₃ hsat₄ ha₄ hU₄ hTiso hTL hTdim
  -- back to `Q₃`, then to `Q`
  have hrkc : finrank R (jordanChain Ls₃ i) = finrank R (jordanChain Ks₃ i) := by
    rw [(isJordanSplitting_jordanChain Q₃ hJ₃ i).split.finrank_eq_sum (F := F),
      (isJordanSplitting_jordanChain Q₃ hJK₃ i).split.finrank_eq_sum (F := F)]
    refine Finset.sum_congr rfl fun k _ => ?_
    obtain ⟨hT', hJT'⟩ := hJ₃.sameJordanType Q₃ hL₃fg hJK₃
    have := (hJT' (chainIdx i k)).2.1; rwa [show Fin.cast hT' (chainIdx i k) = chainIdx i k from Fin.ext (by simp)]
      at this
  rw [hQ₄, discQuot_smul_iff Q₃ hσi hrkc, fIdeal_smul_form Q₃ hσi] at h₄
  exact disc_of_prod Q Qn hfg hfg hL hK' hLn.split hmodn (fun k => hgn _) i j h₄


set_option maxHeartbeats 1000000 in
/-- **93:28, necessity of condition (i)** (O'Meara 1963, §93F, pp. 268–271): for two Jordan splittings
$L = L_1 \perp \cdots \perp L_t = K_1 \perp \cdots \perp K_t$ of the same lattice on a regular quadratic space over a
dyadic local field, $dL_{(i)}/dK_{(i)} \cong 1 \bmod \mathfrak f_i$ for $1 \le i \le t-1$. The adjunctions of
O'Meara's step 2: $L \perp L \perp L$ (all dimensions $\ge 3$), then a copy of it with a saturated splitting (93:21),
then `nec_disc_sat`. -/
@[kb "omeara1963" "§93F, proof of 93:28, necessity of condition (i), pp. 268–271"]
theorem nec_disc {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
    [FiniteDimensional F V] (Q : QuadraticForm F V) (hK : PadicClass.LocalHilbertField F) (h2p : ¬ IsUnit (2 : R))
    (h2 : (2 : R) ≠ 0) (hQ : (QuadraticMap.associated Q).Nondegenerate) {L : Submodule R V} [hLl : L.IsLattice F]
    {t : ℕ} {Ls Ks : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls) (hK' : IsJordanSplitting Q L Ks)
    (i j : Fin t) (hij : i.val + 1 = j.val) :
    DiscQuotSqEquivMod Q (jordanChain Ls i) (jordanChain Ks i) (fIdeal Q L Ls i j) := by
  classical
  have hfg : L.FG := hLl.fg
  have hLk : ∀ k, (Ls k).FG := fun k => FG.of_le hfg (hL.split.iSup_eq ▸ le_iSup Ls k)
  obtain ⟨hT, hJT⟩ := hL.sameJordanType Q hfg hK'
  have hscKL : ∀ k, scale Q (Ks k) = scale Q (Ls k) := fun k => by
    have := (hJT k).1; rw [show Fin.cast hT k = k from Fin.ext (by simp)] at this; exact this.symm
  -- (A1) `L ⊥ (L ⊥ L)`: all dimensions `≥ 3`
  set QW : QuadraticForm F (V × V) := Q.prod Q with hQW
  set H := L.prod L with hH
  set Hs : Fin t → Submodule R (V × V) := fun k => (Ls k).prod (Ls k) with hHs
  obtain ⟨hJH, hrkH⟩ := isJordanSplitting_prod Q Q hfg hfg hL hL.split (fun k => hL.modular k)
  have hHmod : ∀ k, IsModular QW (scale Q (Ls k)) (Hs k) := fun k =>
    (isModular_prod Q Q (hL.modular k) (hL.modular k) (hLk k) (hLk k)).1
  have hgH : ∀ k, normGroup QW (subA QW (scale Q (Ls k)) H) ≤ normGroup Q (subA Q (scale Q (Ls k)) L) := by
    intro k; rw [hQW, hH, subA_prod, normGroup_prod, sup_idem]
  have hHl : H.IsLattice F := isLattice_prod hLl hLl
  obtain ⟨hJ₁, hrk₁⟩ := isJordanSplitting_prod Q QW hfg hHl.fg hL hJH.split hHmod
  obtain ⟨hJK₁, -⟩ := isJordanSplitting_prod Q QW hfg hHl.fg hK' hJH.split (fun k => (hscKL k).symm ▸ hHmod k)
  set Q₁ : QuadraticForm F (V × (V × V)) := Q.prod QW with hQ₁
  set L₁ := L.prod H with hL₁
  set Ls₁ : Fin t → Submodule R (V × (V × V)) := fun k => (Ls k).prod (Hs k) with hLs₁
  set Ks₁ : Fin t → Submodule R (V × (V × V)) := fun k => (Ks k).prod (Hs k) with hKs₁
  have hL₁l : L₁.IsLattice F := isLattice_prod hLl hHl
  have hQ₁nd : (QuadraticMap.associated Q₁).Nondegenerate :=
    nondegenerate_prod Q QW hQ (nondegenerate_prod Q Q hQ hQ)
  have hdim₁ : ∀ k, 3 ≤ finrank R (Ls₁ k) := by
    intro k
    rw [hrk₁ k, show finrank R ((Ls k).prod (Ls k)) = _ from hrkH k]
    have : 1 ≤ finrank R (Ls k) := Nat.one_le_iff_ne_zero.mpr fun h0 => by
      have hb := (hL.modular k).1
      obtain ⟨b⟩ := exists_basis (R := R) (F := F) (hLk k)
      have : Ls k = ⊥ := by
        rw [← span_basis_eq b, span_eq_bot]; rintro _ ⟨k', rfl⟩; exact Fin.elim0 (h0 ▸ k')
      rw [(hL.modular k).2.1.symm, this, scale_bot] at hb; exact hb rfl
    omega
  -- (A2) a saturated splitting `Js` of `L₁` (93:21), adjoined
  obtain ⟨Js, hJs⟩ := (Sat93.saturatedSplittingExistence (R := R) hK Q₁).exists_saturated h2p hQ₁nd L₁ Ls₁ hJ₁ hdim₁
  have hL₁fg : L₁.FG := hL₁l.fg
  obtain ⟨hT₁, hJT₁⟩ := hJ₁.sameJordanType Q₁ hL₁fg hJs.1
  have hscJs : ∀ k, scale Q₁ (Js k) = scale Q₁ (Ls₁ k) := fun k => by
    have := (hJT₁ k).1; rw [show Fin.cast hT₁ k = k from Fin.ext (by simp)] at this; exact this.symm
  have hJsmod : ∀ k, IsModular Q₁ (scale Q₁ (Ls₁ k)) (Js k) := fun k => hscJs k ▸ hJs.1.modular k
  obtain ⟨hJ₂, hrk₂⟩ := isJordanSplitting_prod Q₁ Q₁ hL₁fg hL₁fg hJ₁ hJs.1.split hJsmod
  obtain ⟨hJK₂, -⟩ := isJordanSplitting_prod Q₁ Q₁ hL₁fg hL₁fg hJK₁ hJs.1.split (fun k => by
    obtain ⟨hT', hJT'⟩ := hJ₁.sameJordanType Q₁ hL₁fg hJK₁
    have := (hJT' k).1; rw [show Fin.cast hT' k = k from Fin.ext (by simp)] at this
    rw [← this]; exact hJsmod k)
  have hsc₂ : ∀ k, scale (Q₁.prod Q₁) ((Ls₁ k).prod (Js k)) = scale Q₁ (Ls₁ k) := fun k =>
    (isModular_prod Q₁ Q₁ (hJ₁.modular k) (hJsmod k) (FG.of_le hL₁fg (hJ₁.split.iSup_eq ▸ le_iSup Ls₁ k))
      (FG.of_le hL₁fg (hJs.1.split.iSup_eq ▸ le_iSup Js k))).1.2.1
  have hsat₂ : IsSaturated (Q₁.prod Q₁) (L₁.prod L₁) (fun k => (Ls₁ k).prod (Js k)) := by
    refine ⟨hJ₂, fun k => ?_⟩
    rw [fundNormGroup_prod Q₁ Q₁ Ls₁ Js (fun k => le_rfl) k (hsc₂ k), normGroup_prod,
      fundNormGroup_eq_of_isJordanSplitting hL₁fg hJs.1 hJ₁ k k rfl, ← hJs.2 k]
    exact sup_eq_right.mpr (hJs.2 k ▸ (fundNormGroup_eq_of_isJordanSplitting hL₁fg hJs.1 hJ₁ k k rfl).symm ▸
      normGroup_le_fundNormGroup Q₁ hL₁fg hJ₁ k)
  have hdim₂ : ∀ k, 3 ≤ finrank R ((Ls₁ k).prod (Js k)) := fun k => by rw [hrk₂ k]; have := hdim₁ k; omega
  have hL₂l : (L₁.prod L₁).IsLattice F := isLattice_prod hL₁l hL₁l
  have h₂ := nec_disc_sat (Q₁.prod Q₁) hK h2p h2 (nondegenerate_prod Q₁ Q₁ hQ₁nd hQ₁nd) hJ₂ hJK₂ hdim₂ hsat₂
    i j hij
  have h₁ := disc_of_prod Q₁ Q₁ hL₁fg hL₁fg hJ₁ hJK₁ hJs.1.split hJsmod (fun k => le_rfl) i j h₂
  exact disc_of_prod Q QW hfg hHl.fg hL hK' hJH.split hHmod hgH i j h₁

end Main

end QuadFormsKB.OMeara.NecI
