/-
# O'Meara 93:28, necessity of (ii): the hyperbolic step

**Setting** (as in `Sec93FNecI.lean`).

**Proves** (O'Meara 1963, §93F, proof of 93:28, necessity of (ii), p. 270-271)
* `isFundNormGenerators_prod`: an adjunction does not change the fundamental norm generators;
* `one_div_smul`, `threshold_smul'`: the threshold $4a\,\mathfrak w^{-1}$ under scaling the form;
* `nec_rep_sat`: the analogue of `nec_disc_sat` for representations: for a saturated Jordan splitting with all
  dimensions $\ge 3$, $\mathfrak f_i \subsetneq 4a_j\mathfrak w_j^{-1}$ implies $FK_{(i)} \to FL_{(i)} \perp \langle a_j\rangle$.
-/
import QuadFormsKB.Literature.OMeara.Sec93FNecI
import QuadFormsKB.Literature.OMeara.Sec93FNecII
import QuadFormsKB.Literature.OMeara.Sec93FNecRepMerge

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.NecRepSat

open Sat93 Transfer28 NecBase NecBlock Merge28 NecDual NecMerge Adjoin28 NecI NecII RepTransfer NecRepMerge

section Aux

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {W : Type*} [AddCommGroup W] [Module F W] [Module R W] [IsScalarTower R F W]
variable (Q : QuadraticForm F V) (QW : QuadraticForm F W)

/-- Fundamental norm generators are unchanged by an adjunction with $\mathfrak g(H^{\mathfrak s_k}) \subseteq
\mathfrak g(L^{\mathfrak s_k})$. -/
theorem isFundNormGenerators_prod {L : Submodule R V} {H : Submodule R W} {t : ℕ} {Ls : Fin t → Submodule R V}
    {Hs : Fin t → Submodule R W}
    (hg : ∀ k, normGroup QW (subA QW (scale Q (Ls k)) H) ≤ normGroup Q (subA Q (scale Q (Ls k)) L))
    (hsc : ∀ k, scale (Q.prod QW) ((Ls k).prod (Hs k)) = scale Q (Ls k)) {a : Fin t → F}
    (ha : IsFundNormGenerators Q L Ls a) :
    IsFundNormGenerators (Q.prod QW) (L.prod H) (fun k => (Ls k).prod (Hs k)) a := by
  intro k
  refine ⟨?_, ?_⟩
  · show a k ∈ fundNormGroup (Q.prod QW) (L.prod H) (fun k => (Ls k).prod (Hs k)) k
    rw [fundNormGroup_prod Q QW Ls Hs hg k (hsc k)]
    exact (ha k).1
  · show R ∙ a k = fundNormIdeal (Q.prod QW) (L.prod H) (fun k => (Ls k).prod (Hs k)) k
    rw [fIdeal_fundNormIdeal_eq_span, fundNormGroup_prod Q QW Ls Hs hg k (hsc k), ← fIdeal_fundNormIdeal_eq_span]
    exact (ha k).2

variable (R) in
/-- $1/(\alpha N) = \alpha^{-1}(1/N)$. -/
theorem one_div_smul {α : F} (hα : α ≠ 0) (N : Submodule R F) :
    (1 : Submodule R F) / (α • N) = α⁻¹ • ((1 : Submodule R F) / N) := by
  ext x
  constructor
  · intro hx
    rw [Submodule.mem_smul_pointwise_iff_exists]
    refine ⟨α * x, ?_, by simp [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hα]⟩
    rw [Submodule.mem_div_iff_forall_mul_mem]
    intro y hy
    have := (Submodule.mem_div_iff_forall_mul_mem.1 hx) (α • y)
      ((Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨y, hy, rfl⟩)
    convert this using 1
    simp only [smul_eq_mul]; ring
  · intro hx
    obtain ⟨u, hu, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    rw [Submodule.mem_div_iff_forall_mul_mem]
    intro y hy
    obtain ⟨n, hn, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
    have := (Submodule.mem_div_iff_forall_mul_mem.1 hu) n hn
    convert this using 1
    simp only [smul_eq_mul]; field_simp

/-- The threshold $4a\,\mathfrak w^{-1}$ under scaling the form by $\alpha$. -/
theorem threshold_smul' {α : F} (hα : α ≠ 0) (a : F) (N : Submodule R F) :
    (4 * (α * a)) • ((1 : Submodule R F) / (α • N)) = (4 * a) • ((1 : Submodule R F) / N) := by
  rw [one_div_smul R hα, smul_smul]
  congr 1
  field_simp

end Aux

section Main

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]

set_option maxHeartbeats 1000000 in
/-- **The hyperbolic step for (ii)** (O'Meara 1963, p. 270, "the adjunction of the lattice $L^{-1}$"): for a
saturated Jordan splitting with all dimensions $\ge 3$ and $\mathfrak f_i \subsetneq 4a_j\mathfrak w_j^{-1}$ ($j = i+1$),
$FK_{(i)} \to FL_{(i)} \perp \langle a_j\rangle$. (Proof as `nec_disc_sat`, with `nec_rep_merge`.) -/
@[kb "omeara1963" "§93F, proof of 93:28, necessity of (ii), step 2, pp. 270–271 (the hyperbolic step)"]
theorem nec_rep_sat {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
    [FiniteDimensional F V] (Q : QuadraticForm F V) (hK : PadicClass.LocalHilbertField F) (h2p : ¬ IsUnit (2 : R))
    (h2 : (2 : R) ≠ 0) (hQ : (QuadraticMap.associated Q).Nondegenerate) {L : Submodule R V} [hLl : L.IsLattice F]
    {t : ℕ} {Ls Ks : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls) (hK' : IsJordanSplitting Q L Ks)
    (hdim : ∀ k, 3 ≤ finrank R (Ls k)) (hsat : IsSaturated Q L Ls) {a : Fin t → F}
    (ha : IsFundNormGenerators Q L Ls a) (i j : Fin t) (hij : i.val + 1 = j.val)
    (hlt : fIdeal Q L Ls i j < (4 * a j) • (1 / fundWeight Q L Ls j)) :
    SpanRepresents Q (jordanChain Ks i) (jordanChain Ls i) (a j) := by
  classical
  have hfg : L.FG := hLl.fg
  have ha0 : a j ≠ 0 := by
    rintro h0
    rw [h0] at hlt
    simp at hlt
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
  obtain ⟨hT, hJT⟩ := hL.sameJordanType Q hfg hK'
  have hscKL : ∀ k, scale Q (Ks k) = scale Q (Ls k) := fun k => by
    have := (hJT k).1; rw [show Fin.cast hT k = k from Fin.ext (by simp)] at this; exact this.symm
  -- the adjunction `L ⊥ L⁻¹`
  set Q₃ : QuadraticForm F (V × V) := Q.prod Qn with hQ₃
  set L₃ := L.prod L with hL₃
  set Ls₃ : Fin t → Submodule R (V × V) := fun k => (Ls k).prod (Ls k) with hLs₃
  set Ks₃ : Fin t → Submodule R (V × V) := fun k => (Ks k).prod (Ls k) with hKs₃
  obtain ⟨hJ₃, hrk₃⟩ := isJordanSplitting_prod Q Qn hfg hfg hL hLn.split hmodn
  obtain ⟨hJK₃, -⟩ := isJordanSplitting_prod Q Qn hfg hfg hK' hLn.split (fun k => by
    rw [hscKL k]; exact hmodn k)
  have hLfk : ∀ k, (Ls k).FG := fun k => FG.of_le hfg (hL.split.iSup_eq ▸ le_iSup Ls k)
  have hsc₃ : ∀ k, scale Q₃ (Ls₃ k) = scale Q (Ls k) := fun k =>
    (isModular_prod Q Qn (hL.modular k) (hmodn k) (hLfk k) (hLfk k)).1.2.1
  have hfund₃ : ∀ k, fundNormGroup Q₃ L₃ Ls₃ k = fundNormGroup Q L Ls k := fun k =>
    fundNormGroup_prod Q Qn Ls Ls (fun k => hgn _) k (hsc₃ k)
  have hQnd : (QuadraticMap.associated Qn).Nondegenerate := nondegenerate_smul Q hm1 hQ
  have hQ₃nd : (QuadraticMap.associated Q₃).Nondegenerate := nondegenerate_prod Q Qn hQ hQnd
  have hL₃l : L₃.IsLattice F := isLattice_prod hLl hLl
  have hL₃fg : L₃.FG := hL₃l.fg
  have hdim₃ : ∀ k, 3 ≤ finrank R (Ls₃ k) := fun k => by rw [hrk₃ k]; have := hdim k; omega
  have hsat₃ : IsSaturated Q₃ L₃ Ls₃ := by
    refine ⟨hJ₃, fun k => ?_⟩
    rw [hfund₃, ← hsat.2 k, hLs₃, normGroup_prod, hQn, normGroup_neg_form, sup_idem]
  have ha₃ : IsFundNormGenerators Q₃ L₃ Ls₃ a :=
    isFundNormGenerators_prod Q Qn (fun k => hgn _) hsc₃ ha
  have hfI₃ : fIdeal Q₃ L₃ Ls₃ i j = fIdeal Q L Ls i j :=
    fIdeal_prod_eq Q Qn hfg hfg hL hLn.split hmodn (fun k => hgn _) i j
  have hfw₃ : fundWeight Q₃ L₃ Ls₃ j = fundWeight Q L Ls j :=
    fundWeight_prod_eq Q Qn hfg hfg hL hLn.split hmodn (fun k => hgn _) j
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
  have ha₄ : IsFundNormGenerators Q₄ L₃ Ls₃ (fun k => σ⁻¹ * a k) := isFundNormGenerators_smul_form Q₃ hσi ha₃
  have hlt₄ : fIdeal Q₄ L₃ Ls₃ i j < (4 * (σ⁻¹ * a j)) • (1 / fundWeight Q₄ L₃ Ls₃ j) := by
    rw [hQ₄, fIdeal_smul_form Q₃ hσi, fundWeight_smul_form Q₃ hσi, hfI₃, hfw₃, threshold_smul' hσi]
    exact hlt
  -- the totally isotropic diagonal of `FL^(j) ⊥ F(L⁻¹)^(j)`
  set M := invJordanChain Ls j with hM
  have htail : invJordanChain Ls₃ j = M.prod M := invJordanChain_prod Ls Ls j
  set T : Submodule F (V × V) := (span F (M : Set V)).map (LinearMap.prod LinearMap.id LinearMap.id) with hT'
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
      rw [hT', ← (Submodule.equivMapOfInjective _ hinj (span F (M : Set V))).finrank_eq,
        ← finrank_eq_finrank_span (F := F) M]
    omega
  have h₄ := nec_rep_merge Q₄ hK h2p h2 hQ₄nd hJ₄ hJK₄ i j hij hdim₃ hsat₄ ha₄ hU₄ hTiso hTL hTdim hlt₄
  -- back to `Q₃`, then to `Q`
  have h₃ : SpanRepresents Q₃ (jordanChain Ks₃ i) (jordanChain Ls₃ i) (a j) :=
    (spanRepresents_smul_iff Q₃ hσi _ _ (a j)).mp h₄
  exact rep_of_prod Q Qn hfg hfg hK' hL hLn.split (fun k => by rw [hscKL k]; exact hmodn k) i ha0 h₃

end Main

end QuadFormsKB.OMeara.NecRepSat
