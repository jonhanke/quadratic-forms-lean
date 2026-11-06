/-
# Hanke 2011, Def. 6.1 for every lattice: the adelic stabilizer $SO(\hat L)$ of an arbitrary lattice

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (bib key `hanke2011structure`), Def. 6.1 and Theorem 6.2, pp. 25–26; the mass is Hanke 2005's
$\mathrm{Mass}(\Lambda,\varphi)$ [(5.4)–(5.6)] (bib key `hanke2005crelle`).

**Setting.** $F$ a number field, $Q_0$ a nondegenerate quadratic form over $\mathcal O_F$ in $n$ variables (any signature),
$V = (F^n, Q)$ with $Q = Q_0\otimes F$, and $L$ an **arbitrary** lattice on $V$ (`Lat F n`: any Steinitz class). The library's
proper-class decomposition (`ClassicalSetup.lean`, `ClassicalDiscrete.lean`, `SiegelIndefinite.lean`) is written for
$L = \mathcal O_F^n$; here it is redone for $L$.

**Proves** (unconditional, standard axioms only)
* `isOpen_locStab_lat`, `isCompact_locStab_lat`: $O(\hat L) = \{h\in O(V)(\mathbb A_f) : h_{\mathfrak p}L_{\mathfrak p} = L_{\mathfrak p}\
  \forall\mathfrak p\}$ is compact open for every lattice $L$ (it contains the open subgroup $O(\hat L)\cap O(\hat{\mathcal O}_F^n)$
  with finite index);
* `KSOLat Q₀ L` $= SO(\hat L) = O(\hat L)\cap SO(V)(\mathbb A_f)$, compact open (`isCompact_KSOLat`, `isOpen_KSOLat`), equal to
  the library's `KSO Q₀` for $L = \mathcal O_F^n$ (`KSOLat_std`);
* `DCLat Q₀ L`: the double cosets $SO(V)(F)\backslash SO(V)(\mathbb A_f)/SO(\hat L)$ (the proper classes in the genus of $L$),
  countable, with representatives `dcRepLat`; `unitGroupLat Q₀ L i` $= \Gamma_i = SO(M_i)$ in $G_\infty = SO(V)(F\otimes\mathbb R)$,
  discrete (`discreteTopology_levelGroup_of_isCompact`);
* **`covolume_eq_muFin_KSOLat_mul_tsum`**: $\operatorname{covol}(SO(V)(F)\backslash SO(V)(\mathbb A)) =
  \mu_f(SO(\hat L))\cdot\sum_i\operatorname{vol}(\Gamma_i\backslash G_\infty)$ for Weil's Tamagawa measure, for every lattice $L$.
-/
import QuadFormsKB.Literature.Hanke2011Structure.GlobalMass
import QuadFormsKB.Literature.Hanke2011Structure.GlobalMassLattice

namespace QuadFormsKB.Hanke2011Structure

open MeasureTheory Measure MulAction Set NumberField IsDedekindDomain
open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil
  QuadFormsKB.Tamagawa.Indefinite
open scoped ENNReal

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 400000

/-! ### A subgroup with a compact subgroup of finite index is compact -/

section Compact

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- If $U \le H$ is compact of finite index in $H$, then $H$ is compact (a finite union of translates of $U$). -/
theorem isCompact_of_le_of_relIndex_ne_zero {H U : Subgroup G} (hU : IsCompact (U : Set G)) (hle : U ≤ H)
    (hfin : U.relIndex H ≠ 0) : IsCompact (H : Set G) := by
  classical
  have : (U.subgroupOf H).FiniteIndex := ⟨hfin⟩
  have : Finite (H ⧸ U.subgroupOf H) := Subgroup.finite_quotient_of_finiteIndex
  have hH : (H : Set G) =
      ⋃ q : H ⧸ U.subgroupOf H, (fun x => ((Quotient.out q : H) : G) * x) '' (U : Set G) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_image, SetLike.mem_coe]
    constructor
    · intro hx
      refine ⟨(QuotientGroup.mk ⟨x, hx⟩ : H ⧸ U.subgroupOf H), ?_⟩
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (U.subgroupOf H) ⟨x, hx⟩
      refine ⟨((h : H) : G)⁻¹, U.inv_mem (Subgroup.mem_subgroupOf.mp h.2), ?_⟩
      rw [hh]
      simp
    · rintro ⟨q, u, hu, rfl⟩
      exact H.mul_mem (Quotient.out q).2 (hle hu)
  rw [hH]
  exact isCompact_iUnion fun q => hU.image (continuous_const.mul continuous_id)

end Compact

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-! ### $O(\hat L)$ is compact open for every lattice -/

section Topology

variable (Q : QuadForm F n)

/-- $h \in O(\hat L)\cap O(\hat{\mathcal O}_F^n)$ iff $h \in O(\hat{\mathcal O}_F^n)$ and $h_{\mathfrak p}L_{\mathfrak p} = L_{\mathfrak p}$ at the
finitely many $\mathfrak p$ with $L_{\mathfrak p}\ne\mathfrak o_{\mathfrak p}^n$. -/
theorem mem_locStab_inf_std_iff (L : Lat F n) (h : OAf Q) :
    h ∈ locStab Q L ⊓ locStab Q (Tamagawa.stdLat F n) ↔ h ∈ locStab Q (Tamagawa.stdLat F n) ∧
      ∀ v ∈ {v : HeightOneSpectrum (𝓞 F) | ¬ loc v L.1 = std v},
        h v ∈ stabLat v (orthGroup Q (v.adicCompletion F)).subtype (loc v L.1) := by
  constructor
  · rintro ⟨hL, hstd⟩
    exact ⟨hstd, fun v _ => hL v⟩
  · rintro ⟨hstd, hS⟩
    refine ⟨fun v => ?_, hstd⟩
    by_cases hv : loc v L.1 = std v
    · have h1 := hstd v
      change locAct v _ (loc v intVec) = loc v intVec at h1
      rw [loc_intVec] at h1
      change locAct v _ (loc v L.1) = loc v L.1
      rw [hv]
      exact h1
    · exact hS v hv

/-- **$O(\hat L)$ is open** in $O(V)(\mathbb A_f)$, for every lattice $L$. -/
@[kb "omeara1963" "§101A, 101:4 (ii), p. 289"]
theorem isOpen_locStab_lat (L : Lat F n) : IsOpen (locStab Q L : Set (OAf Q)) := by
  classical
  set S := {v : HeightOneSpectrum (𝓞 F) | ¬ loc v L.1 = std v}
  have hS : S.Finite := Filter.eventually_cofinite.mp (loc_eventually_std L.2)
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), IsOpen ((fun f : OAf Q => f v) ⁻¹'
      (stabLat v (orthGroup Q (v.adicCompletion F)).subtype (loc v L.1) : Set (orthGroup Q (v.adicCompletion F)))) := by
    intro v
    obtain ⟨γ, hγ⟩ := exists_locAct_std_model v L
    rw [hγ]
    exact (isOpen_stabLat v Q γ).preimage (RestrictedProduct.continuous_eval v)
  have hU : IsOpen ((locStab Q (Tamagawa.stdLat F n) : Set (OAf Q)) ∩
      ⋂ v ∈ S, (fun f : OAf Q => f v) ⁻¹'
        (stabLat v (orthGroup Q (v.adicCompletion F)).subtype (loc v L.1) : Set (orthGroup Q (v.adicCompletion F)))) :=
    (isOpen_locStab Q).inter (hS.isOpen_biInter fun v _ => hloc v)
  have he : ((locStab Q L ⊓ locStab Q (Tamagawa.stdLat F n) : Subgroup (OAf Q)) : Set (OAf Q)) =
      (locStab Q (Tamagawa.stdLat F n) : Set (OAf Q)) ∩
        ⋂ v ∈ S, (fun f : OAf Q => f v) ⁻¹'
          (stabLat v (orthGroup Q (v.adicCompletion F)).subtype (loc v L.1) :
            Set (orthGroup Q (v.adicCompletion F))) := by
    ext h
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
    exact mem_locStab_inf_std_iff Q L h
  rw [← he] at hU
  exact Subgroup.isOpen_mono inf_le_left hU

/-- **$O(\hat L)$ is compact**, for every lattice $L$: $O(\hat L)\cap O(\hat{\mathcal O}_F^n)$ is a compact open subgroup of
finite index in it (`commensurable_locStab`). -/
theorem isCompact_locStab_lat (L : Lat F n) : IsCompact (locStab Q L : Set (OAf Q)) := by
  have hUo : IsOpen ((locStab Q L ⊓ locStab Q (Tamagawa.stdLat F n) : Subgroup (OAf Q)) : Set (OAf Q)) :=
    (isOpen_locStab_lat Q L).inter (isOpen_locStab Q)
  have hUc : IsCompact ((locStab Q L ⊓ locStab Q (Tamagawa.stdLat F n) : Subgroup (OAf Q)) : Set (OAf Q)) :=
    (isCompact_locStab Q).of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hUo)
      (fun x hx => hx.2)
  refine isCompact_of_le_of_relIndex_ne_zero hUc inf_le_left ?_
  rw [Subgroup.inf_relIndex_left]
  exact relIndex_locStab_ne_zero Q L (Tamagawa.stdLat F n)

end Topology

/-! ### $SO(\hat L)$ and the proper classes in the genus of $L$ -/

section SO

variable (Q₀ : QuadForm (𝓞 F) n)

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

/-- **$SO(\hat L) = O(\hat L)\cap SO(V)(\mathbb A_f)$** for an arbitrary lattice $L$ on $V = (F^n, Q_0\otimes F)$, as a subgroup of
$SO(V)(\mathbb A_f)$ (`KSO Q₀` is the case $L = \mathcal O_F^n$). -/
abbrev KSOLat (L : Lat F n) : Subgroup (SOAf Q₀) := (locStab QF L).subgroupOf (soAf QF)

theorem KSOLat_std : KSOLat Q₀ (Tamagawa.stdLat F n) = KSO Q₀ := rfl

theorem isCompact_KSOLat (L : Lat F n) : IsCompact (KSOLat Q₀ L : Set (SOAf Q₀)) :=
  (isClosed_soAf QF).isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_locStab_lat QF L)

theorem isOpen_KSOLat (L : Lat F n) : IsOpen (KSOLat Q₀ L : Set (SOAf Q₀)) :=
  (isOpen_locStab_lat QF L).preimage continuous_subtype_val

/-- **$SO(V)(\mathbb A_f)/SO(\hat L)$ is countable**: $g\,SO(\hat L)\mapsto gL$ is injective (`cosetLat_injective`). -/
theorem countable_SOAf_quot_lat (L : Lat F n) : Countable (SOAf Q₀ ⧸ KSOLat Q₀ L) := by
  have := countable_lat (F := F) (n := n)
  let ι : SOAf Q₀ ⧸ KSOLat Q₀ L → OAf QF ⧸ locStab QF L :=
    Quotient.map' (fun a : SOAf Q₀ => (a : OAf QF)) (fun a b hab => by
      rw [QuotientGroup.leftRel_apply] at hab ⊢; exact hab)
  refine Function.Injective.countable (f := fun y => cosetLat QF L (ι y)) fun x y h => ?_
  induction x using QuotientGroup.induction_on with | H a => ?_
  induction y using QuotientGroup.induction_on with | H b => ?_
  have h' := cosetLat_injective QF L h
  change (QuotientGroup.mk (a : OAf QF) : OAf QF ⧸ locStab QF L) = QuotientGroup.mk (b : OAf QF) at h'
  rw [QuotientGroup.eq] at h' ⊢
  rw [Subgroup.mem_subgroupOf]
  simpa using h'

/-- The relation $b\sim b'$ iff $b' = \gamma bk$ with $\gamma\in SO(V)(F)$, $k\in SO(\hat L)$. -/
def dcSetoidLat (L : Lat F n) : Setoid (SOAf Q₀) where
  r b b' := ∃ γ ∈ GammaSOAdele Q₀, ∃ k ∈ KSOLat Q₀ L, b' = γ.2 * b * k
  iseqv := by
    refine ⟨fun b => ⟨1, (GammaSOAdele Q₀).one_mem, 1, (KSOLat Q₀ L).one_mem, by simp⟩, ?_, ?_⟩
    · rintro b b' ⟨γ, hγ, k, hk, rfl⟩
      refine ⟨γ⁻¹, (GammaSOAdele Q₀).inv_mem hγ, k⁻¹, (KSOLat Q₀ L).inv_mem hk, ?_⟩
      simp [mul_assoc]
    · rintro b b' b'' ⟨γ, hγ, k, hk, rfl⟩ ⟨γ', hγ', k', hk', rfl⟩
      refine ⟨γ' * γ, (GammaSOAdele Q₀).mul_mem hγ' hγ, k * k', (KSOLat Q₀ L).mul_mem hk hk', ?_⟩
      simp [mul_assoc]

/-- **The double cosets** $SO(V)(F)\backslash SO(V)(\mathbb A_f)/SO(\hat L)$: the proper classes in the genus of $L$. -/
abbrev DCLat (L : Lat F n) : Type := Quotient (dcSetoidLat Q₀ L)

instance countable_DCLat (L : Lat F n) : Countable (DCLat Q₀ L) := by
  have := countable_SOAf_quot_lat Q₀ L
  let f : SOAf Q₀ ⧸ KSOLat Q₀ L → DCLat Q₀ L :=
    Quotient.lift (fun b : SOAf Q₀ => (⟦b⟧ : DCLat Q₀ L)) fun b b' h =>
      Quotient.sound ⟨1, (GammaSOAdele Q₀).one_mem, b⁻¹ * b', QuotientGroup.leftRel_apply.mp h, by simp⟩
  refine Function.Surjective.countable (f := f) ?_
  rintro ⟨b⟩
  exact ⟨QuotientGroup.mk b, rfl⟩

/-- Representatives $b_i$ of the double cosets of $SO(\hat L)$. -/
def dcRepLat (L : Lat F n) (i : DCLat Q₀ L) : SOAf Q₀ := Quotient.out i

theorem dcRepLat_cov (L : Lat F n) (g : SOAf Q₀) :
    ∃ i, ∃ γ ∈ GammaSOAdele Q₀, ∃ k ∈ KSOLat Q₀ L, g = γ.2 * dcRepLat Q₀ L i * k :=
  ⟨⟦g⟧, Quotient.mk_out (s := dcSetoidLat Q₀ L) g⟩

theorem dcRepLat_disj (L : Lat F n) (i j : DCLat Q₀ L) (γ : SOAdele Q₀) (hγ : γ ∈ GammaSOAdele Q₀) (k : SOAf Q₀)
    (hk : k ∈ KSOLat Q₀ L) (k' : SOAf Q₀) (hk' : k' ∈ KSOLat Q₀ L)
    (h : γ.2 * dcRepLat Q₀ L i * k = dcRepLat Q₀ L j * k') : i = j := by
  have hrel : (dcSetoidLat Q₀ L) (dcRepLat Q₀ L i) (dcRepLat Q₀ L j) :=
    ⟨γ, hγ, k * k'⁻¹, (KSOLat Q₀ L).mul_mem hk ((KSOLat Q₀ L).inv_mem hk'), by
      rw [← mul_assoc, h, mul_inv_cancel_right]⟩
  rw [← Quotient.out_eq i, ← Quotient.out_eq j]
  exact Quotient.sound hrel

/-- **The unit group of the class $i$** in the genus of $L$: $\Gamma_i = SO(M_i)$, $M_i = b_i\hat L\cap V$, viewed in
$G_\infty$ (the image of $SO(V)(F)\cap(G_\infty\times b_iSO(\hat L)b_i^{-1})$). -/
abbrev unitGroupLat (L : Lat F n) (i : DCLat Q₀ L) : Subgroup (GInfSO Q₀) :=
  levelGroup (GammaSOAdele Q₀) (KSOLat Q₀ L) (dcRepLat Q₀ L i)

/-- **The unit groups are discrete in $G_\infty$** for every compact subgroup $K\le SO(V)(\mathbb A_f)$
(`discreteTopology_levelGroup` for $K = SO(\hat{\mathcal O}_F^n)$). -/
theorem discreteTopology_levelGroup_of_isCompact (K : Subgroup (SOAf Q₀)) (hK : IsCompact (K : Set (SOAf Q₀)))
    (b : SOAf Q₀) : DiscreteTopology (levelGroup (GammaSOAdele Q₀) K b) := by
  haveI := discreteTopology_GammaSOAdele Q₀
  have hcl : IsClosed ((GammaSOAdele Q₀ : Subgroup (SOAdele Q₀)) : Set (SOAdele Q₀)) :=
    Subgroup.isClosed_of_discreteTopology
  obtain ⟨C, hCc, hC⟩ := exists_compact_mem_nhds (1 : GInfSO Q₀)
  set M : Set (SOAf Q₀) := (fun x => b * x * b⁻¹) '' (K : Set (SOAf Q₀)) with hM
  have hMc : IsCompact M := hK.image (by fun_prop)
  have hfin : (((GammaSOAdele Q₀ : Subgroup (SOAdele Q₀)) : Set (SOAdele Q₀)) ∩ C ×ˢ M).Finite := by
    have hcpt : IsCompact (((GammaSOAdele Q₀ : Subgroup (SOAdele Q₀)) : Set (SOAdele Q₀)) ∩ C ×ˢ M) :=
      (hCc.prod hMc).inter_left hcl
    exact hcpt.finite (IsDiscrete.mono (DiscreteTopology.isDiscrete (s :=
      ((GammaSOAdele Q₀ : Subgroup (SOAdele Q₀)) : Set (SOAdele Q₀)))) Set.inter_subset_left)
  set H := levelGroup (GammaSOAdele Q₀) K b with hH
  have hHC : ((H : Set (GInfSO Q₀)) ∩ C).Finite := by
    refine (hfin.image Prod.fst).subset ?_
    rintro a ⟨ha, haC⟩
    obtain ⟨g, ⟨hgΓ, hgK⟩, rfl⟩ := Subgroup.mem_map.mp ha
    refine ⟨g, ⟨hgΓ, haC, ?_⟩, rfl⟩
    refine ⟨b⁻¹ * g.2 * b, hgK, ?_⟩
    simp [mul_assoc]
  set Fs : Set (GInfSO Q₀) := ((H : Set (GInfSO Q₀)) ∩ C) \ {1} with hFs
  have hFsc : IsClosed Fs := (hHC.subset Set.sdiff_subset).isClosed
  have hopen : IsOpen (interior C \ Fs) := isOpen_interior.sdiff hFsc
  rw [discreteTopology_iff_isOpen_singleton_one]
  refine isOpen_induced_iff.mpr ⟨interior C \ Fs, hopen, ?_⟩
  ext ⟨x, hx⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Subgroup.mk_eq_one]
  constructor
  · rintro ⟨hxi, hxF⟩
    by_contra hne
    exact hxF ⟨⟨hx, interior_subset hxi⟩, hne⟩
  · rintro rfl
    exact ⟨mem_interior_iff_mem_nhds.mpr hC, fun h => h.2 rfl⟩

/-- **Exact measurable fundamental domain of $\Gamma_b$** in $G_\infty$, for a compact $K$. -/
theorem exists_fd_levelGroup_of_isCompact (K : Subgroup (SOAf Q₀)) (hK : IsCompact (K : Set (SOAf Q₀)))
    (b : SOAf Q₀) :
    ∃ D : Set (GInfSO Q₀), MeasurableSet D ∧
      ∀ a : GInfSO Q₀, ∃! s : levelGroup (GammaSOAdele Q₀) K b, s • a ∈ D := by
  haveI := discreteTopology_levelGroup_of_isCompact Q₀ K hK b
  exact exists_measurableSet_forall_existsUnique_smul_mem (levelGroup (GammaSOAdele Q₀) K b)

/-- **The β-decomposition of the covolume for an arbitrary lattice** (any signature, any number field):
$$\operatorname{covol}(SO(V)(F)\backslash SO(V)(\mathbb A),\mu_{\mathrm{Tam}}) = \mu_f(SO(\hat L))\cdot
\sum_{i}\operatorname{vol}(\Gamma_i\backslash G_\infty,\mu_\infty),$$
$\Gamma_i$ = `unitGroupLat Q₀ L i`, $\mu_\infty$ = `muArchTamSO`, $\mu_f$ = `muFin` (Weil's measure on $SO(V)(\mathbb A_f)$). -/
@[kb "weil1982" "§2.4, p. 23 (τ(G) = vol(G_𝔸/G_k)); the decomposition along the classes of a genus [unverified]"]
theorem covolume_eq_muFin_KSOLat_mul_tsum (hQ : Q₀.Nondegenerate) (L : Lat F n) :
    covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ fun _ => 1) =
      muFin Q₀ (fun _ => 1) (KSOLat Q₀ L) *
        ∑' i, covolume (unitGroupLat Q₀ L i) (GInfSO Q₀) (muArchTamSO Q₀ hQ) := by
  have := countable_GammaSOAdele Q₀
  haveI := fun i => countable_levelGroup (Γ := GammaSOAdele Q₀) (KSOLat Q₀ L) (dcRepLat Q₀ L i)
  haveI := fun i => smulInvariantMeasure_subgroup (levelGroup (GammaSOAdele Q₀) (KSOLat Q₀ L) (dcRepLat Q₀ L i))
    (muArchTamSO Q₀ hQ)
  haveI := fun i => measurableConstSMul_subgroup (levelGroup (GammaSOAdele Q₀) (KSOLat Q₀ L) (dcRepLat Q₀ L i))
  exact covolume_eq_measure_mul_tsum_covolume (GammaSOAdele Q₀) (KSOLat Q₀ L) (isOpen_KSOLat Q₀ L).measurableSet
    (dcRepLat Q₀ L) (dcRepLat_cov Q₀ L)
    (fun i j γ hγ k hk k' hk' h => dcRepLat_disj Q₀ L i j γ hγ k hk k' hk' h)
    (fun i γ hγ h1 => GammaSOAdele_injA Q₀ γ hγ.1 h1)
    (fun i => (exists_fd_levelGroup_of_isCompact Q₀ _ (isCompact_KSOLat Q₀ L) (dcRepLat Q₀ L i)).choose)
    (fun i => (exists_fd_levelGroup_of_isCompact Q₀ _ (isCompact_KSOLat Q₀ L) (dcRepLat Q₀ L i)).choose_spec.1)
    (fun i => (exists_fd_levelGroup_of_isCompact Q₀ _ (isCompact_KSOLat Q₀ L) (dcRepLat Q₀ L i)).choose_spec.2)
    (muArchTamSO Q₀ hQ) (muFin Q₀ fun _ => 1)

end SO

end

end QuadFormsKB.Hanke2011Structure

#print axioms QuadFormsKB.Hanke2011Structure.isOpen_locStab_lat
#print axioms QuadFormsKB.Hanke2011Structure.isCompact_locStab_lat
#print axioms QuadFormsKB.Hanke2011Structure.covolume_eq_muFin_KSOLat_mul_tsum
