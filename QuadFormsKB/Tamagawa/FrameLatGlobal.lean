/-
# The type sum of a lattice $T$ as a product of local type sums

**Layer:** $F$ a number field, an arbitrary integral lattice $L$ in the split space $V = (F^{r+n'}, T\perp Q')$ with $T_0$, $Q_0'$ over
$\mathcal O_F$, and a lattice $T_\ell$ on $(F^r, T_0)$; the local types `LocFrameSetL` (`FrameLatDefs.lean`).

**Proves**
* `locFrameWeightL_smul`: the local weights do not depend on the representative of a type (`modRatio_eq_one`);
* `locFrameTypeSumL_std`: for $T_{\ell,\mathfrak p} = \mathfrak o_\mathfrak p^r$ the local type sum is the
  `locFrameTypeSumG`;
* `locFrameTypeSumL_nonneg`, `hasFiniteMulSupport_locFrameTypeSumL` ($W_\mathfrak p = 1$ at the good primes);
* **`repMassLat_eq_mass_mul_finprod`** (Weil 1982, §3.4–3.5 [unverified locator]):
  $$\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{r(M, T)}{|O(M)|} = \mathrm{Mass}(\mathcal O_F^{n'}, Q')\prod_\mathfrak p W_\mathfrak p(L_\mathfrak p, T_{\ell,\mathfrak p}).$$
  *Proof:* as `typeSumT_eq_finprod_gen`: global types are families of local types at the finite set
  $S = $ `frameBadSetG` $\cup \{\mathfrak p : T_{\ell,\mathfrak p} \ne \mathfrak o_\mathfrak p^r\}$, glued with `LocFamily.glue`; the condition
  $E\,T_\ell \subseteq M$ is checked prime by prime (`mem_iff_forall_loc`).

Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.FrameLatRepMass
import QuadFormsKB.Tamagawa.FrameGlobalGen

open NumberField IsDedekindDomain Matrix MulAction
open scoped RestrictedProduct

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.FramesLat

open QuadFormsKB.Tamagawa Lattices Frames QuadFormsKB.HilbertModular LocalDensity LocalDensity.DVR

section Local

variable {F : Type*} [Field F] [NumberField F] {r n' : ℕ} (v : HeightOneSpectrum (𝓞 F)) (T : QuadForm F r)
  (Q' : QuadForm F n')

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **The weights do not depend on the representative of a type** (`modRatio_eq_one`). -/
theorem locFrameWeightL_smul (hQ' : Q'.Nondegenerate) {Λ : Submodule 𝔬 (Fin (r + n') → Fv)} (hΛ : Λ.IsLattice Fv)
    (Θ : Submodule 𝔬 (Fin r → Fv)) (h : orthGroup Q' Fv) (M : LocFrameSetL v T Q' Λ Θ) :
    locFrameWeightL v T Q' Λ Θ (h • M) = locFrameWeightL v T Q' Λ Θ M := by
  set ψ : orthGroup Q' Fv →* GL (Fin (r + n')) Fv :=
    (orthGroup (blockForm T Q') Fv).subtype.comp (orthEmbB T Q' Fv)
  have hlat : ∀ N : LocFrameSetL v T Q' Λ Θ, N.1.IsLattice Fv := by
    intro N
    obtain ⟨g, hg⟩ := N.2.1
    rw [← hg]; exact locAct_isLattice _ hΛ
  have hK₀ : stdStab Q' v = stabLat v ψ (std v) := by
    ext g; exact (mem_stdStab_orthEmbB_iff T Q' v g).symm
  have hst : ∀ N : LocFrameSetL v T Q' Λ Θ, stabilizer (orthGroup Q' Fv) N = stabLat v ψ N.1 := by
    intro N
    ext g
    rw [mem_stabilizer_iff]
    constructor
    · intro hg; exact congrArg Subtype.val hg
    · intro hg; exact Subtype.ext hg
  have hmod := modRatio_eq_one v Q' hQ' h
  unfold modRatio at hmod
  show relRatio (stdStab Q' v) (stabilizer _ (h • M)) = relRatio (stdStab Q' v) (stabilizer _ M)
  rw [stabilizer_smul_eq_stabilizer_map_conj]
  have hstd : (std v : Submodule 𝔬 (Fin (r + n') → Fv)).IsLattice Fv := std_isLattice v
  have hc1 : Commens (stdStab Q' v) ((stdStab Q' v).map (MulAut.conj h).toMonoidHom) := by
    rw [hK₀, stabLat_map_conj]; exact commens_stabLat v ψ hstd (locAct_isLattice _ hstd)
  have hc2 : Commens ((stdStab Q' v).map (MulAut.conj h).toMonoidHom)
      ((stabilizer (orthGroup Q' Fv) M).map (MulAut.conj h).toMonoidHom) := by
    rw [hK₀, hst M, stabLat_map_conj, stabLat_map_conj]
    exact commens_stabLat v ψ (locAct_isLattice _ hstd) (locAct_isLattice _ (hlat _))
  have hc3 : Commens (stdStab Q' v)
      ((stabilizer (orthGroup Q' Fv) M).map (MulAut.conj h).toMonoidHom) := by
    rw [hK₀, hst M, stabLat_map_conj]; exact commens_stabLat v ψ hstd (locAct_isLattice _ (hlat _))
  rw [← relRatio_mul hc1 hc2 hc3, hmod, one_mul, relRatio_map (MulAut.conj h).injective]

theorem locFrameTypeSumL_nonneg (Λ : Submodule 𝔬 (Fin (r + n') → Fv)) (Θ : Submodule 𝔬 (Fin r → Fv)) :
    0 ≤ locFrameTypeSumL v T Q' Λ Θ := by
  unfold locFrameTypeSumL
  by_cases hfin : (Function.support fun t : LocFrameTypesL v T Q' Λ Θ =>
      locFrameWeightL v T Q' Λ Θ t.out).Finite
  · rw [finsum_eq_sum _ hfin]
    exact Finset.sum_nonneg fun t _ => by unfold locFrameWeightL; positivity
  · rw [finsum_of_infinite_support hfin]

/-- $E\,s = (s, 0)$. -/
theorem stdFrameMat_mulVec_eq_append (s : Fin r → Fv) :
    (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) *ᵥ s = Fin.append s (0 : Fin n' → Fv) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
  · simp [Matrix.mulVec, dotProduct]

/-- For $\Theta = \mathfrak o_\mathfrak p^r$, "$E\Theta \subseteq M$" is "the columns of $E$ lie in $M$". -/
theorem stdFrame_mem_iff_stdCol (Λ' : Submodule 𝔬 (Fin (r + n') → Fv)) :
    (∀ t ∈ (std v : Submodule 𝔬 (Fin r → Fv)), (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) *ᵥ t ∈ Λ') ↔
      ∀ j, stdCol v (n' := n') j ∈ Λ' := by
  constructor
  · intro h j
    have := h (Pi.single j 1) (single_one_mem_std v j)
    convert this using 1
    ext i
    simp [stdCol, Matrix.mulVec, dotProduct, Pi.single_apply]
  · intro h t ht
    have ht' : ∀ i, Valued.v (t i) ≤ 1 := fun i => by
      have := ht i
      rwa [neg_zero, WithZero.exp_zero] at this
    have hsum : (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) *ᵥ t =
        ∑ j, (⟨t j, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (ht' j)⟩ : 𝔬) •
          stdCol v (n' := n') j := by
      ext i
      simp [stdCol, Matrix.mulVec, dotProduct, Finset.sum_apply, Algebra.smul_def, mul_comm]
    rw [hsum]
    exact Submodule.sum_mem _ fun j _ => Λ'.smul_mem _ (h j)

/-- The identification of the local type sets for $\Theta = \mathfrak o_\mathfrak p^r$. -/
def locFrameSetLEquivG (Λ : Submodule 𝔬 (Fin (r + n') → Fv)) :
    LocFrameSetL v T Q' Λ (std v) ≃ LocFrameSetG v T Q' Λ :=
  Equiv.subtypeEquivRight fun M => and_congr_right fun _ => stdFrame_mem_iff_stdCol v M

/-- **For $\Theta = \mathfrak o_\mathfrak p^r$ the local type sum is** `locFrameTypeSumG`. -/
theorem locFrameTypeSumL_std (hQ' : Q'.Nondegenerate) {Λ : Submodule 𝔬 (Fin (r + n') → Fv)} (hΛ : Λ.IsLattice Fv) :
    locFrameTypeSumL v T Q' Λ (std v) = locFrameTypeSumG v T Q' Λ := by
  classical
  set e := locFrameSetLEquivG v T Q' Λ
  have he : ∀ (h : orthGroup Q' Fv) (M : LocFrameSetL v T Q' Λ (std v)), e (h • M) = h • e M :=
    fun h M => rfl
  have hw : ∀ M, locFrameWeightG v T Q' Λ (e M) = locFrameWeightL v T Q' Λ (std v) M := by
    intro M
    have hs : stabilizer (orthGroup Q' Fv) (e M) = stabilizer (orthGroup Q' Fv) M := by
      ext g
      simp only [mem_stabilizer_iff]
      constructor
      · intro h
        have h' : (g • e M).1 = (e M).1 := congrArg Subtype.val h
        exact Subtype.ext h'
      · intro h
        have h' : (g • M).1 = M.1 := congrArg Subtype.val h
        exact Subtype.ext h'
    unfold locFrameWeightG locFrameWeightL
    rw [hs]
  have hinvL := locFrameWeightL_smul v T Q' hQ' hΛ (std v)
  have hinvG : ∀ (h : orthGroup Q' Fv) (y : LocFrameSetG v T Q' Λ),
      locFrameWeightG v T Q' Λ (h • y) = locFrameWeightG v T Q' Λ y := by
    intro h y
    obtain ⟨M, rfl⟩ := e.surjective y
    rw [← he, hw, hw, hinvL]
  have h1 := finsum_orbit_congr e he (locFrameWeightL v T Q' Λ (std v)) (locFrameWeightG v T Q' Λ) hw
    (fun h M => hinvL h M)
  unfold locFrameTypeSumL locFrameTypeSumG
  rw [h1]
  refine finsum_congr fun t => ?_
  have hm : (Quotient.mk'' (locFrameRepG v T Q' Λ t) : LocFrameTypesG v T Q' Λ) = Quotient.mk'' t.out :=
    (locFrameRepG_mk v T Q' Λ t).trans (Quotient.out_eq' t).symm
  obtain ⟨h, hh⟩ := orbitRel_apply.mp (Quotient.exact' hm)
  rw [← hh, hinvG]

end Local

/-! ### Local components of the global type set of a lattice -/

section Components

variable {F : Type} [Field F] [NumberField F] {r n' : ℕ} (T : QuadForm F r) (Q' : QuadForm F n')
  (L : Lat F (r + n')) (Tl : Lat F r)

/-- Localizing the condition: $E\,T_\ell \subseteq M$ gives $E\,T_{\ell,\mathfrak p} \subseteq M_\mathfrak p$. -/
theorem stdFrame_mem_loc (v : HeightOneSpectrum (𝓞 F)) {M : Lat F (r + n')}
    (hM : ∀ t ∈ Tl.1, (stdFrameMat : Matrix (Fin (r + n')) (Fin r) F) *ᵥ t ∈ M.1) :
    ∀ t ∈ loc v Tl.1, (stdFrameMat : Matrix (Fin (r + n')) (Fin r) (v.adicCompletion F)) *ᵥ t ∈ loc v M.1 := by
  intro t ht
  let f : (Fin r → v.adicCompletion F) →ₗ[v.adicCompletionIntegers F] (Fin (r + n') → v.adicCompletion F) :=
    (Matrix.mulVecLin (stdFrameMat : Matrix (Fin (r + n')) (Fin r) (v.adicCompletion F))).restrictScalars
      (v.adicCompletionIntegers F)
  have hmap : (loc v Tl.1).map f = Submodule.span (v.adicCompletionIntegers F) (f '' (locVec v '' (Tl.1 : Set (Fin r → F)))) :=
    Submodule.map_span f _
  have hle : (loc v Tl.1).map f ≤ loc v M.1 := by
    rw [hmap, Submodule.span_le]
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    show (stdFrameMat : Matrix (Fin (r + n')) (Fin r) (v.adicCompletion F)) *ᵥ locVec v x ∈ loc v M.1
    rw [← locVec_stdFrameMat_mulVec]
    exact locVec_mem_loc v (hM x hx)
  exact hle ⟨t, ht, rfl⟩

/-- **The local component** $M_\mathfrak p \in Y_\mathfrak p(L_\mathfrak p, T_{\ell,\mathfrak p})$ of $M \in Y$. -/
def locOfL (v : HeightOneSpectrum (𝓞 F)) (M : CompSetL T Q' L Tl) :
    LocFrameSetL v T Q' (loc v L.1) (loc v Tl.1) :=
  ⟨loc v M.1.1, by
      obtain ⟨g, hg, hgM⟩ := M.2.1 v
      exact ⟨⟨g, hg⟩, hgM⟩,
    stdFrame_mem_loc Tl v M.2.2⟩

theorem locOfL_val (v : HeightOneSpectrum (𝓞 F)) (M : CompSetL T Q' L Tl) :
    (locOfL T Q' L Tl v M).1 = loc v M.1.1 := rfl

theorem locOfL_smul (v : HeightOneSpectrum (𝓞 F)) (h : OAf Q') (M : CompSetL T Q' L Tl) :
    locOfL T Q' L Tl v (h • M) = h v • locOfL T Q' L Tl v M := by
  refine Subtype.ext ?_
  rw [LocFrameSetL.smul_val, locOfL_val, locOfL_val, CompSetL.smul_val]
  exact loc_latSMul (blockForm T Q') (orthEmbBAf T Q' h) M.1 v

/-- **Global orbits are determined prime by prime** (lattice condition). -/
theorem mem_orbit_compSetL_iff (M M' : CompSetL T Q' L Tl) :
    M' ∈ orbit (OAf Q') M ↔
      ∀ v, locOfL T Q' L Tl v M' ∈ orbit (orthGroup Q' (v.adicCompletion F)) (locOfL T Q' L Tl v M) := by
  classical
  constructor
  · rintro ⟨h, rfl⟩ v
    exact ⟨h v, (locOfL_smul T Q' L Tl v h M).symm⟩
  · intro hloc
    choose hv hhv using hloc
    let hp : (v : HeightOneSpectrum (𝓞 F)) → orthGroup Q' (v.adicCompletion F) := fun v =>
      if loc v M.1.1 = loc v M'.1.1 then 1 else hv v
    have hev : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, hp v ∈ stdStab Q' v := by
      filter_upwards [loc_eventually_std M.1.2, loc_eventually_std M'.1.2] with v h1 h2
      have : loc v M.1.1 = loc v M'.1.1 := h1.trans h2.symm
      simp only [hp, this, ↓reduceIte]
      exact (stdStab Q' v).one_mem
    let hA : OAf Q' := ⟨hp, hev⟩
    refine ⟨hA, Subtype.ext (Subtype.ext (loc_injective (hA • M).1.2 M'.1.2 fun v => ?_))⟩
    have e := locOfL_smul T Q' L Tl v hA M
    have e2 : loc v (hA • M).1.1 = (locOfL T Q' L Tl v (hA • M)).1 := rfl
    rw [e2, e]
    show (hp v • locOfL T Q' L Tl v M).1 = _
    simp only [hp]
    split_ifs with heq
    · rw [one_smul]; exact heq
    · have := congrArg Subtype.val (hhv v)
      exact this

end Components

/-! ### Weights of the global types -/

section Weights

variable {F : Type} [Field F] [NumberField F] {r n' : ℕ} (T : QuadForm F r) (Q' : QuadForm F n')
  (L : Lat F (r + n')) (Tl : Lat F r)

/-- **The weight of a lattice** $M \in Y$: `typeWeightL t` is `compWeightL t.out`. -/
def compWeightL (y : CompSetL T Q' L Tl) : ℝ :=
  ((stabilizer (OAf Q') y).relIndex (locStab Q' (stdLat F n')) : ℝ) /
    ((locStab Q' (stdLat F n')).relIndex (stabilizer (OAf Q') y) : ℝ)

theorem typeWeightL_eq_compWeightL (t : orbitRel.Quotient (OAf Q') (CompSetL T Q' L Tl)) :
    typeWeightL T Q' L Tl t = compWeightL T Q' L Tl t.out := rfl

theorem dcMass_compSetL_eq (hpd' : IsTotallyPosDef Q') (hLi' : IsIntegral Q' (stdLat F n').1)
    (y : CompSetL T Q' L Tl) :
    dcMass (ratPoints Q') (stabilizer (OAf Q') y) = mass Q' (stdLat F n') * compWeightL T Q' L Tl y := by
  have hK := commensurable_stabilizer_compSetL T Q' L Tl y
  have := finite_orbits hpd' (stdLat F n') hLi'
  have h := dcMass_mul_idxVol (ratPoints Q') (locStab Q' (stdLat F n')) (stabilizer (OAf Q') y) 1 hK
    (finite_stabilizer hpd' (stdLat F n') hLi')
  rw [one_mul, ← mass_eq_dcMass] at h
  have h1 : ((stabilizer (OAf Q') y).relIndex (locStab Q' (stdLat F n')) : ℝ) ≠ 0 := by
    exact_mod_cast hK.1.relIndex_ne_zero
  have h2 : ((locStab Q' (stdLat F n')).relIndex (stabilizer (OAf Q') y) : ℝ) ≠ 0 := by
    exact_mod_cast hK.2.relIndex_ne_zero
  unfold idxVol at h
  unfold compWeightL
  rw [← h]
  field_simp

theorem compWeightL_smul (hpd' : IsTotallyPosDef Q') (hLi' : IsIntegral Q' (stdLat F n').1) (h : OAf Q')
    (y : CompSetL T Q' L Tl) : compWeightL T Q' L Tl (h • y) = compWeightL T Q' L Tl y := by
  have h1 := dcMass_compSetL_eq T Q' L Tl hpd' hLi' (h • y)
  rw [stabilizer_smul_eq_stabilizer_map_conj, dcMass_map_conj, dcMass_compSetL_eq T Q' L Tl hpd' hLi' y] at h1
  exact (mul_left_cancel₀ (mass_pos hpd' (stdLat F n') hLi').ne' h1).symm

theorem compWeightL_of_mem_orbit (hpd' : IsTotallyPosDef Q') (hLi' : IsIntegral Q' (stdLat F n').1)
    {y y' : CompSetL T Q' L Tl} (h : y' ∈ orbit (OAf Q') y) :
    compWeightL T Q' L Tl y' = compWeightL T Q' L Tl y := by
  obtain ⟨h, rfl⟩ := h
  exact compWeightL_smul T Q' L Tl hpd' hLi' h y

end Weights

section Global

variable {F : Type} [Field F] [NumberField F] {r n' : ℕ}

/-! #### The exceptional primes and the gluing -/

section Glue

variable (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate) (Q₀' : QuadForm (𝓞 F) n') (hQ' : Q₀'.Nondegenerate)
  (L : Lat F (r + n')) (Tl : Lat F r)

local notation "TF" => T₀.map (algebraMap (𝓞 F) F)
local notation "QF'" => Q₀'.map (algebraMap (𝓞 F) F)

theorem finite_loc_ne_std_lat : {v : HeightOneSpectrum (𝓞 F) | loc v Tl.1 ≠ std v}.Finite :=
  Filter.eventually_cofinite.mp (loc_eventually_std Tl.2)

open Classical in
/-- **The exceptional primes** of $(L, T_\ell, T_0)$: those of `frameBadSetG` and those with $T_{\ell,\mathfrak p} \ne \mathfrak o_\mathfrak p^r$. -/
def frameBadSetL : Finset (HeightOneSpectrum (𝓞 F)) :=
  frameBadSetG T₀ hT L ∪ (finite_loc_ne_std_lat Tl).toFinset

theorem not_mem_frameBadSetL {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ frameBadSetL T₀ hT L Tl) :
    v ∉ frameBadSet T₀ hT ∧ loc v L.1 = std v ∧ loc v Tl.1 = std v := by
  classical
  simp only [frameBadSetL, Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_or, not_not] at hv
  obtain ⟨h1, h2⟩ := hv
  obtain ⟨h3, h4⟩ := not_mem_frameBadSetG T₀ hT L h1
  exact ⟨h3, h4, h2⟩

local notation "S" => frameBadSetL T₀ hT L Tl

include hQ' in
/-- At a prime outside $S$ the local type set has one orbit. -/
theorem exists_smul_of_not_memL {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S)
    (M M' : LocFrameSetL v TF QF' (loc v L.1) (loc v Tl.1)) :
    M' ∈ orbit (orthGroup QF' (v.adicCompletion F)) M := by
  obtain ⟨hv0, hL, hTl⟩ := not_mem_frameBadSetL T₀ hT L Tl hv
  have key : ∀ N : LocFrameSetL v TF QF' (loc v L.1) (loc v Tl.1), ∃ h : orthGroup QF' (v.adicCompletion F),
      (h • locFrameStdPt v TF QF').1 = N.1 := by
    intro N
    have hN : ∀ j, stdCol v (n' := n') j ∈ N.1 :=
      (stdFrame_mem_iff_stdCol v N.1).mp fun t ht => N.2.2 t (by rw [hTl]; exact ht)
    obtain ⟨h, hh⟩ := exists_smul_locFrameStdPt T₀ hT Q₀' hQ' hv0 ⟨N.1, by rw [← hL]; exact N.2.1, hN⟩
    exact ⟨h, congrArg Subtype.val hh⟩
  obtain ⟨h, hh⟩ := key M
  obtain ⟨h', hh'⟩ := key M'
  refine ⟨h' * h⁻¹, Subtype.ext ?_⟩
  show locAct v (orthEmbB TF QF' _ (h' * h⁻¹) : GL (Fin (r + n')) (v.adicCompletion F)) M.1 = M'.1
  rw [← hh, ← hh', LocFrameSet.smul_val, LocFrameSet.smul_val, ← locAct_mul, ← Subgroup.coe_mul, ← map_mul,
    inv_mul_cancel_right]

/-- **Global types to local types at the primes of $S$.** -/
def typeMapTL : orbitRel.Quotient (OAf QF') (CompSetL TF QF' L Tl) →
    ((v : S) → LocFrameTypesL v TF QF' (loc v L.1) (loc v Tl.1)) :=
  Quotient.lift (fun M v => Quotient.mk'' (locOfL TF QF' L Tl v M)) (fun a b hab => funext fun v => by
    exact Quotient.sound' ((mem_orbit_compSetL_iff TF QF' L Tl b a).mp hab v))

theorem typeMapTL_mk (M : CompSetL TF QF' L Tl) (v : S) :
    typeMapTL T₀ hT Q₀' L Tl (Quotient.mk'' M) v = Quotient.mk'' (locOfL TF QF' L Tl v M) := rfl

include hQ' in
theorem typeMapTL_injective : Function.Injective (typeMapTL T₀ hT Q₀' L Tl) := by
  intro t t' h
  induction t using Quotient.inductionOn' with | h M => ?_
  induction t' using Quotient.inductionOn' with | h M' => ?_
  apply Quotient.sound'
  show M ∈ orbit (OAf QF') M'
  rw [mem_orbit_compSetL_iff]
  intro v
  by_cases hv : v ∈ S
  · have := congrFun h ⟨v, hv⟩
    rw [typeMapTL_mk, typeMapTL_mk] at this
    exact Quotient.exact' this
  · exact exists_smul_of_not_memL T₀ hT Q₀' hQ' L Tl hv _ _

open Classical in
/-- The local family glued from representatives of local types at the primes of $S$ (and $L_\mathfrak p$ elsewhere). -/
def glueFamTL (f : (v : S) → LocFrameTypesL v TF QF' (loc v L.1) (loc v Tl.1)) : LocFamily F (r + n') where
  M v := if hv : v ∈ S then (f ⟨v, hv⟩).out.1 else loc v L.1
  isLattice v := by
    split_ifs with hv
    · obtain ⟨g, hg⟩ := (f ⟨v, hv⟩).out.2.1
      rw [← hg]
      exact locAct_isLattice _ (loc_isLattice v L.2)
    · exact loc_isLattice v L.2
  eventually_std := by
    filter_upwards [(S).finite_toSet.compl_mem_cofinite] with v hv
    have hv' : v ∉ S := hv
    simp only [hv', ↓reduceDIte]
    exact (not_mem_frameBadSetL T₀ hT L Tl hv').2.1

/-- At a prime outside $S$, $E\,\mathfrak o_\mathfrak p^r \subseteq \mathfrak o_\mathfrak p^{r+n'}$. -/
theorem stdFrame_mem_std (v : HeightOneSpectrum (𝓞 F)) (t : Fin r → v.adicCompletion F) (ht : t ∈ std v) :
    (stdFrameMat : Matrix (Fin (r + n')) (Fin r) (v.adicCompletion F)) *ᵥ t ∈ (std v : Submodule _ (Fin (r + n') → _)) := by
  rw [stdFrameMat_mulVec_eq_append]
  exact (mem_std_append v).mpr ⟨ht, Submodule.zero_mem _⟩

open Classical in
/-- **The glued lattice** with prescribed local types. -/
def glueCompTL (f : (v : S) → LocFrameTypesL v TF QF' (loc v L.1) (loc v Tl.1)) : CompSetL TF QF' L Tl :=
  ⟨⟨(glueFamTL T₀ hT Q₀' L Tl f).glue, (glueFamTL T₀ hT Q₀' L Tl f).glue_isLattice⟩, by
      intro v
      rw [LocFamily.loc_glue]
      show ∃ g ∈ _, _ = if hv : v ∈ S then _ else _
      split_ifs with hv
      · obtain ⟨g, hg⟩ := (f ⟨v, hv⟩).out.2.1
        exact ⟨g, g.2, hg⟩
      · exact ⟨1, (orthGroup _ _).one_mem, locAct_one _⟩,
    fun t ht => by
      rw [mem_iff_forall_loc (glueFamTL T₀ hT Q₀' L Tl f).glue_isLattice]
      intro v
      rw [LocFamily.loc_glue, locVec_stdFrameMat_mulVec]
      show _ ∈ if hv : v ∈ S then _ else _
      split_ifs with hv
      · exact (f ⟨v, hv⟩).out.2.2 _ (locVec_mem_loc v ht)
      · obtain ⟨-, hL, hTl⟩ := not_mem_frameBadSetL T₀ hT L Tl hv
        rw [hL]
        have : locVec v t ∈ std v := by rw [← hTl]; exact locVec_mem_loc v ht
        exact stdFrame_mem_std v _ this⟩

theorem locOfL_glueCompTL (f : (v : S) → LocFrameTypesL v TF QF' (loc v L.1) (loc v Tl.1)) (v : S) :
    locOfL TF QF' L Tl v (glueCompTL T₀ hT Q₀' L Tl f) = (f v).out := by
  classical
  apply Subtype.ext
  rw [locOfL_val]
  show loc (v : HeightOneSpectrum (𝓞 F)) (glueFamTL T₀ hT Q₀' L Tl f).glue = _
  rw [LocFamily.loc_glue]
  show (if hv : (v : HeightOneSpectrum (𝓞 F)) ∈ S then _ else _) = _
  simp only [v.2, ↓reduceDIte]

theorem locOfL_glueCompTL_of_not_mem (f : (v : S) → LocFrameTypesL v TF QF' (loc v L.1) (loc v Tl.1))
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) :
    (locOfL TF QF' L Tl v (glueCompTL T₀ hT Q₀' L Tl f)).1 = std v := by
  classical
  rw [locOfL_val]
  show loc v (glueFamTL T₀ hT Q₀' L Tl f).glue = _
  rw [LocFamily.loc_glue]
  show (if hv : v ∈ S then _ else _) = _
  simp only [hv, ↓reduceDIte]
  exact (not_mem_frameBadSetL T₀ hT L Tl hv).2.1

theorem typeMapTL_glueCompTL (f : (v : S) → LocFrameTypesL v TF QF' (loc v L.1) (loc v Tl.1)) :
    typeMapTL T₀ hT Q₀' L Tl (Quotient.mk'' (glueCompTL T₀ hT Q₀' L Tl f)) = f := by
  funext v
  rw [typeMapTL_mk, locOfL_glueCompTL]
  exact Quotient.out_eq' (f v)

include hQ' in
/-- **Global types = families of local types at the primes of $S$.** -/
def typeEquivTL : orbitRel.Quotient (OAf QF') (CompSetL TF QF' L Tl) ≃
    ((v : S) → LocFrameTypesL v TF QF' (loc v L.1) (loc v Tl.1)) :=
  Equiv.ofBijective _ ⟨typeMapTL_injective T₀ hT Q₀' hQ' L Tl,
    fun f => ⟨_, typeMapTL_glueCompTL T₀ hT Q₀' L Tl f⟩⟩

/-- **The global weight of a glued lattice is the product of the local weights.** -/
theorem compWeightL_glueCompTL (f : (v : S) → LocFrameTypesL v TF QF' (loc v L.1) (loc v Tl.1)) :
    compWeightL TF QF' L Tl (glueCompTL T₀ hT Q₀' L Tl f) =
      ∏ v : S, locFrameWeightL v TF QF' (loc v L.1) (loc v Tl.1) (f v).out := by
  classical
  set y := glueCompTL T₀ hT Q₀' L Tl f
  set A' : (v : HeightOneSpectrum (𝓞 F)) → Subgroup (orthGroup QF' (v.adicCompletion F)) :=
    fun v => stabilizer (orthGroup QF' (v.adicCompletion F)) (locOfL TF QF' L Tl v y)
  have hA : ∀ v ∉ S, A' v = stdStab QF' v := by
    intro v hv
    simp only [A']
    ext h
    rw [mem_stabilizer_iff, ← mem_stdStab_orthEmbB_iff TF QF' v h]
    have e := locOfL_glueCompTL_of_not_mem T₀ hT Q₀' L Tl f hv
    constructor
    · intro hh
      have := congrArg Subtype.val hh
      rw [LocFrameSetL.smul_val, e] at this
      exact this
    · intro hh
      apply Subtype.ext
      rw [LocFrameSetL.smul_val, e]
      exact hh
  have hB : ∀ v ∉ S, stdStab QF' v = stdStab QF' v := fun _ _ => rfl
  have hAm : ∀ h, h ∈ stabilizer (OAf QF') y ↔ ∀ v, h v ∈ A' v := by
    intro h
    rw [stabilizer_compSetL, Subgroup.mem_comap]
    show (∀ v, _ = _) ↔ _
    refine forall_congr' fun v => ?_
    simp only [A', mem_stabilizer_iff]
    constructor
    · intro hh; exact Subtype.ext hh
    · intro hh; exact congrArg Subtype.val hh
  have hBm : ∀ h, h ∈ locStab QF' (stdLat F n') ↔ ∀ v, h v ∈ stdStab QF' v := mem_locStab_intVec QF'
  have e1 := relIndex_restrictedPi S A' (fun v => stdStab QF' v) hA hB _ _ hAm hBm
  have e2 := relIndex_restrictedPi S (fun v => stdStab QF' v) A' hB hA _ _ hBm hAm
  unfold compWeightL
  rw [e1, e2, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib, ← Finset.prod_coe_sort S]
  refine Finset.prod_congr rfl fun v _ => ?_
  simp only [A', locFrameWeightL]
  rw [locOfL_glueCompTL]

end Glue

/-- `IsTotallyPosDef` of an orthogonal sum gives it for the first summand (no total-reality assumption on $F$). -/
theorem isTotallyPosDef_of_blockForm_left' {T : QuadForm F r} {Q' : QuadForm F n'}
    (h : IsTotallyPosDef (blockForm T Q')) : IsTotallyPosDef T := by
  intro x hx
  have h1 : (Fin.append x (0 : Fin n' → F) : Fin (r + n') → F) ≠ 0 := by
    intro h0; apply hx; funext i
    simpa using congrFun h0 (Fin.castAdd n' i)
  have := h _ h1
  rw [QuadForm.eval, evalIn_blockForm] at this
  simpa [Fin.append, QuadForm.evalIn] using this

/-- **The local factor is $1$ outside $S$.** -/
theorem locFrameTypeSumL_eq_one_of_not_mem (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate)
    (Q₀' : QuadForm (𝓞 F) n') (hQ' : Q₀'.Nondegenerate) (L : Lat F (r + n')) (Tl : Lat F r)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ frameBadSetL T₀ hT L Tl) :
    locFrameTypeSumL v (formF T₀) (formF Q₀') (loc v L.1) (loc v Tl.1) = 1 := by
  obtain ⟨hv0, hL, hTl⟩ := not_mem_frameBadSetL T₀ hT L Tl hv
  rw [hTl, locFrameTypeSumL_std v _ _ ((nondeg_map_alg Q₀').mp hQ') (loc_isLattice v L.2)]
  exact locFrameTypeSumG_eq_one_of_good T₀ hT Q₀' hQ' L hL hv0

/-- **The local factors are $1$ at almost every prime.** -/
theorem hasFiniteMulSupport_locFrameTypeSumL (T₀ : QuadForm (𝓞 F) r) (Q₀' : QuadForm (𝓞 F) n') (L : Lat F (r + n'))
    (Tl : Lat F r) (hpd : IsTotallyPosDef (blockForm (formF T₀) (formF Q₀'))) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      locFrameTypeSumL v (formF T₀) (formF Q₀') (loc v L.1) (loc v Tl.1) := by
  classical
  have hT : T₀.Nondegenerate := (nondeg_map_alg T₀).mpr (isTotallyPosDef_of_blockForm_left' hpd).nondegenerate
  have hQ' : Q₀'.Nondegenerate := (nondeg_map_alg Q₀').mpr (isTotallyPosDef_of_blockForm_right hpd).nondegenerate
  refine (frameBadSetL T₀ hT L Tl).finite_toSet.subset ?_
  intro v hv
  by_contra hvS
  exact hv (locFrameTypeSumL_eq_one_of_not_mem T₀ hT Q₀' hQ' L Tl hvS)

/-- **Weil's orbit counting for embeddings of a lattice $T$, factored over the primes** (Weil 1982, §3.4–3.5 [unverified locator]):
for $T_0\perp Q_0'$ totally positive definite and $L$ integral for it,
$$\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{r(M, T)}{|O(M)|} = \mathrm{Mass}(\mathcal O_F^{n'}, Q')\prod_\mathfrak p W_\mathfrak p(L_\mathfrak p, T_{\ell,\mathfrak p}).$$ -/
@[kb "weil1982" "§3.4-3.5 (orbit counting, lattices) [unverified locator]"]
theorem repMassLat_eq_mass_mul_finprod (T₀ : QuadForm (𝓞 F) r) (Q₀' : QuadForm (𝓞 F) n') (L : Lat F (r + n'))
    (Tl : Lat F r) (hpd : IsTotallyPosDef (blockForm (formF T₀) (formF Q₀')))
    (hLi : IsIntegral (blockForm (formF T₀) (formF Q₀')) L.1) :
    repMassLat (blockForm (formF T₀) (formF Q₀')) L Tl (formF T₀) =
      mass (formF Q₀') (stdLat F n') *
        ∏ᶠ v : HeightOneSpectrum (𝓞 F), locFrameTypeSumL v (formF T₀) (formF Q₀') (loc v L.1) (loc v Tl.1) := by
  classical
  have hpdT := isTotallyPosDef_of_blockForm_left' hpd
  have hpd' := isTotallyPosDef_of_blockForm_right hpd
  have hT : T₀.Nondegenerate := (nondeg_map_alg T₀).mpr hpdT.nondegenerate
  have hQ' : Q₀'.Nondegenerate := (nondeg_map_alg Q₀').mpr hpd'.nondegenerate
  have hLi' : IsIntegral (Q₀'.map (algebraMap (𝓞 F) F)) (stdLat F n').1 := isIntegral_stdLat_map _
  rw [repMassLat_eq_mass_mul (formF T₀) (formF Q₀') L Tl hpd hLi hpdT.nondegenerate hpd' hLi']
  congr 1
  have hfin := finite_typesL (formF T₀) (formF Q₀') L Tl hpd hLi hpdT.nondegenerate
  -- the finprod is a product over S
  have hsub : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      locFrameTypeSumL v (formF T₀) (formF Q₀') (loc v L.1) (loc v Tl.1)) ⊆ ↑(frameBadSetL T₀ hT L Tl) :=
    fun v hv => by
      by_contra hvS
      exact hv (locFrameTypeSumL_eq_one_of_not_mem T₀ hT Q₀' hQ' L Tl hvS)
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  by_cases hall : ∀ w : frameBadSetL T₀ hT L Tl, Nonempty (LocFrameTypesL w (formF T₀) (formF Q₀')
      (loc w L.1) (loc w Tl.1))
  swap
  · push_neg at hall
    obtain ⟨w₀, hw₀⟩ := hall
    have hR : ∏ v ∈ frameBadSetL T₀ hT L Tl, locFrameTypeSumL v (formF T₀) (formF Q₀')
        (loc v L.1) (loc v Tl.1) = 0 := by
      refine Finset.prod_eq_zero w₀.2 ?_
      rw [locFrameTypeSumL, finsum_of_isEmpty]
    have hE : IsEmpty (orbitRel.Quotient (OAf (formF Q₀')) (CompSetL (formF T₀) (formF Q₀') L Tl)) :=
      ⟨fun t => hw₀.false (typeMapTL T₀ hT Q₀' L Tl t w₀)⟩
    rw [hR, finsum_of_isEmpty]
  have hfinP : Finite ((v : frameBadSetL T₀ hT L Tl) → LocFrameTypesL v (formF T₀) (formF Q₀')
      (loc v L.1) (loc v Tl.1)) := Finite.of_equiv _ (typeEquivTL T₀ hT Q₀' hQ' L Tl)
  have hfinv : ∀ v : frameBadSetL T₀ hT L Tl, Finite (LocFrameTypesL v (formF T₀) (formF Q₀')
      (loc v L.1) (loc v Tl.1)) := by
    intro v
    let f₀ : (w : frameBadSetL T₀ hT L Tl) → LocFrameTypesL w (formF T₀) (formF Q₀')
      (loc w L.1) (loc w Tl.1) := fun w => Classical.choice (hall w)
    exact Finite.of_injective (fun x => Function.update f₀ v x) (Function.update_injective f₀ v)
  let _ : Fintype (orbitRel.Quotient (OAf (formF Q₀')) (CompSetL (formF T₀) (formF Q₀') L Tl)) :=
    Fintype.ofFinite _
  let _ : ∀ v : frameBadSetL T₀ hT L Tl, Fintype (LocFrameTypesL v (formF T₀) (formF Q₀')
    (loc v L.1) (loc v Tl.1)) := fun v => Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  have step : ∀ t, typeWeightL (formF T₀) (formF Q₀') L Tl t =
      compWeightL (formF T₀) (formF Q₀') L Tl (glueCompTL T₀ hT Q₀' L Tl (typeEquivTL T₀ hT Q₀' hQ' L Tl t)) := by
    intro t
    rw [typeWeightL_eq_compWeightL]
    refine compWeightL_of_mem_orbit _ _ _ _ hpd' hLi' ?_
    have h1 : (Quotient.mk'' (glueCompTL T₀ hT Q₀' L Tl (typeEquivTL T₀ hT Q₀' hQ' L Tl t)) :
        orbitRel.Quotient (OAf (formF Q₀')) (CompSetL (formF T₀) (formF Q₀') L Tl)) = t :=
      typeMapTL_injective T₀ hT Q₀' hQ' L Tl (typeMapTL_glueCompTL T₀ hT Q₀' L Tl _)
    have h2 : (Quotient.mk'' t.out : orbitRel.Quotient (OAf (formF Q₀')) (CompSetL (formF T₀) (formF Q₀') L Tl)) =
        Quotient.mk'' (glueCompTL T₀ hT Q₀' L Tl (typeEquivTL T₀ hT Q₀' hQ' L Tl t)) := by
      rw [h1, Quotient.out_eq']
    exact Quotient.exact' h2
  rw [Finset.sum_congr rfl fun t _ => step t,
    Equiv.sum_comp (typeEquivTL T₀ hT Q₀' hQ' L Tl) (fun f => compWeightL (formF T₀) (formF Q₀') L Tl
      (glueCompTL T₀ hT Q₀' L Tl f))]
  simp_rw [compWeightL_glueCompTL]
  rw [← Finset.prod_coe_sort (frameBadSetL T₀ hT L Tl)]
  simp_rw [locFrameTypeSumL, finsum_eq_sum_of_fintype]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

end Global

end QuadFormsKB.Tamagawa.FramesLat
