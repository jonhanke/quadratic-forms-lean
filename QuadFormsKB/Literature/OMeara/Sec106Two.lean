/-
# O'Meara §106B: Proposition 106:2, proved

**Layer:** $F = \mathbb Q$, $V = \mathbb Q^n$ with $Q = x_0^2 + \dots + x_{n-1}^2$ (`sumSqForm n`, O'Meara's $I_n$), lattices
`Lat ℚ n`, unimodular lattices `IsUnimodularZ`, the set $\mathcal G(L)$ = `omearaG`. The adelic argument
(`exists_rotation_agree_away`) is stated for a general number field $F$ with $\mathcal O_F$ a PID and one exceptional
finite place.

**Proves**
* `omeara106_2_holds` (**Proposition 106:2**, O'Meara 1973, p. 325): for $n \ge 5$ and unimodular lattices $K, L$ on $I_n$
  there is $J$ with $J = \sigma K$ for a rotation $\sigma \in O^+(V)$ (`IsProperIsometric`) and $J \in \mathcal G(L)$, i.e.
  $J_p = L_p$ for every odd prime $p$. The statement is exactly the field `holds` of the named statement `OMeara106_2`
  (`Sec106Class.lean`, not imported here), so that `⟨omeara106_2_holds⟩ : OMeara106_2`. **Unconditional.**
* `exists_rotation_agree_away`: for a nondegenerate $Q$ in $n \ge 3$ variables isotropic at a finite place $v_0$, lattices
  $K, L$ with local isometries $K_v \to L_v$ at all $v \ne v_0$, `LocalSpinorUnits Q v K` at all $v \ne v_0$, and global
  rotations of every spinor norm $\pm a_0$ ($a_0 \in \mathcal O_F \setminus 0$): there is $\rho \in O^+(V)$ with
  $(\rho K)_v = L_v$ for all $v \ne v_0$.
* `exists_locAct_of_unimodular`, `localSpinorUnits_of_free`: the local inputs at a non-dyadic place for free integral
  lattices with Gram determinant prime to $v$ (O'Meara 92:2, 92:5).

**Deviation from the book's proof.** O'Meara applies Theorem 104:10 over $\mathbb Z' = \mathbb Z[\tfrac12]$ (class = genus
for modular lattices of the same norm). Here the library's strong approximation away from one prime
(`strongApproximationSpinAt`, `Lattices/SATernaryAway.lean`, with $v_0 = 2$ and $V_2$ isotropic since $n \ge 5$) is used
instead, together with the spinor norms of the rotation $\rho = \tau_x\tau_{e_0}$ ($Q(x) = |a|$ by Lagrange's four-squares
theorem, $n \ge 4$) that corrects the local spinor norms of the isometries $K_p \to L_p$.
-/
import QuadFormsKB.Lattices.SpinorGlobal
import QuadFormsKB.Lattices.SATernaryAway
import QuadFormsKB.Literature.OMeara.Sec102
import QuadFormsKB.Literature.OMeara.Sec106Defs
import QuadFormsKB.Literature.OMeara.Sec106E
import QuadFormsKB.HilbertModular.HeckeGenusLocal

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

/-! ### The adelic argument (a general number field, one exceptional place) -/

section Key

variable {F : Type} [Field F] [NumberField F] [IsPrincipalIdealRing (𝓞 F)] {n : ℕ} (Q : QuadForm F n)

theorem exists_rotation_agree_away (hSA : StrongApproximationSpinAt F) (hQ : Q.Nondegenerate) (hn : 3 ≤ n)
    {v₀ : HeightOneSpectrum (𝓞 F)} (hiso : Q.IsotropicIn (v₀.adicCompletion F)) (K L : Lat F n)
    (hI1 : ∀ v, v ≠ v₀ → ∃ σ : orthGroup Q (v.adicCompletion F),
      locAct v (σ : GL (Fin n) (v.adicCompletion F)) (loc v K.1) = loc v L.1)
    (hI2 : ∀ v, v ≠ v₀ → LocalSpinorUnits Q v K)
    (hρ : ∀ a₀ : 𝓞 F, a₀ ≠ 0 → ∃ x y : Fin n → F, Q.evalIn F y ≠ 0 ∧ ∃ u : F,
      (∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) u) = 1) ∧
      Q.evalIn F x = u * algebraMap (𝓞 F) F a₀ * Q.evalIn F y) :
    ∃ ρ : orthGroup Q F, ρ ∈ Tamagawa.soSub Q F ∧ ∀ v, v ≠ v₀ →
      loc v (glImage (ρ : GL (Fin n) F) K.1) = loc v L.1 := by
  classical
  -- local isometries `σ v`
  let σ : ∀ v : HeightOneSpectrum (𝓞 F), orthGroup Q (v.adicCompletion F) := fun v =>
    if h : v ≠ v₀ ∧ loc v K.1 ≠ loc v L.1 then (hI1 v h.1).choose else 1
  have hσ1 : ∀ v, loc v K.1 = loc v L.1 → σ v = 1 := by
    intro v h
    simp [σ, h]
  have hσ : ∀ v, v ≠ v₀ → locAct v (σ v : GL (Fin n) (v.adicCompletion F)) (loc v K.1) = loc v L.1 := by
    intro v hv
    by_cases h : loc v K.1 = loc v L.1
    · rw [hσ1 v h, Subgroup.coe_one, locAct_one]; exact h
    · have : σ v = (hI1 v hv).choose := by simp [σ, hv, h]
      rw [this]; exact (hI1 v hv).choose_spec
  -- spinor norms of the `σ v`
  have hx : ∀ v : HeightOneSpectrum (𝓞 F), ∃ x : v.adicCompletion F, x ≠ 0 ∧
      spinorNorm Q (v.adicCompletion F) (σ v) = sqClassOf x := by
    intro v
    obtain ⟨xs, hxs, hxe⟩ := exists_symmProd_eq Q (v.adicCompletion F) hQ (σ v)
    exact ⟨_, valProd_ne_zero Q _ hxs, by rw [← hxe, spinorNorm_symmProd Q _ hQ xs hxs]⟩
  choose xv hxv0 hxvθ using hx
  let m : HeightOneSpectrum (𝓞 F) → ℤ := fun v => log (Valued.v (xv v))
  let ε : HeightOneSpectrum (𝓞 F) → ℕ := fun v => (m v % 2).toNat
  have hm : ∀ v, Valued.v (xv v) = exp (m v) := fun v =>
    (exp_log ((map_ne_zero _).mpr (hxv0 v))).symm
  have hε : ∀ v, ((ε v : ℕ) : ℤ) = m v % 2 := fun v => Int.toNat_of_nonneg (Int.emod_nonneg _ two_ne_zero)
  -- the finite set where `K_v ≠ L_v`
  have hfin : {v | loc v K.1 ≠ loc v L.1}.Finite := by
    refine ((Filter.eventually_cofinite.mp (loc_eventually_std K.2)).union
      (Filter.eventually_cofinite.mp (loc_eventually_std L.2))).subset ?_
    intro v hv
    by_contra hc
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hc
    exact hv (hc.1.trans hc.2.symm)
  set S := hfin.toFinset
  set a₀ : 𝓞 F := ∏ w ∈ S, primeGen w ^ ε w
  set a : F := algebraMap (𝓞 F) F a₀
  have ha0 : a₀ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ => pow_ne_zero _ (primeGen_ne_zero w)
  obtain ⟨x, y, hy, u, hu, hxy⟩ := hρ a₀ ha0
  have hu0 : u ≠ 0 := by
    intro h
    have := hu v₀
    rw [h, map_zero, map_zero] at this
    exact zero_ne_one this
  have ha : a ≠ 0 := (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mpr ha0
  have hx0 : Q.evalIn F x ≠ 0 := by rw [hxy]; exact mul_ne_zero (mul_ne_zero hu0 ha) hy
  have hva : ∀ v ∈ S, Valued.v (algebraMap F (v.adicCompletion F) (u * a)) = exp (-(ε v : ℤ)) := by
    intro v hv
    rw [map_mul, map_mul, hu v, one_mul, ← IsScalarTower.algebraMap_apply]
    exact valued_prod_primeGen_of_mem v ε hv
  have hva' : ∀ v ∉ S, Valued.v (algebraMap F (v.adicCompletion F) (u * a)) = 1 := by
    intro v hv
    rw [map_mul, map_mul, hu v, one_mul, ← IsScalarTower.algebraMap_apply]
    exact valued_prod_primeGen_of_not_mem v ε hv
  set ρ : orthGroup Q F := symm Q F x * symm Q F y with hρdef
  have hθρ : ∀ v : HeightOneSpectrum (𝓞 F), spinorNorm Q (v.adicCompletion F) (orthMap Q _ ρ) =
      sqClassOf (algebraMap F (v.adicCompletion F) (u * a)) := by
    intro v
    rw [spinorNorm_orthMap_symm_mul Q hQ v hx0 hy]
    have hyv : algebraMap F (v.adicCompletion F) (Q.evalIn F y) ≠ 0 := (map_ne_zero _).mpr hy
    have hav : algebraMap F (v.adicCompletion F) (u * a) ≠ 0 := (map_ne_zero _).mpr (mul_ne_zero hu0 ha)
    have e2 : algebraMap F (v.adicCompletion F) (Q.evalIn F x * Q.evalIn F y) =
        algebraMap F (v.adicCompletion F) (u * a) * (algebraMap F (v.adicCompletion F) (Q.evalIn F y) *
          algebraMap F (v.adicCompletion F) (Q.evalIn F y)) := by
      rw [show Q.evalIn F x = u * a * Q.evalIn F y from hxy, ← map_mul, ← map_mul]
      congr 1
      ring
    rw [e2, sqClassOf_mul hav (mul_ne_zero hyv hyv),
      (sqClassOf_eq_one_iff (mul_ne_zero hyv hyv)).mpr ⟨_, rfl⟩, mul_one]
  -- the local elements `k_v`
  have hdec : ∀ v : HeightOneSpectrum (𝓞 F), ∃ k : orthGroup Q (v.adicCompletion F),
      k ∈ spinorKernel Q (v.adicCompletion F) ∧
      (v ≠ v₀ → k⁻¹ * ((orthMap Q _ ρ)⁻¹ * σ v) ∈ locStabV Q v K) := by
    intro v
    by_cases hv : v = v₀
    · exact ⟨1, (spinorKernel Q _).one_mem, fun h => absurd hv h⟩
    · set Kv := v.adicCompletion F
      have hav : algebraMap F Kv (u * a) ≠ 0 := (map_ne_zero _).mpr (mul_ne_zero hu0 ha)
      by_cases hvS : v ∈ S
      · obtain ⟨k, hk, hg⟩ := hI2 v hv ((orthMap Q Kv ρ)⁻¹ * σ v) (by
          rw [← spinorNormHom_apply Q Kv hQ, map_mul, map_inv, spinorNormHom_apply, spinorNormHom_apply,
            hθρ, SqClass.inv_eq, hxvθ, ← sqClassOf_mul hav (hxv0 v)]
          refine isUnitSqClass_of_valued_eq v _ (m v / 2) ?_
          rw [map_mul, hva v hvS, hm, ← exp_add, hε]
          congr 1
          omega)
        exact ⟨k, hk, fun _ => hg⟩
      · have hKL : loc v K.1 = loc v L.1 := by
          by_contra hc; exact hvS (hfin.mem_toFinset.mpr hc)
        obtain ⟨k, hk, hg⟩ := hI2 v hv ((orthMap Q Kv ρ)⁻¹ * σ v) (by
          rw [hσ1 v hKL, mul_one, ← spinorNormHom_apply Q Kv hQ, map_inv, spinorNormHom_apply, hθρ,
            SqClass.inv_eq]
          exact ⟨_, hva' v hvS, rfl⟩)
        exact ⟨k, hk, fun _ => hg⟩
  choose kv hkv hkv' using hdec
  -- the adelic element `h`
  let h : OAf Q := ⟨kv, by
    filter_upwards [loc_eventually_std K.2, loc_eventually_std L.2, (diagF Q ρ).2,
      Filter.eventually_cofinite_ne v₀] with v hK hL hρv hne
    have hKL : loc v K.1 = loc v L.1 := hK.trans hL.symm
    have hs := (locStabV_eq_stdStab Q v K hK).mp (by
      have := hkv' v hne
      rwa [hσ1 v hKL, mul_one] at this)
    have e : kv v = (orthMap Q _ ρ)⁻¹ * ((kv v)⁻¹ * (orthMap Q _ ρ)⁻¹)⁻¹ := by group
    rw [e]
    exact (stdStab Q v).mul_mem ((stdStab Q v).inv_mem hρv) ((stdStab Q v).inv_mem hs)⟩
  have hk : h ∈ spinorKernelAf Q := fun v => hkv v
  obtain ⟨γ, hγ, hloc⟩ := hSA.approx Q hn hQ v₀ hiso K h hk
  refine ⟨ρ * γ, ?_, fun v hv => ?_⟩
  · rw [Tamagawa.mem_soSub, Subgroup.coe_mul, Units.val_mul, det_mul]
    have h1 : ((ρ : GL (Fin n) F)).val.det = 1 := by
      rw [hρdef, Subgroup.coe_mul, Units.val_mul, det_mul, symm_det Q F hx0, symm_det Q F hy]
      norm_num
    have h2 : ((γ : GL (Fin n) F)).val.det = 1 := by
      have := ((Subgroup.mem_inf.mp ((spinorKernel_eq_ker Q F hQ) ▸ hγ)).2)
      have h3 := congrArg Units.val (MonoidHom.mem_ker.mp this)
      rw [detHom_val] at h3
      simpa using h3
    rw [h1, h2, one_mul]
  · have h1 := hloc v hv
    have h2 := hσ v hv
    have h3 := hkv' v hv
    -- `locAct (k_v⁻¹ ρ_v⁻¹ σ_v) K_v = K_v`
    have h4 : locAct v ((((kv v)⁻¹ * ((orthMap Q _ ρ)⁻¹ * σ v) : orthGroup Q _)) : GL (Fin n) _)
        (loc v K.1) = loc v K.1 := h3
    rw [Subgroup.coe_mul, locAct_mul, Subgroup.coe_mul, locAct_mul, h2] at h4
    have e1 : locAct v ((kv v : GL (Fin n) (v.adicCompletion F))) (loc v K.1) =
        locAct v (GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) (γ : GL (Fin n) F))
          (loc v K.1) := by
      have h1' : locAct v ((((orthMap Q (v.adicCompletion F) γ : orthGroup Q _) : GL _ _))⁻¹ *
          (kv v : GL _ _)) (loc v K.1) = loc v K.1 := h1
      rw [locAct_mul] at h1'
      have := locAct_eq_iff.mp h1'
      rw [inv_inv] at this
      exact this
    have e2 : locAct v (((orthMap Q (v.adicCompletion F) ρ : orthGroup Q _) : GL _ _)⁻¹) (loc v L.1) =
        locAct v ((kv v : GL (Fin n) (v.adicCompletion F))) (loc v K.1) := by
      have := locAct_eq_iff.mp h4
      simp only [Subgroup.coe_inv, inv_inv] at this
      exact this
    rw [Subgroup.coe_mul, glImage_mul, loc_glImage, loc_glImage, ← e1, ← e2]
    change locAct v ((orthMap Q (v.adicCompletion F) ρ : orthGroup Q _) : GL _ _)
      (locAct v (((orthMap Q (v.adicCompletion F) ρ : orthGroup Q _) : GL _ _)⁻¹) (loc v L.1)) = _
    rw [← locAct_mul, mul_inv_cancel, locAct_one]

end Key

/-! ### Local lemmas at a non-dyadic place -/

section LocalLemmas

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

open QuadFormsKB.LocalDensity in
/-- Two free lattices, integral with Gram determinants prime to $v$ ($v$ non-dyadic), are carried onto each other
by an element of $O(V_v)$ (O'Meara 92:2). -/
theorem exists_locAct_of_unimodular (v : HeightOneSpectrum (𝓞 F)) (h2 : (2 : 𝓞 F) ∉ v.asIdeal)
    (γ δ : GL (Fin n) F) (hγ : IsIntegral Q (latOf γ)) (hδ : IsIntegral Q (latOf δ))
    (hdγ : (gramZ Q γ hγ).hessian.det ∉ v.asIdeal) (hdδ : (gramZ Q δ hδ).hessian.det ∉ v.asIdeal) :
    ∃ g ∈ orthGroup Q (v.adicCompletion F), locAct v g (loc v (latOf γ)) = loc v (latOf δ) := by
  refine HilbertModular.exists_locAct_of_isometricGL v Q γ δ hγ hδ ?_
  refine Nbr.isometricGL_of_unimodular_of_isometricIn (NF.irreducible_π v) (NF.π_not_dvd_two v h2)
    (v.adicCompletion F) _ _ (NF.π_not_dvd_det v _ hdγ) (NF.π_not_dvd_det v _ hdδ)
    (GeneralLinearGroup.map (algebraMap F _) (γ⁻¹ * δ)) fun x => ?_
  rw [HilbertModular.evalIn_gramZ_map_completion, HilbertModular.evalIn_gramZ_map_completion]
  change _ = Q.evalIn _ (γ.val.map _ *ᵥ ((γ⁻¹ * δ).val.map _ *ᵥ x))
  rw [mulVec_mulVec, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel_left]

variable (K : Type*) [Field K] [Algebra F K] [CharZero K]

/-- $(Q_\gamma)(x_0) = Q(\gamma x_0)$ for the Gram form $Q_\gamma = Q(\gamma\,\cdot)$ of a free integral lattice,
base changed to $F$ and evaluated over $K$. -/
theorem evalIn_gramZ_map_F (γ : GL (Fin n) F) (hγ : IsIntegral Q (latOf γ)) (x₀ : Fin n → K) :
    ((gramZ Q γ hγ).map (algebraMap (𝓞 F) F)).evalIn K x₀ =
      Q.evalIn K ((GeneralLinearGroup.map (algebraMap F K) γ).val *ᵥ x₀) := by
  rw [gramZ_map, evalIn_gramF]
  rfl

/-- **Conjugating a symmetry by a basis change:** $\tau^{Q}_{\gamma x_0} = \gamma\,\tau^{Q_\gamma}_{x_0}\,\gamma^{-1}$. -/
theorem symm_gram_conj (γ : GL (Fin n) F) (hγ : IsIntegral Q (latOf γ)) (x₀ : Fin n → K)
    (hx : ((gramZ Q γ hγ).map (algebraMap (𝓞 F) F)).evalIn K x₀ ≠ 0) :
    ((symm Q K ((GeneralLinearGroup.map (algebraMap F K) γ).val *ᵥ x₀) : orthGroup Q K) : GL (Fin n) K) =
      GeneralLinearGroup.map (algebraMap F K) γ *
        (symm ((gramZ Q γ hγ).map (algebraMap (𝓞 F) F)) K x₀ : GL (Fin n) K) *
          (GeneralLinearGroup.map (algebraMap F K) γ)⁻¹ := by
  set G := GeneralLinearGroup.map (algebraMap F K) γ with hG
  set Qg := (gramZ Q γ hγ).map (algebraMap (𝓞 F) F) with hQg
  have hQ' : Q.evalIn K (G.val *ᵥ x₀) = Qg.evalIn K x₀ := (evalIn_gramZ_map_F Q K γ hγ x₀).symm
  have hx' : Q.evalIn K (G.val *ᵥ x₀) ≠ 0 := by rwa [hQ']
  have hH : Qg.hessian.map (algebraMap F K) = G.valᵀ * Q.hessian.map (algebraMap F K) * G.val := by
    rw [hQg, gramZ_map, hessian_gramF]
    simp [hG, Matrix.map_mul, Matrix.transpose_map]
  have key : ∀ a b : Fin n → K, a ⬝ᵥ (Qg.hessian.map (algebraMap F K) *ᵥ b) =
      (G.val *ᵥ a) ⬝ᵥ (Q.hessian.map (algebraMap F K) *ᵥ (G.val *ᵥ b)) := by
    intro a b
    rw [hH, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec a, vecMul_transpose]
  apply Units.ext
  refine Matrix.toLin'.injective (LinearMap.ext fun y => ?_)
  simp only [Matrix.toLin'_apply]
  rw [Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec]
  change _ = G.val *ᵥ (((symm Qg K x₀ : orthGroup Qg K) : GL (Fin n) K).val *ᵥ _)
  rw [symm_mulVec Q K hx', symm_mulVec Qg K hx, mulVec_sub, mulVec_smul, mulVec_inv_mulVec, key x₀,
    mulVec_inv_mulVec, hQ']

/-- **`LocalSpinorUnits` for a free integral lattice with Gram determinant prime to a non-dyadic $v$** ($n \ge 2$,
$Q$ nondegenerate): symmetries in vectors of $L_v = \gamma\,\mathfrak o_v^n$ whose value is a unit are improper
elements of $O(L_v)$ with every unit spinor norm. -/
theorem localSpinorUnits_of_free (hQ : Q.Nondegenerate) (hn : 2 ≤ n) (v : HeightOneSpectrum (𝓞 F))
    (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (γ : GL (Fin n) F) (hγ : IsIntegral Q (latOf γ))
    (hdγ : (gramZ Q γ hγ).hessian.det ∉ v.asIdeal) (L : Lat F n) (hL : L.1 = latOf γ) :
    LocalSpinorUnits Q v L := by
  refine localSpinorUnits_of_improper Q v hQ L fun u hu => ?_
  obtain ⟨x₀, hx₀, hQx₀⟩ := exists_std_evalIn_eq_unit v (gramZ Q γ hγ) h2 hdγ hn hu
  set G := GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) γ with hG
  have hu0 : u ≠ 0 := by intro h; rw [h, map_zero] at hu; exact zero_ne_one hu
  have hQx : Q.evalIn (v.adicCompletion F) (G.val *ᵥ x₀) = u := by
    rw [← hQx₀]; exact (evalIn_gramZ_map_F Q (v.adicCompletion F) γ hγ x₀).symm
  have hne : ((gramZ Q γ hγ).map (algebraMap (𝓞 F) F)).evalIn (v.adicCompletion F) x₀ ≠ 0 := by rw [hQx₀]; exact hu0
  have hloc : loc v L.1 = locAct v G (std v) := by
    rw [hL, latOf, loc_glImage, loc_intVec]
  have hx0 : Q.evalIn (v.adicCompletion F) (G.val *ᵥ x₀) ≠ 0 := by rw [hQx]; exact hu0
  refine ⟨symm Q (v.adicCompletion F) (G.val *ᵥ x₀), ?_, ?_, ?_⟩
  · change locAct v ((symm Q (v.adicCompletion F) (G.val *ᵥ x₀) : orthGroup Q (v.adicCompletion F)) : GL (Fin n) (v.adicCompletion F)) (loc v L.1) = loc v L.1
    have hs := symm_mem_stdStab v (gramZ Q γ hγ) hx₀ (by rw [hQx₀, hu])
    have hs' : locAct v ((symm ((gramZ Q γ hγ).map (algebraMap (𝓞 F) F)) (v.adicCompletion F) x₀ : orthGroup _ (v.adicCompletion F)) :
        GL (Fin n) (v.adicCompletion F)) (std v) = std v := hs
    rw [symm_gram_conj Q (v.adicCompletion F) γ hγ x₀ hne, hloc, locAct_mul, locAct_mul, locAct_inv_locAct, hs']
  · ext
    rw [detHom_val, symm_det Q (v.adicCompletion F) hx0]
    simp
  · rw [spinorNorm_symm Q (v.adicCompletion F) hQ hx0, hQx]

end LocalLemmas

/-! ### The case $I_n$ over $\mathbb Q$: Gram determinant of a unimodular free lattice -/

section SumSq

variable {n : ℕ}

theorem two_sumSq_hessian (n : ℕ) : (sumSqForm n).hessian = (2 : ℚ) • (1 : Matrix (Fin n) (Fin n) ℚ) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp [QuadForm.hessian, sumSqForm, QuadForm.diag]; norm_num
  · simp [QuadForm.hessian, sumSqForm, QuadForm.diag, hij]

theorem two_sumSq_bil_dot (x y : Fin n → ℚ) : bil (sumSqForm n) x y = 2 * (x ⬝ᵥ y) := by
  rw [bil, two_sumSq_hessian, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]

theorem exists_int_of_mem_intVec {z : Fin n → ℚ} (hz : z ∈ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ))) (i : Fin n) :
    ∃ m : ℤ, z i = m := by
  obtain ⟨a, ha⟩ := hz i
  exact ⟨Rat.ringOfIntegersEquiv a, by rw [Rat.ringOfIntegersEquiv_apply_coe]; exact ha.symm⟩

/-- **A unimodular free lattice $\gamma\mathbb Z^n$ on $I_n$ has $(\det\gamma)^2 = 1$.** -/
theorem sq_det_eq_one_of_unimodular (γ : GL (Fin n) ℚ) (hu : IsUnimodularZ (sumSqForm n) (latOf γ)) :
    γ.val.det ^ 2 = 1 := by
  have hd : ∀ x ∈ latOf γ, ∀ y ∈ latOf γ, ∃ m : ℤ, x ⬝ᵥ y = m := by
    intro x hx y hy
    have hx' : x ∈ omearaDual (sumSqForm n) (latOf γ) := by rw [hu]; exact hx
    obtain ⟨m, hm⟩ := hx' y hy
    exact ⟨m, by rw [two_sumSq_bil_dot] at hm; linarith⟩
  set M := (γ⁻¹ : GL (Fin n) ℚ).val with hM
  have hMγ : M * γ.val = 1 := by rw [hM, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hγM : γ.val * M = 1 := by rw [hM, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  obtain ⟨Gz, hGz⟩ : ∃ Gz : Matrix (Fin n) (Fin n) ℤ, Gz.map (Int.cast : ℤ → ℚ) = γ.valᵀ * γ.val := by
    have : ∀ j k, ∃ m : ℤ, (γ.valᵀ * γ.val) j k = m := by
      intro j k
      obtain ⟨m, hm⟩ := hd _ (mulVec_mem_glImage (single_one_mem_intVec j)) _
        (mulVec_mem_glImage (single_one_mem_intVec k))
      refine ⟨m, ?_⟩
      rw [← hm, mulVec_single_one, mulVec_single_one]
      simp [Matrix.mul_apply, dotProduct]
    choose g hg using this
    exact ⟨Matrix.of g, by ext j k; simp [hg]⟩
  obtain ⟨Wz, hWz⟩ : ∃ Wz : Matrix (Fin n) (Fin n) ℤ, Wz.map (Int.cast : ℤ → ℚ) = M * Mᵀ := by
    have : ∀ j i, ∃ m : ℤ, (M * Mᵀ) j i = m := by
      intro j i
      have hdi : (fun k => M i k) ∈ omearaDual (sumSqForm n) (latOf γ) := by
        intro y hy
        rw [latOf, mem_glImage] at hy
        obtain ⟨z, hz, rfl⟩ := hy
        obtain ⟨m, hm⟩ := exists_int_of_mem_intVec hz i
        refine ⟨m, ?_⟩
        rw [two_sumSq_bil_dot]
        have : (fun k => M i k) ⬝ᵥ (γ.val *ᵥ z) = z i := by
          have := congrFun (show M *ᵥ (γ.val *ᵥ z) = z by rw [mulVec_mulVec, hMγ, one_mulVec]) i
          simpa [Matrix.mulVec, dotProduct] using this
        rw [this, hm]; ring
      rw [hu, latOf, mem_glImage] at hdi
      obtain ⟨w, hw, hgw⟩ := hdi
      obtain ⟨m, hm⟩ := exists_int_of_mem_intVec hw j
      refine ⟨m, ?_⟩
      have hw' : w = M *ᵥ (fun k => M i k) := by rw [← hgw, mulVec_mulVec, hMγ, one_mulVec]
      rw [← hm, hw']
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    choose g hg using this
    exact ⟨Matrix.of g, by ext j i; simp [hg]⟩
  have hGW : Gz * Wz = 1 := by
    have hinj : Function.Injective ((Int.castRingHom ℚ).mapMatrix : Matrix (Fin n) (Fin n) ℤ →+* _) :=
      Matrix.map_injective (Int.cast_injective (α := ℚ))
    apply hinj
    rw [map_mul, map_one]
    simp only [RingHom.mapMatrix_apply, Int.coe_castRingHom]
    rw [hGz, hWz]
    calc γ.valᵀ * γ.val * (M * Mᵀ) = γ.valᵀ * (γ.val * M) * Mᵀ := by simp [Matrix.mul_assoc]
      _ = 1 := by rw [hγM, Matrix.mul_one, ← Matrix.transpose_mul, hMγ, Matrix.transpose_one]
  have hdet : Gz.det * Wz.det = 1 := by rw [← Matrix.det_mul, hGW, Matrix.det_one]
  have hcast : (Gz.det : ℚ) = γ.val.det ^ 2 := by
    rw [Int.cast_det, hGz, Matrix.det_mul, Matrix.det_transpose, sq]
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hdet with h | h
  · rw [← hcast, h]; simp
  · exfalso
    have : (0 : ℚ) ≤ γ.val.det ^ 2 := sq_nonneg _
    rw [← hcast, h] at this
    norm_num at this

theorem two_sumSq_evalIn (x : Fin n → ℚ) : (sumSqForm n).evalIn ℚ x = ∑ i, x i ^ 2 := by
  rw [sumSqForm, QuadForm.evalIn_diag]; simp

/-- A unimodular lattice on $I_n$ is integral ($Q(L) \subseteq \mathbb Z$). -/
theorem isIntegral_of_unimodular {L : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hu : IsUnimodularZ (sumSqForm n) L) :
    IsIntegral (sumSqForm n) L := by
  intro x hx
  have hx' : x ∈ omearaDual (sumSqForm n) L := by rw [hu]; exact hx
  obtain ⟨m, hm⟩ := hx' x hx
  refine ⟨Rat.ringOfIntegersEquiv.symm m, ?_⟩
  rw [← Rat.ringOfIntegersEquiv_apply_coe]
  simp only [RingEquiv.apply_symm_apply]
  rw [two_sumSq_bil_dot] at hm
  rw [two_sumSq_evalIn]
  have : ∑ i, x i ^ 2 = x ⬝ᵥ x := by simp [dotProduct, sq]
  rw [this]; linarith

/-- The Gram form of a unimodular free lattice on $I_n$ has determinant $2^n$, which is prime to every odd place. -/
theorem gram_det_not_mem (γ : GL (Fin n) ℚ) (hγ : IsIntegral (sumSqForm n) (latOf γ))
    (hu : IsUnimodularZ (sumSqForm n) (latOf γ)) (v : HeightOneSpectrum (𝓞 ℚ))
    (h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal) : (gramZ (sumSqForm n) γ hγ).hessian.det ∉ v.asIdeal := by
  intro hmem
  have e : algebraMap (𝓞 ℚ) ℚ (gramZ (sumSqForm n) γ hγ).hessian.det = 2 ^ n := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    have h1 : (gramZ (sumSqForm n) γ hγ).hessian.map (algebraMap (𝓞 ℚ) ℚ) =
        γ.valᵀ * (sumSqForm n).hessian * γ.val := by
      rw [← QuadForm.hessian_map, gramZ_map, hessian_gramF]
    rw [h1, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, two_sumSq_hessian, Matrix.det_smul,
      Matrix.det_one, Fintype.card_fin]
    have := sq_det_eq_one_of_unimodular γ hu
    rw [mul_comm _ (2 ^ n * 1), mul_assoc, mul_comm _ (γ.val.det), ← sq, this]
    ring
  have e' : (gramZ (sumSqForm n) γ hγ).hessian.det = 2 ^ n :=
    FaithfulSMul.algebraMap_injective (𝓞 ℚ) ℚ (by rw [e, map_pow, map_ofNat])
  rw [e'] at hmem
  exact h2 (v.isPrime.mem_of_pow_mem n hmem)

/-- **$I_n$ ($n \ge 4$) represents every natural number** (Lagrange's four-squares theorem). -/
theorem exists_eval_eq_natCast (hn : 4 ≤ n) (N : ℕ) : ∃ x : Fin n → ℚ, (sumSqForm n).evalIn ℚ x = N := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 4 + m := ⟨n - 4, by omega⟩
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares N
  refine ⟨Fin.append ![(a : ℚ), b, c, d] 0, ?_⟩
  rw [two_sumSq_evalIn, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, Finset.sum_const_zero, add_zero, Fin.sum_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  exact_mod_cast h

/-- $\pm 1$ is a unit at every finite place. -/
theorem valued_unit_of_pm_one {F : Type} [Field F] [NumberField F] (u : F) (h : u = 1 ∨ u = -1)
    (v : HeightOneSpectrum (𝓞 F)) : Valued.v (algebraMap F (v.adicCompletion F) u) = 1 := by
  rcases h with rfl | rfl <;> simp

/-- The rational hypothesis of `exists_rotation_agree_away` for $I_n$ ($n \ge 4$): for every non-zero integer
$a_0$ there are $x, y$ with $Q(y) = 1$ and $Q(x) = \pm a_0 Q(y)$, the sign being a unit at every place. -/
theorem exists_rho_sumSq (hn : 4 ≤ n) (a₀ : 𝓞 ℚ) (ha₀ : a₀ ≠ 0) :
    ∃ x y : Fin n → ℚ, (sumSqForm n).evalIn ℚ y ≠ 0 ∧ ∃ u : ℚ, (u = 1 ∨ u = -1) ∧
      (sumSqForm n).evalIn ℚ x = u * algebraMap (𝓞 ℚ) ℚ a₀ * (sumSqForm n).evalIn ℚ y := by
  set k : ℤ := Rat.ringOfIntegersEquiv a₀ with hk
  have hk0 : k ≠ 0 := by
    intro h; apply ha₀
    exact Rat.ringOfIntegersEquiv.injective (by rw [← hk, h, map_zero])
  have hak : algebraMap (𝓞 ℚ) ℚ a₀ = (k : ℚ) := by
    rw [hk, Rat.ringOfIntegersEquiv_apply_coe]
  obtain ⟨x, hx⟩ := exists_eval_eq_natCast hn k.natAbs
  let i0 : Fin n := ⟨0, by omega⟩
  have hy : (sumSqForm n).evalIn ℚ (Pi.single i0 (1 : ℚ)) = 1 := by
    rw [two_sumSq_evalIn]; simp [Pi.single_apply]
  refine ⟨x, Pi.single i0 1, by rw [hy]; exact one_ne_zero, ?_⟩
  have hcast : ((k.natAbs : ℕ) : ℚ) = |(k : ℚ)| := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]; simp
  rcases lt_or_gt_of_ne hk0 with hneg | hpos
  · refine ⟨-1, Or.inr rfl, ?_⟩
    have : (k : ℚ) < 0 := by exact_mod_cast hneg
    rw [hx, hy, hak, hcast, abs_of_neg this]; ring
  · refine ⟨1, Or.inl rfl, ?_⟩
    have : (0 : ℚ) < k := by exact_mod_cast hpos
    rw [hx, hy, hak, hcast, abs_of_pos this]; ring

end SumSq

/-! ### Proposition 106:2 -/

section Main

/-- $2$ is a prime element of $\mathcal O_{\mathbb Q} \cong \mathbb Z$. -/
theorem two_prime_oQ : Prime (2 : 𝓞 ℚ) := by
  have h : Prime ((Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ) 2) := by
    rw [map_ofNat]; exact Int.prime_two
  exact (MulEquiv.prime_iff (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ).toMulEquiv).mp h

/-- The dyadic place of $\mathbb Q$ (the spot of the prime $2$). -/
def two_dyadicPlace : HeightOneSpectrum (𝓞 ℚ) := Nbr.hosOf two_prime_oQ

theorem two_mem_two_dyadicPlace : (2 : 𝓞 ℚ) ∈ two_dyadicPlace.asIdeal := by
  change (2 : 𝓞 ℚ) ∈ Ideal.span {(2 : 𝓞 ℚ)}
  exact Ideal.mem_span_singleton_self _

/-- A place is dyadic iff $2$ lies in it. -/
theorem two_notMem_of_ne_two_dyadicPlace {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ≠ two_dyadicPlace) :
    (2 : 𝓞 ℚ) ∉ v.asIdeal := by
  intro h2
  apply hv
  have hle : two_dyadicPlace.asIdeal ≤ v.asIdeal := by
    change Ideal.span {(2 : 𝓞 ℚ)} ≤ v.asIdeal
    rw [Ideal.span_le, Set.singleton_subset_iff]; exact h2
  exact HeightOneSpectrum.ext ((two_dyadicPlace.isMaximal.eq_of_le v.isPrime.ne_top hle).symm)

theorem ne_two_dyadicPlace_of_notMem {v : HeightOneSpectrum (𝓞 ℚ)} (h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal) :
    v ≠ two_dyadicPlace := fun h => h2 (h ▸ two_mem_two_dyadicPlace)

/-- The dual of the image of a lattice under an isometry is the image of the dual (for $I_n$). -/
theorem two_omearaDual_glImage {n : ℕ} {γ : GL (Fin n) ℚ} (hγ : γ ∈ orthGroup (sumSqForm n) ℚ)
    (K : Submodule (𝓞 ℚ) (Fin n → ℚ)) :
    omearaDual (sumSqForm n) (glImage γ K) = glImage γ (omearaDual (sumSqForm n) K) := by
  ext x
  constructor
  · intro hx
    refine ⟨γ⁻¹.val *ᵥ x, ?_, mulVec_inv_mulVec γ x⟩
    intro y hy
    obtain ⟨m, hm⟩ := hx (γ.val *ᵥ y) (mulVec_mem_glImage hy)
    refine ⟨m, ?_⟩
    have := bil_isometry (sumSqForm n) hγ (γ⁻¹.val *ᵥ x) y
    rw [mulVec_inv_mulVec] at this
    rw [← this]
    exact hm
  · rintro ⟨x', hx', rfl⟩ y hy
    obtain ⟨y', hy', rfl⟩ := hy
    obtain ⟨m, hm⟩ := hx' y' hy'
    refine ⟨m, ?_⟩
    show bil (sumSqForm n) (γ.val *ᵥ x') (γ.val *ᵥ y') / 2 = m
    rw [bil_isometry (sumSqForm n) hγ]
    exact hm

/-- **Proposition 106:2 — proved** (O'Meara 1973, §106B, p. 325). Let $n \ge 5$ and let $K, L$ be unimodular lattices on
$V = I_n$ over $\mathbb Q$ (`sumSqForm n`, `IsUnimodularZ`). Then there is a lattice $J$ in the proper class of $K$
(`IsProperIsometric`: $J = \sigma K$ with $\sigma \in O^+(V)$) with $J \in \mathcal G(L)$ (`omearaG`: $J$ unimodular and
$J_p = L_p$ at every odd prime $p$). This is the same proposition as the field `holds` of `OMeara106_2`
(`Sec106Class.lean`). The proof uses strong approximation away from $2$ (`strongApproximationSpinAt`) instead of
O'Meara's Theorem 104:10 over $\mathbb Z[\tfrac12]$; unconditional. -/
@[kb "omeara1963" "§106B, 106:2, p. 325 (different proof: strong approximation away from 2)"]
theorem omeara106_2_holds : ∀ (n : ℕ), 5 ≤ n → ∀ K L : Lat ℚ n, IsUnimodularZ (sumSqForm n) K.1 →
    IsUnimodularZ (sumSqForm n) L.1 →
    ∃ J : Lat ℚ n, IsProperIsometric (sumSqForm n) K.1 J.1 ∧ J ∈ omearaG (sumSqForm n) L := by
  intro n hn K L hK hL
  have : IsPrincipalIdealRing (𝓞 ℚ) :=
    IsPrincipalIdealRing.of_surjective Rat.ringOfIntegersEquiv.symm.toRingHom
      Rat.ringOfIntegersEquiv.symm.surjective
  have hQ : (sumSqForm n).Nondegenerate := QuadForm.nondegenerate_diag (fun _ => one_ne_zero)
  obtain ⟨γ, hγ⟩ := HilbertModular.exists_latOf_of_isPrincipalIdealRing K
  obtain ⟨δ, hδ⟩ := HilbertModular.exists_latOf_of_isPrincipalIdealRing L
  have hKγ : IsUnimodularZ (sumSqForm n) (latOf γ) := hγ ▸ hK
  have hLδ : IsUnimodularZ (sumSqForm n) (latOf δ) := hδ ▸ hL
  have hIγ : IsIntegral (sumSqForm n) (latOf γ) := isIntegral_of_unimodular hKγ
  have hIδ : IsIntegral (sumSqForm n) (latOf δ) := isIntegral_of_unimodular hLδ
  obtain ⟨ρ, hρso, hρloc⟩ := exists_rotation_agree_away (sumSqForm n) strongApproximationSpinAt hQ
    (by omega) (v₀ := two_dyadicPlace) (isotropicIn_completion_of_five_le _ hn hQ _) K L
    (fun v hv => by
      have h2 := two_notMem_of_ne_two_dyadicPlace hv
      obtain ⟨g, hg, he⟩ := exists_locAct_of_unimodular (sumSqForm n) v h2 γ δ hIγ hIδ
        (gram_det_not_mem γ hIγ hKγ v h2) (gram_det_not_mem δ hIδ hLδ v h2)
      exact ⟨⟨g, hg⟩, by rw [hγ, hδ]; exact he⟩)
    (fun v hv => by
      have h2 := two_notMem_of_ne_two_dyadicPlace hv
      exact localSpinorUnits_of_free (sumSqForm n) hQ (by omega) v h2 γ hIγ
        (gram_det_not_mem γ hIγ hKγ v h2) K hγ)
    (fun a₀ ha₀ => by
      obtain ⟨x, y, hy, u, hu, hxy⟩ := exists_rho_sumSq (n := n) (by omega) a₀ ha₀
      exact ⟨x, y, hy, u, valued_unit_of_pm_one u hu, hxy⟩)
  refine ⟨Lat.image (ρ : GL (Fin n) ℚ) K, ⟨ρ, hρso, rfl⟩, ?_, fun v hv => ?_⟩
  · show omearaDual (sumSqForm n) (glImage (ρ : GL (Fin n) ℚ) K.1) = glImage (ρ : GL (Fin n) ℚ) K.1
    rw [two_omearaDual_glImage ρ.2, show omearaDual (sumSqForm n) K.1 = K.1 from hK]
  · exact hρloc v (ne_two_dyadicPlace_of_notMem hv)

end Main

end QuadFormsKB.Lattices
