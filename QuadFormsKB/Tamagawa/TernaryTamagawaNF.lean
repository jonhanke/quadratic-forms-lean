/-
# $\tau(SO_3) = 2$ for every totally real field: `TernaryTamagawaTwo F` for every class number

**Layer:** $F$ totally real (any class number), $D = (a,b)_F$ totally definite, $\mathcal O \supseteq \mathcal O_F\langle1,i,j,k\rangle$ a maximal order,
$L = \mathcal O^0$ (`pureLat`, not free in general), $Q_0 = \langle -a,-b,ab\rangle$.

**Assembly.** By `tauSOLat_eq_dcMass` $\tau = \mu_{\mathrm{Tam}}(K_{SO}(L))\cdot\mathrm{dcMass}(SO(F), SO(\hat L))$.
By the local computations (completion of the trace-zero lattice, local conjugation maps, the index $[K_0 : K']$)
and Eichler's mass formula for
every class number (`dcMass_K0NF_eq`, $h_F$ cancels) the mass is $2^{-\#\mathrm{Ram}_f}\cdot2\zeta_F(2)\prod_{\mathrm{Ram}_f}(1-N\mathfrak p^{-1})/(c_{\mathcal O}d_F^{1/2}\pi^{2d})$.
By `tamagawaKLat_eq_local_gen` with local adapted bases and the local factors (`LTZ.localFactor_eq`),
$\mu(K_{SO}(L)) = d_F^{-3/2}\prod_\sigma\mathrm{vol}(SO(V_\sigma))\prod_v(1-q_v^{-2})\varepsilon_v|8|_v^{-1}|ab|_v^{-3}\|\det E_v\|$, and
$\prod_v\|\det E_v\| = \operatorname{covol}(\mathcal O)^{-1}$ (`tprod_norm_det_presBasisV`), $c_{\mathcal O} = (|N(ab)|\,d_F^2\operatorname{covol}(\mathcal O))^{-1}$
(`latConst_mul_covol`). The product is $2$.

**Proves** **`tauSOLat_pureLat_eq_two`** and **`ternaryTamagawaTwo_nf`**: `TernaryTamagawaTwo F` for every totally real $F$, unconditionally.

Source: Weil 1982, §3.7(a), Thm. 3.7.1 ($m = 3$); Voight 2021, Thm. 26.5.4 (Eichler's mass formula, with $h_F$).
-/
import QuadFormsKB.Tamagawa.TernarySOMassNF
import QuadFormsKB.Tamagawa.TernaryLocalFactorNF
import QuadFormsKB.Tamagawa.TernaryCovolNF
import QuadFormsKB.Tamagawa.LatticeLocalGenNF

open NumberField IsDedekindDomain Matrix Quaternion Real
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

open QuadFormsKB.Quat QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.QuadForm QuadFormsKB.QuatZeta
  QuadFormsKB.HilbertModular QuadFormsKB.NFEuler QuadFormsKB.SphericalUnfold QuadFormsKB.IdeleClass
  QuadFormsKB.AdditiveZeta QuadFormsKB.LocalDensity

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F}

/-! ### Helpers -/

theorem map_Qp_pureFormO (v : HeightOneSpectrum (𝓞 F)) :
    (NF.Qp v (pureFormO a b)).map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) = LTZ.QV v a b := by
  refine QuadForm.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp [QuadForm.map, pureFormO, pureForm, QuadForm.diag, Matrix.diagonal, NF.Qp]

theorem detHalf_pureFormO : detHalf (pureFormO a b) = (algebraMap (𝓞 F) F a) ^ 2 * (algebraMap (𝓞 F) F b) ^ 2 := by
  have hH : (pureFormO a b).hessian = Matrix.diagonal ![-2 * a, -2 * b, 2 * (a * b)] := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [QuadForm.hessian, pureFormO, QuadForm.diag, Matrix.diagonal] <;> ring
  rw [detHalf, hH, det_diagonal, Fin.prod_univ_three]
  simp
  rw [map_ofNat]; ring

theorem detHalf_pureFormO_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : detHalf (pureFormO a b) ≠ 0 := by
  rw [detHalf_pureFormO]
  have ha' : algebraMap (𝓞 F) F a ≠ 0 := (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr ha
  have hb' : algebraMap (𝓞 F) F b ≠ 0 := (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hb
  exact mul_ne_zero (pow_ne_zero _ ha') (pow_ne_zero _ hb')

variable [IsTotallyReal F]

/-- The archimedean product for $\langle -a,-b,ab\rangle$: $\prod_\sigma\mathrm{vol}(SO(V_\sigma)) = (\pi^2/8)^d/|N(a^2b^2)|^2$. -/
theorem prod_archVolSO_pureFormO (ha : a ≠ 0) (hb : b ≠ 0) :
    ∏ σ : F →ₐ[ℚ] ℂ, archVolSO 3 (detGram (pureFormO a b) σ) =
      (π ^ 2 / 8) ^ Module.finrank ℚ F / |((Algebra.norm ℚ (detHalf (pureFormO a b)) : ℚ) : ℝ)| ^ 2 := by
  have hD := detHalf_pureFormO_ne_zero ha hb
  have hg : ∀ σ : F →ₐ[ℚ] ℂ, detGram (pureFormO a b) σ = ‖σ (detHalf (pureFormO a b))‖ := fun σ => by
    unfold detGram detHalf; norm_num
  have hpos : ∀ σ : F →ₐ[ℚ] ℂ, 0 < ‖σ (detHalf (pureFormO a b))‖ := fun σ => norm_pos_iff.2 ((map_ne_zero σ).2 hD)
  simp_rw [hg, fun σ => archVolSO_three (hpos σ)]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, AlgHom.card, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, AlgHom.card, Finset.prod_pow, prod_norm_embeddings, div_pow, div_div]

/-- **The lattice constant of $\mathcal O_F\langle1,i,j,k\rangle$**: $c = (|N(ab)|\,d_F^2)^{-1}$. -/
theorem latConst_nrdGram_one (hdef : IsTotDefinite a b) :
    latConst (Gen.nrdGram (F := F) a b) (fun _ => 1) =
      (|((Algebra.norm ℚ (algebraMap (𝓞 F) F a * algebraMap (𝓞 F) F b) : ℚ) : ℝ)| *
        (NumberField.discr F : ℝ) ^ 2)⁻¹ := by
  have hd : (0 : ℝ) < NumberField.discr F := AdditiveZeta.discr_pos
  unfold AdditiveZeta.latConst
  have hdet : ∀ v : InfinitePlace F, Real.sqrt ((Gen.nrdGram (F := F) a b).map (realEmb F v)).det =
      |realEmb F v (algebraMap (𝓞 F) F a * algebraMap (𝓞 F) F b)| := fun v => by
    have h1 : ((Gen.nrdGram (F := F) a b).map (realEmb F v)).det =
        (realEmb F v (algebraMap (𝓞 F) F a * algebraMap (𝓞 F) F b)) ^ 2 := by
      rw [Gen.nrdGram, Matrix.diagonal_map (map_zero _), det_diagonal, Fin.prod_univ_four]
      simp [nrdDiag, map_mul]; ring
    rw [h1, Real.sqrt_sq_eq_abs]
  simp_rw [hdet]
  rw [prod_abs_realEmb_eq, Finset.prod_const, Finset.card_univ, Fintype.card_fin, embDet_one]
  rw [show Real.sqrt (NumberField.discr F : ℝ) ^ 4 = (NumberField.discr F : ℝ) ^ 2 by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hd.le]]
  rw [mul_inv]

omit [IsTotallyReal F] in
theorem absV_eq_norm (v : HeightOneSpectrum (𝓞 F)) (x : F) : absV v x = ‖algebraMap F (v.adicCompletion F) x‖ := rfl

omit [IsTotallyReal F] in
/-- **The product of the local factors** $\prod_v(1-q_v^{-2})\varepsilon_v|8|_v^{-1}|ab|_v^{-3}D_v$ for $D_v = 1$ off a finite set. -/
theorem tprod_tzLoc (ha : a ≠ 0) (hb : b ≠ 0) {_inst : ∀ v, Decidable (v ∈ ramFin ha hb)}
    (D : HeightOneSpectrum (𝓞 F) → ℝ) (S : Finset (HeightOneSpectrum (𝓞 F))) (hD : ∀ v ∉ S, D v = 1) :
    ∏' v, tzLoc v (v ∈ ramFin ha hb) (absV v 8) (absV v (algebraMap (𝓞 F) F a * algebraMap (𝓞 F) F b)) (D v) =
      (dedekindZetaR F 2)⁻¹ * ((2 : ℝ) ^ (ramFin ha hb).card / ∏ v ∈ ramFin ha hb, (1 - (normP v : ℝ) ^ (-(1 : ℝ)))) *
        |((Algebra.norm ℚ (8 : F) : ℚ) : ℝ)| *
        |((Algebra.norm ℚ (algebraMap (𝓞 F) F a * algebraMap (𝓞 F) F b) : ℚ) : ℝ)| ^ 3 * ∏' v, D v := by
  classical
  rw [tprod_eq_prod hD]
  set x := algebraMap (𝓞 F) F a * algebraMap (𝓞 F) F b
  have hx : x ≠ 0 := mul_ne_zero ((map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr ha)
    ((map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hb)
  set g : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    (if v ∈ ramFin ha hb then 2 / (1 - (normP v : ℝ) ^ (-(1 : ℝ))) else 1) * (absV v 8)⁻¹ * (absV v x ^ 3)⁻¹ * D v
  have hfac : ∀ v, tzLoc v (v ∈ ramFin ha hb) (absV v 8) (absV v x) (D v) = (1 - (normP v : ℝ) ^ (-(2 : ℝ))) * g v := by
    intro v; unfold tzLoc; simp only [g]; ring
  have h8 : (8 : F) ≠ 0 := by norm_num
  set S' := ramFin ha hb ∪ (absV_hasFiniteMulSupport h8).toFinset ∪ (absV_hasFiniteMulSupport hx).toFinset ∪ S
  have hmem : ∀ {y : F} (hy : y ≠ 0) v, absV v y ≠ 1 → v ∈ (absV_hasFiniteMulSupport hy).toFinset := by
    intro y hy v hv; rw [Set.Finite.mem_toFinset]; exact hv
  have h8S : ∀ v, absV v 8 ≠ 1 → v ∈ S' := fun v hv => by
    simp only [S', Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (hmem h8 v hv)))
  have hxS : ∀ v, absV v x ≠ 1 → v ∈ S' := fun v hv => by
    simp only [S', Finset.mem_union]; exact Or.inl (Or.inr (hmem hx v hv))
  have hRS : ramFin ha hb ⊆ S' := fun v hv => by simp only [S', Finset.mem_union]; exact Or.inl (Or.inl (Or.inl hv))
  have hSS : S ⊆ S' := fun v hv => by simp only [S', Finset.mem_union]; exact Or.inr hv
  have hg1 : ∀ v ∉ S', g v = 1 := by
    intro v hv
    have e8 : absV v 8 = 1 := by_contra fun h => hv (h8S v h)
    have ex : absV v x = 1 := by_contra fun h => hv (hxS v h)
    have eR : v ∉ ramFin ha hb := fun h => hv (hRS h)
    have eD : D v = 1 := hD v fun h => hv (hSS h)
    simp only [g, e8, ex, if_neg eR, eD]; norm_num
  have hP : HasProd (fun v => (1 - (normP v : ℝ) ^ (-(2 : ℝ))) * g v) ((dedekindZetaR F 2)⁻¹ * ∏ v ∈ S', g v) :=
    (hasProd_one_sub_rpow (F := F) (by norm_num : (1 : ℝ) < 2)).mul (hasProd_prod_of_ne_finset_one hg1)
  have hR : ∏ v ∈ S', (if v ∈ ramFin ha hb then 2 / (1 - (normP v : ℝ) ^ (-(1 : ℝ))) else 1) =
      (2 : ℝ) ^ (ramFin ha hb).card / ∏ v ∈ ramFin ha hb, (1 - (normP v : ℝ) ^ (-(1 : ℝ))) := by
    rw [← Finset.prod_subset hRS (fun v _ hv => if_neg hv), Finset.prod_congr rfl (fun v hv => if_pos hv),
      Finset.prod_div_distrib, Finset.prod_const]
  have hDS : ∏ v ∈ S', D v = ∏ v ∈ S, D v :=
    (Finset.prod_subset hSS fun v _ hv => hD v hv).symm
  rw [tprod_congr hfac, hP.tprod_eq]
  simp only [g]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_inv_distrib,
    Finset.prod_inv_distrib, Finset.prod_pow, hR, prod_absV_of_subset h8 h8S, prod_absV_of_subset hx hxS, hDS,
    inv_inv, inv_pow, inv_inv]
  ring

/-- The local covolumes of a presented order are $1$ almost everywhere. -/
theorem exists_finset_norm_det_presBasisV {f : Fin 4 → QuatF F a b} {𝔟 : Fin 4 → Ideal (𝓞 F)} (h𝔟 : ∀ i, 𝔟 i ≠ ⊥)
    (hli : LinearIndependent F f) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, ‖(coordQ (presBasisV v f 𝔟)).det‖ = 1 := by
  classical
  have hdet0 : (coordMat f).det ≠ 0 := det_coordMat_ne_zero hli
  choose n hn hn0 using fun i => Submodule.exists_mem_ne_zero_of_ne_bot (h𝔟 i)
  refine ⟨(absV_hasFiniteMulSupport hdet0).toFinset ∪ Finset.univ.biUnion fun i => Gen.primeSupport (hn0 i),
    fun v hv => ?_⟩
  rw [norm_det_coordQ_presBasisV]
  have h1 : absV v (coordMat f).det = 1 := by
    by_contra h; exact hv (Finset.mem_union_left _ ((absV_hasFiniteMulSupport hdet0).mem_toFinset.2 h))
  rw [h1, one_mul]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [Gen.cI_eq_zero_of_mem_not_mem (h𝔟 i) (hn i) fun h => hv (Finset.mem_union_right _
    (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, (Gen.mem_primeSupport (hn0 i)).2 h⟩)), pow_zero, inv_one]

/-! ### The assembly -/

set_option maxHeartbeats 4000000 in
/-- **$\tau = 2$ on the trace-zero lattice of a maximal order, every class number** ($F$ totally real, $D = (a,b)_F$ totally definite,
$\mathcal O \supseteq \mathcal O_F\langle1,i,j,k\rangle$ maximal): `LatChange.tauSOLat` $\langle -a,-b,ab\rangle$ computed with $\mathcal O^0$ is $2$. -/
@[kb "weil1982" "§3.7(a), Thm. 3.7.1 (m = 3), p. 62-65; Voight 2021, Thm. 26.5.4 (with h_F)"]
theorem tauSOLat_pureLat_eq_two (ha : a ≠ 0) (hb : b ≠ 0)
    (hpd : IsTotallyPosDef ((pureFormO a b).map (algebraMap (𝓞 F) F)))
    {O : Subalgebra (𝓞 F) (QuatF F a b)} (hO : IsMaximalOrder (𝓞 F) F O) (hstd : stdOrder F a b ≤ O) :
    LatChange.tauSOLat (pureFormO a b) (pureLat hO.1) = 2 := by
  classical
  have hdef := isTotDefinite_of_pureFormO hpd
  have hQ : (pureFormO a b).Nondegenerate := nondegenerate_of_map hpd.nondegenerate
  rw [tauSOLat_eq_dcMass (pureFormO a b) hQ (by decide) hpd (pureLat hO.1) (isIntegral_pureLat hO.1)]
  change _ * dcMass (GamNF a b) (K0NF hO.1) = 2
  obtain ⟨f, 𝔟, h𝔟, hli, hmem⟩ := exists_integral_presentation hO.1
  have hmass := dcMass_K0NF_eq ha hb hdef hO hstd hli hmem
  rw [hmass]
  -- the local bases
  let L : ∀ v, LTZ v O := fun v => Classical.choice (LTZ.exists v hO.1)
  have hK := LatChange.tamagawaKLat_eq_local_gen (n := 3) (by norm_num) (by norm_num) (pureFormO a b) hQ
    (pureLat hO.1) (fun v => (L v).PG) (fun v => (L v).formT hO.1)
    (fun v => by rw [(L v).map_formT hO.1, map_Qp_pureFormO]; rfl) (fun v => (L v).loc_eq hO.1)
  rw [hK]
  -- the local factors
  have hloc : ∀ v, (1 / 2 : ℝ) * DVR.localDensityForm ((L v).formT hO.1) ((L v).formT hO.1) (NF.π v) *
      ‖(((L v).PG : GL (Fin 3) (v.adicCompletion F)).val.det)‖ ^ (3 + 1) =
      tzLoc v (v ∈ ramFin ha hb) (absV v 8) (absV v (algebraMap (𝓞 F) F a * algebraMap (𝓞 F) F b))
        ‖(coordQ (presBasisV v f 𝔟)).det‖ := by
    intro v
    have h1 := (L v).localFactor_eq ha hb hO (_inst := Classical.dec _)
    rw [LTZ.coordV_eq, norm_det_coordQ_eq (L v).mem_iff (mem_localOrder_iff_pres h𝔟 hmem) (L v).li] at h1
    rw [LTZ.PG_val]
    convert h1 using 2
    · rw [absV_eq_norm, map_ofNat]
    · rw [absV_eq_norm, map_mul]; rfl
  rw [tprod_congr hloc]
  obtain ⟨S, hS⟩ := exists_finset_norm_det_presBasisV h𝔟 hli
  rw [tprod_tzLoc ha hb _ S hS, tprod_norm_det_presBasisV h𝔟 hli, prod_archVolSO_pureFormO ha hb]
  -- the lattice constant
  have hlat := LatCovol.latConst_mul_covol (Gen.isTotPosGram_nrdGram hdef) (coordMat f) (det_coordMat_ne_zero hli)
    (fun i => Gen.idealUnit (𝔟 i) (h𝔟 i))
  rw [← Gen.gramMat_eq_nrdGram, latConst_nrdGram_one hdef] at hlat
  have hcov : LatCovol.covol (coordMat f) (fun i => Gen.idealUnit (𝔟 i) (h𝔟 i)) =
      |((Algebra.norm ℚ (coordMat f).det : ℚ) : ℝ)| * ∏ i, (Ideal.absNorm (𝔟 i) : ℝ) := by
    unfold LatCovol.covol
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [idealNorm, Gen.coe_idealUnit, FractionalIdeal.coeIdeal_absNorm]
    push_cast; rfl
  rw [hcov] at hlat
  -- the final arithmetic
  set C := |((Algebra.norm ℚ (coordMat f).det : ℚ) : ℝ)| * ∏ i, (Ideal.absNorm (𝔟 i) : ℝ) with hC
  set x := algebraMap (𝓞 F) F a * algebraMap (𝓞 F) F b with hx
  have hx0 : x ≠ 0 := mul_ne_zero ((map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr ha)
    ((map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hb)
  set Nab := |((Algebra.norm ℚ x : ℚ) : ℝ)| with hNab
  have hNab0 : 0 < Nab := abs_pos.2 (by exact_mod_cast (Algebra.norm_ne_zero_iff).2 hx0)
  have hdet0 : (coordMat f).det ≠ 0 := det_coordMat_ne_zero hli
  have hC0 : 0 < C := mul_pos (abs_pos.2 (by exact_mod_cast (Algebra.norm_ne_zero_iff).2 hdet0))
    (Finset.prod_pos fun i _ => by
      have : Ideal.absNorm (𝔟 i) ≠ 0 := fun h => h𝔟 i (Ideal.absNorm_eq_zero_iff.1 h)
      exact_mod_cast Nat.pos_of_ne_zero this)
  have hd : (0 : ℝ) < NumberField.discr F := AdditiveZeta.discr_pos
  set d : ℝ := (NumberField.discr F : ℝ) with hddef
  have hlat' : AdditiveZeta.latConst (gramMat f) (fun i => Gen.idealUnit (𝔟 i) (h𝔟 i)) = (Nab * d ^ 2)⁻¹ / C := by
    rw [eq_div_iff hC0.ne']; exact hlat
  rw [hlat']
  have hDH : |((Algebra.norm ℚ (detHalf (pureFormO a b)) : ℚ) : ℝ)| = Nab ^ 2 := by
    rw [detHalf_pureFormO, show (algebraMap (𝓞 F) F a) ^ 2 * (algebraMap (𝓞 F) F b) ^ 2 = x ^ 2 by rw [hx]; ring,
      map_pow]
    push_cast
    rw [abs_pow]
  have h8 : Algebra.norm ℚ (8 : F) = 8 ^ Module.finrank ℚ F := by
    rw [show (8 : F) = algebraMap ℚ F 8 by simp, Algebra.norm_algebraMap]
  rw [hDH, h8, abs_of_pos hd, HilbertModular.card_infinitePlace]
  set n := Module.finrank ℚ F
  have hZ : 0 < dedekindZetaR F 2 := lt_of_lt_of_le one_pos (one_le_dedekindZetaR (by norm_num))
  have hR : 0 < ∏ v ∈ ramFin ha hb, (1 - (normP v : ℝ) ^ (-(1 : ℝ))) := Finset.prod_pos fun v _ => by
    have h1 : (1 : ℝ) < normP v := by exact_mod_cast lt_of_lt_of_le (by norm_num) (two_le_normP v)
    have := Real.rpow_lt_one_of_one_lt_of_neg h1 (by norm_num : (-(1 : ℝ)) < 0)
    linarith
  have hdd : d ^ (-(((3 : ℕ) : ℝ) * (((3 : ℕ) : ℝ) - 1) / 4)) = (d ^ (3 / 2 : ℝ))⁻¹ := by
    rw [← Real.rpow_neg hd.le]; norm_num
  have h32 : d ^ (3 / 2 : ℝ) = d * d ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_one_add' hd.le (by norm_num)]; norm_num
  have hs : 0 < d ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hd _
  have hs2 : (d ^ (1 / 2 : ℝ)) ^ 2 = d := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hd.le]; norm_num
  rw [hdd, h32]
  push_cast
  rw [abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
  have hπ : 0 < π := Real.pi_pos
  have h2R : (0 : ℝ) < 2 ^ (ramFin ha hb).card := by positivity
  field_simp
  have h88 : (1 / 8 : ℝ) ^ n * 8 ^ n = 1 := by rw [← mul_pow]; norm_num
  linear_combination (π ^ (n * 2) * (d ^ (1 / 2 : ℝ)) ^ 2) * h88 + π ^ (n * 2) * hs2 -
    (π ^ (n * 2) * (1 + (1 / 8 : ℝ) ^ n * 8 ^ n)) * hs2

/-- **`TernaryTamagawaTwo F` for every totally real field, any class number, unconditionally:** every totally positive definite
ternary form over $\mathcal O_F$ has $\tau(SO) = 2$. Route: `ternaryTamagawaTwo_of_orders_nf` with a maximal order
$\mathcal O \supseteq \mathcal O_F\langle1,i,j,k\rangle$ and `tauSOLat_pureLat_eq_two`. -/
@[kb "weil1982" "§3.7(a), Thm. 3.7.1 (m = 3), p. 62-65; every class number"]
theorem ternaryTamagawaTwo_nf : TernaryTamagawaTwo F :=
  ternaryTamagawaTwo_of_orders_nf fun a b ha hb hpd => by
    have h2ab : algebraMap (𝓞 F) F (2 * a * b) ≠ 0 :=
      (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr (mul_ne_zero (mul_ne_zero two_ne_zero ha) hb)
    obtain ⟨O, hO, hstd⟩ := exists_isMaximalOrder_ge_stdOrder (R := 𝓞 F) (K := F) h2ab
    exact ⟨O, hO.1, tauSOLat_pureLat_eq_two ha hb hpd hO hstd⟩

end QuadFormsKB.QuatOrder

/-! ### Corollaries over $F$ for every class number -/

namespace QuadFormsKB.Tamagawa

open QuadFormsKB.Lattices QuadFormsKB.HilbertModular QuadFormsKB.QuatOrder NumberField

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/-- **$\tau(SO(Q_0)) = 2$ for every totally positive definite ternary form over every totally real field** (any class number). -/
@[kb "weil1982" "Thm. 3.7.1 (m = 3), p. 65; every class number"]
theorem tamagawaNumberTwo_ternary_nf (Q₀ : QuadForm (𝓞 F) 3) (hpd : IsTotallyPosDef (formF Q₀)) : TamagawaNumberTwo Q₀ :=
  ternaryTamagawaTwo_nf.tau_eq_two Q₀ (nondegenerate_of_map hpd.nondegenerate) hpd (LatChange.isIntegral_std Q₀)

/-- **The mass formula for the genus of an arbitrary ternary lattice** (any Steinitz class, every totally real field):
$\mathrm{Mass}(L) = \mu_{\mathrm{Tam}}(K_{SO}(L))^{-1}$. -/
@[kb "kitaoka1993" "Thm 6.8.1 (mass formula), arbitrary lattice, rank 3, every class number [unverified]"]
theorem massFormula_lat_ternary_nf (Q₀ : QuadForm (𝓞 F) 3) (hpd : IsTotallyPosDef (formF Q₀)) (L : Lat F 3)
    (hLi : IsIntegral (formF Q₀) L.1) : mass (formF Q₀) L = (LatChange.tamagawaKLat Q₀ L)⁻¹ :=
  LatChange.massFormula_lat_nf Q₀ (nondegenerate_of_map hpd.nondegenerate) (by norm_num) hpd
    (tamagawaNumberTwo_ternary_nf Q₀ hpd) L hLi

/-- **`QuaternaryTamagawaTwo F` for every totally real field**, given rank-4 Siegel for the number $1$ (`RankFourUnitSiegel F`). -/
@[kb "weil1982" "Thm. 3.7.1 (m = 4), p. 65; every class number, given rank-4 Siegel for m = 1"]
theorem quaternaryTamagawaTwo_nf (hS : RankFourUnitSiegel F) : QuaternaryTamagawaTwo F :=
  quaternaryTamagawaTwo_of_ternary_nf ternaryTamagawaTwo_nf hS

/-- **$\tau = 2$ in every rank $N \ge 4$ over every totally real field**, given `RankFourUnitSiegel F`. -/
@[kb "weil1982" "Thm. 3.7.1, Thm. 4.5.1, p. 109; every class number, given rank-4 Siegel for m = 1"]
theorem tamagawaNumberTwo_all_ranks_nf (hS : RankFourUnitSiegel F) {N : ℕ} (hN : 4 ≤ N) (Q₀ : QuadForm (𝓞 F) N)
    (hpd : IsTotallyPosDef (formF Q₀)) : TamagawaNumberTwo Q₀ :=
  tamagawaNumberTwo_of_ternary_nf ternaryTamagawaTwo_nf hS hN Q₀ hpd

/-- **The mass formula in every rank $N \ge 4$ over every totally real field**, given `RankFourUnitSiegel F`. -/
@[kb "weil1982" "Thm. 4.5.1, p. 109; mass formula; every class number, given rank-4 Siegel for m = 1"]
theorem massFormula_all_ranks_nf (hS : RankFourUnitSiegel F) {N : ℕ} (hN : 4 ≤ N) (Q₀ : QuadForm (𝓞 F) N)
    (hpd : IsTotallyPosDef (formF Q₀)) : MassFormulaHolds Q₀ :=
  massFormula_of_ternary_nf ternaryTamagawaTwo_nf hS hN Q₀ hpd

/-- **Siegel's formula for numbers in every rank $N \ge 5$ over every totally real field**, given `RankFourUnitSiegel F`. -/
@[kb "weil1982" "§4.5, p. 100; Thm 4.5.1, p. 109; every class number, given rank-4 Siegel for m = 1"]
theorem siegelFormulaAt_all_ranks_nf (hS : RankFourUnitSiegel F) {n : ℕ} (hn : 4 ≤ n) (Q₀ : QuadForm (𝓞 F) (n + 1))
    (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 F} (hm : ∀ v, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    SiegelFormulaAt Q₀ m :=
  siegelFormulaAt_of_ternary_nf ternaryTamagawaTwo_nf hS hn Q₀ hpd hm

/-- **The mass formula for the genus of an arbitrary lattice in every rank $N \ge 4$ over every totally real field** (any Steinitz
class), given `RankFourUnitSiegel F`. -/
@[kb "kitaoka1993" "Thm 6.8.1 (mass formula), arbitrary lattice, every class number, given rank-4 Siegel for m = 1 [unverified]"]
theorem massFormula_lat_all_ranks_nf (hS : RankFourUnitSiegel F) {N : ℕ} (hN : 4 ≤ N) (Q₀ : QuadForm (𝓞 F) N)
    (hpd : IsTotallyPosDef (formF Q₀)) (L : Lat F N) (hLi : IsIntegral (formF Q₀) L.1) :
    mass (formF Q₀) L = (LatChange.tamagawaKLat Q₀ L)⁻¹ :=
  massFormula_lat_of_quaternary_nf (quaternaryTamagawaTwo_nf hS) hN Q₀ hpd L hLi

end QuadFormsKB.Tamagawa
