/-
# The singular series of degree $r$ is the Euler product of the local Whittaker integrals
**Layer:** global over a totally real number field $F$, with the local Whittaker integrals at every finite place (dyadic included).

**Setting.** $Q = \sum_{i<n}b_ix_i^2$ totally positive with $b_i \in \mathcal O_F$, $n = 2m$, $L = \mathcal O_F^n$, $\Phi_v = \mathbf 1_{L_v^r}$; $r \ge 1$,
$m > 4r^2$ (absolute convergence, `summable_norm_fFinR_quot`); $T_0$ a nondegenerate form in $r$ variables over $\mathcal O_F$;
$\operatorname{vol}_v = \operatorname{vol}(\mathcal O_v)^{r(r+1)/2}$ for the self-dual measure (`volR`).

**Main result.** **`singR_hasProd`**: if $\prod_vW_{T,v}/\operatorname{vol}_v$ is multipliable (true for $T_0$ totally positive definite and
$n \ge r + 3$, `multipliable_whittakerR_div`), then
$$\sum_{B\in\mathrm{Sym}_r(F)/\mathrm{Sym}_r(\mathcal O_F)}f_f(w\,n(B), s_0)\,e_T(\sigma(B)) = \prod_{v<\infty}\operatorname{vol}(\mathcal O_v)^{-r(r+1)/2}\,
  W_{T,v}(\mathbf 1_{L_v^r}),$$
$W_{T,v}$ = `whittakerR`, i.e. **Siegel's singular series of degree $r$ is the Euler product of the local Whittaker integrals**
(`whittakerR_eq_NF_localDensityForm`: of the forms-by-forms local densities $\beta_v(Q, T)$, up to the explicit constants).
*Proof.* For $c = (X!)^E$ the truncation is $\prod_v W^{(e_v)}_{T,v}/\operatorname{vol}_v$ (`truncSS_eq_finprod`, `sum_gLocR_eq`); as $E \to \infty$
the factors at $v \mid X!$ reach $W_{T,v}$ (the truncations stabilize, `whittakerTrR_eventually_eq`) and the others are $f_v(w)$, which
is $1$ outside a finite set; as $X \to \infty$ these partial products converge to the Euler product. On the sum side the same double
limit gives the singular series (`tendsto_tsum_denPowR_inner`, `tendsto_tsum_denPowR_outer`).

Sources: Siegel, *Über die analytische Theorie der quadratischen Formen*, Ann. Math. 36 (1935), §§ 3–5 [unverified]; Weil, Acta Math.
113 (1965), Ch. II [unverified]; Kudla, *Some extensions of the Siegel–Weil formula* (2008), §1 ($E_T = \prod_vW_{T,v}$) [unverified].
-/
import QuadFormsKB.SiegelWeil.Forms.SingularSeriesRCRT
import QuadFormsKB.SiegelWeil.Forms.GlobalWhittaker
import QuadFormsKB.SiegelWeil.Forms.DensityProduct

open Matrix NumberField IsDedekindDomain Filter Topology WithZero
open QuadFormsKB.HilbertModular QuadFormsKB.Analysis QuadFormsKB.WeilRep QuadFormsKB.WeilRep.LocalData
  QuadFormsKB.WeilRep.Genus QuadFormsKB.Lattices

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {m r : ℕ}

local notation "ιO" => algebraMap (𝓞 F) F

variable (r) in
/-- $\operatorname{vol}_v = \operatorname{vol}(\mathcal O_v)^{r(r+1)/2}$ (self-dual measure; $= 1$ unless $v \mid \mathfrak d_F$). -/
def volR (v : HeightOneSpectrum (𝓞 F)) : ℂ :=
  (((selfDualV v).real (latticeV v 0) : ℝ) : ℂ) ^ Fintype.card (SymIdx r)

lemma volR_ne_zero (v : HeightOneSpectrum (𝓞 F)) : volR r v ≠ 0 := by
  unfold volR
  refine pow_ne_zero _ ?_
  rw [selfDualV_real_latticeV]
  have hm : (0 : ℝ) < modV v := by exact_mod_cast modV_pos v
  have := (mul_pos (Real.rpow_pos_of_pos hm ((diffExp v : ℝ) / 2)) (zpow_pos hm (0 : ℤ))).ne'
  exact_mod_cast this

/-- The local form $T_v$ of a form over $\mathcal O_F$. -/
abbrev locT (v : HeightOneSpectrum (𝓞 F)) (T₀ : QuadForm (𝓞 F) r) : QuadForm (v.adicCompletion F) r :=
  (T₀.map (algebraMap (𝓞 F) F)).map (algebraMap F (v.adicCompletion F))

lemma locT_eq (v : HeightOneSpectrum (𝓞 F)) (T₀ : QuadForm (𝓞 F) r) :
    locT v T₀ = (LocalDensity.NF.Qp v T₀).map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) := by
  ext i j; rfl

/-- **The local sum is the truncated Whittaker integral**: $\sum_xf_v(w\,n(\tilde x/c))\psi_v(\cdots) = W^{(e_v)}_{T,v}/\operatorname{vol}_v$. -/
lemma sum_gLocR_eq (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (T₀ : QuadForm (𝓞 F) r) (c : 𝓞 F) (hc : c ≠ 0)
    (v : HeightOneSpectrum (𝓞 F)) :
    ∑ x : SymIdx r → 𝓞 F ⧸ v.asIdeal ^ eC c v, gLocR b hb (T₀.map ιO) c v x =
      whittakerTrR v (aV (unitsOfInt b hb) v) (locT v T₀) (eC c v) / volR r v := by
  rw [whittakerTrR_eq_sum v _ (aV_unitsOfInt_le_one b hb v) _ (valued_coeff_map_int v T₀) (resRho c v)
    (resRho_unique v hc) (resRho_le v hc)]
  change _ = volR r v * _ / volR r v
  rw [mul_div_cancel_left₀ _ (volR_ne_zero v)]
  rfl

/-- The truncations reach the Whittaker integral. -/
lemma eventually_whittakerTrR_eq (hrn : r ≤ 2 * m) (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (T₀ : QuadForm (𝓞 F) r)
    (hT₀ : T₀.Nondegenerate) (v : HeightOneSpectrum (𝓞 F)) :
    ∀ᶠ k in atTop, whittakerTrR v (aV (unitsOfInt b hb) v) (locT v T₀) k =
      whittakerR v (aV (unitsOfInt b hb) v) (locT v T₀) := by
  have ha := aV_unitsOfInt_le_one b hb v
  have hT := LocalDensity.NF.nondegenerate_Qp v hT₀
  rw [locT_eq, whittakerR_eq_localDensityForm v _ hrn ha _ hT]
  exact (whittakerTrR_eventually_eq v _ hrn ha _ hT).mono fun k hk => by rw [hk, whittakerConstR]

lemma ordI_top (v : HeightOneSpectrum (𝓞 F)) : SingularNF.ordI v ⊤ = 0 := by
  by_contra h
  have h1 : 1 ≤ SingularNF.ordI v ⊤ := Nat.one_le_iff_ne_zero.mpr h
  have := (SingularNF.pow_dvd_iff_le_ordI v (I := ⊤) (by simp) 1).mpr h1
  rw [pow_one, Ideal.dvd_iff_le, top_le_iff] at this
  exact v.isPrime.ne_top this

lemma eC_one (v : HeightOneSpectrum (𝓞 F)) : eC (1 : 𝓞 F) v = 0 := by
  rw [eC, Ideal.span_singleton_one]; exact ordI_top v

/-- The factor $W^{(0)}_{T,v}/\operatorname{vol}_v = f_v(w)$ at level $0$. -/
lemma whittakerTrR_zero_div (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (T₀ : QuadForm (𝓞 F) r)
    (v : HeightOneSpectrum (𝓞 F)) :
    whittakerTrR v (aV (unitsOfInt b hb) v) (locT v T₀) 0 / volR r v =
      wfunR v (aV (unitsOfInt b hb) v) (locU v (0 : SymIdx r → F)) := by
  have h1 : (1 : 𝓞 F) ≠ 0 := one_ne_zero
  have he : eC (1 : 𝓞 F) v = 0 := eC_one v
  have e := sum_gLocR_eq b hb T₀ 1 h1 v
  conv_lhs => rw [show (0 : ℕ) = eC (1 : 𝓞 F) v from he.symm]
  rw [← e]
  have : Subsingleton (𝓞 F ⧸ v.asIdeal ^ eC (1 : 𝓞 F) v) :=
    Ideal.Quotient.subsingleton_iff.mpr (by rw [he, pow_zero, Ideal.one_eq_top])
  rw [Finset.sum_eq_single (0 : SymIdx r → 𝓞 F ⧸ v.asIdeal ^ eC (1 : 𝓞 F) v)
    (fun y _ hy => absurd (Subsingleton.elim y 0) hy) (fun h0 => absurd (Finset.mem_univ _) h0)]
  exact gLocR_of_eC_eq_zero b hb T₀ 1 h1 v he _

lemma eC_pow (c : 𝓞 F) (hc : c ≠ 0) (v : HeightOneSpectrum (𝓞 F)) (E : ℕ) : eC (c ^ E) v = E * eC c v := by
  induction E with
  | zero =>
    rw [pow_zero, eC_one, zero_mul]
  | succ E ih =>
    rw [pow_succ, eC, ← Ideal.span_singleton_mul_span_singleton,
      SingularNF.ordI_mul v (SingularNF.span_ne_bot (pow_ne_zero E hc)) (SingularNF.span_ne_bot hc)]
    rw [eC] at ih; rw [ih, eC]; ring

lemma mem_TX_iff_eC_ne_zero (X : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    v ∈ SingularNF.TX F X ↔ eC (SingularNF.cX F X) v ≠ 0 := by
  rw [SingularNF.TX, SingularNF.mem_suppI, eC,
    SingularNF.ordI_ne_zero_iff (SingularNF.span_ne_bot (SingularNF.cX_ne_zero X))]

open Classical in
/-- **Siegel's singular series of degree $r$ is the Euler product of the local Whittaker integrals** ($F$ totally real,
$Q = \sum_ib_ix_i^2$ totally positive over $\mathcal O_F$, $n = 2m$, $r \ge 1$, $m > 4r^2$, $T_0$ nondegenerate over $\mathcal O_F$, the Euler
product multipliable):
$$\sum_{B\in\mathrm{Sym}_r(F)/\mathrm{Sym}_r(\mathcal O_F)}f_f(w\,n(B), s_0)\,e_T(\sigma(B)) = \prod_{v<\infty}\frac{W_{T,v}(\mathbf 1_{L_v^r})}
  {\operatorname{vol}(\mathcal O_v)^{r(r+1)/2}}.$$ -/
@[kb "siegel1935" "§§ 3–5 (the singular series is the product of the local densities) [unverified]; kudla2008 §1 ($E_T = \\prod_vW_{T,v}$) [unverified]"]
theorem singR_hasProd (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (hbpos : ∀ i v, 0 < realEmb F v (algebraMap (𝓞 F) F (b i))) (hr : 1 ≤ r) (hm : 4 * (r : ℝ) ^ 2 < m)
    (hrn : r ≤ 2 * m) (T₀ : QuadForm (𝓞 F) r) (hT₀ : T₀.Nondegenerate)
    (hmult : Multipliable fun v => whittakerR v (aV (unitsOfInt b hb) v) (locT v T₀) / volR r v) :
    HasProd (fun v => whittakerR v (aV (unitsOfInt b hb) v) (locT v T₀) / volR r v) (singR b hb (T₀.map ιO)) := by
  set A : HeightOneSpectrum (𝓞 F) → ℂ := fun v => whittakerR v (aV (unitsOfInt b hb) v) (locT v T₀) / volR r v
  obtain ⟨P, hP⟩ := hmult
  set T := T₀.map ιO
  have hTint : IsIntMat T.coeff := fun i j => ⟨T₀.coeff i j, rfl⟩
  set f := ssTermR b hb T
  have hsum := summable_norm_ssTermR b hb hbpos hr hm T
  set κ : HeightOneSpectrum (𝓞 F) → ℂ := fun v => wfunR v (aV (unitsOfInt b hb) v) (locU v (0 : SymIdx r → F))
  have hκ : (Function.mulSupport κ).Finite := hasFiniteMulSupport_wfunR b hb (0 : SymIdx r → F)
  set B : ℕ → HeightOneSpectrum (𝓞 F) → ℂ := fun X v => if v ∈ SingularNF.TX F X then A v else κ v
  -- the inner limit ($E \to \infty$)
  have hinner : ∀ X, (∑' q, if DenPowR X q then f q else 0) = ∏ᶠ v, B X v := by
    intro X
    have hcX := SingularNF.cX_ne_zero (F := F) X
    have h1 := tendsto_tsum_denPowR_inner hsum X
    have h2 : ∀ E : ℕ, (∑' q, if DenDvdR (SingularNF.cX F X ^ E) q then f q else 0) =
        ∏ᶠ v, whittakerTrR v (aV (unitsOfInt b hb) v) (locT v T₀) (E * eC (SingularNF.cX F X) v) / volR r v := by
      intro E
      have hc : SingularNF.cX F X ^ E ≠ 0 := pow_ne_zero _ hcX
      let _ : Fintype (𝓞 F ⧸ Ideal.span {SingularNF.cX F X ^ E}) :=
        @Fintype.ofFinite _ (SingularNF.finite_quot_span hc)
      rw [← sum_uOf_eq_tsum b hb T hTint _ hc, truncSS_eq_finprod b hb T₀ _ hc]
      congr 1; funext v
      rw [sum_gLocR_eq b hb T₀ _ hc v, eC_pow _ hcX]
    have hev : ∀ v ∈ SingularNF.TX F X, ∀ᶠ E : ℕ in atTop,
        whittakerTrR v (aV (unitsOfInt b hb) v) (locT v T₀) (E * eC (SingularNF.cX F X) v) =
          whittakerR v (aV (unitsOfInt b hb) v) (locT v T₀) := by
      intro v hv
      have hpos : 1 ≤ eC (SingularNF.cX F X) v := Nat.one_le_iff_ne_zero.mpr ((mem_TX_iff_eC_ne_zero X v).mp hv)
      have ht : Tendsto (fun E : ℕ => E * eC (SingularNF.cX F X) v) atTop atTop :=
        tendsto_atTop_mono (fun E => Nat.le_mul_of_pos_right E hpos) tendsto_id
      exact ht.eventually (eventually_whittakerTrR_eq hrn b hb T₀ hT₀ v)
    have h3 : ∀ᶠ E : ℕ in atTop, (∏ᶠ v, whittakerTrR v (aV (unitsOfInt b hb) v) (locT v T₀)
        (E * eC (SingularNF.cX F X) v) / volR r v) = ∏ᶠ v, B X v := by
      filter_upwards [(Filter.eventually_all_finset _).mpr hev] with E hE
      congr 1; funext v
      by_cases hv : v ∈ SingularNF.TX F X
      · simp only [B, if_pos hv, A]; rw [hE v hv]
      · have he : eC (SingularNF.cX F X) v = 0 := by
          by_contra h; exact hv ((mem_TX_iff_eC_ne_zero X v).mpr h)
        simp only [B, if_neg hv, he, mul_zero, κ]
        exact whittakerTrR_zero_div b hb T₀ v
    have h4 : Tendsto (fun E : ℕ => ∑' q, if DenDvdR (SingularNF.cX F X ^ E) q then f q else 0) atTop
        (𝓝 (∏ᶠ v, B X v)) := by
      simp_rw [h2]
      exact tendsto_const_nhds.congr' (h3.mono fun E hE => hE.symm)
    exact tendsto_nhds_unique h1 h4
  -- the outer limit ($X \to \infty$)
  have hout : Tendsto (fun X => ∏ᶠ v, B X v) atTop (𝓝 (∑' q, f q)) :=
    (tendsto_tsum_denPowR_outer hsum).congr hinner
  have hlim : Tendsto (fun X => ∏ᶠ v, B X v) atTop (𝓝 P) := by
    have hK : ∀ᶠ X in atTop, hκ.toFinset ⊆ SingularNF.TX F X :=
      SingularNF.tendsto_TX.eventually (eventually_ge_atTop _)
    have hP' : Tendsto (fun X => ∏ v ∈ SingularNF.TX F X, A v) atTop (𝓝 P) :=
      (show Tendsto (fun s : Finset (HeightOneSpectrum (𝓞 F)) => ∏ v ∈ s, A v) atTop (𝓝 P) from hP).comp
        SingularNF.tendsto_TX
    refine hP'.congr' ?_
    filter_upwards [hK] with X hX
    rw [finprod_eq_prod_of_mulSupport_subset (s := SingularNF.TX F X) (B X) (fun v hv => ?_)]
    · exact Finset.prod_congr rfl fun v hv => by simp only [B, if_pos hv]
    · by_contra h
      apply hv
      show B X v = 1
      rw [show B X v = κ v from if_neg h]
      by_contra h'
      exact h (hX (hκ.mem_toFinset.mpr h'))
  have hS : singR b hb T = P := tendsto_nhds_unique hout hlim
  rw [hS]
  exact hP

/-- **The Euler product is multipliable** for $T_0$ totally positive definite and $n \ge r + 3$ (`multipliable_localDensityForm`,
`hasProd_whittakerR`; the volume factors are $1$ outside the ramified places). -/
theorem multipliable_whittakerR_div (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hr : 1 ≤ r) (hrN : r + 3 ≤ 2 * m)
    (hpd : IsTotallyPosDef ((QuadForm.diag b).map (algebraMap (𝓞 F) F))) (T₀ : QuadForm (𝓞 F) r)
    (hT₀ : T₀.Nondegenerate) (hpdT : IsTotallyPosDef (T₀.map (algebraMap (𝓞 F) F))) :
    Multipliable fun v => whittakerR v (aV (unitsOfInt b hb) v) (locT v T₀) / volR r v := by
  obtain ⟨P, hP⟩ := multipliable_localDensityForm (QuadForm.diag b) T₀ hr hrN hpd hpdT
  have hW := hasProd_whittakerR r (by omega) b hb T₀ hT₀ hP
  have hvol : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => (volR r v)⁻¹ :=
    (hasFiniteMulSupport_vol (F := F)).subset fun v hv h' => hv (by simp only at h' ⊢; simp [volR, h'])
  have hV : Multipliable fun v : HeightOneSpectrum (𝓞 F) => (volR r v)⁻¹ := multipliable_of_hasFiniteMulSupport hvol
  refine (hW.multipliable.mul hV).congr fun v => ?_
  simp only [div_eq_mul_inv, ← aOfInt_eq_aV, locT_eq]

/-- **The $T$-th Fourier coefficient of the big-cell part of $E(g_Z, s_0)$ as an Euler product** ($F$ totally real,
$Q = \sum_ib_ix_i^2$ totally positive definite over $\mathcal O_F$, $n = 2m$, $r \ge 1$, $m > 4r^2$, $T_0$ totally positive definite over
$\mathcal O_F$, $Y_w$ positive definite):
$$\int_{(0,1]^J}E_{\mathrm{big}}(X(t) + iY)\,e_T(-X(t))\,dt = \Big(\int_{\mathbb R^J}g_\infty(X(t)+iY)\,e_T(-X(t))\,dt\Big)\cdot
  \prod_{v<\infty}\frac{W_{T,v}(\mathbf 1_{L_v^r})}{\operatorname{vol}(\mathcal O_v)^{r(r+1)/2}},$$
the product converging (`HasProd`): the unfolding `coeffR_eisBigR` and the Euler product of the singular series `singR_hasProd`. -/
@[kb "weil1965" "Ch. II (Fourier coefficients of the Siegel Eisenstein series as products of local Whittaker integrals) [unverified]; kudla2008 §1 [unverified]"]
theorem coeffR_eisBigR_eq_euler (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (hbpos : ∀ i v, 0 < realEmb F v (algebraMap (𝓞 F) F (b i))) (hr : 1 ≤ r) (hm : 4 * (r : ℝ) ^ 2 < m)
    (hpd : IsTotallyPosDef ((QuadForm.diag b).map (algebraMap (𝓞 F) F))) (T₀ : QuadForm (𝓞 F) r)
    (hT₀ : T₀.Nondegenerate) (hpdT : IsTotallyPosDef (T₀.map (algebraMap (𝓞 F) F)))
    {Y : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ} (hY : ∀ w, (Y w).PosDef) :
    HasProd (fun v => whittakerR v (aV (unitsOfInt b hb) v) (locT v T₀) / volR r v) (singR b hb (T₀.map ιO)) ∧
      coeffR (eisBigR b hb) (T₀.map ιO) Y = archIntR m (T₀.map ιO) Y * singR b hb (T₀.map ιO) := by
  have hr4 : (r : ℝ) + 3 ≤ 4 * (r : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    nlinarith
  have hrN : r + 3 ≤ 2 * m := by
    have : ((r + 3 : ℕ) : ℝ) < 2 * m := by push_cast; linarith
    exact_mod_cast this.le
  refine ⟨singR_hasProd b hb hbpos hr hm (by omega) T₀ hT₀
    (multipliable_whittakerR_div b hb hr hrN hpd T₀ hT₀ hpdT), ?_⟩
  exact coeffR_eisBigR b hb hbpos hr hm hY _ fun i j => ⟨T₀.coeff i j, rfl⟩

end QuadFormsKB.SiegelWeil.Forms
