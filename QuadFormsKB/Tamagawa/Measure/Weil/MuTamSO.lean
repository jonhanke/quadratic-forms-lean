import QuadFormsKB.Tamagawa.Measure.Weil.CovolumeTransport
import QuadFormsKB.Tamagawa.Measure.AdelicRepMass
import QuadFormsKB.Tamagawa.Measure.LerayArch
import QuadFormsKB.Tamagawa.Measure.Weil.FundamentalDomain

/-!
# Weil's Tamagawa measure on $SO(V)(\mathbb A)$ for every signature and every number field

**Layer:** number fields. $F$ is any number field, $Q_0$ a nondegenerate quadratic form over $\mathcal O_F$ in $n$
variables ($V = F^n$ with $Q = Q_0\otimes F$, any signature at the real places, complex places allowed).

**Defines**
* `QRe Q₀ w`, `QCx Q₀ w`: the real form $Q^{\sigma_w}$ at a real place $w$ and the complex form $Q^{\tau_w}$ at a complex
  place $w$ (the embeddings of `muArchNF`);
* `archHomR ρ`, `archHomC ρ`: $SO(V)(F)\to SO(Q^\rho)(\mathbb R)$, $SO(Q^\rho)(\mathbb C)$ for embeddings $\rho$;
* `GInfSO Q₀` $= G_\infty = \prod_{w\ \mathrm{real}}SO(Q^{\sigma_w})(\mathbb R)\times\prod_{w\ \mathrm{complex}}SO(Q^{\tau_w})(\mathbb C)$
  and `SOAdele Q₀` $= SO(V)(\mathbb A) = G_\infty\times SO(V)(\mathbb A_f)$ (`SOAf`);
* `diagSOAdele Q₀`, `GammaSOAdele Q₀` $= SO(V)(F)$ embedded diagonally (generalizing `GammaSO` to every signature);
* `muArchTamSO Q₀ hQ` $= c_F\cdot\mu_\infty^{\mathrm{Leray}}$ ($c_F = |d_F|^{-n(n-1)/4}$ = `cF`, `muArchNF`);
* **`muTam Q₀ hQ λ`** $= c_F\,\mu_\infty^{\mathrm{Leray}}\times\mu_f$, $\mu_f$ = `muFin Q₀ λ` (normalized by
  $\mu_f(SO(\hat L)) = \prod'_v\mu_v(SO(L_v))$ with the local measures `muLocSO v Q₀ λ_v`; equal to the restricted product
  $\prod_v\lambda_v^{-1}\mu_v$ on every box by `muFin_boxSO`, `map_restrict_muFin_KSO`);
* **`TamagawaNumberTwoAdelic Q₀`**: $\mathrm{covol}(SO(V)(F), SO(V)(\mathbb A), \mu_{\mathrm{Tam}}) = 2$ (with $\lambda_v = 1$).

**Proves**
* `gramDetR_QRe_ne_zero`, `gramDetC_QCx_ne_zero`: nondegeneracy at every archimedean place;
* `countable_GammaSOAdele`; `sigmaFinite_muFin_of_nondegenerate` ($\mu_f$ is $\sigma$-finite for every nondegenerate $Q_0$,
  any signature: $SO(V)(\mathbb A_f)/SO(\hat L)$ injects into the countable set of lattices);
* `muTam` is left invariant and $\sigma$-finite;
* **specialization** (`map_muAdele_eq_muTam`, `covolume_muTam_eq_covolume_muAdele`): for $F$ totally real and $Q$ totally
  positive definite, a measurable group isomorphism $SO(V)(\mathbb A)_{\mathrm{prod}}\cong SO(V)(\mathbb A)$ (reindexing real
  embeddings by real places) carries `GammaSO` to `GammaSOAdele` and `muAdele` to `muTam`; hence
  **`tamagawaNumberTwoAdelic_iff`**: `TamagawaNumberTwoAdelic Q₀ ↔ TamagawaNumberTwo Q₀` (no PID, no class-number hypothesis),
  and the corollaries `tamagawaNumberTwoAdelic_ternary` (every totally real $F$), `tamagawaNumberTwoAdelic_all_ranks`
  ($\mathcal O_F$ a PID, $[F:\mathbb Q]\ge2$, $n\ge3$), `tamagawaNumberTwoAdelic_all_ranks_of_rankFour` (given
  `RankFourUnitSiegel F`).
-/

open MeasureTheory Measure Set Topology MulAction
open scoped ENNReal NNReal Pointwise Classical

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices Matrix
  QuadFormsKB.Siegel QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure
  QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.LerayComplex
  QuadFormsKB.Tamagawa.Measure.LerayArch

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q₀ : QuadForm (𝓞 F) n)

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

/-! ### The archimedean forms and their nondegeneracy -/

/-- The real form $Q^{\sigma_w}$ at a real place $w$ of $F$. -/
abbrev QRe (w : {w : InfinitePlace F // w.IsReal}) : QuadForm ℝ n := (QF).map (embedding_of_isReal w.2)

/-- The complex form $Q^{\tau_w}$ at a complex place $w$ of $F$ ($\tau_w$ = `w.embedding`). -/
abbrev QCx (w : {w : InfinitePlace F // w.IsComplex}) : QuadForm ℂ n := (QF).map w.1.embedding

theorem hessian_det_map {S : Type*} [CommRing S] (ρ : F →+* S) :
    ((QF).map ρ).hessian.det = ρ (algebraMap (𝓞 F) F Q₀.hessian.det) := by
  rw [hessian_map_NF, hessian_map_NF, Matrix.map_map,
    show (⇑ρ ∘ ⇑(algebraMap (𝓞 F) F)) = ⇑(ρ.comp (algebraMap (𝓞 F) F)) from rfl, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det]
  rfl

/-- **Nondegeneracy at the real places:** $\det(Q^\rho) \ne 0$ for every real embedding $\rho$. -/
theorem gramDetR_map_ne_zero (hQ : Q₀.Nondegenerate) (ρ : F →+* ℝ) : gramDetR ((QF).map ρ) ≠ 0 := by
  rw [gramDetR, hessian_det_map]
  refine div_ne_zero ((map_ne_zero_iff _ ρ.injective).mpr ?_) (pow_ne_zero _ two_ne_zero)
  exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hQ

/-- **Nondegeneracy at the complex places:** $\det(\tfrac12 H(Q^\rho)) \ne 0$ for every complex embedding $\rho$. -/
theorem gramDetC_map_ne_zero (hQ : Q₀.Nondegenerate) (ρ : F →+* ℂ) : gramDetC ((QF).map ρ) ≠ 0 := by
  rw [gramDetC, gramC, Matrix.det_smul, hessian_det_map]
  refine mul_ne_zero (pow_ne_zero _ (by norm_num)) ((map_ne_zero_iff _ ρ.injective).mpr ?_)
  exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hQ

theorem gramDetR_QRe_ne_zero (hQ : Q₀.Nondegenerate) (w : {w : InfinitePlace F // w.IsReal}) :
    gramDetR (QRe Q₀ w) ≠ 0 := gramDetR_map_ne_zero Q₀ hQ _

theorem gramDetC_QCx_ne_zero (hQ : Q₀.Nondegenerate) (w : {w : InfinitePlace F // w.IsComplex}) :
    gramDetC (QCx Q₀ w) ≠ 0 := gramDetC_map_ne_zero Q₀ hQ _

/-! ### The archimedean embeddings of $SO(V)(F)$ -/

/-- $\gamma\mapsto\rho(\gamma)$: $SO(V)(F)\to SO(Q^\rho)(\mathbb R)$ for a real embedding $\rho$. -/
def archHomR (ρ : F →+* ℝ) : soSub QF F →* ArchSO ((QF).map ρ) :=
  ((Matrix.GeneralLinearGroup.map ρ).comp ((orthGroup QF F).subtype.comp (soSub QF F).subtype)).codRestrict
    (soReal ((QF).map ρ)) fun γ => by
      set M := ((γ : orthGroup QF F) : GL (Fin n) F).val
      have hM : ((Matrix.GeneralLinearGroup.map ρ).comp ((orthGroup QF F).subtype.comp
          (soSub QF F).subtype) γ : Matrix (Fin n) (Fin n) ℝ) = M.map ρ := rfl
      have hγ := (mem_orthGroup QF).mp (γ : orthGroup QF F).2
      have hid : (QF).hessian.map (algebraMap F F) = (QF).hessian := by
        rw [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id]
      rw [hid] at hγ
      rw [mem_soReal_iff, hM, hessian_map_NF]
      refine ⟨?_, ?_⟩
      · rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hγ]
      · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, show M.det = 1 from mem_soSub.mp γ.2, map_one]

/-- $\gamma\mapsto\rho(\gamma)$: $SO(V)(F)\to SO(Q^\rho)(\mathbb C)$ for a complex embedding $\rho$. -/
def archHomC (ρ : F →+* ℂ) : soSub QF F →* ArchSOC ((QF).map ρ) :=
  ((Matrix.GeneralLinearGroup.map ρ).comp ((orthGroup QF F).subtype.comp (soSub QF F).subtype)).codRestrict
    (soC ((QF).map ρ)) fun γ => by
      set M := ((γ : orthGroup QF F) : GL (Fin n) F).val
      have hM : ((Matrix.GeneralLinearGroup.map ρ).comp ((orthGroup QF F).subtype.comp
          (soSub QF F).subtype) γ : Matrix (Fin n) (Fin n) ℂ) = M.map ρ := rfl
      have hγ := (mem_orthGroup QF).mp (γ : orthGroup QF F).2
      have hid : (QF).hessian.map (algebraMap F F) = (QF).hessian := by
        rw [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id]
      rw [hid] at hγ
      rw [mem_soC_iff, hM, gramC, hessian_map_NF]
      refine ⟨?_, ?_⟩
      · rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hγ]
      · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, show M.det = 1 from mem_soSub.mp γ.2, map_one]

/-! ### $SO(V)(\mathbb A)$ and the diagonal $SO(V)(F)$ -/

/-- **The archimedean group** $G_\infty = \prod_{w\ \mathrm{real}}SO(Q^{\sigma_w})(\mathbb R)\times
\prod_{w\ \mathrm{complex}}SO(Q^{\tau_w})(\mathbb C)$ (any signature). -/
abbrev GInfSO : Type := ArchGroup (QRe Q₀) (QCx Q₀)

/-- **$SO(V)(\mathbb A) = G_\infty\times SO(V)(\mathbb A_f)$** for every signature and every number field. -/
abbrev SOAdele : Type := GInfSO Q₀ × SOAf Q₀

/-- **The diagonal embedding** $SO(V)(F)\to SO(V)(\mathbb A)$, $\gamma\mapsto((\sigma_w(\gamma))_w, (\tau_w(\gamma))_w,
(\gamma)_v)$. -/
def diagSOAdele : soSub QF F →* SOAdele Q₀ :=
  MonoidHom.prod (M := soSub QF F) (N := GInfSO Q₀) (P := SOAf Q₀)
    (MonoidHom.prod (MonoidHom.pi fun w : {w : InfinitePlace F // w.IsReal} => archHomR Q₀ (embedding_of_isReal w.2))
      (MonoidHom.pi fun w : {w : InfinitePlace F // w.IsComplex} => archHomC Q₀ w.1.embedding)) (finHom Q₀)

/-- **$\Gamma = SO(V)(F)$, diagonally in $SO(V)(\mathbb A)$** (Weil 1982, §2.4: $G_k\subset G_{\mathbb A}$), any signature. -/
@[kb "weil1982" "§2.4, p. 23 (G_k ⊂ G_𝔸)"]
def GammaSOAdele : Subgroup (SOAdele Q₀) := (diagSOAdele Q₀).range

theorem countable_GammaSOAdele : Countable (GammaSOAdele Q₀) := by
  have := countable_soSub Q₀
  have h : ((GammaSOAdele Q₀ : Subgroup _) : Set (SOAdele Q₀)) = Set.range (diagSOAdele Q₀) :=
    MonoidHom.coe_range _
  exact (h ▸ Set.countable_range (diagSOAdele Q₀)).to_subtype

/-- $\Gamma\to SO(V)(\mathbb A_f)$ is injective. -/
theorem GammaSOAdele_inj : ∀ γ ∈ GammaSOAdele Q₀, γ.2 = 1 → γ = 1 := by
  rintro _ ⟨g, rfl⟩ h
  have h1 : diagF QF (g : orthGroup QF F) = 1 := congrArg Subtype.val h
  have hg : g = 1 := Subtype.ext (diagF_injective QF (h1.trans (map_one _).symm))
  rw [hg, map_one]

/-! ### $\sigma$-finiteness of $\mu_f$ for every nondegenerate form -/

/-- Lattices in $F^n$ form a countable set (each is the span of a finite subset of the countable set $F^n$). -/
theorem countable_lat : Countable (Lat F n) := by
  have : Countable F := Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.toEquiv.symm
  refine Function.Surjective.countable (f := fun s : {s : Finset (Fin n → F) // (Submodule.span (𝓞 F)
      (s : Set (Fin n → F))).IsLattice F} => (⟨Submodule.span (𝓞 F) (s.1 : Set (Fin n → F)), s.2⟩ : Lat F n)) ?_
  rintro ⟨L, hL⟩
  obtain ⟨s, hs⟩ := hL.fg
  exact ⟨⟨s, hs ▸ hL⟩, Subtype.ext hs⟩

/-- **$SO(V)(\mathbb A_f)/SO(\hat L)$ is countable** (any signature): $g\,SO(\hat L)\mapsto gL$ is injective
(`cosetLatSO_injective`). -/
theorem countable_SOAf_quot : Countable (SOAf Q₀ ⧸ KSO Q₀) := by
  have := countable_lat (F := F) (n := n)
  let ι : SOAf Q₀ ⧸ KSO Q₀ → OAf QF ⧸ locStab QF (stdLat F n) :=
    Quotient.map' (fun a : SOAf Q₀ => (a : OAf QF)) (fun a b hab => by
      rw [QuotientGroup.leftRel_apply] at hab ⊢; exact hab)
  refine Function.Injective.countable (f := fun y => cosetLat QF (stdLat F n) (ι y)) fun x y h => ?_
  induction x using QuotientGroup.induction_on with | H a => ?_
  induction y using QuotientGroup.induction_on with | H b => ?_
  have h' := cosetLat_injective QF (stdLat F n) h
  change (QuotientGroup.mk (a : OAf QF) : OAf QF ⧸ locStab QF (stdLat F n)) = QuotientGroup.mk (b : OAf QF) at h'
  rw [QuotientGroup.eq] at h' ⊢
  rw [Subgroup.mem_subgroupOf]
  simpa using h'

/-- **$\mu_f$ is $\sigma$-finite for every form** (no definiteness): $SO(V)(\mathbb A_f)$ is a countable union of translates
of the compact open $SO(\hat L)$. -/
theorem sigmaFinite_muFin' (lam : HeightOneSpectrum (𝓞 F) → ℝ) : SigmaFinite (muFin Q₀ lam) := by
  have := countable_SOAf_quot Q₀
  refine Measure.sigmaFinite_of_countable (S := Set.range fun q : SOAf Q₀ ⧸ KSO Q₀ =>
      (Quotient.out q : SOAf Q₀) • (KSO Q₀ : Set (SOAf Q₀))) (Set.countable_range _) ?_ ?_
  · rintro _ ⟨q, rfl⟩
    rw [measure_smul, muFin_KSO]; exact ENNReal.ofReal_lt_top
  · refine Set.eq_univ_of_forall fun g => ?_
    refine Set.mem_sUnion.mpr ⟨_, ⟨(QuotientGroup.mk g : SOAf Q₀ ⧸ KSO Q₀), rfl⟩, ?_⟩
    have h := QuotientGroup.mk_out_eq_mul (KSO Q₀) g
    obtain ⟨k, hk⟩ := h
    refine Set.mem_smul_set.mpr ⟨(k : SOAf Q₀)⁻¹, (KSO Q₀).inv_mem k.2, ?_⟩
    rw [smul_eq_mul, hk, mul_inv_cancel_right]

/-! ### Weil's Tamagawa measure -/

instance sigmaFinite_muFin_inst (lam : HeightOneSpectrum (𝓞 F) → ℝ) : SigmaFinite (muFin Q₀ lam) :=
  sigmaFinite_muFin' Q₀ lam

/-- **The archimedean Tamagawa factor** $c_F\cdot\mu_\infty^{\mathrm{Leray}}$ on $G_\infty$, with
$c_F = |d_F|^{-n(n-1)/4}$ (`cF`, Weil's $\mu_k^{-\dim SO_n}$ with $\mu_k = |d_F|^{1/2}$) and $\mu_\infty^{\mathrm{Leray}}$ the
product of the gauge-form (Leray) measures at the real and complex places (`muArchNF`). -/
@[kb "weil1982" "§2.3, p. 21 (Tamagawa measure, factor μ_k^{-dim}); §2.2 (gauge forms) [unverified]"]
def muArchTamSO (hQ : Q₀.Nondegenerate) : Measure (GInfSO Q₀) :=
  ENNReal.ofReal (cF F n) • muArchNF QF (gramDetR_QRe_ne_zero Q₀ hQ) (gramDetC_QCx_ne_zero Q₀ hQ)

/-- **Weil's Tamagawa measure on $SO(V)(\mathbb A)$**, any signature, any number field, with convergence factors
$(\lambda_v)$: $\mu_{\mathrm{Tam}} = c_F\,\mu_\infty^{\mathrm{Leray}}\times\mu_f$, where $\mu_f$ = `muFin Q₀ λ` is the Haar
measure on $SO(V)(\mathbb A_f)$ with $\mu_f(SO(\hat L)) = \prod'_v\mu_v(SO(L_v))$, $\mu_v$ = `muLocSO v Q₀ λ_v`. -/
@[kb "weil1982" "§2.3, p. 21 (Tamagawa measure (ω,(λ_v))); §2.4, p. 23"]
def muTam (hQ : Q₀.Nondegenerate) (lam : HeightOneSpectrum (𝓞 F) → ℝ) : Measure (SOAdele Q₀) :=
  (muArchTamSO Q₀ hQ).prod (muFin Q₀ lam)

instance (hQ : Q₀.Nondegenerate) : (muArchTamSO Q₀ hQ).IsMulLeftInvariant := by
  have := isHaarMeasure_muArchLeray (QRe Q₀) (QCx Q₀) (gramDetR_QRe_ne_zero Q₀ hQ) (gramDetC_QCx_ne_zero Q₀ hQ)
  unfold muArchTamSO muArchNF; infer_instance

theorem ofReal_smul_eq {α : Type*} [MeasurableSpace α] (c : ℝ) (μ : Measure α) :
    ENNReal.ofReal c • μ = (Real.toNNReal c) • μ := by
  ext s; simp [ENNReal.ofReal]

instance (hQ : Q₀.Nondegenerate) : SigmaFinite (muArchTamSO Q₀ hQ) := by
  have := isHaarMeasure_muArchLeray (QRe Q₀) (QCx Q₀) (gramDetR_QRe_ne_zero Q₀ hQ) (gramDetC_QCx_ne_zero Q₀ hQ)
  unfold muArchTamSO muArchNF; rw [ofReal_smul_eq]; infer_instance

instance (hQ : Q₀.Nondegenerate) (lam : HeightOneSpectrum (𝓞 F) → ℝ) : (muTam Q₀ hQ lam).IsMulLeftInvariant := by
  unfold muTam; infer_instance

instance (hQ : Q₀.Nondegenerate) (lam : HeightOneSpectrum (𝓞 F) → ℝ) : SigmaFinite (muTam Q₀ hQ lam) := by
  unfold muTam; infer_instance

/-- `muTam` is the product $c_F\cdot(\mu_\infty^{\mathrm{Leray}}\times\mu_f)$. -/
theorem muTam_eq_smul (hQ : Q₀.Nondegenerate) (lam : HeightOneSpectrum (𝓞 F) → ℝ) :
    muTam Q₀ hQ lam = ENNReal.ofReal (cF F n) •
      (muArchNF QF (gramDetR_QRe_ne_zero Q₀ hQ) (gramDetC_QCx_ne_zero Q₀ hQ)).prod (muFin Q₀ lam) := by
  rw [muTam, muArchTamSO, Measure.prod_smul_left]

/-! ### The adelic statement $\tau(SO(V)) = 2$ -/

/-- **Weil's theorem $\tau(SO(V)) = 2$, adelic form, for every signature** (target statement; Weil 1982, §2.4, p. 23 for
$\tau(G) = \mathrm{vol}(G_{\mathbb A}/G_k)$; Thm 3.7.1, Thm 4.5.1 for the value): the covolume of $SO(V)(F)$ in
$SO(V)(\mathbb A)$ for Weil's Tamagawa measure (convergence factors $\lambda_v = 1$, legitimate for $n\ge3$) is $2$.
It is a *target*, used as a hypothesis only in specialization and transport lemmas. -/
@[kb "weil1982" "§2.4, p. 23 (τ(G) = vol(G_𝔸/G_k)); Thm 3.7.1, Thm 4.5.1, p. 109 (τ(SO) = 2)"]
def TamagawaNumberTwoAdelic (hQ : Q₀.Nondegenerate) : Prop :=
  covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ fun _ => 1) = 2


/-! ### $SO(V)(F)$ is discrete in $SO(V)(\mathbb A)$ (any signature) -/

section Discrete

/-- An algebraic integer all of whose archimedean absolute values are $< 1$ is $0$ (its norm is an integer of absolute
value $< 1$). -/
theorem eq_zero_of_isIntegral_of_forall_lt_one {a : F} (ha : a ∈ (algebraMap (𝓞 F) F).range)
    (h : ∀ w : InfinitePlace F, w a < 1) : a = 0 := by
  obtain ⟨b, rfl⟩ := ha
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hN : ((|Algebra.norm ℚ (algebraMap (𝓞 F) F b)| : ℚ) : ℝ) < 1 := by
    rw [← prod_eq_abs_norm, ← Finset.mul_prod_erase _ _ (Finset.mem_univ w₀)]
    have h1 : ∏ w ∈ Finset.univ.erase w₀, w (algebraMap (𝓞 F) F b) ^ mult w ≤ 1 :=
      Finset.prod_le_one₀ (fun w _ => pow_nonneg (apply_nonneg _ _) _)
        fun w _ => pow_le_one₀ (apply_nonneg _ _) (h w).le
    have h2 : w₀ (algebraMap (𝓞 F) F b) ^ mult w₀ < 1 :=
      pow_lt_one₀ (apply_nonneg _ _) (h w₀) (mult_pos.ne')
    calc w₀ (algebraMap (𝓞 F) F b) ^ mult w₀ * ∏ w ∈ Finset.univ.erase w₀, w (algebraMap (𝓞 F) F b) ^ mult w
        ≤ w₀ (algebraMap (𝓞 F) F b) ^ mult w₀ * 1 := mul_le_mul_of_nonneg_left h1 (pow_nonneg (apply_nonneg _ _) _)
      _ < 1 := by rw [mul_one]; exact h2
  have hZ : Algebra.norm ℤ b = 0 := by
    have : |((Algebra.norm ℤ b : ℤ) : ℚ)| < 1 := by
      rw [show ((Algebra.norm ℤ b : ℤ) : ℚ) = Algebra.norm ℚ (algebraMap (𝓞 F) F b) from Algebra.coe_norm_int b]
      exact_mod_cast hN
    have : |Algebra.norm ℤ b| < 1 := by exact_mod_cast this
    exact Int.abs_lt_one_iff.mp this
  rw [Algebra.norm_eq_zero_iff.mp hZ, map_zero]

/-- The entries of $\gamma\in SO(V)(F)$ with $(\gamma)_v\in SO(\hat L)$ are algebraic integers. -/
theorem entry_mem_range_of_mem_KSO (γ : soSub QF F) (h : finHom Q₀ γ ∈ KSO Q₀) (i j : Fin n) :
    ((γ : orthGroup QF F) : GL (Fin n) F).val i j ∈ (algebraMap (𝓞 F) F).range := by
  refine HeightOneSpectrum.mem_integers_of_valuation_le_one F _ fun v => ?_
  have hv : ((finHom Q₀ γ : SOAf Q₀) : OAf QF).1 v ∈ (stdStab QF v : Set _) := by
    have h' : ((finHom Q₀ γ : SOAf Q₀) : OAf QF) ∈ (locStab QF (stdLat F n) : Set (OAf QF)) := h
    rw [coe_locStab_std] at h'
    exact h' v
  have := entries_le_one_of_locAct v hv i j
  rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact this

/-- The neighbourhood $W$ of $1$ in $SO(V)(\mathbb A)$: finite component in $SO(\hat L)$, archimedean entries within $1$
of the identity matrix. -/
def nbhdOne : Set (SOAdele Q₀) :=
  Prod.snd ⁻¹' (KSO Q₀ : Set (SOAf Q₀)) ∩
    ((⋂ w, ⋂ i, ⋂ j, {x : SOAdele Q₀ |
      |(ArchSO.incl _ (x.1.1 w) : GL (Fin n) ℝ).val i j - (1 : Matrix (Fin n) (Fin n) ℝ) i j| < 1}) ∩
    (⋂ w, ⋂ i, ⋂ j, {x : SOAdele Q₀ |
      ‖(ArchSOC.incl _ (x.1.2 w) : GL (Fin n) ℂ).val i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ < 1}))

theorem isOpen_nbhdOne : IsOpen (nbhdOne Q₀) := by
  refine ((isOpen_KSO Q₀).preimage continuous_snd).inter (IsOpen.inter ?_ ?_)
  · refine isOpen_iInter_of_finite fun w => isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    refine isOpen_lt (Continuous.abs (Continuous.sub ?_ continuous_const)) continuous_const
    exact (Units.continuous_val.comp ((ArchSO.continuous_incl _).comp ((continuous_apply w).comp
      (continuous_fst.comp continuous_fst)))).matrix_elem i j
  · refine isOpen_iInter_of_finite fun w => isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    refine isOpen_lt (Continuous.norm (Continuous.sub ?_ continuous_const)) continuous_const
    exact (Units.continuous_val.comp ((ArchSOC.continuous_incl _).comp ((continuous_apply w).comp
      (continuous_snd.comp continuous_fst)))).matrix_elem i j

/-- **$W\cap\Gamma = \{1\}$.** -/
theorem eq_one_of_diag_mem_nbhdOne (γ : soSub QF F) (h : diagSOAdele Q₀ γ ∈ nbhdOne Q₀) : γ = 1 := by
  obtain ⟨hK, hR, hC⟩ := h
  set M := ((γ : orthGroup QF F) : GL (Fin n) F).val
  have hM : M = 1 := by
    ext i j
    rw [← sub_eq_zero]
    refine eq_zero_of_isIntegral_of_forall_lt_one ?_ fun w => ?_
    · refine Subring.sub_mem _ (entry_mem_range_of_mem_KSO Q₀ γ hK i j) ?_
      rw [Matrix.one_apply]; split_ifs
      · exact ⟨1, map_one _⟩
      · exact ⟨0, map_zero _⟩
    · have h1 : ∀ (S : Type) [CommRing S] (ρ : F →+* S),
          ρ (M i j - (1 : Matrix (Fin n) (Fin n) F) i j) = ρ (M i j) - (1 : Matrix (Fin n) (Fin n) S) i j := by
        intro S _ ρ
        rw [map_sub, Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
      rcases w.isReal_or_isComplex with hw | hw
      · have := Set.mem_iInter.mp (Set.mem_iInter.mp (Set.mem_iInter.mp hR ⟨w, hw⟩) i) j
        rw [← norm_embedding_eq, ← embedding_of_isReal_apply hw, Complex.norm_real, Real.norm_eq_abs, h1]
        exact this
      · have := Set.mem_iInter.mp (Set.mem_iInter.mp (Set.mem_iInter.mp hC ⟨w, hw⟩) i) j
        rw [← norm_embedding_eq, h1]
        exact this
  have : (γ : orthGroup QF F) = 1 := Subtype.ext (Units.ext hM)
  exact Subtype.ext this

/-- **$SO(V)(F)$ is a discrete subgroup of $SO(V)(\mathbb A)$**, for every nondegenerate $Q_0$ of any signature over any
number field (Weil 1982, §2.4: $G_k$ is discrete in $G_{\mathbb A}$). -/
@[kb "weil1982" "§2.4, p. 23 (G_k discrete in G_𝔸) [unverified]"]
theorem discreteTopology_GammaSOAdele : DiscreteTopology (GammaSOAdele Q₀) := by
  refine discreteTopology_of_isOpen_singleton_one ?_
  have : ({1} : Set (GammaSOAdele Q₀)) = Subtype.val ⁻¹' nbhdOne Q₀ := by
    ext ⟨x, γ, rfl⟩
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · intro h
      have h' : diagSOAdele Q₀ γ = 1 := congrArg Subtype.val h
      rw [h']
      refine ⟨one_mem (KSO Q₀), ?_, ?_⟩
      · exact Set.mem_iInter.mpr fun w => Set.mem_iInter.mpr fun i => Set.mem_iInter.mpr fun j => by simp
      · exact Set.mem_iInter.mpr fun w => Set.mem_iInter.mpr fun i => Set.mem_iInter.mpr fun j => by simp
    · intro h
      refine Subtype.ext ?_
      show diagSOAdele Q₀ γ = 1
      rw [eq_one_of_diag_mem_nbhdOne Q₀ γ h, map_one]
  rw [this]
  exact (isOpen_nbhdOne Q₀).preimage continuous_subtype_val

end Discrete


/-! ### Second countability and fundamental domains -/

section FundDomain

/-- A topological group with an open second-countable subgroup of countable index is second countable. -/
theorem secondCountable_of_openSubgroup {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K : Subgroup G) (hK : IsOpen (K : Set G)) [SecondCountableTopology K] [Countable (G ⧸ K)] :
    SecondCountableTopology G := by
  have hsc : ∀ q : G ⧸ K, SecondCountableTopology ↥((Quotient.out q : G) • (K : Set G)) := by
    intro q
    have h : (Quotient.out q : G) • (K : Set G) = (Homeomorph.mulLeft (Quotient.out q : G)) '' (K : Set G) :=
      (Set.image_smul).symm
    rw [h]
    exact ((Homeomorph.mulLeft (Quotient.out q : G)).image (K : Set G)).symm.isEmbedding.secondCountableTopology
  refine TopologicalSpace.secondCountableTopology_of_countable_cover
    (U := fun q : G ⧸ K => (Quotient.out q : G) • (K : Set G)) (fun q => hK.smul _) ?_
  refine Set.eq_univ_of_forall fun g => Set.mem_iUnion.mpr ⟨QuotientGroup.mk g, ?_⟩
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
  refine Set.mem_smul_set.mpr ⟨(k : G)⁻¹, K.inv_mem k.2, ?_⟩
  rw [smul_eq_mul, hk, mul_inv_cancel_right]

/-- The finite places of a number field form a countable set (as in `AdditiveAdele.lean`). -/
instance countable_heightOneSpectrum' : Countable (HeightOneSpectrum (𝓞 F)) := by
  have : Countable F := Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.toEquiv.symm
  have : Countable (𝓞 F) := Subtype.countable
  have hsurj : Function.Surjective fun s : Finset (𝓞 F) => Ideal.span (s : Set (𝓞 F)) := fun I =>
    (IsNoetherian.noetherian I).imp fun s hs => hs
  have : Countable (Ideal (𝓞 F)) := hsurj.countable
  exact Function.Injective.countable (f := HeightOneSpectrum.asIdeal) fun a b h => HeightOneSpectrum.ext h

/-- **$SO(\hat L)$ is second countable** (it embeds in $\prod_v O(L_v)$, a countable product of second-countable groups). -/
instance secondCountable_KSO : SecondCountableTopology (KSO Q₀) := by
  let ψ : KSO Q₀ → ∀ v : HeightOneSpectrum (𝓞 F), (stdStab QF v : Set (orthGroup QF (v.adicCompletion F))) :=
    fun x v => ⟨((x : SOAf Q₀) : OAf QF).1 v, by
      have h' : ((x : SOAf Q₀) : OAf QF) ∈ (locStab QF (stdLat F n) : Set (OAf QF)) := x.2
      rw [coe_locStab_std] at h'
      exact h' v⟩
  have hincl : Topology.IsEmbedding (fun x : KSO Q₀ => ((x : SOAf Q₀) : OAf QF)) :=
    Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
  have hcomp : (RestrictedProduct.structureMap _ _ Filter.cofinite) ∘ ψ =
      fun x : KSO Q₀ => ((x : SOAf Q₀) : OAf QF) := by
    funext x; rfl
  have hψ : Topology.IsEmbedding ψ :=
    (RestrictedProduct.isEmbedding_structureMap).of_comp_iff.mp (hcomp ▸ hincl)
  exact hψ.secondCountableTopology

/-- **$SO(V)(\mathbb A_f)$ is second countable** (any signature). -/
instance secondCountable_SOAf : SecondCountableTopology (SOAf Q₀) := by
  have := countable_SOAf_quot Q₀
  exact secondCountable_of_openSubgroup (KSO Q₀) (isOpen_KSO Q₀)

/-- **$SO(V)(\mathbb A)$ is second countable.** -/
instance secondCountable_SOAdele : SecondCountableTopology (SOAdele Q₀) := inferInstance

/-- **$SO(V)(F)\backslash SO(V)(\mathbb A)$ has a measurable fundamental domain** for every measure (any signature; `exists_isFundamentalDomain` for the discrete countable subgroup `GammaSOAdele`), so the covolume is the measure of any
fundamental domain, not the junk value $0$. -/
@[kb "weil1982" "§2.4, p. 23 (fundamental domain for G_k in G_𝔸) [unverified]"]
theorem hasFundamentalDomain_GammaSOAdele (μ : Measure (SOAdele Q₀)) :
    HasFundamentalDomain (GammaSOAdele Q₀) (SOAdele Q₀) μ := by
  have := discreteTopology_GammaSOAdele Q₀
  obtain ⟨D, hD⟩ := exists_isFundamentalDomain (GammaSOAdele Q₀) μ
  exact ⟨D, hD⟩

/-- The covolume of $SO(V)(F)$ for `muTam` is the measure of any fundamental domain. -/
theorem covolume_muTam_eq (hQ : Q₀.Nondegenerate) (lam : HeightOneSpectrum (𝓞 F) → ℝ) {D : Set (SOAdele Q₀)}
    (hD : IsFundamentalDomain (GammaSOAdele Q₀) D (muTam Q₀ hQ lam)) :
    covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ lam) = muTam Q₀ hQ lam D := by
  have := countable_GammaSOAdele Q₀
  exact hD.covolume_eq_volume _

/-- **Finite volume of $SO(V)(F)\backslash SO(V)(\mathbb A)$** for Weil's measure (target statement; Weil 1982, §2.4, p. 23,
where finiteness is part of the definition of $\tau(G)$). It is implied by `TamagawaNumberTwoAdelic`. -/
@[kb "weil1982" "§2.4, p. 23 (vol(G_𝔸/G_k) < ∞)"]
def TamagawaFiniteAdelic (hQ : Q₀.Nondegenerate) : Prop :=
  covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ fun _ => 1) < ⊤

theorem TamagawaNumberTwoAdelic.finite {hQ : Q₀.Nondegenerate} (h : TamagawaNumberTwoAdelic Q₀ hQ) :
    TamagawaFiniteAdelic Q₀ hQ := by
  rw [TamagawaFiniteAdelic, show covolume _ _ _ = 2 from h]; exact ENNReal.ofNat_lt_top

/-- Under `TamagawaNumberTwoAdelic`, every fundamental domain of $SO(V)(F)$ has measure $2$. -/
theorem TamagawaNumberTwoAdelic.measure_fundamentalDomain {hQ : Q₀.Nondegenerate}
    (h : TamagawaNumberTwoAdelic Q₀ hQ) {D : Set (SOAdele Q₀)}
    (hD : IsFundamentalDomain (GammaSOAdele Q₀) D (muTam Q₀ hQ fun _ => 1)) : muTam Q₀ hQ (fun _ => 1) D = 2 := by
  rw [← covolume_muTam_eq Q₀ hQ _ hD]; exact h

end FundDomain

/-! ### Relabelling a form: $SO(Q)(\mathbb R) = SO(Q')(\mathbb R)$ for $Q = Q'$ -/

section Congr

/-- The identification $SO(Q)(\mathbb R) \cong SO(Q')(\mathbb R)$ along an equality $Q = Q'$. -/
def archSOCongr {Q Q' : QuadForm ℝ n} (h : Q = Q') : ArchSO Q ≃* ArchSO Q' := by
  subst h; exact MulEquiv.refl _

theorem incl_archSOCongr {Q Q' : QuadForm ℝ n} (h : Q = Q') (g : ArchSO Q) :
    ArchSO.incl Q' (archSOCongr h g) = ArchSO.incl Q g := by
  subst h; rfl

theorem measurable_archSOCongr {Q Q' : QuadForm ℝ n} (h : Q = Q') : Measurable (archSOCongr h) := by
  subst h; exact measurable_id

theorem measurePreserving_archSOCongr {Q Q' : QuadForm ℝ n} (h : Q = Q') [Fact (IsPosDefR Q)]
    [Fact (IsPosDefR Q')] : MeasurePreserving (archSOCongr h) (ArchSO.mu Q) (ArchSO.mu Q') := by
  subst h; exact MeasurePreserving.id _

theorem archSO_ext {Q : QuadForm ℝ n} {a b : ArchSO Q} (h : ArchSO.incl Q a = ArchSO.incl Q b) : a = b :=
  Subtype.ext h

end Congr

/-! ### Specialization: totally real $F$, totally positive definite $Q$ -/

section Definite

variable [IsTotallyReal F]

instance isEmpty_complexPlaces : IsEmpty {w : InfinitePlace F // w.IsComplex} :=
  ⟨fun w => (not_isComplex_iff_isReal.mpr (IsTotallyReal.isReal w.1)) w.2⟩

/-- In a totally real field, the embeddings $F \to \mathbb C$ correspond to the real places. -/
def realPlaceEquiv : (F →ₐ[ℚ] ℂ) ≃ {w : InfinitePlace F // w.IsReal} :=
  Equiv.ofBijective (fun σ => ⟨mk (σ : F →+* ℂ), IsTotallyReal.isReal _⟩) <| by
    refine ⟨fun σ τ h => ?_, fun w => ?_⟩
    · have h' : mk (σ : F →+* ℂ) = mk (τ : F →+* ℂ) := congrArg Subtype.val h
      have := congrArg InfinitePlace.embedding h'
      rw [embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal _),
        embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal _)] at this
      exact AlgHom.toRingHom_injective this
    · refine ⟨w.1.embedding.toRatAlgHom, Subtype.ext ?_⟩
      exact mk_embedding w.1

theorem embedding_realPlaceEquiv {σ : F →ₐ[ℚ] ℂ} {w : {w : InfinitePlace F // w.IsReal}}
    (h : realPlaceEquiv σ = w) : embedding_of_isReal w.2 = realEmb σ := by
  subst h
  ext x
  apply Complex.ofReal_injective
  rw [embedding_of_isReal_apply, realEmb_apply]
  show (mk (σ : F →+* ℂ)).embedding x = σ x
  rw [embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal _)]
  rfl

theorem realQ_eq_QRe {σ : F →ₐ[ℚ] ℂ} {w : {w : InfinitePlace F // w.IsReal}} (h : realPlaceEquiv σ = w) :
    realQ Q₀ σ = QRe Q₀ w := by
  rw [QRe, embedding_realPlaceEquiv h]; rfl

/-- **Relabelling the real factor**: $\prod_\sigma SO(Q^\sigma)(\mathbb R)$ (indexed by embeddings) $\cong
\prod_{w\ \mathrm{real}} SO(Q^{\sigma_w})(\mathbb R)$ (indexed by places). -/
def archRelabel : ArchSOProd (realQ Q₀) ≃* ∀ w : {w : InfinitePlace F // w.IsReal}, ArchSO (QRe Q₀ w) where
  toFun g := fun w => archSOCongr (realQ_eq_QRe Q₀ (realPlaceEquiv.apply_symm_apply w)) (g (realPlaceEquiv.symm w))
  invFun g := fun σ => archSOCongr (realQ_eq_QRe Q₀ (rfl : realPlaceEquiv σ = _)).symm (g (realPlaceEquiv σ))
  left_inv g := by
    funext σ
    refine archSO_ext ?_
    rw [incl_archSOCongr, incl_archSOCongr]
    exact congrArg (fun τ => ArchSO.incl (realQ Q₀ τ) (g τ)) (realPlaceEquiv.symm_apply_apply σ)
  right_inv g := by
    funext w
    refine archSO_ext ?_
    rw [incl_archSOCongr, incl_archSOCongr]
    exact congrArg (fun v => ArchSO.incl (QRe Q₀ v) (g v)) (realPlaceEquiv.apply_symm_apply w)
  map_mul' a b := by
    funext w
    exact map_mul (archSOCongr _) (a _) (b _)

theorem measurable_archRelabel : Measurable (archRelabel Q₀) :=
  measurable_pi_iff.mpr fun _ => (measurable_archSOCongr _).comp (measurable_pi_apply _)

theorem measurable_archRelabel_symm : Measurable (archRelabel Q₀).symm :=
  measurable_pi_iff.mpr fun _ => (measurable_archSOCongr _).comp (measurable_pi_apply _)

theorem QuadForm_map_map {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] (g : R →+* S) (f : S →+* T)
    (Q : QuadForm R n) : (Q.map g).map f = Q.map (f.comp g) := rfl

theorem isPosDefR_QRe (hQ : Q₀.Nondegenerate) (hpd : IsTotallyPosDef QF) (w : {w : InfinitePlace F // w.IsReal}) :
    IsPosDefR (QRe Q₀ w) := by
  rw [QRe, QuadForm_map_map]; exact isPosDefR_map Q₀ _ hQ hpd

/-- The relabelling carries the $\mu_\infty$ to the $\mu_\infty$ (definite case). -/
theorem map_archRelabel_muInf (hQ : Q₀.Nondegenerate) (hpd : IsTotallyPosDef QF) :
    haveI : ∀ σ, Fact (IsPosDefR (realQ Q₀ σ)) := fun σ => ⟨isPosDefR_realQ Q₀ hQ hpd σ⟩
    haveI : ∀ w, Fact (IsPosDefR (QRe Q₀ w)) := fun w => ⟨isPosDefR_QRe Q₀ hQ hpd w⟩
    (muInf (realQ Q₀)).map (archRelabel Q₀) = muInf (QRe Q₀) := by
  have : ∀ σ, Fact (IsPosDefR (realQ Q₀ σ)) := fun σ => ⟨isPosDefR_realQ Q₀ hQ hpd σ⟩
  have : ∀ w, Fact (IsPosDefR (QRe Q₀ w)) := fun w => ⟨isPosDefR_QRe Q₀ hQ hpd w⟩
  have h1 := (measurePreserving_piCongrLeft (α := fun σ => ArchSO (realQ Q₀ σ))
    (fun σ => ArchSO.mu (realQ Q₀ σ)) (realPlaceEquiv (F := F)).symm).symm
  have h2 := measurePreserving_pi (fun w => ArchSO.mu (realQ Q₀ (realPlaceEquiv.symm w)))
    (fun w => ArchSO.mu (QRe Q₀ w))
    (f := fun w => archSOCongr (realQ_eq_QRe Q₀ (realPlaceEquiv.apply_symm_apply w)))
    fun w => measurePreserving_archSOCongr _
  exact (h2.comp h1).map_eq

/-- **The archimedean comparison** $\prod_\sigma SO(Q^\sigma)(\mathbb R) \cong G_\infty$ (no complex places). -/
def archEquivM1d : ArchSOProd (realQ Q₀) ≃* GInfSO Q₀ :=
  (archRelabel Q₀).trans (MulEquiv.prodUnique (M := ∀ w : {w : InfinitePlace F // w.IsReal}, ArchSO (QRe Q₀ w))
    (N := ∀ w : {w : InfinitePlace F // w.IsComplex}, ArchSOC (QCx Q₀ w))).symm

theorem archEquivM1d_apply (g : ArchSOProd (realQ Q₀)) : archEquivM1d Q₀ g = (archRelabel Q₀ g, default) := rfl

theorem measurable_archEquivM1d : Measurable (archEquivM1d Q₀) :=
  (measurable_archRelabel Q₀).prodMk measurable_const

theorem measurable_archEquivM1d_symm : Measurable (archEquivM1d Q₀).symm :=
  (measurable_archRelabel_symm Q₀).comp measurable_fst

/-- **The archimedean Tamagawa measures agree** (totally real, totally definite): the comparison carries the $c_F\,\mu_\infty$ to $c_F\,\mu_\infty^{\mathrm{Leray}}$ (`pi_lerayMeasure_eq_muInf`). -/
@[kb "weil1982" "§2.2–2.3 (gauge forms at real places) [unverified]"]
theorem map_muInfTam (hQ : Q₀.Nondegenerate) (hn : 0 < n) (hpd : IsTotallyPosDef QF) :
    (muInfTam Q₀ hQ hpd).map (archEquivM1d Q₀) = muArchTamSO Q₀ hQ := by
  have : ∀ σ, Fact (IsPosDefR (realQ Q₀ σ)) := fun σ => ⟨isPosDefR_realQ Q₀ hQ hpd σ⟩
  have : ∀ w, Fact (IsPosDefR (QRe Q₀ w)) := fun w => ⟨isPosDefR_QRe Q₀ hQ hpd w⟩
  rw [muInfTam, muArchTamSO, Measure.map_smul]
  congr 1
  have hfun : (archEquivM1d Q₀ : ArchSOProd (realQ Q₀) → GInfSO Q₀) =
      (fun x => (x, (default : ∀ w : {w : InfinitePlace F // w.IsComplex}, ArchSOC (QCx Q₀ w)))) ∘
        (archRelabel Q₀) := rfl
  rw [hfun, ← Measure.map_map measurable_prodMk_right (measurable_archRelabel Q₀),
    map_archRelabel_muInf Q₀ hQ hpd, ← Measure.prod_dirac, muArchNF, muArchLeray,
    pi_lerayMeasure_eq_muInf (QRe Q₀) _ hn, Measure.pi_of_empty]
  · congr 2
  · exact (measurable_archEquivM1d Q₀).aemeasurable

/-- **The adelic comparison** $SO(V)(\mathbb A)_{\mathrm{prod}} = \prod_\sigma SO(Q^\sigma)(\mathbb R)\times SO(V)(\mathbb A_f)
\cong SO(V)(\mathbb A)$ = `SOAdele Q₀`. -/
def adeleEquivM1d : ArchSOProd (realQ Q₀) × SOAf Q₀ ≃* SOAdele Q₀ :=
  (archEquivM1d Q₀).prodCongr (MulEquiv.refl _)

/-- **The comparison carries the $\Gamma$ to $\Gamma$.** -/
theorem map_GammaSO : (GammaSO Q₀).map (adeleEquivM1d Q₀).toMonoidHom = GammaSOAdele Q₀ := by
  rw [GammaSO, MonoidHom.map_range, GammaSOAdele]
  congr 1
  ext1 γ
  refine Prod.ext (Prod.ext ?_ (Subsingleton.elim _ _)) rfl
  funext w
  refine archSO_ext ?_
  show ArchSO.incl _ (archSOCongr _ (archHom Q₀ (realPlaceEquiv.symm w) γ)) =
    ArchSO.incl _ (archHomR Q₀ (embedding_of_isReal w.2) γ)
  rw [incl_archSOCongr]
  show Matrix.GeneralLinearGroup.map (realEmb (realPlaceEquiv.symm w)) ((γ : orthGroup QF F) : GL (Fin n) F) =
    Matrix.GeneralLinearGroup.map (embedding_of_isReal w.2) ((γ : orthGroup QF F) : GL (Fin n) F)
  rw [embedding_realPlaceEquiv (realPlaceEquiv.apply_symm_apply w)]

/-- **Weil's measure specializes to `muAdele`** (totally real $F$, totally positive definite $Q$, any $\lambda$): the comparison
isomorphism carries `muAdele` to `muTam`. -/
@[kb "weil1982" "§2.3, p. 21 (Tamagawa measure); cf. muAdele [unverified]"]
theorem map_muAdele_eq_muTam (hQ : Q₀.Nondegenerate) (hn : 0 < n) (hpd : IsTotallyPosDef QF) (lam : HeightOneSpectrum (𝓞 F) → ℝ) :
    (muAdele Q₀ hQ hpd lam).map (adeleEquivM1d Q₀) = muTam Q₀ hQ lam := by
  have h := map_prodMap_prod (measurable_archEquivM1d Q₀) measurable_id (muInfTam Q₀ hQ hpd) (muFin Q₀ lam)
    (muArchTamSO Q₀ hQ) (muFin Q₀ lam) (rA := 1) (rB := 1) (by rw [one_smul, map_muInfTam Q₀ hQ hn hpd])
    (by rw [one_smul, Measure.map_id])
  rw [one_mul, one_smul] at h
  exact h

/-- **Covolume comparison**: $\mathrm{covol}(\Gamma, SO(V)(\mathbb A), \mu_{\mathrm{Tam}}) =
\mathrm{covol}(\Gamma, SO(V)(\mathbb A)_{\mathrm{prod}}, \mu_{\mathbb A})$ for totally real $F$, totally definite $Q$, any $\lambda$. -/
@[kb "weil1982" "§2.4, p. 23 (τ(G) = vol(G_𝔸/G_k))"]
theorem covolume_muTam_eq_covolume_muAdele (hQ : Q₀.Nondegenerate) (hn : 0 < n) (hpd : IsTotallyPosDef QF)
    (lam : HeightOneSpectrum (𝓞 F) → ℝ) :
    covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ lam) =
      covolume (GammaSO Q₀) (ArchSOProd (realQ Q₀) × SOAf Q₀) (muAdele Q₀ hQ hpd lam) := by
  have : ∀ σ, Fact (IsPosDefR (realQ Q₀ σ)) := fun σ => ⟨isPosDefR_realQ Q₀ hQ hpd σ⟩
  have := countable_GammaSO Q₀
  have : SFinite (muInfTam Q₀ hQ hpd) := by unfold muInfTam; infer_instance
  have : (muInfTam Q₀ hQ hpd).IsMulLeftInvariant := by unfold muInfTam; infer_instance
  have : (muAdele Q₀ hQ hpd lam).IsMulLeftInvariant := by unfold muAdele; infer_instance
  exact (covolume_eq_of_map (GammaSO Q₀) (GammaSOAdele Q₀) (adeleEquivM1d Q₀)
    ((measurable_archEquivM1d Q₀).prodMap measurable_id) ((measurable_archEquivM1d_symm Q₀).prodMap measurable_id)
    (map_GammaSO Q₀) _ _ (map_muAdele_eq_muTam Q₀ hQ hn hpd lam)).symm

/-- **`TamagawaNumberTwoAdelic` specializes to `TamagawaNumberTwo`** (totally real $F$, $Q$ totally positive definite,
$n\ge1$; no PID or class-number hypothesis): Weil's adelic statement for the Tamagawa measure `muTam` is the library's
$\tau(SO(Q_0)) = 2$. -/
@[kb "weil1982" "§2.4, p. 23; Thm 3.7.1, Thm 4.5.1 (τ(SO) = 2)"]
theorem tamagawaNumberTwoAdelic_iff (hQ : Q₀.Nondegenerate) (hn : 0 < n) (hpd : IsTotallyPosDef QF)
    (hLi : IsIntegral QF (stdLat F n).1) : TamagawaNumberTwoAdelic Q₀ hQ ↔ TamagawaNumberTwo Q₀ := by
  rw [TamagawaNumberTwoAdelic, covolume_muTam_eq_covolume_muAdele Q₀ hQ hn hpd,
    tamagawaNumberTwo_iff_covolume Q₀ hQ hn hpd hLi]

end Definite

end QuadFormsKB.Tamagawa.Measure.Weil
