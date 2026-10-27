/-
# The norm-one volumes of an isotropic binary stabilizer by double cosets

**Layer:** number fields, adeles. $Q$ a nondegenerate **isotropic** binary form over $\mathcal O_F$, $e$ an isotropic vector,
$\chi = \chi_e : SO(Q)(\mathbb A)\to\mathbb A_F^\times$ the eigenvalue on the line $F e$ (`isoChar`, a bijection), $H = SO(Q)$
(a split torus $\cong\mathbb G_m$, so all groups below are commutative), $\Gamma = H(F)$ (`GammaSOAdele`).

* `isoNormInf`, `isoNormFin`: $a\mapsto|\chi(a)|_\infty$ on $H_\infty$ and $u\mapsto|\chi(u)|_f$ on $H(\mathbb A_f)$; their product
  is $|\chi|_{\mathbb A}$ (`ideleNorm_isoChar_split`);
* `isoShellInf` $=\{a\in H_\infty : 0\le\log|\chi(a)|_\infty<1\}$, the archimedean shell;
* `DCq Q U`: the double cosets $\Gamma_f\backslash H(\mathbb A_f)/U$ for a subgroup $U$, `dcqRep` representatives;
* **`tauIso_eq_tsum_DCq`** (the torus lemma): for every measurable subgroup $U\le H(\mathbb A_f)$ with countably many double cosets, discrete level groups, on which $|\chi|_f = 1$,
  $$\tau^1(H) = \rho_F^{-1}\,\mu^\lambda_f(U)\sum_{c\in\Gamma_f\backslash H(\mathbb A_f)/U}
    \operatorname{covol}\bigl(\Gamma_c\backslash H_\infty,\ \mu_\infty|_{\text{shell}}\bigr),$$
  $\Gamma_c$ = `levelGroup Γ U c` $=\{\gamma_\infty : \gamma\in\Gamma,\ \gamma_f\in U\}$ (a group of units, inside $H^1_\infty$),
  $\mu_\infty$ = `muArchTamSO Q`, $\mu^\lambda_f$ = `muFin Q lamV` ($\lambda_v = 1 - Nv^{-1}$), so $\rho_F^{-1}\mu_\infty\times
  \mu^\lambda_f$ = `muTamIso Q`. Since $\mu_\infty = \mu^1_\infty\times dt/t$, each covolume is
  $\operatorname{vol}(\Gamma_c\backslash H^1_\infty)$. For $U = \hat{\mathcal O}^\times$ (and $Q$ hyperbolic) this is the class number
  formula $\rho_F = 2^{r_1}(2\pi)^{r_2}hR/(w\sqrt{|d_F|})$ in Weil's normalization.

*Proof.* $\bigcup_cD_c\times cU$ ($D_c$ exact fundamental domains of $\Gamma_c$ in $H_\infty$) is a fundamental domain of
$\Gamma$ (`exists_unique_smul_mem_beta`); on $D_c\times cU$ the shell $\{0\le\log|\chi|_{\mathbb A}<1\}$ is
$(D_c\cap s_c^{-1}\,\text{shell})\times cU$ with $|\chi(s_c)|_\infty = |\chi(c)|_f$; translating by $s_c$ (the groups are
commutative) gives the covolume.
-/
import QuadFormsKB.Tamagawa.Measure.Weil.BinaryIsoFinal
import QuadFormsKB.Tamagawa.Indefinite.ThetaUnfold
import QuadFormsKB.Tamagawa.Indefinite.ClassicalLattice

open MeasureTheory Set MulAction
open scoped ENNReal Pointwise

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField IsDedekindDomain QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil

variable {F : Type} [Field F] [NumberField F] (Q : QuadForm (𝓞 F) 2) (hQ : Q.Nondegenerate) {e : Fin 2 → F}
  (he : IsIsoVec Q e)

/-! ### The norms of $\chi$ at the infinite and at the finite places -/

/-- $|\chi_e(a)|_\infty$ for $a\in SO(Q)(F_\infty)$ (the idele norm of $\chi_e(a, 1)$). -/
def isoNormInf (a : GInfSO Q) : ℝ := ideleNorm F (isoChar hQ he ((a, 1) : SOAdele Q))

/-- $|\chi_e(u)|_f$ for $u\in SO(Q)(\mathbb A_f)$ (the idele norm of $\chi_e(1, u)$). -/
def isoNormFin (u : SOAf Q) : ℝ := ideleNorm F (isoChar hQ he ((1, u) : SOAdele Q))

/-- **The archimedean shell** $\{a : 0\le\log|\chi_e(a)|_\infty<1\}\subseteq SO(Q)(F_\infty)$. -/
def isoShellInf : Set (GInfSO Q) := (fun a => Real.log (isoNormInf Q hQ he a)) ⁻¹' Ico 0 1

theorem ideleNorm_isoChar_split (g : SOAdele Q) :
    ideleNorm F (isoChar hQ he g) = isoNormInf Q hQ he g.1 * isoNormFin Q hQ he g.2 := by
  have h : g = ((g.1, 1) : SOAdele Q) * ((1, g.2) : SOAdele Q) := by
    ext <;> simp
  conv_lhs => rw [h]
  rw [map_mul, ideleNorm_mul]
  rfl

theorem isoNormInf_mul (a b : GInfSO Q) :
    isoNormInf Q hQ he (a * b) = isoNormInf Q hQ he a * isoNormInf Q hQ he b := by
  have h : ((a * b, 1) : SOAdele Q) = ((a, 1) : SOAdele Q) * ((b, 1) : SOAdele Q) := by
    ext <;> simp
  rw [isoNormInf, h, map_mul, ideleNorm_mul]
  rfl

theorem isoNormFin_mul (a b : SOAf Q) :
    isoNormFin Q hQ he (a * b) = isoNormFin Q hQ he a * isoNormFin Q hQ he b := by
  have h : ((1, a * b) : SOAdele Q) = ((1, a) : SOAdele Q) * ((1, b) : SOAdele Q) := by
    ext <;> simp
  rw [isoNormFin, h, map_mul, ideleNorm_mul]
  rfl

theorem isoNormInf_pos (a : GInfSO Q) : 0 < isoNormInf Q hQ he a := ideleNorm_pos _

theorem isoNormFin_pos (u : SOAf Q) : 0 < isoNormFin Q hQ he u := ideleNorm_pos _

theorem measurable_isoNormInf : Measurable (isoNormInf Q hQ he) :=
  continuous_ideleNorm.measurable.comp ((isoComparison_of_isotropic hQ he).measurable.comp
    (measurable_id.prodMk measurable_const))

theorem measurableSet_isoShellInf : MeasurableSet (isoShellInf Q hQ he) :=
  (Real.measurable_log.comp (measurable_isoNormInf Q hQ he)) measurableSet_Ico

/-- **The product formula**: $|\chi_e(\gamma)|_{\mathbb A} = 1$ for $\gamma\in SO(Q)(F)$. -/
theorem ideleNorm_isoChar_gamma (γ : SOAdele Q) (hγ : γ ∈ GammaSOAdele Q) : ideleNorm F (isoChar hQ he γ) = 1 := by
  have h : isoChar hQ he γ ∈ diagUnitsSub F := by
    rw [← map_GammaSOAdele_isoChar hQ he]; exact ⟨γ, hγ, rfl⟩
  obtain ⟨ξ, hξ⟩ := h
  rw [← hξ]
  exact ideleNorm_diagUnits ξ

/-! ### Commutativity -/

theorem isoChar_injective : Function.Injective (isoChar hQ he) := (isoChar_bijective hQ he).1

include hQ he in
theorem mul_comm_SOAdele_iso (g h : SOAdele Q) : g * h = h * g :=
  isoChar_injective Q hQ he (by rw [map_mul, map_mul, mul_comm])

include hQ he in
theorem mul_comm_GInfSO_iso (a b : GInfSO Q) : a * b = b * a := by
  have := mul_comm_SOAdele_iso Q hQ he ((a, 1) : SOAdele Q) ((b, 1) : SOAdele Q)
  simpa using congrArg Prod.fst this

include hQ he in
theorem mul_comm_SOAf_iso (a b : SOAf Q) : a * b = b * a := by
  have := mul_comm_SOAdele_iso Q hQ he ((1, a) : SOAdele Q) ((1, b) : SOAdele Q)
  simpa using congrArg Prod.snd this

/-- **Every positive real is an archimedean norm** $|\chi_e(a)|_\infty$. -/
theorem exists_isoNormInf_eq {t : ℝ} (ht : 0 < t) : ∃ a : GInfSO Q, isoNormInf Q hQ he a = t := by
  obtain ⟨g, hg⟩ := (isoChar_bijective hQ he).2 (normSection F t ht)
  have h2 : isoChar hQ he ((1, g.2) : SOAdele Q) = 1 := by
    apply Units.ext
    rw [isoChar_val, Units.val_one]
    have hv := congrArg (fun x : (Adeles F)ˣ => (x : Adeles F)) hg
    simp only [isoChar_val] at hv
    refine Prod.ext (map_one _) ?_
    exact (congrArg Prod.snd hv).trans rfl
  have hg2 : g.2 = 1 := by
    have := isoChar_injective Q hQ he (h2.trans (map_one _).symm)
    exact congrArg Prod.snd this
  refine ⟨g.1, ?_⟩
  rw [isoNormInf, show ((g.1, 1) : SOAdele Q) = g from Prod.ext rfl hg2.symm, hg]
  exact ideleNorm_normSection t ht

/-! ### Double cosets $\Gamma_f\backslash H(\mathbb A_f)/U$ -/

variable (U : Subgroup (SOAf Q))

/-- The relation $b' \in\Gamma_f\,b\,U$. -/
def dcqSetoid : Setoid (SOAf Q) where
  r b b' := ∃ γ ∈ GammaSOAdele Q, ∃ u ∈ U, b' = γ.2 * b * u
  iseqv := by
    refine ⟨fun b => ⟨1, (GammaSOAdele Q).one_mem, 1, U.one_mem, by simp⟩, fun {b b'} h => ?_,
      fun {b b' b''} h h' => ?_⟩
    · obtain ⟨γ, hγ, u, hu, rfl⟩ := h
      refine ⟨γ⁻¹, (GammaSOAdele Q).inv_mem hγ, u⁻¹, U.inv_mem hu, ?_⟩
      simp only [Prod.snd_inv]; group
    · obtain ⟨γ, hγ, u, hu, rfl⟩ := h
      obtain ⟨γ', hγ', u', hu', rfl⟩ := h'
      refine ⟨γ' * γ, (GammaSOAdele Q).mul_mem hγ' hγ, u * u', U.mul_mem hu hu', ?_⟩
      simp only [Prod.snd_mul]; group

/-- **The double cosets** $\Gamma_f\backslash H(\mathbb A_f)/U$. -/
abbrev DCq : Type := Quotient (dcqSetoid Q U)

/-- A representative of a double coset. -/
def dcqRep (c : DCq Q U) : SOAf Q := Quotient.out c

theorem countable_quot_of_isOpen (hU : IsOpen (U : Set (SOAf Q))) : Countable (SOAf Q ⧸ U) := by
  have : DiscreteTopology (SOAf Q ⧸ U) := QuotientGroup.discreteTopology hU
  exact (TopologicalSpace.separableSpace_iff_countable).1 inferInstance

theorem countable_DCq (hU : IsOpen (U : Set (SOAf Q))) : Countable (DCq Q U) := by
  have := countable_quot_of_isOpen Q U hU
  refine Function.Surjective.countable (f := fun q : SOAf Q ⧸ U => (Quotient.mk _ (Quotient.out q) : DCq Q U)) ?_
  intro c
  refine ⟨(QuotientGroup.mk (dcqRep Q U c) : SOAf Q ⧸ U), ?_⟩
  conv_rhs => rw [← Quotient.out_eq c]
  apply Quotient.sound
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U (dcqRep Q U c)
  refine ⟨1, (GammaSOAdele Q).one_mem, u⁻¹, U.inv_mem u.2, ?_⟩
  rw [hu]; simp [dcqRep]

include hQ he in
/-- In a commutative group the level groups do not depend on the representative. -/
theorem levelGroup_eq_one (b : SOAf Q) :
    levelGroup (GammaSOAdele Q) U b = levelGroup (GammaSOAdele Q) U 1 := by
  have h : conjSub U b = conjSub U 1 := by
    ext x
    rw [mem_conjSub, mem_conjSub, mul_comm_SOAf_iso Q hQ he b⁻¹, mul_assoc, inv_mul_cancel, mul_one, inv_one,
      one_mul, mul_one]
  simp only [levelGroup, levelStab, h]

/-! ### The torus lemma -/

theorem isoNormInf_levelGroup (hU1 : ∀ u ∈ U, isoNormFin Q hQ he u = 1) (b : SOAf Q)
    (γ : levelGroup (GammaSOAdele Q) U b) : isoNormInf Q hQ he γ = 1 := by
  obtain ⟨g, hg, hgγ⟩ := Subgroup.mem_map.mp γ.2
  have h1 := ideleNorm_isoChar_gamma Q hQ he g hg.1
  have hf : g.2 ∈ U := by
    have : b⁻¹ * g.2 * b ∈ U := hg.2
    rwa [mul_comm_SOAf_iso Q hQ he b⁻¹, mul_assoc, inv_mul_cancel, mul_one] at this
  rw [ideleNorm_isoChar_split, hU1 _ hf, mul_one] at h1
  rw [← hgγ]
  exact h1

theorem smul_mem_isoShellInf_iff (hU1 : ∀ u ∈ U, isoNormFin Q hQ he u = 1) (b : SOAf Q)
    (γ : levelGroup (GammaSOAdele Q) U b) (a : GInfSO Q) :
    γ • a ∈ isoShellInf Q hQ he ↔ a ∈ isoShellInf Q hQ he := by
  show Real.log (isoNormInf Q hQ he ((γ : GInfSO Q) * a)) ∈ Ico 0 1 ↔ Real.log (isoNormInf Q hQ he a) ∈ Ico 0 1
  rw [isoNormInf_mul, isoNormInf_levelGroup Q hQ he U hU1 b γ, one_mul]

set_option maxHeartbeats 1600000 in
/-- **The torus lemma**: $\tau^1(H) = \rho_F^{-1}\mu^\lambda_f(U)\sum_c\operatorname{covol}(\Gamma_c\backslash H_\infty,
\mu_\infty|_{\text{shell}})$ for every open subgroup $U\le H(\mathbb A_f)$ with $|\chi_e|_f = 1$ on $U$ and discrete level
groups. -/
theorem tauIso_eq_tsum_DCq (hUm : MeasurableSet (U : Set (SOAf Q))) [Countable (DCq Q U)] (hU1 : ∀ u ∈ U, isoNormFin Q hQ he u = 1)
    (hdisc : ∀ b, DiscreteTopology (levelGroup (GammaSOAdele Q) U b)) :
    tauIso Q hQ he = ENNReal.ofReal (dedekindZeta_residue F)⁻¹ * muFin Q lamV U *
      ∑' c : DCq Q U, covolume (levelGroup (GammaSOAdele Q) U (dcqRep Q U c)) (GInfSO Q)
        ((muArchTamSO Q hQ).restrict (isoShellInf Q hQ he)) := by
  classical
  haveI := countable_GammaSOAdele Q
  set Γ := GammaSOAdele Q with hΓ
  set β := dcqRep Q U with hβ
  set ρ := ENNReal.ofReal (dedekindZeta_residue F)⁻¹ with hρ
  set Sh := isoShellInf Q hQ he with hSh
  have hcov : ∀ g : SOAf Q, ∃ i, ∃ γ ∈ Γ, ∃ k ∈ U, g = γ.2 * β i * k := by
    intro g
    obtain ⟨γ, hγ, u, hu, h⟩ := Quotient.mk_out (s := dcqSetoid Q U) g
    exact ⟨Quotient.mk _ g, γ, hγ, u, hu, h⟩
  have hdisj : ∀ i j, ∀ γ ∈ Γ, ∀ k ∈ U, ∀ k' ∈ U, γ.2 * β i * k = β j * k' → i = j := by
    intro i j γ hγ k hk k' hk' h
    have h' : β j = γ.2 * β i * (k * k'⁻¹) := by rw [← mul_assoc, h]; group
    have : (Quotient.mk _ (β i) : DCq Q U) = Quotient.mk _ (β j) :=
      Quotient.sound ⟨γ, hγ, k * k'⁻¹, U.mul_mem hk (U.inv_mem hk'), h'⟩
    simpa [β, dcqRep, Quotient.out_eq] using this
  have hinjA : ∀ i, ∀ γ ∈ levelStab Γ U (β i), γ.1 = 1 → γ = 1 := fun i γ hγ h1 =>
    GammaSOAdele_injA Q γ hγ.1 h1
  have hD : ∀ i, ∃ D : Set (GInfSO Q), MeasurableSet D ∧
      ∀ a : GInfSO Q, ∃! s : levelGroup Γ U (β i), s • a ∈ D := fun i => by
    haveI := hdisc (β i)
    exact exists_measurableSet_forall_existsUnique_smul_mem (levelGroup Γ U (β i))
  choose D hDm hDu using hD
  haveI : ∀ i, Countable (levelGroup Γ U (β i)) := fun i => countable_levelGroup (Γ := Γ) U (β i)
  haveI : ∀ i, MeasurableConstSMul (levelGroup Γ U (β i)) (GInfSO Q) := fun i =>
    measurableConstSMul_subgroup _
  haveI : ∀ i, SMulInvariantMeasure (levelGroup Γ U (β i)) (GInfSO Q) (muArchTamSO Q hQ) := fun i =>
    smulInvariantMeasure_subgroup _ _
  haveI : ∀ i, SMulInvariantMeasure (levelGroup Γ U (β i)) (GInfSO Q) ((muArchTamSO Q hQ).restrict Sh) :=
    fun i => smulInvariantMeasure_restrict _ _ (smul_mem_isoShellInf_iff Q hQ he U hU1 (β i))
  -- the fundamental domain of `Γ` and the shell
  have hEm : ∀ i, MeasurableSet (D i ×ˢ (β i • (U : Set (SOAf Q)))) := fun i =>
    (hDm i).prod (hUm.const_smul (β i))
  haveI := measurableConstSMul_subgroup Γ
  haveI : SMulInvariantMeasure Γ (SOAdele Q) (muTamIso Q hQ) := smulInvariantMeasure_muTamIso
  haveI : SMulInvariantMeasure Γ (SOAdele Q) ((muTamIso Q hQ).restrict (isoShell Q hQ he)) :=
    smulInvariantMeasure_restrict _ _ (smul_mem_isoShellIco_iff (isoComparison_of_isotropic hQ he) 0 1)
  have hE : IsFundamentalDomain Γ (⋃ i, D i ×ˢ (β i • (U : Set (SOAf Q))))
      ((muTamIso Q hQ).restrict (isoShell Q hQ he)) :=
    IsFundamentalDomain.mk' (MeasurableSet.iUnion hEm).nullMeasurableSet
      (exists_unique_smul_mem_beta Γ U β hcov hdisj hinjA D hDu)
  have hdisjSet : Pairwise (Function.onFun Disjoint fun i => D i ×ˢ (β i • (U : Set (SOAf Q)))) := by
    intro i j hne
    rw [Function.onFun, Set.disjoint_left]
    rintro ⟨a, b⟩ ⟨-, k, hk, rfl⟩ ⟨-, k', hk', hb⟩
    exact hne (hdisj i j 1 Γ.one_mem k hk k' hk' (by simpa using hb.symm))
  have hShm : MeasurableSet (isoShell Q hQ he) := by
    show MeasurableSet (isoShellIco Q hQ he 0 1)
    rw [isoShellIco_eq_preimage]
    exact (isoComparison_of_isotropic hQ he).measurable (measurableSet_ideleLogShell 0 1)
  rw [tauIso, hE.covolume_eq_volume, Measure.restrict_apply (MeasurableSet.iUnion hEm), iUnion_inter,
    measure_iUnion (fun i j hij => (hdisjSet hij).mono inter_subset_left inter_subset_left)
      (fun i => (hEm i).inter hShm), ← ENNReal.tsum_mul_left]
  refine tsum_congr fun i => ?_
  -- one double coset
  obtain ⟨s, hs⟩ := exists_isoNormInf_eq Q hQ he (isoNormFin_pos Q hQ he (β i))
  have hset : D i ×ˢ (β i • (U : Set (SOAf Q))) ∩ isoShell Q hQ he =
      (D i ∩ (fun a => s * a) ⁻¹' Sh) ×ˢ (β i • (U : Set (SOAf Q))) := by
    ext ⟨a, b⟩
    simp only [mem_inter_iff, mem_prod, mem_preimage]
    constructor
    · rintro ⟨⟨ha, hb⟩, hsh⟩
      refine ⟨⟨ha, ?_⟩, hb⟩
      obtain ⟨u, hu, rfl⟩ := hb
      have : ideleNorm F (isoChar hQ he ((a, β i • u) : SOAdele Q)) =
          isoNormInf Q hQ he (s * a) := by
        rw [ideleNorm_isoChar_split, isoNormInf_mul, hs, smul_eq_mul, isoNormFin_mul, hU1 u hu, mul_one,
          mul_comm]
      show Real.log (isoNormInf Q hQ he (s * a)) ∈ Ico 0 1
      rw [← this]; exact hsh
    · rintro ⟨⟨ha, hsh⟩, hb⟩
      refine ⟨⟨ha, hb⟩, ?_⟩
      obtain ⟨u, hu, rfl⟩ := hb
      have : ideleNorm F (isoChar hQ he ((a, β i • u) : SOAdele Q)) =
          isoNormInf Q hQ he (s * a) := by
        rw [ideleNorm_isoChar_split, isoNormInf_mul, hs, smul_eq_mul, isoNormFin_mul, hU1 u hu, mul_one,
          mul_comm]
      show Real.log (ideleNorm F (isoChar hQ he ((a, β i • u) : SOAdele Q))) ∈ Ico 0 1
      rw [this]; exact hsh
  -- the translated fundamental domain
  have hsD : ∀ a : GInfSO Q, ∃! γ : levelGroup Γ U (β i), γ • a ∈ (fun a => s⁻¹ * a) ⁻¹' D i := by
    intro a
    obtain ⟨γ, hγ, huniq⟩ := hDu i (s⁻¹ * a)
    refine ⟨γ, ?_, fun γ' hγ' => huniq γ' ?_⟩
    · show s⁻¹ * ((γ : GInfSO Q) * a) ∈ D i
      rw [← mul_assoc, mul_comm_GInfSO_iso Q hQ he s⁻¹, mul_assoc]; exact hγ
    · show (γ' : GInfSO Q) * (s⁻¹ * a) ∈ D i
      have : s⁻¹ * ((γ' : GInfSO Q) * a) ∈ D i := hγ'
      rwa [← mul_assoc, mul_comm_GInfSO_iso Q hQ he s⁻¹, mul_assoc] at this
  have hsDm : MeasurableSet ((fun a => s⁻¹ * a) ⁻¹' D i) := measurable_const_mul _ (hDm i)
  have hcovi : covolume (levelGroup Γ U (β i)) (GInfSO Q) ((muArchTamSO Q hQ).restrict Sh) =
      muArchTamSO Q hQ (D i ∩ (fun a => s * a) ⁻¹' Sh) := by
    rw [(IsFundamentalDomain.mk' hsDm.nullMeasurableSet hsD).covolume_eq_volume,
      Measure.restrict_apply hsDm]
    have e : (fun a => s⁻¹ * a) ⁻¹' D i ∩ Sh = (fun a => s⁻¹ * a) ⁻¹' (D i ∩ (fun a => s * a) ⁻¹' Sh) := by
      ext a; simp [mul_assoc]
    rw [e, measure_preimage_mul]
  rw [hset, muTamIso, Measure.smul_apply, muTam, Measure.prod_prod, measure_smul, hcovi, smul_eq_mul]
  ring

end QuadFormsKB.Tamagawa.Indefinite
