import QuadFormsKB.Weil.Global
import QuadFormsKB.Weil.LocalK0
import QuadFormsKB.Analysis.AdelicPoissonPi

/-!
# The theta distribution on data with an arbitrary Schwartz archimedean part

`thetaDist_gW` and `thetaDist_omegaG` (`Weil/Global.lean`) need fully factorizable data (`GDatum.IsPure`:
$\Phi_\infty = c_0\bigotimes_if_{0,i}$, $\Phi_v = c_v\bigotimes_if_{v,i}$). Here the archimedean component is an
**arbitrary** Schwartz function on $F_\infty^{2m}$ and the finite components are arbitrary elements of $S(V_v)$.

* `thetaDist_gW_schwartz`: $\Theta(\omega(w)\Phi) = \Theta(\Phi)$ when $\Phi_v = c_v\bigotimes_if_{v,i}$ are pure tensors
  (`GDatum.IsSchwartzInf`). *Proof.* $\omega_\infty(w)\Phi_\infty(y) = \gamma_{V,\infty}\prod_i|2a_i|_\infty^{1/2}\,
  \hat\Phi_\infty\big((2a_iy_i)_i\big)$, $\hat\Phi_\infty$ = `fourierInfPi` (`opWf_inf_eq`); at a finite place
  $\omega_v(w)\Phi_v = c_v\gamma_{V,v}\bigotimes_i|2a_i|_v^{1/2}\hat f_{v,i}(2a_i\,\cdot)$; the substitution
  $\xi_i \mapsto 2a_i\xi_i$ of $F^{2m}$, $\prod_u|2a_i|_u^{1/2} = 1$ (`sqrt_prod_modulus_eq_one`), the $n$-variable adelic
  Poisson formula (`adelicPoisson_factorizable_pi`) and $\prod_u\gamma_{V,u} = 1$ (`prod_gammaV_eq_one`).
* `thetaDist_gW_schwartzAdm`: the same for every admissible datum with $\Phi_v \in S(V_v)$ (`GDatum.IsSchwartzAdm`),
  by induction over the finitely many places where $\Phi_v$ is not a pure tensor (`gWClaim_induct`; linearity of
  $\Phi_v \mapsto \Theta(\Phi)$ and of $\omega_v(w)$ on $S(V_v)$).
* **`thetaDist_omegaG_schwartzAdm`**: $\Theta(\omega(\gamma)\Phi) = \Theta(\Phi)$ for every $\gamma \in \mathrm{SL}_2(F)$ and every
  such datum: the class is stable under $\omega(n(b))$, $\omega(m(t))$, $\omega(w)$ (`exists_schwartz_opNf`,
  `exists_schwartz_opMf`, `exists_schwartz_opWf`, the last from `exists_schwartz_fourierInfPi`).
-/

open IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory
open QuadFormsKB.Analysis
open scoped Classical Real FourierTransform MatrixGroups

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.WeilRep

open LocalData

variable {F : Type} [Field F] [NumberField F]

/-- **Data with a Schwartz archimedean part** (`IsSchwartzInf`): $\Phi = (\Phi_\infty, (c_v\bigotimes_if_{v,i})_v)$ with
$\Phi_\infty$ an arbitrary Schwartz function on $F_\infty^n$, $f_{v,i}$ locally constant with compact support, and
$c_v = 1$, $f_{v,i} = \mathbf 1_{\mathcal O_v}$ for $v \notin T$, a finite set. -/
def GDatum.IsSchwartzInf {n : ℕ} (Φ : GDatum F n) : Prop :=
  ∃ (G : SchwartzMap (Fin n → mixedSpace F) ℂ) (c : HeightOneSpectrum (𝓞 F) → ℂ)
    (f : ∀ v : HeightOneSpectrum (𝓞 F), Fin n → v.adicCompletion F → ℂ) (T : Finset (HeightOneSpectrum (𝓞 F))),
    (∀ v i, f v i ∈ SBK (v.adicCompletion F)) ∧ (∀ v ∉ T, c v = 1 ∧ ∀ i, f v i = ballIndV v 0 0) ∧
      Φ = ⟨G, fun v => c v • ptensor (f v)⟩

variable {m : ℕ} (a : Fin (2 * m) → Fˣ)

lemma traceInf_sum {ι : Type*} (s : Finset ι) (g : ι → mixedSpace F) :
    traceInf (∑ i ∈ s, g i) = ∑ i ∈ s, traceInf (g i) :=
  map_sum (traceInfL (F := F)) g s

/-- **$\omega_\infty(w)$ through the $n$-variable transform:**
$\omega_\infty(w)\Phi(\xi) = \gamma_{V,\infty}\prod_i|2a_i|_\infty^{1/2}\,\hat\Phi\big((2a_i\xi_i)_i\big)$ at $\xi \in F^{2m}$. -/
lemma opWf_inf_eq (Φ : (Fin (2 * m) → mixedSpace F) → ℂ) (ξ : Fin (2 * m) → F) :
    (localDataInf (F := F)).opWf (aInf a) Φ (ιInf ξ) =
      (localDataInf (F := F)).gammaV (aInf a) *
        (∏ i, ((Real.sqrt (mixedEmbedding.norm (mixedEmbedding F (2 * (a i : F)))) : ℝ) : ℂ)) *
          fourierInfPi Φ (ιInf fun i => 2 * (a i : F) * ξ i) := by
  have hc : (localDataInf (F := F)).cB (aInf a) =
      ∏ i, ((Real.sqrt (mixedEmbedding.norm (mixedEmbedding F (2 * (a i : F)))) : ℝ) : ℂ) := by
    simp only [cB]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [aInf_val, map_mul, map_ofNat]
    rfl
  rw [opWf, hc]
  congr 1
  simp only [fourierInfPi, muN]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  congr 1
  show ((𝐞 (traceInf (Bform (aInf a) x (ιInf ξ))) : Circle) : ℂ) = _
  rw [Bform, traceInf_sum]
  congr 3
  funext i
  congr 1
  rw [aInf_val, ιInf, ιInf, map_mul, map_mul, map_ofNat]
  ring

/-- `thetaDist_gW_schwartz` together with the absolute convergence of both theta series. -/
lemma gW_schwartz_aux {Φ : GDatum F (2 * m)} (hΦ : Φ.IsSchwartzInf) :
    Summable Φ.eval ∧ Summable (gW a Φ).eval ∧ thetaDist (gW a Φ) = thetaDist Φ := by
  obtain ⟨G, c, f, T, hf, hT, rfl⟩ := hΦ
  set s : Fin (2 * m) → F := fun i => 2 * (a i : F) with hsdef
  have hs : ∀ i, s i ≠ 0 := fun i => mul_ne_zero two_ne_zero (a i).ne_zero
  set P : (Fin (2 * m) → F) → ℂ := fun η => fourierInfPi G (ιInf η) *
    ∏ i, ∏ᶠ v, fourierV v (f v i) (algebraMap F (v.adicCompletion F) (η i)) with hP
  -- finite supports
  have hfinF : ∀ i (y : F), Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      fourierV v (f v i) (algebraMap F _ y) := by
    intro i y
    refine ((T.finite_toSet.union finite_support_diffExp).union
      (HeightOneSpectrum.Support.finite (𝓞 F) y)).subset fun v hv => ?_
    by_contra h
    simp only [Set.mem_union, Finset.mem_coe, Function.mem_support, not_or, not_not] at h
    exact hv (by
      show fourierV v (f v i) _ = 1
      rw [(hT v h.1.1).2 i]
      exact fourierV_ballIndV_zero_eq_one v (by exact_mod_cast h.1.2) (valued_le_one_of_not_mem_support h.2))
  have hfinS : ∀ i, Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ((Real.sqrt (Analysis.Weil.modK (v.adicCompletion F) (algebraMap F (v.adicCompletion F) (s i))) : ℝ) : ℂ) :=
    fun i => (hasFiniteMulSupport_modK (hs i)).subset fun v hv h' => hv (by simp only at h' ⊢; rw [h']; simp)
  have hγfin : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => (localDataV v).gammaV (aV a v) :=
    (badW_finite a).subset fun v hv => by by_contra h; exact hv (gammaV_eq_one a h)
  have hcfin : Function.HasFiniteMulSupport c := hasFiniteMulSupport_const hT
  -- the finite components of `gW a Φ`
  have hloc : ∀ v (x : F) i, (localDataV v).Fa (algebraMap F _ (a i : F)) (f v i) (algebraMap F _ x) =
      ((Real.sqrt (Analysis.Weil.modK (v.adicCompletion F) (algebraMap F (v.adicCompletion F) (s i))) : ℝ) : ℂ) *
        fourierV v (f v i) (algebraMap F _ (s i * x)) := by
    intro v x i
    simp only [LocalData.Fa, Pi.smul_apply, smul_eq_mul, dil, localDataV_four, hsdef, map_mul, map_ofNat]
    rfl
  have hfinv : ∀ v (ξ : Fin (2 * m) → F), (gW a ⟨G, fun v => c v • ptensor (f v)⟩).fin v (ιV v ξ) =
      (c v * (localDataV v).gammaV (aV a v)) *
        ∏ i, (((Real.sqrt (Analysis.Weil.modK (v.adicCompletion F)
          (algebraMap F (v.adicCompletion F) (s i))) : ℝ) : ℂ) *
          fourierV v (f v i) (algebraMap F _ (s i * ξ i))) := by
    intro v ξ
    show (localDataV v).opWf (aV a v) (c v • ptensor (f v)) (ιV v ξ) = _
    rw [LocalData.opWf_smul, LocalData.opWf_ptensor (isOps_V v), smul_smul]
    simp only [Pi.smul_apply, smul_eq_mul, ptensor, ιV]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← hloc v (ξ i) i, aV_val]
  -- the value of `gW a Φ` at a rational point
  have heval : ∀ ξ : Fin (2 * m) → F, (gW a ⟨G, fun v => c v • ptensor (f v)⟩).eval ξ =
      ((localDataInf (F := F)).gammaV (aInf a) * ((∏ᶠ v, c v) * ∏ᶠ v, (localDataV v).gammaV (aV a v))) *
        P (fun i => s i * ξ i) := by
    intro ξ
    rw [GDatum.eval, finprod_congr (hfinv · ξ)]
    show (localDataInf (F := F)).opWf (aInf a) G (ιInf ξ) * _ = _
    rw [opWf_inf_eq]
    have hprodF : ∀ i, Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
        ((Real.sqrt (Analysis.Weil.modK (v.adicCompletion F)
          (algebraMap F (v.adicCompletion F) (s i))) : ℝ) : ℂ) *
          fourierV v (f v i) (algebraMap F _ (s i * ξ i)) := fun i => (hfinS i).mul (hfinF i _)
    have hcγ : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
        c v * (localDataV v).gammaV (aV a v) := hcfin.mul hγfin
    rw [finprod_mul_distrib hcγ (Function.HasFiniteMulSupport.prod hprodF Finset.univ),
      finprod_mul_distrib hcfin hγfin, finprod_prod_comm Finset.univ _ fun i _ => hprodF i]
    simp_rw [finprod_mul_distrib (hfinS _) (hfinF _ _)]
    rw [Finset.prod_mul_distrib]
    have hK : ∏ i, (((Real.sqrt (mixedEmbedding.norm (mixedEmbedding F (s i))) : ℝ) : ℂ) *
        ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((Real.sqrt (Analysis.Weil.modK (v.adicCompletion F)
          (algebraMap F (v.adicCompletion F) (s i))) : ℝ) : ℂ)) = 1 :=
      Finset.prod_eq_one fun i _ => sqrt_prod_modulus_eq_one (hs i)
    rw [Finset.prod_mul_distrib] at hK
    simp only [hP]
    linear_combination ((localDataInf (F := F)).gammaV (aInf a) * ((∏ᶠ v, c v) *
      ∏ᶠ v, (localDataV v).gammaV (aV a v)) * (fourierInfPi G (ιInf fun i => s i * ξ i) *
        ∏ i, ∏ᶠ v, fourierV v (f v i) (algebraMap F _ (s i * ξ i)))) * hK
  -- the value of `Φ`
  have hevalΦ : ∀ η : Fin (2 * m) → F, GDatum.eval ⟨G, fun v => c v • ptensor (f v)⟩ η =
      (∏ᶠ v, c v) * (G (ιInf η) * ∏ i, ∏ᶠ v, f v i (algebraMap F (v.adicCompletion F) (η i))) := by
    intro η
    simp only [GDatum.eval, Pi.smul_apply, smul_eq_mul, ptensor, ιV]
    rw [finprod_mul_distrib hcfin (Function.HasFiniteMulSupport.prod
        (fun i => hasFiniteMulSupport_coord hT i (η i)) Finset.univ),
      finprod_prod_comm Finset.univ _ fun i _ => hasFiniteMulSupport_coord hT i (η i)]
    ring
  -- substitution and Poisson summation
  set e : (Fin (2 * m) → F) ≃ (Fin (2 * m) → F) := Equiv.piCongrRight fun i => Equiv.mulLeft₀ (s i) (hs i)
  have hsub : ∑' ξ : Fin (2 * m) → F, P (fun i => s i * ξ i) = ∑' η, P η := e.tsum_eq P
  have hPoisson := adelicPoisson_factorizable_pi (fun i v => f v i) T
    (fun i v _ => isSchwartzBruhatV_of_mem_SBK v (hf v i)) (fun i v hv => (hT v hv).2 i) G
  refine ⟨?_, ?_, ?_⟩
  · rw [show GDatum.eval ⟨G, fun v => c v • ptensor (f v)⟩ = fun η => (∏ᶠ v, c v) * (G (ιInf η) *
        ∏ i, ∏ᶠ v, f v i (algebraMap F (v.adicCompletion F) (η i))) from funext hevalΦ]
    exact (summable_adelicPoisson_factorizable_pi_lhs (fun i v => f v i) T
      (fun i v _ => isSchwartzBruhatV_of_mem_SBK v (hf v i)) (fun i v hv => (hT v hv).2 i) G).mul_left _
  · rw [show (gW a ⟨G, fun v => c v • ptensor (f v)⟩).eval = fun ξ =>
        ((localDataInf (F := F)).gammaV (aInf a) * ((∏ᶠ v, c v) * ∏ᶠ v, (localDataV v).gammaV (aV a v))) *
          P (e ξ) from funext heval]
    refine Summable.mul_left _ ?_
    exact (e.summable_iff (f := P)).mpr (summable_adelicPoisson_factorizable_pi_rhs (fun i v => f v i) T
      (fun i v _ => isSchwartzBruhatV_of_mem_SBK v (hf v i)) (fun i v hv => (hT v hv).2 i) G)
  rw [thetaDist, thetaDist, tsum_congr heval, tsum_mul_left, hsub, tsum_congr hevalΦ, tsum_mul_left]
  have hγ := prod_gammaV_eq_one a
  have : ∑' η, P η = ∑' η : Fin (2 * m) → F, G (ιInf η) *
      ∏ i, ∏ᶠ v, f v i (algebraMap F (v.adicCompletion F) (η i)) := hPoisson.symm
  rw [this]
  linear_combination ((∏ᶠ v, c v) * ∑' η : Fin (2 * m) → F, G (ιInf η) *
      ∏ i, ∏ᶠ v, f v i (algebraMap F (v.adicCompletion F) (η i))) * hγ

/-- **$\Theta$ is invariant under $\omega(w)$ on data with an arbitrary Schwartz archimedean part:** for
$\Phi = (\Phi_\infty, (c_v\bigotimes_if_{v,i})_v)$ with $\Phi_\infty$ any Schwartz function on $F_\infty^{2m}$, $f_{v,i}$
locally constant with compact support and $c_v = 1$, $f_{v,i} = \mathbf 1_{\mathcal O_v}$ for almost all $v$
(`GDatum.IsSchwartzInf`), $\Theta(\omega(w)\Phi) = \Theta(\Phi)$. *Proof:* `opWf_inf_eq`, the substitution
$\xi_i \mapsto 2a_i\xi_i$, $\prod_u|2a_i|_u^{1/2} = 1$, `adelicPoisson_factorizable_pi` and `prod_gammaV_eq_one`. -/
@[kb "weil1964" "§29–§30 (Poisson summation formula) [unverified]"]
theorem thetaDist_gW_schwartz {Φ : GDatum F (2 * m)} (hΦ : Φ.IsSchwartzInf) :
    thetaDist (gW a Φ) = thetaDist Φ :=
  (gW_schwartz_aux a hΦ).2.2

/-! ### Finite components in $S(V_v)$: linearity -/

/-- **Data with a Schwartz archimedean part and finite components in $S(V_v)$** (`IsSchwartzAdm`): $\Phi_\infty$ an
arbitrary Schwartz function on $F_\infty^n$, every $\Phi_v$ in $S(V_v)$ (`Sn`: finite sums of pure tensors of locally
constant compactly supported functions), and $\Phi_v = \mathbf 1_{\mathcal O_v^n}$ for almost all $v$ (`Adm`). -/
def GDatum.IsSchwartzAdm {n : ℕ} (Φ : GDatum F n) : Prop :=
  (∃ G : SchwartzMap (Fin n → mixedSpace F) ℂ, Φ.inf = (G : (Fin n → mixedSpace F) → ℂ)) ∧
    (∀ v, Φ.fin v ∈ (localDataV v).Sn n) ∧ Φ.Adm

lemma GDatum.Adm.update {n : ℕ} {Φ : GDatum F n} (hΦ : Φ.Adm) (v₀ : HeightOneSpectrum (𝓞 F))
    (x : (Fin n → v₀.adicCompletion F) → ℂ) : (GDatum.mk Φ.inf (Function.update Φ.fin v₀ x)).Adm := by
  obtain ⟨T, hT⟩ := hΦ
  refine ⟨insert v₀ T, fun v hv => ?_⟩
  simp only [Finset.mem_insert, not_or] at hv
  simp only [Function.update_of_ne hv.1]
  exact hT v hv.2

/-- Splitting off the place $v_0$: $\Phi(\xi) = \Phi_\infty(\xi)\,\Phi_{v_0}(\xi)\prod_{v\ne v_0}\Phi_v(\xi)$. -/
lemma eval_split {n : ℕ} {Φ : GDatum F n} (hΦ : Φ.Adm) (v₀ : HeightOneSpectrum (𝓞 F)) (ξ : Fin n → F) :
    Φ.eval ξ = Φ.inf (ιInf ξ) * (Φ.fin v₀ (ιV v₀ ξ) * ∏ᶠ (v) (_ : v ≠ v₀), Φ.fin v (ιV v ξ)) := by
  rw [GDatum.eval, mul_finprod_cond_ne v₀ (hΦ.finite_mulSupport ξ)]

lemma eval_update {n : ℕ} {Φ : GDatum F n} (hΦ : Φ.Adm) (v₀ : HeightOneSpectrum (𝓞 F))
    (x : (Fin n → v₀.adicCompletion F) → ℂ) (ξ : Fin n → F) :
    (GDatum.mk Φ.inf (Function.update Φ.fin v₀ x)).eval ξ =
      Φ.inf (ιInf ξ) * (x (ιV v₀ ξ) * ∏ᶠ (v) (_ : v ≠ v₀), Φ.fin v (ιV v ξ)) := by
  rw [eval_split (hΦ.update v₀ x) v₀]
  simp only [Function.update_self]
  congr 2
  refine finprod_congr fun v => finprod_congr fun hv => ?_
  rw [Function.update_of_ne hv]

lemma gW_update (Φ : GDatum F (2 * m)) (v₀ : HeightOneSpectrum (𝓞 F))
    (x : (Fin (2 * m) → v₀.adicCompletion F) → ℂ) :
    gW a (GDatum.mk Φ.inf (Function.update Φ.fin v₀ x)) =
      GDatum.mk (gW a Φ).inf (Function.update (gW a Φ).fin v₀ ((localDataV v₀).opWf (aV a v₀) x)) := by
  show GDatum.mk _ _ = GDatum.mk _ _
  congr 1
  funext v
  by_cases hv : v = v₀
  · subst hv; simp
  · simp only [Function.update_of_ne hv]
    rfl

/-- The statement proved by induction on the places where $\Phi_v$ is not a pure tensor. -/
def GWClaim (Φ : GDatum F (2 * m)) : Prop :=
  Summable Φ.eval ∧ Summable (gW a Φ).eval ∧ thetaDist (gW a Φ) = thetaDist Φ

lemma gWClaim_pure {Φ : GDatum F (2 * m)} (hG : ∃ G : SchwartzMap (Fin (2 * m) → mixedSpace F) ℂ, Φ.inf = (G : (Fin (2 * m) → mixedSpace F) → ℂ))
    (hpure : ∀ v, ∃ (c : ℂ) (f : Fin (2 * m) → v.adicCompletion F → ℂ),
      (∀ i, f i ∈ SBK (v.adicCompletion F)) ∧ Φ.fin v = c • ptensor f)
    (hadm : Φ.Adm) : GWClaim a Φ := by
  obtain ⟨G, hG⟩ := hG
  obtain ⟨T, hT⟩ := hadm
  choose c f hf hcf using hpure
  set c' : HeightOneSpectrum (𝓞 F) → ℂ := fun v => if v ∈ T then c v else 1
  set f' : ∀ v : HeightOneSpectrum (𝓞 F), Fin (2 * m) → v.adicCompletion F → ℂ :=
    fun v => if v ∈ T then f v else fun _ => ballIndV v 0 0
  have hball : ∀ v : HeightOneSpectrum (𝓞 F), ballIndV v 0 0 ∈ SBK (v.adicCompletion F) :=
    fun v => ballIndV_zero_mem_SBK v
  refine gW_schwartz_aux a ⟨G, c', f', T, fun v i => ?_, fun v hv => ?_, ?_⟩
  · by_cases hv : v ∈ T
    · simp only [f', if_pos hv]; exact hf v i
    · simp only [f', if_neg hv]; exact hball v
  · simp [c', f', hv]
  · cases Φ with
    | mk inf fin =>
      simp only at hG hT hcf
      subst hG
      congr 1
      funext v
      by_cases hv : v ∈ T
      · simp only [c', f', if_pos hv]; exact hcf v
      · simp only [c', f', if_neg hv, one_smul]; rw [hT v hv]; rfl

lemma gWClaim_zero {Φ : GDatum F (2 * m)} (hadm : Φ.Adm) (v₀ : HeightOneSpectrum (𝓞 F)) :
    GWClaim a (GDatum.mk Φ.inf (Function.update Φ.fin v₀ 0)) := by
  have h1 : ∀ ξ, (GDatum.mk Φ.inf (Function.update Φ.fin v₀ 0)).eval ξ = 0 := fun ξ => by
    rw [eval_update hadm]; simp
  have h0 : (localDataV v₀).opWf (aV a v₀) 0 = 0 := by
    have := LocalData.opWf_smul (D := localDataV v₀) (a := aV a v₀) 0 0
    simpa using this
  have h2 : ∀ ξ, (gW a (GDatum.mk Φ.inf (Function.update Φ.fin v₀ 0))).eval ξ = 0 := fun ξ => by
    rw [gW_update, h0, eval_update (hadm.gW a)]; simp
  refine ⟨?_, ?_, ?_⟩
  · simp only [funext h1]; exact summable_zero
  · simp only [funext h2]; exact summable_zero
  · rw [thetaDist, thetaDist, tsum_congr h1, tsum_congr h2]

lemma gWClaim_add {Φ : GDatum F (2 * m)} (hadm : Φ.Adm) (v₀ : HeightOneSpectrum (𝓞 F))
    {x y : (Fin (2 * m) → v₀.adicCompletion F) → ℂ} (hx : x ∈ (localDataV v₀).Sn (2 * m))
    (hy : y ∈ (localDataV v₀).Sn (2 * m))
    (Hx : GWClaim a (GDatum.mk Φ.inf (Function.update Φ.fin v₀ x)))
    (Hy : GWClaim a (GDatum.mk Φ.inf (Function.update Φ.fin v₀ y))) :
    GWClaim a (GDatum.mk Φ.inf (Function.update Φ.fin v₀ (x + y))) := by
  have h1 : (GDatum.mk Φ.inf (Function.update Φ.fin v₀ (x + y))).eval =
      (GDatum.mk Φ.inf (Function.update Φ.fin v₀ x)).eval + (GDatum.mk Φ.inf (Function.update Φ.fin v₀ y)).eval := by
    funext ξ
    rw [Pi.add_apply, eval_update hadm, eval_update hadm, eval_update hadm, Pi.add_apply]
    ring
  have hW : (localDataV v₀).opWf (aV a v₀) (x + y) =
      (localDataV v₀).opWf (aV a v₀) x + (localDataV v₀).opWf (aV a v₀) y :=
    LocalData.opWf_add (isOps_V v₀) hx hy
  have h2 : (gW a (GDatum.mk Φ.inf (Function.update Φ.fin v₀ (x + y)))).eval =
      (gW a (GDatum.mk Φ.inf (Function.update Φ.fin v₀ x))).eval +
        (gW a (GDatum.mk Φ.inf (Function.update Φ.fin v₀ y))).eval := by
    funext ξ
    rw [gW_update, gW_update, gW_update, hW, Pi.add_apply, eval_update (hadm.gW a), eval_update (hadm.gW a),
      eval_update (hadm.gW a), Pi.add_apply]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [h1]; exact Hx.1.add Hy.1
  · rw [h2]; exact Hx.2.1.add Hy.2.1
  · rw [thetaDist, thetaDist, h2, h1]
    simp only [Pi.add_apply]
    rw [Summable.tsum_add Hx.2.1 Hy.2.1, Summable.tsum_add Hx.1 Hy.1]
    rw [← thetaDist, ← thetaDist, ← thetaDist, ← thetaDist, Hx.2.2, Hy.2.2]

lemma gWClaim_smul {Φ : GDatum F (2 * m)} (hadm : Φ.Adm) (v₀ : HeightOneSpectrum (𝓞 F)) (t : ℂ)
    {x : (Fin (2 * m) → v₀.adicCompletion F) → ℂ}
    (Hx : GWClaim a (GDatum.mk Φ.inf (Function.update Φ.fin v₀ x))) :
    GWClaim a (GDatum.mk Φ.inf (Function.update Φ.fin v₀ (t • x))) := by
  have h1 : (GDatum.mk Φ.inf (Function.update Φ.fin v₀ (t • x))).eval =
      fun ξ => t * (GDatum.mk Φ.inf (Function.update Φ.fin v₀ x)).eval ξ := by
    funext ξ
    rw [eval_update hadm, eval_update hadm, Pi.smul_apply, smul_eq_mul]
    ring
  have h2 : (gW a (GDatum.mk Φ.inf (Function.update Φ.fin v₀ (t • x)))).eval =
      fun ξ => t * (gW a (GDatum.mk Φ.inf (Function.update Φ.fin v₀ x))).eval ξ := by
    funext ξ
    rw [gW_update, gW_update, LocalData.opWf_smul, eval_update (hadm.gW a), eval_update (hadm.gW a),
      Pi.smul_apply, smul_eq_mul]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [h1]; exact Hx.1.mul_left t
  · rw [h2]; exact Hx.2.1.mul_left t
  · rw [thetaDist, thetaDist, h2, h1, tsum_mul_left, tsum_mul_left, ← thetaDist, ← thetaDist, Hx.2.2]

lemma gWClaim_induct (T : Finset (HeightOneSpectrum (𝓞 F))) : ∀ Φ : GDatum F (2 * m),
    (∃ G : SchwartzMap (Fin (2 * m) → mixedSpace F) ℂ, Φ.inf = (G : (Fin (2 * m) → mixedSpace F) → ℂ)) →
    (∀ v, Φ.fin v ∈ (localDataV v).Sn (2 * m)) →
    (∀ v ∉ T, ∃ (c : ℂ) (f : Fin (2 * m) → v.adicCompletion F → ℂ),
      (∀ i, f i ∈ SBK (v.adicCompletion F)) ∧ Φ.fin v = c • ptensor f) →
    Φ.Adm → GWClaim a Φ := by
  induction T using Finset.induction_on with
  | empty => intro Φ hG _ hp hadm; exact gWClaim_pure a hG (fun v => hp v (Finset.notMem_empty v)) hadm
  | insert v₀ T hv₀ ih =>
    intro Φ hG hS hp hadm
    have key : ∀ x (hx : x ∈ (localDataV v₀).Sn (2 * m)),
        GWClaim a (GDatum.mk Φ.inf (Function.update Φ.fin v₀ x)) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨f, hf, rfl⟩ := hx
        refine ih _ hG (fun v => ?_) (fun v hv => ?_) (hadm.update v₀ _)
        · by_cases h : v = v₀
          · subst h; simp only [Function.update_self]; exact LocalData.ptensor_mem_Sn hf
          · simp only [Function.update_of_ne h]; exact hS v
        · by_cases h : v = v₀
          · subst h; exact ⟨1, f, hf, by simp⟩
          · simp only [Function.update_of_ne h]
            exact hp v (by simp [h, hv])
      | zero => exact gWClaim_zero a hadm v₀
      | add x y hx hy ihx ihy => exact gWClaim_add a hadm v₀ hx hy ihx ihy
      | smul t x hx ihx => exact gWClaim_smul a hadm v₀ t ihx
    have := key (Φ.fin v₀) (hS v₀)
    rwa [Function.update_eq_self] at this

/-- **$\Theta$ is invariant under $\omega(w)$ on admissible data with an arbitrary Schwartz archimedean part and
arbitrary finite components:** for $\Phi = (\Phi_\infty, (\Phi_v)_v)$ with $\Phi_\infty$ any Schwartz function on
$F_\infty^{2m}$, every $\Phi_v \in S(V_v)$ and $\Phi_v = \mathbf 1_{\mathcal O_v^{2m}}$ for almost all $v$
(`GDatum.IsSchwartzAdm`), $\Theta(\omega(w)\Phi) = \Theta(\Phi)$, and both theta series converge absolutely.
*Proof:* induction on the finitely many places where $\Phi_v$ is not a pure tensor, by linearity of $\Phi_v \mapsto
\Theta(\Phi)$ and of $\omega_v(w)$ on $S(V_v)$, down to `thetaDist_gW_schwartz`. -/
@[kb "weil1964" "§29–§30 (Poisson summation formula) [unverified]"]
theorem thetaDist_gW_schwartzAdm {Φ : GDatum F (2 * m)} (hΦ : Φ.IsSchwartzAdm) :
    thetaDist (gW a Φ) = thetaDist Φ := by
  obtain ⟨hG, hS, T, hT⟩ := hΦ
  refine (gWClaim_induct a T Φ hG hS (fun v hv => ⟨1, fun _ => ballIndV v 0 0,
    fun _ => ballIndV_zero_mem_SBK v, ?_⟩) ⟨T, hT⟩).2.2
  rw [hT v hv, one_smul]
  rfl

/-! ### $\mathrm{SL}_2(F)$-invariance on data with a Schwartz archimedean part -/

lemma hasTemperateGrowth_finset_prod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}
    (s : Finset ι) (f : ι → E → ℂ) (h : ∀ i, (f i).HasTemperateGrowth) :
    (fun x => ∏ i ∈ s, f i x).HasTemperateGrowth := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Function.HasTemperateGrowth.const (E := E) (1 : ℂ)
  | insert j s hj ih =>
    simp only [Finset.prod_insert hj]
    exact (h j).mul ih

/-- Coordinatewise multiplication by units, $x \mapsto (u_ix_i)_i$, as a continuous linear equivalence of
$F_\infty^n$. -/
def scaleL {n : ℕ} (u : Fin n → (mixedSpace F)ˣ) : (Fin n → mixedSpace F) ≃L[ℝ] (Fin n → mixedSpace F) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x i => (u i : mixedSpace F) * x i
      invFun := fun x i => ((u i)⁻¹ : (mixedSpace F)ˣ) * x i
      map_add' := fun x y => by funext i; simp [mul_add]
      map_smul' := fun c x => by funext i; simp [mul_smul_comm]
      left_inv := fun x => by funext i; simp [← mul_assoc]
      right_inv := fun x => by funext i; simp [← mul_assoc] }

lemma scaleL_apply {n : ℕ} (u : Fin n → (mixedSpace F)ˣ) (x : Fin n → mixedSpace F) (i : Fin n) :
    scaleL u x i = (u i : mixedSpace F) * x i := rfl

/-- $\omega_\infty(n(b))$ preserves Schwartz functions on $F_\infty^{2m}$. -/
lemma exists_schwartz_opNf (b : mixedSpace F) (G : SchwartzMap (Fin (2 * m) → mixedSpace F) ℂ) :
    ∃ H : SchwartzMap (Fin (2 * m) → mixedSpace F) ℂ,
      (H : (Fin (2 * m) → mixedSpace F) → ℂ) = (localDataInf (F := F)).opNf (aInf a) b G := by
  have he : (fun x : Fin (2 * m) → mixedSpace F => ((localDataInf (F := F)).ψ (b * Qform (aInf a) x) : ℂ)) =
      fun x => ∏ i, (psiInf ((b * ((aInf a i : (mixedSpace F)ˣ) : mixedSpace F)) * x i * x i) : ℂ) := by
    funext x
    rw [LocalData.psi_Qform]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [sq, ← mul_assoc]
    rfl
  have ht : (fun x : Fin (2 * m) → mixedSpace F =>
      ((localDataInf (F := F)).ψ (b * Qform (aInf a) x) : ℂ)).HasTemperateGrowth := by
    rw [he]
    refine hasTemperateGrowth_finset_prod _ _ fun i => ?_
    have hp : (fun x : Fin (2 * m) → mixedSpace F => x i).HasTemperateGrowth :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 * m) => mixedSpace F) i).hasTemperateGrowth
    exact (hasTemperateGrowth_chirpInf _).comp hp
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun x : Fin (2 * m) → mixedSpace F =>
    ((localDataInf (F := F)).ψ (b * Qform (aInf a) x) : ℂ)) G, ?_⟩
  funext x
  rw [SchwartzMap.smulLeftCLM_apply_apply ht, smul_eq_mul]
  rfl

/-- $\omega_\infty(m(t))$, $t \in F_\infty^\times$, preserves Schwartz functions on $F_\infty^{2m}$. -/
lemma exists_schwartz_opMf (t : (mixedSpace F)ˣ) (G : SchwartzMap (Fin (2 * m) → mixedSpace F) ℂ) :
    ∃ H : SchwartzMap (Fin (2 * m) → mixedSpace F) ℂ,
      (H : (Fin (2 * m) → mixedSpace F) → ℂ) = (localDataInf (F := F)).opMf (aInf a) t G := by
  refine ⟨((localDataInf (F := F)).chiV (aInf a) t * ((localDataInf (F := F)).md t : ℂ) ^ m) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (scaleL fun _ => t) G, ?_⟩
  funext x
  simp only [_root_.smul_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    smul_eq_mul, LocalData.opMf]
  rfl

/-- **$\omega_\infty(w)$ through the $n$-variable transform**, at every point of $F_\infty^{2m}$. -/
lemma opWf_inf_apply (Φ : (Fin (2 * m) → mixedSpace F) → ℂ) (y : Fin (2 * m) → mixedSpace F) :
    (localDataInf (F := F)).opWf (aInf a) Φ y =
      (localDataInf (F := F)).gammaV (aInf a) * (localDataInf (F := F)).cB (aInf a) *
        fourierInfPi Φ (fun i => (2 * ((aInf a i : (mixedSpace F)ˣ) : mixedSpace F)) * y i) := by
  rw [opWf]
  congr 1
  simp only [fourierInfPi, muN]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  congr 1
  show ((𝐞 (traceInf (Bform (aInf a) x y)) : Circle) : ℂ) = _
  rw [Bform, traceInf_sum]
  congr 3
  funext i
  congr 1
  ring

/-- The units $2a_i$ of $F_\infty$. -/
def twoAInf : Fin (2 * m) → (mixedSpace F)ˣ := fun i => twoInf * aInf a i

/-- $\omega_\infty(w)$ preserves Schwartz functions on $F_\infty^{2m}$. -/
lemma exists_schwartz_opWf (G : SchwartzMap (Fin (2 * m) → mixedSpace F) ℂ) :
    ∃ H : SchwartzMap (Fin (2 * m) → mixedSpace F) ℂ,
      (H : (Fin (2 * m) → mixedSpace F) → ℂ) = (localDataInf (F := F)).opWf (aInf a) G := by
  obtain ⟨H, hH⟩ := exists_schwartz_fourierInfPi G
  refine ⟨((localDataInf (F := F)).gammaV (aInf a) * (localDataInf (F := F)).cB (aInf a)) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (scaleL (twoAInf a)) H, ?_⟩
  funext y
  rw [opWf_inf_apply]
  simp only [_root_.smul_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    smul_eq_mul, hH]
  congr 2
  funext i
  rw [scaleL_apply, twoAInf, Units.val_mul, twoInf_val]

lemma GDatum.IsSchwartzAdm.gN {Φ : GDatum F (2 * m)} (hΦ : Φ.IsSchwartzAdm) (b : F) :
    (gN a b Φ).IsSchwartzAdm := by
  obtain ⟨⟨G, hG⟩, hS, hadm⟩ := hΦ
  refine ⟨?_, fun v => ?_, hadm.gN a b⟩
  · obtain ⟨H, hH⟩ := exists_schwartz_opNf a (mixedEmbedding F b) G
    exact ⟨H, by rw [hH, ← hG]; rfl⟩
  · exact LocalData.opNf_mem (isOps_V v) _ (hS v)

lemma GDatum.IsSchwartzAdm.gM {Φ : GDatum F (2 * m)} (hΦ : Φ.IsSchwartzAdm) (t : Fˣ) :
    (gM a t Φ).IsSchwartzAdm := by
  obtain ⟨⟨G, hG⟩, hS, hadm⟩ := hΦ
  refine ⟨?_, fun v => ?_, hadm.gM a t⟩
  · obtain ⟨H, hH⟩ := exists_schwartz_opMf a (Units.map (mixedEmbedding F).toMonoidHom t) G
    exact ⟨H, by rw [hH, ← hG]; rfl⟩
  · exact LocalData.opMf_mem (isOps_V v) (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom t) (hS v)

lemma GDatum.IsSchwartzAdm.gW {Φ : GDatum F (2 * m)} (hΦ : Φ.IsSchwartzAdm) : (gW a Φ).IsSchwartzAdm := by
  obtain ⟨⟨G, hG⟩, hS, hadm⟩ := hΦ
  refine ⟨?_, fun v => ?_, hadm.gW a⟩
  · obtain ⟨H, hH⟩ := exists_schwartz_opWf a G
    exact ⟨H, by rw [hH, ← hG]; rfl⟩
  · exact LocalData.opWf_mem (isOps_V v) (hS v)

/-- **The theta distribution is $\mathrm{SL}_2(F)$-invariant on data with an arbitrary Schwartz archimedean part:**
for every admissible datum $\Phi = (\Phi_\infty, (\Phi_v)_v)$ with $\Phi_\infty$ any Schwartz function on $F_\infty^{2m}$ and
every $\Phi_v \in S(V_v)$ (`GDatum.IsSchwartzAdm`), and every $\gamma \in \mathrm{SL}_2(F)$,
$\Theta(\omega(\gamma)\Phi) = \Theta(\Phi)$. This extends `thetaDist_omegaG` (fully factorizable data) to all of
$S(V(\mathbb A))$ with a Schwartz archimedean component; the class is stable under $\omega(n(b))$, $\omega(m(t))$,
$\omega(w)$ (`GDatum.IsSchwartzAdm.gN`, `.gM`, `.gW`). -/
@[kb "weil1964" "§29–§30, Thm. 4 (the distribution is invariant under $\\mathrm{Sp}(X_k)$) [unverified]"]
theorem thetaDist_omegaG_schwartzAdm {Φ : GDatum F (2 * m)} (hΦ : Φ.IsSchwartzAdm) (γ : SL(2, F)) :
    thetaDist (omegaG a γ Φ) = thetaDist Φ := by
  unfold omegaG
  by_cases hc : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  · rw [cellRep_of_c_eq_zero hc, Aof_of_ne (a_ne_zero_of_c_eq_zero hc)]
    show thetaDist (gM a _ (gN a _ Φ)) = _
    rw [thetaDist_gM a (hΦ.2.2.gN a _), thetaDist_gN a hΦ.2.2]
  · rw [cellRep_of_c_ne_zero hc, Aof_of_ne (unit_ne_zero_aux hc)]
    show thetaDist (gN a _ (gM a _ (gW a (gN a _ Φ)))) = _
    have h1 := hΦ.gN a ((γ : Matrix (Fin 2) (Fin 2) F) 1 1 / γ 1 0)
    rw [thetaDist_gN a ((h1.2.2.gW a).gM a _), thetaDist_gM a (h1.2.2.gW a), thetaDist_gW_schwartzAdm a h1,
      thetaDist_gN a hΦ.2.2]

end QuadFormsKB.WeilRep


