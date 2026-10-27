import QuadFormsKB.Tamagawa.Measure.Weil.QuatPoisson
import QuadFormsKB.Tamagawa.Measure.Weil.SL2Tamagawa
import QuadFormsKB.Tamagawa.Measure.Weil.DHatVolume

/-!
# The Gaussian Poisson formula on $\mathbb A_F^\iota$ twisted by $\mathrm{GL}_\iota(\mathbb A_F)$

$F$ a number field, $\iota$ a finite index set, $G$ the standard Gaussian on $F_\infty^\iota$ (`gV`), $\beta$ the trace form
$\beta(y,z) = \sum_i\operatorname{Tr}_{F_\infty/\mathbb R}(y_iz_i)$ on $F_\infty^\iota$ (`betaV`). For $M\in\mathrm{GL}_\iota(\mathbb A_F)$ with
components $M_\infty$, $M_f$ (`glInf`, `glFin`) and an open subgroup $\Lambda\subseteq\mathbb A_f^\iota$ with bounded denominators,
the twisted theta sum is
$$\Theta_\Lambda(M) = \sum_{\xi\in F^\iota,\ M_f\xi\in\Lambda}G(M_\infty\xi)\qquad(\texttt{glTheta}).$$

* **`glTheta_poisson`** (lattice Poisson): $\|\det M\|_{\mathbb A}\,\Theta_\Lambda(M) = \mu_f(\Lambda)\sum_{\eta\in L^\vee}G(\eta)$, $L^\vee$
  the $\beta$-dual of the lattice $L = M_\infty\{\xi : M_f\xi\in\Lambda\}$ (`glDualSet`). Proof as for $(\mathbb H\otimes\mathbb A)^\times$
  (`quatTheta_poisson`): `poisson_basisGauss`, the covolume $\mu_\infty(P)\mu_f(U) = 1$ (`fundamentalDomain_mul_eq_one`), the
  scalings `addHaar_image_linearMap` and `map_mulVec_muFinVec`.
* **`glTheta_poisson_dual`** (the adelic Poisson formula for the Gaussian): if $M'^{\mathsf T}M = 1$, then
  $$\Theta_{\hat{\mathcal O}^\iota}(M) = \|\det M\|_{\mathbb A}^{-1}\,\mu_f(\hat{\mathcal O}^\iota)\,\Theta_{\hat{\mathfrak d}^{-1,\iota}}(M').$$
  *No identification of dual lattices is needed*: the two lattices $L_1$ (for $M$, $\hat{\mathcal O}$) and $L_2$ (for $M'$,
  $\hat{\mathfrak d}^{-1}$) satisfy $L_2\subseteq L_1^\vee$ and $L_1\subseteq L_2^\vee$, because
  $\beta(M_\infty\xi, M'_\infty\eta) = \operatorname{Tr}_{F/\mathbb Q}(\xi\cdot\eta)$ and $\xi\cdot\eta = (M_f\xi)\cdot(M'_f\eta)\in
  F\cap\hat{\mathfrak d}^{-1} = \mathfrak d^{-1}$. Poisson for both lattices gives
  $\Theta_1\ge c_1^{-1}\Theta_2\ge c_1^{-1}c_2^{-1}\Theta_1$, and $c_1c_2 = (\mu_f(\hat{\mathcal O})\mu_f(\hat{\mathfrak d}^{-1}))^{-|\iota|} = 1$
  (`muFinVec_OHatVec_mul_DHatVec`), so all are equal.
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology Set NumberField.mixedEmbedding Matrix
open scoped ENNReal NNReal Classical

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]

set_option synthInstance.maxHeartbeats 400000

local notation "V" => mixedSpace F
local notation "AF" => FiniteAdeleRing (𝓞 F) F

/-! ### Bounded denominators -/

theorem sum_mem_OHat {κ : Type*} (s : Finset κ) {f : κ → AF} (h : ∀ k ∈ s, f k ∈ OHat) : ∑ k ∈ s, f k ∈ OHat :=
  Finset.sum_induction f (· ∈ OHat) (fun _ _ => add_mem_OHat) zero_mem_OHat h

/-- A matrix over $\mathbb A_f$ has bounded denominators: $eA$ is integral for some integer $e\ne0$. -/
theorem exists_nat_mul_mem_OHat_matrix (A : Matrix ι ι AF) :
    ∃ e : ℕ, e ≠ 0 ∧ ∀ i j, (e : AF) * A i j ∈ OHat := by
  choose d hd0 hd using fun p : ι × ι => exists_nat_mul_mem_OHat (A p.1 p.2)
  refine ⟨∏ p, d p, Finset.prod_ne_zero_iff.mpr fun p _ => hd0 p, fun i j => ?_⟩
  rw [← Finset.prod_erase_mul Finset.univ d (Finset.mem_univ (i, j))]
  exact natCast_mul_mul_mem_OHat (hd (i, j)) _

/-- $U_A(\Lambda) = \{c\in\mathbb A_f^\iota : Ac\in\Lambda\}$. -/
def twistSub (A : Matrix ι ι AF) (Λ : AddSubgroup (ι → AF)) : AddSubgroup (ι → AF) :=
  Λ.comap (Matrix.mulVecLin A).toAddMonoidHom

theorem mem_twistSub {A : Matrix ι ι AF} {Λ : AddSubgroup (ι → AF)} {c : ι → AF} :
    c ∈ twistSub A Λ ↔ A *ᵥ c ∈ Λ := Iff.rfl

theorem twistSub_coe (A : Matrix ι ι AF) (Λ : AddSubgroup (ι → AF)) :
    (twistSub A Λ : Set (ι → AF)) = A.mulVec ⁻¹' (Λ : Set (ι → AF)) := rfl

theorem isOpen_twistSub (A : Matrix ι ι AF) {Λ : AddSubgroup (ι → AF)} (hΛ : IsOpen (Λ : Set (ι → AF))) :
    IsOpen (twistSub A Λ : Set (ι → AF)) :=
  hΛ.preimage (continuous_const.matrix_mulVec continuous_id)

theorem twistSub_upper (A : GL ι AF) {Λ : AddSubgroup (ι → AF)} {d : ℕ} (hd0 : d ≠ 0)
    (hd : ∀ c ∈ Λ, ∀ i, (d : AF) * c i ∈ OHat) :
    ∃ e : ℕ, e ≠ 0 ∧ ∀ c ∈ twistSub (A : Matrix ι ι AF) Λ, ∀ i, (e : AF) * c i ∈ OHat := by
  obtain ⟨e, he0, he⟩ := exists_nat_mul_mem_OHat_matrix ((A⁻¹ : GL ι AF) : Matrix ι ι AF)
  refine ⟨e * d, Nat.mul_ne_zero he0 hd0, fun c hc i => ?_⟩
  have hy := hd _ (mem_twistSub.mp hc)
  have hc' : c = ((A⁻¹ : GL ι AF) : Matrix ι ι AF) *ᵥ ((A : Matrix ι ι AF) *ᵥ c) := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  generalize (A : Matrix ι ι AF) *ᵥ c = y at hy hc'
  subst hc'
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Nat.cast_mul]
  refine sum_mem_OHat _ fun k _ => ?_
  rw [show (e : AF) * (d : AF) * (((A⁻¹ : GL ι AF) : Matrix ι ι AF) i k * y k) =
    ((e : AF) * ((A⁻¹ : GL ι AF) : Matrix ι ι AF) i k) * ((d : AF) * y k) by ring]
  exact mul_mem_OHat (he i k) (hy k)

theorem algebraMap_int_mem_OHat (ξ : 𝓞 F) : algebraMap F AF (ξ : F) ∈ OHat :=
  (algebraMap_mem_OHat_iff _).mpr ⟨ξ, rfl⟩

theorem twistSub_lower (A : GL ι AF) {Λ : AddSubgroup (ι → AF)} {d : ℕ} (hd0 : d ≠ 0)
    (hd : ∀ c : ι → AF, (∀ i, c i ∈ OHat) → (fun i => (d : AF) * c i) ∈ Λ) :
    ∃ e : ℕ, e ≠ 0 ∧ ∀ ξ : ι → 𝓞 F, jFin F ι (fun i => (e : F) * (ξ i : F)) ∈ twistSub (A : Matrix ι ι AF) Λ := by
  obtain ⟨e, he0, he⟩ := exists_nat_mul_mem_OHat_matrix (A : Matrix ι ι AF)
  refine ⟨d * e, Nat.mul_ne_zero hd0 he0, fun ξ => ?_⟩
  rw [mem_twistSub]
  have hc : ∀ k, ∑ j, ((e : AF) * (A : Matrix ι ι AF) k j) * algebraMap F AF (ξ j : F) ∈ OHat := fun k =>
    sum_mem_OHat _ fun j _ => mul_mem_OHat (he k j) (algebraMap_int_mem_OHat _)
  have := hd _ hc
  convert this using 1
  funext k
  simp only [Matrix.mulVec, dotProduct, jFin_apply, map_mul, map_natCast, Nat.cast_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-! ### The twisted theta sum and its lattice -/

/-- The archimedean action of $A\in\mathrm{GL}_\iota(F_\infty)$ on $F_\infty^\iota$, as a real linear equivalence. -/
def glInfEquiv (A : GL ι V) : (ι → V) ≃ₗ[ℝ] (ι → V) where
  toFun z := (A : Matrix ι ι V) *ᵥ z
  invFun z := ((A⁻¹ : GL ι V) : Matrix ι ι V) *ᵥ z
  map_add' z w := Matrix.mulVec_add _ _ _
  map_smul' c z := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, mul_smul_comm]
  left_inv z := by
    show ((A⁻¹ : GL ι V) : Matrix ι ι V) *ᵥ ((A : Matrix ι ι V) *ᵥ z) = z
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  right_inv z := by
    show (A : Matrix ι ι V) *ᵥ (((A⁻¹ : GL ι V) : Matrix ι ι V) *ᵥ z) = z
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem glInfEquiv_apply (A : GL ι V) (z : ι → V) : glInfEquiv A z = (A : Matrix ι ι V) *ᵥ z := rfl

/-- The real determinant of $z\mapsto Az$ on $F_\infty^\iota$ is $\det_{\mathbb R}(\det A\cdot)$. -/
theorem det_glInfEquiv (A : GL ι V) :
    LinearMap.det (glInfEquiv A).toLinearMap = LinearMap.det (LinearMap.mulLeft ℝ (A : Matrix ι ι V).det) := by
  have h : (glInfEquiv A).toLinearMap = (Matrix.mulVecLin (A : Matrix ι ι V)).restrictScalars ℝ := rfl
  rw [h, LinearMap.det_restrictScalars, show Matrix.mulVecLin (A : Matrix ι ι V) = Matrix.toLin' (A : Matrix ι ι V)
    from rfl, LinearMap.det_toLin', Algebra.norm_apply]
  rfl

/-- **$\mu_\infty(AS) = |\det_{\mathbb R}A|\,\mu_\infty(S)$** on $F_\infty^\iota$. -/
theorem muInfVec_glInfEquiv_image (A : GL ι V) (S : Set (ι → V)) :
    muInfVec F ι (glInfEquiv A '' S) =
      ENNReal.ofReal |LinearMap.det (LinearMap.mulLeft ℝ (A : Matrix ι ι V).det)| * muInfVec F ι S := by
  rw [← det_glInfEquiv]
  exact Measure.addHaar_image_linearMap _ _ _

/-- **The twisted theta sum** $\Theta_\Lambda(M) = \sum_{\xi\in F^\iota,\ M_f\xi\in\Lambda}G(M_\infty\xi)$. -/
def glTheta (M : GL ι (Adeles F)) (Λ : AddSubgroup (ι → AF)) : ℝ≥0∞ :=
  ∑' ξ : ι → F, (Λ : Set (ι → AF)).indicator (fun _ => (1 : ℝ≥0∞)) ((glFin M : Matrix ι ι AF) *ᵥ jFin F ι ξ) *
    ENNReal.ofReal (gV ((glInf M : Matrix ι ι V) *ᵥ jInf F ι ξ))

/-- **The theta sum is a lattice sum**: $\Theta_\Lambda(M) = \sum_{w\in L_U}G(M_\infty w)$, $U = M_f^{-1}\Lambda$. -/
theorem glTheta_eq_tsum_lattice (M : GL ι (Adeles F)) (Λ : AddSubgroup (ι → AF)) :
    glTheta M Λ = ∑' w : adelicLat (twistSub (glFin M : Matrix ι ι AF) Λ),
      ENNReal.ofReal (gV ((glInf M : Matrix ι ι V) *ᵥ (w : ι → V))) := by
  set U := twistSub (glFin M : Matrix ι ι AF) Λ
  set f : (ι → V) → ℝ≥0∞ := fun w => ENNReal.ofReal (gV ((glInf M : Matrix ι ι V) *ᵥ w))
  have h1 : ∀ c : ι → F, (Λ : Set (ι → AF)).indicator (fun _ => (1 : ℝ≥0∞))
      ((glFin M : Matrix ι ι AF) *ᵥ jFin F ι c) * f (jInf F ι c) =
      ((U.comap (jFin F ι) : Set (ι → F))).indicator (fun c => f (jInf F ι c)) c := by
    intro c
    by_cases h : (glFin M : Matrix ι ι AF) *ᵥ jFin F ι c ∈ Λ
    · rw [indicator_of_mem (show _ ∈ (Λ : Set (ι → AF)) from h), one_mul,
        indicator_of_mem (show c ∈ (U.comap (jFin F ι) : Set _) from h)]
    · rw [indicator_of_notMem (show _ ∉ (Λ : Set (ι → AF)) from h), zero_mul,
        indicator_of_notMem (show c ∉ (U.comap (jFin F ι) : Set _) from h)]
  let e : (U.comap (jFin F ι) : Set (ι → F)) ≃ adelicLat U :=
    Equiv.ofBijective (fun c => ⟨jInf F ι c.1, jInf_mem_adelicLat U c.2⟩)
      ⟨fun c₁ c₂ h => Subtype.ext (jInf_injective (congrArg Subtype.val h)),
        fun ⟨w, ξ, hξ, hw⟩ => ⟨⟨ξ, hξ⟩, Subtype.ext hw⟩⟩
  calc glTheta M Λ = ∑' c, ((U.comap (jFin F ι) : Set (ι → F))).indicator (fun c => f (jInf F ι c)) c :=
        tsum_congr h1
    _ = ∑' c : (U.comap (jFin F ι) : Set (ι → F)), f (jInf F ι c) := (tsum_subtype _ _).symm
    _ = ∑' w : adelicLat U, f w := e.tsum_eq (fun w => f w)

/-- The $\beta$-dual of the lattice $L = M_\infty L_U$, as a set. -/
def glDualSet (M : GL ι (Adeles F)) (Λ : AddSubgroup (ι → AF)) : Set (ι → V) :=
  {η | ∀ w ∈ adelicLat (twistSub (glFin M : Matrix ι ι AF) Λ), ∃ n : ℤ,
    betaV F ι η ((glInf M : Matrix ι ι V) *ᵥ w) = n}

theorem ideleNorm_det_eq (M : GL ι (Adeles F)) :
    ideleNorm F (GeneralLinearGroup.det M) =
      |LinearMap.det (LinearMap.mulLeft ℝ (glInf M : Matrix ι ι V).det)| *
        (distribHaarChar AF (GeneralLinearGroup.det (glFin M)) : ℝ) := by
  have hfin : (∏ᶠ v, (modAt (GeneralLinearGroup.det (glFin M)) v : ℝ)) =
      (distribHaarChar AF (GeneralLinearGroup.det (glFin M)) : ℝ) := by
    rw [distribHaarChar_finiteAdeleRing]
    exact (MonoidHom.map_finprod NNReal.toRealHom.toMonoidHom (mulSupport_modAt_finite _)).symm
  rw [ideleNorm, infPart_det, finPart_det, hfin]

set_option maxHeartbeats 1000000 in
/-- **The $\mathrm{GL}_\iota(\mathbb A_F)$-twisted lattice Poisson formula for the Gaussian**:
$\|\det M\|_{\mathbb A}\,\Theta_\Lambda(M) = \mu_f(\Lambda)\sum_{\eta\in L^\vee}G(\eta)$, for $\Lambda$ open with bounded denominators. -/
theorem glTheta_poisson (M : GL ι (Adeles F)) {Λ : AddSubgroup (ι → AF)} (hΛ : IsOpen (Λ : Set (ι → AF)))
    {d₁ : ℕ} (hd₁ : d₁ ≠ 0) (hup : ∀ c ∈ Λ, ∀ i, (d₁ : AF) * c i ∈ OHat)
    {d₂ : ℕ} (hd₂ : d₂ ≠ 0) (hlow : ∀ c : ι → AF, (∀ i, c i ∈ OHat) → (fun i => (d₂ : AF) * c i) ∈ Λ) :
    ENNReal.ofReal (ideleNorm F (GeneralLinearGroup.det M)) * glTheta M Λ =
      muFinVec F ι (Λ : Set (ι → AF)) * ∑' η : glDualSet M Λ, ENNReal.ofReal (gV (η : ι → V)) := by
  set U := twistSub (glFin M : Matrix ι ι AF) Λ
  obtain ⟨e₁, he₁, hU₁⟩ := twistSub_upper (glFin M) hd₁ hup
  obtain ⟨e₂, he₂, hU₂⟩ := twistSub_lower (glFin M) hd₂ hlow
  have : DiscreteTopology (adelicLat U) := discreteTopology_adelicLat U he₁ hU₁
  have : IsZLattice ℝ (adelicLat U) := isZLattice_adelicLat U he₂ hU₂
  set b' := latBasis (adelicLat U)
  have hb' : Submodule.span ℤ (Set.range b') = adelicLat U := span_latBasis _
  set e := glInfEquiv (glInf M)
  set b'' := b'.map e
  -- the theta sum as a sum over span b''
  have hθ : glTheta M Λ = ∑' z : Submodule.span ℤ (Set.range b''), ENNReal.ofReal (gV (z : ι → V)) := by
    rw [glTheta_eq_tsum_lattice, tsum_span_basis b'' (fun z => ENNReal.ofReal (gV z))]
    have h1 := tsum_span_basis b' (fun w => ENNReal.ofReal (gV ((glInf M : Matrix ι ι V) *ᵥ w)))
    rw [hb'] at h1
    rw [h1]
    refine tsum_congr fun k => ?_
    congr 2
    rw [show (glInf M : Matrix ι ι V) *ᵥ (∑ j, (k j : ℝ) • b' j) = e (∑ j, (k j : ℝ) • b' j) from rfl, map_sum]
    simp only [map_smul, b'', Module.Basis.map_apply]
  -- the dual sets agree
  have hspan : Submodule.span ℤ (Set.range b'') = (adelicLat U).map (e.toLinearMap.restrictScalars ℤ) := by
    have hr : Set.range b'' = (e.toLinearMap.restrictScalars ℤ) '' Set.range b' := by
      rw [← Set.range_comp]; rfl
    rw [hr, Submodule.span_image, hb']
  have hdual : ((betaV F ι).dualSubmodule (Submodule.span ℤ (Set.range b'')) : Set (ι → V)) = glDualSet M Λ := by
    ext η
    rw [SetLike.mem_coe, LinearMap.BilinForm.mem_dualSubmodule, hspan]
    simp only [Submodule.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Submodule.mem_one]
    refine forall₂_congr fun w _ => ?_
    change (∃ n : ℤ, algebraMap ℤ ℝ n = betaV F ι η ((glInf M : Matrix ι ι V) *ᵥ w)) ↔ _
    exact ⟨fun ⟨n, hn⟩ => ⟨n, by rw [← hn]; simp⟩, fun ⟨n, hn⟩ => ⟨n, by rw [hn]; simp⟩⟩
  have hP := poisson_basisGauss b''
  have hiff : ∀ η, η ∈ (betaV F ι).dualSubmodule (Submodule.span ℤ (Set.range b'')) ↔ η ∈ glDualSet M Λ :=
    fun η => by rw [← SetLike.mem_coe, hdual]
  have hdualsum : (∑' η : (betaV F ι).dualSubmodule (Submodule.span ℤ (Set.range b'')),
      ENNReal.ofReal (gV (η : ι → V))) = ∑' η : glDualSet M Λ, ENNReal.ofReal (gV (η : ι → V)) :=
    (Equiv.subtypeEquivRight hiff).tsum_eq (fun η : glDualSet M Λ => ENNReal.ofReal (gV (η : ι → V)))
  rw [hdualsum] at hP
  -- the covolume
  have hcov : muInfVec F ι b''.parallelepiped =
      ENNReal.ofReal |LinearMap.det (LinearMap.mulLeft ℝ (glInf M : Matrix ι ι V).det)| *
        muInfVec F ι b'.parallelepiped := by
    rw [Module.Basis.parallelepiped_map, TopologicalSpace.PositiveCompacts.coe_map]
    exact muInfVec_glInfEquiv_image (glInf M) _
  have hfd : muInfVec F ι b'.parallelepiped * muFinVec F ι (U : Set (ι → AF)) = 1 := by
    rw [Module.Basis.coe_parallelepiped,
      ← measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped b' (muInfVec F ι))]
    exact fundamentalDomain_mul_eq_one U b' hb' (isOpen_twistSub _ hΛ)
  have hUvol : muFinVec F ι (U : Set (ι → AF)) =
      ENNReal.ofReal (distribHaarChar AF (GeneralLinearGroup.det (glFin M)) : ℝ)⁻¹ *
        muFinVec F ι (Λ : Set (ι → AF)) := by
    have hm : Measurable (glFin M : Matrix ι ι AF).mulVec :=
      (continuous_const.matrix_mulVec continuous_id).measurable
    rw [twistSub_coe, ← Measure.map_apply hm hΛ.measurableSet, map_mulVec_muFinVec, Measure.smul_apply,
      ENNReal.smul_def, smul_eq_mul]
    congr 1
    rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_inv]
  rw [hUvol] at hfd
  set nI := |LinearMap.det (LinearMap.mulLeft ℝ (glInf M : Matrix ι ι V).det)|
  set nF := (distribHaarChar AF (GeneralLinearGroup.det (glFin M)) : ℝ)
  have hnI : 0 < nI := by
    simp only [nI]
    rw [abs_pos]
    exact det_mulLeft_ne_zero_of_isUnit (GeneralLinearGroup.det (glInf M)).isUnit
  have hnF : 0 < nF := NNReal.coe_pos.mpr distribHaarChar_pos
  set A := muFinVec F ι (Λ : Set (ι → AF))
  set cI := ENNReal.ofReal nI
  set cF := ENNReal.ofReal nF
  have hcI0 : cI ≠ 0 := by simp [cI, hnI]
  have hcF0 : cF ≠ 0 := by simp [cF, hnF]
  have hcIT : cI ≠ ⊤ := ENNReal.ofReal_ne_top
  have hcFT : cF ≠ ⊤ := ENNReal.ofReal_ne_top
  have hinvF : ENNReal.ofReal nF⁻¹ = cF⁻¹ := ENNReal.ofReal_inv_of_pos hnF
  rw [hinvF] at hfd
  have hP' : muInfVec F ι b'.parallelepiped = (cF⁻¹ * A)⁻¹ := ENNReal.eq_inv_of_mul_eq_one_left hfd
  have hN : ENNReal.ofReal (ideleNorm F (GeneralLinearGroup.det M)) = cI * cF := by
    rw [ideleNorm_det_eq, ENNReal.ofReal_mul hnI.le]
  rw [hθ, hP, hcov, hP', hN, ← mul_assoc]
  congr 1
  rw [ENNReal.mul_inv (Or.inl hcI0) (Or.inl hcIT), inv_inv,
    show cI * cF * (cI⁻¹ * (cF⁻¹ * A)) = (cI * cI⁻¹) * (cF * cF⁻¹) * A by ring,
    ENNReal.mul_inv_cancel hcI0 hcIT, ENNReal.mul_inv_cancel hcF0 hcFT, one_mul, one_mul]

/-! ### The dual pair $(M,\hat{\mathcal O})$, $(M',\hat{\mathfrak d}^{-1})$ with $M'^{\mathsf T}M = 1$ -/

variable (F ι) in
/-- $\hat{\mathcal O}^\iota$ as an additive subgroup of $\mathbb A_f^\iota$. -/
def OHatVecSub : AddSubgroup (ι → AF) where
  carrier := {c | ∀ i, c i ∈ OHat}
  add_mem' := fun ha hb i => add_mem_OHat (ha i) (hb i)
  zero_mem' := fun _ => zero_mem_OHat
  neg_mem' := fun ha i => neg_mem_OHat (ha i)

theorem coe_OHatVecSub : (OHatVecSub F ι : Set (ι → AF)) = OHatVec := by
  ext c; simp [OHatVecSub, OHatVec]

theorem coe_DHatVecSub : (DHatVecSub F ι : Set (ι → AF)) = {c | ∀ i, c i ∈ DHat} := rfl

theorem isOpen_OHatVecSub : IsOpen (OHatVecSub F ι : Set (ι → AF)) := by
  rw [coe_OHatVecSub]; exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_OHat

theorem sum_mem_DHat {κ : Type*} (s : Finset κ) {f : κ → AF} (h : ∀ k ∈ s, f k ∈ DHat) : ∑ k ∈ s, f k ∈ DHat :=
  Finset.sum_induction f (· ∈ DHat) (fun _ _ => add_mem_DHat) zero_mem_DHat h

/-- $b\cdot a\in\hat{\mathfrak d}^{-1}$ for $a\in\hat{\mathcal O}^\iota$, $b\in\hat{\mathfrak d}^{-1,\iota}$. -/
theorem dotProduct_mem_DHat {a b : ι → AF} (ha : ∀ i, a i ∈ OHat) (hb : ∀ i, b i ∈ DHat) :
    b ⬝ᵥ a ∈ DHat := by
  refine sum_mem_DHat _ fun i _ => ?_
  rw [mul_comm]; exact mul_mem_DHat (ha i) (hb i)

/-- An element $t\in F$ with $t\in\hat{\mathfrak d}^{-1}$ has $\operatorname{Tr}_{F/\mathbb Q}t\in\mathbb Z$. -/
theorem trace_int_of_mem_DHat {t : F} (ht : algebraMap F AF t ∈ DHat) :
    ∃ n : ℤ, ((Algebra.trace ℚ F t : ℚ) : ℝ) = n := by
  have h := (FractionalIdeal.mem_dual one_ne_zero).mp ((algebraMap_mem_DHat_iff t).mp ht) 1
    (FractionalIdeal.one_mem_one _)
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  rw [Algebra.traceForm_apply, mul_one] at hn
  rw [← hn]
  simp

theorem glInf_coe (M : GL ι (Adeles F)) :
    (glInf M : Matrix ι ι V) = (M : Matrix ι ι (Adeles F)).map (RingHom.fst V AF) := rfl

theorem glFin_coe (M : GL ι (Adeles F)) :
    (glFin M : Matrix ι ι AF) = (M : Matrix ι ι (Adeles F)).map (RingHom.snd V AF) := rfl

/-- For $M'^{\mathsf T}M = 1$: $\beta(M'_\infty\eta, M_\infty\xi) = \operatorname{Tr}_{F/\mathbb Q}(\eta\cdot\xi)$. -/
theorem betaV_glInf_pair {M M' : GL ι (Adeles F)} (h : (M' : Matrix ι ι (Adeles F))ᵀ * M = 1) (η ξ : ι → F) :
    betaV F ι ((glInf M' : Matrix ι ι V) *ᵥ jInf F ι η) ((glInf M : Matrix ι ι V) *ᵥ jInf F ι ξ) =
      ((Algebra.trace ℚ F (η ⬝ᵥ ξ) : ℚ) : ℝ) := by
  have h1 : (glInf M' : Matrix ι ι V)ᵀ * (glInf M : Matrix ι ι V) = 1 := by
    rw [glInf_coe, glInf_coe, ← Matrix.transpose_map, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [betaV_mulVec, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, betaV_apply, dotProduct, map_sum, Rat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [jInf_apply, jInf_apply, ← map_mul, Analysis.traceInf_mixedEmbedding]

/-- For $M'^{\mathsf T}M = 1$: $\eta\cdot\xi = (M'_f\eta)\cdot(M_f\xi)$ in $\mathbb A_f$. -/
theorem algebraMap_dotProduct_pair {M M' : GL ι (Adeles F)} (h : (M' : Matrix ι ι (Adeles F))ᵀ * M = 1)
    (η ξ : ι → F) :
    algebraMap F AF (η ⬝ᵥ ξ) =
      ((glFin M' : Matrix ι ι AF) *ᵥ jFin F ι η) ⬝ᵥ ((glFin M : Matrix ι ι AF) *ᵥ jFin F ι ξ) := by
  have h1 : (glFin M' : Matrix ι ι AF)ᵀ * (glFin M : Matrix ι ι AF) = 1 := by
    rw [glFin_coe, glFin_coe, ← Matrix.transpose_map, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  exact RingHom.map_dotProduct (algebraMap F AF) η ξ

/-- **The easy inclusion** $M'_\infty L_{U'}\subseteq L^\vee$: if $M'^{\mathsf T}M = 1$ and $b\cdot a\in\hat{\mathfrak d}^{-1}$ for
$a\in\Lambda$, $b\in\Lambda'$, then $M'_\infty\eta\in L^\vee$ for every $\eta\in F^\iota$ with $M'_f\eta\in\Lambda'$. -/
theorem mem_glDualSet_of_pair {M M' : GL ι (Adeles F)} (h : (M' : Matrix ι ι (Adeles F))ᵀ * M = 1)
    {Λ Λ' : AddSubgroup (ι → AF)} (hΛ : ∀ a ∈ Λ, ∀ b ∈ Λ', b ⬝ᵥ a ∈ DHat) {η : ι → F}
    (hη : (glFin M' : Matrix ι ι AF) *ᵥ jFin F ι η ∈ Λ') :
    (glInf M' : Matrix ι ι V) *ᵥ jInf F ι η ∈ glDualSet M Λ := by
  rintro w ⟨ξ, hξ, rfl⟩
  rw [betaV_glInf_pair h]
  exact trace_int_of_mem_DHat (by rw [algebraMap_dotProduct_pair h]; exact hΛ _ hξ _ hη)

/-- $\Theta_{\Lambda'}(M')\le\sum_{\eta\in L^\vee}G(\eta)$ under the hypotheses of `mem_glDualSet_of_pair`. -/
theorem glTheta_le_dual {M M' : GL ι (Adeles F)} (h : (M' : Matrix ι ι (Adeles F))ᵀ * M = 1)
    {Λ Λ' : AddSubgroup (ι → AF)} (hΛ : ∀ a ∈ Λ, ∀ b ∈ Λ', b ⬝ᵥ a ∈ DHat) :
    glTheta M' Λ' ≤ ∑' η : glDualSet M Λ, ENNReal.ofReal (gV (η : ι → V)) := by
  rw [glTheta_eq_tsum_lattice]
  have hmem : ∀ w : adelicLat (twistSub (glFin M' : Matrix ι ι AF) Λ'),
      (glInf M' : Matrix ι ι V) *ᵥ (w : ι → V) ∈ glDualSet M Λ := by
    rintro ⟨w, ξ, hξ, rfl⟩
    exact mem_glDualSet_of_pair h hΛ hξ
  have hinj : Function.Injective (fun w : adelicLat (twistSub (glFin M' : Matrix ι ι AF) Λ') =>
      (⟨_, hmem w⟩ : glDualSet M Λ)) := by
    intro w₁ w₂ h12
    exact Subtype.ext ((glInfEquiv (glInf M')).injective (congrArg Subtype.val h12))
  exact ENNReal.tsum_comp_le_tsum_of_injective hinj (fun η : glDualSet M Λ => ENNReal.ofReal (gV (η : ι → V)))

theorem det_mul_det_of_pair {M M' : GL ι (Adeles F)} (h : (M' : Matrix ι ι (Adeles F))ᵀ * M = 1) :
    GeneralLinearGroup.det M * GeneralLinearGroup.det M' = 1 := by
  refine Units.ext ?_
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
  rw [Units.val_mul, GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_det_apply, mul_comm, this,
    Units.val_one]

/-- **The adelic Poisson formula for the Gaussian, twisted by $\mathrm{GL}_\iota(\mathbb A_F)$**: for $M, M'\in\mathrm{GL}_\iota(\mathbb A_F)$
with $M'^{\mathsf T}M = 1$,
$$\|\det M\|_{\mathbb A}\sum_{\xi\in F^\iota,\ M_f\xi\in\hat{\mathcal O}^\iota}G(M_\infty\xi) =
  \mu_f(\hat{\mathcal O}^\iota)\sum_{\eta\in F^\iota,\ M'_f\eta\in\hat{\mathfrak d}^{-1,\iota}}G(M'_\infty\eta),$$
i.e. $\|\det M\|_{\mathbb A}\sum_\xi\Phi_0(M\xi) = \sum_\eta\hat\Phi_0(M'\eta)$ for $\Phi_0 = G\otimes\mathbf 1_{\hat{\mathcal O}^\iota}$ and its
transform $\hat\Phi_0 = \mu_f(\hat{\mathcal O}^\iota)\,G\otimes\mathbf 1_{\hat{\mathfrak d}^{-1,\iota}}$ for the character
$\psi(x\cdot y)$ and the self-dual measure. Proof: the squeeze described in the module docstring. -/
@[kb "weil1982" "§2.1, Poisson formula on X_A (the theta series of X_A) [unverified page]"]
theorem glTheta_poisson_dual {M M' : GL ι (Adeles F)} (h : (M' : Matrix ι ι (Adeles F))ᵀ * M = 1) :
    ENNReal.ofReal (ideleNorm F (GeneralLinearGroup.det M)) * glTheta M (OHatVecSub F ι) =
      muFinVec F ι OHatVec * glTheta M' (DHatVecSub F ι) := by
  obtain ⟨d, hd0, hd⟩ := exists_nat_mul_DHat_subset_OHat (F := F)
  have hOup : ∀ c ∈ OHatVecSub F ι, ∀ i, ((1 : ℕ) : AF) * c i ∈ OHat := fun c hc i => by
    rw [Nat.cast_one, one_mul]; exact hc i
  have hOlow : ∀ c : ι → AF, (∀ i, c i ∈ OHat) → (fun i => ((1 : ℕ) : AF) * c i) ∈ OHatVecSub F ι :=
    fun c hc i => by simp only [Nat.cast_one, one_mul]; exact hc i
  have hDup : ∀ c ∈ DHatVecSub F ι, ∀ i, (d : AF) * c i ∈ OHat := fun c hc i => hd _ (hc i)
  have hDlow : ∀ c : ι → AF, (∀ i, c i ∈ OHat) → (fun i => ((1 : ℕ) : AF) * c i) ∈ DHatVecSub F ι :=
    fun c hc i => by simp only [Nat.cast_one, one_mul]; exact OHat_subset_DHat (hc i)
  have P1 := glTheta_poisson M isOpen_OHatVecSub one_ne_zero hOup one_ne_zero hOlow
  have P2 := glTheta_poisson M' isOpen_DHatVec hd0 hDup one_ne_zero hDlow
  have hT : (M : Matrix ι ι (Adeles F))ᵀ * M' = 1 := by
    have := congrArg Matrix.transpose h
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  have I1 := glTheta_le_dual (M := M) (M' := M') h (Λ := OHatVecSub F ι) (Λ' := DHatVecSub F ι)
    (fun a ha b hb => dotProduct_mem_DHat ha hb)
  have I2 := glTheta_le_dual (M := M') (M' := M) hT (Λ := DHatVecSub F ι) (Λ' := OHatVecSub F ι)
    (fun a ha b hb => by rw [dotProduct_comm]; exact dotProduct_mem_DHat hb ha)
  have hnn : ENNReal.ofReal (ideleNorm F (GeneralLinearGroup.det M)) *
      ENNReal.ofReal (ideleNorm F (GeneralLinearGroup.det M')) = 1 := by
    rw [← ENNReal.ofReal_mul (ideleNorm_pos _).le, ← ideleNorm_mul, det_mul_det_of_pair h, ideleNorm_one,
      ENNReal.ofReal_one]
  have hAA := muFinVec_OHatVec_mul_DHatVec (F := F) (ι := ι)
  rw [coe_OHatVecSub] at P1
  rw [coe_DHatVecSub] at P2
  set nM := ENNReal.ofReal (ideleNorm F (GeneralLinearGroup.det M))
  set nM' := ENNReal.ofReal (ideleNorm F (GeneralLinearGroup.det M'))
  set A1 := muFinVec F ι OHatVec
  set A2 := muFinVec F ι {c : ι → AF | ∀ i, c i ∈ DHat}
  set T1 := glTheta M (OHatVecSub F ι)
  set T2 := glTheta M' (DHatVecSub F ι)
  refine le_antisymm ?_ ?_
  · calc nM * T1 = nM * ((A1 * A2) * T1) := by rw [hAA, one_mul]
      _ = nM * A1 * (A2 * T1) := by ring
      _ ≤ nM * A1 * (A2 * ∑' η : glDualSet M' (DHatVecSub F ι), ENNReal.ofReal (gV (η : ι → V))) := by
          gcongr
      _ = nM * A1 * (nM' * T2) := by rw [P2]
      _ = (nM * nM') * (A1 * T2) := by ring
      _ = A1 * T2 := by rw [hnn, one_mul]
  · calc A1 * T2 ≤ A1 * ∑' η : glDualSet M (OHatVecSub F ι), ENNReal.ofReal (gV (η : ι → V)) := by gcongr
      _ = nM * T1 := P1.symm

end

end QuadFormsKB.Tamagawa.Measure.Weil
