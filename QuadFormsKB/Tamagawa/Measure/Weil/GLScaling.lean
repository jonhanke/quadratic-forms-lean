import QuadFormsKB.Tamagawa.Measure.Weil.LinearScaling

/-!
# $\mathrm{GL}_n$ scaling of Haar measure on $R^n$, and on $\mathbb A_f^n$

**Generic part** (namespace `MeasureTheory`, Mathlib-only hypotheses; upstreamable). For a commutative locally compact
topological ring $R$, $\mathrm{GL}_n(R)$ acts on $R^n$ by $M\cdot x = Mx$ (`Matrix.GLmulVec.instDistribMulAction`, a
scoped instance), and `glHaarChar R ι := distribHaarChar (ι → R)` is its Haar character:
$M_*\nu = \chi(M)^{-1}\nu$ for every regular Haar measure $\nu$ on $R^n$ (`map_mulVec_eq_glHaarChar_inv`).
* `glHaarChar_diagGL`: $\chi(\operatorname{diag}(d)) = \prod_i\Delta_R(d_i)$;
* `glHaarChar_transvecGL`: $\chi(t) = 1$ for a transvection (Fubini along the sheared coordinate; the proof of
  Mathlib's `Real.volume_preserving_transvectionStruct`, for any Haar measure);
* `glHaarChar_eq_of_field`: over a field, $\chi(M) = \Delta_K(\det M)$ (`diagonal_transvection_induction`).

**Finite adeles** ($F$ any number field): **`glHaarChar_finiteAdeleRing`**: $\chi(M) = \Delta_{\mathbb A_f}(\det M)$ for
$M\in\mathrm{GL}_n(\mathbb A_f)$, hence **`map_mulVec_muFinVec`**:
$M_*\mu_f^n = \Delta_{\mathbb A_f}(\det M)^{-1}\mu_f^n = (\prod_v|\det M_v|_v)^{-1}\mu_f^n$. The proof is an induction on the
finite set of places where $M_v\notin\mathrm{GL}_n(\mathcal O_v)$: at such a $v$, $M_v$ is a product of transvections and a
diagonal matrix over the field $F_v$ (`Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec`); each factor
lifts to $\mathbb A_f$ as the same factor at $v$ and the identity elsewhere (coefficients `Pi.single v c`,
`Pi.mulSingle v u`), and on $\mathrm{GL}_n(\hat{\mathcal O})$ both sides are $1$ ($M\hat{\mathcal O}^n = \hat{\mathcal O}^n$).

**Adeles.** **`map_mulVec_muAddVec`**: $M_*\mu = \|\det M\|_{\mathbb A}^{-1}\mu$ for $M\in\mathrm{GL}_n(\mathbb A_F)$ on
$\mathbb A_F^n$ (archimedean part `map_mulVec_muInfVec`, conjugated through $\mathbb A^n\cong F_\infty^n\times\mathbb A_f^n$).
Twisted Minkowski: **`adelicMinkowski_GL`**, compact forms **`exists_isCompact_forall_GL_mulVec_mem`** and
**`exists_isCompact_forall_SL_mulVec_mem`** (one compact set for all of $\mathrm{SL}_n(\mathbb A_F)$).

**Quaternions.** For $x\in(\mathbb H[F,a,b]\otimes\mathbb A)^\times$ (`QuatAdele a b` $=\mathbb H[\mathbb A_F,a,b]$), $L_x$ in the
basis $1,i,j,k$ is `quatLmat x` with $\det L_x = \operatorname{nrd}(x)^2$ (`det_quatLmat_eq`), so
**`map_quatLmat_muAddVec`**: $(L_x)_*\mu = \|\operatorname{nrd}x\|_{\mathbb A}^{-2}\mu$; twisted Minkowski
**`adelicMinkowski_quat_smul`** and its compact form **`exists_isCompact_forall_quat_mul_mem`** (Fujisaki's input).
-/

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal Pointwise

namespace Matrix.GLmulVec

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- $\mathrm{GL}_n(R)$ acting on column vectors $R^n$ by $M\cdot x = Mx$ (scoped, to avoid instance pollution). -/
scoped instance instDistribMulAction : DistribMulAction (GL ι R) (ι → R) where
  smul M x := (M : Matrix ι ι R) *ᵥ x
  one_smul x := by
    change ((1 : GL ι R) : Matrix ι ι R) *ᵥ x = x
    rw [Units.val_one, one_mulVec]
  mul_smul M N x := by
    change ((M * N : GL ι R) : Matrix ι ι R) *ᵥ x = (M : Matrix ι ι R) *ᵥ ((N : Matrix ι ι R) *ᵥ x)
    rw [Units.val_mul, mulVec_mulVec]
  smul_zero _ := mulVec_zero _
  smul_add _ _ _ := mulVec_add _ _ _

theorem smul_def (M : GL ι R) (x : ι → R) : M • x = (M : Matrix ι ι R) *ᵥ x := rfl

scoped instance instContinuousConstSMul [TopologicalSpace R] [IsTopologicalRing R] :
    ContinuousConstSMul (GL ι R) (ι → R) :=
  ⟨fun _ => continuous_const.matrix_mulVec continuous_id⟩

end Matrix.GLmulVec

open Matrix.GLmulVec

namespace MeasureTheory

/-- The generic form of `map_smul_eq_distribHaarChar_inv`: for a group $G$ acting distributively and continuously on a
locally compact group $A$ and a regular Haar measure $\mu$, $(g\cdot)_*\mu = \Delta(g)^{-1}\mu$. -/
theorem map_smul_eq_distribHaarChar_inv' {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A] [ContinuousConstSMul G A]
    [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [μ.IsAddHaarMeasure] [μ.Regular] (g : G) :
    Measure.map (g • ·) μ = (distribHaarChar A g)⁻¹ • μ := by
  ext s hs
  rw [Measure.map_apply (continuous_const_smul g).measurable hs]
  have : (g • ·) ⁻¹' s = g⁻¹ • s := by
    ext x; simp [Set.mem_smul_set_iff_inv_smul_mem]
  rw [this, ← distribHaarChar_mul μ g⁻¹ s, map_inv, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]

variable (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
  (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- **The Haar character of $\mathrm{GL}_n(R)$ on $R^n$**: $\nu(M\cdot s) = \chi(M)\,\nu(s)$ for every Haar measure $\nu$ on
$R^n$. -/
noncomputable def glHaarChar : GL ι R →* ℝ≥0 := distribHaarChar (ι → R)

variable {R ι}

/-- $M_*\nu = \chi(M)^{-1}\nu$ for every regular Haar measure $\nu$ on $R^n$. -/
theorem map_mulVec_eq_glHaarChar_inv [MeasurableSpace (ι → R)] [BorelSpace (ι → R)] (ν : Measure (ι → R))
    [ν.IsAddHaarMeasure] [ν.Regular] (M : GL ι R) :
    Measure.map (M : Matrix ι ι R).mulVec ν = (glHaarChar R ι M)⁻¹ • ν :=
  map_smul_eq_distribHaarChar_inv' ν M

/-- The invertible diagonal matrix $\operatorname{diag}(d)$, $d\in(R^\times)^n$. -/
def diagGL (d : ι → Rˣ) : GL ι R :=
  Units.map (diagonalRingHom ι R : (ι → R) →* Matrix ι ι R) (MulEquiv.piUnits.symm d)

omit [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] in
@[simp] theorem coe_diagGL (d : ι → Rˣ) : (diagGL d : Matrix ι ι R) = diagonal fun i => (d i : R) := rfl

omit [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] in
theorem det_diagGL (d : ι → Rˣ) : GeneralLinearGroup.det (diagGL d) = ∏ i, d i := by
  ext; simp [GeneralLinearGroup.det, Units.coe_prod]

/-- A transvection as an element of $\mathrm{GL}_n(R)$. -/
def transvecGL (t : TransvectionStruct ι R) : GL ι R :=
  ⟨t.toMatrix, t.inv.toMatrix, t.mul_inv, t.inv_mul⟩

omit [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] in
@[simp] theorem coe_transvecGL (t : TransvectionStruct ι R) : (transvecGL t : Matrix ι ι R) = t.toMatrix := rfl

omit [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] in
theorem det_transvecGL (t : TransvectionStruct ι R) : GeneralLinearGroup.det (transvecGL t) = 1 := by
  ext; simp [GeneralLinearGroup.det, TransvectionStruct.det]

section Measure

variable [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R]

/-- A transvection preserves the product of any Haar measure on $R^n$ (Fubini along the sheared coordinate). -/
theorem measurePreserving_transvection (μ : Measure R) [μ.IsAddHaarMeasure] (t : TransvectionStruct ι R) :
    MeasurePreserving (t.toMatrix *ᵥ ·) (Measure.pi fun _ : ι => μ) (Measure.pi fun _ : ι => μ) := by
  have ht : Measurable (t.toMatrix *ᵥ · : (ι → R) → ι → R) :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  refine ⟨ht, ?_⟩
  refine (Measure.pi_eq fun s hs ↦ ?_).symm
  have h2s : MeasurableSet (Set.univ.pi s) := .pi Set.countable_univ fun i _ ↦ hs i
  simp_rw [← Measure.pi_pi, ← lintegral_indicator_one h2s]
  rw [lintegral_map (measurable_one.indicator h2s) ht]
  refine lintegral_eq_of_lmarginal_eq {t.i} ((measurable_one.indicator h2s).comp ht)
    (measurable_one.indicator h2s) ?_
  simp_rw [lmarginal_singleton]
  ext x
  cases t with | mk t_i t_j t_hij t_c =>
  simp [transvection, add_mulVec, one_mulVec, single_mulVec, t_hij.symm, ← Function.update_add,
    lintegral_add_right_eq_self (μ := μ) fun xᵢ ↦ Set.indicator (Set.univ.pi s) 1 (Function.update x t_i xᵢ)]

omit [SecondCountableTopology R] in
/-- A measurable set of finite positive Haar measure in $R$. -/
theorem exists_pi_measure_pos_ne_top (μ : Measure R) [μ.IsAddHaarMeasure] :
    ∃ K : Set R, MeasurableSet K ∧ 0 < μ K ∧ μ K ≠ ⊤ := by
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : R)
  exact ⟨closure K, isClosed_closure.measurableSet,
    (μ.measure_pos_of_mem_nhds hK0).trans_le (measure_mono subset_closure),
    hK.closure.measure_lt_top.ne⟩

omit [CommRing R] [IsTopologicalRing R] [LocallyCompactSpace R] [DecidableEq ι] in
variable (ι) in
theorem pi_borelSpace : BorelSpace (ι → R) := Pi.borelSpace

/-- **Diagonal matrices**: $\chi(\operatorname{diag}(d)) = \prod_i\Delta_R(d_i)$. -/
theorem glHaarChar_diagGL (d : ι → Rˣ) : glHaarChar R ι (diagGL d) = ∏ i, distribHaarChar R (d i) := by
  have := pi_borelSpace (R := R) ι
  set μ : Measure R := Measure.addHaar
  obtain ⟨K, hKm, hK0, hKT⟩ := exists_pi_measure_pos_ne_top μ
  set ν : Measure (ι → R) := Measure.pi fun _ => μ
  have hpi : ν (Set.univ.pi fun _ => K) = ∏ _i : ι, μ K := Measure.pi_pi _ _
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := ν) (s := Set.univ.pi fun _ => K) ?_ ?_ ?_
  · rw [hpi]; exact Finset.prod_ne_zero_iff.mpr fun _ _ => hK0.ne'
  · rw [hpi]; exact ENNReal.prod_ne_top fun _ _ => hKT
  · have hset : diagGL d • (Set.univ.pi fun _ => K) = Set.univ.pi fun i => d i • K := by
      ext x
      simp only [Set.mem_smul_set, Set.mem_univ_pi]
      constructor
      · rintro ⟨y, hy, rfl⟩ i
        exact ⟨y i, hy i, by rw [smul_def, coe_diagGL, mulVec_diagonal, Units.smul_def, smul_eq_mul]⟩
      · intro h
        choose y hy hyx using h
        refine ⟨y, hy, funext fun i => ?_⟩
        rw [smul_def, coe_diagGL, mulVec_diagonal, ← hyx i, Units.smul_def, smul_eq_mul]
    rw [hset, Measure.pi_pi, hpi, ENNReal.ofNNReal_finsetProd, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => (distribHaarChar_mul μ (d i) K).symm

/-- **Transvections**: $\chi(t) = 1$. -/
theorem glHaarChar_transvecGL (t : TransvectionStruct ι R) : glHaarChar R ι (transvecGL t) = 1 := by
  have := pi_borelSpace (R := R) ι
  set μ : Measure R := Measure.addHaar
  obtain ⟨K, hKm, hK0, hKT⟩ := exists_pi_measure_pos_ne_top μ
  set ν : Measure (ι → R) := Measure.pi fun _ => μ
  have hpi : ν (Set.univ.pi fun _ => K) = ∏ _i : ι, μ K := Measure.pi_pi _ _
  have hsm : MeasurableSet (Set.univ.pi fun _ : ι => K) := .univ_pi fun _ => hKm
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := ν) (s := Set.univ.pi fun _ => K) ?_ ?_ ?_
  · rw [hpi]; exact Finset.prod_ne_zero_iff.mpr fun _ _ => hK0.ne'
  · rw [hpi]; exact ENNReal.prod_ne_top fun _ _ => hKT
  · have hset : transvecGL t • (Set.univ.pi fun _ : ι => K) =
        (t.inv.toMatrix *ᵥ ·) ⁻¹' (Set.univ.pi fun _ => K) := by
      ext x
      simp only [Set.mem_smul_set, Set.mem_preimage, smul_def, coe_transvecGL]
      constructor
      · rintro ⟨y, hy, rfl⟩
        rwa [mulVec_mulVec, t.inv_mul, one_mulVec]
      · intro h
        exact ⟨_, h, by rw [mulVec_mulVec, t.mul_inv, one_mulVec]⟩
    rw [hset, ← Measure.map_apply (measurePreserving_transvection μ t.inv).measurable hsm,
      (measurePreserving_transvection μ t.inv).map_eq, ENNReal.coe_one, one_mul]

/-- **Over a field**, $\chi(M) = \Delta_K(\det M)$: the Haar modulus of $M\in\mathrm{GL}_n(K)$ on $K^n$ is the modulus of
its determinant. -/
theorem glHaarChar_eq_of_field {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    [LocallyCompactSpace K] [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] (M : GL ι K) :
    glHaarChar K ι M = distribHaarChar K (GeneralLinearGroup.det M) := by
  set H := MonoidHom.eqLocus (glHaarChar K ι) ((distribHaarChar K).comp GeneralLinearGroup.det)
  suffices ∀ A : Matrix ι ι K, ∀ h : A.det ≠ 0, GeneralLinearGroup.mkOfDetNeZero A h ∈ H by
    have := this M (GeneralLinearGroup.det_ne_zero M)
    have hM : GeneralLinearGroup.mkOfDetNeZero (M : Matrix ι ι K) (GeneralLinearGroup.det_ne_zero M) = M :=
      Units.ext rfl
    rw [hM] at this; exact this
  intro A hA
  refine diagonal_transvection_induction_of_det_ne_zero (fun A => ∀ h, GeneralLinearGroup.mkOfDetNeZero A h ∈ H)
    A hA ?_ ?_ ?_ hA
  · intro D hD h
    have hD' : ∀ i, D i ≠ 0 := fun i => by
      rw [det_diagonal] at hD; exact Finset.prod_ne_zero_iff.mp hD i (Finset.mem_univ i)
    have : GeneralLinearGroup.mkOfDetNeZero (diagonal D) h = diagGL fun i => Units.mk0 (D i) (hD' i) :=
      Units.ext rfl
    rw [this]
    change glHaarChar K ι _ = distribHaarChar K (GeneralLinearGroup.det _)
    rw [glHaarChar_diagGL, det_diagGL, map_prod]
  · intro t h
    have : GeneralLinearGroup.mkOfDetNeZero t.toMatrix h = transvecGL t := Units.ext rfl
    rw [this]
    change glHaarChar K ι _ = distribHaarChar K (GeneralLinearGroup.det _)
    rw [glHaarChar_transvecGL, det_transvecGL, map_one]
  · intro A B hA hB hPA hPB h
    have : GeneralLinearGroup.mkOfDetNeZero (A * B) h =
        GeneralLinearGroup.mkOfDetNeZero A hA * GeneralLinearGroup.mkOfDetNeZero B hB := Units.ext rfl
    rw [this]
    exact H.mul_mem (hPA hA) (hPB hB)

end Measure

end MeasureTheory

namespace QuadFormsKB.Tamagawa.Measure.Weil

open IsDedekindDomain NumberField RestrictedProduct
open scoped Classical

noncomputable section

variable {F : Type} [Field F] [NumberField F]

local notation "AF" => FiniteAdeleRing (𝓞 F) F

/-! ### Finite adeles: places, single-place elements -/

/-- Evaluation at a place, $\mathbb A_f\to F_v$, as a ring homomorphism. -/
def evalAt (v : HeightOneSpectrum (𝓞 F)) : AF →+* v.adicCompletion F where
  toFun x := x v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem evalAt_apply (v : HeightOneSpectrum (𝓞 F)) (x : AF) : evalAt v x = x v := rfl

/-- The finite adele which is $c$ at $v$ and $0$ elsewhere. -/
def singleAt (v : HeightOneSpectrum (𝓞 F)) (c : v.adicCompletion F) : AF :=
  show Πʳ w : HeightOneSpectrum (𝓞 F), [w.adicCompletion F, w.adicCompletionIntegers F] from
  ⟨Pi.single v c, (Set.finite_singleton v).subset fun w hw => by
    by_contra h
    exact hw (show Pi.single v c w ∈ w.adicCompletionIntegers F by
      rw [Pi.single_eq_of_ne (by simpa using h)]; exact zero_mem _)⟩

theorem singleAt_apply (v : HeightOneSpectrum (𝓞 F)) (c : v.adicCompletion F) (w : HeightOneSpectrum (𝓞 F)) :
    singleAt v c w = Pi.single v c w := rfl

/-- The finite adele which is $u$ at $v$ and $1$ elsewhere. -/
def mulSingleAt' (v : HeightOneSpectrum (𝓞 F)) (c : v.adicCompletion F) : AF :=
  show Πʳ w : HeightOneSpectrum (𝓞 F), [w.adicCompletion F, w.adicCompletionIntegers F] from
  ⟨Pi.mulSingle v c, (Set.finite_singleton v).subset fun w hw => by
    by_contra h
    exact hw (show Pi.mulSingle v c w ∈ w.adicCompletionIntegers F by
      rw [Pi.mulSingle_eq_of_ne (by simpa using h)]; exact one_mem _)⟩

theorem mulSingleAt'_apply (v : HeightOneSpectrum (𝓞 F)) (c : v.adicCompletion F) (w : HeightOneSpectrum (𝓞 F)) :
    mulSingleAt' v c w = Pi.mulSingle v c w := rfl

/-- The finite idele which is $u$ at $v$ and $1$ elsewhere. -/
def mulSingleAt (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ) : AFˣ where
  val := mulSingleAt' v u
  inv := mulSingleAt' v ↑u⁻¹
  val_inv := by
    apply Subtype.ext; funext w
    change Pi.mulSingle v (u : v.adicCompletion F) w * Pi.mulSingle v ((u⁻¹ : (v.adicCompletion F)ˣ) :
      v.adicCompletion F) w = 1
    by_cases h : w = v
    · subst h; simp
    · simp [Pi.mulSingle_eq_of_ne h]
  inv_val := by
    apply Subtype.ext; funext w
    change Pi.mulSingle v ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) w *
      Pi.mulSingle v (u : v.adicCompletion F) w = 1
    by_cases h : w = v
    · subst h; simp
    · simp [Pi.mulSingle_eq_of_ne h]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem transvection_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (i j : ι) (c : R) :
    (transvection i j c).map f = transvection i j (f c) := by
  rw [transvection, transvection, Matrix.map_add f (map_add f), Matrix.map_one f (map_zero f) (map_one f), map_single]

/-- $M\in\mathrm{GL}_n(F_v)$ lies in $\mathrm{GL}_n(\mathcal O_v)$: $M$ and $M^{-1}$ have entries in $\mathcal O_v$. -/
def IsIntegralGL {v : HeightOneSpectrum (𝓞 F)} (A : GL ι (v.adicCompletion F)) : Prop :=
  ∀ i j, (A : Matrix ι ι (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F ∧
    ((A⁻¹ : GL ι (v.adicCompletion F)) : Matrix ι ι (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F

theorem isIntegralGL_one (v : HeightOneSpectrum (𝓞 F)) : IsIntegralGL (1 : GL ι (v.adicCompletion F)) := by
  intro i j
  by_cases h : i = j <;> simp [h, one_mem, zero_mem]

/-- The places where $M\notin\mathrm{GL}_n(\mathcal O_v)$ form a finite set. -/
theorem finite_not_isIntegralGL (M : GL ι AF) :
    {v | ¬ IsIntegralGL (GeneralLinearGroup.map (evalAt v) M)}.Finite := by
  have h1 : ∀ x : AF, {v : HeightOneSpectrum (𝓞 F) | x v ∉ v.adicCompletionIntegers F}.Finite := fun x => x.2
  refine ((Set.finite_iUnion fun i => Set.finite_iUnion fun j =>
    (h1 ((M : Matrix ι ι AF) i j)).union (h1 (((M⁻¹ : GL ι AF) : Matrix ι ι AF) i j)))).subset ?_
  intro v hv
  simp only [IsIntegralGL, not_forall, not_and_or] at hv
  obtain ⟨i, j, h⟩ := hv
  simp only [Set.mem_iUnion, Set.mem_union, Set.mem_ofPred_eq]
  refine ⟨i, j, ?_⟩
  rcases h with h | h
  · exact Or.inl h
  · rw [← map_inv] at h; exact Or.inr h

/-! ### The Haar character on $\mathbb A_f^n$ -/

instance borelSpace_finVec : BorelSpace (ι → AF) := Pi.borelSpace

/-- $\hat{\mathcal O}^n$. -/
def OHatVec : Set (ι → AF) := Set.univ.pi fun _ => OHat

omit [DecidableEq ι] in
theorem muFinVec_OHatVec : muFinVec F ι OHatVec = ∏ _i : ι, muFin F OHat := Measure.pi_pi _ _

omit [DecidableEq ι] in
theorem muFinVec_OHatVec_ne_zero : muFinVec F ι OHatVec ≠ 0 := by
  rw [muFinVec_OHatVec]; exact Finset.prod_ne_zero_iff.mpr fun _ _ => muFin_OHat_ne_zero

omit [DecidableEq ι] in
theorem muFinVec_OHatVec_ne_top : muFinVec F ι OHatVec ≠ ⊤ := by
  rw [muFinVec_OHatVec]; exact ENNReal.prod_ne_top fun _ _ => muFin_OHat_ne_top

theorem mem_of_mem_integers_matrix {v : HeightOneSpectrum (𝓞 F)} (A : Matrix ι ι (v.adicCompletion F))
    (hA : ∀ i j, A i j ∈ v.adicCompletionIntegers F) : A.det ∈ v.adicCompletionIntegers F := by
  set N : Matrix ι ι (v.adicCompletionIntegers F) := fun i j => ⟨A i j, hA i j⟩
  have : A = (v.adicCompletionIntegers F).subtype.mapMatrix N := rfl
  rw [this, ← RingHom.map_det]
  exact (N.det).2

theorem smul_OHatVec_subset (M : GL ι AF) (hM : ∀ v i j, (M : Matrix ι ι AF) i j v ∈ v.adicCompletionIntegers F) :
    M • (OHatVec : Set (ι → AF)) ⊆ OHatVec := by
  rintro _ ⟨x, hx, rfl⟩ i _ v
  change evalAt v (((M : Matrix ι ι AF) *ᵥ x) i) ∈ _
  rw [RingHom.map_mulVec, mulVec, dotProduct]
  exact sum_mem fun j _ => mul_mem (hM v i j) (hx j (Set.mem_univ j) v)

/-- On $\mathrm{GL}_n(\hat{\mathcal O})$ the Haar character is trivial. -/
theorem glHaarChar_of_integral (M : GL ι AF) (hM : ∀ v, IsIntegralGL (GeneralLinearGroup.map (evalAt v) M)) :
    glHaarChar AF ι M = 1 := by
  have h1 := smul_OHatVec_subset M fun v i j => (hM v i j).1
  have h2 := smul_OHatVec_subset M⁻¹ fun v i j => by
    have := (hM v i j).2; rwa [← map_inv] at this
  have hset : M • (OHatVec : Set (ι → AF)) = OHatVec := by
    refine h1.antisymm fun x hx => ⟨M⁻¹ • x, h2 ⟨x, hx, rfl⟩, smul_inv_smul M x⟩
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := muFinVec F ι) muFinVec_OHatVec_ne_zero
    muFinVec_OHatVec_ne_top ?_
  rw [hset, ENNReal.coe_one, one_mul]

/-- On $\mathrm{GL}_n(\hat{\mathcal O})$ the modulus of the determinant is trivial. -/
theorem distribHaarChar_det_of_integral (M : GL ι AF)
    (hM : ∀ v, IsIntegralGL (GeneralLinearGroup.map (evalAt v) M)) :
    distribHaarChar AF (GeneralLinearGroup.det M) = 1 := by
  set u := GeneralLinearGroup.det M
  have hu : ∀ v, (u : AF) v ∈ v.adicCompletionIntegers F := fun v => by
    change evalAt v (M : Matrix ι ι AF).det ∈ _
    rw [RingHom.map_det]
    exact mem_of_mem_integers_matrix _ fun i j => (hM v i j).1
  have hu' : ∀ v, ((u⁻¹ : AFˣ) : AF) v ∈ v.adicCompletionIntegers F := fun v => by
    change evalAt v ((M⁻¹ : GL ι AF) : Matrix ι ι AF).det ∈ _
    rw [RingHom.map_det]
    exact mem_of_mem_integers_matrix _ fun i j => by
      have := (hM v i j).2; rwa [← map_inv] at this
  have hset : u • (OHat : Set AF) = OHat := by
    ext x
    simp only [Set.mem_smul_set, Units.smul_def, smul_eq_mul]
    constructor
    · rintro ⟨y, hy, rfl⟩ v; exact mul_mem (hu v) (hy v)
    · intro hx
      exact ⟨((u⁻¹ : AFˣ) : AF) * x, fun v => mul_mem (hu' v) (hx v), by simp⟩
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := muFin F) muFin_OHat_ne_zero muFin_OHat_ne_top ?_
  rw [hset, ENNReal.coe_one, one_mul]

variable (F ι) in
/-- The subgroup of $\mathrm{GL}_n(\mathbb A_f)$ where $\chi(M) = \Delta_{\mathbb A_f}(\det M)$ (eventually all of it). -/
def glEqLocus : Subgroup (GL ι AF) :=
  MonoidHom.eqLocus (glHaarChar AF ι) ((distribHaarChar AF).comp GeneralLinearGroup.det)

theorem mem_glEqLocus {M : GL ι AF} :
    M ∈ glEqLocus F ι ↔ glHaarChar AF ι M = distribHaarChar AF (GeneralLinearGroup.det M) := Iff.rfl

/-- Every element of $\mathrm{GL}_n(F_v)$ lifts to an element of `glEqLocus` which is the identity away from $v$. -/
theorem exists_lift_mem_glEqLocus (v : HeightOneSpectrum (𝓞 F)) (A : Matrix ι ι (v.adicCompletion F))
    (hA : A.det ≠ 0) : ∃ N ∈ glEqLocus F ι, (N : Matrix ι ι AF).map (evalAt v) = A ∧
      ∀ w ≠ v, (N : Matrix ι ι AF).map (evalAt w) = 1 := by
  refine diagonal_transvection_induction_of_det_ne_zero (fun A => ∃ N ∈ glEqLocus F ι,
    (N : Matrix ι ι AF).map (evalAt v) = A ∧ ∀ w ≠ v, (N : Matrix ι ι AF).map (evalAt w) = 1) A hA ?_ ?_ ?_
  · intro D hD
    have hD' : ∀ i, D i ≠ 0 := fun i => by
      rw [det_diagonal] at hD; exact Finset.prod_ne_zero_iff.mp hD i (Finset.mem_univ i)
    refine ⟨diagGL fun i => mulSingleAt v (Units.mk0 (D i) (hD' i)), ?_, ?_, fun w hw => ?_⟩
    · rw [mem_glEqLocus, glHaarChar_diagGL, det_diagGL, map_prod]
    · rw [coe_diagGL, diagonal_map (map_zero _)]
      congr 1; funext i
      change Pi.mulSingle v _ v = _
      simp
    · rw [coe_diagGL, diagonal_map (map_zero _)]
      have : (fun i => evalAt w ((mulSingleAt v (Units.mk0 (D i) (hD' i)) : AFˣ) : AF)) = fun _ => 1 := by
        funext i
        change Pi.mulSingle v _ w = _
        rw [Pi.mulSingle_eq_of_ne hw]
      rw [this, diagonal_one]
  · intro t
    obtain ⟨i, j, hij, c⟩ := t
    refine ⟨transvecGL ⟨i, j, hij, singleAt v c⟩, ?_, ?_, fun w hw => ?_⟩
    · rw [mem_glEqLocus, glHaarChar_transvecGL, det_transvecGL, map_one]
    · rw [coe_transvecGL]
      change (transvection i j (singleAt v c)).map (evalAt v) = transvection i j c
      rw [transvection_map]
      congr 1
      change Pi.single v c v = c
      simp
    · rw [coe_transvecGL]
      change (transvection i j (singleAt v c)).map (evalAt w) = 1
      rw [transvection_map]
      change transvection i j (Pi.single v c w) = 1
      rw [Pi.single_eq_of_ne hw, transvection_zero]
  · rintro A B - - ⟨N₁, h₁, hv₁, hw₁⟩ ⟨N₂, h₂, hv₂, hw₂⟩
    refine ⟨N₁ * N₂, (glEqLocus F ι).mul_mem h₁ h₂, ?_, fun w hw => ?_⟩
    · rw [Units.val_mul, Matrix.map_mul, hv₁, hv₂]
    · rw [Units.val_mul, Matrix.map_mul, hw₁ w hw, hw₂ w hw, one_mul]

/-- **The Haar character of $\mathrm{GL}_n(\mathbb A_f)$ on $\mathbb A_f^n$ is the modulus of the determinant**:
$\chi(M) = \Delta_{\mathbb A_f}(\det M)$. -/
theorem glHaarChar_finiteAdeleRing (M : GL ι AF) :
    glHaarChar AF ι M = distribHaarChar AF (GeneralLinearGroup.det M) := by
  suffices ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ M : GL ι AF,
      (∀ v ∉ S, IsIntegralGL (GeneralLinearGroup.map (evalAt v) M)) → M ∈ glEqLocus F ι from
    this (finite_not_isIntegralGL M).toFinset M fun v hv => by simpa using hv
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro M hM
    rw [mem_glEqLocus, glHaarChar_of_integral M fun v => hM v (Finset.notMem_empty v),
      distribHaarChar_det_of_integral M fun v => hM v (Finset.notMem_empty v)]
  | insert v S hvS ih =>
    intro M hM
    set A := GeneralLinearGroup.map (evalAt v) M
    obtain ⟨N, hN, hNv, hNw⟩ := exists_lift_mem_glEqLocus v (A : Matrix ι ι (v.adicCompletion F))
      (GeneralLinearGroup.det_ne_zero A)
    have hNv' : GeneralLinearGroup.map (evalAt v) N = A := Units.ext hNv
    have hNw' : ∀ w ≠ v, GeneralLinearGroup.map (evalAt w) N = 1 := fun w hw => Units.ext (hNw w hw)
    have hM' : N⁻¹ * M ∈ glEqLocus F ι := by
      refine ih _ fun w hw => ?_
      rw [map_mul, map_inv]
      by_cases hwv : w = v
      · subst hwv
        rw [hNv', inv_mul_cancel]; exact isIntegralGL_one _
      · rw [hNw' w hwv, inv_one, one_mul]
        exact hM w (by simp [hwv, hw])
    have := (glEqLocus F ι).mul_mem hN hM'
    rwa [mul_inv_cancel_left] at this

/-- **Finite-place $\mathrm{GL}_n$ scaling.** For $M\in\mathrm{GL}_n(\mathbb A_f)$ acting on $\mathbb A_f^n$,
$M_*\mu_f^n = \Delta_{\mathbb A_f}(\det M)^{-1}\,\mu_f^n$, with $\Delta_{\mathbb A_f}(u) = \prod_v|u_v|_v$
(`distribHaarChar_finiteAdeleRing`). -/
@[kb "weil1982" "§2.1 [unverified page]"]
theorem map_mulVec_muFinVec (M : GL ι AF) :
    Measure.map (M : Matrix ι ι AF).mulVec (muFinVec F ι) =
      ((distribHaarChar AF (GeneralLinearGroup.det M))⁻¹ : ℝ≥0) • muFinVec F ι := by
  have : (muFinVec F ι).Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  rw [map_mulVec_eq_glHaarChar_inv, glHaarChar_finiteAdeleRing]

/-- The same, with the local moduli: $M_*\mu_f^n = (\prod_v\Delta_v(\det M_v))^{-1}\mu_f^n$. -/
theorem map_mulVec_muFinVec' (M : GL ι AF) :
    Measure.map (M : Matrix ι ι AF).mulVec (muFinVec F ι) =
      ((∏ᶠ v, modAt (GeneralLinearGroup.det M) v)⁻¹ : ℝ≥0) • muFinVec F ι := by
  rw [map_mulVec_muFinVec, distribHaarChar_finiteAdeleRing]


/-! ### The adelic $\mathrm{GL}_n$ scaling and twisted Minkowski -/

section Adelic

set_option synthInstance.maxHeartbeats 400000

open Module NumberField.mixedEmbedding

/-- The archimedean component $M_\infty\in\mathrm{GL}_n(F_\infty)$ of $M\in\mathrm{GL}_n(\mathbb A_F)$. -/
abbrev glInf (M : GL ι (Adeles F)) : GL ι (mixedSpace F) := GeneralLinearGroup.map (RingHom.fst _ _) M

/-- The finite component $M_f\in\mathrm{GL}_n(\mathbb A_f)$ of $M\in\mathrm{GL}_n(\mathbb A_F)$. -/
abbrev glFin (M : GL ι (Adeles F)) : GL ι AF := GeneralLinearGroup.map (RingHom.snd _ _) M

theorem arrowProd_mulVec (M : GL ι (Adeles F)) (y : AdeleSpace F ι) :
    MeasurableEquiv.arrowProdEquivProdArrow (mixedSpace F) AF ι ((M : Matrix ι ι (Adeles F)) *ᵥ y) =
      Prod.map (glInf M : Matrix ι ι (mixedSpace F)).mulVec (glFin M : Matrix ι ι AF).mulVec
        (MeasurableEquiv.arrowProdEquivProdArrow (mixedSpace F) AF ι y) := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · exact RingHom.map_mulVec (RingHom.fst (mixedSpace F) AF) (M : Matrix ι ι (Adeles F)) y i
  · exact RingHom.map_mulVec (RingHom.snd (mixedSpace F) AF) (M : Matrix ι ι (Adeles F)) y i

theorem infPart_det (M : GL ι (Adeles F)) :
    (infPart (GeneralLinearGroup.det M) : mixedSpace F) = (glInf M : Matrix ι ι (mixedSpace F)).det :=
  RingHom.map_det (RingHom.fst (mixedSpace F) AF) (M : Matrix ι ι (Adeles F))

theorem finPart_det (M : GL ι (Adeles F)) :
    finPart (GeneralLinearGroup.det M) = GeneralLinearGroup.det (glFin M) :=
  Units.ext (RingHom.map_det (RingHom.snd (mixedSpace F) AF) (M : Matrix ι ι (Adeles F)))

/-- **Adelic $\mathrm{GL}_n$ scaling.** For $M\in\mathrm{GL}_n(\mathbb A_F)$ acting on $\mathbb A_F^n$,
$M_*\mu = \|\det M\|_{\mathbb A}^{-1}\,\mu$ for the self-dual measure $\mu$ of $\mathbb A_F^n$
($\|\cdot\|_{\mathbb A}$ = `ideleNorm`). -/
@[kb "weil1982" "§2.1 [unverified page]"]
theorem map_mulVec_muAddVec (M : GL ι (Adeles F)) :
    Measure.map (M : Matrix ι ι (Adeles F)).mulVec (muAddVec F ι) =
      ENNReal.ofReal (ideleNorm F (GeneralLinearGroup.det M))⁻¹ • muAddVec F ι := by
  set e := MeasurableEquiv.arrowProdEquivProdArrow (mixedSpace F) AF ι
  have hpres := measurePreserving_arrowProd (F := F) (ι := ι)
  have hInf := map_mulVec_muInfVec (F := F) (n := Fintype.card ι)
  -- reindex the archimedean statement from `Fin (card ι)` to `ι`
  have hInf' : Measure.map (glInf M : Matrix ι ι (mixedSpace F)).mulVec (muInfVec F ι) =
      ENNReal.ofReal |LinearMap.det (LinearMap.mulLeft ℝ (glInf M : Matrix ι ι (mixedSpace F)).det)|⁻¹ •
        muInfVec F ι := by
    have hdet : LinearMap.det (((glInf M : Matrix ι ι (mixedSpace F))).mulVecLin.restrictScalars ℝ) =
        Algebra.norm ℝ (glInf M : Matrix ι ι (mixedSpace F)).det := by
      rw [LinearMap.det_restrictScalars, show Matrix.mulVecLin (glInf M : Matrix ι ι (mixedSpace F)) =
        Matrix.toLin' (glInf M : Matrix ι ι (mixedSpace F)) from rfl, LinearMap.det_toLin']
    have h0 : LinearMap.det (((glInf M : Matrix ι ι (mixedSpace F))).mulVecLin.restrictScalars ℝ) ≠ 0 := by
      rw [hdet]; exact ((GeneralLinearGroup.det (glInf M)).isUnit.map (Algebra.norm ℝ)).ne_zero
    have := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := muInfVec F ι) h0
    rw [hdet, Algebra.norm_apply, abs_inv] at this
    exact this
  have hFin := map_mulVec_muFinVec (glFin M)
  have hmInf : Measurable (glInf M : Matrix ι ι (mixedSpace F)).mulVec :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  have hmFin : Measurable (glFin M : Matrix ι ι AF).mulVec :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  have hm : Measurable (M : Matrix ι ι (Adeles F)).mulVec :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  have hconj : (M : Matrix ι ι (Adeles F)).mulVec =
      e.symm ∘ Prod.map (glInf M : Matrix ι ι (mixedSpace F)).mulVec (glFin M : Matrix ι ι AF).mulVec ∘ e := by
    funext y
    simp only [Function.comp_apply]
    rw [← arrowProd_mulVec, MeasurableEquiv.symm_apply_apply]
  have hprod : Measure.map (Prod.map (glInf M : Matrix ι ι (mixedSpace F)).mulVec
      (glFin M : Matrix ι ι AF).mulVec) ((muInfVec F ι).prod (muFinVec F ι)) =
      (ENNReal.ofReal |LinearMap.det (LinearMap.mulLeft ℝ (glInf M : Matrix ι ι (mixedSpace F)).det)|⁻¹ *
        ((distribHaarChar AF (GeneralLinearGroup.det (glFin M)))⁻¹ : ℝ≥0)) •
          ((muInfVec F ι).prod (muFinVec F ι)) := by
    have : SigmaFinite (Measure.map (glInf M : Matrix ι ι (mixedSpace F)).mulVec (muInfVec F ι)) := by
      rw [hInf']; exact SMul.sigmaFinite (μ := muInfVec F ι) (Real.toNNReal _)
    have : SigmaFinite (Measure.map (glFin M : Matrix ι ι AF).mulVec (muFinVec F ι)) := by
      rw [hFin]; infer_instance
    rw [← Measure.map_prod_map _ _ hmInf hmFin, hInf', hFin, Measure.prod_smul_left, Measure.prod_smul_right,
      ENNReal.smul_def, smul_smul]
  calc Measure.map (M : Matrix ι ι (Adeles F)).mulVec (muAddVec F ι)
      = Measure.map e.symm (Measure.map (Prod.map (glInf M : Matrix ι ι (mixedSpace F)).mulVec
          (glFin M : Matrix ι ι AF).mulVec) (Measure.map e (muAddVec F ι))) := by
        rw [Measure.map_map (hmInf.prodMap hmFin) e.measurable, Measure.map_map e.symm.measurable
          ((hmInf.prodMap hmFin).comp e.measurable), hconj]
    _ = _ := by
        rw [hpres.map_eq, hprod, Measure.map_smul, ← hpres.map_eq, MeasurableEquiv.map_symm_map]
        congr 1
        have hfin : (∏ᶠ v, (modAt (GeneralLinearGroup.det (glFin M)) v : ℝ)) =
            (distribHaarChar AF (GeneralLinearGroup.det (glFin M)) : ℝ) := by
          rw [distribHaarChar_finiteAdeleRing]
          exact (MonoidHom.map_finprod NNReal.toRealHom.toMonoidHom (mulSupport_modAt_finite _)).symm
        rw [ideleNorm, infPart_det, finPart_det, hfin, mul_inv,
          ENNReal.ofReal_mul (inv_nonneg.2 (abs_nonneg _)), ← NNReal.coe_inv, ENNReal.ofReal_coe_nnreal]
        exact e.symm.measurable.aemeasurable


theorem ideleNorm_one : ideleNorm F 1 = 1 := by
  rw [← distribHaarChar_adeles, map_one, NNReal.coe_one]

theorem ideleNorm_mul (g h : (Adeles F)ˣ) : ideleNorm F (g * h) = ideleNorm F g * ideleNorm F h := by
  rw [← distribHaarChar_adeles, ← distribHaarChar_adeles, ← distribHaarChar_adeles, map_mul, NNReal.coe_mul]

private theorem lt_ofReal_inv_mul' {n : ℕ} {N : ℝ} (hN : 0 < N) {X : ℝ≥0∞}
    (h : 2 ^ n * ENNReal.ofReal N < X) : 1 * 2 ^ n < ENNReal.ofReal N⁻¹ * X := by
  rw [one_mul, ENNReal.ofReal_inv_of_pos hN, ← ENNReal.div_eq_inv_mul,
    ENNReal.lt_div_iff_mul_lt (Or.inl (ENNReal.ofReal_pos.mpr hN).ne') (Or.inl ENNReal.ofReal_ne_top)]
  exact h

/-- **Twisted adelic Minkowski for $\mathrm{GL}_n(\mathbb A_F)$.** Let $M\in\mathrm{GL}_n(\mathbb A_F)$,
$C_\infty\subseteq F_\infty^n$ convex, symmetric and measurable, and $H\le\mathbb A_f^n$ a measurable subgroup. If
$2^{n[F:\mathbb Q]}\,\|\det M\|_{\mathbb A} < \mu_\infty^n(C_\infty)\,\mu_f^n(H)$ (self-dual measures, covolume $1$), then
$M\xi\in C_\infty\times H$ for some $0\ne\xi\in F^n$. -/
@[kb "weil1982" "§2.1 [unverified page]"]
theorem adelicMinkowski_GL (M : GL ι (Adeles F)) {C : Set (ι → mixedSpace F)}
    (h_symm : ∀ x ∈ C, -x ∈ C) (h_conv : Convex ℝ C) (hC : MeasurableSet C) (H : AddSubgroup (ι → AF))
    (hH : MeasurableSet (H : Set (ι → AF)))
    (h : 2 ^ (Fintype.card ι * finrank ℚ F) * ENNReal.ofReal (ideleNorm F (GeneralLinearGroup.det M)) <
      muInfVec F ι C * muFinVec F ι H) :
    ∃ ξ : ι → F, ξ ≠ 0 ∧ (M : Matrix ι ι (Adeles F)) *ᵥ diagVec F ι ξ ∈ boxSet C (H : Set (ι → AF)) := by
  set T : AdeleSpace F ι →+ AdeleSpace F ι := (Matrix.mulVecLin (M : Matrix ι ι (Adeles F))).toAddMonoidHom
  have hT : Measurable T := (continuous_const.matrix_mulVec continuous_id).measurable
  have hC2 : MeasurableSet ((2⁻¹ : ℝ) • C) := hC.const_smul_of_ne_zero (by norm_num)
  have hS : MeasurableSet (boxSet ((2⁻¹ : ℝ) • C) (H : Set (ι → AF))) :=
    (MeasurableEquiv.arrowProdEquivProdArrow (mixedSpace F) AF ι).measurable (hC2.prod hH)
  obtain ⟨⟨_, x, rfl⟩, hne, hmem⟩ := exists_ne_zero_map_mem_of_sub_mem (C := boxSet C (H : Set (ι → AF)))
    (isAddFundamentalDomain_fundDomVec (muAddVec F ι)) T hT (map_mulVec_muAddVec M) hS
    (by
      rw [muAddVec_fundDomVec, muAddVec_boxSet, ← Measure.prod_prod]
      exact lt_mul_measure_half_prod (by rw [finrank_infVec]; exact lt_ofReal_inv_mul' (ideleNorm_pos _) h))
    (fun x hx y hy => ⟨sub_mem_of_mem_inv_two_smul h_symm h_conv hx.1 hy.1, H.sub_mem hx.2 hy.2⟩)
  refine ⟨x, fun h0 => hne ?_, hmem⟩
  subst h0; exact Subtype.ext (map_zero _)

/-- **Twisted adelic Minkowski for $\mathrm{GL}_n(\mathbb A_F)$, compact form.** For every $B$ there is a compact
$\mathcal C\subseteq\mathbb A_F^n$ such that every $M\in\mathrm{GL}_n(\mathbb A_F)$ with $\|\det M\|_{\mathbb A}\le B$ has
$M\xi\in\mathcal C$ for some $0\ne\xi\in F^n$ ($n\ge 1$). -/
@[kb "weil1982" "§2.1 [unverified page]"]
theorem exists_isCompact_forall_GL_mulVec_mem [Nonempty ι] (B : ℝ) :
    ∃ K : Set (AdeleSpace F ι), IsCompact K ∧
      ∀ M : GL ι (Adeles F), ideleNorm F (GeneralLinearGroup.det M) ≤ B →
        ∃ ξ : ι → F, ξ ≠ 0 ∧ (M : Matrix ι ι (Adeles F)) *ᵥ diagVec F ι ξ ∈ K := by
  have hn : 0 < finrank ℝ (ι → mixedSpace F) := by
    rw [finrank_infVec]; exact Nat.mul_pos Fintype.card_pos Module.finrank_pos
  set H : AddSubgroup (ι → AF) := AddSubgroup.pi Set.univ fun _ => OHatSub
  have hHcoe : (H : Set (ι → AF)) = Set.univ.pi fun _ => OHat := by
    ext x; simp [H, AddSubgroup.mem_pi]; rfl
  have hHm : MeasurableSet (H : Set (ι → AF)) := by
    rw [hHcoe]; exact MeasurableSet.univ_pi fun _ => measurableSet_OHat
  have hHvol : muFinVec F ι H = ∏ _i : ι, muFin F OHat := by
    rw [hHcoe, Measure.pi_pi]
  have hH0 : muFinVec F ι H ≠ 0 := by
    rw [hHvol]; exact Finset.prod_ne_zero_iff.mpr fun _ _ => muFin_OHat_ne_zero
  have hHt : muFinVec F ι H ≠ ⊤ := by
    rw [hHvol]; exact ENNReal.prod_ne_top fun _ _ => muFin_OHat_ne_top
  obtain ⟨R, hR, hlt⟩ := exists_lt_measure_closedBall_mul (muInfVec F ι) hn
    (a := 2 ^ (Fintype.card ι * finrank ℚ F) * ENNReal.ofReal B)
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) ENNReal.ofReal_ne_top) hH0 hHt
  refine ⟨Set.univ.pi fun _ => Metric.closedBall (0 : mixedSpace F) R ×ˢ OHat,
    isCompact_univ_pi fun _ => (isCompact_closedBall _ _).prod isCompact_OHat, fun M hM => ?_⟩
  obtain ⟨ξ, hξ, hmem⟩ := adelicMinkowski_GL M (fun x hx => by simpa using hx) (convex_closedBall _ _)
    Metric.isClosed_closedBall.measurableSet H hHm (lt_of_le_of_lt (by gcongr) hlt)
  refine ⟨ξ, hξ, fun i _ => ⟨?_, ?_⟩⟩
  · have h1 := hmem.1
    rw [mem_closedBall_zero_iff] at h1 ⊢
    exact (norm_le_pi_norm (fun i => (((M : Matrix ι ι (Adeles F)) *ᵥ diagVec F ι ξ) i).1) i).trans h1
  · have h2 := hmem.2
    rw [hHcoe] at h2
    exact h2 i (Set.mem_univ i)

/-- **Adelic Minkowski for $\mathrm{SL}_n(\mathbb A_F)$** (in particular $\mathrm{SL}_2$): there is one compact
$\mathcal C\subseteq\mathbb A_F^n$ such that every $g\in\mathrm{SL}_n(\mathbb A_F)$ has $g\xi\in\mathcal C$ for some
$0\ne\xi\in F^n$. This is the input to the finiteness of $\operatorname{vol}(\mathrm{SL}_2(F)\backslash\mathrm{SL}_2(\mathbb A_F))$
by Siegel's mean-value argument. -/
@[kb "weil1982" "§2.1 [unverified page]"]
theorem exists_isCompact_forall_SL_mulVec_mem [Nonempty ι] :
    ∃ K : Set (AdeleSpace F ι), IsCompact K ∧
      ∀ g : Matrix.SpecialLinearGroup ι (Adeles F),
        ∃ ξ : ι → F, ξ ≠ 0 ∧ (g : Matrix ι ι (Adeles F)) *ᵥ diagVec F ι ξ ∈ K := by
  obtain ⟨K, hK, hKM⟩ := exists_isCompact_forall_GL_mulVec_mem (F := F) (ι := ι) 1
  refine ⟨K, hK, fun g => hKM (Matrix.SpecialLinearGroup.toGL g) ?_⟩
  have : GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL g) = 1 :=
    Units.ext (by rw [Matrix.SpecialLinearGroup.coeToGL_det])
  rw [this, ideleNorm_one]

end Adelic

/-! ### Quaternions: the scaling by $(\mathbb H\otimes\mathbb A)^\times$ and twisted Minkowski -/

section Quaternion

set_option synthInstance.maxHeartbeats 400000

open Module NumberField.mixedEmbedding
open scoped Quaternion

variable (a b : F)

/-- $\mathbb H[F,a,b]\otimes\mathbb A_F = \mathbb H[\mathbb A_F,a,b]$. -/
abbrev QuatAdele := ℍ[Adeles F, diag F a, 0, diag F b]

/-- The diagonal embedding $\mathbb H[F,a,b]\to\mathbb H[\mathbb A_F,a,b]$ (coordinatewise `diag`). -/
def quatDiag (ξ : ℍ[F,a,b]) : QuatAdele a b :=
  ⟨diag F ξ.re, diag F ξ.imI, diag F ξ.imJ, diag F ξ.imK⟩

theorem linearEquivTuple_quatDiag (ξ : ℍ[F,a,b]) :
    QuaternionAlgebra.linearEquivTuple (R := Adeles F) _ _ _ (quatDiag a b ξ) = diagQuat a b ξ := by
  funext i; fin_cases i <;> rfl

variable {a b}

/-- The matrix $L_x\in\mathrm{GL}_4(\mathbb A_F)$ of left multiplication by $x\in(\mathbb H\otimes\mathbb A)^\times$ in the
basis $1,i,j,k$. -/
def quatLmat (x : (QuatAdele a b)ˣ) : GL (Fin 4) (Adeles F) :=
  Units.map (Algebra.leftMulMatrix (QuaternionAlgebra.basisOneIJK _ _ _)).toMonoidHom x

theorem quatLmat_mulVec (x : (QuatAdele a b)ˣ) (y : QuatAdele a b) :
    (quatLmat x : Matrix (Fin 4) (Fin 4) (Adeles F)) *ᵥ QuaternionAlgebra.linearEquivTuple _ _ _ y =
      QuaternionAlgebra.linearEquivTuple _ _ _ ((x : QuatAdele a b) * y) :=
  Algebra.leftMulMatrix_mulVec_repr _ _ _

theorem det_quatLmat (x : (QuatAdele a b)ˣ) :
    ((GeneralLinearGroup.det (quatLmat x) : (Adeles F)ˣ) : Adeles F) =
      (((x : QuatAdele a b) * star (x : QuatAdele a b)).re) ^ 2 := by
  change (Algebra.leftMulMatrix (QuaternionAlgebra.basisOneIJK _ _ _) (x : QuatAdele a b)).det = _
  rw [Algebra.leftMulMatrix_apply, LinearMap.det_toMatrix]
  exact QuaternionAlgebra.det_mulLeft _ _ _

/-- The reduced norm $\operatorname{nrd}(x) = x\bar x$ of $x\in(\mathbb H\otimes\mathbb A)^\times$, as an idele. -/
noncomputable def nrdUnit (x : (QuatAdele a b)ˣ) : (Adeles F)ˣ :=
  (((isUnit_pow_iff (two_ne_zero)).mp
    (det_quatLmat x ▸ (GeneralLinearGroup.det (quatLmat x)).isUnit))).unit

@[simp] theorem nrdUnit_val (x : (QuatAdele a b)ˣ) :
    ((nrdUnit x : (Adeles F)ˣ) : Adeles F) = ((x : QuatAdele a b) * star (x : QuatAdele a b)).re := rfl

theorem det_quatLmat_eq (x : (QuatAdele a b)ˣ) : GeneralLinearGroup.det (quatLmat x) = nrdUnit x ^ 2 :=
  Units.ext (by rw [det_quatLmat, Units.val_pow_eq_pow_val, nrdUnit_val])

theorem ideleNorm_det_quatLmat (x : (QuatAdele a b)ˣ) :
    ideleNorm F (GeneralLinearGroup.det (quatLmat x)) = ideleNorm F (nrdUnit x) ^ 2 := by
  rw [det_quatLmat_eq, sq, ideleNorm_mul, sq]

/-- **Scaling by $(\mathbb H\otimes\mathbb A)^\times$.** In the coordinates $1,i,j,k$, left multiplication by $x$ scales
the (coordinate) self-dual measure of $\mathbb A_F^4$ by $\|\operatorname{nrd}x\|_{\mathbb A}^{-2}$. -/
@[kb "weil1982" "§2.1 [unverified page]"]
theorem map_quatLmat_muAddVec (x : (QuatAdele a b)ˣ) :
    Measure.map (quatLmat x : Matrix (Fin 4) (Fin 4) (Adeles F)).mulVec (muAddVec F (Fin 4)) =
      ENNReal.ofReal (ideleNorm F (nrdUnit x) ^ 2)⁻¹ • muAddVec F (Fin 4) := by
  rw [map_mulVec_muAddVec, ideleNorm_det_quatLmat]

/-- **Twisted adelic Minkowski for $(\mathbb H\otimes\mathbb A)^\times$** (coordinates $1,i,j,k$, coordinate self-dual
measure). If $2^{4[F:\mathbb Q]}\,\|\operatorname{nrd}x\|_{\mathbb A}^2 < \mu_\infty^4(C_\infty)\,\mu_f^4(H)$, then
$x\xi\in C_\infty\times H$ for some $0\ne\xi\in\mathbb H[F,a,b]$. -/
@[kb "weil1982" "§2.1 [unverified page]"]
theorem adelicMinkowski_quat_smul (x : (QuatAdele a b)ˣ) {C : Set (Fin 4 → mixedSpace F)}
    (h_symm : ∀ x ∈ C, -x ∈ C) (h_conv : Convex ℝ C) (hC : MeasurableSet C) (H : AddSubgroup (Fin 4 → AF))
    (hH : MeasurableSet (H : Set (Fin 4 → AF)))
    (h : 2 ^ (Fintype.card (Fin 4) * finrank ℚ F) * ENNReal.ofReal (ideleNorm F (nrdUnit x) ^ 2) <
      muInfVec F (Fin 4) C * muFinVec F (Fin 4) H) :
    ∃ ξ : ℍ[F,a,b], ξ ≠ 0 ∧ QuaternionAlgebra.linearEquivTuple _ _ _ ((x : QuatAdele a b) * quatDiag a b ξ) ∈
      boxSet C (H : Set (Fin 4 → AF)) := by
  obtain ⟨η, hη, hmem⟩ := adelicMinkowski_GL (quatLmat x) h_symm h_conv hC H hH
    (by rwa [ideleNorm_det_quatLmat])
  refine ⟨(QuaternionAlgebra.linearEquivTuple (R := F) a 0 b).symm η,
    fun h0 => hη ((LinearEquiv.map_eq_zero_iff _).mp h0), ?_⟩
  rw [← quatLmat_mulVec, linearEquivTuple_quatDiag]
  change (quatLmat x : Matrix (Fin 4) (Fin 4) (Adeles F)) *ᵥ diagVec F (Fin 4)
    (QuaternionAlgebra.linearEquivTuple (R := F) a 0 b
      ((QuaternionAlgebra.linearEquivTuple (R := F) a 0 b).symm η)) ∈ _
  rwa [LinearEquiv.apply_symm_apply]

/-- **Twisted adelic Minkowski for $(\mathbb H\otimes\mathbb A)^\times$, compact form** (the input to Fujisaki's lemma). For every $B$ there is a compact $\mathcal C\subseteq\mathbb A_F^4$ such that every $x\in(\mathbb H\otimes\mathbb A)^\times$
with $\|\operatorname{nrd}x\|_{\mathbb A}\le B$ has $x\xi\in\mathcal C$ (coordinates) for some
$0\ne\xi\in\mathbb H[F,a,b]$. -/
@[kb "weil1982" "§2.1 [unverified page]"]
theorem exists_isCompact_forall_quat_mul_mem (B : ℝ) :
    ∃ K : Set (AdeleSpace F (Fin 4)), IsCompact K ∧
      ∀ x : (QuatAdele a b)ˣ, ideleNorm F (nrdUnit x) ≤ B →
        ∃ ξ : ℍ[F,a,b], ξ ≠ 0 ∧
          QuaternionAlgebra.linearEquivTuple _ _ _ ((x : QuatAdele a b) * quatDiag a b ξ) ∈ K := by
  obtain ⟨K, hK, hKM⟩ := exists_isCompact_forall_GL_mulVec_mem (F := F) (ι := Fin 4) (B ^ 2)
  refine ⟨K, hK, fun x hx => ?_⟩
  obtain ⟨η, hη, hmem⟩ := hKM (quatLmat x) (by
    rw [ideleNorm_det_quatLmat]
    exact pow_le_pow_left₀ (ideleNorm_pos _).le hx 2)
  refine ⟨(QuaternionAlgebra.linearEquivTuple (R := F) a 0 b).symm η,
    fun h0 => hη ((LinearEquiv.map_eq_zero_iff _).mp h0), ?_⟩
  rw [← quatLmat_mulVec, linearEquivTuple_quatDiag]
  change (quatLmat x : Matrix (Fin 4) (Fin 4) (Adeles F)) *ᵥ diagVec F (Fin 4)
    (QuaternionAlgebra.linearEquivTuple (R := F) a 0 b
      ((QuaternionAlgebra.linearEquivTuple (R := F) a 0 b).symm η)) ∈ _
  rwa [LinearEquiv.apply_symm_apply]

end Quaternion

end

end QuadFormsKB.Tamagawa.Measure.Weil
