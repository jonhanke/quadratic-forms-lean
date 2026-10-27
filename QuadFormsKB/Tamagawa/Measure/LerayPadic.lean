import QuadFormsKB.Tamagawa.Measure.LocalSO
import QuadFormsKB.Tamagawa.Measure.Weil.GLScaling
import QuadFormsKB.Tamagawa.LocalZeta

/-!
# The $p$-adic Leray (gauge-form) measure on $O(V)(F_v)$ is `muLoc`

$F_v$ = `v.adicCompletion F` (any finite place, **dyadic included**), $Q_0$ a nondegenerate form over $\mathcal O_F$ in $n$
variables, $V = (F^n, Q_0)$, $H$ its Hessian, $q = N(v)$. On $M_n(F_v)$ we use the standard Haar measure
$dX = \prod_{i,j}dx_{ij}$ (`volM`, $\mathrm{vol}(M_n(\mathfrak o_v)) = 1$) and the fibre map
$X \mapsto \Phi(X) = Q_0\circ X$ (the form $y \mapsto Q_0(Xy)$, `QuadForm.compMat`), whose fibre over $\Phi(1) = Q_0$ is
$O(V)(F_v)$, in the $N = n(n+1)/2$ coefficient coordinates (`phi`). Weil's gauge form $\omega = dX/d\Phi$ on
$O(V)$ (AAG §2.2 [unverified]) gives the measure characterized by the **Leray limit**
$$|\omega|_v(W \cap O(V)) = \lim_{k\to\infty} q^{kN}\,\mathrm{vol}\{X \in W : \Phi(X) \equiv Q_0 \bmod \mathfrak p_v^k\}
\qquad (W \subseteq M_n(F_v) \text{ compact open}),$$
the $p$-adic counterpart of the real `LerayReal.tendsto_lerayMeasure` (`lerayApprox` here,
`thick k` the congruence set).

**Main theorem** (`lerayApprox_eventually_eq`): for every compact open $W \subseteq M_n(F_v)$ the normalized volumes
$q^{kN}\mathrm{vol}(W \cap \Phi^{-1}(Q_0 + \mathfrak p^k))$ are **eventually equal** to $\mu_v(W \cap O(V)(F_v))$, where
$\mu_v$ = `muLoc v Q₀ 1` is the density-normalized Haar measure ($\mu_v(O(L_v)) = \beta_v(L, L)$). So $\mu_v$
**is** Weil's gauge-form measure $|\omega|_v$ at every finite place, and `muLocSO v Q₀ 1` is $|\omega|_v$ on $SO(V)(F_v)$
(`lerayApprox_eventually_eq_muLocSO`). No inverse function theorem is used:
* `volM_intMat_inter_thick`: $\mathrm{vol}(M_n(\mathfrak o) \cap \Phi^{-1}(Q_0 + \mathfrak p^k)) = A_{\pi^k}(Q_0, Q_0)\,q^{-kn^2}$,
  so on $W = M_n(\mathfrak o)$ the Leray quotient is $A_{\pi^k}/q^{k\dim}$, eventually $\beta_v(L,L)$ (Siegel's stabilization,
  `NF.localDensityForm_self_eventually_eq`);
* left translation by $g \in O(V)(F_v)$ preserves $dX$ ($|\det g|_v = 1$; `glHaarChar_eq_of_field`) and the
  congruence sets ($\Phi(gX) = \Phi(X)$), so the Leray quotients are left invariant (`lerayApprox_smul`);
* a compact $W$ missing $O(V)$ misses the congruence sets for large $k$ (`eventually_inter_thick_eq_empty`);
* the principal congruence subgroups $K_m = O(V) \cap (1 + \pi^mM_n(\mathfrak o))$ ($m \ge 1$) are a neighbourhood basis
  of $1$, and every compact open subset of $O(V)$ is a finite disjoint union of cosets $gK_m$, matched by the disjoint
  translates $g(1 + \pi^mM_n(\mathfrak o))$ in $M_n(F_v)$; comparing with $W = M_n(\mathfrak o)$ gives the value on $K_m$.

Sources: A. Weil, *Adeles and Algebraic Groups* (1982), §2.2 (gauge forms and their measures, the volume
$\int_{X(\mathfrak o)}|\omega| = \lim q^{-k\dim}\#X(\mathfrak o/\mathfrak p^k)$) [unverified]; Siegel 1935 (local densities as
limits); related: W. T. Gan and J.-K. Yu, *Group schemes and local densities*, Duke Math. J. 105 (2000); W. T. Gan,
J. Hanke and J.-K. Yu, *On an exact mass formula of Shimura*, Duke Math. J. 107 (2001) [unverified] (the same
identification via smooth integral models; not used).
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology WithZero Matrix
open scoped ENNReal NNReal Pointwise
open QuadFormsKB.Analysis QuadFormsKB.LocalDensity QuadFormsKB.LocalZeta QuadFormsKB.Lattices

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.LerayPadic

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F
local notation "πv" => LocalDensity.NF.π v

/-! ### Forms over $F_v$ determined by their Hessian -/

/-- Over a domain with $2 \ne 0$, a form is determined by its Hessian. -/
theorem QuadForm.eq_of_hessian_eq' {A : Type*} [CommRing A] [IsDomain A] (h2 : (2 : A) ≠ 0) {r : ℕ}
    {Q₁ Q₂ : QuadForm A r} (h : Q₁.hessian = Q₂.hessian) : Q₁ = Q₂ := by
  refine QuadForm.ext_upper fun i j hij => ?_
  have hij' := congrFun (congrFun h i) j
  simp only [QuadForm.hessian, Matrix.add_apply, Matrix.transpose_apply] at hij'
  rcases hij.lt_or_eq with hlt | heq
  · have h1 : Q₁.coeff j i = 0 := Q₁.upper (show id i < id j from hlt)
    have h2 : Q₂.coeff j i = 0 := Q₂.upper (show id i < id j from hlt)
    rwa [h1, h2, add_zero, add_zero] at hij'
  · subst heq
    have : (2 : A) * Q₁.coeff i i = 2 * Q₂.coeff i i := by linear_combination hij'
    exact mul_left_cancel₀ h2 this

/-- Over a domain of characteristic zero, a form is determined by its Hessian. -/
theorem QuadForm.eq_of_hessian_eq {A : Type*} [CommRing A] [IsDomain A] [CharZero A] {r : ℕ}
    {Q₁ Q₂ : QuadForm A r} (h : Q₁.hessian = Q₂.hessian) : Q₁ = Q₂ :=
  QuadForm.eq_of_hessian_eq' two_ne_zero h

variable (Q₀ : QuadForm (𝓞 F) n)

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

/-- **$Q_0$ over $F_v$**, as the base change of $Q_0 \otimes \mathfrak o_v$ (`NF.Qp`). -/
abbrev QV : QuadForm Fv n := (NF.Qp v Q₀).map (algebraMap 𝔬 Fv)

theorem hessian_QV : (QV v Q₀).hessian = (QF).hessian.map (algebraMap F Fv) := by
  ext i j
  simp only [QuadForm.hessian, QuadForm.map, Matrix.add_apply, Matrix.map_apply, Matrix.transpose_apply,
    map_add]
  rfl

/-- **The fibre of $\Phi$ over $Q_0$**: $Q_0 \circ X = Q_0$ over $F_v$ iff $X^{\mathsf T}HX = H$. -/
theorem compMat_QV_eq_iff (X : Matrix (Fin n) (Fin n) Fv) :
    (QV v Q₀).compMat X = QV v Q₀ ↔ Xᵀ * (QF).hessian.map (algebraMap F Fv) * X =
      (QF).hessian.map (algebraMap F Fv) := by
  constructor
  · intro h
    have := congrArg QuadForm.hessian h
    rwa [QuadForm.hessian_compMat, hessian_QV] at this
  · intro h
    apply QuadForm.eq_of_hessian_eq
    rw [QuadForm.hessian_compMat, hessian_QV, h]

theorem compMat_QV_orth (g : orthGroup QF Fv) :
    (QV v Q₀).compMat ((g : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) = QV v Q₀ :=
  (compMat_QV_eq_iff v Q₀ _).mpr g.2

/-! ### The congruence sets $\Phi^{-1}(Q_0 + \mathfrak p^k)$ and the Leray quotients -/

/-- **The congruence set** $\{X \in M_n(F_v) : \Phi(X) \equiv Q_0 \bmod \mathfrak p_v^k\}$: every coefficient of
$Q_0 \circ X - Q_0$ has valuation $\le q^{-k}$. -/
def thick (k : ℕ) : Set (Matrix (Fin n) (Fin n) Fv) :=
  {X | ∀ i j, Valued.v (((QV v Q₀).compMat X).coeff i j - (QV v Q₀).coeff i j) ≤ exp (-(k : ℤ))}

/-- **The standard Haar measure on $M_n(F_v)$**, $dX = \prod_{i,j}dx_{ij}$ with $\mathrm{vol}(\mathfrak o_v) = 1$
(`haarV`), taken column by column (the product of the column measures, transported by transposition). -/
def volM : Measure (Matrix (Fin n) (Fin n) Fv) :=
  (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n => haarV v).map
    (fun Y : Fin n → Fin n → Fv => (Matrix.of Y)ᵀ)

/-- **The Leray quotient** $q^{kN}\,\mathrm{vol}(W \cap \Phi^{-1}(Q_0 + \mathfrak p^k))$, $N = n(n+1)/2$ (the number of
coefficient coordinates; $q^{-kN}$ is the volume of the box $\mathfrak p^k$ in coefficient space). -/
def lerayApprox (W : Set (Matrix (Fin n) (Fin n) Fv)) (k : ℕ) : ℝ≥0∞ :=
  ((DVR.q 𝔬 : ℝ≥0∞)) ^ (k * (n * (n + 1) / 2)) * volM v (W ∩ thick v Q₀ k)

/-- **The trace of $W \subseteq M_n(F_v)$ on $O(V)(F_v)$.** -/
def traceO (W : Set (Matrix (Fin n) (Fin n) Fv)) : Set (orthGroup QF Fv) :=
  {g | ((g : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) ∈ W}

/-! ### Topology of the congruence sets -/

theorem valued_le_iff_mem_latticeV (x : Fv) (k : ℕ) :
    Valued.v x ≤ exp (-(k : ℤ)) ↔ x ∈ (latticeV v (k : ℤ) : Set Fv) := by
  rw [SetLike.mem_coe, mem_latticeV]

theorem isOpen_latticeV (k : ℤ) : IsOpen (latticeV v k : Set Fv) := by
  rw [coe_latticeV]
  exact IsUltrametricDist.isOpen_closedBall _
    (norm_pos_iff.mpr (zpow_ne_zero _ (HN.ϖ_ne_zero v))).ne'

/-- An element of $F_v$ of valuation $\le q^{-k}$ for every $k$ is $0$. -/
theorem eq_zero_of_forall_valued_le {x : Fv} (h : ∀ k : ℕ, Valued.v x ≤ exp (-(k : ℤ))) : x = 0 := by
  by_contra hx
  have hv : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  set L := WithZero.log (Valued.v x)
  have he : exp L = Valued.v x := WithZero.exp_log hv
  have h1 : exp L ≤ exp (-((L.natAbs + 1 : ℕ) : ℤ)) := by rw [he]; exact h _
  rw [exp_le_exp] at h1
  omega

theorem continuous_compMat_coeff (Q : QuadForm Fv n) (i j : Fin n) :
    Continuous fun X : Matrix (Fin n) (Fin n) Fv => (Q.compMat X).coeff i j := by
  have hcol : ∀ a : Fin n, Continuous fun X : Matrix (Fin n) (Fin n) Fv => fun l => X l a :=
    fun a => continuous_pi fun l => continuous_id.matrix_elem l a
  simp only [QuadForm.compMat_coeff]
  split_ifs
  · simp only [QuadForm.eval_eq_dotProduct']
    exact (hcol i).dotProduct (continuous_const.matrix_mulVec (hcol i))
  · exact (hcol i).dotProduct (continuous_const.matrix_mulVec (hcol j))
  · exact continuous_const

theorem thick_eq (k : ℕ) : thick v Q₀ k = ⋂ i, ⋂ j,
    (fun X : Matrix (Fin n) (Fin n) Fv => ((QV v Q₀).compMat X).coeff i j - (QV v Q₀).coeff i j) ⁻¹'
      (latticeV v (k : ℤ) : Set Fv) := by
  ext X
  simp only [thick, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, valued_le_iff_mem_latticeV]

theorem isClosed_thick (k : ℕ) : IsClosed (thick v Q₀ k) := by
  rw [thick_eq]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    (isCompact_latticeV v k).isClosed.preimage ((continuous_compMat_coeff v _ i j).sub continuous_const)

theorem isOpen_thick (k : ℕ) : IsOpen (thick v Q₀ k) := by
  rw [thick_eq]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (isOpen_latticeV v k).preimage ((continuous_compMat_coeff v _ i j).sub continuous_const)

theorem measurableSet_thick (k : ℕ) : MeasurableSet (thick v Q₀ k) := (isClosed_thick v Q₀ k).measurableSet

theorem thick_antitone : Antitone (thick v Q₀) := by
  intro k l hkl X hX i j
  exact (hX i j).trans (exp_le_exp.mpr (by omega))

/-- **The intersection of the congruence sets is the fibre** $\Phi^{-1}(Q_0)$, i.e. the matrices of $O(V)(F_v)$. -/
theorem mem_iInter_thick_iff (X : Matrix (Fin n) (Fin n) Fv) :
    (∀ k, X ∈ thick v Q₀ k) ↔ (QV v Q₀).compMat X = QV v Q₀ := by
  constructor
  · intro h
    refine QuadForm.ext_upper fun i j _ => ?_
    exact sub_eq_zero.mp (eq_zero_of_forall_valued_le v fun k => h k i j)
  · intro h k i j
    rw [h, sub_self, map_zero]
    exact zero_le

/-- A matrix in the fibre $\Phi^{-1}(Q_0)$ is the matrix of an element of $O(V)(F_v)$ ($Q_0$ nondegenerate). -/
theorem exists_orth_of_compMat_eq (hQ : Q₀.Nondegenerate) {X : Matrix (Fin n) (Fin n) Fv}
    (hX : (QV v Q₀).compMat X = QV v Q₀) :
    ∃ g : orthGroup QF Fv, ((g : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) = X := by
  have h := (compMat_QV_eq_iff v Q₀ X).mp hX
  have hH : ((QF).hessian.map (algebraMap F Fv)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).mpr (Measure.nondegenerate_QF Q₀ hQ)
  have hdet : X.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det h
    rw [det_mul, det_mul, det_transpose, h0, zero_mul, zero_mul] at this
    exact hH this.symm
  exact ⟨⟨GeneralLinearGroup.mkOfDetNeZero X hdet, h⟩, rfl⟩

/-- **A compact set missing $O(V)(F_v)$ misses the congruence sets** for all large $k$. -/
theorem eventually_inter_thick_eq_empty (hQ : Q₀.Nondegenerate) {W : Set (Matrix (Fin n) (Fin n) Fv)}
    (hW : IsCompact W) (hW0 : traceO v Q₀ W = ∅) : ∀ᶠ k in atTop, W ∩ thick v Q₀ k = ∅ := by
  have hdisj : Disjoint W (⋂ k, thick v Q₀ k) := by
    rw [Set.disjoint_left]
    intro X hXW hX
    obtain ⟨g, hg⟩ := exists_orth_of_compMat_eq v Q₀ hQ ((mem_iInter_thick_iff v Q₀ X).mp (Set.mem_iInter.mp hX))
    have : g ∈ traceO v Q₀ W := by simp only [traceO, Set.mem_ofPred_eq, hg, hXW]
    rw [hW0] at this; exact this
  obtain ⟨k₀, hk₀⟩ := hW.elim_directed_family_closed (thick v Q₀) (isClosed_thick v Q₀) hdisj
    (thick_antitone v Q₀).directed_ge
  rw [eventually_atTop]
  refine ⟨k₀, fun k hk => ?_⟩
  exact Set.disjoint_iff_inter_eq_empty.mp (hk₀.mono_right (thick_antitone v Q₀ hk))

/-! ### Left invariance -/

/-- **$\Phi(gX) = \Phi(X)$** for $g \in O(V)(F_v)$, so the congruence sets are left $O(V)(F_v)$-invariant. -/
theorem preimage_mul_thick (g : orthGroup QF Fv) (k : ℕ) :
    (fun X => ((g : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) * X) ⁻¹' thick v Q₀ k = thick v Q₀ k := by
  ext X
  simp only [Set.mem_preimage, thick, Set.mem_ofPred_eq]
  rw [← QuadForm.compMat_mul, compMat_QV_orth]

theorem distribHaarChar_eq_one_of_sq {u : Fvˣ} (hu : u ^ 2 = 1) : distribHaarChar Fv u = 1 := by
  have h : (distribHaarChar Fv u) ^ 2 = 1 := by rw [← map_pow, hu, map_one]
  exact (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).mp h

/-- $x \mapsto gx$ preserves Haar measure on $F_v^n$ for $g \in O(V)(F_v)$ ($|\det g|_v = 1$;
`glHaarChar_eq_of_field`). -/
theorem measurePreserving_mulVec (hQ : Q₀.Nondegenerate) (g : orthGroup QF Fv) :
    MeasurePreserving (((g : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv).mulVec)
      (Measure.pi fun _ : Fin n => haarV v) (Measure.pi fun _ : Fin n => haarV v) := by
  have : (Measure.pi fun _ : Fin n => haarV v).Regular :=
    Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  refine ⟨(continuous_const.matrix_mulVec continuous_id).measurable, ?_⟩
  rw [map_mulVec_eq_glHaarChar_inv, glHaarChar_eq_of_field]
  have hdet : GeneralLinearGroup.det (g : GL (Fin n) Fv) ^ 2 = 1 := by
    ext
    simp only [Units.val_pow_eq_pow_val, GeneralLinearGroup.val_det_apply, Units.val_one]
    rcases det_eq_one_or_neg_one QF (Measure.nondegenerate_QF Q₀ hQ) g with h | h <;> rw [h] <;> norm_num
  rw [distribHaarChar_eq_one_of_sq v hdet, inv_one, one_smul]

theorem measurable_ofT : Measurable fun Y : Fin n → Fin n → Fv => (Matrix.of Y)ᵀ :=
  measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j =>
    (measurable_pi_apply i).comp (measurable_pi_apply j)

/-- **Left translation by $g \in O(V)(F_v)$ preserves $dX$** on $M_n(F_v)$. -/
theorem measurePreserving_mul (hQ : Q₀.Nondegenerate) (g : orthGroup QF Fv) :
    MeasurePreserving (fun X => ((g : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) * X) (volM v) (volM v) := by
  set G := ((g : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv)
  have hφ : MeasurePreserving (fun (Y : Fin n → Fin n → Fv) j => G *ᵥ Y j)
      (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n => haarV v)
      (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n => haarV v) :=
    measurePreserving_pi _ _ fun _ => measurePreserving_mulVec v Q₀ hQ g
  have hmul : Measurable fun X : Matrix (Fin n) (Fin n) Fv => G * X :=
    (continuous_const.matrix_mul continuous_id).measurable
  have hcomm : (fun X => G * X) ∘ (fun Y : Fin n → Fin n → Fv => (Matrix.of Y)ᵀ) =
      (fun Y : Fin n → Fin n → Fv => (Matrix.of Y)ᵀ) ∘ (fun Y j => G *ᵥ Y j) := by
    funext Y; ext i j
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  refine ⟨hmul, ?_⟩
  rw [volM, Measure.map_map hmul (measurable_ofT v), hcomm,
    ← Measure.map_map (measurable_ofT v) hφ.measurable, hφ.map_eq]

/-- **The Leray quotients are left $O(V)(F_v)$-invariant.** -/
theorem lerayApprox_preimage_mul (hQ : Q₀.Nondegenerate) (g : orthGroup QF Fv)
    {W : Set (Matrix (Fin n) (Fin n) Fv)} (hW : MeasurableSet W) (k : ℕ) :
    lerayApprox v Q₀ ((fun X => ((g : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) * X) ⁻¹' W) k =
      lerayApprox v Q₀ W k := by
  unfold lerayApprox
  congr 1
  rw [← preimage_mul_thick v Q₀ g k, ← Set.preimage_inter, preimage_mul_thick v Q₀ g k]
  exact (measurePreserving_mul v Q₀ hQ g).measure_preimage
    (hW.inter (measurableSet_thick v Q₀ k)).nullMeasurableSet

/-! ### The count on $M_n(\mathfrak o_v)$ -/

/-- The integral matrices $M_n(\mathfrak o_v)$ (`intMat`). -/
abbrev intM : Set (Matrix (Fin n) (Fin n) Fv) := Measure.intMat v

/-- The matrix over $\mathfrak o_v$ underlying an integral matrix. -/
def toOM (X : Matrix (Fin n) (Fin n) Fv) (hX : X ∈ intM v) : Matrix (Fin n) (Fin n) 𝔬 :=
  fun i j => ⟨X i j, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (hX i j)⟩

theorem map_toOM (X : Matrix (Fin n) (Fin n) Fv) (hX : X ∈ intM v) : (toOM v X hX).map (algebraMap 𝔬 Fv) = X := by
  ext i j; rfl

/-- Reduction $M_n(\mathfrak o_v) \to M_n(\mathfrak o_v/\mathfrak p_v^k)$. -/
def redM (k : ℕ) (X : Matrix (Fin n) (Fin n) Fv) (hX : X ∈ intM v) : Matrix (Fin n) (Fin n) (RQ v k) :=
  (toOM v X hX).map (Ideal.Quotient.mk _)

/-- A lift of a residue matrix. -/
def liftM (k : ℕ) (Y : Matrix (Fin n) (Fin n) (RQ v k)) : Matrix (Fin n) (Fin n) Fv :=
  fun i j => ((Quotient.out (Y i j) : 𝔬) : Fv)

/-- The fibre of the reduction over $Y$: $\tilde Y + \pi^kM_n(\mathfrak o_v)$. -/
def fiberM (k : ℕ) (Y : Matrix (Fin n) (Fin n) (RQ v k)) : Set (Matrix (Fin n) (Fin n) Fv) :=
  {X | ∀ i j, Valued.v (X i j - liftM v k Y i j) ≤ exp (-(k : ℤ))}

theorem mem_fiberM_iff {k : ℕ} {Y : Matrix (Fin n) (Fin n) (RQ v k)} {X : Matrix (Fin n) (Fin n) Fv} :
    X ∈ fiberM v k Y ↔ ∃ hX : X ∈ intM v, redM v k X hX = Y := by
  constructor
  · intro h
    have hX : X ∈ intM v := by
      intro i j
      have h1 : Valued.v (X i j - liftM v k Y i j) ≤ 1 := (h i j).trans (by rw [← exp_zero, exp_le_exp]; omega)
      have h2 : Valued.v (liftM v k Y i j) ≤ 1 := (Quotient.out (Y i j)).2
      calc Valued.v (X i j) = Valued.v ((X i j - liftM v k Y i j) + liftM v k Y i j) := by ring_nf
        _ ≤ max _ _ := Valuation.map_add _ _ _
        _ ≤ 1 := max_le h1 h2
    refine ⟨hX, ?_⟩
    ext i j
    rw [redM, Matrix.map_apply, ← Ideal.Quotient.mk_out (Y i j), valued_sub_le_iff_mk_eq]
    exact h i j
  · rintro ⟨hX, rfl⟩ i j
    exact (valued_sub_le_iff_mk_eq v k (toOM v X hX i j) (Quotient.out (redM v k X hX i j))).mp
      (by rw [Ideal.Quotient.mk_out]; rfl)

theorem fiberM_disjoint {k : ℕ} {Y Y' : Matrix (Fin n) (Fin n) (RQ v k)} (h : Y ≠ Y') :
    Disjoint (fiberM v k Y) (fiberM v k Y') := by
  rw [Set.disjoint_left]
  intro X hX hX'
  obtain ⟨h1, rfl⟩ := (mem_fiberM_iff v).mp hX
  obtain ⟨h2, e⟩ := (mem_fiberM_iff v).mp hX'
  exact h e

/-- **On $M_n(\mathfrak o_v)$ the congruence condition is a condition mod $\pi^k$:** $X \in \Phi^{-1}(Q_0 + \mathfrak p^k)$ iff
$(Q_0 \bmod \pi^k)\circ(X \bmod \pi^k) = Q_0 \bmod \pi^k$. -/
theorem mem_thick_iff_redM {k : ℕ} {X : Matrix (Fin n) (Fin n) Fv} (hX : X ∈ intM v) :
    X ∈ thick v Q₀ k ↔ ((NF.Qp v Q₀).map (Ideal.Quotient.mk _)).compMat (redM v k X hX) =
      (NF.Qp v Q₀).map (Ideal.Quotient.mk (Ideal.span {πv ^ k})) := by
  have e1 : (QV v Q₀).compMat X = ((NF.Qp v Q₀).compMat (toOM v X hX)).map (algebraMap 𝔬 Fv) := by
    conv_lhs => rw [← map_toOM v X hX]
    exact QuadForm.map_compMat _ _ _
  have e2 : ((NF.Qp v Q₀).map (Ideal.Quotient.mk _)).compMat (redM v k X hX) =
      ((NF.Qp v Q₀).compMat (toOM v X hX)).map (Ideal.Quotient.mk (Ideal.span {πv ^ k})) :=
    QuadForm.map_compMat _ _ _
  have cm : ∀ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (S : QuadForm A n) (i j : Fin n),
      (S.map f).coeff i j = f (S.coeff i j) := fun _ _ _ _ => rfl
  rw [e2]
  constructor
  · intro h
    refine QuadForm.ext_upper fun i j _ => ?_
    rw [cm, cm, valued_sub_le_iff_mk_eq]
    have := h i j
    rw [e1, cm] at this
    exact this
  · intro h i j
    have := congrArg (fun S : QuadForm (RQ v k) n => S.coeff i j) h
    simp only [cm] at this
    rw [valued_sub_le_iff_mk_eq] at this
    rw [e1, cm]
    exact this

open Classical in
theorem intM_inter_thick_eq (k : ℕ) [Fintype (RQ v k)] :
    intM v ∩ thick v Q₀ k = ⋃ Y ∈ (Finset.univ.filter fun Y : Matrix (Fin n) (Fin n) (RQ v k) =>
      ((NF.Qp v Q₀).map (Ideal.Quotient.mk _)).compMat Y =
        (NF.Qp v Q₀).map (Ideal.Quotient.mk (Ideal.span {πv ^ k}))), fiberM v k Y := by
  ext X
  simp only [Set.mem_inter_iff, Set.mem_iUnion, Finset.mem_univ, true_and, exists_prop,
    Finset.mem_filter]
  constructor
  · rintro ⟨hX, hT⟩
    exact ⟨redM v k X hX, (mem_thick_iff_redM v Q₀ hX).mp hT, (mem_fiberM_iff v).mpr ⟨hX, rfl⟩⟩
  · rintro ⟨Y, hY, hXY⟩
    obtain ⟨hX, rfl⟩ := (mem_fiberM_iff v).mp hXY
    exact ⟨hX, (mem_thick_iff_redM v Q₀ hX).mpr hY⟩

theorem fiberM_eq_preimage (k : ℕ) (Y : Matrix (Fin n) (Fin n) (RQ v k)) :
    (fun Y' : Fin n → Fin n → Fv => (Matrix.of Y')ᵀ) ⁻¹' fiberM v k Y =
      Set.univ.pi fun j => Set.univ.pi fun i =>
        (fun z : Fv => z + -liftM v k Y i j) ⁻¹' (latticeV v (k : ℤ) : Set Fv) := by
  ext Y'
  simp only [Set.mem_preimage, fiberM, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies,
    SetLike.mem_coe, mem_latticeV, Matrix.transpose_apply, Matrix.of_apply, ← sub_eq_add_neg]
  exact ⟨fun h j i => h i j, fun h i j => h j i⟩

theorem measurableSet_fiberM (k : ℕ) (Y : Matrix (Fin n) (Fin n) (RQ v k)) : MeasurableSet (fiberM v k Y) := by
  have : fiberM v k Y = ⋂ i, ⋂ j, (fun X : Matrix (Fin n) (Fin n) Fv => X i j + -liftM v k Y i j) ⁻¹'
      (latticeV v (k : ℤ) : Set Fv) := by
    ext X; simp [fiberM, mem_latticeV, sub_eq_add_neg]
  rw [this]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
    (measurableSet_latticeV v k).preimage ((continuous_id.matrix_elem i j).add continuous_const).measurable

theorem volM_fiberM (k : ℕ) (Y : Matrix (Fin n) (Fin n) (RQ v k)) :
    volM v (fiberM v k Y) = haarV v (latticeV v (k : ℤ)) ^ (n * n) := by
  rw [volM, Measure.map_apply (measurable_ofT v) (measurableSet_fiberM v k Y), fiberM_eq_preimage,
    Measure.pi_pi]
  simp only [Measure.pi_pi, measure_preimage_add_right, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← pow_mul]

/-- **The volume of the congruence set in $M_n(\mathfrak o_v)$:**
$\mathrm{vol}(M_n(\mathfrak o_v) \cap \Phi^{-1}(Q_0 + \mathfrak p_v^k)) = A_{\pi^k}(Q_0, Q_0)\cdot\mathrm{vol}(\mathfrak p_v^k)^{n^2}$
(every finite place). The set is the disjoint union of the cosets $\tilde Y + \pi^kM_n(\mathfrak o_v)$ over the solutions
$Y$ mod $\pi^k$ (the matrix version of `volume_congSet`; Weil 1982, §4.3, p. 89, for vectors). -/
@[kb "weil1982" "§2.2 (volume of X(o) by counting mod p^k) [unverified]"]
theorem volM_intM_inter_thick (k : ℕ) :
    volM v (intM v ∩ thick v Q₀ k) =
      (DVR.repCountForm (NF.Qp v Q₀) (NF.Qp v Q₀) πv k : ℝ≥0∞) * haarV v (latticeV v (k : ℤ)) ^ (n * n) := by
  classical
  have := DVR.finite_quot_pow πv (NF.irreducible_π v) k
  let _ : Fintype (RQ v k) := Fintype.ofFinite _
  rw [intM_inter_thick_eq v Q₀ k, measure_biUnion_finset]
  · simp only [volM_fiberM, Finset.sum_const, nsmul_eq_mul]
    congr 1
    rw [DVR.repCountForm, Nat.card_eq_fintype_card, Fintype.card_subtype]
  · intro Y _ Y' _ h
    exact fiberM_disjoint v h
  · intro Y _; exact measurableSet_fiberM v k Y

theorem haarV_latticeV_nat (k : ℕ) : haarV v (latticeV v (k : ℤ)) = ((DVR.q 𝔬 : ℝ≥0∞) ^ k)⁻¹ := by
  have h := measure_latticeV_zero v (haarV v) k
  rw [haarV_latticeV_zero] at h
  have hq0 : (DVR.q 𝔬 : ℝ≥0∞) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast (q_pos v).ne')
  have hqt : (DVR.q 𝔬 : ℝ≥0∞) ^ k ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  exact ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h.symm)

theorem two_mul_choose (n : ℕ) : n * (n + 1) / 2 + n * (n - 1) / 2 = n * n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 : 2 * ((m + 1) * (m + 1 + 1) / 2) = (m + 1) * (m + 1 + 1) :=
    Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self (m + 1))
  simp only [Nat.add_sub_cancel]
  have h2 : 2 * ((m + 1) * m / 2) = (m + 1) * m := by
    rw [mul_comm (m + 1) m]; exact Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self m)
  have : 2 * ((m + 1) * (m + 1 + 1) / 2 + (m + 1) * m / 2) = 2 * ((m + 1) * (m + 1)) := by
    rw [mul_add, h1, h2]; ring
  omega

/-- **The Leray quotient of $M_n(\mathfrak o_v)$ is Siegel's normalized count:**
$q^{kN}\mathrm{vol}(M_n(\mathfrak o_v)\cap\Phi^{-1}(Q_0+\mathfrak p^k)) = A_{\pi^k}(Q_0,Q_0)/q^{k\,n(n-1)/2}$. -/
theorem lerayApprox_intM (k : ℕ) :
    lerayApprox v Q₀ (intM v) k = (DVR.repCountForm (NF.Qp v Q₀) (NF.Qp v Q₀) πv k : ℝ≥0∞) /
      (DVR.q 𝔬 : ℝ≥0∞) ^ (k * (n * (n - 1) / 2)) := by
  have hq0 : (DVR.q 𝔬 : ℝ≥0∞) ≠ 0 := by exact_mod_cast (q_pos v).ne'
  have hqt : (DVR.q 𝔬 : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  set a := (DVR.q 𝔬 : ℝ≥0∞) ^ (k * (n * (n + 1) / 2))
  set b := (DVR.q 𝔬 : ℝ≥0∞) ^ (k * (n * (n - 1) / 2))
  set c := (DVR.repCountForm (NF.Qp v Q₀) (NF.Qp v Q₀) πv k : ℝ≥0∞)
  have hab : ((DVR.q 𝔬 : ℝ≥0∞) ^ k)⁻¹ ^ (n * n) = (a * b)⁻¹ := by
    have : a * b = ((DVR.q 𝔬 : ℝ≥0∞) ^ k) ^ (n * n) := by
      rw [← pow_add, ← mul_add, two_mul_choose, pow_mul]
    rw [this, ← ENNReal.inv_pow]
  rw [lerayApprox, volM_intM_inter_thick, haarV_latticeV_nat, hab,
    ENNReal.mul_inv (Or.inl (pow_ne_zero _ hq0)) (Or.inl (ENNReal.pow_ne_top hqt))]
  calc a * (c * (a⁻¹ * b⁻¹)) = (a * a⁻¹) * (c * b⁻¹) := by ring
    _ = _ := by rw [ENNReal.mul_inv_cancel (pow_ne_zero _ hq0) (ENNReal.pow_ne_top hqt), one_mul,
      div_eq_mul_inv]

/-- **On $M_n(\mathfrak o_v)$ the Leray quotients are eventually $\beta_v(L, L) = \mu_v(O(L_v))$** ($Q_0$ nondegenerate;
Siegel's stabilization). -/
theorem lerayApprox_intM_eventually (hQ : Q₀.Nondegenerate) :
    ∀ᶠ k in atTop, lerayApprox v Q₀ (intM v) k = ENNReal.ofReal (NF.localDensityForm v Q₀ Q₀) := by
  filter_upwards [NF.localDensityForm_self_eventually_eq v Q₀ hQ] with k hk
  rw [lerayApprox_intM, ← hk, NF.repCountForm_eq_completion, ← NF.q_completion]
  have hq : (0 : ℝ) < (DVR.q 𝔬 : ℝ) := by exact_mod_cast q_pos v
  rw [ENNReal.ofReal_div_of_pos (pow_pos hq _), ENNReal.ofReal_natCast, ENNReal.ofReal_pow hq.le,
    ENNReal.ofReal_natCast]

/-! ### Principal congruence subgroups $K_m = O(V)(F_v) \cap (1 + \pi^mM_n(\mathfrak o_v))$ -/

/-- **The ball** $1 + \pi^mM_n(\mathfrak o_v) \subseteq M_n(F_v)$. -/
def ballOne (m : ℕ) : Set (Matrix (Fin n) (Fin n) Fv) :=
  {X | ∀ i j, Valued.v (X i j - (1 : Matrix (Fin n) (Fin n) Fv) i j) ≤ exp (-(m : ℤ))}

theorem valued_one_apply_le (i j : Fin n) : Valued.v ((1 : Matrix (Fin n) (Fin n) Fv) i j) ≤ 1 := by
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem coe_one_apply (i j : Fin n) :
    (((1 : Matrix (Fin n) (Fin n) 𝔬) i j : 𝔬) : Fv) = (1 : Matrix (Fin n) (Fin n) Fv) i j := by
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem exp_neg_le_one (m : ℕ) : exp (-(m : ℤ)) ≤ (1 : ℤᵐ⁰) := by
  rw [← exp_zero, exp_le_exp]; omega

theorem ballOne_subset_intM (m : ℕ) : ballOne v m ⊆ intM v (n := n) := by
  intro X hX i j
  calc Valued.v (X i j) = Valued.v ((X i j - (1 : Matrix (Fin n) (Fin n) Fv) i j) +
        (1 : Matrix (Fin n) (Fin n) Fv) i j) := by ring_nf
    _ ≤ max _ _ := Valuation.map_add _ _ _
    _ ≤ 1 := max_le ((hX i j).trans (exp_neg_le_one m)) (valued_one_apply_le v i j)

theorem valued_mul_apply_le {A B : Matrix (Fin n) (Fin n) Fv} {a b : ℤᵐ⁰}
    (hA : ∀ i j, Valued.v (A i j) ≤ a) (hB : ∀ i j, Valued.v (B i j) ≤ b) (i j : Fin n) :
    Valued.v ((A * B) i j) ≤ a * b := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul]; exact mul_le_mul' (hA i l) (hB l j)

theorem mul_mem_ballOne {m : ℕ} {X Y : Matrix (Fin n) (Fin n) Fv} (hX : X ∈ ballOne v m) (hY : Y ∈ ballOne v m) :
    X * Y ∈ ballOne v m := by
  intro i j
  have e : X * Y - 1 = (X - 1) * (Y - 1) + (X - 1) + (Y - 1) := by noncomm_ring
  have e' : (X * Y) i j - (1 : Matrix (Fin n) (Fin n) Fv) i j =
      ((X - 1) * (Y - 1)) i j + (X - 1) i j + (Y - 1) i j := by
    rw [← Matrix.sub_apply, e]; rfl
  rw [e']
  have h1 : Valued.v (((X - 1) * (Y - 1)) i j) ≤ exp (-(m : ℤ)) :=
    (valued_mul_apply_le v hX hY i j).trans (by
      calc exp (-(m : ℤ)) * exp (-(m : ℤ)) ≤ exp (-(m : ℤ)) * 1 := mul_le_mul_right (exp_neg_le_one m) _
        _ = _ := mul_one _)
  refine (Valuation.map_add _ _ _).trans (max_le ((Valuation.map_add _ _ _).trans (max_le h1 (hX i j))) (hY i j))

/-- The determinant of an integral matrix, as an element of $\mathfrak o_v$. -/
theorem det_toOM (X : Matrix (Fin n) (Fin n) Fv) (hX : X ∈ intM v) :
    ((toOM v X hX).det : Fv) = X.det := by
  conv_rhs => rw [← map_toOM v X hX]
  exact (RingHom.map_det (algebraMap 𝔬 Fv) (toOM v X hX))

/-- **Integral matrices of unit determinant have integral inverses** (adjugate formula). -/
theorem inv_mem_intM {X : Matrix (Fin n) (Fin n) Fv} (hX : X ∈ intM v) (hd : Valued.v X.det = 1) :
    X⁻¹ ∈ intM v := by
  intro i j
  have hadj : X.adjugate = (toOM v X hX).adjugate.map (algebraMap 𝔬 Fv) := by
    have := RingHom.map_adjugate (algebraMap 𝔬 Fv) (toOM v X hX)
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, map_toOM] at this
    exact this.symm
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, hd, inv_one,
    one_mul, hadj, Matrix.map_apply]
  exact ((toOM v X hX).adjugate i j).2

theorem valued_det_sub_one_le {m : ℕ} {X : Matrix (Fin n) (Fin n) Fv} (hX : X ∈ ballOne v m) :
    Valued.v (X.det - 1) ≤ exp (-(m : ℤ)) := by
  have hXi := ballOne_subset_intM v m hX
  have hred : redM v m X hXi = (1 : Matrix (Fin n) (Fin n) 𝔬).map (Ideal.Quotient.mk _) := by
    ext i j
    rw [redM, Matrix.map_apply, Matrix.map_apply, valued_sub_le_iff_mk_eq, coe_one_apply]
    exact hX i j
  have h := congrArg Matrix.det hred
  rw [redM, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← RingHom.map_det,
    Matrix.det_one] at h
  have := (valued_sub_le_iff_mk_eq v m _ _).mp h
  rwa [det_toOM, OneMemClass.coe_one] at this

theorem valued_det_eq_one {m : ℕ} (hm : 1 ≤ m) {X : Matrix (Fin n) (Fin n) Fv} (hX : X ∈ ballOne v m) :
    Valued.v X.det = 1 := by
  have h := valued_det_sub_one_le v hX
  have hlt : Valued.v (X.det - 1) < 1 :=
    lt_of_le_of_lt h (by rw [← exp_zero, exp_lt_exp]; omega)
  have := Valuation.map_one_add_of_lt _ hlt
  rwa [add_sub_cancel] at this

theorem inv_mem_ballOne {m : ℕ} (hm : 1 ≤ m) {X : Matrix (Fin n) (Fin n) Fv} (hX : X ∈ ballOne v m) :
    X⁻¹ ∈ ballOne v m ∧ X⁻¹ * X = 1 := by
  have hXi := ballOne_subset_intM v m hX
  have hd := valued_det_eq_one v hm hX
  have hdet : IsUnit X.det := isUnit_iff_ne_zero.mpr (by intro h; rw [h, map_zero] at hd; exact zero_ne_one hd)
  have hinv : X⁻¹ * X = 1 := Matrix.nonsing_inv_mul X hdet
  refine ⟨fun i j => ?_, hinv⟩
  have e : X⁻¹ - 1 = -(X⁻¹ * (X - 1)) := by rw [Matrix.mul_sub, hinv, Matrix.mul_one]; abel
  have e' : X⁻¹ i j - (1 : Matrix (Fin n) (Fin n) Fv) i j = -((X⁻¹ * (X - 1)) i j) := by
    rw [← Matrix.sub_apply, e]; rfl
  rw [e', Valuation.map_neg]
  calc Valued.v ((X⁻¹ * (X - 1)) i j) ≤ 1 * exp (-(m : ℤ)) :=
        valued_mul_apply_le v (inv_mem_intM v hXi hd) hX i j
    _ = _ := one_mul _

theorem one_mem_ballOne (m : ℕ) : (1 : Matrix (Fin n) (Fin n) Fv) ∈ ballOne v m := by
  intro i j; rw [sub_self, map_zero]; exact zero_le

theorem ballOne_eq (m : ℕ) : ballOne v m = ⋂ i, ⋂ j,
    (fun X : Matrix (Fin n) (Fin n) Fv => X i j - (1 : Matrix (Fin n) (Fin n) Fv) i j) ⁻¹'
      (latticeV v (m : ℤ) : Set Fv) := by
  ext X; simp only [ballOne, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, valued_le_iff_mem_latticeV]

theorem isClosed_ballOne (m : ℕ) : IsClosed (ballOne v m (n := n)) := by
  rw [ballOne_eq]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    (isCompact_latticeV v m).isClosed.preimage ((continuous_id.matrix_elem i j).sub continuous_const)

theorem isOpen_ballOne (m : ℕ) : IsOpen (ballOne v m (n := n)) := by
  rw [ballOne_eq]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (isOpen_latticeV v m).preimage ((continuous_id.matrix_elem i j).sub continuous_const)

theorem isCompact_ballOne (m : ℕ) : IsCompact (ballOne v m (n := n)) :=
  (Measure.isCompact_intMat v).of_isClosed_subset (isClosed_ballOne v m) (ballOne_subset_intM v m)

/-- **The balls $1 + \pi^mM_n(\mathfrak o_v)$ are a neighbourhood basis of $1$ in $M_n(F_v)$.** -/
theorem exists_ballOne_subset {A : Set (Matrix (Fin n) (Fin n) Fv)} (hA : A ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) Fv)) :
    ∃ m, 1 ≤ m ∧ ballOne v m ⊆ A := by
  have hA' : A ∈ 𝓝 (fun i j => (1 : Matrix (Fin n) (Fin n) Fv) i j : Fin n → Fin n → Fv) := hA
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hA'
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (norm_ϖ_lt_one v)
  refine ⟨N + 1, by omega, fun X hX => hball (a := (fun i j => X i j : Fin n → Fin n → Fv)) ?_⟩
  have hr : (0 : ℝ) ≤ ‖HN.ϖ v‖ ^ (N + 1) := by positivity
  have hle : dist (fun i j => X i j : Fin n → Fin n → Fv)
      (fun i j => (1 : Matrix (Fin n) (Fin n) Fv) i j : Fin n → Fin n → Fv) ≤ ‖HN.ϖ v‖ ^ (N + 1) := by
    refine (dist_pi_le_iff hr).mpr fun i => (dist_pi_le_iff hr).mpr fun j => ?_
    have h := hX i j
    rw [valued_le_iff_mem_latticeV, coe_latticeV, Metric.mem_closedBall, dist_zero_right] at h
    rw [dist_eq_norm]
    calc ‖X i j - (1 : Matrix (Fin n) (Fin n) Fv) i j‖ ≤ ‖HN.ϖ v ^ ((N + 1 : ℕ) : ℤ)‖ := h
      _ = ‖HN.ϖ v‖ ^ (N + 1) := by rw [zpow_natCast, norm_pow]
  rw [Metric.mem_ball]
  calc _ ≤ ‖HN.ϖ v‖ ^ (N + 1) := hle
    _ ≤ ‖HN.ϖ v‖ ^ N := pow_le_pow_of_le_one (norm_nonneg _) (norm_ϖ_lt_one v).le (by omega)
    _ < ε := hN

/-- **The principal congruence subgroup** $K_m = O(V)(F_v) \cap (1 + \pi^mM_n(\mathfrak o_v))$, $m \ge 1$. -/
def congSub (m : ℕ) (hm : 1 ≤ m) : Subgroup (orthGroup QF Fv) where
  carrier := traceO v Q₀ (ballOne v m)
  mul_mem' {a b} ha hb := by
    change (((a * b : orthGroup QF Fv) : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) ∈ ballOne v m
    rw [Subgroup.coe_mul, Units.val_mul]
    exact mul_mem_ballOne v ha hb
  one_mem' := by
    change (((1 : orthGroup QF Fv) : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) ∈ ballOne v m
    rw [OneMemClass.coe_one, Units.val_one]; exact one_mem_ballOne v m
  inv_mem' {a} ha := by
    change (((a⁻¹ : orthGroup QF Fv) : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) ∈ ballOne v m
    rw [Subgroup.coe_inv, Matrix.coe_units_inv]
    exact (inv_mem_ballOne v hm ha).1

theorem mem_congSub {m : ℕ} {hm : 1 ≤ m} {g : orthGroup QF Fv} :
    g ∈ congSub v Q₀ m hm ↔ ((g : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) ∈ ballOne v m := Iff.rfl

theorem continuous_coeM : Continuous fun g : orthGroup QF Fv => ((g : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) :=
  Units.continuous_val.comp continuous_subtype_val

theorem isOpen_traceO {W : Set (Matrix (Fin n) (Fin n) Fv)} (hW : IsOpen W) : IsOpen (traceO v Q₀ W) :=
  hW.preimage (continuous_coeM v Q₀)

theorem isOpen_congSub (m : ℕ) (hm : 1 ≤ m) : IsOpen (congSub v Q₀ m hm : Set (orthGroup QF Fv)) :=
  isOpen_traceO v Q₀ (isOpen_ballOne v m)

/-- **$K_m \le O(L_v)$.** -/
theorem congSub_le_stdStab (m : ℕ) (hm : 1 ≤ m) : congSub v Q₀ m hm ≤ stdStab QF v := by
  intro g hg
  have h1 := ballOne_subset_intM v m hg
  have h2 := ballOne_subset_intM v m ((congSub v Q₀ m hm).inv_mem hg)
  have : (g : GL (Fin n) Fv) ∈ Measure.glInt v := by
    rw [Measure.glInt_eq]
    refine ⟨h1, ?_⟩
    simpa only [Set.mem_preimage, Units.embedProduct_apply, MulOpposite.unop_op, Subgroup.coe_inv] using h2
  exact this

/-- **$O(L_v) = O(V)(F_v) \cap M_n(\mathfrak o_v)$** (an integral isometry has determinant $\pm1$, so an integral inverse). -/
theorem traceO_intM (hQ : Q₀.Nondegenerate) : traceO v Q₀ (intM v) = (stdStab QF v : Set (orthGroup QF Fv)) := by
  ext g
  constructor
  · intro hg
    have hd : Valued.v (((g : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv)).det = 1 := by
      rcases det_eq_one_or_neg_one QF (Measure.nondegenerate_QF Q₀ hQ) g with h | h <;> simp [h]
    have h2 := inv_mem_intM v hg hd
    change (g : GL (Fin n) Fv) ∈ Measure.glInt v
    rw [Measure.glInt_eq]
    refine ⟨hg, ?_⟩
    simpa only [Set.mem_preimage, Units.embedProduct_apply, MulOpposite.unop_op, Matrix.coe_units_inv] using h2
  · intro hg
    have : (g : GL (Fin n) Fv) ∈ Measure.glInt v := hg
    rw [Measure.glInt_eq] at this
    exact this.1

/-- **The $K_m$ form a neighbourhood basis of $1$ in $O(V)(F_v)$.** -/
theorem exists_congSub_subset {O : Set (orthGroup QF Fv)} (hO : O ∈ 𝓝 (1 : orthGroup QF Fv)) :
    ∃ m, ∃ hm : 1 ≤ m, (congSub v Q₀ m hm : Set (orthGroup QF Fv)) ⊆ O := by
  obtain ⟨u, hu, huO⟩ := (mem_nhds_subtype _ _ _).mp hO
  rw [OneMemClass.coe_one, Units.isEmbedding_embedProduct.isInducing.nhds_eq_comap, Filter.mem_comap] at hu
  obtain ⟨t, ht, htu⟩ := hu
  rw [Units.embedProduct_apply, mem_nhds_prod_iff] at ht
  obtain ⟨a, ha, b, hb, hab⟩ := ht
  simp only [inv_one, Units.val_one] at ha hb
  have hb' : MulOpposite.op ⁻¹' b ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) Fv) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hb
  obtain ⟨m, hm, hsub⟩ := exists_ballOne_subset v (Filter.inter_mem ha hb')
  refine ⟨m, hm, fun g hg => huO (htu (hab ?_))⟩
  have hg' := (congSub v Q₀ m hm).inv_mem hg
  rw [Units.embedProduct_apply]
  refine ⟨(hsub hg).1, ?_⟩
  have := (hsub hg').2
  simpa only [Set.mem_preimage, Subgroup.coe_inv] using this

/-- For $g \in O(V)(F_v)$, $g^{-1} = H^{-1}g^{\mathsf T}H$. -/
theorem inv_eq_hessian (hQ : Q₀.Nondegenerate) (g : orthGroup QF Fv) :
    (((g : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv))⁻¹ =
      ((QF).hessian.map (algebraMap F Fv))⁻¹ * ((g : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv)ᵀ *
        (QF).hessian.map (algebraMap F Fv) := by
  have hH : IsUnit ((QF).hessian.map (algebraMap F Fv)).det := by
    rw [isUnit_iff_ne_zero, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).mpr (Measure.nondegenerate_QF Q₀ hQ)
  set H := (QF).hessian.map (algebraMap F Fv)
  apply Matrix.inv_eq_left_inv
  have hg : ((g : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv)ᵀ * H * (g : GL (Fin n) Fv) = H := g.2
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ H, hg, Matrix.nonsing_inv_mul H hH]

/-- **Traces of compact sets are compact** in $O(V)(F_v)$ (the inverse is $X \mapsto H^{-1}X^{\mathsf T}H$ on $O(V)$). -/
theorem isCompact_traceO (hQ : Q₀.Nondegenerate) {W : Set (Matrix (Fin n) (Fin n) Fv)} (hW : IsCompact W) :
    IsCompact (traceO v Q₀ W) := by
  set H := (QF).hessian.map (algebraMap F Fv)
  set W₂ := (fun X : Matrix (Fin n) (Fin n) Fv => H⁻¹ * Xᵀ * H) '' W
  have hW₂ : IsCompact W₂ := hW.image ((continuous_const.matrix_mul continuous_id.matrix_transpose).matrix_mul
    continuous_const)
  have hT : IsCompact (Units.embedProduct _ ⁻¹' (W ×ˢ (MulOpposite.unop ⁻¹' W₂)) : Set (GL (Fin n) Fv)) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (hW.prod ((MulOpposite.opHomeomorph.symm.isCompact_preimage).mpr hW₂))
  refine (Measure.isCompact_preimage_val v QF hT).of_isClosed_subset ?_ ?_
  · exact hW.isClosed.preimage (continuous_coeM v Q₀)
  · intro g hg
    simp only [Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod, MulOpposite.unop_op]
    refine ⟨hg, ?_⟩
    rw [Matrix.coe_units_inv, inv_eq_hessian v Q₀ hQ g]
    exact ⟨_, hg, rfl⟩

/-! ### Coset decomposition and the main theorem -/

/-- **Two compact open sets with the same trace on $O(V)(F_v)$ have eventually equal Leray quotients.** -/
theorem lerayApprox_eventually_eq_of_traceO_eq (hQ : Q₀.Nondegenerate) {W₁ W₂ : Set (Matrix (Fin n) (Fin n) Fv)}
    (h₁ : IsCompact W₁) (h₁o : IsOpen W₁) (h₂ : IsCompact W₂) (h₂o : IsOpen W₂)
    (h : traceO v Q₀ W₁ = traceO v Q₀ W₂) :
    ∀ᶠ k in atTop, lerayApprox v Q₀ W₁ k = lerayApprox v Q₀ W₂ k := by
  have hiff : ∀ g : orthGroup QF Fv, ((g : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) ∈ W₁ ↔
      ((g : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) ∈ W₂ := fun g => Set.ext_iff.mp h g
  have e1 : traceO v Q₀ (W₁ \ W₂) = ∅ := by
    ext g; simp only [traceO, Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_empty_iff_false, iff_false, not_and,
      not_not]; exact fun hg => (hiff g).mp hg
  have e2 : traceO v Q₀ (W₂ \ W₁) = ∅ := by
    ext g; simp only [traceO, Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_empty_iff_false, iff_false, not_and,
      not_not]; exact fun hg => (hiff g).mpr hg
  filter_upwards [eventually_inter_thick_eq_empty v Q₀ hQ (h₁.diff h₂o) e1,
    eventually_inter_thick_eq_empty v Q₀ hQ (h₂.diff h₁o) e2] with k hk1 hk2
  have : W₁ ∩ thick v Q₀ k = W₂ ∩ thick v Q₀ k := by
    ext X
    constructor
    · rintro ⟨hX1, hXt⟩
      by_contra hX2
      have : X ∈ (W₁ \ W₂) ∩ thick v Q₀ k := ⟨⟨hX1, fun h => hX2 ⟨h, hXt⟩⟩, hXt⟩
      rw [hk1] at this; exact this
    · rintro ⟨hX2, hXt⟩
      by_contra hX1
      have : X ∈ (W₂ \ W₁) ∩ thick v Q₀ k := ⟨⟨hX2, fun h => hX1 ⟨h, hXt⟩⟩, hXt⟩
      rw [hk2] at this; exact this
  unfold lerayApprox; rw [this]

/-- The matrix of an element of $O(V)(F_v)$ (notation for the proofs below). -/
abbrev coeM (g : orthGroup QF Fv) : Matrix (Fin n) (Fin n) Fv := ((g : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv)

theorem coeM_mul (a b : orthGroup QF Fv) : coeM v Q₀ (a * b) = coeM v Q₀ a * coeM v Q₀ b := by
  simp only [coeM, Subgroup.coe_mul, Units.val_mul]

theorem coeM_mul_inv (a : orthGroup QF Fv) : coeM v Q₀ a * coeM v Q₀ a⁻¹ = 1 := by
  rw [← coeM_mul, mul_inv_cancel]; simp [coeM]

theorem coeM_inv_mul (a : orthGroup QF Fv) : coeM v Q₀ a⁻¹ * coeM v Q₀ a = 1 := by
  rw [← coeM_mul, inv_mul_cancel]; simp [coeM]

/-- **The coset decomposition.** If the trace $U$ of a compact open $W$ is right $K_m$-stable, then
$W$ has eventually the Leray quotients of $\#(U/K_m)$ disjoint translates $g(1 + \pi^mM_n(\mathfrak o_v))$, $g \in O(V)(F_v)$. -/
theorem lerayApprox_cosets (hQ : Q₀.Nondegenerate) {W : Set (Matrix (Fin n) (Fin n) Fv)} (hWc : IsCompact W)
    (hWo : IsOpen W) (m : ℕ) (hm : 1 ≤ m)
    (hstab : ∀ g ∈ traceO v Q₀ W, ∀ h ∈ congSub v Q₀ m hm, g * h ∈ traceO v Q₀ W) :
    ∀ᶠ k in atTop, lerayApprox v Q₀ W k =
      (Nat.card (QuotientGroup.mk '' traceO v Q₀ W : Set (orthGroup QF Fv ⧸ congSub v Q₀ m hm)) : ℝ≥0∞) *
        lerayApprox v Q₀ (ballOne v m) k := by
  classical
  set K := congSub v Q₀ m hm
  set U := traceO v Q₀ W
  have : DiscreteTopology (orthGroup QF Fv ⧸ K) := QuotientGroup.discreteTopology (isOpen_congSub v Q₀ m hm)
  have hfin : (QuotientGroup.mk '' U : Set (orthGroup QF Fv ⧸ K)).Finite :=
    ((isCompact_traceO v Q₀ hQ hWc).image QuotientGroup.continuous_mk).finite_of_discrete
  set S := hfin.toFinset
  let r : orthGroup QF Fv ⧸ K → orthGroup QF Fv := fun c => Quotient.out c
  have hr : ∀ c, (QuotientGroup.mk (r c) : orthGroup QF Fv ⧸ K) = c := fun c => QuotientGroup.out_eq' c
  let piece : orthGroup QF Fv ⧸ K → Set (Matrix (Fin n) (Fin n) Fv) :=
    fun c => (fun X => coeM v Q₀ (r c)⁻¹ * X) ⁻¹' ballOne v m
  have hpiece_img : ∀ c, piece c = (fun X => coeM v Q₀ (r c) * X) '' ballOne v m := by
    intro c; ext X
    simp only [piece, Set.mem_preimage, Set.mem_image]
    constructor
    · intro hX
      refine ⟨_, hX, ?_⟩
      rw [← Matrix.mul_assoc, coeM_mul_inv, Matrix.one_mul]
    · rintro ⟨Y, hY, rfl⟩
      rwa [← Matrix.mul_assoc, coeM_inv_mul, Matrix.one_mul]
  set W' := ⋃ c ∈ S, piece c
  have hmem_piece : ∀ c (g : orthGroup QF Fv), coeM v Q₀ g ∈ piece c ↔ (QuotientGroup.mk g : _ ⧸ K) = c := by
    intro c g
    simp only [piece, Set.mem_preimage]
    rw [← coeM_mul, ← mem_congSub v Q₀ (hm := hm), ← QuotientGroup.eq, hr]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  -- the trace of W' is U
  have htr : traceO v Q₀ W' = U := by
    ext g
    simp only [traceO, Set.mem_ofPred_eq, W', Set.mem_iUnion, exists_prop, S, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨c, ⟨u, hu, rfl⟩, hg⟩
      have hg' := (hmem_piece _ g).mp hg
      rw [QuotientGroup.eq] at hg'
      have := hstab u hu _ (K.inv_mem hg')
      rwa [_root_.mul_inv_rev, inv_inv, mul_inv_cancel_left] at this
    · intro hg
      exact ⟨_, ⟨g, hg, rfl⟩, (hmem_piece _ g).mpr rfl⟩
  -- pairwise disjoint pieces
  have hdisj : Set.PairwiseDisjoint (↑S) piece := by
    intro c _ d _ hcd
    rw [Function.onFun, Set.disjoint_left]
    intro X hc hd
    apply hcd
    simp only [piece, Set.mem_preimage] at hc hd
    set Y := coeM v Q₀ (r c)⁻¹ * X
    set Z := coeM v Q₀ (r d)⁻¹ * X
    obtain ⟨hYi, hYY⟩ := inv_mem_ballOne v hm hc
    have hYdet : IsUnit Y.det := isUnit_iff_ne_zero.mpr fun h => by
      have := valued_det_eq_one v hm hc; rw [h, map_zero] at this; exact zero_ne_one this
    have hYY' : Y * Y⁻¹ = 1 := Matrix.mul_nonsing_inv Y hYdet
    have hZ : coeM v Q₀ ((r d)⁻¹ * r c) * Y = Z := by
      simp only [Y, Z, coeM_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (coeM v Q₀ (r c)), coeM_mul_inv, Matrix.one_mul]
    have hK : (r d)⁻¹ * r c ∈ K := by
      rw [mem_congSub]
      have : coeM v Q₀ ((r d)⁻¹ * r c) = Z * Y⁻¹ := by rw [← hZ, Matrix.mul_assoc, hYY', Matrix.mul_one]
      rw [show ((((r d)⁻¹ * r c : orthGroup QF Fv) : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) =
        coeM v Q₀ ((r d)⁻¹ * r c) from rfl, this]
      exact mul_mem_ballOne v hd hYi
    rw [← hr c, ← hr d]
    exact (QuotientGroup.eq.mpr hK).symm
  have hmeas : ∀ c, MeasurableSet (piece c) := fun c =>
    (isClosed_ballOne v m).measurableSet.preimage (continuous_const.matrix_mul continuous_id).measurable
  have hW'c : IsCompact W' := S.isCompact_biUnion fun c _ => by
    rw [hpiece_img]; exact (isCompact_ballOne v m).image (continuous_const.matrix_mul continuous_id)
  have hW'o : IsOpen W' := isOpen_biUnion fun c _ =>
    (isOpen_ballOne v m).preimage (continuous_const.matrix_mul continuous_id)
  have hval : ∀ k, lerayApprox v Q₀ W' k = (S.card : ℝ≥0∞) * lerayApprox v Q₀ (ballOne v m) k := by
    intro k
    have hpk : ∀ c, lerayApprox v Q₀ (piece c) k = lerayApprox v Q₀ (ballOne v m) k := fun c =>
      lerayApprox_preimage_mul v Q₀ hQ (r c)⁻¹ (isClosed_ballOne v m).measurableSet k
    unfold lerayApprox at hpk ⊢
    rw [Set.iUnion₂_inter, measure_biUnion_finset]
    · have : ∀ c ∈ S, volM v (piece c ∩ thick v Q₀ k) = volM v (ballOne v m ∩ thick v Q₀ k) := by
        intro c _
        have := hpk c
        have hq : ((DVR.q 𝔬 : ℝ≥0∞)) ^ (k * (n * (n + 1) / 2)) ≠ 0 :=
          pow_ne_zero _ (by exact_mod_cast (q_pos v).ne')
        have hqt : ((DVR.q 𝔬 : ℝ≥0∞)) ^ (k * (n * (n + 1) / 2)) ≠ ⊤ :=
          ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
        exact (ENNReal.mul_right_inj hq hqt).mp this
      rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
      ring
    · intro c hc d hd hcd
      exact (hdisj hc hd hcd).mono Set.inter_subset_left Set.inter_subset_left
    · intro c _; exact (hmeas c).inter (measurableSet_thick v Q₀ k)
  have hcard : (S.card : ℝ≥0∞) = (Nat.card (QuotientGroup.mk '' U : Set (orthGroup QF Fv ⧸ K)) : ℝ≥0∞) := by
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hfin]
  filter_upwards [lerayApprox_eventually_eq_of_traceO_eq v Q₀ hQ hWc hWo hW'c hW'o htr.symm] with k hk
  rw [hk, hval, hcard]

/-- **The Leray quotients of $1 + \pi^mM_n(\mathfrak o_v)$ are eventually $\mu_v(K_m)$.** Compare
$M_n(\mathfrak o_v) \supseteq \bigsqcup_{g \in O(L_v)/K_m} g(1 + \pi^mM_n(\mathfrak o_v))$ with
$\mu_v(O(L_v)) = [O(L_v) : K_m]\,\mu_v(K_m)$. -/
theorem lerayApprox_ballOne_eventually (hQ : Q₀.Nondegenerate) (m : ℕ) (hm : 1 ≤ m) :
    ∀ᶠ k in atTop, lerayApprox v Q₀ (ballOne v m) k = Measure.muLoc v Q₀ 1 (congSub v Q₀ m hm : Set _) := by
  set K := congSub v Q₀ m hm
  have htr := traceO_intM v Q₀ hQ
  have hstab : ∀ g ∈ traceO v Q₀ (intM v), ∀ h ∈ K, g * h ∈ traceO v Q₀ (intM v) := by
    intro g hg h hh
    rw [htr] at hg ⊢
    exact (stdStab QF v).mul_mem hg (congSub_le_stdStab v Q₀ m hm hh)
  have : DiscreteTopology (orthGroup QF Fv ⧸ K) := QuotientGroup.discreteTopology (isOpen_congSub v Q₀ m hm)
  have hfin : (QuotientGroup.mk '' traceO v Q₀ (intM v) : Set (orthGroup QF Fv ⧸ K)).Finite :=
    ((isCompact_traceO v Q₀ hQ (Measure.isCompact_intMat v)).image QuotientGroup.continuous_mk).finite_of_discrete
  have hcos : IsCosetUnion K (traceO v Q₀ (intM v)) := ⟨hstab, hfin⟩
  set N₀ := Nat.card (QuotientGroup.mk '' traceO v Q₀ (intM v) : Set (orthGroup QF Fv ⧸ K))
  have hN0 : (N₀ : ℝ≥0∞) ≠ 0 := by
    have : Finite (QuotientGroup.mk '' traceO v Q₀ (intM v) : Set (orthGroup QF Fv ⧸ K)) := hfin.to_subtype
    have hne : Nonempty (QuotientGroup.mk '' traceO v Q₀ (intM v) : Set (orthGroup QF Fv ⧸ K)) := by
      refine ⟨⟨QuotientGroup.mk 1, 1, ?_, rfl⟩⟩
      rw [htr]; exact (stdStab QF v).one_mem
    exact_mod_cast (Nat.card_pos (α := (QuotientGroup.mk '' traceO v Q₀ (intM v) : Set _))).ne'
  have hμ := measure_cosetUnion (Measure.muLoc v Q₀ 1) (isOpen_congSub v Q₀ m hm) hcos
  have hβ : Measure.muLoc v Q₀ 1 (traceO v Q₀ (intM v)) = ENNReal.ofReal (NF.localDensityForm v Q₀ Q₀) := by
    rw [htr, Measure.muLoc_stdStab, div_one]
  filter_upwards [lerayApprox_cosets v Q₀ hQ (Measure.isCompact_intMat v) (Measure.isOpen_intMat v) m hm hstab,
    lerayApprox_intM_eventually v Q₀ hQ] with k h1 h2
  rw [h2, ← hβ, hμ] at h1
  exact ((ENNReal.mul_right_inj hN0 (ENNReal.natCast_ne_top _)).mp h1).symm

/-- **$\mu_v$ is Weil's gauge-form (Leray) measure** (every finite place $v$, dyadic included; $Q_0$ nondegenerate):
for every compact open $W \subseteq M_n(F_v)$,
$$q^{kN}\,\mathrm{vol}\{X \in W : Q_0 \circ X \equiv Q_0 \bmod \mathfrak p_v^k\} = \mu_v(W \cap O(V)(F_v))
\qquad\text{for all large } k,$$
$N = n(n+1)/2$, $dX$ the standard Haar measure on $M_n(F_v)$ (`volM`), $\mu_v$ = `muLoc v Q₀ 1`. This is Weil's
$|\omega|_v = |dX/d\Phi|_v$ on the fibre $O(V) = \Phi^{-1}(Q_0)$ (AAG §2.2 [unverified]), the $p$-adic analogue of
the real `LerayReal.tendsto_lerayMeasure`. -/
@[kb "weil1982" "§2.2 (gauge-form measures on p-adic varieties; Leray/volume limit) [unverified]"]
theorem lerayApprox_eventually_eq (hQ : Q₀.Nondegenerate) {W : Set (Matrix (Fin n) (Fin n) Fv)}
    (hWc : IsCompact W) (hWo : IsOpen W) :
    ∀ᶠ k in atTop, lerayApprox v Q₀ W k = Measure.muLoc v Q₀ 1 (traceO v Q₀ W) := by
  set U := traceO v Q₀ W
  have hUc : IsCompact U := isCompact_traceO v Q₀ hQ hWc
  have hUo : IsOpen U := isOpen_traceO v Q₀ hWo
  obtain ⟨V, hV, hUV⟩ := compact_open_separated_mul_right hUc hUo subset_rfl
  obtain ⟨m, hm, hKV⟩ := exists_congSub_subset v Q₀ hV
  have hstab : ∀ g ∈ U, ∀ h ∈ congSub v Q₀ m hm, g * h ∈ U := fun g hg h hh =>
    hUV (Set.mul_mem_mul hg (hKV hh))
  have : DiscreteTopology (orthGroup QF Fv ⧸ congSub v Q₀ m hm) :=
    QuotientGroup.discreteTopology (isOpen_congSub v Q₀ m hm)
  have hcos : IsCosetUnion (congSub v Q₀ m hm) U :=
    ⟨hstab, (hUc.image QuotientGroup.continuous_mk).finite_of_discrete⟩
  filter_upwards [lerayApprox_cosets v Q₀ hQ hWc hWo m hm hstab, lerayApprox_ballOne_eventually v Q₀ hQ m hm]
    with k h1 h2
  rw [h1, h2, measure_cosetUnion (Measure.muLoc v Q₀ 1) (isOpen_congSub v Q₀ m hm) hcos]

/-- **The Leray limit** (limit form of `lerayApprox_eventually_eq`). -/
theorem tendsto_lerayApprox (hQ : Q₀.Nondegenerate) {W : Set (Matrix (Fin n) (Fin n) Fv)}
    (hWc : IsCompact W) (hWo : IsOpen W) :
    Tendsto (lerayApprox v Q₀ W) atTop (𝓝 (Measure.muLoc v Q₀ 1 (traceO v Q₀ W))) :=
  tendsto_const_nhds.congr' (EventuallyEq.symm (lerayApprox_eventually_eq v Q₀ hQ hWc hWo))

/-! ### Corollaries: $SO(V)$, uniqueness, the good places -/

/-- **`muLocSO v Q₀ 1` is the gauge-form measure on $SO(V)(F_v)$**: the Leray limit for compact open
$W \subseteq M_n(F_v)$ whose trace lies in $SO(V)(F_v)$ ($n \ge 1$). -/
@[kb "weil1982" "§2.2 [unverified]"]
theorem lerayApprox_eventually_eq_muLocSO (hQ : Q₀.Nondegenerate) (hn : 0 < n)
    {W : Set (Matrix (Fin n) (Fin n) Fv)} (hWc : IsCompact W) (hWo : IsOpen W)
    (hW : traceO v Q₀ W ⊆ (soSub QF Fv : Set (orthGroup QF Fv))) :
    ∀ᶠ k in atTop, lerayApprox v Q₀ W k =
      Measure.muLocSO v Q₀ 1 {g : Measure.SOv v Q₀ | coeM v Q₀ (g : orthGroup QF Fv) ∈ W} := by
  have himg : (Subtype.val '' {g : Measure.SOv v Q₀ | coeM v Q₀ (g : orthGroup QF Fv) ∈ W}) = traceO v Q₀ W := by
    ext g
    simp only [Set.mem_image, Set.mem_ofPred_eq, traceO]
    exact ⟨fun ⟨h, hh, e⟩ => e ▸ hh, fun hg => ⟨⟨g, hW hg⟩, hg, rfl⟩⟩
  rw [Measure.muLocSO_eq_comap v Q₀ hQ hn one_pos, (Measure.measurableEmbedding_soSub v Q₀ hQ).comap_apply, himg]
  exact lerayApprox_eventually_eq v Q₀ hQ hWc hWo

/-- **Uniqueness:** a left-invariant $\sigma$-finite measure on $O(V)(F_v)$ that satisfies the Leray limit on
$W = M_n(\mathfrak o_v)$ is `muLoc v Q₀ 1`; so $\mu_v$ is characterized as the gauge-form measure. -/
theorem eq_muLoc_of_lerayApprox (hQ : Q₀.Nondegenerate) (μ : MeasureTheory.Measure (orthGroup QF Fv)) [MeasureTheory.Measure.IsMulLeftInvariant μ]
    [SigmaFinite μ] (h : ∀ᶠ k in atTop, lerayApprox v Q₀ (intM v) k = μ (traceO v Q₀ (intM v))) :
    μ = Measure.muLoc v Q₀ 1 := by
  have h2 := (h.and (lerayApprox_eventually_eq v Q₀ hQ (Measure.isCompact_intMat v)
    (Measure.isOpen_intMat v))).exists
  obtain ⟨k, hk1, hk2⟩ := h2
  have hK := traceO_intM v Q₀ hQ
  have hc := Measure.isCompact_stdStab v QF
  have ho := Measure.isOpen_stdStab v QF
  have hμK : μ (stdStab QF v : Set (orthGroup QF Fv)) = Measure.muLoc v Q₀ 1 (stdStab QF v : Set _) := by
    rw [← hK, ← hk1, hk2]
  rw [Measure.eq_haarNorm hc ho μ (by rw [hμK]; exact hc.measure_lt_top.ne),
    Measure.eq_haarNorm hc ho (Measure.muLoc v Q₀ 1) hc.measure_lt_top.ne, hμK]

section Good

/-- **Gauge-form volume of $SO(L_v)$ at a unimodular place** ($\pi \nmid \det H_{Q}$; every finite place):
$|\omega|_v(SO(L_v)) = \mu_v(SO(L_v)) = \#O(\bar Q)(\mathbb F_q)/(2q^{n(n-1)/2})$, $\bar Q = Q \bmod \pi$ (Hensel:
`DVR.localDensityForm_self_unimodular`). Since $[O(\bar Q) : SO(\bar Q)] = 2$ for $q$ odd, this is Weil's
$\#SO(\bar Q)(\mathbb F_q)/q^{\dim SO}$ (AAG §2.2 [unverified]; the index-2 statement over $\mathbb F_q$ is not formalized
here). -/
@[kb "weil1982" "§2.2 (volume of a smooth model = #points/q^dim) [unverified]"]
theorem muLocSO_soStabSO_unimodular (Q₁ : QuadForm (𝓞 F) n) (hdet : ¬ πv ∣ (NF.Qp v Q₁).hessian.det) :
    Measure.muLocSO v Q₁ 1 (Measure.soStabSO v Q₁ : Set (Measure.SOv v Q₁)) =
      ENNReal.ofReal ((Nat.card (DVR.orthMod (NF.Qp v Q₁) πv 1) : ℝ) /
        (2 * (DVR.q 𝔬 : ℝ) ^ (n * (n - 1) / 2))) := by
  rw [Measure.muLocSO_soStabSO, NF.siegelDensity]
  simp only [↓reduceIte, div_one]
  rw [NF.localDensityForm_eq_completion,
    DVR.localDensityForm_self_unimodular _ _ (NF.irreducible_π v) (DVR.dvr_isUnit_of_not_dvd (NF.irreducible_π v) hdet)]
  congr 1
  ring

/-- **Gauge-form volume of $SO(L_v)$, odd rank, good place** ($v \nmid 2\det H_Q$, $n = 2m + 1$):
$$|\omega|_v(SO(L_v)) = \mu_v(SO(L_v)) = \prod_{i=1}^m(1 - q^{-2i})$$
(KB's `DVR.localDensityForm_self_odd`, via $|O_{2m+1}(\mathbb F_q)| = 2q^{m^2}\prod_{i=1}^m(q^{2i}-1)$; Conway–Sloane 1988,
Table 1 [unverified]). For $n = 3$: $1 - q^{-2}$. Index shift: $i = 0,\dots,m-1$ with exponent $2(i+1)$. -/
@[kb "weil1982" "§2.2 [unverified]"]
theorem muLocSO_soStabSO_odd (m : ℕ) (Q₁ : QuadForm (𝓞 F) (2 * m + 1)) (h2 : ¬ πv ∣ 2)
    (hdet : ¬ πv ∣ (NF.Qp v Q₁).hessian.det) :
    Measure.muLocSO v Q₁ 1 (Measure.soStabSO v Q₁ : Set (Measure.SOv v Q₁)) =
      ENNReal.ofReal (∏ i ∈ Finset.range m, (1 - ((DVR.q 𝔬 : ℝ) ^ (2 * (i + 1)))⁻¹)) := by
  classical
  let _ : Fintype (IsLocalRing.ResidueField 𝔬) := Fintype.ofFinite _
  rw [Measure.muLocSO_soStabSO, NF.siegelDensity]
  simp only [↓reduceIte, div_one]
  rw [NF.localDensityForm_eq_completion,
    DVR.localDensityForm_self_odd πv m _ (NF.irreducible_π v) h2 hdet]
  congr 1
  ring

/-- **The ternary case** ($n = 3$, $v \nmid 2\det H_Q$): $|\omega|_v(SO(L_v)) = \mu_v(SO(L_v)) = 1 - q^{-2}$. -/
@[kb "weil1982" "§2.2 [unverified]"]
theorem muLocSO_soStabSO_ternary (Q₁ : QuadForm (𝓞 F) 3) (h2 : ¬ πv ∣ 2)
    (hdet : ¬ πv ∣ (NF.Qp v Q₁).hessian.det) :
    Measure.muLocSO v Q₁ 1 (Measure.soStabSO v Q₁ : Set (Measure.SOv v Q₁)) =
      ENNReal.ofReal (1 - ((DVR.q 𝔬 : ℝ) ^ 2)⁻¹) := by
  have := muLocSO_soStabSO_odd v 1 Q₁ h2 hdet
  simpa using this

end Good

/-! ### The elementary Weil–Hensel volume lemma -/

section Hensel

open LocalDensity.DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Finite (IsLocalRing.ResidueField R)]
  {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **Weil–Hensel volume lemma for smooth quadratic systems** (Weil 1982, §2.2 [unverified]; Hanke 2004, Lemma 3.2,
multivariable): let $F : R^\iota \to R^\kappa$ be a quadratic map,
$F(\vec x + c\vec w) = F(\vec x) + c\,D_{\vec x}\vec w + c^2F(\vec w)$, and suppose the system $F = \vec t$ is **smooth**: at
every $\vec x$ with $F(\vec x) \equiv \vec t \bmod \pi$ the differential $D_{\vec x} : R^\iota \to R^\kappa$ is surjective
(equivalently, by Nakayama, surjective mod $\pi$; the surjectivity over $R$ is the hypothesis used). Then
$$\#S_{k+1}\cdot q^{k|\kappa|} = q^{k|\iota|}\cdot\#S_1,\qquad\text{i.e.}\qquad
  \frac{\#S_{k+1}}{q^{(k+1)(|\iota| - |\kappa|)}} = \frac{\#\{\mathbb F_q\text{-points}\}}{q^{|\iota|-|\kappa|}},$$
$S_N = \{\vec x \bmod \pi^N : F(\vec x) \equiv \vec t \bmod \pi^N\}$: the gauge-form volume of the smooth model is
$\#X(\mathbb F_q)/q^{\dim X}$. (For $X = O(Q)$, $F = $ `formF`, this is `localDensityForm_self_unimodular`.) Iterates the
KB's counting Hensel lemma `card_sol_succ` with $d = 0$. -/
@[kb "weil1982" "§2.2 (smooth models: vol = #X(F_q)/q^dim) [unverified]"]
theorem card_sol_of_smooth (π : R) (hπ : Irreducible π) (Fm : (ι → R) → (κ → R))
    (D : (ι → R) → (ι → R) →ₗ[R] (κ → R))
    (hF : ∀ x w (c : R), Fm (x + c • w) = Fm x + c • D x w + c ^ 2 • Fm w) (t : κ → R)
    (hD : ∀ x, (∀ j, π ∣ Fm x j - t j) → Function.Surjective (D x)) (k : ℕ) :
    Nat.card {x : ι → R ⧸ Ideal.span {π ^ (k + 1)} // ∀ j, π ^ (k + 1) ∣ Fm (liftI π (k + 1) x) j - t j} *
        q R ^ (k * Fintype.card κ) =
      q R ^ (k * Fintype.card ι) *
        Nat.card {x : ι → R ⧸ Ideal.span {π ^ 1} // ∀ j, π ^ 1 ∣ Fm (liftI π 1 x) j - t j} := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep := card_sol_succ π hπ Fm D hF t 0 (k + 1) (by omega) fun x hx c => by
      obtain ⟨w, hw⟩ := hD x (fun j => (dvd_pow_self π (Nat.succ_ne_zero k)).trans (hx j)) c
      exact ⟨w, by rw [pow_zero, one_smul]; exact hw⟩
    set S2 := Nat.card {x : ι → R ⧸ Ideal.span {π ^ (k + 1 + 1)} //
      ∀ j, π ^ (k + 1 + 1) ∣ Fm (liftI π (k + 1 + 1) x) j - t j}
    set S1 := Nat.card {x : ι → R ⧸ Ideal.span {π ^ (k + 1)} // ∀ j, π ^ (k + 1) ∣ Fm (liftI π (k + 1) x) j - t j}
    set S0 := Nat.card {x : ι → R ⧸ Ideal.span {π ^ 1} // ∀ j, π ^ 1 ∣ Fm (liftI π 1 x) j - t j}
    rw [Nat.succ_mul, Nat.succ_mul, pow_add, pow_add]
    calc S2 * (q R ^ (k * Fintype.card κ) * q R ^ Fintype.card κ)
        = (S2 * q R ^ Fintype.card κ) * q R ^ (k * Fintype.card κ) := by ring
      _ = q R ^ Fintype.card ι * (S1 * q R ^ (k * Fintype.card κ)) := by rw [hstep]; ring
      _ = _ := by rw [ih]; ring

end Hensel

/-! ### $\#SO(\bar Q)(\mathbb F_q) = \#O(\bar Q)(\mathbb F_q)/2$ at odd unimodular places -/

section SOCount

open LocalDensity.DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {m : ℕ}

/-- **The reflection matrix** $\tau_x = 1 - c\,x\,(Hx)^{\mathsf T}$ ($c = Q(x)^{-1}$): $\tau_x y = y - c\,B(x,y)\,x$. -/
def reflMat (Q : QuadForm R m) (x : Fin m → R) (c : R) : Matrix (Fin m) (Fin m) R :=
  1 - c • vecMulVec x (Q.hessian *ᵥ x)

theorem hessian_reflMat (Q : QuadForm R m) (x : Fin m → R) (c : R) (hc : c * Q.eval x = 1) :
    (reflMat Q x c)ᵀ * Q.hessian * reflMat Q x c = Q.hessian := by
  set H := Q.hessian
  set h := H *ᵥ x
  have hx : h ⬝ᵥ x = 2 * Q.eval x := by rw [dotProduct_comm]; exact QuadForm.dotProduct_hessian_self Q x
  have hHx : x ᵥ* H = h := by rw [← Matrix.mulVec_transpose, QuadForm.hessian_transpose]
  have e1 : vecMulVec h x * H = vecMulVec h h := by rw [vecMulVec_mul, hHx]
  have e2 : H * vecMulVec x h = vecMulVec h h := by rw [mul_vecMulVec]
  have e3 : vecMulVec h x * H * vecMulVec x h = (2 * Q.eval x) • vecMulVec h h := by
    rw [e1, vecMulVec_mul_vecMulVec, hx]
    ext i j; simp [vecMulVec_apply]; ring
  have hexp : (1 - c • vecMulVec h x) * H * (1 - c • vecMulVec x h) =
      H - c • (vecMulVec h x * H) - c • (H * vecMulVec x h) + (c * c) • (vecMulVec h x * H * vecMulVec x h) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.mul_assoc]
    abel
  unfold reflMat
  rw [transpose_sub, transpose_one, transpose_smul, transpose_vecMulVec, hexp, e3, e1, e2, smul_smul]
  have hcoef : c * c * (2 * Q.eval x) = 2 * c := by linear_combination 2 * c * hc
  rw [hcoef]
  module

theorem det_reflMat (Q : QuadForm R m) (x : Fin m → R) (c : R) (hc : c * Q.eval x = 1) :
    (reflMat Q x c).det = -1 := by
  have hx : (Q.hessian *ᵥ x) ⬝ᵥ x = 2 * Q.eval x := by
    rw [dotProduct_comm]; exact QuadForm.dotProduct_hessian_self Q x
  have e : reflMat Q x c = 1 + replicateCol Unit (-c • x) * replicateRow Unit (Q.hessian *ᵥ x) := by
    rw [← vecMulVec_eq, reflMat]
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, smul_eq_mul, hx]
  linear_combination (-2 : R) * hc

/-- **The determinant on $O(\bar Q)(\mathbb F_q)$.** -/
def detOrthMod (Q : QuadForm R m) (π : R) : orthMod Q π 1 →* (R ⧸ Ideal.span {π ^ 1})ˣ :=
  Matrix.GeneralLinearGroup.det.comp (orthMod Q π 1).subtype

/-- **$SO(\bar Q)(\mathbb F_q)$**, the kernel of the determinant on $O(\bar Q)(\mathbb F_q)$ = `orthMod Q π 1`. -/
def soMod (Q : QuadForm R m) (π : R) : Subgroup (orthMod Q π 1) := (detOrthMod Q π).ker

/-- **$\#O(\bar Q)(\mathbb F_q) = 2\,\#SO(\bar Q)(\mathbb F_q)$** for $\pi \nmid 2\det H_Q$, $m \ge 1$: the reflection in a
vector $x$ with $Q(x)$ a unit (`DVR.exists_diag_of_unimodular`) has determinant $-1 \ne 1$, and every isometry has
determinant $\pm1$. With `card_orthMod_one_unimodular` this gives $\#SO_m(\mathbb F_q) = o_m/2$ (Artin, *Geometric
Algebra*, Ch. III [unverified]). -/
@[kb "kitaoka1993" "§5.6 (|O_n(F_q)| = 2|SO_n(F_q)|) [unverified]"]
theorem card_orthMod_eq_two_mul_soMod (Q : QuadForm R m) (π : R) (hπ : Irreducible π) (h2 : ¬ π ∣ 2)
    (hdet : ¬ π ∣ Q.hessian.det) (hm : 0 < m) :
    Nat.card (orthMod Q π 1) = 2 * Nat.card (soMod Q π) := by
  classical
  set K := R ⧸ Ideal.span {π ^ 1}
  have hmax : (Ideal.span {π ^ 1}).IsMaximal := by
    rw [pow_one]; exact PrincipalIdealRing.isMaximal_of_irreducible hπ
  let _ : Field K := Ideal.Quotient.field _
  set mk := Ideal.Quotient.mk (Ideal.span {π ^ 1})
  have hmk : ∀ r : R, mk r = 0 ↔ π ∣ r := fun r => by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, pow_one]
  have h2K : (2 : K) ≠ 0 := by
    intro h; apply h2; rw [← hmk, map_ofNat]; exact h
  have hne : (1 : Kˣ) ≠ -1 := by
    intro h
    have h' := congrArg Units.val h
    simp only [Units.val_one, Units.val_neg] at h'
    exact h2K (by linear_combination h')
  -- a reflection over R
  obtain ⟨a, ha, ⟨U, _, hUQ⟩, -⟩ := exists_diag_of_unimodular Q π hπ h2 hdet
  set i0 : Fin m := ⟨0, hm⟩
  set x := U *ᵥ Pi.single i0 1
  have hQx : Q.eval x = a i0 := by
    rw [← hUQ, QuadForm.eval_single]; simp [QuadForm.diag]
  obtain ⟨u, hu⟩ := dvr_isUnit_of_not_dvd hπ (ha i0)
  set c : R := ((u⁻¹ : Rˣ) : R)
  have hc : c * Q.eval x = 1 := by rw [hQx, ← hu]; simp [c]
  have h2R : (2 : R) ≠ 0 := fun h => h2 (h ▸ dvd_zero π)
  set ρ := reflMat Q x c
  have hρQ : Q.compMat ρ = Q :=
    QuadForm.eq_of_hessian_eq' h2R (by rw [QuadForm.hessian_compMat, hessian_reflMat Q x c hc])
  have hρdet : (ρ.map mk).det = -1 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, det_reflMat Q x c hc, map_neg, map_one]
  set ρK : GL (Fin m) K := Matrix.nonsingInvUnit (ρ.map mk) (by rw [hρdet]; exact isUnit_one.neg)
  have hρK : ρK ∈ orthMod Q π 1 := by
    show (Q.map mk).compMat (ρ.map mk) = Q.map mk
    rw [QuadForm.map_compMat, hρQ]
  -- determinants are ±1
  have hHK : (Q.map mk).hessian.det ≠ 0 := by
    rw [QuadForm.hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    intro h; exact hdet ((hmk _).mp h)
  have hpm : ∀ g : orthMod Q π 1, detOrthMod Q π g = 1 ∨ detOrthMod Q π g = -1 := by
    intro g
    have hg : (Q.map mk).compMat (g : GL (Fin m) K).val = Q.map mk := g.2
    have hh := congrArg (fun S => Matrix.det (QuadForm.hessian S)) hg
    simp only [QuadForm.hessian_compMat, det_mul, det_transpose] at hh
    have hsq : (g : GL (Fin m) K).val.det * (g : GL (Fin m) K).val.det = 1 := by
      apply mul_right_cancel₀ hHK; linear_combination hh
    rcases mul_self_eq_one_iff.mp hsq with h | h
    · left; ext; simpa [detOrthMod] using h
    · right; ext; simpa [detOrthMod] using h
  have hrange : ((detOrthMod Q π).range : Set Kˣ) = {1, -1} := by
    ext w
    simp only [SetLike.mem_coe, MonoidHom.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨g, rfl⟩; exact hpm g
    · rintro (rfl | rfl)
      · exact ⟨1, map_one _⟩
      · refine ⟨⟨ρK, hρK⟩, ?_⟩
        ext; simp [detOrthMod, ρK, Matrix.nonsingInvUnit, hρdet]
  have hcard : Nat.card (detOrthMod Q π).range = 2 := by
    rw [← SetLike.coe_sort_coe, hrange, Nat.card_coe_set_eq, Set.ncard_pair hne]
  have := Subgroup.card_mul_index (soMod Q π)
  rw [soMod, Subgroup.index_ker, hcard] at this
  rw [← this, soMod, mul_comm]

end SOCount

/-- **Weil's formula at a unimodular odd place** ($v \nmid 2\det H_Q$, $n \ge 1$):
$$|\omega|_v(SO(L_v)) = \mu_v(SO(L_v)) = \frac{\#SO(\bar Q)(\mathbb F_q)}{q^{\dim SO}},\qquad \dim SO = n(n-1)/2$$
(Weil 1982, §2.2 [unverified]; `soMod` = $SO(\bar Q)(\mathbb F_q)$). -/
@[kb "weil1982" "§2.2 (volume of a smooth model = #points/q^dim) [unverified]"]
theorem muLocSO_soStabSO_eq_card_soMod (Q₁ : QuadForm (𝓞 F) n) (hn : 0 < n) (h2 : ¬ πv ∣ 2)
    (hdet : ¬ πv ∣ (NF.Qp v Q₁).hessian.det) :
    Measure.muLocSO v Q₁ 1 (Measure.soStabSO v Q₁ : Set (Measure.SOv v Q₁)) =
      ENNReal.ofReal ((Nat.card (soMod (NF.Qp v Q₁) πv) : ℝ) / (DVR.q 𝔬 : ℝ) ^ (n * (n - 1) / 2)) := by
  rw [muLocSO_soStabSO_unimodular v Q₁ hdet,
    card_orthMod_eq_two_mul_soMod (NF.Qp v Q₁) πv (NF.irreducible_π v) h2 hdet hn]
  congr 1
  push_cast
  have hq : (0 : ℝ) < (DVR.q 𝔬 : ℝ) ^ (n * (n - 1) / 2) := pow_pos (by exact_mod_cast q_pos v) _
  field_simp

end QuadFormsKB.Tamagawa.Measure.LerayPadic
