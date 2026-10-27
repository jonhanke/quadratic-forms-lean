import QuadFormsKB.Tamagawa.Measure.Weil.BaseChangeMeasure
import QuadFormsKB.Tamagawa.Measure.Weil.GLScaling

/-!
# Base change of adeles: the adelic norm and the Haar modulus
$K/k$ a finite extension of number fields, $b$ a $k$-basis of $K$, $\Psi$ = `adeleBaseChange b`.

* `adeleLmat b y` : the matrix over $\mathbb A_k$ of multiplication by $y\in\mathbb A_K$ in the coordinates $b$, with
  **`adeleBaseChange_mulVec_adeleLmat`**: $\Psi(M(y)a) = y\,\Psi(a)$; $y\mapsto M(y)$ is multiplicative
  (`adeleLmatHom`), and $M(c) = $ `Algebra.leftMulMatrix b c` for $c\in K$ (`adeleLmat_diag`).
* `adeleNorm b` : $\mathbb A_K^\times\to\mathbb A_k^\times$, $y\mapsto\det M(y)$, the adelic norm $N_{K/k}$; it extends the
  field norm (`adeleNorm_diagUnits`: $N(c) = N_{K/k}(c)$ for $c\in K^\times$).
* **`ideleNorm_adeleNorm`**: $\|N_{K/k}(y)\|_{\mathbb A_k} = \|y\|_{\mathbb A_K}$ for every idele $y$. *Proof:* the Haar
  modulus is intrinsic: $\Psi$ is measure preserving (`map_adeleBaseChange_muAddVec`) and conjugates $x\mapsto yx$ to
  $a\mapsto M(y)a$, whose modulus is $\|\det M(y)\|_{\mathbb A_k}$ (`map_mulVec_muAddVec`). This is the transport
  of multiplicative Haar measures: $\|y\|_{\mathbb A_K}^{-1}dy$ on $\mathbb A_K^\times$ is
  $\|N_{K/k}(y)\|_{\mathbb A_k}^{-1}\,d(\Psi^{-1}y)$ in $k$-coordinates.
-/

open IsDedekindDomain NumberField Topology Filter MeasureTheory NumberField.mixedEmbedding Matrix
open scoped ENNReal

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

set_option synthInstance.maxHeartbeats 400000

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k K)

/-- The matrix over $\mathbb A_k$ of $x\mapsto yx$ on $\mathbb A_K = \mathbb A_k^\iota$: column $j$ is $\Psi^{-1}(y\,b_j)$. -/
def adeleLmat (y : Adeles K) : Matrix ι ι (Adeles k) :=
  Matrix.of fun i j => (adeleBaseChange b).symm (y * diagRing K (b j)) i

theorem adeleBaseChange_single (j : ι) : adeleBaseChange b (Pi.single j 1) = diagRing K (b j) := by
  rw [adeleBaseChange_apply, Finset.sum_eq_single j]
  · rw [Pi.single_eq_same, map_one, mul_one]
  · intro i _ hij; rw [Pi.single_eq_of_ne hij, map_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- $\Psi(M(y)\,a) = y\,\Psi(a)$. -/
theorem adeleBaseChange_mulVec_adeleLmat (y : Adeles K) (a : AdeleSpace k ι) :
    adeleBaseChange b (adeleLmat b y *ᵥ a) = y * adeleBaseChange b a := by
  have hsplit : adeleLmat b y *ᵥ a = ∑ j, fun i => a j * adeleLmat b y i j := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hcol : ∀ j, (fun i => adeleLmat b y i j) = (adeleBaseChange b).symm (y * diagRing K (b j)) := fun j => rfl
  rw [hsplit, map_sum]
  simp only [adeleBaseChange_smul, hcol, ContinuousAddEquiv.apply_symm_apply]
  rw [adeleBaseChange_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem adeleLmat_ext {M N : Matrix ι ι (Adeles k)}
    (h : ∀ a, adeleBaseChange b (M *ᵥ a) = adeleBaseChange b (N *ᵥ a)) : M = N := by
  refine Matrix.ext fun i j => ?_
  have := congrFun ((adeleBaseChange b).injective (h (Pi.single j 1))) i
  simpa [Matrix.mulVec_single_one] using this

theorem adeleLmat_mul (y z : Adeles K) : adeleLmat b (y * z) = adeleLmat b y * adeleLmat b z :=
  adeleLmat_ext b fun a => by
    rw [← Matrix.mulVec_mulVec, adeleBaseChange_mulVec_adeleLmat, adeleBaseChange_mulVec_adeleLmat,
      adeleBaseChange_mulVec_adeleLmat, mul_assoc]

theorem adeleLmat_one : adeleLmat b 1 = 1 :=
  adeleLmat_ext b fun a => by rw [adeleBaseChange_mulVec_adeleLmat, one_mul, Matrix.one_mulVec]

/-- $y\mapsto M(y)$ as a monoid homomorphism. -/
def adeleLmatHom : Adeles K →* Matrix ι ι (Adeles k) where
  toFun := adeleLmat b
  map_one' := adeleLmat_one b
  map_mul' := adeleLmat_mul b

/-- $M(y)\in\mathrm{GL}_\iota(\mathbb A_k)$ for an idele $y$. -/
def adeleLmatGL : (Adeles K)ˣ →* GL ι (Adeles k) := Units.map (adeleLmatHom b)

/-- **The adelic norm** $N_{K/k} : \mathbb A_K^\times\to\mathbb A_k^\times$, $y\mapsto\det M(y)$. -/
def adeleNorm : (Adeles K)ˣ →* (Adeles k)ˣ := Matrix.GeneralLinearGroup.det.comp (adeleLmatGL b)

/-- For $c\in K$, $M(c)$ is `Algebra.leftMulMatrix b c` (entrywise diagonal). -/
theorem adeleLmat_diag (c : K) :
    adeleLmat b (diagRing K c) = (Algebra.leftMulMatrix b c).map (diagRing k) :=
  adeleLmat_ext b fun a => by
    rw [adeleBaseChange_mulVec_adeleLmat, ← adeleBaseChange_mulVec]
    congr 1

/-- $N_{K/k}$ extends the field norm: $N(c) = N_{K/k}(c)$ for $c\in K^\times$. -/
theorem adeleNorm_diagUnits (c : Kˣ) :
    adeleNorm b (diagUnits K c) = diagUnits k (Units.map (Algebra.norm k : K →* k) c) := by
  refine Units.ext ?_
  change (adeleLmat b (diagRing K c)).det = diagRing k (Algebra.norm k (c : K))
  rw [adeleLmat_diag, Algebra.norm_eq_matrix_det b]
  exact (RingHom.map_det (diagRing k) _).symm

/-- **$\|N_{K/k}(y)\|_{\mathbb A_k} = \|y\|_{\mathbb A_K}$** for every idele $y$ of $K$ (transport of the Haar modulus
along $\Psi$). -/
@[kb "weil1982" "§2.1 [unverified page]"]
theorem ideleNorm_adeleNorm (y : (Adeles K)ˣ) : ideleNorm k (adeleNorm b y) = ideleNorm K y := by
  have hm : Measurable (adeleBaseChange b) := (adeleBaseChange b).continuous.measurable
  have hms : Measurable (adeleBaseChange b).symm := (adeleBaseChange b).symm.continuous.measurable
  have hmy : Measurable fun x : Adeles K => y • x := measurable_const_smul _
  have hconj : (fun a => (adeleLmatGL b y : Matrix ι ι (Adeles k)) *ᵥ a) =
      (adeleBaseChange b).symm ∘ (fun x => y • x) ∘ (adeleBaseChange b) := by
    funext a
    simp only [Function.comp_apply]
    rw [Units.smul_def, smul_eq_mul, ← adeleBaseChange_mulVec_adeleLmat, ContinuousAddEquiv.symm_apply_apply]
    rfl
  have hΨ := map_adeleBaseChange_muAddVec b
  have hΨs : (muAdd K).map (adeleBaseChange b).symm = muAddVec k ι := by
    rw [← hΨ, Measure.map_map hms hm]
    have : (adeleBaseChange b).symm ∘ (adeleBaseChange b) = id := funext fun x => by simp
    rw [this, Measure.map_id]
  have h1 : (muAddVec k ι).map (fun a => (adeleLmatGL b y : Matrix ι ι (Adeles k)) *ᵥ a) =
      ENNReal.ofReal (ideleNorm K y)⁻¹ • muAddVec k ι := by
    rw [hconj, ← Measure.map_map hms (hmy.comp hm), ← Measure.map_map hmy hm, hΨ,
      map_smul_muAdd, Measure.map_smul, hΨs]
    exact hms.aemeasurable
  have h2 := map_mulVec_muAddVec (F := k) (ι := ι) (adeleLmatGL b y)
  rw [h1] at h2
  have h3 := congrArg (fun μ : Measure (AdeleSpace k ι) => μ (fundDomVec k ι)) h2
  simp only [Measure.smul_apply, smul_eq_mul] at h3
  rw [← (isAddFundamentalDomain_fundDomVec (muAddVec k ι)).covolume_eq_volume, addCovolume_muAddVec,
    mul_one, mul_one] at h3
  have hpos1 := ideleNorm_pos y
  have hpos2 := ideleNorm_pos (GeneralLinearGroup.det (adeleLmatGL b y))
  have := (ENNReal.ofReal_eq_ofReal_iff (inv_nonneg.mpr hpos1.le) (inv_nonneg.mpr hpos2.le)).mp h3
  exact (inv_inj.mp this).symm

end

end QuadFormsKB.Tamagawa.Measure.Weil
