import QuadFormsKB.Tamagawa.Measure.Weil.BaseChangeIntegral

/-!
# The local constant $c_v=1$ at the good places

For a basis $b$ of algebraic integers with $v(\operatorname{disc}b)=1$ we show `localConst b v = 1`, i.e. the coordinate
measure $dx_v^{\otimes\iota}$ is carried by the base change to exactly the product of the $\psi_{K,w}$-self-dual
measures. Proof (duality trick, no Fourier analysis beyond the library's `selfDualV_real_mul`):

1. `pairing_localPi`: $\sum_{w\mid v}\operatorname{Tr}_{K_w/k_v}(\Phi(c)_w\Phi(y)_w)=\sum_{ij}c_iG_{ij}y_j$ ($G$ the trace Gram
   matrix), by the local trace formula `traceMatrix_map_eq_sum`.
2. `localPi_preimage_dual`: $\Phi^{-1}\big(\prod_w\mathfrak p_w^{-d_w}\big)=(\mathfrak p_v^{-d_v})^\iota$. Both are the
   $\psi_v\circ\operatorname{Tr}$-duals of $\Phi(\mathcal O_v^\iota)=\prod_w\mathcal O_w$ (`localPi_image_integers`); on the
   $k_v^\iota$ side because $G\in\mathrm{GL}_n(\mathcal O_v)$, on the other side because $\psi_{K,w}=\psi_v\circ\operatorname{Tr}_{K_w/k_v}$.
3. $c_v^2\,\nu(\prod\mathcal O_w)\,\nu(\prod\mathfrak p_w^{-d_w})=\mu(\mathcal O_v^\iota)\,\mu(\ldots)$, and both products of volumes are $1$
   (`selfDualV_real_mul`), so $c_v^2=1$.

Sources: Tate's thesis, Cassels–Fröhlich Ch. XV §2.2 [unverified] (self-dual measure: $\operatorname{vol}(L)\operatorname{vol}(L^\perp)=1$);
Neukirch, *Algebraic Number Theory*, Ch. III Prop. 2.12 [unverified].
-/

open IsDedekindDomain NumberField Topology Filter MeasureTheory QuadFormsKB
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

/-- Cramer's rule bound over any valued field: if $G$ has entries of valuation $\le1$ and a unit determinant, then
$Gr=t$ with all $\nu(t_j)\le m$ forces $\nu(r_i)\le m$ (for $m\ge1$... any $m$ with $\nu(\text{adj}\cdot t)\le m$). -/
theorem val_le_of_mulVec_eq {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] (ν : Valuation F Γ) (G : Matrix ι ι F) (hG : ∀ i j, ν (G i j) ≤ 1)
    (hdet : ν G.det = 1) (m : Γ) (t r : ι → F) (ht : ∀ j, ν (t j) ≤ m)
    (hr : G.mulVec r = t) (i : ι) : ν (r i) ≤ m := by
  let R := ν.valuationSubring
  let G' : Matrix ι ι R := Matrix.of fun i j => ⟨G i j, (Valuation.mem_valuationSubring_iff _ _).mpr (hG i j)⟩
  have hGG : G'.map R.subtype = G := by ext i j; rfl
  have hadj : ∀ i j, ν (G.adjugate i j) ≤ 1 := by
    intro i j
    have := congrFun (congrFun (RingHom.map_adjugate R.subtype G') i) j
    rw [← hGG]
    have h2 : (G'.map R.subtype).adjugate i j = R.subtype (G'.adjugate i j) := by
      simpa using this.symm
    rw [h2]
    exact (Valuation.mem_valuationSubring_iff _ _).mp (G'.adjugate i j).2
  have key : G.det • r = G.adjugate.mulVec t := by
    rw [← hr, Matrix.mulVec_mulVec, Matrix.adjugate_mul]
    funext j
    simp [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.one_apply]
  have h1 : ν (G.det * r i) ≤ m := by
    have := congrFun key i
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct] at this
    rw [this]
    refine Valuation.map_sum_le _ fun j _ => ?_
    rw [map_mul]
    calc ν (G.adjugate i j) * ν (t j) ≤ 1 * m := mul_le_mul' (hadj i j) (ht j)
      _ = m := one_mul m
  rwa [map_mul, hdet, one_mul] at h1

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  {ι : Type} [Fintype ι] (b : Module.Basis ι k K) (v : HeightOneSpectrum (𝓞 k))

/-- **The trace pairing in coordinates:** $\sum_{w\mid v}\operatorname{Tr}_{K_w/k_v}(\Phi(c)_w\Phi(y)_w)
=\sum_{i,j}c_iG_{ij}y_j$ with $G=(\operatorname{Tr}_{K/k}(b_ib_j))$. -/
theorem pairing_localPi (c y : ι → v.adicCompletion k) :
    ∑ w : PlaceSet (K := K) v, localTrace v w.1 w.2 (localPi b v c w * localPi b v y w) =
      ∑ i, ∑ j, c i * algebraMap k (v.adicCompletion k) (Algebra.traceMatrix k b i j) * y j := by
  have h1 : ∀ w : PlaceSet (K := K) v, localTrace v w.1 w.2 (localPi b v c w * localPi b v y w) =
      ∑ i, ∑ j, (c i * y j) * localTrace v w.1 w.2 (((b i * b j : K)) : w.1.adicCompletion K) := by
    intro w
    rw [localPi_apply, localPi_apply, Finset.sum_mul_sum]
    rw [localTrace_eq, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e : ((b i : K) : w.1.adicCompletion K) * localRingHom v w.1 w.2 (c i) *
        (((b j : K) : w.1.adicCompletion K) * localRingHom v w.1 w.2 (y j)) =
        (c i * y j) • (((b i * b j : K)) : w.1.adicCompletion K) := by
      rw [Algebra.smul_def, algebraMap_instAlgebraPlace, map_mul]
      have : (((b i * b j : K)) : w.1.adicCompletion K) =
          ((b i : K) : w.1.adicCompletion K) * ((b j : K) : w.1.adicCompletion K) := by
        change algebraMap K (w.1.adicCompletion K) (b i * b j) = _
        rw [map_mul]; rfl
      rw [this]; ring
    rw [e, map_smul, smul_eq_mul, localTrace_eq]
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum, traceMatrix_map_eq_sum]
  ring

/-- $\prod_w\mathfrak p_w^{-d_w}\subseteq\prod_{w\mid v}K_w$. -/
def dualPlace : Set (PlaceProd (K := K) v) := {z | ∀ w, Valued.v (z w) ≤ WithZero.exp (Analysis.diffExp w.1 : ℤ)}

/-- $(\mathfrak p_v^{-d_v})^\iota\subseteq k_v^\iota$. -/
def dualLat : Set (ι → v.adicCompletion k) := {c | ∀ i, Valued.v (c i) ≤ WithZero.exp (Analysis.diffExp v : ℤ)}

theorem psiV_prod_eq (s : Finset ι) (f : ι → v.adicCompletion k) :
    Analysis.psiV v (∑ i ∈ s, f i) = ∏ i ∈ s, Analysis.psiV v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j S hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, AddChar.map_add_eq_mul, ih]

/-- **Duality on $\prod_{w\mid v}K_w$:** $z\in\prod\mathfrak p_w^{-d_w}$ iff $\psi_v(\operatorname{Tr}(zy))=1$ for all
$y\in\prod\mathcal O_w$. -/
theorem mem_dualPlace_iff (z : PlaceProd (K := K) v) :
    z ∈ dualPlace (K := K) v ↔ ∀ y ∈ intPlace (K := K) v,
      Analysis.psiV v (∑ w : PlaceSet (K := K) v, localTrace v w.1 w.2 (z w * y w)) = 1 := by
  classical
  have hloc : ∀ (w : PlaceSet (K := K) v) (x : w.1.adicCompletion K),
      Analysis.psiV v (localTrace v w.1 w.2 x) = Analysis.psiV w.1 x := fun w x =>
    (psiV_localTrace v (toSp v w.1 w.2) w.2 x).symm
  constructor
  · intro hz y hy
    rw [psiV_prod_eq]
    refine Finset.prod_eq_one fun w _ => ?_
    rw [hloc]
    have : z w ∈ Analysis.invDiffV w.1 := (Analysis.mem_invDiffV_iff w.1 _).mpr (hz w)
    rw [mul_comm]
    exact this _ (hy w)
  · intro h w0
    rw [← Analysis.mem_invDiffV_iff]
    intro x hx
    have hy : (Pi.single w0 x : PlaceProd (K := K) v) ∈ intPlace (K := K) v := by
      intro w
      by_cases hw : w = w0
      · subst hw; simpa using hx
      · simp [Pi.single_eq_of_ne hw]
    have := h _ hy
    rw [psiV_prod_eq, Finset.prod_eq_single w0] at this
    · rw [hloc] at this
      rw [mul_comm]
      simpa using this
    · intro w _ hw
      simp [Pi.single_eq_of_ne hw]
    · simp

section Dual

variable [DecidableEq ι]

/-- The trace Gram matrix over $k_v$. -/
def gramV : Matrix ι ι (v.adicCompletion k) := (Algebra.traceMatrix k b).map (algebraMap k (v.adicCompletion k))

theorem gramV_symm (i j : ι) : gramV b v i j = gramV b v j i := by
  simp only [gramV, Matrix.map_apply, Algebra.traceMatrix_apply]
  rw [Algebra.traceForm_apply, Algebra.traceForm_apply, mul_comm]

theorem valued_gramV_le_one (hb : ∀ i, IsIntegral ℤ (b i)) (i j : ι) : Valued.v (gramV b v i j) ≤ 1 := by
  simp only [gramV, Matrix.map_apply, Algebra.traceMatrix_apply]
  rw [HN.valued_algebraMap]
  exact valuation_trace_le_one v _ ((hb i).mul (hb j))

theorem valued_det_gramV (hd : v.valuation k (Algebra.discr k b) = 1) : Valued.v (gramV b v).det = 1 := by
  have : (gramV b v).det = algebraMap k (v.adicCompletion k) (Algebra.discr k b) := by
    rw [Algebra.discr_def, gramV, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rw [this, HN.valued_algebraMap]
  exact hd

theorem sum_gram_eq (c y : ι → v.adicCompletion k) :
    ∑ i, ∑ j, c i * algebraMap k (v.adicCompletion k) (Algebra.traceMatrix k b i j) * y j =
      ∑ j, ((gramV b v).mulVec c) j * y j := by
  simp only [Matrix.mulVec, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  have hs : algebraMap k (v.adicCompletion k) (Algebra.traceMatrix k b i j) = gramV b v j i := by
    rw [gramV_symm b v j i]; rfl
  rw [hs]
  ring

/-- **Duality on $k_v^\iota$ for the trace form:** if $G\in\mathrm{GL}_n(\mathcal O_v)$, $c\in(\mathfrak p_v^{-d_v})^\iota$ iff
$\psi_v(c^TGy)=1$ for all $y\in\mathcal O_v^\iota$. -/
theorem mem_dualLat_iff (hb : ∀ i, IsIntegral ℤ (b i)) (hd : v.valuation k (Algebra.discr k b) = 1)
    (c : ι → v.adicCompletion k) :
    c ∈ dualLat (ι := ι) v ↔ ∀ y ∈ intLat (ι := ι) v,
      Analysis.psiV v (∑ i, ∑ j, c i * algebraMap k (v.adicCompletion k) (Algebra.traceMatrix k b i j) * y j) = 1 := by
  classical
  simp only [sum_gram_eq]
  have hg : c ∈ dualLat (ι := ι) v ↔ ∀ j, Valued.v (((gramV b v).mulVec c) j) ≤ WithZero.exp (Analysis.diffExp v : ℤ) := by
    constructor
    · intro hc j
      simp only [Matrix.mulVec, dotProduct]
      refine Valuation.map_sum_le _ fun i _ => ?_
      rw [map_mul]
      calc _ ≤ 1 * WithZero.exp (Analysis.diffExp v : ℤ) := mul_le_mul' (valued_gramV_le_one b v hb j i) (hc i)
        _ = _ := one_mul _
    · intro h i
      exact val_le_of_mulVec_eq (Valued.v) (gramV b v) (valued_gramV_le_one b v hb) (valued_det_gramV b v hd) _ _ c h rfl i
  rw [hg]
  constructor
  · intro h y hy
    rw [psiV_prod_eq]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [mul_comm]
    exact (Analysis.mem_invDiffV_iff v _).mpr (h j) _ (hy j)
  · intro h j
    rw [← Analysis.mem_invDiffV_iff]
    intro x hx
    have hy : (Pi.single j x : ι → v.adicCompletion k) ∈ intLat (ι := ι) v := by
      intro i
      by_cases hi : i = j
      · subst hi; simpa using hx
      · simp [Pi.single_eq_of_ne hi]
    have := h _ hy
    rw [psiV_prod_eq, Finset.prod_eq_single j] at this
    · rw [mul_comm]; simpa using this
    · intro i _ hi; simp [Pi.single_eq_of_ne hi]
    · simp

/-- **$\Phi\big((\mathfrak p_v^{-d_v})^\iota\big)=\prod_{w\mid v}\mathfrak p_w^{-d_w}$** at the good places: the
$\psi_v\circ\operatorname{Tr}$-dual of $\Phi(\mathcal O_v^\iota)=\prod\mathcal O_w$ computed on both sides. -/
theorem localPi_image_dual (hb : ∀ i, IsIntegral ℤ (b i)) (hd : v.valuation k (Algebra.discr k b) = 1) :
    localPi b v '' dualLat (ι := ι) v = dualPlace (K := K) v := by
  ext z
  obtain ⟨c, rfl⟩ := localPi_surjective b v z
  rw [(localPi_injective b v).mem_set_image, mem_dualPlace_iff, mem_dualLat_iff b v hb hd]
  constructor
  · intro h y hy
    rw [← localPi_image_integers b v hb hd] at hy
    obtain ⟨y, hy, rfl⟩ := hy
    rw [pairing_localPi]
    exact h y hy
  · intro h y hy
    have := h (localPi b v y) (localPi_mem_intPlace b v hb hy)
    rwa [pairing_localPi] at this

end Dual

section Measure

theorem intLat_eq_pi : intLat (ι := ι) (k := k) v =
    Set.pi Set.univ fun _ : ι => (Analysis.latticeV v 0 : Set (v.adicCompletion k)) := by
  ext c; simp [intLat, Analysis.mem_latticeV]

theorem dualLat_eq_pi : dualLat (ι := ι) (k := k) v =
    Set.pi Set.univ fun _ : ι => (Analysis.latticeV v (-(Analysis.diffExp v : ℤ)) : Set (v.adicCompletion k)) := by
  ext c; simp [dualLat, Analysis.mem_latticeV]

theorem intPlace_eq_pi : intPlace (K := K) v =
    Set.pi Set.univ fun w : PlaceSet (K := K) v => (Analysis.latticeV w.1 0 : Set (w.1.adicCompletion K)) := by
  ext c; simp [intPlace, Analysis.mem_latticeV]

theorem dualPlace_eq_pi : dualPlace (K := K) v =
    Set.pi Set.univ fun w : PlaceSet (K := K) v =>
      (Analysis.latticeV w.1 (-(Analysis.diffExp w.1 : ℤ)) : Set (w.1.adicCompletion K)) := by
  ext c; simp [dualPlace, Analysis.mem_latticeV]

theorem real_pi_selfDual {F : Type} [Field F] [NumberField F] {J : Type} [Fintype J]
    (u : J → HeightOneSpectrum (𝓞 F)) (S : ∀ j, Set ((u j).adicCompletion F)) :
    (Measure.pi fun j => Analysis.selfDualV (u j)).real (Set.pi Set.univ S) =
      ∏ j, (Analysis.selfDualV (u j)).real (S j) := by
  rw [Measure.real, Measure.pi_pi, ENNReal.toReal_prod]
  rfl

theorem vol_mul_vol_dual :
    (volVN (ι := ι) v).real (intLat v) * (volVN (ι := ι) v).real (dualLat v) = 1 := by
  rw [intLat_eq_pi, dualLat_eq_pi]
  have := real_pi_selfDual (J := ι) (fun _ => v) (fun _ => (Analysis.latticeV v 0 : Set (v.adicCompletion k)))
  have h2 := real_pi_selfDual (J := ι) (fun _ => v)
    (fun _ => (Analysis.latticeV v (-(Analysis.diffExp v : ℤ)) : Set (v.adicCompletion k)))
  show (Measure.pi fun _ : ι => Analysis.selfDualV v).real _ * (Measure.pi fun _ : ι => Analysis.selfDualV v).real _ = 1
  rw [this, h2, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun _ _ => ?_
  have := Analysis.selfDualV_real_mul v 0
  simpa using this

theorem place_mul_place_dual :
    (placeMeasure (K := K) v).real (intPlace v) * (placeMeasure (K := K) v).real (dualPlace v) = 1 := by
  rw [intPlace_eq_pi, dualPlace_eq_pi]
  have h1 := real_pi_selfDual (J := PlaceSet (K := K) v) (fun w => w.1)
    (fun w => (Analysis.latticeV w.1 0 : Set (w.1.adicCompletion K)))
  have h2 := real_pi_selfDual (J := PlaceSet (K := K) v) (fun w => w.1)
    (fun w => (Analysis.latticeV w.1 (-(Analysis.diffExp w.1 : ℤ)) : Set (w.1.adicCompletion K)))
  unfold placeMeasure
  rw [h1, h2, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun w _ => ?_
  have := Analysis.selfDualV_real_mul w.1 0
  simpa using this

end Measure

/-- The transported measure of the image of a set. -/
theorem map_localPi_apply (S : Set (ι → v.adicCompletion k)) :
    ((volVN (ι := ι) v).map (localPiCLE b v)) (localPiCLE b v '' S) = volVN (ι := ι) v S := by
  have h := (localPiCLE b v).toHomeomorph.toMeasurableEquiv.map_apply (μ := volVN (ι := ι) v)
    (localPiCLE b v '' S)
  have hinj : Function.Injective (localPiCLE b v) := (localPiCLE b v).injective
  have h2 : (localPiCLE b v).toHomeomorph.toMeasurableEquiv ⁻¹' (localPiCLE b v '' S) = S :=
    Set.preimage_image_eq _ hinj
  rw [h2] at h
  exact h


variable [DecidableEq ι]

/-- **The local constant is $1$ at the good places.** If $b$ is a $k$-basis of $K$ consisting of algebraic integers and
$v(\operatorname{disc}b)=1$, the base change carries the coordinate self-dual measure $dx_v^{\otimes\iota}$ of $k_v^\iota$
to exactly the product $\bigotimes_{w\mid v}\mu_w$ of the $\psi_{K,w}$-self-dual measures. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2 (vol(L) vol(L^⊥) = 1 for self-dual measures) [unverified]; Neukirch III.2.12 [unverified]"]
theorem localConst_eq_one (hb : ∀ i, IsIntegral ℤ (b i)) (hd : v.valuation k (Algebra.discr k b) = 1) :
    localConst b v = 1 := by
  have hmap := map_volVN_localPi b v
  have e1 : ((volVN (ι := ι) v).map (localPiCLE b v)) (intPlace (K := K) v) = volVN (ι := ι) v (intLat v) := by
    rw [← localPi_image_integers b v hb hd]
    exact map_localPi_apply b v _
  have e2 : ((volVN (ι := ι) v).map (localPiCLE b v)) (dualPlace (K := K) v) = volVN (ι := ι) v (dualLat v) := by
    rw [← localPi_image_dual b v hb hd]
    exact map_localPi_apply b v _
  rw [hmap] at e1 e2
  have r1 : (volVN (ι := ι) v).real (intLat v) = (localConst b v : ℝ) * (placeMeasure (K := K) v).real (intPlace v) := by
    rw [Measure.real, ← e1, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal]; rfl
  have r2 : (volVN (ι := ι) v).real (dualLat v) = (localConst b v : ℝ) * (placeMeasure (K := K) v).real (dualPlace v) := by
    rw [Measure.real, ← e2, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal]; rfl
  have h := vol_mul_vol_dual (ι := ι) (k := k) v
  have h' := place_mul_place_dual (K := K) v
  rw [r1, r2] at h
  have hc : (localConst b v : ℝ) ^ 2 = 1 := by
    have : (localConst b v : ℝ) ^ 2 * ((placeMeasure (K := K) v).real (intPlace v) *
        (placeMeasure (K := K) v).real (dualPlace v)) = 1 := by rw [← h]; ring
    rwa [h', mul_one] at this
  have : (localConst b v : ℝ) = 1 := by
    have h0 : 0 ≤ (localConst b v : ℝ) := NNReal.coe_nonneg _
    nlinarith [sq_nonneg ((localConst b v : ℝ) - 1)]
  exact_mod_cast this


/-- A nonzero $x\in k$ is a $v$-adic unit for all but finitely many $v$ (the restricted-product condition for $x$ and
$x^{-1}$). -/
theorem finite_valuation_ne_one (x : k) (hx : x ≠ 0) :
    {v : HeightOneSpectrum (𝓞 k) | v.valuation k x ≠ 1}.Finite := by
  have h1 := (algebraMap k (FiniteAdeleRing (𝓞 k) k) x).2
  have h2 := (algebraMap k (FiniteAdeleRing (𝓞 k) k) x⁻¹).2
  have := h1.and h2
  rw [Filter.eventually_cofinite] at this
  refine this.subset fun v hv => ?_
  intro ⟨a, b⟩
  apply hv
  have a' : v.valuation k x ≤ 1 := by
    rw [← QuadFormsKB.HN.valued_algebraMap]
    exact a
  have b' : v.valuation k x⁻¹ ≤ 1 := by
    rw [← QuadFormsKB.HN.valued_algebraMap]
    exact b
  rw [map_inv₀] at b'
  have h0 : v.valuation k x ≠ 0 := by simpa using hx
  exact le_antisymm a' (by simpa using inv_le_one_iff₀.mp b' |>.resolve_left (by simpa using h0) |> fun h => h)

/-- **The local constants are $1$ outside the finitely many places dividing the discriminant**, hence
$\prod_v c_v$ is a finite product. (The individual $c_v$ at the bad places are not computed: the $\prod_vr_v=1$ comes from the global `map_adeleBaseChange_muAddVec` / `finprod_traceFactor_mul_inf`.) -/
theorem finite_localConst_ne_one (hb : ∀ i, IsIntegral ℤ (b i)) :
    {v : HeightOneSpectrum (𝓞 k) | localConst b v ≠ 1}.Finite := by
  refine (finite_valuation_ne_one (Algebra.discr k b) (Algebra.discr_not_zero_of_basis k b)).subset fun v hv => ?_
  intro hd
  exact hv (localConst_eq_one b v hb hd)

theorem finprod_localConst_eq_prod (hb : ∀ i, IsIntegral ℤ (b i)) :
    ∏ᶠ v, (localConst b v : ℝ) = ∏ v ∈ (finite_localConst_ne_one b hb).toFinset, (localConst b v : ℝ) := by
  classical
  refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
  simp only [Finset.mem_coe, Set.Finite.mem_toFinset]
  rw [Function.mem_mulSupport] at hv
  intro h
  exact hv (by rw [h]; simp)

end

end QuadFormsKB.Tamagawa.Measure.Weil
