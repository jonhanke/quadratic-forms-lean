import QuadFormsKB.Tamagawa.Measure.Weil.BaseChangeInfinite
import QuadFormsKB.Tamagawa.Measure.Weil.Ideles

/-!
# Base change of adeles: $K\otimes_k\mathbb A_k\cong\mathbb A_K$
$K/k$ is any finite extension of number fields and $b = (b_i)_{i\in\iota}$ any $k$-basis of $K$, so that
$K\otimes_k\mathbb A_k = \mathbb A_k^\iota$ (`AdeleSpace k ι`) in the coordinates $b$.

* `finMap k K : 𝔸_{k,f} →+* 𝔸_{K,f}` and `infRingHom k K : k_∞ →+* K_∞`, hence **`adeleMap k K : 𝔸_k →+* 𝔸_K`**,
  continuous ring homomorphisms extending $k\hookrightarrow K$ (`adeleMap_diag`). Multiplicativity of the finite part is
  by density of $k$ in $\mathbb A_{k,f}$; of the infinite part by $\mathbb R$-bilinearity on the basis `latticeBasis k`.
* **`adeleBaseChange b : 𝔸_k^ι ≃ₜ+ 𝔸_K`**, an additive homeomorphism with the closed formula
  **`adeleBaseChange_apply`**: $\Psi(a) = \sum_i b_i\,\iota(a_i)$ ($\iota$ = `adeleMap`), i.e. $\Psi$ is the map
  $K\otimes_k\mathbb A_k\to\mathbb A_K$, $\sum_i b_i\otimes a_i\mapsto\sum_ib_i\iota(a_i)$. It is
  * $\mathbb A_k$-linear (`adeleBaseChange_smul`: $\Psi(ta) = \iota(t)\Psi(a)$),
  * $K$-linear (`adeleBaseChange_mulVec`: multiplication by $c\in K$ is the matrix `Algebra.leftMulMatrix b c`),
  * the identity on $K$: `adeleBaseChange_diag` ($\Psi(x) = \sum_ix_ib_i$), so $\Psi(k^\iota) = K$
    (`adeleBaseChange_map_diagVecSub`).
  These two linearity properties say that $\Psi$ is the ring isomorphism $K\otimes_k\mathbb A_k\cong\mathbb A_K$ (the
  multiplication of $K\otimes_k\mathbb A_k$ is determined by them); `quadBaseChange` makes this explicit for a quadratic
  extension.

This is a lean rewrite: the FLT project's `IsDedekindDomain.FiniteAdeleRing.baseChangeAlgEquiv`
(`FLT/DedekindDomain/FiniteAdeleRing/BaseChange.lean`) is cited, not imported.
-/

open IsDedekindDomain NumberField Topology Filter NumberField.mixedEmbedding

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

local notation "Ak" => FiniteAdeleRing (𝓞 k) k
local notation "AK" => FiniteAdeleRing (𝓞 K) K

/-! ### The finite ring map $\mathbb A_{k,f}\to\mathbb A_{K,f}$ -/

section FinMap

variable (k K) in
/-- $t\mapsto\Psi_f(t\cdot\lambda)$ with $\lambda$ the coordinates of $1$ in `Module.finBasis k K`. -/
def finMapFun (t : Ak) : AK :=
  finBaseChange (Module.finBasis k K)
    (fun i => algebraMap k Ak ((Module.finBasis k K).equivFun 1 i) * t)

theorem continuous_finMapFun : Continuous (finMapFun k K) :=
  (finBaseChange _).continuous.comp (continuous_pi fun _ => continuous_const_mul _)

theorem finMapFun_algebraMap (x : k) :
    finMapFun k K (algebraMap k Ak x) = algebraMap K AK (algebraMap k K x) := by
  set b := Module.finBasis k K
  have h : (fun i => algebraMap k Ak (b.equivFun 1 i) * algebraMap k Ak x) =
      diagFinVec (x • b.equivFun 1) := by
    funext i
    rw [diagFinVec_apply, Pi.smul_apply, smul_eq_mul, map_mul, mul_comm]
  rw [finMapFun, h, finBaseChange_diag, map_smul, LinearEquiv.symm_apply_apply, Algebra.smul_def, mul_one]

theorem finMapFun_add (s t : Ak) : finMapFun k K (s + t) = finMapFun k K s + finMapFun k K t := by
  simp only [finMapFun, mul_add]
  exact map_add (finBaseChange (Module.finBasis k K)) _ _

theorem finMapFun_mul (s t : Ak) : finMapFun k K (s * t) = finMapFun k K s * finMapFun k K t := by
  refine denseRange_algebraMap_finiteAdele.induction_on₂
    (p := fun s t => finMapFun k K (s * t) = finMapFun k K s * finMapFun k K t) ?_ ?_ s t
  · exact isClosed_eq (continuous_finMapFun.comp continuous_mul)
      ((continuous_finMapFun.comp continuous_fst).mul (continuous_finMapFun.comp continuous_snd))
  · intro x y
    simp only [← map_mul, finMapFun_algebraMap]

variable (k K) in
/-- **The finite adele map** $\iota_f : \mathbb A_{k,f}\to\mathbb A_{K,f}$, a continuous ring homomorphism extending
$k\hookrightarrow K$ (`finMap_algebraMap`). -/
def finMap : Ak →+* AK where
  toFun := finMapFun k K
  map_one' := by rw [← map_one (algebraMap k Ak), finMapFun_algebraMap, map_one, map_one]
  map_mul' := finMapFun_mul
  map_zero' := by rw [← map_zero (algebraMap k Ak), finMapFun_algebraMap, map_zero, map_zero]
  map_add' := finMapFun_add

theorem continuous_finMap : Continuous (finMap k K) := continuous_finMapFun

theorem finMap_algebraMap (x : k) : finMap k K (algebraMap k Ak x) = algebraMap K AK (algebraMap k K x) :=
  finMapFun_algebraMap x

variable {ι : Type} [Fintype ι] (b : Module.Basis ι k K)

/-- **Closed formula for the finite base change**: $\Psi_f(a) = \sum_ib_i\,\iota_f(a_i)$. -/
theorem finBaseChange_eq_sum (a : ι → Ak) :
    finBaseChange b a = ∑ i, algebraMap K AK (b i) * finMap k K (a i) := by
  have hc : Continuous fun a : ι → Ak => ∑ i, algebraMap K AK (b i) * finMap k K (a i) :=
    continuous_finset_sum _ fun i _ => continuous_const_mul _ |>.comp (continuous_finMap.comp (continuous_apply i))
  have := denseRange_diagFinVec.equalizer (finBaseChange b).continuous hc (funext fun x => by
    show finBaseChange b (diagFinVec x) = ∑ i, algebraMap K AK (b i) * finMap k K (diagFinVec x i)
    rw [finBaseChange_diag]
    simp only [diagFinVec_apply, finMap_algebraMap, ← map_mul, ← map_sum, Module.Basis.equivFun_symm_apply,
      Algebra.smul_def, mul_comm])
  exact congrFun this a

end FinMap

/-! ### The archimedean ring map $k_\infty\to K_\infty$ -/

section InfMap

theorem infMap_mixedEmbedding_mul (t : k) (y : mixedSpace k) :
    infMap k K (mixedEmbedding k t * y) = mixedEmbedding K (algebraMap k K t) * infMap k K y := by
  have : (infMap k K) ∘ₗ (LinearMap.mulLeft ℝ (mixedEmbedding k t)) =
      (LinearMap.mulLeft ℝ (mixedEmbedding K (algebraMap k K t))) ∘ₗ (infMap k K) := by
    refine (latticeBasis k).ext fun j => ?_
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, latticeBasis_apply, ← map_mul,
      infMap_mixedEmbedding]
  exact LinearMap.congr_fun this y

theorem infMap_mul (x y : mixedSpace k) : infMap k K (x * y) = infMap k K x * infMap k K y := by
  have : (infMap k K) ∘ₗ (LinearMap.mulRight ℝ y) =
      (LinearMap.mulRight ℝ (infMap k K y)) ∘ₗ (infMap k K) := by
    refine (latticeBasis k).ext fun j => ?_
    simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, latticeBasis_apply,
      infMap_mixedEmbedding_mul, infMap_mixedEmbedding]
  exact LinearMap.congr_fun this x

theorem infMap_one : infMap k K 1 = 1 := by
  rw [← map_one (mixedEmbedding k), infMap_mixedEmbedding, map_one, map_one]

variable (k K) in
/-- **The archimedean map** $\iota_\infty : k_\infty\to K_\infty$ as a ring homomorphism. -/
def infRingHom : mixedSpace k →+* mixedSpace K where
  toFun := infMap k K
  map_one' := infMap_one
  map_mul' := infMap_mul
  map_zero' := map_zero _
  map_add' := map_add _

theorem continuous_infRingHom : Continuous (infRingHom k K) :=
  (infMap k K).continuous_of_finiteDimensional

theorem infRingHom_mixedEmbedding (x : k) :
    infRingHom k K (mixedEmbedding k x) = mixedEmbedding K (algebraMap k K x) := infMap_mixedEmbedding x

end InfMap

/-! ### The adele map and the base change isomorphism -/

variable (k K) in
/-- **The natural map** $\iota : \mathbb A_k\to\mathbb A_K$ (continuous ring homomorphism). -/
def adeleMap : Adeles k →+* Adeles K :=
  ((infRingHom k K).comp (RingHom.fst _ _)).prod ((finMap k K).comp (RingHom.snd _ _))

@[simp] theorem adeleMap_fst (t : Adeles k) : (adeleMap k K t).1 = infRingHom k K t.1 := rfl
@[simp] theorem adeleMap_snd (t : Adeles k) : (adeleMap k K t).2 = finMap k K t.2 := rfl

theorem continuous_adeleMap : Continuous (adeleMap k K) :=
  (continuous_infRingHom.comp continuous_fst).prodMk (continuous_finMap.comp continuous_snd)

/-- $\iota$ extends $k\hookrightarrow K$. -/
theorem adeleMap_diag (x : k) : adeleMap k K (diag k x) = diag K (algebraMap k K x) :=
  Prod.ext (infRingHom_mixedEmbedding x) (finMap_algebraMap x)

variable {ι : Type} [Fintype ι] (b : Module.Basis ι k K)

/-- **Base change of adeles** $\Psi : \mathbb A_k^\iota = K\otimes_k\mathbb A_k\cong\mathbb A_K$, an additive homeomorphism
(`infBaseChange` × `finBaseChange`). -/
def adeleBaseChange : AdeleSpace k ι ≃ₜ+ Adeles K where
  toFun a := (infBaseChange b fun i => (a i).1, finBaseChange b fun i => (a i).2)
  invFun y i := ((infBaseChange b).symm y.1 i, (finBaseChange b).symm y.2 i)
  left_inv a := by
    funext i
    simp only [ContinuousLinearEquiv.symm_apply_apply, ContinuousAddEquiv.symm_apply_apply]
  right_inv y := by
    simp only [ContinuousLinearEquiv.apply_symm_apply, ContinuousAddEquiv.apply_symm_apply]
  map_add' a a' := by
    refine Prod.ext ?_ ?_
    · exact map_add (infBaseChange b) (fun i => (a i).1) (fun i => (a' i).1)
    · exact map_add (finBaseChange b) (fun i => (a i).2) (fun i => (a' i).2)
  continuous_toFun :=
    ((infBaseChange b).continuous.comp (continuous_pi fun i => continuous_fst.comp (continuous_apply i))).prodMk
      ((finBaseChange b).continuous.comp (continuous_pi fun i => continuous_snd.comp (continuous_apply i)))
  continuous_invFun := continuous_pi fun i =>
    ((continuous_apply i).comp ((infBaseChange b).symm.continuous.comp continuous_fst)).prodMk
      ((continuous_apply i).comp ((finBaseChange b).symm.continuous.comp continuous_snd))

theorem adeleBaseChange_apply_fst (a : AdeleSpace k ι) :
    (adeleBaseChange b a).1 = infBaseChange b fun i => (a i).1 := rfl

theorem adeleBaseChange_apply_snd (a : AdeleSpace k ι) :
    (adeleBaseChange b a).2 = finBaseChange b fun i => (a i).2 := rfl

/-- **Closed formula**: $\Psi(a) = \sum_ib_i\,\iota(a_i)$, i.e. $\Psi(\sum_ib_i\otimes a_i) = \sum_ib_i\iota(a_i)$. -/
theorem adeleBaseChange_apply (a : AdeleSpace k ι) :
    adeleBaseChange b a = ∑ i, diagRing K (b i) * adeleMap k K (a i) := by
  refine Prod.ext ?_ ?_
  · rw [adeleBaseChange_apply_fst, infBaseChange_apply, infBaseChangeLin_apply, Prod.fst_sum]
    rfl
  · rw [adeleBaseChange_apply_snd, finBaseChange_eq_sum, Prod.snd_sum]
    rfl

/-- **$\Psi$ is the identity on $K$**: $\Psi(x) = \sum_ix_ib_i$ for $x\in k^\iota$. -/
@[kb "casselsfrohlich1967" "Ch. II (Cassels), §14, Lemma, (14.2), pp. 63–64 (k ⊗ K = K is mapped identically onto K ⊂ V_K), and Cor., p. 64; FLT `FiniteAdeleRing.baseChangeAlgEquiv` (cited)"]
theorem adeleBaseChange_diag (x : ι → k) :
    adeleBaseChange b (diagVec k ι x) = diag K (b.equivFun.symm x) := by
  rw [adeleBaseChange_apply]
  simp only [diagVec_apply, adeleMap_diag]
  simp only [← diagRing_apply, ← map_mul, ← map_sum, Module.Basis.equivFun_symm_apply, Algebra.smul_def,
    mul_comm]

/-- $\Psi$ maps $k^\iota\subset\mathbb A_k^\iota$ onto $K\subset\mathbb A_K$. -/
theorem adeleBaseChange_map_diagVecSub :
    (diagVecSub k ι).map (adeleBaseChange b).toAddEquiv.toAddMonoidHom = diagSub K := by
  ext y
  simp only [AddSubgroup.mem_map, diagVecSub, diagSub, AddMonoidHom.mem_range]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨b.equivFun.symm x, (adeleBaseChange_diag b x).symm⟩
  · rintro ⟨z, rfl⟩
    refine ⟨_, ⟨b.equivFun z, rfl⟩, ?_⟩
    change adeleBaseChange b (diagVec k ι (b.equivFun z)) = _
    rw [adeleBaseChange_diag, LinearEquiv.symm_apply_apply]

/-- **$\mathbb A_k$-linearity**: $\Psi(t\,a) = \iota(t)\,\Psi(a)$. -/
theorem adeleBaseChange_smul (t : Adeles k) (a : AdeleSpace k ι) :
    adeleBaseChange b (fun i => t * a i) = adeleMap k K t * adeleBaseChange b a := by
  simp only [adeleBaseChange_apply, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **$K$-linearity**: multiplication by $c\in K$ on $K\otimes_k\mathbb A_k = \mathbb A_k^\iota$ is the matrix
$M = $ `Algebra.leftMulMatrix b c` ($cb_j = \sum_iM_{ij}b_i$), and $\Psi(Ma) = c\,\Psi(a)$. -/
theorem adeleBaseChange_mulVec [DecidableEq ι] (c : K) (a : AdeleSpace k ι) :
    adeleBaseChange b (fun i => ∑ j, diagRing k (Algebra.leftMulMatrix b c i j) * a j) =
      diagRing K c * adeleBaseChange b a := by
  simp only [adeleBaseChange_apply, map_sum, map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hcb : c * b j = ∑ i, Algebra.leftMulMatrix b c i j • b i := by
    simp only [Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply, Algebra.coe_lmul_eq_mul,
      LinearMap.mul_apply']
    exact (b.sum_repr (c * b j)).symm
  have hι : ∀ i, adeleMap k K (diagRing k (Algebra.leftMulMatrix b c i j)) =
      diagRing K (algebraMap k K (Algebra.leftMulMatrix b c i j)) := fun i => adeleMap_diag _
  simp only [hι]
  rw [← mul_assoc, ← map_mul, hcb, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, map_mul]
  ring

end

end QuadFormsKB.Tamagawa.Measure.Weil
