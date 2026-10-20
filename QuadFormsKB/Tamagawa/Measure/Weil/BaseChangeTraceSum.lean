import QuadFormsKB.Tamagawa.Measure.Weil.BaseChangeTrace

/-!
# $K\otimes_kk_v\cong\prod_{w\mid v}K_w$ as $k_v$-modules, and the trace formula

With `PlaceSet v` the finite type of places of $K$ over $v$ and $A_v=\prod_{w\mid v}K_w$ (a $k_v$-algebra through the library's
`localRingHom`):

* `localPi b v : k_v^ι →ₗ[k_v] A_v`, $c\mapsto(\Psi_f(c e_v)_w)_{w\mid v}$, is bijective
  (`localPiEquiv`): injective by `isEmbedding_localBaseChange`; surjective because a finitely supported family
  $(z_w)_{w\mid v}$ is an adele supported over $v$ (`mem_range_localBaseChange_iff`).
* **`trace_localPi_conj`**: for $y\in A_v$ the trace of the $k_v$-linear map "multiply by $y$" on $k_v^\iota$ (transported
  through `localPi`) is $\sum_{w\mid v}\operatorname{Tr}_{K_w/k_v}(y_w)$ (`Algebra.trace_pi'`).
* **`trace_eq_sum_localTrace`**: for $x\in K$, $\operatorname{Tr}_{K/k}(x)=\sum_{w\mid v}\operatorname{Tr}_{K_w/k_v}(x)$ in $k_v$,
  and the matrix $\operatorname{Tr}(b_ib_j)$ is the sum over $w\mid v$ of the local trace forms (`traceMatrix_eq_sum_localTrace`).

Sources: Neukirch, *Algebraic Number Theory*, Ch. II Prop. 8.3 [unverified]; Cassels–Fröhlich Ch. II §14 [unverified];
Mathlib `Algebra.trace_eq_matrix_trace`, `LinearMap.trace_conj'`, and the library's `Algebra.trace_pi'`.
-/

open IsDedekindDomain NumberField Topology Filter

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  {ι : Type} [Fintype ι] (b : Module.Basis ι k K) (v : HeightOneSpectrum (𝓞 k))

/-- The places of $K$ over $v$. -/
abbrev PlaceSet : Type := {w : HeightOneSpectrum (𝓞 K) // underPlace (k := k) w = v}

instance : Fintype (PlaceSet (K := K) v) :=
  haveI : Finite (PlaceSet (K := K) v) := (finite_placesOver (K := K) v).to_subtype
  Fintype.ofFinite _

instance instAlgebraPlace (w : PlaceSet (K := K) v) :
    Algebra (v.adicCompletion k) (w.1.adicCompletion K) := localAlg v w.1 w.2

theorem algebraMap_instAlgebraPlace (w : PlaceSet (K := K) v) :
    algebraMap (v.adicCompletion k) (w.1.adicCompletion K) = localRingHom v w.1 w.2 := rfl

/-- $A_v=\prod_{w\mid v}K_w$. -/
abbrev PlaceProd : Type := ∀ w : PlaceSet (K := K) v, w.1.adicCompletion K

/-- **The $k_v$-linear map $k_v^\iota\to\prod_{w\mid v}K_w$**, $c\mapsto(\sum_ib_i\varphi_w(c_i))_w$. -/
def localPi : (ι → v.adicCompletion k) →ₗ[v.adicCompletion k] PlaceProd (K := K) v where
  toFun c w := localBaseChange b v c w.1
  map_add' c c' := by
    funext w
    show (localBaseChange b v (c + c')) w.1 = (localBaseChange b v c) w.1 + (localBaseChange b v c') w.1
    rw [localBaseChange_add]; rfl
  map_smul' a c := by
    funext w
    show (localBaseChange b v (a • c)) w.1 = (algebraMap _ _ a) * (localBaseChange b v c) w.1
    rw [localBaseChange_apply_over b v w.1 w.2, localBaseChange_apply_over b v w.1 w.2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, algebraMap_instAlgebraPlace]
    ring

theorem localPi_apply (c : ι → v.adicCompletion k) (w : PlaceSet (K := K) v) :
    localPi b v c w = ∑ i, ((b i : K) : w.1.adicCompletion K) * localRingHom v w.1 w.2 (c i) :=
  localBaseChange_apply_over b v w.1 w.2 c

theorem localPi_injective : Function.Injective (localPi b v) := by
  intro c c' h
  apply (isEmbedding_localBaseChange b v).injective
  refine FiniteAdeleRing.ext K fun u => ?_
  by_cases hu : underPlace (k := k) u = v
  · exact congrFun h ⟨u, hu⟩
  · rw [localBaseChange_apply_ne b v u hu, localBaseChange_apply_ne b v u hu]

open Classical in
/-- The adele `z_w` placed at the place `w`, zero elsewhere. -/
def singleAdeleK (w : HeightOneSpectrum (𝓞 K)) : w.adicCompletion K →+ FiniteAdeleRing (𝓞 K) K :=
  RestrictedProduct.singleAddMonoidHom (fun u : HeightOneSpectrum (𝓞 K) => u.adicCompletionIntegers K) w

open Classical in
theorem singleAdeleK_apply_self (w : HeightOneSpectrum (𝓞 K)) (c : w.adicCompletion K) :
    (singleAdeleK w c) w = c := by
  change (Pi.single w c : ∀ u : HeightOneSpectrum (𝓞 K), u.adicCompletion K) w = c
  simp

open Classical in
theorem singleAdeleK_apply_ne {w u : HeightOneSpectrum (𝓞 K)} (h : u ≠ w) (c : w.adicCompletion K) :
    (singleAdeleK w c) u = 0 := by
  change (Pi.single w c : ∀ u : HeightOneSpectrum (𝓞 K), u.adicCompletion K) u = 0
  simp [h]

/-- The adele supported over $v$ with components $z_w$. -/
def supportedAdele (z : PlaceProd (K := K) v) : FiniteAdeleRing (𝓞 K) K :=
  ∑ w : PlaceSet (K := K) v, singleAdeleK w.1 (z w)

open Classical in
theorem supportedAdele_apply (z : PlaceProd (K := K) v) (u : HeightOneSpectrum (𝓞 K)) :
    (supportedAdele v z) u = if h : underPlace (k := k) u = v then z ⟨u, h⟩ else 0 := by
  have hsum : (supportedAdele v z) u = ∑ w : PlaceSet (K := K) v, (singleAdeleK w.1 (z w)) u := by
    unfold supportedAdele
    exact map_sum (evAdele u) (fun w : PlaceSet (K := K) v => singleAdeleK w.1 (z w)) Finset.univ
  rw [hsum]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨u, h⟩]
    · exact singleAdeleK_apply_self u _
    · intro w _ hw
      have : u ≠ w.1 := fun e => hw (Subtype.ext e.symm)
      exact singleAdeleK_apply_ne this _
    · simp
  · refine Finset.sum_eq_zero fun w _ => ?_
    have : u ≠ w.1 := fun e => h (e ▸ w.2)
    exact singleAdeleK_apply_ne this _

theorem localPi_surjective : Function.Surjective (localPi b v) := by
  intro z
  obtain ⟨c, hc⟩ := (mem_range_localBaseChange_iff b v (supportedAdele v z)).mpr fun u hu => by
    simp [supportedAdele_apply, hu]
  refine ⟨c, funext fun w => ?_⟩
  show localBaseChange b v c w.1 = z w
  rw [hc]; simp [supportedAdele_apply, w.2]


/-- **$K\otimes_kk_v\cong\prod_{w\mid v}K_w$ as $k_v$-modules.** -/
@[kb "casselsfrohlich1967" "Ch. II §14 (K ⊗ k_v ≅ ∏_{w|v} K_w) [unverified]; Neukirch II.8.3 [unverified]; FLT `FiniteAdeleRing.baseChangeAlgEquiv` (cited, not imported)"]
def localPiEquiv : (ι → v.adicCompletion k) ≃ₗ[v.adicCompletion k] PlaceProd (K := K) v :=
  LinearEquiv.ofBijective (localPi b v) ⟨localPi_injective b v, localPi_surjective b v⟩

instance instFiniteDimensionalPlace (w : PlaceSet (K := K) v) :
    FiniteDimensional (v.adicCompletion k) (w.1.adicCompletion K) :=
  finiteDimensional_localAlg v ⟨w.1, resChar_eq_of_underPlace v w.1 w.2⟩ w.2

theorem localTrace_eq (w : PlaceSet (K := K) v) (y : w.1.adicCompletion K) :
    localTrace v w.1 w.2 y = Algebra.trace (v.adicCompletion k) (w.1.adicCompletion K) y := rfl

/-- **The trace on $K\otimes_kk_v$ is the sum of the local traces:** for $y\in\prod_{w\mid v}K_w$, the trace of
multiplication by $y$ on $k_v^\iota$ (transported through `localPiEquiv`) is $\sum_{w\mid v}\operatorname{Tr}_{K_w/k_v}(y_w)$. -/
@[kb "casselsfrohlich1967" "Ch. II §14 / Neukirch II.8.3 (Tr_{K/k} = Σ_w Tr_{K_w/k_v}) [unverified]"]
theorem trace_localPi_conj (y : PlaceProd (K := K) v) :
    LinearMap.trace (v.adicCompletion k) (ι → v.adicCompletion k)
        ((localPiEquiv b v).symm.conj (LinearMap.mulLeft (v.adicCompletion k) y)) =
      ∑ w : PlaceSet (K := K) v, localTrace v w.1 w.2 (y w) := by
  classical
  rw [LinearMap.trace_conj']
  change Algebra.trace (v.adicCompletion k) (PlaceProd (K := K) v) y = _
  rw [Algebra.trace_pi' (R := v.adicCompletion k) (A := fun w : PlaceSet (K := K) v => w.1.adicCompletion K) y]
  rfl

variable [DecidableEq ι] in
/-- Multiplication by $x\in K$ is the matrix of `Algebra.leftMulMatrix` in the coordinates of `localPi`. -/
theorem localPi_mulVec (x : K) (c : ι → v.adicCompletion k) :
    localPi b v (((Algebra.leftMulMatrix b x).map (algebraMap k (v.adicCompletion k))).mulVec c) =
      fun w => ((x : K) : w.1.adicCompletion K) * localPi b v c w := by
  funext w
  have hxb : ∀ j, x * b j = ∑ i, algebraMap k K (Algebra.leftMulMatrix b x i j) * b i := by
    intro j
    conv_lhs => rw [← b.sum_repr (x * b j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.smul_def]
  rw [localPi_apply, localPi_apply, Finset.mul_sum]
  simp_rw [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : ((x : K) : w.1.adicCompletion K) * (b j : w.1.adicCompletion K) =
      ∑ i, (algebraMap k K (Algebra.leftMulMatrix b x i j) : w.1.adicCompletion K) * (b i : w.1.adicCompletion K) := by
    have := congrArg (algebraMap K (w.1.adicCompletion K)) (hxb j)
    simp only [map_sum, map_mul] at this
    exact this
  have hφ : ∀ m : k, localRingHom v w.1 w.2 (algebraMap k (v.adicCompletion k) m) =
      ((algebraMap k K m : K) : w.1.adicCompletion K) := fun m => localRingHom_algebraMap v w.1 w.2 m
  rw [← mul_assoc, hj, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hφ]
  ring

/-- **$\operatorname{Tr}_{K/k}=\sum_{w\mid v}\operatorname{Tr}_{K_w/k_v}$ on $K$** (in $k_v$): the trace of the
$k_v$-algebra $K\otimes_kk_v\cong\prod_{w\mid v}K_w$ restricted to $K$. -/
@[kb "casselsfrohlich1967" "Ch. II §14 / Neukirch II.8.3 (Tr_{K/k} x = Σ_{w|v} Tr_{K_w/k_v} x) [unverified]"]
theorem trace_eq_sum_localTrace (x : K) :
    algebraMap k (v.adicCompletion k) (Algebra.trace k K x) =
      ∑ w : PlaceSet (K := K) v, localTrace v w.1 w.2 ((x : K) : w.1.adicCompletion K) := by
  have hconj : (localPiEquiv (Module.finBasis k K) v).symm.conj
      (LinearMap.mulLeft (v.adicCompletion k) (fun w : PlaceSet (K := K) v => ((x : K) : w.1.adicCompletion K))) =
      Matrix.toLin' ((Algebra.leftMulMatrix (Module.finBasis k K) x).map (algebraMap k (v.adicCompletion k))) := by
    refine LinearMap.ext fun c => ?_
    rw [LinearEquiv.conj_apply_apply, Matrix.toLin'_apply, LinearEquiv.symm_symm]
    rw [LinearEquiv.symm_apply_eq]
    have e1 : ∀ c', localPiEquiv (Module.finBasis k K) v c' = localPi (Module.finBasis k K) v c' := fun _ => rfl
    rw [e1, e1]
    rw [LinearMap.mulLeft_apply]
    exact (localPi_mulVec (Module.finBasis k K) v x c).symm
  rw [← trace_localPi_conj (Module.finBasis k K) v, hconj, Matrix.trace_toLin'_eq, Algebra.trace_eq_matrix_trace (Module.finBasis k K),
    AddMonoidHom.map_trace]

/-- **The trace Gram matrix of a $k$-basis is the sum of the local trace forms:**
$\operatorname{Tr}_{K/k}(b_ib_j)=\sum_{w\mid v}\operatorname{Tr}_{K_w/k_v}(b_ib_j)$ in $k_v$. -/
theorem traceMatrix_map_eq_sum (i j : ι) :
    algebraMap k (v.adicCompletion k) (Algebra.traceMatrix k b i j) =
      ∑ w : PlaceSet (K := K) v, localTrace v w.1 w.2 (((b i * b j : K)) : w.1.adicCompletion K) := by
  rw [Algebra.traceMatrix_apply]
  exact trace_eq_sum_localTrace v _

end

end QuadFormsKB.Tamagawa.Measure.Weil
