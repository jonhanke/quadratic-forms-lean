import QuadFormsKB.Tamagawa.Measure.Weil.BaseChangeTraceSum
import QuadFormsKB.Tamagawa.Measure.Weil.BaseChangeTraceLocal

/-!
# Local measure compatibility for the base change
For a basis $b$ of $K/k$ and a finite place $v$ of $k$:

* `localPiCLE b v : k_v^ι ≃L[k_v] ∏_{w∣v} K_w`: the linear bijection `localPiEquiv` is a homeomorphism (a linear map out of
  a finite-dimensional space over the complete nontrivially normed field $k_v$ is continuous, in both directions).
* `placeMeasure v = ⊗_{w∣v} selfDualV w`: the product of the $\psi_{K,w}$-self-dual measures.
* **`map_volVN_localPi`**: $(\Phi_b)_*(dx_v^{\otimes\iota}) = c_v\cdot\text{placeMeasure}$ with a constant
  $c_v=$ `localConst b v` $>0$ (Haar uniqueness; `Measure.addHaarScalarFactor`).

Sources: Haar uniqueness (Mathlib `isAddLeftInvariant_eq_smul`); Cassels–Fröhlich Ch. XV (Tate), §1.3, p. 307 (uniqueness of Haar measure) and §2.2, p. 310 (self-dual measures);
Ch. II (Cassels), §10, (10.2), p. 57;
Weil, *Basic Number Theory*, Ch. II–VII [unverified].
-/

open IsDedekindDomain NumberField Topology Filter MeasureTheory
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  {ι : Type} [Fintype ι] (b : Module.Basis ι k K) (v : HeightOneSpectrum (𝓞 k))

instance instContinuousSMulPlace (w : PlaceSet (K := K) v) :
    ContinuousSMul (v.adicCompletion k) (w.1.adicCompletion K) := by
  refine ⟨?_⟩
  simp_rw [Algebra.smul_def, algebraMap_instAlgebraPlace]
  exact ((continuous_localRingHom v w.1 w.2).comp continuous_fst).mul continuous_snd

/-- **`localPi` is a homeomorphism:** $K\otimes_kk_v\cong\prod_{w\mid v}K_w$ topologically. -/
def localPiCLE : (ι → v.adicCompletion k) ≃L[v.adicCompletion k] PlaceProd (K := K) v :=
  (localPiEquiv b v).toContinuousLinearEquiv

theorem localPiCLE_apply (c : ι → v.adicCompletion k) : localPiCLE b v c = localPi b v c := rfl

/-- The product of the $\psi_{K,w}$-self-dual measures on $\prod_{w\mid v}K_w$. -/
def placeMeasure : Measure (PlaceProd (K := K) v) := Measure.pi fun w => Analysis.selfDualV w.1

instance : (placeMeasure (K := K) v).IsAddHaarMeasure := by
  unfold placeMeasure; infer_instance

/-- **The local constant $c_v$:** the Haar scalar of the coordinate measure pushed to $\prod_{w\mid v}K_w$
relative to the product of the self-dual measures. -/
def localConst : ℝ≥0 := Measure.addHaarScalarFactor ((volVN v).map (localPiCLE b v)) (placeMeasure (K := K) v)

instance : (volVN (ι := ι) v).IsAddHaarMeasure := by
  unfold volVN; infer_instance

instance : ((volVN (ι := ι) v).map (localPiCLE b v)).IsAddHaarMeasure :=
  (localPiCLE b v).isAddHaarMeasure_map _

theorem localConst_pos : 0 < localConst b v :=
  Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _

/-- **Local measure compatibility (Haar form).** The coordinate measure $dx_v^{\otimes\iota}$ on $K\otimes_kk_v=k_v^\iota$,
transported to $\prod_{w\mid v}K_w$ by the base change, is the constant $c_v>0$ times the product of the
$\psi_{K,w}$-self-dual measures. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §1.3, p. 307 (uniqueness of Haar measure); self-dual measures §2.2, p. 310; Weil BNT [unverified]; Mathlib `isAddLeftInvariant_eq_smul`"]
theorem map_volVN_localPi :
    (volVN (ι := ι) v).map (localPiCLE b v) = (localConst b v : ℝ≥0∞) • placeMeasure (K := K) v :=
  Measure.isAddLeftInvariant_eq_smul _ _

/-- **Local degree formula:** $\sum_{w\mid v}[K_w:k_v]=[K:k]$ (from the $k_v$-linear isomorphism `localPiCLE`). -/
@[kb "casselsfrohlich1967" "Ch. II (Cassels), §10, Thm., (10.2), p. 57 (compare k_v-dimensions); Neukirch II.8.3 (Σ_{w|v} [K_w : k_v] = [K : k]) [unverified]"]
theorem sum_finrank_places :
    ∑ w : PlaceSet (K := K) v, Module.finrank (v.adicCompletion k) (w.1.adicCompletion K) = Module.finrank k K := by
  have h1 := (localPiEquiv (Module.finBasis k K) v).finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, Module.finrank_pi_fintype] at h1
  exact h1.symm

/-- **At most $[K:k]$ places over $v$.** -/
theorem card_places_le : Fintype.card (PlaceSet (K := K) v) ≤ Module.finrank k K := by
  rw [← sum_finrank_places v]
  calc Fintype.card (PlaceSet (K := K) v) = ∑ _w : PlaceSet (K := K) v, 1 := by simp
    _ ≤ _ := Finset.sum_le_sum fun w _ => Module.finrank_pos

/-- **At most two places in the quadratic case** (three pairwise orthogonal idempotents cannot live in a
2-dimensional algebra; here via $\sum_{w\mid v}[K_w:k_v]=2$ and $[K_w:k_v]\ge1$). -/
@[kb "casselsfrohlich1967" "Ch. II (Cassels), §10, Thm., p. 57 (at most N = [K : k] extensions); Neukirch II.8.3 (a quadratic extension has at most two places over v) [unverified]"]
theorem card_places_le_two (hK : Module.finrank k K = 2) : Fintype.card (PlaceSet (K := K) v) ≤ 2 := by
  have := card_places_le (K := K) v
  omega

/-- **Split case: exactly two places** ($K=k(\delta)$, $\delta^2=d$, $d=c^2$ with $c\ne0$ in $k_v$). -/
theorem card_places_eq_two_of_sq {d : k} {b : Module.Basis (Fin 2) k K} (hb0 : b 0 = 1)
    (hb1 : b 1 * b 1 = algebraMap k K d) (c : v.adicCompletion k) (hc : c ≠ 0)
    (hd : (d : v.adicCompletion k) = c * c) : Fintype.card (PlaceSet (K := K) v) = 2 := by
  have hK : Module.finrank k K = 2 := by rw [Module.finrank_eq_card_basis b]; simp
  refine le_antisymm (card_places_le_two v hK) ?_
  obtain ⟨w₁, w₂, hne, h₁, h₂⟩ := exists_two_places_of_sq hb0 hb1 v c hc hd
  classical
  have : ({⟨w₁, h₁⟩, ⟨w₂, h₂⟩} : Finset (PlaceSet (K := K) v)).card = 2 := by
    rw [Finset.card_pair]
    intro h
    exact hne (congrArg Subtype.val h)
  rw [← this]
  exact Finset.card_le_univ _

end

end QuadFormsKB.Tamagawa.Measure.Weil
