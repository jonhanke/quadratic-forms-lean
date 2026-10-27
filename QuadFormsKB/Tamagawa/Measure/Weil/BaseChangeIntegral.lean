import QuadFormsKB.Tamagawa.Measure.Weil.BaseChangeLocalMeasure

/-!
# The integral statement $\mathcal O_K\otimes\mathcal O_v\cong\prod_{w\mid v}\mathcal O_{K,w}$
Let $b$ be a $k$-basis of $K$ consisting of algebraic integers and $v$ a place of $k$ at which the basis discriminant is a
unit ($v(\operatorname{disc}b)=1$). Then `localPi b v` carries $\mathcal O_v^\iota$ **onto** $\prod_{w\mid v}\mathcal O_w$
(`localPi_image_integers`). For such $v$ the order $\bigoplus\mathcal O_kb_i$ is maximal at $v$.

Proof. ($\subseteq$) $\varphi_w(\mathcal O_v)\subseteq\mathcal O_w$ since $\mathcal O_k$ is dense in $\mathcal O_v$, $\varphi_w$ is
continuous and $\mathcal O_w$ is closed. ($\supseteq$) For $a\in\mathcal O_K$ the coordinates $r=G^{-1}(\operatorname{Tr}(b_ja))_j$
lie in $\mathcal O_v$ because $G=(\operatorname{Tr}(b_ib_j))$ has integral entries and unit determinant at $v$; the image of
$\mathcal O_K$ is dense in $\prod_{w\mid v}\mathcal O_w$ (Chinese remainder theorem, `exists_int_approx_Sp`), and
$\Phi(\mathcal O_v^\iota)$ is closed.

Sources: Neukirch, *Algebraic Number Theory*, Ch. III Prop. 2.12 and Ch. II Prop. 8.3 [unverified]; Serre, *Local Fields*,
Ch. III §5 [unverified]; Mathlib `Algebra.isIntegral_trace`, `Matrix.adjugate_mul`, `Valued.isClosed_valuationSubring`.
-/

open IsDedekindDomain NumberField Topology Filter MeasureTheory QuadFormsKB
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  {ι : Type} [Fintype ι] (b : Module.Basis ι k K) (v : HeightOneSpectrum (𝓞 k))

/-- $\varphi_w(\mathcal O_v)\subseteq\mathcal O_w$ for $w\mid v$. -/
theorem localRingHom_valued_le_one (w : HeightOneSpectrum (𝓞 K)) (h : underPlace (k := k) w = v)
    (c : v.adicCompletion k) (hc : Valued.v c ≤ 1) : Valued.v (localRingHom v w h c) ≤ 1 := by
  have hmem : c ∈ closure (Set.range fun a : 𝓞 k => algebraMap k (v.adicCompletion k) (a : k)) := by
    rw [mem_closure_iff_nhds]
    intro t ht
    obtain ⟨N, hN⟩ := Analysis.exists_N_of_mem_nhds v ht
    obtain ⟨a, ha⟩ := Analysis.exists_int_approx_pow v N c hc
    exact ⟨_, hN _ (by rw [← Valuation.map_neg, neg_sub] at ha; simpa using ha), a, rfl⟩
  have hcl : IsClosed {y : w.adicCompletion K | Valued.v y ≤ 1} := by
    have := Valued.isClosed_valuationSubring (w.adicCompletion K)
    exact this
  have := map_mem_closure (continuous_localRingHom v w h) hmem (t := {y : w.adicCompletion K | Valued.v y ≤ 1}) ?_
  · rwa [hcl.closure_eq] at this
  · rintro _ ⟨a, rfl⟩
    show Valued.v (localRingHom v w h (algebraMap k (v.adicCompletion k) (a : k))) ≤ 1
    have e : localRingHom v w h (algebraMap k (v.adicCompletion k) (a : k)) =
        algebraMap K (w.adicCompletion K) (algebraMap k K (a : k)) :=
      localRingHom_algebraMap v w h (a : k)
    rw [e, HN.valued_algebraMap]
    have : algebraMap k K (a : k) = ((algebraMap (𝓞 k) (𝓞 K) a : 𝓞 K) : K) := rfl
    rw [this]
    exact w.valuation_le_one _

/-- $\mathcal O_v^\iota\subseteq k_v^\iota$. -/
def intLat : Set (ι → v.adicCompletion k) := {c | ∀ i, Valued.v (c i) ≤ 1}

/-- $\prod_{w\mid v}\mathcal O_w\subseteq\prod_{w\mid v}K_w$. -/
def intPlace : Set (PlaceProd (K := K) v) := {z | ∀ w, Valued.v (z w) ≤ 1}

theorem isClosed_intLat : IsClosed (intLat (ι := ι) (k := k) v) := by
  have : intLat (ι := ι) (k := k) v = ⋂ i, (fun c : ι → v.adicCompletion k => c i) ⁻¹' {y | Valued.v y ≤ 1} := by
    ext c; simp [intLat]
  rw [this]
  refine isClosed_iInter fun i => (?_ : IsClosed {y : v.adicCompletion k | Valued.v y ≤ 1}).preimage (continuous_apply i)
  have := Valued.isClosed_valuationSubring (v.adicCompletion k)
  exact this

theorem valued_basis_le_one (hb : ∀ i, IsIntegral ℤ (b i)) (w : HeightOneSpectrum (𝓞 K)) (i : ι) :
    Valued.v ((b i : K) : w.adicCompletion K) ≤ 1 := by
  obtain ⟨x, hx⟩ := (IsIntegralClosure.isIntegral_iff (R := ℤ) (B := K) (A := 𝓞 K)).mp (hb i)
  show Valued.v (algebraMap K (w.adicCompletion K) (b i)) ≤ 1
  rw [HN.valued_algebraMap, ← hx]
  exact w.valuation_le_one x

theorem localPi_mem_intPlace (hb : ∀ i, IsIntegral ℤ (b i)) {c : ι → v.adicCompletion k} (hc : c ∈ intLat v) :
    localPi b v c ∈ intPlace (K := K) v := by
  intro w
  rw [localPi_apply]
  refine Valuation.map_sum_le _ fun i _ => ?_
  rw [map_mul]
  calc _ ≤ 1 * 1 := mul_le_mul' (valued_basis_le_one b hb w.1 i)
        (localRingHom_valued_le_one v w.1 w.2 _ (hc i))
    _ = 1 := one_mul 1

/-- Cramer: if $G$ has $v$-integral entries and unit determinant, $Gr=t$ with $t$ integral forces $r$ integral. -/
theorem val_le_one_of_mulVec_eq [DecidableEq ι] (G : Matrix ι ι k) (hG : ∀ i j, v.valuation k (G i j) ≤ 1)
    (hdet : v.valuation k G.det = 1) (t r : ι → k) (ht : ∀ j, v.valuation k (t j) ≤ 1)
    (hr : G.mulVec r = t) (i : ι) : v.valuation k (r i) ≤ 1 := by
  let R := (v.valuation k).valuationSubring
  let G' : Matrix ι ι R := Matrix.of fun i j => ⟨G i j, (Valuation.mem_valuationSubring_iff _ _).mpr (hG i j)⟩
  have hGG : G'.map R.subtype = G := by ext i j; rfl
  have hadj : ∀ i j, v.valuation k (G.adjugate i j) ≤ 1 := by
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
  have h1 : v.valuation k (G.det * r i) ≤ 1 := by
    have := congrFun key i
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct] at this
    rw [this]
    refine Valuation.map_sum_le _ fun j _ => ?_
    rw [map_mul]
    exact mul_le_one' (hadj i j) (ht j)
  rwa [map_mul, hdet, one_mul] at h1

theorem valuation_trace_le_one (x : K) (hx : IsIntegral ℤ x) : v.valuation k (Algebra.trace k K x) ≤ 1 := by
  have h1 : IsIntegral (𝓞 k) x := hx.tower_top
  have h2 : IsIntegral (𝓞 k) (Algebra.trace k K x) := Algebra.isIntegral_trace h1
  have h3 : IsIntegral ℤ (Algebra.trace k K x) := by
    exact isIntegral_trans (R := ℤ) (A := 𝓞 k) _ h2
  obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (R := ℤ) (B := k) (A := 𝓞 k)).mp h3
  rw [← hy]
  exact v.valuation_le_one y

variable [DecidableEq ι] in
/-- **Integers have $v$-integral coordinates** when the basis is integral with unit discriminant at $v$. -/
theorem exists_mem_intLat_of_integer (hb : ∀ i, IsIntegral ℤ (b i)) (hd : v.valuation k (Algebra.discr k b) = 1)
    (a : 𝓞 K) :
    ∃ c ∈ intLat (ι := ι) v, ∀ w : PlaceSet (K := K) v, localPi b v c w = ((a : K) : w.1.adicCompletion K) := by
  have hint : ∀ i j, IsIntegral ℤ (b i * b j) := fun i j => (hb i).mul (hb j)
  refine ⟨fun i => algebraMap k (v.adicCompletion k) (b.repr (a : K) i), ?_, ?_⟩
  · intro i
    rw [HN.valued_algebraMap]
    refine val_le_one_of_mulVec_eq v (Algebra.traceMatrix k b) (fun i j => ?_) ?_
      (fun j => Algebra.trace k K (b j * a)) (fun i => b.repr (a : K) i) ?_ ?_ i
    · rw [Algebra.traceMatrix_apply]; exact valuation_trace_le_one v _ (hint i j)
    · rw [← Algebra.discr_def]; exact hd
    · intro j
      exact valuation_trace_le_one v _ ((hb j).mul a.isIntegral_coe)
    · funext j
      simp only [Matrix.mulVec, dotProduct, Algebra.traceMatrix_apply]
      conv_rhs => rw [← b.sum_repr (a : K)]
      rw [Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
      rfl
  · intro w
    rw [localPi_apply]
    have h1 := congrArg (algebraMap K (w.1.adicCompletion K)) (b.sum_repr (a : K))
    simp only [map_sum, Algebra.smul_def, map_mul] at h1
    refine Eq.trans ?_ h1
    refine Finset.sum_congr rfl fun i _ => ?_
    have hφ : localRingHom v w.1 w.2 (algebraMap k (v.adicCompletion k) (b.repr (a : K) i)) =
        algebraMap K (w.1.adicCompletion K) (algebraMap k K (b.repr (a : K) i)) :=
      localRingHom_algebraMap v w.1 w.2 _
    rw [hφ]
    exact mul_comm _ _

/-- The diagonal image of $K$ in $\prod_{w\mid v}K_w$. -/
def diagPlace (x : K) : PlaceProd (K := K) v := fun w => ((x : K) : w.1.adicCompletion K)

open Classical in
/-- **Integers are dense in $\prod_{w\mid v}\mathcal O_w$** (Chinese remainder / weak approximation). -/
theorem intPlace_subset_closure : intPlace (K := K) v ⊆ closure (Set.range fun a : 𝓞 K => diagPlace v (a : K)) := by
  intro z hz
  rw [mem_closure_iff_nhds]
  intro t ht
  obtain ⟨u, hut, hu, hzu⟩ := mem_nhds_iff.mp ht
  obtain ⟨I, U, hU, hIU⟩ := isOpen_pi_iff.mp hu z hzu
  have hN : ∀ w : PlaceSet (K := K) v, ∃ N : ℕ, ∀ x : w.1.adicCompletion K,
      Valued.v (x - z w) ≤ WithZero.exp (-(N : ℤ)) → w ∈ I → x ∈ U w := by
    intro w
    by_cases hw : w ∈ I
    · obtain ⟨N, hN⟩ := Analysis.exists_N_of_mem_nhds w.1 ((hU w hw).1.mem_nhds (hU w hw).2)
      exact ⟨N, fun x hx _ => hN x hx⟩
    · exact ⟨0, fun x _ h => absurd h hw⟩
  choose N hN using hN
  let N0 : ℕ := Finset.univ.sup N
  let q := Analysis.resChar v
  let y : ∀ w : Analysis.Sp K q, w.1.adicCompletion K := fun w =>
    if h : underPlace (k := k) w.1 = v then z ⟨w.1, h⟩ else 0
  have hy : ∀ w, Valued.v (y w) ≤ 1 := by
    intro w
    by_cases h : underPlace (k := k) w.1 = v
    · simp only [y, dif_pos h]; exact hz ⟨w.1, h⟩
    · simp only [y, dif_neg h, map_zero]; exact bot_le
  obtain ⟨a, ha⟩ := Analysis.exists_int_approx_Sp (F := K) q y hy N0
  refine ⟨diagPlace v (a : K), hut ?_, a, rfl⟩
  refine hIU fun w hw => ?_
  refine hN w _ ?_ hw
  have h1 := ha (toSp v w.1 w.2)
  have hyw : y (toSp v w.1 w.2) = z w := by simp [y, toSp, w.2]
  rw [hyw] at h1
  have h2 : Valued.v (diagPlace v (a : K) w - z w) ≤ WithZero.exp (-(N0 : ℤ)) := by
    rw [← Valuation.map_neg, neg_sub]; exact h1
  refine h2.trans (WithZero.exp_le_exp.mpr ?_)
  have : N w ≤ N0 := Finset.le_sup (f := N) (Finset.mem_univ w)
  omega

variable [DecidableEq ι] in
/-- **$\mathcal O_K\otimes\mathcal O_v\cong\prod_{w\mid v}\mathcal O_{K,w}$ at the good places** (integral statement):
if $b$ is a $k$-basis of $K$ of algebraic integers and $v(\operatorname{disc}b)=1$, the isomorphism
$K\otimes_kk_v\cong\prod_{w\mid v}K_w$ maps $\bigoplus_i\mathcal O_vb_i$ onto $\prod_{w\mid v}\mathcal O_w$. This holds for
all but finitely many $v$ (the primes dividing $\operatorname{disc}b\ne0$). -/
@[kb "casselsfrohlich1967" "Ch. II (Cassels), §12, Lemma, (12.1), p. 61 (proof pp. 61–62); Neukirch III.2.12, II.8.3 (O_K ⊗ O_v ≅ ∏ O_w away from the discriminant) [unverified]"]
theorem localPi_image_integers (hb : ∀ i, IsIntegral ℤ (b i)) (hd : v.valuation k (Algebra.discr k b) = 1) :
    localPi b v '' intLat v = intPlace (K := K) v := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨c, hc, rfl⟩
    exact localPi_mem_intPlace b v hb hc
  · intro z hz
    have hcl : IsClosed (localPi b v '' intLat (ι := ι) v) :=
      (localPiCLE b v).toHomeomorph.isClosedMap _ (isClosed_intLat v)
    refine (closure_minimal ?_ hcl) (intPlace_subset_closure v hz)
    rintro _ ⟨a, rfl⟩
    obtain ⟨c, hc, hca⟩ := exists_mem_intLat_of_integer b v hb hd a
    exact ⟨c, hc, funext hca⟩

end

end QuadFormsKB.Tamagawa.Measure.Weil
