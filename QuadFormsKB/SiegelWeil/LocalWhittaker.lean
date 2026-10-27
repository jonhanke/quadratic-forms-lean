/-
# Local Whittaker integrals are local densities

**Layer:** local, non-archimedean. Every finite place $v$ of a number field $F$, **dyadic places included**.

**Setting.** $V_v = \langle a_0, \dots, a_{2m-1}\rangle$ over $F_v$, $a_i \in \mathcal O_v\setminus\{0\}$, $n = 2m$ (0-based indices);
$L_v = \mathcal O_v^{n}$ and $\varphi_v = \mathbf 1_{L_v}$ (`oneS`); $f_v(g) = (\omega_v(g)\varphi_v)(0)$ the section of
`SiegelWeil/Sections.lean` for the local Weil representation `weilRepV`. Measures: the self-dual measure $db$ on $F_v$
for $\psi_v$ (`selfDualV`, $\operatorname{vol}(\mathcal O_v) = N(\mathfrak d_v)^{-1/2}$), and $dx = \prod_i dx_i$ on $V_v$ (`muN`).
$\mathfrak d_v = \mathfrak p_v^{d_v}$ is the local different (`diffExp`), $q = N\mathfrak p_v$.

**The local Whittaker integral** $W_v(t) = \int_{F_v}f_v(wn(b))\psi_v(-tb)\,db$ is taken as the limit of the integrals over
$\mathfrak p_v^{-k}$ (`whittakerTr`, `whittakerV`): this is the classical definition (Siegel's "singular series" at $v$;
Kudla, Yang), and the limit is in fact attained: the truncated integrals are *eventually constant* (`whittakerTr_eventually_eq`).
When $b \mapsto f_v(wn(b))\psi_v(-tb)$ is integrable the limit is the Lebesgue integral (`whittakerV_eq_integral`).

**Results.**
* `muN_congSet` (**the volume of a congruence set**): for $j \ge 0$, $t \in \mathcal O_v$,
  $$\operatorname{vol}\{x \in L_v : Q(x) \equiv t \bmod \mathfrak p_v^j\} = r_{\mathfrak p^j}(t)\,\operatorname{vol}(\mathfrak p_v^j)^{n},$$
  $r_{\mathfrak p^j}(t) = \#\{x \in (\mathcal O_v/\mathfrak p_v^j)^n : Q(x) \equiv t\}$ the repo's count `DVR.repCount`.
* `whittakerTr_eq` (**the heart**): for every $k \ge d_v$ and $t \in \mathcal O_v$ (also $t = 0$), with $j = k - d_v$,
  $$\int_{\mathfrak p_v^{-k}}f_v(wn(b))\psi_v(-tb)\,db
    = \gamma_V\,c_B\,\operatorname{vol}(\mathcal O_v)^{n-1}\,\frac{r_{\mathfrak p^{j}}(t)}{q^{j(n-1)}},\qquad
    c_B = \prod_{i<n}|2a_i|_v^{1/2},\ \operatorname{vol}(\mathcal O_v) = N(\mathfrak d_v)^{-1/2}.$$
  *Proof* (Siegel; Weil 1965): $f_v(wn(b)) = \gamma_Vc_B\int_{L_v}\psi_v(bQ(x))\,dx$ (`sec_wMat_nMat`); Fubini; the
  $b$-integral $\int_{\mathfrak p^{-k}}\psi_v(b(Q(x) - t))\,db = \operatorname{vol}(\mathfrak p^{-k})\mathbf 1[Q(x) - t \in \mathfrak p^{k - d_v}]$
  (`fourierV_ballIndV`: the annihilator of $\mathfrak p^{-k}$ is $\mathfrak p^{k}\mathfrak d_v^{-1}{}^{\perp} = \mathfrak p^{k-d_v}$); then `muN_congSet`;
  the powers of $q$ combine to $\operatorname{vol}(\mathcal O_v)^{n-1}$.
* **`whittakerV_eq_localDensity`** (**Whittaker = local density**, every finite place, dyadic included): for
  $t \in \mathcal O_v\setminus\{0\}$,
  $$W_v(f_{\mathbf 1_{L_v}}, t) = \gamma_V\cdot\prod_{i<n}|2a_i|_v^{1/2}\cdot N(\mathfrak d_v)^{-(n-1)/2}\cdot\beta_v(t),$$
  $\beta_v(t) = \lim_j r_{\mathfrak p^j}(t)/q^{j(n-1)}$ the repo's local density (`DVR.localDensity`, Hanke (5.1)–(5.2)).
  Over $\mathcal O_F$: `whittakerV_eq_NF_localDensity` with `NF.localDensity` of the form $\sum_ib_ix_i^2$, $b_i \in \mathcal O_F$.
  Equivalently, $\gamma_V\,\operatorname{vol}_{\mu_B}(L_v)\operatorname{vol}(\mathcal O_v)^{-1}\beta_v(t)$, $\mu_B$ the measure self-dual for $\psi_v(B(x,y))$.
* `whittakerV_eq_zero_of_not_int`: $W_v(t) = 0$ for $t \notin \mathcal O_v$; `whittakerTr_zero_eq` (the constant term,
  $t = 0$): the same formula with $r_{\mathfrak p^j}(0)$, for every $k \ge d_v$.

*Constants.* $\gamma_V = \chi_V(-1)\prod_ig_v(a_i)^{-1} = \prod_ig_v(a_i)$ is the Weil index (`gammaV`, `gammaV_eq_prod_gN`);
$c_B$ is `cB`; at a place with $d_v = 0$, $v \nmid 2$ and all $a_i$ units, $\gamma_V = 1$ and $c_B = 1$, so $W_v(t) = \beta_v(t)$.

Sources: Siegel, Ann. Math. 36 (1935) (the densities as Gauss-sum limits) [unverified]; Weil, *Sur la formule de
Siegel dans la théorie des groupes classiques*, Acta Math. 113 (1965), Ch. II and §§ 36–41 [unverified]; Kudla, *Some
extensions of the Siegel–Weil formula* (2008), §1 [unverified]; Yang, *An explicit formula for local densities of
quadratic forms*, J. Number Theory 72 (1998), §1 [unverified].
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.SiegelWeil.Sections
import QuadFormsKB.LocalDensity.NFLocal
import QuadFormsKB.LocalDensity.DVRTable2

open IsDedekindDomain NumberField MeasureTheory WithZero Filter Topology
open QuadFormsKB.Analysis QuadFormsKB.WeilRep QuadFormsKB.WeilRep.LocalData
open scoped MatrixGroups

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

variable {m : ℕ} (a : Fin (2 * m) → (v.adicCompletion F)ˣ)

/-! ### The integral form and the congruence sets -/

/-- The coefficients $a_i$ as elements of $\mathcal O_v$ (when $|a_i|_v \le 1$). -/
def aO (ha : ∀ i, Valued.v (a i : Fv) ≤ 1) : Fin (2 * m) → 𝔬 :=
  fun i => ⟨a i, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (ha i)⟩

/-- **The lattice form** $Q = \sum_ia_ix_i^2$ on $L_v = \mathcal O_v^{2m}$, as a `QuadForm` over the DVR $\mathcal O_v$. -/
def QO (ha : ∀ i, Valued.v (a i : Fv) ≤ 1) : QuadForm 𝔬 (2 * m) := QuadForm.diag (aO v a ha)

/-- **The congruence set** $\{x \in L_v : Q(x) \equiv t \bmod \mathfrak p_v^j\}$, $L_v = \mathcal O_v^{2m}$. -/
def congSet (t : Fv) (j : ℕ) : Set (Fin (2 * m) → Fv) :=
  {x | (∀ i, Valued.v (x i) ≤ 1) ∧ Valued.v (Qform a x - t) ≤ exp (-(j : ℤ))}

lemma valued_Qform_le_one (ha : ∀ i, Valued.v (a i : Fv) ≤ 1) (x : Fin (2 * m) → Fv) (hx : ∀ i, Valued.v (x i) ≤ 1) :
    Valued.v (Qform a x) ≤ 1 := by
  unfold Qform
  refine Valuation.map_sum_le _ fun i _ => ?_
  rw [map_mul, map_pow]
  exact mul_le_one' (ha i) (pow_le_one' (hx i) _)

/-- $Q(x) \in \mathcal O_v$ for $x \in L_v$. -/
def QformO (ha : ∀ i, Valued.v (a i : Fv) ≤ 1) (x : Fin (2 * m) → Fv) (hx : ∀ i, Valued.v (x i) ≤ 1) : 𝔬 :=
  ⟨Qform a x, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (valued_Qform_le_one v a ha x hx)⟩

section Count

variable (ha : ∀ i, Valued.v (a i : v.adicCompletion F) ≤ 1) (j : ℕ)

/-- The residue ring $\mathcal O_v/\mathfrak p_v^j$ (uniformizer `NF.π v`). -/
abbrev RQ (j : ℕ) : Type := 𝔬 ⧸ Ideal.span {LocalDensity.NF.π v ^ j}

lemma valued_sub_le_iff_mk_eq (x y : 𝔬) :
    Ideal.Quotient.mk (Ideal.span {LocalDensity.NF.π v ^ j}) x = Ideal.Quotient.mk _ y ↔
      Valued.v ((x : Fv) - (y : Fv)) ≤ exp (-(j : ℤ)) := by
  rw [Ideal.Quotient.eq, LocalDensity.NF.mem_span_π_pow]
  rfl

/-- The lift of a residue vector to $L_v$ (by `Quotient.out`). -/
def liftR (y : Fin (2 * m) → (RQ v j)) : Fin (2 * m) → Fv := fun i => ((Quotient.out (y i) : 𝔬) : Fv)

/-- The fiber of the reduction map over a residue vector $y$: the coset $\tilde y + (\mathfrak p_v^j)^{2m}$. -/
def fiberR (y : Fin (2 * m) → (RQ v j)) : Set (Fin (2 * m) → Fv) :=
  Set.univ.pi fun i => {z : Fv | Valued.v (z - liftR v j y i) ≤ exp (-(j : ℤ))}

lemma valued_le_one_of_mem_fiberR {y : Fin (2 * m) → (RQ v j)} {x : Fin (2 * m) → Fv} (hx : x ∈ fiberR v j y) (i : Fin (2 * m)) :
    Valued.v (x i) ≤ 1 := by
  have h1 : Valued.v (x i - liftR v j y i) ≤ 1 :=
    (hx i (Set.mem_univ _)).trans (by rw [← exp_zero, exp_le_exp]; omega)
  have h2 : Valued.v (liftR v j y i) ≤ 1 := (Quotient.out (y i)).2
  calc Valued.v (x i) = Valued.v ((x i - liftR v j y i) + liftR v j y i) := by ring_nf
    _ ≤ max _ _ := Valuation.map_add _ _ _
    _ ≤ 1 := max_le h1 h2

/-- The reduction $L_v \to (\mathcal O_v/\mathfrak p_v^j)^{2m}$. -/
def redR (x : Fin (2 * m) → Fv) (hx : ∀ i, Valued.v (x i) ≤ 1) : Fin (2 * m) → (RQ v j) :=
  fun i => Ideal.Quotient.mk _ ⟨x i, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (hx i)⟩

lemma mem_fiberR_iff {y : Fin (2 * m) → (RQ v j)} {x : Fin (2 * m) → Fv} :
    x ∈ fiberR v j y ↔ ∃ hx : ∀ i, Valued.v (x i) ≤ 1, redR v j x hx = y := by
  constructor
  · intro h
    refine ⟨valued_le_one_of_mem_fiberR v j h, funext fun i => ?_⟩
    have := h i (Set.mem_univ _)
    rw [redR, ← Ideal.Quotient.mk_out (y i), valued_sub_le_iff_mk_eq]
    exact this
  · rintro ⟨hx, rfl⟩ i -
    show Valued.v (x i - ((Quotient.out (redR v j x hx i) : 𝔬) : Fv)) ≤ _
    have := (valued_sub_le_iff_mk_eq v j ⟨x i, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (hx i)⟩
      (Quotient.out (redR v j x hx i))).mp (by rw [Ideal.Quotient.mk_out]; rfl)
    exact this

lemma evalIn_redR (x : Fin (2 * m) → Fv) (hx : ∀ i, Valued.v (x i) ≤ 1) :
    (QO v a ha).evalIn (RQ v j) (redR v j x hx) = Ideal.Quotient.mk _ (QformO v a ha x hx) := by
  rw [QO, LocalDensity.DVR.evalIn_diag]
  simp only [redR, Ideal.Quotient.algebraMap_eq, ← map_pow, ← map_mul, ← map_sum]
  congr 1
  apply Subtype.ext
  simp [Qform, aO, QformO]

lemma congSet_eq_biUnion (t : 𝔬) [Fintype (RQ v j)] [DecidableEq (RQ v j)] :
    congSet v a (t : Fv) j = ⋃ y ∈ (Finset.univ.filter fun y : Fin (2 * m) → (RQ v j) =>
      (QO v a ha).evalIn (RQ v j) y = Ideal.Quotient.mk _ t), fiberR v j y := by
  ext x
  simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and, exists_prop]
  constructor
  · rintro ⟨hx, hQ⟩
    refine ⟨redR v j x hx, ?_, (mem_fiberR_iff v j).mpr ⟨hx, rfl⟩⟩
    rw [evalIn_redR v a ha j x hx, valued_sub_le_iff_mk_eq]
    exact hQ
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨hx, rfl⟩ := (mem_fiberR_iff v j).mp hxy
    refine ⟨hx, ?_⟩
    rw [evalIn_redR v a ha j x hx, valued_sub_le_iff_mk_eq] at hy
    exact hy

lemma measurableSet_fiberR (y : Fin (2 * m) → (RQ v j)) : MeasurableSet (fiberR v j y) := by
  refine MeasurableSet.univ_pi fun i => ?_
  have : {z : Fv | Valued.v (z - liftR v j y i) ≤ exp (-(j : ℤ))} =
      (fun z => z + -liftR v j y i) ⁻¹' (latticeV v j : Set Fv) := by
    ext z; simp [mem_latticeV, sub_eq_add_neg]
  rw [this]
  exact (measurableSet_latticeV v j).preimage (measurable_add_const _)

lemma measure_fiberR (y : Fin (2 * m) → (RQ v j)) :
    (localDataV v).muN (2 * m) (fiberR v j y) = selfDualV v (latticeV v j) ^ (2 * m) := by
  have : SigmaFinite (localDataV v).μ := (isOps_V v).sigmaFinite
  rw [muN, fiberR, Measure.pi_pi]
  have : ∀ i, (localDataV v).μ {z : Fv | Valued.v (z - liftR v j y i) ≤ exp (-(j : ℤ))} =
      selfDualV v (latticeV v j) := by
    intro i
    have e : {z : Fv | Valued.v (z - liftR v j y i) ≤ exp (-(j : ℤ))} =
        (fun z => z + -liftR v j y i) ⁻¹' (latticeV v j : Set Fv) := by
      ext z; simp [mem_latticeV, sub_eq_add_neg]
    rw [e]
    exact measure_preimage_add_right (selfDualV v) _ _
  simp only [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma fiberR_disjoint {y y' : Fin (2 * m) → (RQ v j)} (h : y ≠ y') : Disjoint (fiberR v j y) (fiberR v j y') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨h1, rfl⟩ := (mem_fiberR_iff v j).mp hx
  obtain ⟨h2, e⟩ := (mem_fiberR_iff v j).mp hx'
  exact h e

/-- **The volume of a congruence set** (every finite place, dyadic included): for $j \ge 0$ and $t \in \mathcal O_v$,
$$\operatorname{vol}\{x \in \mathcal O_v^{2m} : Q(x) \equiv t \bmod \mathfrak p_v^j\} = r_{\mathfrak p^j}(t)\cdot\operatorname{vol}(\mathfrak p_v^j)^{2m},$$
with $r_{\mathfrak p^j}(t)$ = `DVR.repCount` of $Q = \sum_ia_ix_i^2$ over $\mathcal O_v$ and the uniformizer `NF.π v`. *Proof:* the
set is the disjoint union of the cosets $\tilde y + (\mathfrak p_v^j)^{2m}$ over the solutions $y$ mod $\mathfrak p_v^j$;
each has volume $\operatorname{vol}(\mathfrak p_v^j)^{2m}$ by translation invariance. -/
@[kb "siegel1935" "§1 (densities as limits of volumes of congruence sets) [unverified]"]
theorem muN_congSet (t : 𝔬) :
    ((localDataV v).muN (2 * m)).real (congSet v a (t : Fv) j) =
      (LocalDensity.DVR.repCount (QO v a ha) (LocalDensity.NF.π v) j t : ℝ) *
        (selfDualV v).real (latticeV v j) ^ (2 * m) := by
  classical
  have := LocalDensity.DVR.finite_quot_pow (LocalDensity.NF.π v) (LocalDensity.NF.irreducible_π v) j
  haveI : Fintype (RQ v j) := Fintype.ofFinite _
  rw [congSet_eq_biUnion v a ha j t, Measure.real, measure_biUnion_finset]
  · simp only [measure_fiberR, Finset.sum_const, nsmul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_natCast, Measure.real]
    congr 1
    rw [LocalDensity.DVR.repCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  · intro y _ y' _ h
    exact fiberR_disjoint v j h
  · intro y _; exact measurableSet_fiberR v j y

omit ha in
lemma measurableSet_congSet (ha : ∀ i, Valued.v (a i : v.adicCompletion F) ≤ 1) (t : 𝔬) : MeasurableSet (congSet v a (t : Fv) j) := by
  classical
  have := LocalDensity.DVR.finite_quot_pow (LocalDensity.NF.π v) (LocalDensity.NF.irreducible_π v) j
  have : Fintype (RQ v j) := Fintype.ofFinite _
  rw [congSet_eq_biUnion v a ha j t]
  exact Finset.measurableSet_biUnion _ fun y _ => measurableSet_fiberR v j y

end Count

/-! ### The truncated Whittaker integral -/

/-- **The function $b \mapsto f_v(wn(b))$** for the lattice section $f_v = f_{\mathbf 1_{L_v}}$:
$f_v(wn(b)) = \gamma_V\,c_B\int_{L_v}\psi_v(bQ(x))\,dx$ (`wfun_eq`). -/
def wfun (b : Fv) : ℂ := secV v a (oneS v m) (wMat * nMat b)

/-- **The truncated local Whittaker integral** $\int_{\mathfrak p_v^{-k}}f_v(wn(b))\,\psi_v(-tb)\,db$ (self-dual $db$), written
with the indicator $\mathbf 1_{\mathfrak p_v^{-k}}$ = `ballIndV v 0 (-k)`. -/
@[kb "weil1965" "Ch. II (the local factors of the Fourier coefficients of the Eisenstein series) [unverified]"]
def whittakerTr (t : Fv) (k : ℕ) : ℂ :=
  ∫ b, ballIndV v 0 (-(k : ℤ)) b * (wfun v a b * (psiV v (-(t * b)) : ℂ)) ∂selfDualV v

/-- **The local Whittaker integral** $W_v(f_{\mathbf 1_{L_v}}, t) = \int_{F_v}f_v(wn(b))\psi_v(-tb)\,db
= \lim_{k\to\infty}\int_{\mathfrak p_v^{-k}}f_v(wn(b))\psi_v(-tb)\,db$ (`limUnder`; the limit is attained,
`whittakerTr_eventually_eq`). -/
@[kb "weil1965" "Ch. II [unverified]; Kudla (2008), §1 ($W_{T,v}(e, s_0, \\Phi_v)$) [unverified]"]
def whittakerV (t : Fv) : ℂ := limUnder atTop (whittakerTr v a t)

lemma wfun_eq (b : Fv) : wfun v a b = (localDataV v).gammaV a * (localDataV v).cB a *
    ∫ x, (psiV v (b * Qform a x) : ℂ) * oneV v (2 * m) x ∂(localDataV v).muN (2 * m) := by
  unfold wfun secV
  rw [sec_wMat_nMat]
  rfl

lemma continuous_oneV : Continuous (oneV v (2 * m)) := by
  unfold oneV ptensor
  exact continuous_finsetProd _ fun i _ =>
    (continuous_of_mem_SBK (ballIndV_zero_mem_SBK v)).comp (continuous_apply i)

lemma continuous_ballIndV_zero (k : ℤ) : Continuous (ballIndV v 0 k) := by
  have : ballIndV v 0 k ∈ SBK Fv := by
    have e : ballIndV v 0 k = (Metric.closedBall (0 : Fv) ‖HN.ϖ v ^ k‖).indicator fun _ => (1 : ℂ) := by
      unfold ballIndV; rw [ballIndV_eq]
    rw [e]
    exact indicator_closedBall_mem_SBK 0 (norm_pos_iff.mpr (zpow_ne_zero _ (HN.ϖ_ne_zero v)))
  exact continuous_of_mem_SBK this

lemma integrable_ballIndV_zero (k : ℤ) : Integrable (ballIndV v 0 k) (selfDualV v) := by
  have := integrable_ballIndV_mul v 0 k (g := fun _ => (1 : ℂ)) continuous_const
  simpa using this

lemma integrable_oneV : Integrable (oneV v (2 * m)) ((localDataV v).muN (2 * m)) := by
  have := integrable_Sn_char (a := fun _ : Fin (2 * m) => (1 : (v.adicCompletion F)ˣ)) (isOps_V v) (oneV_mem_Sn v (m := m)) 0
  simpa [Bform] using this

lemma oneV_mul_ballIndV (t : Fv) (j : ℕ) (x : Fin (2 * m) → Fv) :
    oneV v (2 * m) x * ballIndV v 0 (j : ℤ) (Qform a x - t) = (congSet v a t j).indicator 1 x := by
  classical
  have h1 : oneV v (2 * m) x = if ∀ i, Valued.v (x i) ≤ 1 then 1 else 0 := by
    unfold oneV ptensor
    split_ifs with h
    · exact Finset.prod_eq_one fun i _ => by
        change ballIndV v 0 0 (x i) = 1
        rw [ballIndV, Set.indicator_of_mem (by simpa using h i)]
    · push Not at h
      obtain ⟨i, hi⟩ := h
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by
        change ballIndV v 0 0 (x i) = 0
        rw [ballIndV, Set.indicator_of_notMem (by simpa using hi)])
  have h2 : ballIndV v 0 (j : ℤ) (Qform a x - t) =
      if Valued.v (Qform a x - t) ≤ exp (-(j : ℤ)) then 1 else 0 := by
    unfold ballIndV
    split_ifs with h
    · exact Set.indicator_of_mem (by simpa using h) _
    · exact Set.indicator_of_notMem (by simpa using h) _
  rw [h1, h2, Set.indicator_apply]
  by_cases hA : ∀ i, Valued.v (x i) ≤ 1 <;>
    by_cases hB : Valued.v (Qform a x - t) ≤ exp (-(j : ℤ)) <;> simp [congSet, hA, hB]

lemma isClosed_congSet (t : Fv) (j : ℕ) : IsClosed (congSet v a t j) := by
  have e : congSet v a t j = (⋂ i, (fun x : Fin (2 * m) → Fv => x i) ⁻¹' (latticeV v 0 : Set Fv)) ∩
      ((fun x => Qform a x - t) ⁻¹' (latticeV v j : Set Fv)) := by
    ext x
    simp only [congSet, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
      SetLike.mem_coe, mem_latticeV, neg_zero, exp_zero, Nat.cast_zero]
  rw [e]
  refine IsClosed.inter (isClosed_iInter fun i => (isCompact_latticeV v 0).isClosed.preimage (continuous_apply i)) ?_
  refine (isCompact_latticeV v j).isClosed.preimage ?_
  refine Continuous.sub ?_ continuous_const
  unfold Qform
  exact continuous_finsetSum _ fun i _ => continuous_const.mul ((continuous_apply i).pow 2)

/-- **The truncated Whittaker integral as a volume** (every $t \in F_v$, $k \ge d_v$, $j = k - d_v$):
$\int_{\mathfrak p_v^{-k}}f_v(wn(b))\psi_v(-tb)\,db = \gamma_Vc_B\operatorname{vol}(\mathfrak p_v^{-k})\operatorname{vol}\{x \in L_v : Q(x) - t \in \mathfrak p_v^{j}\}$. -/
theorem whittakerTr_eq_vol (t : Fv) (k : ℕ) (hk : diffExp v ≤ k) :
    whittakerTr v a t k = (localDataV v).gammaV a * (localDataV v).cB a *
      (((selfDualV v).real (latticeV v (-(k : ℤ))) : ℂ) *
        (((localDataV v).muN (2 * m)).real (congSet v a t (k - diffExp v)) : ℂ)) := by
  set j := k - diffExp v with hj
  set d := diffExp v
  set γc := (localDataV v).gammaV a * (localDataV v).cB a
  have : SigmaFinite (localDataV v).μ := (isOps_V v).sigmaFinite
  have : SFinite ((localDataV v).muN (2 * m)) := by unfold muN; infer_instance
  -- Step 1: expand `wfun` and combine the characters
  have hW : ∀ b : Fv, ballIndV v 0 (-(k : ℤ)) b * (wfun v a b * (psiV v (-(t * b)) : ℂ)) =
      γc * ∫ x, ballIndV v 0 (-(k : ℤ)) b * (oneV v (2 * m) x * (psiV v (b * (Qform a x - t)) : ℂ))
        ∂(localDataV v).muN (2 * m) := by
    intro b
    rw [wfun_eq]
    simp only [← integral_const_mul, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have : (psiV v (b * (Qform a x - t)) : ℂ) = (psiV v (b * Qform a x) : ℂ) * (psiV v (-(t * b)) : ℂ) := by
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]; congr 2; ring
    dsimp only
    rw [this]; ring
  -- Step 2: Fubini
  have hint : Integrable (Function.uncurry fun (b : Fv) (x : Fin (2 * m) → Fv) =>
      ballIndV v 0 (-(k : ℤ)) b * (oneV v (2 * m) x * (psiV v (b * (Qform a x - t)) : ℂ)))
      ((selfDualV v).prod ((localDataV v).muN (2 * m))) := by
    refine Integrable.mono' ((integrable_ballIndV_zero v (-(k : ℤ))).norm.mul_prod
      (integrable_oneV v (m := m)).norm) ?_ (Filter.Eventually.of_forall fun p => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      refine ((continuous_ballIndV_zero v _).comp continuous_fst).mul
        (((continuous_oneV v).comp continuous_snd).mul ?_)
      refine continuous_subtype_val.comp ((continuous_psiV v).comp ?_)
      refine continuous_fst.mul ((?_ : Continuous fun x : Fin (2 * m) → Fv => Qform a x).comp continuous_snd
        |>.sub continuous_const)
      unfold Qform
      exact continuous_finsetSum _ fun i _ => continuous_const.mul ((continuous_apply i).pow 2)
    · simp only [Function.uncurry, norm_mul, Circle.norm_coe, mul_one]
      exact le_rfl
  have hfub : whittakerTr v a t k = γc * ∫ x, oneV v (2 * m) x *
      ∫ b, ballIndV v 0 (-(k : ℤ)) b * (psiV v (b * (Qform a x - t)) : ℂ) ∂selfDualV v
        ∂(localDataV v).muN (2 * m) := by
    rw [whittakerTr, integral_congr_ae (Filter.Eventually.of_forall hW), integral_const_mul,
      integral_integral_swap hint]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
    dsimp only
    ring
  -- Step 3: the `b`-integral
  have hb : ∀ y : Fv, ∫ b, ballIndV v 0 (-(k : ℤ)) b * (psiV v (b * y) : ℂ) ∂selfDualV v =
      ballIndV v 0 (j : ℤ) y * ((selfDualV v).real (latticeV v (-(k : ℤ))) : ℂ) := by
    intro y
    have := congrFun (fourierV_ballIndV_eq v 0 (-(k : ℤ))) y
    simp only [zero_mul, AddChar.map_zero_eq_one, Circle.coe_one, mul_one, neg_neg] at this
    rw [show ((k : ℤ) - d) = (j : ℤ) by omega] at this
    exact this
  -- Step 4: the `x`-integral is the volume of the congruence set
  have hx : ∫ x, oneV v (2 * m) x * ∫ b, ballIndV v 0 (-(k : ℤ)) b * (psiV v (b * (Qform a x - t)) : ℂ)
      ∂selfDualV v ∂(localDataV v).muN (2 * m) =
      ((selfDualV v).real (latticeV v (-(k : ℤ))) : ℂ) *
        (((localDataV v).muN (2 * m)).real (congSet v a t j) : ℂ) := by
    simp only [hb, ← mul_assoc]
    rw [integral_mul_const, mul_comm]
    congr 1
    rw [integral_congr_ae (Filter.Eventually.of_forall (oneV_mul_ballIndV v a t j))]
    have e : (fun x => (congSet v a t j).indicator (1 : (Fin (2 * m) → Fv) → ℂ) x) =
        fun x => (((congSet v a t j).indicator (1 : (Fin (2 * m) → Fv) → ℝ) x : ℝ) : ℂ) := by
      funext x; by_cases hx : x ∈ congSet v a t j <;> simp [hx]
    rw [e, integral_complex_ofReal, integral_indicator_one (isClosed_congSet v a t j).measurableSet]
  rw [hfub, hx]

/-- **The heart of the Whittaker = local density identity, before the limit.** For every $k \ge d_v$ and
$t \in \mathcal O_v$ (including $t = 0$), with
$j = k - d_v$,
$$\int_{\mathfrak p_v^{-k}}f_v(wn(b))\psi_v(-tb)\,db = \gamma_V\,c_B\,\operatorname{vol}(\mathcal O_v)^{n-1}\,
  \frac{r_{\mathfrak p^j}(t)}{q^{j(n-1)}},$$
$n = 2m$, $c_B = \prod_i|2a_i|_v^{1/2}$ (`cB`), $\operatorname{vol}(\mathcal O_v) = N(\mathfrak d_v)^{-1/2}$ (`selfDualV_real_Ov`),
$q = \#\mathcal O_v/\mathfrak p_v$, $r_{\mathfrak p^j}(t)$ = `DVR.repCount` (every finite place, dyadic included).
*Proof:* Fubini; the $b$-integral is $\operatorname{vol}(\mathfrak p^{-k})\mathbf 1[Q(x) - t \in \mathfrak p^{k - d_v}]$
(`fourierV_ballIndV_eq`); `muN_congSet`; $\operatorname{vol}(\mathfrak p^{-k})\operatorname{vol}(\mathfrak p^{j})^{n} =
\operatorname{vol}(\mathcal O_v)^{n-1}q^{-j(n-1)}$. -/
@[kb "weil1965" "Ch. II; Siegel (1935), §1 (the local factor as a limit of counts) [unverified]"]
theorem whittakerTr_eq (hm : 0 < m) (ha : ∀ i, Valued.v (a i : v.adicCompletion F) ≤ 1) (t : 𝔬) (k : ℕ)
    (hk : diffExp v ≤ k) :
    whittakerTr v a (t : Fv) k = (localDataV v).gammaV a * (localDataV v).cB a *
      ((((selfDualV v).real (latticeV v 0) ^ (2 * m - 1) *
        ((LocalDensity.DVR.repCount (QO v a ha) (LocalDensity.NF.π v) (k - diffExp v) t : ℝ) /
          (LocalDensity.DVR.q 𝔬 : ℝ) ^ ((k - diffExp v) * (2 * m - 1)))) : ℝ) : ℂ) := by
  set j := k - diffExp v with hj
  set d := diffExp v
  -- Step 5: volumes
  have key : (selfDualV v).real (latticeV v (-(k : ℤ))) *
      ((LocalDensity.DVR.repCount (QO v a ha) (LocalDensity.NF.π v) j t : ℝ) *
        (selfDualV v).real (latticeV v j) ^ (2 * m)) =
      (selfDualV v).real (latticeV v 0) ^ (2 * m - 1) *
        ((LocalDensity.DVR.repCount (QO v a ha) (LocalDensity.NF.π v) j t : ℝ) /
          (LocalDensity.DVR.q 𝔬 : ℝ) ^ (j * (2 * m - 1))) := by
    have hΔ : (0 : ℝ) < modV v := by exact_mod_cast modV_pos v
    have hq : (LocalDensity.DVR.q 𝔬 : ℝ) = (modV v : ℝ)⁻¹ := by
      rw [LocalDensity.NF.q_completion, modV_eq, inv_inv]
    rw [selfDualV_real_latticeV, selfDualV_real_latticeV, selfDualV_real_latticeV, hq, zpow_zero, mul_one,
      inv_pow, div_inv_eq_mul, pow_mul (modV v : ℝ) j]
    set c := (modV v : ℝ) ^ ((d : ℝ) / 2)
    set r := (LocalDensity.DVR.repCount (QO v a ha) (LocalDensity.NF.π v) j t : ℝ)
    have hc2 : c * c = (modV v : ℝ) ^ d := by
      rw [← Real.rpow_add hΔ, add_halves, Real.rpow_natCast]
    have hcpos : 0 < c := Real.rpow_pos_of_pos hΔ _
    have hkjd : (k : ℤ) = (j : ℤ) + (d : ℤ) := by omega
    have e1 : (modV v : ℝ) ^ (-(k : ℤ)) = (((modV v : ℝ) ^ j)⁻¹ * ((modV v : ℝ) ^ d)⁻¹) := by
      rw [hkjd, neg_add, zpow_add₀ hΔ.ne', zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
    rw [e1, zpow_natCast]
    obtain ⟨N, hN⟩ : ∃ N, 2 * m = N + 1 := ⟨2 * m - 1, by omega⟩
    rw [hN, Nat.add_sub_cancel, mul_pow, pow_succ c, pow_succ ((modV v : ℝ) ^ j)]
    have hX : (0 : ℝ) < (modV v : ℝ) ^ j := pow_pos hΔ _
    rw [← hc2]
    field_simp
  rw [whittakerTr_eq_vol v a (t : Fv) k hk, muN_congSet v a ha j t, ← key]
  push_cast
  ring

/-! ### The limit: Whittaker = local density -/

lemma QO_nondegenerate (ha : ∀ i, Valued.v (a i : v.adicCompletion F) ≤ 1) : (QO v a ha).Nondegenerate := by
  unfold QuadForm.Nondegenerate QuadForm.hessian QO QuadForm.diag
  simp only [Matrix.diagonal_transpose, Matrix.diagonal_add, Matrix.det_diagonal]
  rw [Finset.prod_ne_zero_iff]
  intro i _ h
  have h' : ((aO v a ha i + aO v a ha i : 𝔬) : Fv) = 0 := by rw [h]; rfl
  have : (2 : Fv) * (a i : Fv) = 0 := by
    rw [two_mul]; simpa [aO] using h'
  exact (mul_ne_zero two_ne_zero (a i).ne_zero) this

lemma two_ne_zero_O : (2 : 𝔬) ≠ 0 := by
  intro h
  have : ((2 : 𝔬) : Fv) = 0 := by rw [h]; rfl
  exact two_ne_zero (by simpa using this)

/-- The constant $\gamma_V\,c_B\operatorname{vol}(\mathcal O_v)^{n-1}$ of the Whittaker–density identity, $n = 2m$. -/
def whittakerConst : ℂ :=
  (localDataV v).gammaV a * (localDataV v).cB a * (((selfDualV v).real (latticeV v 0) ^ (2 * m - 1) : ℝ) : ℂ)

/-- **The truncated Whittaker integrals are eventually constant**, equal to $\gamma_Vc_B\operatorname{vol}(\mathcal O_v)^{n-1}\beta_v(t)$,
for $t \in \mathcal O_v\setminus\{0\}$, at every finite place (from the stabilization of the counts,
`DVR.localDensity_eventually_eq`, Hanke (5.2)). -/
theorem whittakerTr_eventually_eq (hm : 0 < m) (ha : ∀ i, Valued.v (a i : v.adicCompletion F) ≤ 1) (t : 𝔬)
    (ht : t ≠ 0) :
    ∀ᶠ k in atTop, whittakerTr v a (t : Fv) k = whittakerConst v a *
      (LocalDensity.DVR.localDensity (QO v a ha) (LocalDensity.NF.π v) t : ℂ) := by
  have hst := LocalDensity.DVR.localDensity_eventually_eq (QO v a ha) (QO_nondegenerate v a ha)
    (LocalDensity.NF.π v) (LocalDensity.NF.irreducible_π v) t ht (two_ne_zero_O v)
  have hshift := (tendsto_sub_atTop_nat (diffExp v)).eventually hst
  filter_upwards [hshift, eventually_ge_atTop (diffExp v)] with k hk hkd
  rw [whittakerTr_eq v a hm ha t k hkd, whittakerConst, ← hk]
  push_cast
  ring

/-- **Whittaker = local density** (every finite place $v$, **dyadic included**). For
$V_v = \langle a_0, \dots, a_{n-1}\rangle$, $n = 2m \ge 2$, $a_i \in \mathcal O_v\setminus\{0\}$, $\varphi_v = \mathbf 1_{\mathcal O_v^n}$
and $t \in \mathcal O_v\setminus\{0\}$:
$$W_v(f_{\varphi_v}, t) = \lim_k\int_{\mathfrak p_v^{-k}}(\omega_v(wn(b))\varphi_v)(0)\,\psi_v(-tb)\,db
  = \gamma_V\cdot\prod_{i<n}|2a_i|_v^{1/2}\cdot\operatorname{vol}(\mathcal O_v)^{n-1}\cdot\beta_v(t),$$
$\operatorname{vol}(\mathcal O_v) = N(\mathfrak d_v)^{-1/2}$ (self-dual measure), $\gamma_V$ the Weil index of $V_v$ (`gammaV`), and
$\beta_v(t) = \lim_j\#\{x \in (\mathcal O_v/\mathfrak p_v^j)^n : Q(x) \equiv t\}/q^{j(n-1)}$ = `DVR.localDensity` (Hanke 2004,
(5.1)–(5.2)). -/
@[kb "weil1965" "Ch. II, the local factors of Siegel's formula [unverified]; Yang (1998), §1 [unverified]"]
theorem whittakerV_eq_localDensity (hm : 0 < m) (ha : ∀ i, Valued.v (a i : v.adicCompletion F) ≤ 1) (t : 𝔬)
    (ht : t ≠ 0) :
    whittakerV v a (t : Fv) = (localDataV v).gammaV a * (localDataV v).cB a *
      (((selfDualV v).real (latticeV v 0) ^ (2 * m - 1) : ℝ) : ℂ) *
        (LocalDensity.DVR.localDensity (QO v a ha) (LocalDensity.NF.π v) t : ℂ) := by
  have h := whittakerTr_eventually_eq v a hm ha t ht
  exact (tendsto_const_nhds.congr' (h.mono fun k hk => hk.symm)).limUnder_eq

/-- **The Whittaker integral as a limit** (the truncations converge to $W_v(t)$). -/
theorem tendsto_whittakerTr (hm : 0 < m) (ha : ∀ i, Valued.v (a i : v.adicCompletion F) ≤ 1) (t : 𝔬) (ht : t ≠ 0) :
    Tendsto (whittakerTr v a (t : Fv)) atTop (𝓝 (whittakerV v a (t : Fv))) := by
  rw [whittakerV_eq_localDensity v a hm ha t ht]
  exact tendsto_const_nhds.congr' ((whittakerTr_eventually_eq v a hm ha t ht).mono fun k hk => by
    rw [hk, whittakerConst])

/-- **The constant term** ($t = 0$): for every $k \ge d_v$,
$\int_{\mathfrak p_v^{-k}}f_v(wn(b))\,db = \gamma_Vc_B\operatorname{vol}(\mathcal O_v)^{n-1}\,r_{\mathfrak p^{k-d_v}}(0)/q^{(k-d_v)(n-1)}$; so
$W_v(0) = \gamma_Vc_B\operatorname{vol}(\mathcal O_v)^{n-1}\beta_v(0)$ whenever the density $\beta_v(0)$ exists (e.g. $n \ge 5$). -/
theorem whittakerTr_zero_eq (hm : 0 < m) (ha : ∀ i, Valued.v (a i : v.adicCompletion F) ≤ 1) (k : ℕ)
    (hk : diffExp v ≤ k) :
    whittakerTr v a 0 k = whittakerConst v a *
      (((LocalDensity.DVR.repCount (QO v a ha) (LocalDensity.NF.π v) (k - diffExp v) 0 : ℝ) /
          (LocalDensity.DVR.q 𝔬 : ℝ) ^ ((k - diffExp v) * (2 * m - 1)) : ℝ) : ℂ) := by
  have := whittakerTr_eq v a hm ha 0 k hk
  simp only [ZeroMemClass.coe_zero] at this
  rw [this, whittakerConst]; push_cast; ring

/-- **At a good place the Whittaker integral is the density**: if $d_v = 0$, $v \nmid 2$ and all $a_i$ are units
(`IsGoodV`), then $\gamma_V = 1$, $c_B = 1$, $\operatorname{vol}(\mathcal O_v) = 1$, and $W_v(f_{\mathbf 1_{L_v}}, t) = \beta_v(t)$. -/
theorem whittakerV_eq_localDensity_of_good (hm : 0 < m) (hg : IsGoodV v a) (t : 𝔬) (ht : t ≠ 0) :
    whittakerV v a (t : Fv) = (LocalDensity.DVR.localDensity (QO v a (fun i => (hg.2.2 i).le))
      (LocalDensity.NF.π v) t : ℂ) := by
  rw [whittakerV_eq_localDensity v a hm (fun i => (hg.2.2 i).le) t ht, gammaV_eq_one_of_good hg]
  have hcB : (localDataV v).cB a = 1 := by
    unfold LocalData.cB
    refine Finset.prod_eq_one fun i _ => ?_
    rw [md_eq_one v (by rw [map_mul, hg.2.1, hg.2.2 i, one_mul])]
    simp
  have hvol : (selfDualV v).real (latticeV v 0) = 1 := by
    rw [selfDualV_real_latticeV, hg.1]; simp
  rw [hcB, hvol]; simp

/-! ### Over $\mathcal O_F$ -/

/-- The coefficients of a global diagonal form $\sum_ib_ix_i^2$ ($b_i \in \mathcal O_F\setminus\{0\}$) as units of $F_v$. -/
def aOfInt (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) : Fin (2 * m) → (v.adicCompletion F)ˣ :=
  fun i => Units.mk0 ((LocalDensity.NF.ι v (b i) : 𝔬) : Fv) (by
    intro h
    have h' : (LocalDensity.NF.ι v (b i) : 𝔬) = 0 := Subtype.ext h
    exact hb i ((injective_iff_map_eq_zero _).mp (LocalDensity.NF.ι_injective v) _ h'))

lemma aOfInt_le_one (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (i : Fin (2 * m)) :
    Valued.v ((aOfInt v b hb i : (v.adicCompletion F)ˣ) : v.adicCompletion F) ≤ 1 :=
  (LocalDensity.NF.ι v (b i)).2

lemma QO_aOfInt (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) :
    QO v (aOfInt v b hb) (aOfInt_le_one v b hb) = LocalDensity.NF.Qp v (QuadForm.diag b) := by
  unfold QO LocalDensity.NF.Qp QuadForm.map QuadForm.diag
  congr 1
  · ext i j
    simp only [Matrix.diagonal_apply, Matrix.map_apply]
    split_ifs with h
    · subst h; rfl
    · simp

/-- **Whittaker = local density over $\mathcal O_F$** (every finite prime $\mathfrak p$, dyadic included): for the global
diagonal form $Q = \sum_{i<n}b_ix_i^2$, $b_i \in \mathcal O_F\setminus\{0\}$, $n = 2m \ge 2$, and $t \in \mathcal O_F\setminus\{0\}$,
$$W_\mathfrak p(f_{\mathbf 1_{L_\mathfrak p}}, t) = \gamma_{V,\mathfrak p}\cdot\prod_{i<n}|2b_i|_\mathfrak p^{1/2}\cdot
  N(\mathfrak d_\mathfrak p)^{-(n-1)/2}\cdot\beta_\mathfrak p(Q, t),$$
with $\beta_\mathfrak p(Q,t)$ = `NF.localDensity` (Hanke 2004, (5.1)–(5.2), over $\mathcal O_F$). -/
@[kb "weil1965" "Ch. II [unverified]; Hanke 2004, (5.1)–(5.2) (the densities)"]
theorem whittakerV_eq_NF_localDensity (hm : 0 < m) (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (t : 𝓞 F)
    (ht : t ≠ 0) :
    whittakerV v (aOfInt v b hb) ((LocalDensity.NF.ι v t : 𝔬) : Fv) =
      (localDataV v).gammaV (aOfInt v b hb) * (localDataV v).cB (aOfInt v b hb) *
        (((((Ideal.absNorm v.asIdeal : ℝ) ^ diffExp v) ^ (-(1 : ℝ) / 2)) ^ (2 * m - 1) : ℝ) : ℂ) *
          (LocalDensity.NF.localDensity v (QuadForm.diag b) t : ℂ) := by
  have ht' : LocalDensity.NF.ι v t ≠ 0 := fun h =>
    ht ((injective_iff_map_eq_zero _).mp (LocalDensity.NF.ι_injective v) _ h)
  rw [whittakerV_eq_localDensity v (aOfInt v b hb) hm (aOfInt_le_one v b hb) _ ht', QO_aOfInt,
    ← LocalDensity.NF.localDensity_eq_completion, selfDualV_real_Ov]

/-! ### Non-integral $t$; the Lebesgue integral -/

/-- **$W_v(t) = 0$ for $t \notin \mathcal O_v$**: $Q(L_v) \subseteq \mathcal O_v$, so the congruence sets are empty. -/
theorem whittakerTr_eq_zero_of_not_int (ha : ∀ i, Valued.v (a i : v.adicCompletion F) ≤ 1) {t : Fv}
    (ht : 1 < Valued.v t) (k : ℕ) (hk : diffExp v ≤ k) : whittakerTr v a t k = 0 := by
  have hempty : congSet v a t (k - diffExp v) = ∅ := by
    ext x
    simp only [congSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
    intro hx
    by_contra hle
    push Not at hle
    have h1 := valued_Qform_le_one v a ha x hx
    have h2 : Valued.v (Qform a x - t) ≤ 1 := hle.trans (by rw [← exp_zero, exp_le_exp]; omega)
    have : Valued.v t ≤ 1 := by
      calc Valued.v t = Valued.v (Qform a x - (Qform a x - t)) := by ring_nf
        _ ≤ max _ _ := Valuation.map_sub _ _ _
        _ ≤ 1 := max_le h1 h2
    exact absurd ht (not_lt.mpr this)
  rw [whittakerTr_eq_vol v a t k hk, hempty]
  simp

/-- $W_v(t) = 0$ for $t \notin \mathcal O_v$. -/
theorem whittakerV_eq_zero_of_not_int (ha : ∀ i, Valued.v (a i : v.adicCompletion F) ≤ 1) {t : Fv}
    (ht : 1 < Valued.v t) : whittakerV v a t = 0 :=
  (tendsto_const_nhds.congr' ((eventually_ge_atTop (diffExp v)).mono fun k hk =>
    (whittakerTr_eq_zero_of_not_int v a ha ht k hk).symm)).limUnder_eq

lemma eventually_ballIndV_eq_one (b : Fv) : ∀ᶠ k : ℕ in atTop, ballIndV v 0 (-(k : ℤ)) b = 1 := by
  have hϖ : ‖HN.ϖ v‖ < 1 := norm_ϖ_lt_one v
  have hϖ0 : 0 < ‖HN.ϖ v‖ := norm_pos_iff.mpr (HN.ϖ_ne_zero v)
  have hlim : Tendsto (fun k : ℕ => ‖HN.ϖ v‖⁻¹ ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (one_lt_inv₀ hϖ0 |>.mpr hϖ)
  filter_upwards [hlim.eventually_ge_atTop ‖b‖] with k hk
  unfold ballIndV
  rw [ballIndV_eq, Set.indicator_of_mem]
  rw [Metric.mem_closedBall, dist_zero_right, norm_zpow, zpow_neg, zpow_natCast, ← inv_pow]
  exact hk

/-- **The limit is the Lebesgue integral when the latter exists**: if $b \mapsto f_v(wn(b))\psi_v(-tb)$ is integrable on
$F_v$, then $W_v(t) = \int_{F_v}f_v(wn(b))\psi_v(-tb)\,db$ (dominated convergence). So `whittakerV` is the classical
$\int_{F_v}$ whenever that converges absolutely, and the regularized (improper) integral in general. -/
theorem whittakerV_eq_integral (t : Fv)
    (hint : Integrable (fun b => wfun v a b * (psiV v (-(t * b)) : ℂ)) (selfDualV v)) :
    whittakerV v a t = ∫ b, wfun v a b * (psiV v (-(t * b)) : ℂ) ∂selfDualV v := by
  refine Tendsto.limUnder_eq ?_
  refine tendsto_integral_of_dominated_convergence (fun b => ‖wfun v a b * (psiV v (-(t * b)) : ℂ)‖)
    (fun k => ?_) hint.norm (fun k => Filter.Eventually.of_forall fun b => ?_)
    (Filter.Eventually.of_forall fun b => ?_)
  · exact ((continuous_ballIndV_zero v _).aestronglyMeasurable).mul hint.aestronglyMeasurable
  · rw [norm_mul]
    refine mul_le_of_le_one_left (norm_nonneg _) ?_
    unfold ballIndV
    by_cases hb : b ∈ {x : Fv | Valued.v (x - 0) ≤ exp (-(-(k : ℤ)))}
    · rw [Set.indicator_of_mem hb]; simp
    · rw [Set.indicator_of_notMem hb]; simp
  · refine tendsto_const_nhds.congr' ((eventually_ballIndV_eq_one v b).mono fun k hk => ?_)
    dsimp only
    rw [hk, one_mul]



end QuadFormsKB.SiegelWeil
