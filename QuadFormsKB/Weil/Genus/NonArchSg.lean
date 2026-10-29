/-
# The Schwartz space of $V^g$ at a non-archimedean place

**Layer:** local harmonic analysis; combines the abstract Schrödinger model `Weil/Genus/Model.lean` with the
non-archimedean test functions `SBK K` of `Weil/NonArch.lean`.

**Setting.** $K$ is a non-archimedean local field (a nontrivially normed field with ultrametric, proper norm), and $D$ is
a `LocalData K` whose space of test functions is $D.S = \texttt{SBK}\,K$ (hypothesis `hS`) and whose additive character
$D.\psi$ is a standard character (hypothesis `hψ : Analysis.Weil.IsStdChar D.ψ`: continuous, trivial on some ball, nontrivial).
Both hold for `localDataV v` at every finite place $v$ (`isStdChar_psiV`).

**Results.** Write $V^g = M_{n\times g}(K)$, $n = 2m$ (`PtG m g K`).
* `SBG K m g`: the locally constant compactly supported functions $\Phi : V^g \to \mathbb C$, i.e. there are $R$ and
  $\varepsilon > 0$ with $\Phi(X) \ne 0 \Rightarrow \|X_{ij}\| \le R$ for all $i, j$ and $\Phi(X + H) = \Phi(X)$ whenever
  $\|H_{ij}\| \le \varepsilon$ for all $i, j$.
* `mem_Sg_iff`: $\mathcal S(V^g) := $ `Sg D m g` (the span of coordinate pure tensors of test functions) equals `SBG K m g`.
  ($\subseteq$: a pure tensor of test functions is locally constant with compact support; $\supseteq$: on the compact box of
  radius $R$, a function invariant under the open box of radius $\varepsilon$ is a finite sum $\sum_c\Phi(c)\mathbf 1_{c+P}$
  of translates of the indicator of $P$, each a pure tensor of ball indicators; `Analysis.Weil.exists_coset_sum`.)
* `opMg_mem_Sg_nonarch`: $\mathcal S(V^g)$ is stable under $\omega(m(A))$, $A \in \mathrm{GL}_g(K)$ (the substitution $X \mapsto XA$
  preserves `SBG`, by the ultrametric inequality for $XA$ and for $X = (XA)A^{-1}$; the factor $\chi_V(\det A)|\det A|^m$ is constant).
* `opNg_mem_Sg_nonarch`: $\mathcal S(V^g)$ is stable under $\omega(n(B))$ for every matrix $B$ (the phase $\psi(\operatorname{tr}(B\,Q[X]))$
  is locally constant on a bounded box, since $\psi$ is trivial on a small ball; cf. `chirp_mem_SBK`).

No further hypothesis is used: all four results are unconditional given `hS` and `hψ`.

Sources: Weil, Acta Math. 111 (1964), §14 [unverified].
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Weil.Genus.Model
import QuadFormsKB.Weil.NonArch

open MeasureTheory Metric Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.WeilRep.Genus

open WeilRep WeilRep.LocalData

section NonArch

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
  [MeasurableSpace K] [BorelSpace K]

variable (K) in
/-- **Locally constant compactly supported functions on $V^g = M_{2m\times g}(K)$** ($K$ non-archimedean): the
$\Phi : V^g \to \mathbb C$ for which there are $R \in \mathbb R$ and $\varepsilon > 0$ with
$\Phi(X) \ne 0 \Rightarrow \|X_{ij}\| \le R$ for all $i, j$, and $\Phi(X + H) = \Phi(X)$ whenever $\|H_{ij}\| \le \varepsilon$ for
all $i, j$. -/
@[kb "weil1964" "§14 ($\\mathcal S(X)$ for a finite-dimensional $X$ over a $\\mathfrak p$-adic field) [unverified]"]
def SBG (m g : ℕ) : Submodule ℂ (PtG m g K → ℂ) where
  carrier := {Φ | ∃ R ε : ℝ, 0 < ε ∧ (∀ X, Φ X ≠ 0 → ∀ i j, ‖X i j‖ ≤ R) ∧
    ∀ X H : PtG m g K, (∀ i j, ‖H i j‖ ≤ ε) → Φ (X + H) = Φ X}
  zero_mem' := ⟨0, 1, one_pos, fun X h => absurd rfl h, fun _ _ _ => rfl⟩
  add_mem' := by
    rintro Φ Ψ ⟨R, ε, hε, hR, hinv⟩ ⟨R', ε', hε', hR', hinv'⟩
    refine ⟨max R R', min ε ε', lt_min hε hε', fun X hX i j => ?_, fun X H hH => ?_⟩
    · by_cases hf : Φ X = 0
      · have : Ψ X ≠ 0 := by intro hg; apply hX; simp [hf, hg]
        exact (hR' X this i j).trans (le_max_right _ _)
      · exact (hR X hf i j).trans (le_max_left _ _)
    · simp only [Pi.add_apply]
      rw [hinv X H fun i j => (hH i j).trans (min_le_left _ _),
        hinv' X H fun i j => (hH i j).trans (min_le_right _ _)]
  smul_mem' := by
    rintro c Φ ⟨R, ε, hε, hR, hinv⟩
    refine ⟨R, ε, hε, fun X hX => hR X fun h => hX (by simp [h]), fun X H hH => ?_⟩
    simp only [Pi.smul_apply, hinv X H hH]

variable {m g : ℕ}

/-! ### Elementary lemmas -/

lemma norm_sum_le_ult {ι : Type*} (s : Finset ι) (F : ι → K) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i ∈ s, ‖F i‖ ≤ C) : ‖∑ i ∈ s, F i‖ ≤ C :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC h

lemma exists_uniform {ι : Type*} [Fintype ι] (ε : ι → ℝ) (h : ∀ i, 0 < ε i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ ε i := by
  have hS : 0 < 1 + ∑ i, (ε i)⁻¹ :=
    add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun i _ => (inv_pos.mpr (h i)).le)
  refine ⟨(1 + ∑ i, (ε i)⁻¹)⁻¹, inv_pos.mpr hS, fun i => ?_⟩
  rw [← inv_le_inv₀ (h i) (inv_pos.mpr hS)]
  rw [inv_inv]
  have := Finset.single_le_sum (f := fun i => (ε i)⁻¹) (fun i _ => (inv_pos.mpr (h i)).le) (Finset.mem_univ i)
  linarith

lemma entry_le_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (j k : Fin n) :
    ‖A j k‖ ≤ ∑ j', ∑ k', ‖A j' k'‖ :=
  calc ‖A j k‖ ≤ ∑ k', ‖A j k'‖ :=
        Finset.single_le_sum (f := fun k' => ‖A j k'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ k)
    _ ≤ ∑ j', ∑ k', ‖A j' k'‖ :=
        Finset.single_le_sum (f := fun j' => ∑ k', ‖A j' k'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ j)

lemma entry_mul_le (X : PtG m g K) (A : Matrix (Fin g) (Fin g) K) {r N : ℝ} (hr : 0 ≤ r) (hN : 0 ≤ N)
    (hX : ∀ i j, ‖X i j‖ ≤ r) (hA : ∀ j k, ‖A j k‖ ≤ N) : ∀ i k, ‖(X * A) i k‖ ≤ r * N := by
  intro i k
  rw [Matrix.mul_apply]
  refine norm_sum_le_ult _ _ (mul_nonneg hr hN) fun j _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hX i j) (hA j k) (norm_nonneg _) hr

/-! ### The box subgroups -/

/-- The box $\{X : \|X_{ij}\| \le r\ \forall i, j\}$ of $V^g$, an additive subgroup (ultrametric inequality). -/
def box (r : NNReal) : AddSubgroup (PtG m g K) where
  carrier := {X | ∀ i j, ‖X i j‖ ≤ r}
  add_mem' := by
    intro X Y hX hY i j
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hX i j) (hY i j))
  zero_mem' := by
    intro i j
    show ‖(0 : K)‖ ≤ r
    rw [norm_zero]; exact r.coe_nonneg
  neg_mem' := by intro X hX i j; simpa using hX i j

lemma mem_box {r : NNReal} {X : PtG m g K} : X ∈ box (K := K) r ↔ ∀ i j, ‖X i j‖ ≤ r := Iff.rfl

lemma box_mono {r r' : NNReal} (h : r ≤ r') : box (m := m) (g := g) (K := K) r ≤ box r' :=
  fun _ hX i j => (hX i j).trans (by exact_mod_cast h)

lemma coe_box (r : NNReal) :
    (box (m := m) (g := g) (K := K) r : Set (PtG m g K)) =
      Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => closedBall (0 : K) r := by
  ext X
  constructor
  · intro h i _ j _
    rw [mem_closedBall, dist_zero_right]
    exact (mem_box.mp h) i j
  · intro h i j
    have := h i (Set.mem_univ _) j (Set.mem_univ _)
    rwa [mem_closedBall, dist_zero_right] at this

lemma isCompact_box (r : NNReal) : IsCompact (box (m := m) (g := g) (K := K) r : Set (PtG m g K)) := by
  rw [coe_box]
  exact isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_closedBall _ _

lemma isOpen_box {r : NNReal} (hr : 0 < r) : IsOpen (box (m := m) (g := g) (K := K) r : Set (PtG m g K)) := by
  rw [coe_box]
  exact isOpen_set_pi Set.finite_univ fun i _ => isOpen_set_pi Set.finite_univ fun j _ =>
    IsUltrametricDist.isOpen_closedBall (0 : K) (by exact_mod_cast hr.ne')

/-! ### Pure tensors of test functions -/

lemma ptG_mem_SBG {f : Fin (2 * m) → Fin g → K → ℂ} (hf : ∀ i j, f i j ∈ SBK K) : ptG f ∈ SBG K m g := by
  choose R ε hε hR hinv using fun i j => mem_SBK.mp (hf i j)
  obtain ⟨δ, hδ, hδle⟩ := exists_uniform (fun p : Fin (2 * m) × Fin g => ε p.1 p.2) fun p => hε p.1 p.2
  refine ⟨∑ p : Fin (2 * m) × Fin g, |R p.1 p.2|, δ, hδ, fun X hX i j => ?_, fun X H hH => ?_⟩
  · have h1 : f i j (X i j) ≠ 0 :=
      Finset.prod_ne_zero_iff.mp (Finset.prod_ne_zero_iff.mp hX i (Finset.mem_univ _)) j (Finset.mem_univ _)
    calc ‖X i j‖ ≤ R i j := hR i j _ h1
      _ ≤ |R i j| := le_abs_self _
      _ ≤ ∑ p : Fin (2 * m) × Fin g, |R p.1 p.2| :=
        Finset.single_le_sum (f := fun p : Fin (2 * m) × Fin g => |R p.1 p.2|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ (i, j))
  · unfold ptG
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    exact hinv i j (X i j) (H i j) ((hH i j).trans (hδle (i, j)))

/-! ### `Sg = SBG` -/

variable {D : LocalData K} {a : Fin (2 * m) → Kˣ}

lemma Sg_le_SBG (hS : D.S = SBK K) : Sg D m g ≤ SBG K m g := by
  refine Submodule.span_le.mpr ?_
  rintro Φ ⟨f, hf, rfl⟩
  exact ptG_mem_SBG fun i j => by rw [← hS]; exact hf i j

lemma SBG_le_Sg (hS : D.S = SBK K) : SBG K m g ≤ Sg D m g := by
  intro Φ hΦ
  obtain ⟨R, ε, hε, hR, hinv⟩ := hΦ
  have hRε : 0 < max R ε := lt_max_of_lt_right hε
  set R' : NNReal := (max R ε).toNNReal with hR'
  set ε' : NNReal := ε.toNNReal with hε'
  have hR'c : (R' : ℝ) = max R ε := Real.coe_toNNReal _ hRε.le
  have hε'c : (ε' : ℝ) = ε := Real.coe_toNNReal _ hε.le
  have hε'pos : 0 < ε' := by rw [← NNReal.coe_pos, hε'c]; exact hε
  obtain ⟨n, c, hc, hsum⟩ := Analysis.Weil.exists_coset_sum (box (m := m) (g := g) (K := K) R')
    (box ε') (isCompact_box R') (isOpen_box hε'pos) (box_mono (by
      rw [← NNReal.coe_le_coe, hR'c, hε'c]; exact le_max_right _ _)) Φ
    (fun X _ H hH => hinv X H fun i j => (hH i j).trans (le_of_eq hε'c))
  have hΦeq : Φ = (box (m := m) (g := g) (K := K) R' : Set (PtG m g K)).indicator Φ := by
    funext X
    by_cases hX : Φ X = 0
    · simp [Set.indicator, hX]
    · rw [Set.indicator_of_mem]
      intro i j
      rw [hR'c]
      exact (hR X hX i j).trans (le_max_left _ _)
  have hterm : ∀ (x : PtG m g K) (i : Fin n),
      ({y : PtG m g K | y - c i ∈ box (m := m) (g := g) (K := K) ε'}.indicator
        (1 : PtG m g K → ℂ)) x =
        ptG (fun p q => (closedBall (c i p q) ε').indicator (fun _ => (1 : ℂ))) x := by
    intro x i
    by_cases h : x - c i ∈ box (m := m) (g := g) (K := K) ε'
    · rw [Set.indicator_of_mem (show x ∈ {y : PtG m g K | y - c i ∈ box ε'} from h)]
      unfold ptG
      symm
      refine Finset.prod_eq_one fun p _ => Finset.prod_eq_one fun q _ => ?_
      dsimp only
      rw [Set.indicator_of_mem]
      rw [mem_closedBall, dist_eq_norm]
      exact h p q
    · rw [Set.indicator_of_notMem (show x ∉ {y : PtG m g K | y - c i ∈ box ε'} from h)]
      rw [mem_box] at h
      push Not at h
      obtain ⟨p, q, hpq⟩ := h
      unfold ptG
      symm
      refine Finset.prod_eq_zero (Finset.mem_univ p) (Finset.prod_eq_zero (Finset.mem_univ q) ?_)
      dsimp only
      rw [Set.indicator_of_notMem]
      rw [mem_closedBall, dist_eq_norm]
      exact not_le.mpr hpq
  have hΦsum : Φ = ∑ i, Φ (c i) • ptG (fun p q => (closedBall (c i p q) ε').indicator (fun _ => (1 : ℂ))) := by
    funext X
    rw [Finset.sum_apply]
    refine (congrFun hΦeq X).trans ((hsum X).trans (Finset.sum_congr rfl fun i _ => ?_))
    rw [Pi.smul_apply, smul_eq_mul, hterm]
  rw [hΦsum]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (ptG_mem_Sg fun p q => ?_)
  rw [hS]
  exact indicator_closedBall_mem_SBK _ hε'pos

/-- **The Schwartz space of $V^g$ at a non-archimedean place** (Weil 1964, §14): for a `LocalData` $D$ over a
non-archimedean local field $K$, with test functions $D.S = \texttt{SBK}\,K$ (hypothesis `hS`),
$\mathcal S(V^g) = $ `Sg D m g` (span of pure tensors of test functions) equals `SBG K m g`, the space of locally constant
compactly supported functions on $V^g = M_{2m\times g}(K)$. No hypothesis on the character is needed. -/
@[kb "weil1964" "§14 ($\\mathcal S(X)$ for a finite-dimensional $X$ over a $\\mathfrak p$-adic field) [unverified]"]
theorem mem_Sg_iff (hS : D.S = SBK K) {Φ : PtG m g K → ℂ} : Φ ∈ Sg D m g ↔ Φ ∈ SBG K m g :=
  ⟨fun h => Sg_le_SBG hS h, fun h => SBG_le_Sg hS h⟩

/-! ### Stability under $X \mapsto XA$ -/

lemma SBG_comp_mul {Φ : PtG m g K → ℂ} (hΦ : Φ ∈ SBG K m g) (A B : Matrix (Fin g) (Fin g) K)
    (hAB : A * B = 1) : (fun X => Φ (X * A)) ∈ SBG K m g := by
  obtain ⟨R, ε, hε, hR, hinv⟩ := hΦ
  set NA : ℝ := ∑ j, ∑ k, ‖A j k‖ with hNA
  set NB : ℝ := ∑ j, ∑ k, ‖B j k‖ with hNB
  have hNA0 : 0 ≤ NA := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hNB0 : 0 ≤ NB := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨|R| * NB, ε / (NA + 1), by positivity, fun X hX i j => ?_, fun X H hH => ?_⟩
  · have h1 : ∀ i j, ‖(X * A) i j‖ ≤ |R| := fun i j => (hR _ hX i j).trans (le_abs_self _)
    have h2 := entry_mul_le (X * A) B (abs_nonneg R) hNB0 h1 (entry_le_sum B) i j
    rwa [Matrix.mul_assoc, hAB, Matrix.mul_one] at h2
  · show Φ ((X + H) * A) = Φ (X * A)
    rw [Matrix.add_mul]
    refine hinv _ _ fun i k => ?_
    have h3 := entry_mul_le H A (by positivity) hNA0 hH (entry_le_sum A) i k
    refine h3.trans ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith

/-- **Stability under $\omega(m(A))$.** At a non-archimedean place, $\mathcal S(V^g)$ is stable under
$\Phi \mapsto \chi_V(\det A)|\det A|^m\,\Phi(XA)$ for every $A \in \mathrm{GL}_g(K)$ (hypothesis `hS : D.S = SBK K`;
the character plays no role). -/
@[kb "weil1964" "§14 ($\\mathcal S(X)$ for a finite-dimensional $X$ over a $\\mathfrak p$-adic field) [unverified]"]
theorem opMg_mem_Sg_nonarch (hS : D.S = SBK K) (A : GL (Fin g) K) {Φ : PtG m g K → ℂ}
    (hΦ : Φ ∈ Sg D m g) : opMg D a A Φ ∈ Sg D m g := by
  rw [mem_Sg_iff hS] at hΦ ⊢
  have h := SBG_comp_mul hΦ (A : Matrix (Fin g) (Fin g) K) ((A⁻¹ : GL (Fin g) K) : Matrix (Fin g) (Fin g) K)
    (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
  have h' := (SBG K m g).smul_mem
    (D.chiV a (A : Matrix (Fin g) (Fin g) K).det * (D.md (A : Matrix (Fin g) (Fin g) K).det : ℂ) ^ m) h
  have e : opMg D a A Φ = (D.chiV a (A : Matrix (Fin g) (Fin g) K).det *
      (D.md (A : Matrix (Fin g) (Fin g) K).det : ℂ) ^ m) • fun X => Φ (X * (A : Matrix (Fin g) (Fin g) K)) := by
    funext X; rfl
  rw [e]; exact h'

/-! ### Stability under multiplication by $\psi(\operatorname{tr}(B\,Q[X]))$ -/

lemma trace_QX (B : Matrix (Fin g) (Fin g) K) (X : PtG m g K) :
    trace (B * QX a X) = ∑ j, ∑ k, ∑ i, B j k * a i * X i k * X i j := by
  have hQ : ∀ k j, QX a X k j = ∑ i, X i k * a i * X i j := fun k j => by
    rw [QX, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_diagonal, Matrix.transpose_apply]
  simp only [trace, diag_apply, Matrix.mul_apply, hQ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring

lemma norm_trace_QX_sub_le (B : Matrix (Fin g) (Fin g) K) (X H : PtG m g K) {r δ : ℝ} (hr : 0 ≤ r)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hX : ∀ i j, ‖X i j‖ ≤ r) (hH : ∀ i j, ‖H i j‖ ≤ δ) :
    ‖trace (B * QX a (X + H)) - trace (B * QX a X)‖ ≤
      (∑ j, ∑ k, ‖B j k‖) * (∑ i, ‖(a i : K)‖) * ((r + 1) * δ) := by
  set NB : ℝ := ∑ j, ∑ k, ‖B j k‖ with hNB
  set Na : ℝ := ∑ i, ‖(a i : K)‖ with hNa
  have hNB0 : 0 ≤ NB := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hNa0 : 0 ≤ Na := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hdiff : trace (B * QX a (X + H)) - trace (B * QX a X) =
      ∑ j, ∑ k, ∑ i, B j k * a i * (X i k * H i j + H i k * X i j + H i k * H i j) := by
    rw [trace_QX, trace_QX, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.add_apply]
    ring
  rw [hdiff]
  have hC : 0 ≤ NB * Na * ((r + 1) * δ) := by positivity
  refine norm_sum_le_ult _ _ hC fun j _ => norm_sum_le_ult _ _ hC fun k _ => norm_sum_le_ult _ _ hC fun i _ => ?_
  have hu : ‖X i k * H i j + H i k * X i j + H i k * H i j‖ ≤ (r + 1) * δ := by
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le ?_ ?_)) ?_)
    · rw [norm_mul]
      calc ‖X i k‖ * ‖H i j‖ ≤ r * δ := mul_le_mul (hX i k) (hH i j) (norm_nonneg _) hr
        _ ≤ (r + 1) * δ := by nlinarith
    · rw [norm_mul]
      calc ‖H i k‖ * ‖X i j‖ ≤ δ * r := mul_le_mul (hH i k) (hX i j) (norm_nonneg _) hδ0
        _ ≤ (r + 1) * δ := by nlinarith
    · rw [norm_mul]
      calc ‖H i k‖ * ‖H i j‖ ≤ δ * δ := mul_le_mul (hH i k) (hH i j) (norm_nonneg _) hδ0
        _ ≤ (r + 1) * δ := by nlinarith
  have hBa : ‖B j k‖ ≤ NB := entry_le_sum B j k
  have haa : ‖(a i : K)‖ ≤ Na :=
    Finset.single_le_sum (f := fun i => ‖(a i : K)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  rw [norm_mul, norm_mul]
  exact mul_le_mul (mul_le_mul hBa haa (norm_nonneg _) hNB0) hu (norm_nonneg _) (by positivity)

lemma SBG_opNg {Φ : PtG m g K → ℂ} (hψ : Analysis.Weil.IsStdChar D.ψ) (hΦ : Φ ∈ SBG K m g)
    (B : Matrix (Fin g) (Fin g) K) : opNg D a B Φ ∈ SBG K m g := by
  obtain ⟨R, ε, hε, hR, hinv⟩ := hΦ
  obtain ⟨ρ, hρ, hρ1⟩ := hψ.triv
  set NB : ℝ := ∑ j, ∑ k, ‖B j k‖ with hNB
  set Na : ℝ := ∑ i, ‖(a i : K)‖ with hNa
  have hNB0 : 0 ≤ NB := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hNa0 : 0 ≤ Na := Finset.sum_nonneg fun _ _ => norm_nonneg _
  set M : ℝ := NB * Na * (|R| + 1) with hM
  have hM0 : 0 ≤ M := by positivity
  set δ : ℝ := min ε (min 1 (ρ / (M + 1))) with hδ
  have hδpos : 0 < δ := lt_min hε (lt_min one_pos (div_pos hρ (by positivity)))
  have hδε : δ ≤ ε := min_le_left _ _
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hδρ : δ ≤ ρ / (M + 1) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨R, δ, hδpos, fun X hX => hR X fun h => hX (by simp [opNg, h]), fun X H hH => ?_⟩
  have hΦ' : Φ (X + H) = Φ X := hinv X H fun i j => (hH i j).trans hδε
  by_cases hX0 : Φ X = 0
  · simp [opNg, hΦ', hX0]
  have hXb : ∀ i j, ‖X i j‖ ≤ |R| := fun i j => (hR X hX0 i j).trans (le_abs_self _)
  have hsmall := norm_trace_QX_sub_le (a := a) B X H (abs_nonneg R) hδpos.le hδ1 hXb hH
  have hle : (∑ j, ∑ k, ‖B j k‖) * (∑ i, ‖(a i : K)‖) * ((|R| + 1) * δ) ≤ ρ := by
    have : NB * Na * ((|R| + 1) * δ) = M * δ := by rw [hM]; ring
    rw [show (∑ j, ∑ k, ‖B j k‖) * (∑ i, ‖(a i : K)‖) * ((|R| + 1) * δ) = M * δ from this]
    calc M * δ ≤ M * (ρ / (M + 1)) := by gcongr
      _ = ρ * (M / (M + 1)) := by ring
      _ ≤ ρ * 1 := by
        gcongr
        rw [div_le_one (by positivity)]; linarith
      _ = ρ := mul_one _
  have hψΔ := hρ1 _ (hsmall.trans hle)
  show (D.ψ (trace (B * QX a (X + H))) : ℂ) * Φ (X + H) = (D.ψ (trace (B * QX a X)) : ℂ) * Φ X
  rw [hΦ', show trace (B * QX a (X + H)) = trace (B * QX a X) +
    (trace (B * QX a (X + H)) - trace (B * QX a X)) by ring, AddChar.map_add_eq_mul, hψΔ, mul_one]

/-- **Stability under $\omega(n(B))$.** At a non-archimedean place, $\mathcal S(V^g)$ is stable under
$\Phi \mapsto \psi(\operatorname{tr}(B\,Q[X]))\Phi(X)$ for every $B \in M_g(K)$ (hypotheses `hS : D.S = SBK K` and
`hψ : Analysis.Weil.IsStdChar D.ψ`; $\psi$ is trivial on a small ball and $\operatorname{tr}(B\,Q[X + H]) - \operatorname{tr}(B\,Q[X])$
is small for $X$ in a bounded box and $H$ small). -/
@[kb "weil1964" "§14 ($\\mathcal S(X)$ for a finite-dimensional $X$ over a $\\mathfrak p$-adic field) [unverified]"]
theorem opNg_mem_Sg_nonarch (hS : D.S = SBK K) (hψ : Analysis.Weil.IsStdChar D.ψ)
    (B : Matrix (Fin g) (Fin g) K) {Φ : PtG m g K → ℂ} (hΦ : Φ ∈ Sg D m g) :
    opNg D a B Φ ∈ Sg D m g := by
  rw [mem_Sg_iff hS] at hΦ ⊢
  exact SBG_opNg hψ hΦ B

end NonArch

end QuadFormsKB.WeilRep.Genus
