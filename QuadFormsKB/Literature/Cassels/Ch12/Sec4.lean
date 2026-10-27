/-
# Cassels, Chapter 12, §4: Siegel domains, and the finiteness theorems 1.2 and 1.4

Cassels, *Rational Quadratic Forms* (1978), Ch. 12, §4, pp. 266–269.

* Lemma 4.1 (`lemma_4_1`): in a Siegel domain $\mathcal S(\delta, \eta)$ the ratios of $h_j$, $f_{jj}$, $M_j$ are bounded
  in terms of $n, \delta, \eta$.
* Lemma 4.2 (`lemma_4_2`) and its Corollary (`lemma_4_2_cor`): the coordinates of minimal vectors $\vec{m}_J$ are
  bounded in terms of $n, \delta, \eta$.
* Theorem 1.4 (`thm_1_4`, stated in §1, p. 259, proved on p. 269, 12.p2): if $f(\vec{x})$ and $f(T\vec{x})$ lie in the
  same Siegel domain, $T$ integral unimodular, the entries of $T$ are bounded by $C(n, \delta, \eta)$.
* Theorem 1.2 (`thm_1_2`, §1, p. 256): the same for reduced forms, with a bound depending only on $n$ (from
  Lemma 1.3 and Theorem 1.4).
-/
import QuadFormsKB.Literature.Cassels.Ch12.Sec3

open Matrix

namespace QuadFormsKB.Reduction

variable {n : ℕ}

/-- Helper: the data of a Siegel-domain decomposition, with $\delta$ replaced by $D = \max(\delta, 1)$ and $\eta$ by
$E = \max(\eta, 0)$: $h_i > 0$, $h_i \le D^n h_j$ for $i \le j$, and $|c_{ij}| \le E$ for $i < j$. -/
private theorem siegel_data {δ η : ℝ} {F : Matrix (Fin n) (Fin n) ℝ} (hF : InSiegelDomain δ η F)
    {h : Fin n → ℝ} {c : Matrix (Fin n) (Fin n) ℝ} (hd : IsSqDecomp F h c) :
    (∀ i, 0 < h i) ∧ (∀ i j : Fin n, i ≤ j → h i ≤ max δ 1 ^ n * h j) ∧
      ∀ i j, i < j → |c i j| ≤ max η 0 := by
  obtain ⟨h', c', hd', hpos', hstep, hc'⟩ := hF
  obtain ⟨hh, hcc⟩ := IsSqDecomp.unique (hd'.posDef hpos') hd' hd
  subst hh
  subst hcc
  have hD1 : (1 : ℝ) ≤ max δ 1 := le_max_right _ _
  have chain : ∀ k : ℕ, ∀ i j : Fin n, i.val + k = j.val → h' i ≤ max δ 1 ^ k * h' j := by
    intro k
    induction k with
    | zero =>
      intro i j hij
      have : i = j := Fin.ext (by simpa using hij)
      subst this
      simp
    | succ k ih =>
      intro i j hij
      have hlt : i.val + 1 < n := by have := j.2; omega
      have h1 := hstep i ⟨i.val + 1, hlt⟩ rfl
      have h2 := ih ⟨i.val + 1, hlt⟩ j (by simp; omega)
      have h3 : δ * h' ⟨i.val + 1, hlt⟩ ≤ max δ 1 * h' ⟨i.val + 1, hlt⟩ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (hpos' _).le
      calc h' i ≤ δ * h' ⟨i.val + 1, hlt⟩ := h1
        _ ≤ max δ 1 * h' ⟨i.val + 1, hlt⟩ := h3
        _ ≤ max δ 1 * (max δ 1 ^ k * h' j) := mul_le_mul_of_nonneg_left h2 (by linarith)
        _ = max δ 1 ^ (k + 1) * h' j := by ring
  refine ⟨hpos', fun i j hij => ?_, fun i j hij => (hc' i j hij).trans (le_max_left _ _)⟩
  have hk := chain (j.val - i.val) i j (by have : i.val ≤ j.val := hij; omega)
  have hle : max δ 1 ^ (j.val - i.val) ≤ max δ 1 ^ n :=
    pow_le_pow_right₀ hD1 (by have := j.2; omega)
  exact hk.trans (mul_le_mul_of_nonneg_right hle (hpos' j).le)

/-- Helper: the real span of the standard vectors $e_i$, $i < j$. -/
private def lowSpan (j : Fin n) : Submodule ℝ (Fin n → ℝ) :=
  Submodule.span ℝ ((fun i : Fin n => (Pi.single i 1 : Fin n → ℝ)) '' Set.Iio j)

/-- Helper: `lowSpan j` has dimension at most `j`. -/
private theorem finrank_lowSpan_le (j : Fin n) : Module.finrank ℝ (lowSpan j) ≤ j.val := by
  have h := finrank_span_finset_le_card (R := ℝ)
    (Finset.image (fun i : Fin n => (Pi.single i 1 : Fin n → ℝ)) (Finset.Iio j))
  have h2 : Module.finrank ℝ (lowSpan j) ≤
      (Finset.image (fun i : Fin n => (Pi.single i 1 : Fin n → ℝ)) (Finset.Iio j)).card := by
    have e : ((Finset.image (fun i : Fin n => (Pi.single i 1 : Fin n → ℝ)) (Finset.Iio j) :
        Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) =
        (fun i : Fin n => (Pi.single i 1 : Fin n → ℝ)) '' Set.Iio j := by
      rw [Finset.coe_image, Finset.coe_Iio]
    unfold lowSpan
    rw [← e]
    exact h
  refine h2.trans ((Finset.card_image_le).trans ?_)
  simp [Fin.card_Iio]

/-- Helper: a real vector supported on the coordinates $< j$ lies in `lowSpan j`. -/
private theorem mem_lowSpan {j : Fin n} {x : Fin n → ℝ} (hx : ∀ k, j ≤ k → x k = 0) : x ∈ lowSpan j := by
  have hx' : x = ∑ i, Pi.single i (x i) := (Finset.univ_sum_single x).symm
  rw [hx']
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases hi : i < j
  · have : Pi.single i (x i) = x i • (Pi.single i 1 : Fin n → ℝ) := by
      ext k
      by_cases h : k = i <;> simp [Pi.single_apply, h]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  · have : x i = 0 := hx i (not_lt.1 hi)
    simp [this]

/-- Helper: an integral vector not in `lowSpan j` has a last nonzero coordinate `k ≥ j`. -/
private theorem exists_top_nonzero {j : Fin n} {a : Fin n → ℤ} (ha : cast a ∉ lowSpan j) :
    ∃ k, j ≤ k ∧ a k ≠ 0 ∧ ∀ i, k < i → a i = 0 := by
  classical
  have h0 : ∃ k0, j ≤ k0 ∧ a k0 ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact ha (mem_lowSpan fun k hk => by simp [hcon k hk])
  obtain ⟨k0, hk0, hak0⟩ := h0
  have hne : (Finset.univ.filter fun i => a i ≠ 0).Nonempty := ⟨k0, by simp [hak0]⟩
  refine ⟨(Finset.univ.filter fun i => a i ≠ 0).max' hne, ?_, ?_, ?_⟩
  · exact hk0.trans (Finset.le_max' _ _ (by simp [hak0]))
  · have := Finset.max'_mem _ hne
    simpa using this
  · intro i hi
    by_contra hai
    have : i ≤ (Finset.univ.filter fun i => a i ≠ 0).max' hne :=
      Finset.le_max' _ _ (by simp [hai])
    exact absurd hi (not_lt.2 this)

/-- Helper: if $f_{ii} \le M$ for all $i \le j$, then $M_j \le M$ ($e_0, \dots, e_j$ are $j+1$ independent
vectors of value $\le M$). -/
private theorem succMin_le_of_diag {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosDef) (j : Fin n) {M : ℝ}
    (hM : ∀ i, i ≤ j → F i i ≤ M) : succMin F j ≤ M := by
  by_contra hlt
  push_neg at hlt
  have hLI : LinearIndependent ℝ (fun i : Finset.Iic j => (Pi.basisFun ℝ (Fin n)) i.1) :=
    (Pi.basisFun ℝ (Fin n)).linearIndependent.comp _ Subtype.val_injective
  have hrk := finrank_span_eq_card hLI
  have hsub : Submodule.span ℝ (Set.range fun i : Finset.Iic j => (Pi.basisFun ℝ (Fin n)) i.1) ≤
      spanLT F (succMin F j) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    apply Submodule.subset_span
    refine ⟨Pi.single i.1 1, ?_, ?_⟩
    · show val F (cast (Pi.single i.1 1 : Fin n → ℤ)) < succMin F j
      rw [cast_single, val_single]
      exact (hM i.1 (Finset.mem_Iic.1 i.2)).trans_lt hlt
    · show _ = (Pi.basisFun ℝ (Fin n)) i.1
      rw [cast_single, Pi.basisFun_apply]
  have h1 := Submodule.finrank_mono hsub
  rw [hrk, Fintype.card_coe, Fin.card_Iic] at h1
  have h2 := (succMin_spec hF j).2
  omega

/-- **Lemma 4.1** (auxiliary form, explicit constants): with $D = \max(\delta,1)$, $E = \max(\eta,0)$ and
$K = n(1 + E^2D^n)$, we have $h_j \le f_{jj} \le Kh_j$, $h_j \le D^nM_j$ and $M_j \le KD^nh_j$. -/
private theorem lemma_4_1_aux {δ η : ℝ} {F : Matrix (Fin n) (Fin n) ℝ} (hF : InSiegelDomain δ η F)
    {h : Fin n → ℝ} {c : Matrix (Fin n) (Fin n) ℝ} (hd : IsSqDecomp F h c) (j : Fin n) :
    h j ≤ F j j ∧ F j j ≤ (n * (1 + max η 0 ^ 2 * max δ 1 ^ n)) * h j ∧
      h j ≤ max δ 1 ^ n * succMin F j ∧
      succMin F j ≤ (n * (1 + max η 0 ^ 2 * max δ 1 ^ n)) * max δ 1 ^ n * h j := by
  obtain ⟨hpos, hchain, hcb⟩ := siegel_data hF hd
  have hP := hF.posDef
  have hD1 : (1 : ℝ) ≤ max δ 1 := le_max_right _ _
  have hE0 : (0 : ℝ) ≤ max η 0 := le_max_right _ _
  have hDn : (1 : ℝ) ≤ max δ 1 ^ n := one_le_pow₀ hD1
  have hK0 : (0 : ℝ) ≤ n * (1 + max η 0 ^ 2 * max δ 1 ^ n) := by positivity
  have hb : ∀ j, F j j ≤ (n * (1 + max η 0 ^ 2 * max δ 1 ^ n)) * h j := by
    intro j
    rw [hd.diag_eq j]
    calc ∑ i ∈ Finset.Iic j, h i * c i j ^ 2
        ≤ ∑ i ∈ Finset.Iic j, (1 + max η 0 ^ 2 * max δ 1 ^ n) * h j := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hij : i ≤ j := Finset.mem_Iic.1 hi
          have hnn : 0 ≤ max η 0 ^ 2 * max δ 1 ^ n * h j := by have := hpos j; positivity
          rcases hij.lt_or_eq with hlt | rfl
          · have hc2 : c i j ^ 2 ≤ max η 0 ^ 2 := by
              have := pow_le_pow_left₀ (abs_nonneg _) (hcb i j hlt) 2
              rwa [sq_abs] at this
            calc h i * c i j ^ 2 ≤ (max δ 1 ^ n * h j) * max η 0 ^ 2 :=
                  mul_le_mul (hchain i j hlt.le) hc2 (sq_nonneg _) (by have := hpos j; positivity)
              _ = max η 0 ^ 2 * max δ 1 ^ n * h j := by ring
              _ ≤ _ := by nlinarith [hpos j]
          · rw [hd.2.1, one_pow, mul_one]
            nlinarith
      _ = ((Finset.Iic j).card : ℝ) * ((1 + max η 0 ^ 2 * max δ 1 ^ n) * h j) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ n * ((1 + max η 0 ^ 2 * max δ 1 ^ n) * h j) := by
          have hcard : ((Finset.Iic j).card : ℝ) ≤ n := by
            rw [Fin.card_Iic]; exact_mod_cast j.2
          have := hpos j
          gcongr
      _ = _ := by ring
  have ha : h j ≤ F j j := by
    rw [hd.diag_eq j]
    calc h j = h j * c j j ^ 2 := by rw [hd.2.1, one_pow, mul_one]
      _ ≤ _ := Finset.single_le_sum (f := fun i => h i * c i j ^ 2)
          (fun i _ => mul_nonneg (hpos i).le (sq_nonneg _)) (Finset.mem_Iic.2 le_rfl)
  have hc : succMin F j ≤ (n * (1 + max η 0 ^ 2 * max δ 1 ^ n)) * max δ 1 ^ n * h j := by
    refine succMin_le_of_diag hP j fun i hi => ?_
    calc F i i ≤ (n * (1 + max η 0 ^ 2 * max δ 1 ^ n)) * h i := hb i
      _ ≤ (n * (1 + max η 0 ^ 2 * max δ 1 ^ n)) * (max δ 1 ^ n * h j) :=
          mul_le_mul_of_nonneg_left (hchain i j hi) hK0
      _ = _ := by ring
  have hd' : h j ≤ max δ 1 ^ n * succMin F j := by
    obtain ⟨hs1, -⟩ := succMin_spec hP j
    by_contra hcon
    have hex : ∃ a : Fin n → ℤ, val F (cast a) ≤ succMin F j ∧ cast a ∉ lowSpan j := by
      by_contra hno
      push_neg at hno
      have hle : spanLE F (succMin F j) ≤ lowSpan j := by
        rw [spanLE, Submodule.span_le]
        rintro _ ⟨a, ha, rfl⟩
        exact hno a ha
      have := Submodule.finrank_mono hle
      have := finrank_lowSpan_le j
      omega
    obtain ⟨a, ha1, ha2⟩ := hex
    obtain ⟨k, hjk, hak, hz⟩ := exists_top_nonzero ha2
    have h1 := hd.val_ge (fun i => (hpos i).le) hak hz
    have h2 := hchain j k hjk
    apply hcon
    calc h j ≤ max δ 1 ^ n * h k := h2
      _ ≤ max δ 1 ^ n * succMin F j :=
          mul_le_mul_of_nonneg_left (h1.trans ha1) (by positivity)
  exact ⟨ha, hb j, hd', hc⟩

/-- **Lemma 4.1** (Cassels, Ch. 12, §4, pp. 266–267): for $n, \delta, \eta$ there is $C = C(n, \delta, \eta)$ such that
for every real form $f$ in the Siegel domain $\mathcal S(\delta, \eta)$, written as
$\sum_j h_j(x_j + c_{j,j+1}x_{j+1} + \cdots)^2$ (`IsSqDecomp`; the decomposition is unique), with successive minima
$M_j$, and every $j$:
$$h_j \le f_{jj} \le C h_j, \qquad C^{-1}h_j \le M_j \le C h_j.$$
So the ratio of any two of $h_j, f_{jj}, M_j$ is bounded in terms of $n, \delta, \eta$. *Update* (unneeded hypothesis): Cassels assumes $\delta \ge 1$
(p. 266); this is not needed since $\mathcal S(\delta, \eta) \subseteq \mathcal S(\max(\delta, 1), \eta)$. -/
@[kb "cassels1978" "Ch. 12, §4, Lemma 4.1, pp. 266–267"]
theorem lemma_4_1 (n : ℕ) (δ η : ℝ) : ∃ C : ℝ, 0 < C ∧ ∀ F : Matrix (Fin n) (Fin n) ℝ, InSiegelDomain δ η F →
    ∀ (h : Fin n → ℝ) (c : Matrix (Fin n) (Fin n) ℝ), IsSqDecomp F h c → ∀ j : Fin n,
      h j ≤ F j j ∧ F j j ≤ C * h j ∧ h j ≤ C * succMin F j ∧ succMin F j ≤ C * h j := by
  have hD1 : (1 : ℝ) ≤ max δ 1 := le_max_right _ _
  have hE0 : (0 : ℝ) ≤ max η 0 := le_max_right _ _
  have hDn : (1 : ℝ) ≤ max δ 1 ^ n := one_le_pow₀ hD1
  have hK0 : (0 : ℝ) ≤ n * (1 + max η 0 ^ 2 * max δ 1 ^ n) := by positivity
  refine ⟨(1 + n * (1 + max η 0 ^ 2 * max δ 1 ^ n)) * max δ 1 ^ n, by positivity, ?_⟩
  intro F hF h c hd j
  obtain ⟨ha, hb, hc, hd'⟩ := lemma_4_1_aux hF hd j
  obtain ⟨hpos, -, -⟩ := siegel_data hF hd
  have hj := hpos j
  have hM := (succMin_pos hF.posDef j)
  refine ⟨ha, ?_, ?_, ?_⟩
  · refine hb.trans (mul_le_mul_of_nonneg_right ?_ hj.le)
    nlinarith
  · refine hc.trans ?_
    nlinarith
  · refine hd'.trans (mul_le_mul_of_nonneg_right ?_ hj.le)
    nlinarith

/-- Helper: $(C e_v x)_u = c_{uv}x$. -/
private theorem mulVec_single' (c : Matrix (Fin n) (Fin n) ℝ) (v u : Fin n) (x : ℝ) :
    (c *ᵥ Pi.single v x) u = c u v * x := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- Helper (rounding, Cassels p. 268): for an upper unitriangular $c$, any real $\mu$ and any $i$ there is an
integral $t$ supported on $\{0, \dots, i\}$ with $|\mu_u + (ct)_u| \le 1/2$ for all $u \le i$. -/
private theorem exists_round {c : Matrix (Fin n) (Fin n) ℝ} (hc1 : ∀ i, c i i = 1)
    (hc0 : ∀ i j, j < i → c i j = 0) (μ : Fin n → ℝ) (i : Fin n) :
    ∃ t : Fin n → ℤ, (∀ u, i < u → t u = 0) ∧ ∀ u, u ≤ i → |μ u + (c *ᵥ cast t) u| ≤ 1 / 2 := by
  have key : ∀ r : ℕ, ∃ t : Fin n → ℤ, (∀ u, i < u → t u = 0) ∧
      ∀ u, u ≤ i → i.val < u.val + r → |μ u + (c *ᵥ cast t) u| ≤ 1 / 2 := by
    intro r
    induction r with
    | zero => exact ⟨0, fun _ _ => rfl, fun u hu h => by omega⟩
    | succ r ih =>
      obtain ⟨t, ht0, ht⟩ := ih
      by_cases hr : r ≤ i.val
      · obtain ⟨v, hv⟩ : ∃ v : Fin n, v.val = i.val - r := ⟨⟨i.val - r, by have := i.2; omega⟩, rfl⟩
        have hvi : v ≤ i := by rw [Fin.le_def]; omega
        obtain ⟨s, hs⟩ : ∃ s : ℤ, s = -round (μ v + (c *ᵥ cast t) v) := ⟨_, rfl⟩
        have hcast : cast (t + Pi.single v s) = cast t + Pi.single v (s : ℝ) := by
          funext k
          by_cases hk : k = v <;> simp [cast, Pi.single_apply, hk]
        have hval : ∀ u, (c *ᵥ cast (t + Pi.single v s)) u = (c *ᵥ cast t) u + c u v * s := by
          intro u
          rw [hcast, Matrix.mulVec_add, Pi.add_apply, mulVec_single']
        refine ⟨t + Pi.single v s, ?_, ?_⟩
        · intro u hu
          have hne : u ≠ v := fun h => absurd hu (by rw [h]; exact not_lt.2 hvi)
          simp [ht0 u hu, Pi.single_apply, hne]
        · intro u hu hlt
          rw [hval]
          rcases lt_trichotomy u v with h1 | h1 | h1
          · exfalso
            rw [Fin.lt_def] at h1
            omega
          · subst h1
            rw [hc1, hs]
            have := abs_sub_round (μ u + (c *ᵥ cast t) u)
            have e : μ u + ((c *ᵥ cast t) u + 1 * ((-round (μ u + (c *ᵥ cast t) u) : ℤ) : ℝ)) =
                μ u + (c *ᵥ cast t) u - round (μ u + (c *ᵥ cast t) u) := by push_cast; ring
            rw [e]; exact this
          · rw [hc0 u v h1, zero_mul, add_zero]
            apply ht u hu
            rw [Fin.lt_def] at h1
            omega
      · exact ⟨t, ht0, fun u hu h => ht u hu (by have := not_le.1 hr; omega)⟩
  obtain ⟨t, ht0, ht⟩ := key n
  exact ⟨t, ht0, fun u hu => ht u hu (by have := i.2; omega)⟩

/-- **Lemma 4.2** (Cassels, Ch. 12, §4, pp. 267–268): for $n, \delta, \eta$ there is $C_{14} = C_{14}(n, \delta, \eta)$ such
that for every real form $f \in \mathcal S(\delta, \eta)$ with decomposition $(h, c)$, every choice of linearly
independent integral $\vec{m}_0, \dots, \vec{m}_{n-1}$ with $f(\vec{m}_j) = M_j$, and all $i, J$, the number
$$\mu_i = m_{iJ} + c_{i,i+1}m_{i+1,J} + \cdots + c_{i,n-1}m_{n-1,J} \quad ((4.3\,\mathrm{bis}))$$
(the $i$-th coordinate of $C\vec{m}_J$, so that $M_J = \sum_i h_i\mu_i^2$, (4.4)) satisfies $|\mu_i| \le C_{14}$. Here
$m_{iJ}$ is the $i$-th coordinate of $\vec{m}_J$ (Cassels' (4.2)). The formulas (4.3 bis)–(4.4) are partly lost in the
machine-read text and were reconstructed from their use on p. 268. -/
@[kb "cassels1978" "Ch. 12, §4, Lemma 4.2, pp. 267–268"]
theorem lemma_4_2 (n : ℕ) (δ η : ℝ) : ∃ C : ℝ, ∀ F : Matrix (Fin n) (Fin n) ℝ, InSiegelDomain δ η F →
    ∀ (h : Fin n → ℝ) (c : Matrix (Fin n) (Fin n) ℝ), IsSqDecomp F h c →
      ∀ m : Fin n → Fin n → ℤ, LinearIndependent ℝ (fun j => cast (m j)) →
        (∀ j, val F (cast (m j)) = succMin F j) → ∀ i J : Fin n, |(c *ᵥ cast (m J)) i| ≤ C := by
  obtain ⟨C1, hC1pos, hC1⟩ := lemma_4_1 n δ η
  have hD1 : (1 : ℝ) ≤ max δ 1 := le_max_right _ _
  have hDn : (1 : ℝ) ≤ max δ 1 ^ n := one_le_pow₀ hD1
  refine ⟨C1 * max δ 1 ^ n + n * max δ 1 ^ n + 1, ?_⟩
  intro F hF h c hd m hLI hm i J
  obtain ⟨hpos, hchain, hcb⟩ := siegel_data hF hd
  have hP := hF.posDef
  obtain ⟨μ, hμ⟩ : ∃ μ : Fin n → ℝ, μ = c *ᵥ cast (m J) := ⟨_, rfl⟩
  rw [← hμ]
  have hMJ : succMin F J = ∑ u, h u * μ u ^ 2 := by
    rw [← hm J, val_eq_of_isSqDecomp hd, hμ]
  have hterm : h i * μ i ^ 2 ≤ succMin F J := by
    rw [hMJ]
    exact Finset.single_le_sum (f := fun u => h u * μ u ^ 2)
      (fun u _ => mul_nonneg (hpos u).le (sq_nonneg _)) (Finset.mem_univ i)
  have hnD : (0 : ℝ) ≤ n * max δ 1 ^ n := by positivity
  suffices hB : μ i ^ 2 ≤ C1 * max δ 1 ^ n + n * max δ 1 ^ n by
    have : |μ i| ≤ μ i ^ 2 + 1 := by nlinarith [sq_abs (μ i), sq_nonneg (|μ i| - 1)]
    linarith
  have hhi := hpos i
  by_cases hcase : ∃ u, u ≤ i ∧ succMin F J ≤ F u u
  · obtain ⟨u, hui, hu⟩ := hcase
    have h41 := hC1 F hF h c hd u
    have hle : succMin F J ≤ C1 * (max δ 1 ^ n * h i) :=
      calc succMin F J ≤ F u u := hu
        _ ≤ C1 * h u := h41.2.1
        _ ≤ C1 * (max δ 1 ^ n * h i) := mul_le_mul_of_nonneg_left (hchain u i hui) hC1pos.le
    have h1 : h i * μ i ^ 2 ≤ h i * (C1 * max δ 1 ^ n) := by
      calc h i * μ i ^ 2 ≤ _ := hterm.trans hle
        _ = _ := by ring
    have := le_of_mul_le_mul_left h1 hhi
    linarith
  · push_neg at hcase
    obtain ⟨t, ht0, htr⟩ := exists_round hd.2.1 hd.1 μ i
    obtain ⟨a, ha⟩ : ∃ a : Fin n → ℝ, a = c *ᵥ cast t := ⟨_, rfl⟩
    rw [← ha] at htr
    have ha0 : ∀ u, i < u → a u = 0 := by
      intro u hu
      rw [ha, Matrix.mulVec, dotProduct]
      refine Finset.sum_eq_zero fun v _ => ?_
      by_cases hv : v ≤ i
      · rw [hd.1 u v (lt_of_le_of_lt hv hu), zero_mul]
      · rw [show cast t v = 0 by simp [cast, ht0 v (not_le.1 hv)], mul_zero]
    -- the vector m_J + t has value >= M_J
    have hcastadd : cast (m J + t) = cast (m J) + cast t := by
      funext k; simp [cast]
    have hmstar : succMin F J ≤ val F (cast (m J + t)) := by
      by_contra hlt
      push_neg at hlt
      have hmem := mem_span_of_val_lt_succMin hP hLI hm (j := J) (c := m J + t) hlt
      have hsingle : ∀ u, u ≤ i → (Pi.single u 1 : Fin n → ℝ) ∈
          Submodule.span ℝ (Set.image (fun i => cast (m i)) {i | i < J}) := by
        intro u hu
        have := mem_span_of_val_lt_succMin hP hLI hm (j := J) (c := Pi.single u 1)
          (by rw [cast_single, val_single]; exact hcase u hu)
        rwa [cast_single] at this
      have htmem : cast t ∈ Submodule.span ℝ (Set.image (fun i => cast (m i)) {i | i < J}) := by
        have hx : cast t = ∑ u, Pi.single u (cast t u) := (Finset.univ_sum_single (cast t)).symm
        rw [hx]
        refine Submodule.sum_mem _ fun u _ => ?_
        by_cases hu : u ≤ i
        · have : Pi.single u (cast t u) = (cast t u) • (Pi.single u 1 : Fin n → ℝ) := by
            ext k
            by_cases hk : k = u <;> simp [Pi.single_apply, hk]
          rw [this]
          exact Submodule.smul_mem _ _ (hsingle u hu)
        · simp [cast, ht0 u (not_le.1 hu)]
      have hJ : cast (m J) ∈ Submodule.span ℝ (Set.image (fun i => cast (m i)) {i | i < J}) := by
        have : cast (m J) = cast (m J + t) - cast t := by rw [hcastadd]; abel
        rw [this]
        exact Submodule.sub_mem _ hmem htmem
      exact hLI.notMem_span_image (s := {i | i < J}) (x := J) (by simp) hJ
    have hval : val F (cast (m J + t)) = ∑ u, h u * (μ u + a u) ^ 2 := by
      rw [val_eq_of_isSqDecomp hd, hcastadd, Matrix.mulVec_add, ← hμ, ← ha]
      rfl
    rw [hval, hMJ] at hmstar
    have hg : ∑ u, (h u * (μ u + a u) ^ 2 - h u * μ u ^ 2) =
        ∑ u ∈ Finset.Iic i, (h u * (μ u + a u) ^ 2 - h u * μ u ^ 2) := by
      symm
      refine Finset.sum_subset (Finset.subset_univ _) fun u _ hu => ?_
      have : a u = 0 := ha0 u (by simpa using hu)
      simp [this]
    have hg0 : 0 ≤ ∑ u ∈ Finset.Iic i, (h u * (μ u + a u) ^ 2 - h u * μ u ^ 2) := by
      rw [← hg, Finset.sum_sub_distrib]
      linarith
    rw [Finset.sum_sub_distrib] at hg0
    have h2 : h i * μ i ^ 2 ≤ ∑ u ∈ Finset.Iic i, h u * μ u ^ 2 :=
      Finset.single_le_sum (f := fun u => h u * μ u ^ 2)
        (fun u _ => mul_nonneg (hpos u).le (sq_nonneg _)) (Finset.mem_Iic.2 le_rfl)
    have h3 : ∑ u ∈ Finset.Iic i, h u * (μ u + a u) ^ 2 ≤ ∑ u ∈ Finset.Iic i, max δ 1 ^ n * h i / 4 := by
      refine Finset.sum_le_sum fun u hu => ?_
      have hui := Finset.mem_Iic.1 hu
      have hq : (μ u + a u) ^ 2 ≤ 1 / 4 := by
        have := htr u hui
        have := abs_le.1 this
        nlinarith
      calc h u * (μ u + a u) ^ 2 ≤ h u * (1 / 4) :=
            mul_le_mul_of_nonneg_left hq (hpos u).le
        _ = h u / 4 := by ring
        _ ≤ max δ 1 ^ n * h i / 4 := by
            have := hchain u i hui
            linarith
    have h4 : ∑ u ∈ Finset.Iic i, max δ 1 ^ n * h i / 4 ≤ n * max δ 1 ^ n * h i / 4 := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard : ((Finset.Iic i).card : ℝ) ≤ n := by
        rw [Fin.card_Iic]; exact_mod_cast i.2
      have : 0 ≤ max δ 1 ^ n * h i := by positivity
      nlinarith
    have h5 : h i * μ i ^ 2 ≤ h i * (n * max δ 1 ^ n) := by
      nlinarith
    have := le_of_mul_le_mul_left h5 hhi
    have : 0 ≤ C1 * max δ 1 ^ n := by positivity
    linarith

/-- **Lemma 4.2, Corollary** (Cassels, Ch. 12, §4, pp. 268–269): under the hypotheses of Lemma 4.2 the coordinates
of the minimal vectors are bounded: $|m_{iJ}| \le C_{15}(n, \delta, \eta)$. -/
@[kb "cassels1978" "Ch. 12, §4, Lemma 4.2, Corollary, pp. 268–269"]
theorem lemma_4_2_cor (n : ℕ) (δ η : ℝ) : ∃ C : ℝ, ∀ F : Matrix (Fin n) (Fin n) ℝ, InSiegelDomain δ η F →
    ∀ m : Fin n → Fin n → ℤ, LinearIndependent ℝ (fun j => cast (m j)) →
      (∀ j, val F (cast (m j)) = succMin F j) → ∀ i J : Fin n, |(m J i : ℝ)| ≤ C := by
  obtain ⟨C14, hC14⟩ := lemma_4_2 n δ η
  have hE0 : (0 : ℝ) ≤ max η 0 := le_max_right _ _
  refine ⟨max C14 0 * (1 + n * max η 0) ^ n, ?_⟩
  intro F hF m hLI hm i0 J
  obtain ⟨h, c, hd, hpos, hstep, hc'⟩ := id hF
  have hcb : ∀ i j, i < j → |c i j| ≤ max η 0 := fun i j hij => (hc' i j hij).trans (le_max_left _ _)
  have hμ : ∀ i, |(c *ᵥ cast (m J)) i| ≤ max C14 0 := fun i =>
    (hC14 F hF h c hd m hLI hm i J).trans (le_max_left _ _)
  have hq : (1 : ℝ) ≤ 1 + n * max η 0 := by
    have : (0 : ℝ) ≤ n * max η 0 := by positivity
    linarith
  have hA : (0 : ℝ) ≤ max C14 0 := le_max_right _ _
  have hsplit : ∀ i, (c *ᵥ cast (m J)) i =
      (m J i : ℝ) + ∑ k ∈ Finset.Ioi i, c i k * (m J k : ℝ) := by
    intro i
    rw [Matrix.mulVec, dotProduct]
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.Ici i)), ← Finset.Ioi_insert,
      Finset.sum_insert Finset.notMem_Ioi_self, hd.2.1]
    · simp [cast]
    · intro k _ hk
      have : c i k = 0 := hd.1 i k (by simpa using hk)
      rw [this, zero_mul]
  have key : ∀ r : ℕ, ∀ i : Fin n, n ≤ i.val + r → |(m J i : ℝ)| ≤ max C14 0 * (1 + n * max η 0) ^ r := by
    intro r
    induction r with
    | zero => intro i hi; have := i.2; omega
    | succ r ih =>
      intro i hi
      have hsum : |∑ k ∈ Finset.Ioi i, c i k * (m J k : ℝ)| ≤
          ∑ k ∈ Finset.Ioi i, max η 0 * (max C14 0 * (1 + n * max η 0) ^ r) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
        have hik : i < k := Finset.mem_Ioi.1 hk
        rw [abs_mul]
        exact mul_le_mul (hcb i k hik) (ih k (by rw [Fin.lt_def] at hik; omega)) (abs_nonneg _) hE0
      have hcard : ((Finset.Ioi i).card : ℝ) ≤ n := by
        rw [Fin.card_Ioi]; have := i.2; exact_mod_cast (by omega : n - 1 - i.val ≤ n)
      have hpow : (1 : ℝ) ≤ (1 + n * max η 0) ^ r := one_le_pow₀ hq
      have hsum2 : ∑ k ∈ Finset.Ioi i, max η 0 * (max C14 0 * (1 + n * max η 0) ^ r) ≤
          n * max η 0 * (max C14 0 * (1 + n * max η 0) ^ r) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have : 0 ≤ max η 0 * (max C14 0 * (1 + n * max η 0) ^ r) := by positivity
        nlinarith
      have hx : (m J i : ℝ) = (c *ᵥ cast (m J)) i - ∑ k ∈ Finset.Ioi i, c i k * (m J k : ℝ) := by
        rw [hsplit i]; ring
      have hle : |(m J i : ℝ)| ≤ |(c *ᵥ cast (m J)) i| + |∑ k ∈ Finset.Ioi i, c i k * (m J k : ℝ)| := by
        rw [hx]; exact abs_sub _ _
      have := hμ i
      have hAq : max C14 0 ≤ max C14 0 * (1 + n * max η 0) ^ r := by nlinarith
      calc |(m J i : ℝ)| ≤ max C14 0 + n * max η 0 * (max C14 0 * (1 + n * max η 0) ^ r) := by
            linarith
        _ ≤ max C14 0 * (1 + n * max η 0) ^ (r + 1) := by
            rw [pow_succ]; nlinarith
  exact key n i0 (by omega)

/-- Helper: $\mathrm{span}\{\vec m : f(T\vec m) \le M\} = T^{-1}\,\mathrm{span}\{\vec m : f(\vec m) \le M\}$. -/
private theorem spanLE_act (T : GL (Fin n) ℤ) (F : Matrix (Fin n) (Fin n) ℝ) (M : ℝ) :
    spanLE (act T.val F) M =
      (spanLE F M).map (Matrix.mulVecLin (castM (T⁻¹ : GL (Fin n) ℤ).val)) := by
  unfold spanLE
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨m, hm, rfl⟩
    refine ⟨cast (T.val *ᵥ m), ⟨T.val *ᵥ m, ?_, rfl⟩, ?_⟩
    · show val F _ ≤ M
      rw [← val_act_cast]; exact hm
    · simp only [Matrix.mulVecLin_apply]
      rw [castM_mulVec_cast, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    refine ⟨(T⁻¹ : GL (Fin n) ℤ).val *ᵥ m, ?_, ?_⟩
    · show val (act T.val F) _ ≤ M
      rw [val_act_cast, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]; exact hm
    · simp only [Matrix.mulVecLin_apply]
      rw [castM_mulVec_cast]

/-- Helper: the successive minima are invariant under integral unimodular substitution,
$M_j(f(T\vec x)) = M_j(f)$. -/
private theorem succMin_act (T : GL (Fin n) ℤ) (F : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    succMin (act T.val F) j = succMin F j := by
  unfold succMin
  congr 1
  ext M
  simp only [Set.mem_setOf_eq]
  rw [spanLE_act, ← (Submodule.equivMapOfInjective _ (injective_castM_inv T) (spanLE F M)).finrank_eq]

/-- **Theorem 1.4** (Cassels, Ch. 12, §1, p. 259; proved in §4, p. 269): for $n, \delta, \eta$ there is
$C = C(n, \delta, \eta)$ such that whenever $f(\vec{x})$ and $f(T\vec{x})$ are both in the Siegel domain
$\mathcal S(\delta, \eta)$, with $T = (t_{ij})$ integral unimodular, $|t_{ij}| \le C$ for all $i, j$. *Proof*
(Cassels'): the minimal vectors have bounded coordinates in both bases (Corollary to Lemma 4.2); eliminating them
expresses one basis in the other with bounded rational, hence integral, coefficients. -/
@[kb "cassels1978" "Ch. 12, §1, Thm. 1.4, p. 259; proof in §4, p. 269"]
theorem thm_1_4 (n : ℕ) (δ η : ℝ) : ∃ C : ℝ, ∀ (F : Matrix (Fin n) (Fin n) ℝ) (T : GL (Fin n) ℤ),
    InSiegelDomain δ η F → InSiegelDomain δ η (act T.val F) → ∀ i j, |(T.val i j : ℝ)| ≤ C := by
  obtain ⟨C15, hC15⟩ := lemma_4_2_cor n δ η
  have hK1 : (1 : ℝ) ≤ max C15 1 := le_max_right _ _
  refine ⟨n * (max C15 1 * ((n.factorial : ℝ) * max C15 1 ^ n)), ?_⟩
  intro F T hF hG i j
  obtain ⟨m, hLI, hm⟩ := exists_succMin_vectors hF.posDef
  obtain ⟨m', hm'def⟩ : ∃ m' : Fin n → Fin n → ℤ, m' = fun k => (T⁻¹ : GL (Fin n) ℤ).val *ᵥ m k := ⟨_, rfl⟩
  have hTm' : ∀ k, T.val *ᵥ m' k = m k := by
    intro k; rw [hm'def]; simp [Matrix.mulVec_mulVec]
  have hLI' : LinearIndependent ℝ (fun k => cast (m' k)) := by
    refine LinearIndependent.of_comp (Matrix.mulVecLin (castM T.val)) ?_
    convert hLI using 1
    funext k
    simp only [Function.comp, Matrix.mulVecLin_apply, castM_mulVec_cast, hTm']
  have hm'' : ∀ k, val (act T.val F) (cast (m' k)) = succMin (act T.val F) k := by
    intro k; rw [val_act_cast, hTm', hm k, succMin_act]
  have hb := hC15 F hF m hLI hm
  have hb' := hC15 _ hG m' hLI' hm''
  set K := max C15 1 with hK
  -- the matrices of minimal vectors
  set Pz : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun a b => m b a with hPz
  set Qz : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun a b => m' b a with hQz
  have hTQ : T.val * Qz = Pz := by
    ext a b
    have := congrFun (hTm' b) a
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, hPz, hQz] using this
  have hTQr : castM T.val * castM Qz = castM Pz := by
    rw [← castM_mul, hTQ]
  have hdetP : (castM Pz).det ≠ 0 := by
    have h1 : LinearIndependent ℝ (castM Pz).col := hLI
    have h2 := (Matrix.linearIndependent_col_iff_isUnit.1 h1)
    exact (isUnit_iff_ne_zero.1 ((Matrix.isUnit_iff_isUnit_det _).1 h2))
  have hdetQ : (castM Qz).det ≠ 0 := by
    intro h0
    apply hdetP
    rw [← hTQr, Matrix.det_mul, h0, mul_zero]
  have hcd : (castM Qz).det = ((Qz.det : ℤ) : ℝ) := by
    have := (Int.castRingHom ℝ).map_det Qz
    simpa [castM, RingHom.mapMatrix_apply] using this.symm
  have hdetQz : Qz.det ≠ 0 := by
    intro h0
    apply hdetQ
    rw [hcd, h0]; simp
  have hone : (1 : ℝ) ≤ |(castM Qz).det| := by
    rw [hcd]
    have := Int.one_le_abs hdetQz
    exact_mod_cast this
  -- adjugate identity
  have hid : (castM Qz).det • castM T.val = castM Pz * (castM Qz).adjugate := by
    rw [← hTQr, Matrix.mul_assoc, Matrix.mul_adjugate]
    simp
  have hentry : (castM Qz).det * (T.val i j : ℝ) = (castM Pz * (castM Qz).adjugate) i j := by
    have := congrFun (congrFun hid i) j
    simpa [castM] using this
  -- bounds on entries
  have hPb : ∀ a b, |castM Pz a b| ≤ K := fun a b => (hb a b).trans (le_max_left _ _)
  have hQb : ∀ a b, |castM Qz a b| ≤ K := fun a b => (hb' a b).trans (le_max_left _ _)
  have hadj : ∀ a b, |(castM Qz).adjugate a b| ≤ (n.factorial : ℝ) * K ^ n := by
    intro a b
    rw [Matrix.adjugate_apply]
    have := Matrix.det_le (A := (castM Qz).updateRow b (Pi.single a 1))
      (abv := AbsoluteValue.abs) (x := K) (fun p q => by
        show |(castM Qz).updateRow b (Pi.single a 1) p q| ≤ K
        rw [Matrix.updateRow_apply]
        split_ifs
        · by_cases h : q = a <;> simp [Pi.single_apply, h] <;> linarith
        · exact hQb p q)
    simpa [Fintype.card_fin, nsmul_eq_mul] using this
  have hprod : |(castM Pz * (castM Qz).adjugate) i j| ≤ n * (K * ((n.factorial : ℝ) * K ^ n)) := by
    rw [Matrix.mul_apply]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k, |castM Pz i k * (castM Qz).adjugate k j|
        ≤ ∑ k : Fin n, K * ((n.factorial : ℝ) * K ^ n) := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [abs_mul]
          exact mul_le_mul (hPb i k) (hadj k j) (abs_nonneg _) (by linarith)
      _ = _ := by simp
  have hfin : |(T.val i j : ℝ)| ≤ |(castM Qz).det| * |(T.val i j : ℝ)| :=
    le_mul_of_one_le_left (abs_nonneg _) hone
  rw [← abs_mul, hentry] at hfin
  exact hfin.trans hprod

/-- **Theorem 1.2** (Cassels, Ch. 12, §1, p. 256; "clearly follows from Lemma 1.3 and Theorem 1.4", p. 259): there is
$C_n$, depending only on $n$, such that whenever $f(\vec{x})$ and $f(T\vec{x})$ are both Minkowski-reduced, with
$T = (t_{ij})$ integral unimodular, $|t_{ij}| \le C_n$. -/
@[kb "cassels1978" "Ch. 12, §1, Thm. 1.2, p. 256 (from Lemma 1.3 and Thm. 1.4, p. 259)"]
theorem thm_1_2 (n : ℕ) : ∃ C : ℝ, ∀ (F : Matrix (Fin n) (Fin n) ℝ) (T : GL (Fin n) ℤ),
    IsMinkowskiReduced F → IsMinkowskiReduced (act T.val F) → ∀ i j, |(T.val i j : ℝ)| ≤ C := by
  obtain ⟨δ, η, hR⟩ := exists_siegelDomain_of_isMinkowskiReduced n
  obtain ⟨C, hC⟩ := thm_1_4 n δ η
  exact ⟨C, fun F T hF hT => hC F T (hR F hF) (hR _ hT)⟩

/-- **Finiteness of the unimodular $T$ between reduced forms** (Cassels, Ch. 12, Thm. 1.2, used for $W_j$ on p. 272
and for $\Sigma$ in Thm. 7.7, p. 278): only finitely many $T \in \mathrm{GL}_n(\mathbb{Z})$ take some reduced form to a
reduced form. -/
theorem finite_gl_reduced_pair (n : ℕ) :
    {T : GL (Fin n) ℤ | ∃ F, IsMinkowskiReduced F ∧ IsMinkowskiReduced (act T.val F)}.Finite := by
  obtain ⟨C, hC⟩ := thm_1_2 n
  have hB : {A : Fin n → Fin n → ℤ | ∀ i j, A i j ∈ Set.Icc (-⌈C⌉) ⌈C⌉}.Finite := by
    have : {A : Fin n → Fin n → ℤ | ∀ i j, A i j ∈ Set.Icc (-⌈C⌉) ⌈C⌉} =
        Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.Icc (-⌈C⌉) ⌈C⌉ := by
      ext A
      simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
    rw [this]
    exact Set.Finite.pi fun _ => Set.Finite.pi fun _ => Set.finite_Icc _ _
  have hpre := Set.Finite.preimage (f := fun T : GL (Fin n) ℤ => (T.val : Fin n → Fin n → ℤ))
    (Set.injOn_of_injective Units.val_injective) hB
  refine hpre.subset ?_
  rintro T ⟨F, hF, hT⟩
  intro i j
  have h := abs_le.1 (hC F T hF hT i j)
  have h1 : (T.val i j : ℝ) ≤ ⌈C⌉ := h.2.trans (Int.le_ceil C)
  have h2 : (-⌈C⌉ : ℝ) ≤ T.val i j := by
    have := Int.le_ceil C
    linarith [h.1]
  exact ⟨by exact_mod_cast h2, by exact_mod_cast h1⟩

end QuadFormsKB.Reduction
