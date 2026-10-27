/-
# Cassels, Chapter 12, §1: Minkowski-reduced forms and Siegel domains

Cassels, *Rational Quadratic Forms* (1978), Ch. 12, §1, pp. 255–260.

* `IsMinkowskiReduced`: the definition of a reduced form (p. 255, (1.2)), and its gcd form (1.3)–(1.4)
  (`isMinkowskiReduced_iff_gcd`).
* Lemma 1.1 (`IsMinkowskiReduced.diag_mono`, `IsMinkowskiReduced.abs_two_mul_le`).
* Theorem 1.1 (`exists_isMinkowskiReduced`, `finite_isMinkowskiReduced`): every strictly positive definite form is
  equivalent to at least one and at most finitely many reduced forms. Cassels says the finiteness is immediate; it is
  proved here from the inequality $f_{jj} \le (9/4)^j M$ (`IsMinkowskiReduced.diag_le_of_linearIndependent`), which
  is Cassels' argument for Thm. 3.1 (ii), pp. 263–264, with the constant computed.
* The Siegel domain $\mathcal S(\delta, \eta)$ (`InSiegelDomain`, p. 259).

Indices are 0-based: Cassels' $e_1, \dots, e_n$, $f_{11}, \dots$ are $e_0, \dots, e_{n-1}$, $f_{00}, \dots$ here.
-/
import QuadFormsKB.Literature.Cassels.Ch12.SquareDecomp

open Matrix

namespace QuadFormsKB.Reduction

variable {n : ℕ}

/-- Helper: a vector with coordinate `1` at a tail index has tail gcd `1`. -/
private theorem tailGcd_eq_one_of_coord {j k : Fin n} {b : Fin n → ℤ} (hk : j ≤ k) (hb : b k = 1) :
    tailGcd j b = 1 := by
  have h1 : tailGcd j b ∣ b k := Finset.gcd_dvd (Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩)
  rw [hb] at h1
  exact Int.eq_one_of_dvd_one (Int.nonneg_of_normalize_eq_self Finset.normalize_gcd) h1

/-- $f(e_j + c e_i) = f_{jj} + 2cf_{ji} + c^2f_{ii}$ for symmetric $F$. -/
theorem val_pair {F : Matrix (Fin n) (Fin n) ℝ} (hs : F.IsSymm) (i j : Fin n) (c : ℝ) :
    val F (Pi.single j 1 + c • (Pi.single i 1 : Fin n → ℝ)) = F j j + 2 * c * F j i + c ^ 2 * F i i := by
  rw [val_add hs, val_single]
  have h1 : val F (c • (Pi.single i 1 : Fin n → ℝ)) = c ^ 2 * F i i := by rw [val_smul, val_single]
  have h2 : (Pi.single j 1 : Fin n → ℝ) ⬝ᵥ (F *ᵥ (c • (Pi.single i 1 : Fin n → ℝ))) = c * F j i := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    ring
  rw [h1, h2]; ring

/-- **Minkowski-reduced form** (Cassels, Ch. 12, §1, Definition, p. 255, condition (1.2)): the real form $f$ with
matrix $F$ is strictly positive definite and, for each $j = 0, \dots, n-1$,
$$f(\vec{e}^{\,*}) \ge f(e_j) = f_{jj}$$
for every integral vector $\vec{e}^{\,*}$ such that $e_0, \dots, e_{j-1}, \vec{e}^{\,*}$ can be extended to a basis of
$\mathbb{Z}^n$ (`ExtendsBasis`). For $j = 0$, $\vec{e}^{\,*}$ runs through the primitive vectors. Cassels calls these forms
*reduced*; the Soviet "Hermite-reduced" of the Notes (p. 282) and Hermite's reduction (p. 259, `IsHermiteReduced`)
are different notions. Equivalent form with greatest common divisors: `isMinkowskiReduced_iff_gcd`. -/
@[kb "cassels1978" "Ch. 12, §1, Definition, (1.2), p. 255"]
def IsMinkowskiReduced (F : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  F.PosDef ∧ ∀ j : Fin n, ∀ e : Fin n → ℤ, ExtendsBasis j e → F j j ≤ val F (cast e)

/-- **Reduction by greatest common divisors** (Cassels, Ch. 12, (1.3)–(1.4), p. 255): $F$ is reduced iff it is strictly
positive definite and $f(b_0, \dots, b_{n-1}) \ge f_{jj}$ for every $j$ and all integers $b_0, \dots, b_{n-1}$ with
$\gcd(b_j, \dots, b_{n-1}) = 1$. -/
@[kb "cassels1978" "Ch. 12, §1, (1.3)–(1.4), p. 255"]
theorem isMinkowskiReduced_iff_gcd (F : Matrix (Fin n) (Fin n) ℝ) :
    IsMinkowskiReduced F ↔
      F.PosDef ∧ ∀ j : Fin n, ∀ b : Fin n → ℤ, tailGcd j b = 1 → F j j ≤ val F (cast b) := by
  unfold IsMinkowskiReduced
  simp only [extendsBasis_iff_gcd]

/-- **Lemma 1.1, (1.5)** (Cassels, Ch. 12, p. 255): the diagonal of a reduced form increases,
$f_{ii} \le f_{jj}$ for $i < j$ (take $\vec{e}^{\,*} = e_j$ at step $i$). -/
@[kb "cassels1978" "Ch. 12, §1, Lemma 1.1, (1.5), pp. 255–256"]
theorem IsMinkowskiReduced.diag_mono {F : Matrix (Fin n) (Fin n) ℝ} (hF : IsMinkowskiReduced F) {i j : Fin n}
    (hij : i ≤ j) : F i i ≤ F j j := by
  rcases hij.eq_or_lt with rfl | hlt
  · exact le_rfl
  · have h := hF.2 i (Pi.single j 1) ((extendsBasis_iff_gcd _ _).2
      (tailGcd_eq_one_of_coord (k := j) hlt.le (by simp)))
    rwa [cast_single, val_single] at h

/-- **Lemma 1.1, (1.6)** (Cassels, Ch. 12, p. 256): for a reduced form, $|2f_{ij}| \le f_{ii}$ for $i < j$
(take $\vec{e}^{\,*} = e_j \pm e_i$ at step $j$). -/
@[kb "cassels1978" "Ch. 12, §1, Lemma 1.1, (1.6), p. 256"]
theorem IsMinkowskiReduced.abs_two_mul_le {F : Matrix (Fin n) (Fin n) ℝ} (hF : IsMinkowskiReduced F) {i j : Fin n}
    (hij : i < j) : |2 * F i j| ≤ F i i := by
  have hs : F.IsSymm := ((posDef_iff F).1 hF.1).1
  have hsym : F j i = F i j := by
    have : Fᵀ = F := hs
    simpa using congrFun (congrFun this i) j
  have key : ∀ c : ℤ, c = 1 ∨ c = -1 → F j j ≤ F j j + 2 * (c : ℝ) * F j i + (c : ℝ) ^ 2 * F i i := by
    intro c hc
    have hx : cast ((Pi.single j 1 : Fin n → ℤ) + c • Pi.single i 1) =
        (Pi.single j 1 : Fin n → ℝ) + (c : ℝ) • (Pi.single i 1 : Fin n → ℝ) := by
      funext k
      by_cases h1 : k = j
      · subst h1
        have : k ≠ i := hij.ne'
        simp [cast, Pi.single_apply, this]
      · by_cases h2 : k = i <;> simp [cast, Pi.single_apply, h1, h2]
    have hg : tailGcd j ((Pi.single j 1 : Fin n → ℤ) + c • Pi.single i 1) = 1 := by
      apply tailGcd_eq_one_of_coord (k := j) le_rfl
      simp [Pi.single_apply, hij.ne']
    have h := hF.2 j _ ((extendsBasis_iff_gcd _ _).2 hg)
    rwa [hx, val_pair hs] at h
  have h1 := key 1 (Or.inl rfl)
  have h2 := key (-1) (Or.inr rfl)
  push_cast at h1 h2
  rw [abs_le]
  constructor <;> nlinarith

/-- **The key inequality for reduced forms** (Cassels, Ch. 12, proof of Thm. 3.1 (ii), (3.3), p. 264): if $f$ is reduced
and the integral vector $\vec{u}$ is not in the span of $e_0, \dots, e_{j-1}$ (some $u_k \ne 0$ with $k \ge j$), then
$$\sqrt{f_{jj}} \le \sqrt{f(\vec{u})} + \tfrac12\sum_{i < j}\sqrt{f_{ii}}.$$
*Proof:* $\vec{u} = s\vec{e}^{\,*} + \sum_{i<j}t_ie_i$ with $\vec{e}^{\,*}$ extending $e_0, \dots, e_{j-1}$, $s \ge 1$ and
$|t_i| \le s/2$ (`exists_extendsBasis_decomp`); then (1.9) and $f_{jj} \le f(\vec{e}^{\,*})$. -/
@[kb "cassels1978" "Ch. 12, §3, proof of Thm. 3.1 (ii), (3.3), p. 264"]
theorem IsMinkowskiReduced.sqrt_diag_le {F : Matrix (Fin n) (Fin n) ℝ} (hF : IsMinkowskiReduced F) {j : Fin n}
    {u : Fin n → ℤ} (hu : ∃ k, j ≤ k ∧ u k ≠ 0) :
    Real.sqrt (F j j) ≤ Real.sqrt (val F (cast u)) + (1 / 2) * ∑ i ∈ Finset.Iio j, Real.sqrt (F i i) := by
  obtain ⟨s, e, t, hs, he, ht0, ht, hut⟩ := exists_extendsBasis_decomp hu
  have hsd : F.PosSemidef := hF.1.posSemidef
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hspos : (0 : ℝ) < s := by linarith
  have hdecomp : cast e = (1 / (s : ℝ)) • cast u +
      ∑ i ∈ Finset.Iio j, (-((t i : ℝ) / s)) • (Pi.single i 1 : Fin n → ℝ) := by
    funext k
    have hk : (u k : ℝ) = s * e k + t k := by
      have := congrFun hut k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
      exact_mod_cast this
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.single_apply, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_Iio, cast]
    by_cases hkj : k < j
    · rw [if_pos hkj, hk]
      field_simp
      ring
    · rw [if_neg hkj]
      have : (t k : ℝ) = 0 := by exact_mod_cast ht0 k (not_lt.1 hkj)
      rw [hk, this]
      field_simp
      ring
  have hcoef : ∀ i ∈ Finset.Iio j, |-((t i : ℝ) / s)| ≤ 1 / 2 := by
    intro i _
    rw [abs_neg, abs_div, abs_of_pos hspos, div_le_iff₀ hspos]
    have : 2 * |t i| ≤ s := ht i
    have : 2 * |(t i : ℝ)| ≤ s := by exact_mod_cast this
    linarith
  have hsq := Real.sqrt_nonneg (val F (cast u))
  calc Real.sqrt (F j j) ≤ Real.sqrt (val F (cast e)) := Real.sqrt_le_sqrt (hF.2 j e he)
    _ ≤ Real.sqrt (val F ((1 / (s : ℝ)) • cast u)) +
        Real.sqrt (val F (∑ i ∈ Finset.Iio j, (-((t i : ℝ) / s)) • (Pi.single i 1 : Fin n → ℝ))) := by
      rw [hdecomp]; exact sqrt_val_add_le hsd _ _
    _ ≤ Real.sqrt (val F (cast u)) + (1 / 2) * ∑ i ∈ Finset.Iio j, Real.sqrt (F i i) := by
      apply add_le_add
      · rw [sqrt_val_smul, abs_of_pos (by positivity)]
        have : 1 / (s : ℝ) ≤ 1 := by rw [div_le_one hspos]; exact hs1
        exact mul_le_of_le_one_left hsq this
      · refine (sqrt_val_sum_le hsd _ _ _).trans ?_
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i hi
        rw [val_single]
        exact mul_le_mul_of_nonneg_right (hcoef i hi) (Real.sqrt_nonneg _)

/-- Helper: a sum over `Iio j` of a function of the index value is a sum over `range j`. -/
private theorem sum_Iio_val (j : Fin n) (g : ℕ → ℝ) :
    ∑ i ∈ Finset.Iio j, g i.val = ∑ i ∈ Finset.range j.val, g i := by
  have hj := j.2
  apply Finset.sum_bij (fun i _ => i.val)
  · intro i hi
    exact Finset.mem_range.2 (Fin.lt_def.1 (Finset.mem_Iio.1 hi))
  · intro a _ b _ h
    exact Fin.ext h
  · intro b hb
    have hb' := Finset.mem_range.1 hb
    exact ⟨⟨b, by omega⟩, Finset.mem_Iio.2 (Fin.lt_def.2 hb'), rfl⟩
  · intro i _
    rfl

/-- Helper: the geometric sum $\sum_{i<j}(3/2)^i = 2((3/2)^j - 1)$. -/
private theorem geom_three_halves (j : ℕ) :
    ∑ i ∈ Finset.range j, (3 / 2 : ℝ) ^ i = 2 * ((3 / 2 : ℝ) ^ j - 1) := by
  induction j with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

/-- Helper: the square-root form of the diagonal bound, by strong induction on $j$. -/
private theorem diag_aux {F : Matrix (Fin n) (Fin n) ℝ} (hF : IsMinkowskiReduced F) :
    ∀ (m : ℕ) (j : Fin n), j.val = m → ∀ (v : Fin (j.val + 1) → Fin n → ℤ),
      LinearIndependent ℝ (fun k => cast (v k)) → ∀ {M : ℝ}, (∀ k, val F (cast (v k)) ≤ M) →
        Real.sqrt (F j j) ≤ (3 / 2 : ℝ) ^ j.val * Real.sqrt M := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro j hjm v hv M hM
  have hex : ∃ k, ∃ l, j ≤ l ∧ v k l ≠ 0 := by
    by_contra hcon
    push Not at hcon
    let π : (Fin n → ℝ) →ₗ[ℝ] (Fin j.val → ℝ) := LinearMap.funLeft ℝ ℝ (Fin.castLE j.2.le)
    let W : Submodule ℝ (Fin n → ℝ) :=
      { carrier := {x | ∀ l, j ≤ l → x l = 0}
        add_mem' := fun ha hb l hl => by
          simp only [Pi.add_apply]; rw [ha l hl, hb l hl]; simp
        zero_mem' := fun l _ => rfl
        smul_mem' := fun c x hx l hl => by
          simp only [Pi.smul_apply]; rw [hx l hl]; simp }
    have hspan : Submodule.span ℝ (Set.range fun k => cast (v k)) ≤ W := by
      apply Submodule.span_le.2
      rintro _ ⟨k, rfl⟩ l hl
      simp [cast, hcon k l hl]
    have hdisj : Disjoint (Submodule.span ℝ (Set.range fun k => cast (v k))) (LinearMap.ker π) := by
      rw [Submodule.disjoint_def]
      intro x hx hxk
      have htail : ∀ l, j ≤ l → x l = 0 := hspan hx
      funext l
      by_cases hl : j ≤ l
      · exact htail l hl
      · have hl' : l.val < j.val := Fin.lt_def.1 (not_le.1 hl)
        have := congrFun (LinearMap.mem_ker.1 hxk) ⟨l.val, hl'⟩
        simpa [π, LinearMap.funLeft] using this
    have hind := hv.map hdisj
    have := hind.fintype_card_le_finrank
    simp at this
  obtain ⟨k, l, hl, hne⟩ := hex
  have hsd := hF.1.posSemidef
  have hu := hF.sqrt_diag_le (j := j) ⟨l, hl, hne⟩
  have hsM : Real.sqrt (val F (cast (v k))) ≤ Real.sqrt M := Real.sqrt_le_sqrt (hM k)
  have hsum : ∑ i ∈ Finset.Iio j, Real.sqrt (F i i) ≤
      (∑ i ∈ Finset.Iio j, (3 / 2 : ℝ) ^ i.val) * Real.sqrt M := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    have hij : i.val < j.val := Fin.lt_def.1 (Finset.mem_Iio.1 hi)
    have hle : i.val + 1 ≤ j.val + 1 := by omega
    exact ih i.val (by omega) i rfl (fun k' => v (Fin.castLE hle k'))
      (hv.comp _ (Fin.castLE_injective hle)) (fun k' => hM _)
  rw [sum_Iio_val j (fun i => (3 / 2 : ℝ) ^ i), geom_three_halves] at hsum
  have hMs := Real.sqrt_nonneg M
  calc Real.sqrt (F j j) ≤ _ := hu
    _ ≤ Real.sqrt M + (1 / 2) * (2 * ((3 / 2 : ℝ) ^ j.val - 1) * Real.sqrt M) := by
      gcongr
    _ = (3 / 2 : ℝ) ^ j.val * Real.sqrt M := by ring

/-- **Bound for the diagonal of a reduced form** (Cassels, Ch. 12, Thm. 3.1 (ii) and its proof, pp. 263–264, with
the constant computed): if $f$ is reduced and $\vec{v}_0, \dots, \vec{v}_j$ are $j + 1$ integral vectors, linearly
independent over $\mathbb{R}$, with $f(\vec{v}_k) \le M$, then
$$f_{jj} \le (9/4)^j\,M.$$
(Cassels' $C_1(j)$ is $(9/4)^{j}$ here: by induction $\sqrt{f_{jj}} \le \sqrt M\,(1 + \tfrac12\sum_{i<j}(3/2)^i) =
(3/2)^j\sqrt M$.) -/
@[kb "cassels1978" "Ch. 12, §3, Thm. 3.1 (ii) and proof, pp. 263–264"]
theorem IsMinkowskiReduced.diag_le_of_linearIndependent {F : Matrix (Fin n) (Fin n) ℝ}
    (hF : IsMinkowskiReduced F) (j : Fin n) (v : Fin (j.val + 1) → Fin n → ℤ)
    (hv : LinearIndependent ℝ fun k => cast (v k)) {M : ℝ} (hM : ∀ k, val F (cast (v k)) ≤ M) :
    F j j ≤ (9 / 4 : ℝ) ^ j.val * M := by
  have h := diag_aux hF j.val j rfl v hv hM
  have hF0 : 0 ≤ F j j := by
    have := (posSemidef_iff F).1 hF.1.posSemidef |>.2 (Pi.single j 1)
    rwa [val_single] at this
  have hM0 : 0 ≤ M := (((posSemidef_iff F).1 hF.1.posSemidef).2 _).trans (hM 0)
  calc F j j = Real.sqrt (F j j) ^ 2 := (Real.sq_sqrt hF0).symm
    _ ≤ ((3 / 2 : ℝ) ^ j.val * Real.sqrt M) ^ 2 := by gcongr
    _ = (9 / 4 : ℝ) ^ j.val * M := by
      rw [mul_pow, Real.sq_sqrt hM0, ← pow_mul, mul_comm j.val 2, pow_mul]; norm_num

/-- The greedy construction of `exists_isMinkowskiReduced`, started at $k_0$: if $G$ satisfies the reduction
conditions at all indices $< k_0$, some $V \in \mathrm{GL}_n(\mathbb{Z})$ fixing columns $< k_0$ makes $V^{\mathsf T}GV$
satisfy them at all indices $< k$, for any $k \ge k_0$. -/
theorem exists_reduced_from {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) (k0 : ℕ)
    (h0 : ∀ j : Fin n, j.val < k0 → ∀ e, ExtendsBasis j e → G j j ≤ val G (cast e)) :
    ∀ k, k0 ≤ k → ∃ V : GL (Fin n) ℤ,
      (∀ i : Fin n, i.val < k0 → ∀ a, V.val a i = (Pi.single i 1 : Fin n → ℤ) a) ∧
      ∀ j : Fin n, j.val < k → ∀ e, ExtendsBasis j e → act V.val G j j ≤ val (act V.val G) (cast e) := by
  intro k hk0
  induction k, hk0 using Nat.le_induction with
  | base =>
    refine ⟨1, fun i _ a => ?_, fun j hj e he => ?_⟩
    · simp [Matrix.one_apply, Pi.single_apply]
    · rw [Units.val_one, act_one]; exact h0 j hj e he
  | succ k hk ih =>
    obtain ⟨T, hTfix, hT⟩ := ih
    by_cases hkn : n ≤ k
    · exact ⟨T, hTfix, fun j hj => hT j (by have := j.2; omega)⟩
    have hk' : k < n := not_le.1 hkn
    set j0 : Fin n := ⟨k, hk'⟩ with hj0
    obtain ⟨G', hG'⟩ : ∃ G', G' = act T.val G := ⟨_, rfl⟩
    rw [← hG'] at hT
    have hGp : G'.PosDef := hG' ▸ PosDef.act hG T
    set A : Set (Fin n → ℤ) := {e | ExtendsBasis j0 e ∧ val G' (cast e) ≤ G' j0 j0} with hA
    have hfin : A.Finite := (finite_val_le hGp (G' j0 j0)).subset fun e he => he.2
    have hne : A.Nonempty :=
      ⟨Pi.single j0 1, extendsBasis_single j0, by rw [cast_single, val_single]⟩
    obtain ⟨e0, he0A, hmin⟩ := Set.exists_min_image A (fun e => val G' (cast e)) hfin hne
    have hmin' : ∀ e, ExtendsBasis j0 e → val G' (cast e0) ≤ val G' (cast e) := by
      intro e he
      by_cases h : val G' (cast e) ≤ G' j0 j0
      · exact hmin e ⟨he, h⟩
      · exact he0A.2.trans (not_le.1 h).le
    obtain ⟨U, hU1, hU2⟩ := he0A.1
    refine ⟨T * U, fun i hi a => ?_, fun j hj e he => ?_⟩
    · have hik : i < j0 := Fin.lt_def.2 (by show i.val < k; omega)
      rw [Units.val_mul, Matrix.mul_apply]
      simp only [hU1 i hik]
      simp [Pi.single_apply, hTfix i hi a]
    rw [Units.val_mul, act_mul]
    rw [← hG']
    rw [act_diag, val_act, castM_mulVec_cast]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hjk | hjk
    · have hcol : U.val *ᵥ Pi.single j 1 = Pi.single j 1 :=
        mulVec_single_of_col _ j (hU1 j (Fin.lt_def.2 hjk))
      rw [hcol, cast_single, val_single]
      exact hT j hjk (U.val *ᵥ e) (he.mulVec U (fun i hi => hU1 i (hi.trans (Fin.lt_def.2 hjk))))
    · have hjj : j = j0 := Fin.ext hjk
      subst hjj
      have hcol : U.val *ᵥ Pi.single j0 1 = e0 := by
        funext a
        simp [Matrix.mulVec, dotProduct, Pi.single_apply, hU2 a]
      rw [hcol]
      exact hmin' _ (he.mulVec U hU1)

/-- **Theorem 1.1, existence** (Cassels, Ch. 12, p. 256): every strictly positive definite real form is integrally
equivalent to a reduced form: there is $T \in \mathrm{GL}_n(\mathbb{Z})$ with $f(T\vec{x})$ reduced. *Proof* (Cassels'):
choose inductively $b_j$ minimizing $f$ among the vectors that extend $b_0, \dots, b_{j-1}$ to a basis ((1.7); the
minimum exists by `finite_val_le`). -/
@[kb "cassels1978" "Ch. 12, §1, Thm. 1.1, p. 256 (existence)"]
theorem exists_isMinkowskiReduced {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosDef) :
    ∃ T : GL (Fin n) ℤ, IsMinkowskiReduced (act T.val F) := by
  obtain ⟨T, -, hT⟩ := exists_reduced_from hF 0 (fun j hj => absurd hj (Nat.not_lt_zero _)) n (Nat.zero_le _)
  exact ⟨T, PosDef.act hF T, fun j e he => hT j j.2 e he⟩

/-- The columns $U\vec{e}_j$ of a unimodular $U$ with $f(U\vec{x})$ reduced satisfy
$f(U\vec{e}_j) \le (9/4)^n \sum_k f_{kk}$ (as in the finiteness part of Thm. 1.1, via Thm. 3.1 (ii) in the form
`IsMinkowskiReduced.diag_le_of_linearIndependent`, applied to the columns of $U^{-1}$, whose $f$-values are the
diagonal entries of $F$). -/
theorem columns_bound {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosDef) (T : GL (Fin n) ℤ)
    (hT : IsMinkowskiReduced (act T.val F)) (j : Fin n) :
    val F (cast (T.val *ᵥ Pi.single j 1)) ≤ (9 / 4 : ℝ) ^ n * ∑ k, F k k := by
  have hsd := hF.posSemidef
  have hdiag : ∀ k, 0 ≤ F k k := fun k => by
    have := ((posSemidef_iff F).1 hsd).2 (Pi.single k 1)
    rwa [val_single] at this
  set M : ℝ := ∑ k, F k k with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun k _ => hdiag k
  have hinj := injective_castM_inv T
  have hindep : LinearIndependent ℝ (fun a : Fin n => cast (T⁻¹.val *ᵥ Pi.single a 1)) := by
    have h1 := ((Pi.basisFun ℝ (Fin n)).linearIndependent).map' (Matrix.mulVecLin (castM T⁻¹.val))
      (LinearMap.ker_eq_bot.2 hinj)
    convert h1 using 1
    funext a
    rw [Function.comp_apply, Matrix.mulVecLin_apply, Pi.basisFun_apply, ← cast_single, castM_mulVec_cast]
  set v : Fin (j.val + 1) → Fin n → ℤ := fun k => T⁻¹.val *ᵥ Pi.single (Fin.castLE j.2 k) 1 with hv
  have hvi : LinearIndependent ℝ fun k => cast (v k) :=
    hindep.comp (Fin.castLE j.2) (Fin.castLE_injective _)
  have hvM : ∀ k, val (act T.val F) (cast (v k)) ≤ M := by
    intro k
    rw [val_act, castM_mulVec_cast, hv]
    simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, cast_single, val_single]
    exact Finset.single_le_sum (f := fun k => F k k) (fun k _ => hdiag k) (Finset.mem_univ _)
  have h := hT.diag_le_of_linearIndependent j v hvi hvM
  rw [act_diag] at h
  refine h.trans ?_
  have : (9 / 4 : ℝ) ^ j.val ≤ (9 / 4 : ℝ) ^ n :=
    pow_le_pow_right₀ (by norm_num) j.2.le
  exact mul_le_mul_of_nonneg_right this hM0

/-- The set of $T \in \mathrm{GL}_n(\mathbb{Z})$ with $f(T\vec{x})$ reduced is finite (the stronger form of the finiteness
in Theorem 1.1, used in §5 and §7). -/
theorem finite_gl_isMinkowskiReduced {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosDef) :
    {T : GL (Fin n) ℤ | IsMinkowskiReduced (act T.val F)}.Finite := by
  set B : ℝ := (9 / 4 : ℝ) ^ n * ∑ k, F k k with hBdef
  have hB : ∀ T : GL (Fin n) ℤ, IsMinkowskiReduced (act T.val F) → ∀ j : Fin n,
      val F (cast (T.val *ᵥ Pi.single j 1)) ≤ B := fun T hT j => columns_bound hF T hT j
  let Φ : GL (Fin n) ℤ → (Fin n → Fin n → ℤ) := fun T j => T.val *ᵥ Pi.single j 1
  have hinj : Set.InjOn Φ {T : GL (Fin n) ℤ | IsMinkowskiReduced (act T.val F)} := by
    intro T _ T' _ h
    apply Units.ext
    ext a j
    have := congrFun (congrFun h j) a
    simpa [Φ, mulVec_single_apply] using this
  refine Set.Finite.of_finite_image ?_ hinj
  refine (Set.Finite.pi (t := fun _ : Fin n => {m : Fin n → ℤ | val F (cast m) ≤ B})
    (fun _ => finite_val_le hF B)).subset ?_
  rintro _ ⟨T, hT, rfl⟩ j _
  exact hB T hT j

/-- **Theorem 1.1, finiteness** (Cassels, Ch. 12, p. 256): a strictly positive definite real form is integrally
equivalent to at most finitely many reduced forms. *Update* (gap): Cassels says
"we have at once"; the proof needs the bound below. In fact only finitely many $T \in \mathrm{GL}_n(\mathbb{Z})$ make
$f(T\vec{x})$ reduced: the columns $\vec{t}_j$ of such a $T$ satisfy $f(\vec{t}_j) \le (9/4)^{n} \max_k f_{kk}$
(`IsMinkowskiReduced.diag_le_of_linearIndependent`), and `finite_val_le` applies. -/
@[kb "cassels1978" "Ch. 12, §1, Thm. 1.1, p. 256 (finiteness)"]
theorem finite_isMinkowskiReduced {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosDef) :
    {G | IsMinkowskiReduced G ∧ ∃ T : GL (Fin n) ℤ, G = act T.val F}.Finite := by
  refine ((finite_gl_isMinkowskiReduced hF).image fun T : GL (Fin n) ℤ => act T.val F).subset ?_
  rintro G ⟨hG, T, rfl⟩
  exact ⟨T, hG, rfl⟩

/-- **The Siegel domain $\mathcal S(\delta, \eta) = \mathcal S_n(\delta, \eta)$** (Cassels, Ch. 12, §1, Definition,
p. 259): the real forms
$$f(\vec{x}) = h_0(x_0 + c_{01}x_1 + \cdots + c_{0,n-1}x_{n-1})^2 + h_1(x_1 + c_{12}x_2 + \cdots)^2 + \cdots +
h_{n-1}x_{n-1}^2$$
(`IsSqDecomp`) with
$$0 < h_j \le \delta\,h_{j+1} \ (0 \le j < n - 1), \qquad |c_{ij}| \le \eta \ (i < j).$$
Cassels takes $\delta > 0$, $\eta > 0$; no condition on $\delta, \eta$ is imposed here (for other values the set is
just smaller or empty). The displayed conditions are garbled in the machine-read text and were reconstructed from
their use in §§3–4 ((3.4)–(3.6), pp. 265–266; (4.1), p. 266). Forms in a Siegel domain are strictly positive
definite (`InSiegelDomain.posDef`). -/
@[kb "cassels1978" "Ch. 12, §1, Definition (Siegel domain), p. 259"]
def InSiegelDomain (δ η : ℝ) (F : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ (h : Fin n → ℝ) (C : Matrix (Fin n) (Fin n) ℝ), IsSqDecomp F h C ∧ (∀ i, 0 < h i) ∧
    (∀ i j : Fin n, j.val = i.val + 1 → h i ≤ δ * h j) ∧ ∀ i j, i < j → |C i j| ≤ η

theorem InSiegelDomain.posDef {δ η : ℝ} {F : Matrix (Fin n) (Fin n) ℝ} (hF : InSiegelDomain δ η F) :
    F.PosDef := by
  obtain ⟨h, C, hd, hh, -, -⟩ := hF
  exact hd.posDef hh

/-- Siegel domains grow with $\delta$ and $\eta$. -/
theorem InSiegelDomain.mono {δ η δ' η' : ℝ} (hδ : δ ≤ δ') (hη : η ≤ η') {F : Matrix (Fin n) (Fin n) ℝ}
    (hF : InSiegelDomain δ η F) : InSiegelDomain δ' η' F := by
  obtain ⟨h, C, hd, hh, hs, hc⟩ := hF
  exact ⟨h, C, hd, hh, fun i j hij => (hs i j hij).trans (mul_le_mul_of_nonneg_right hδ (hh j).le),
    fun i j hij => (hc i j hij).trans hη⟩

end QuadFormsKB.Reduction
