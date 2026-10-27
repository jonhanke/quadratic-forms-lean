/-
# Cassels, Chapter 12, Lemma 1.2: Minkowski's conditions for $n \le 4$

Cassels, *Rational Quadratic Forms* (1978), Ch. 12, §1, Lemma 1.2, pp. 257–258.

For $n \le 4$ a real symmetric $F$ is Minkowski-reduced iff (i) $0 < f_{00} \le f_{11} \le \dots \le f_{n-1,n-1}$ and
(ii) $f(\vec{s}) \ge f_{jj}$ for every $j$ and every integral $\vec{s}$ with $s_i \in \{0, \pm1\}$ ($i < j$), $s_j = 1$, $s_i = 0$
($i > j$) (`lemma_1_2`). The conditions are partly garbled in the machine-read text (p. 257) and were reconstructed from
the proof (p. 258), which uses exactly these vectors (the all-ones vector, $e_j \pm e_i$, and the vectors $\vec{a}$ with
$a_i \in \{0, 1\}$).

**Proof** (Cassels', arranged to avoid passing to forms in fewer variables). By (ii) with $\vec{s} = e_j \pm e_i$,
$|2f_{ij}| \le f_{ii}$ ((1.6)). Main claim: if $a_\ell \ne 0$ and $a_i = 0$ for $i > \ell$ then $f(\vec{a}) \ge f_{\ell\ell}$.
After sign changes $x_i \mapsto -x_i$ (which preserve (i), (ii)) all $a_i \ge 0$; induct on $\sum a_i$. If all
$a_i \in \{0, 1\}$, (ii) applies. Otherwise let $S$ be the support, $B = \min_S a_i$, $k \in S$ with $a_k = B$ (and
$k = \ell$ if $a_\ell = B$), $\vec{w} = \sum_{i \in S \setminus k} e_i$ and $\vec{b} = \vec{a} - B\vec{w}$. Then
$$f(\vec{a}) - f(\vec{b}) = B\Bigl[2\sum_{i \in S\setminus k} b_i\,B(\vec{w}, e_i) + B\bigl(f(\vec{w} + e_k) - f_{kk}\bigr)\Bigr] \ge 0,$$
since $f(\vec{w} + e_k) \ge f_{\ell\ell} \ge f_{kk}$ by (ii), (i), and $B(\vec{w}, e_i) = f_{ii} + \sum_{i' \in S \setminus\{i,k\}} f_{ii'} \ge 0$
by (1.6) and (i), because $|S| \le 4$ leaves at most two terms in the sum — the only place where $n \le 4$ is used.
Definiteness follows from Lemma 5.4.

**Not formalized:** Note 2 (the set of $\vec{s}$ in (ii) is minimal), whose example forms are lost in the
machine-read text.
-/
import QuadFormsKB.Literature.Cassels.Ch12.Sec5

open Matrix

namespace QuadFormsKB.Reduction

variable {n : ℕ}

/-- **Minkowski's test vectors for $n \le 4$** (Cassels, Ch. 12, Lemma 1.2 (ii), p. 257, 0-based): the integral $\vec{s}$
with $s_i \in \{0, \pm1\}$ for $i < j$, $s_j = 1$ and $s_i = 0$ for $i > j$. Each extends $e_0, \dots, e_{j-1}$ to a basis. -/
@[kb "cassels1978" "Ch. 12, §1, Lemma 1.2 (ii), p. 257"]
def minkowskiTestVectors (j : Fin n) : Set (Fin n → ℤ) :=
  {s | (∀ i < j, s i = 0 ∨ s i = 1 ∨ s i = -1) ∧ s j = 1 ∧ ∀ i, j < i → s i = 0}

/-- Helper: the hypotheses of Lemma 1.2 on a form: symmetry, (i) and (ii), bundled. -/
private def Cond12 (F : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  F.IsSymm ∧ (∀ i : Fin n, i.val = 0 → 0 < F i i) ∧ (∀ i j : Fin n, i ≤ j → F i i ≤ F j j) ∧
    ∀ j : Fin n, ∀ s ∈ minkowskiTestVectors j, F j j ≤ val F (cast s)

/-- Helper: under (i), all diagonal entries are positive. -/
private theorem Cond12.diag_pos {F : Matrix (Fin n) (Fin n) ℝ} (hC : Cond12 F) (i : Fin n) : 0 < F i i := by
  obtain ⟨-, h0, hm, -⟩ := hC
  have hpos : 0 < n := Fin.pos i
  have h := hm ⟨0, hpos⟩ i (by simp [Fin.le_def])
  exact lt_of_lt_of_le (h0 ⟨0, hpos⟩ rfl) h

/-- Helper: (1.6) for all pairs $i \ne j$: $2|f_{ij}| \le f_{ii}$. -/
private theorem Cond12.two_abs_le {F : Matrix (Fin n) (Fin n) ℝ} (hC : Cond12 F) {i j : Fin n} (hij : i ≠ j) :
    2 * |F i j| ≤ F i i := by
  have hs := hC.1
  have hsym : ∀ i j, F j i = F i j := by
    intro i j
    have : Fᵀ = F := hs
    simpa using congrFun (congrFun this i) j
  have key : ∀ i j : Fin n, i < j → 2 * |F i j| ≤ F i i := by
    intro i j hij
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
      have hmem : (Pi.single j 1 : Fin n → ℤ) + c • Pi.single i 1 ∈ minkowskiTestVectors j := by
        refine ⟨fun k hk => ?_, ?_, fun k hk => ?_⟩
        · have hkj : k ≠ j := hk.ne
          by_cases h2 : k = i
          · subst h2
            rcases hc with rfl | rfl <;> simp [Pi.single_apply, hkj]
          · simp [Pi.single_apply, hkj, h2]
        · simp [Pi.single_apply, hij.ne']
        · have hkj : k ≠ j := hk.ne'
          have hki : k ≠ i := (hij.trans hk).ne'
          simp [Pi.single_apply, hkj, hki]
      have h := hC.2.2.2 j _ hmem
      rwa [hx, val_pair hs] at h
    have h1 := key 1 (Or.inl rfl)
    have h2 := key (-1) (Or.inr rfl)
    push_cast at h1 h2
    rw [hsym i j] at h1 h2
    have : |F i j| ≤ F i i / 2 := by
      rw [abs_le]; constructor <;> nlinarith
    linarith
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h
  · have := key j i h
    have hm := hC.2.2.1 j i h.le
    rw [hsym i j] at this
    linarith

/-- Helper: **the main claim for nonnegative coefficients**: if $a \ge 0$, $a_\ell \ne 0$, $a_i = 0$ for $i > \ell$, then
$f(\vec{a}) \ge f_{\ell\ell}$. Strong induction on $\sum a_i$ (Cassels' argument, arranged as in the module docstring). -/
private theorem l12_core_nat (hn : n ≤ 4) {F : Matrix (Fin n) (Fin n) ℝ} (hC : Cond12 F) :
    ∀ (N : ℕ) (a : Fin n → ℕ), ∑ i, a i = N → ∀ ℓ : Fin n, a ℓ ≠ 0 → (∀ i, ℓ < i → a i = 0) →
      F ℓ ℓ ≤ val F (fun i => (a i : ℝ)) := by
  have hpos := hC.diag_pos
  have habs := fun {i j : Fin n} (h : i ≠ j) => hC.two_abs_le h
  obtain ⟨hs, -, hmono, htest⟩ := hC
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro a hN ℓ hℓ hz
  classical
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin n), S = Finset.univ.filter (fun i => a i ≠ 0) := ⟨_, rfl⟩
  have hmemS : ∀ i, i ∈ S ↔ a i ≠ 0 := by intro i; simp [hS]
  have hℓS : ℓ ∈ S := (hmemS ℓ).2 hℓ
  have hSle : ∀ i ∈ S, i ≤ ℓ := by
    intro i hi; by_contra h; exact (hmemS i).1 hi (hz i (not_le.1 h))
  by_cases hcard : S.card = 1
  · obtain ⟨x, hx⟩ := Finset.card_eq_one.1 hcard
    have hxℓ : ℓ = x := by
      have := hℓS; rw [hx] at this; simpa using this
    have hzero : ∀ i, i ≠ ℓ → a i = 0 := by
      intro i hi; by_contra h
      have := (hmemS i).2 h
      rw [hx] at this
      simp at this
      exact hi (this.trans hxℓ.symm)
    have hvec : (fun i => (a i : ℝ)) = (a ℓ : ℝ) • (Pi.single ℓ 1 : Fin n → ℝ) := by
      funext i; by_cases h : i = ℓ
      · subst h; simp
      · simp [Pi.single_apply, h, hzero i h]
    rw [hvec, val_smul, val_single]
    have h1 : (1 : ℝ) ≤ (a ℓ : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hℓ
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (by linarith : (0 : ℝ) ≤ (a ℓ : ℝ) + 1)) (hpos ℓ).le]
  · have hcard2 : 2 ≤ S.card := by
      have : 0 < S.card := Finset.card_pos.2 ⟨ℓ, hℓS⟩
      omega
    obtain ⟨k0, hk0S, hk0min⟩ := Finset.exists_min_image S a ⟨ℓ, hℓS⟩
    obtain ⟨k, hkS, hkmin, hkℓ⟩ : ∃ k ∈ S, (∀ i ∈ S, a k ≤ a i) ∧ (a ℓ = a k → k = ℓ) := by
      by_cases h : a ℓ ≤ a k0
      · exact ⟨ℓ, hℓS, fun i hi => h.trans (hk0min i hi), fun _ => rfl⟩
      · exact ⟨k0, hk0S, hk0min, fun h' => absurd h' (by omega)⟩
    have hBpos : 0 < a k := Nat.pos_of_ne_zero ((hmemS k).1 hkS)
    obtain ⟨w, hw⟩ : ∃ w : Fin n → ℕ, ∀ i, w i = if i ∈ S.erase k then 1 else 0 := ⟨_, fun _ => rfl⟩
    obtain ⟨b, hb⟩ : ∃ b : Fin n → ℕ, ∀ i, b i = a i - a k * w i := ⟨_, fun _ => rfl⟩
    have hab : ∀ i, a i = b i + a k * w i := by
      intro i
      by_cases h : i ∈ S.erase k
      · have : a k ≤ a i := hkmin i (Finset.mem_of_mem_erase h)
        rw [hb, hw, if_pos h]; omega
      · rw [hb, hw, if_neg h]; omega
    have hsumw : ∑ i, w i = (S.erase k).card := by
      simp only [hw, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul, mul_one]
    have hsum : ∑ i, a i = ∑ i, b i + a k * (S.erase k).card := by
      rw [← hsumw, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => hab i)
    have hcardE : 1 ≤ (S.erase k).card := by rw [Finset.card_erase_of_mem hkS]; omega
    have hlt : ∑ i, b i < N := by
      rw [← hN, hsum]
      have : 1 ≤ a k * (S.erase k).card := Nat.mul_pos hBpos hcardE
      omega
    have hbz : ∀ i, ℓ < i → b i = 0 := by
      intro i hi
      have hai := hz i hi
      have hiS : i ∉ S := fun h => (hmemS i).1 h hai
      have : i ∉ S.erase k := fun h => hiS (Finset.mem_of_mem_erase h)
      rw [hb, hw, if_neg this]; simp [hai]
    have hbℓ : b ℓ ≠ 0 := by
      by_cases hkl : k = ℓ
      · have : ℓ ∉ S.erase k := by simp [hkl]
        rw [hb, hw, if_neg this]; simpa using hℓ
      · have hm : ℓ ∈ S.erase k := Finset.mem_erase.2 ⟨Ne.symm hkl, hℓS⟩
        have h1 : a k ≤ a ℓ := hkmin ℓ hℓS
        have h2 : a ℓ ≠ a k := fun h => hkl (hkℓ h)
        rw [hb, hw, if_pos hm]; omega
    have hih := ih _ hlt b rfl ℓ hbℓ hbz
    obtain ⟨W, hWdef⟩ : ∃ W : Fin n → ℝ, ∀ i, W i = (w i : ℝ) := ⟨fun i => (w i : ℝ), fun _ => rfl⟩
    obtain ⟨Q, hQdef⟩ : ∃ Q : Fin n → ℝ, ∀ i, Q i = (F *ᵥ W) i := ⟨_, fun _ => rfl⟩
    have hvec : (fun i => (a i : ℝ)) = (fun i => (b i : ℝ)) + (a k : ℝ) • W := by
      funext i
      have := hab i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hWdef]
      exact_mod_cast this
    have hdot : (fun i => (b i : ℝ)) ⬝ᵥ (F *ᵥ W) = ∑ i, (b i : ℝ) * Q i := by
      simp [dotProduct, hQdef]
    have hexp : val F (fun i => (a i : ℝ)) = val F (fun i => (b i : ℝ)) + 2 * (a k : ℝ) * ∑ i, (b i : ℝ) * Q i
        + (a k : ℝ) ^ 2 * val F W := by
      rw [hvec, val_add hs, val_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, hdot]
      ring
    -- the test vector (indicator of S)
    obtain ⟨s, hsdef⟩ : ∃ s : Fin n → ℤ, ∀ i, s i = if i ∈ S then 1 else 0 := ⟨_, fun _ => rfl⟩
    have hs_mem : s ∈ minkowskiTestVectors ℓ := by
      refine ⟨fun i _ => ?_, ?_, fun i hi => ?_⟩
      · rw [hsdef]; split_ifs <;> simp
      · rw [hsdef, if_pos hℓS]
      · rw [hsdef, if_neg]
        intro h
        exact absurd (hSle i h) (not_le.2 hi)
    have hts := htest ℓ s hs_mem
    have hcs : cast s = (Pi.single k 1 : Fin n → ℝ) + W := by
      funext i
      by_cases h : i = k
      · subst h
        simp [cast, hsdef, hWdef, hw, hkS]
      · by_cases h2 : i ∈ S <;> simp [cast, hsdef, hWdef, hw, h, h2, Finset.mem_erase, Pi.single_apply]
    have hQk : (Pi.single k 1 : Fin n → ℝ) ⬝ᵥ (F *ᵥ W) = Q k := by
      rw [hQdef]; simp [dotProduct, Pi.single_apply]
    have hvs : val F (cast s) = F k k + 2 * Q k + val F W := by
      rw [hcs, val_add hs, hQk, val_single]
    have hkℓ' : F k k ≤ F ℓ ℓ := hmono k ℓ (hSle k hkS)
    have hQ : ∀ i, Q i = ∑ j ∈ S.erase k, F i j := by
      intro i
      simp only [hQdef, hWdef, hw, Matrix.mulVec, dotProduct, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_mem, Finset.univ_inter]
    have hQnn : ∀ i ∈ S.erase k, 0 ≤ Q i := by
      intro i hi
      rw [hQ, ← Finset.add_sum_erase _ _ hi]
      have hcardle : ((S.erase k).erase i).card ≤ 2 := by
        rw [Finset.card_erase_of_mem hi, Finset.card_erase_of_mem hkS]
        have : S.card ≤ n := by simpa using Finset.card_le_univ S
        omega
      have hge : ∀ j ∈ (S.erase k).erase i, -(F i i / 2) ≤ F i j := by
        intro j hj
        have hji : j ≠ i := Finset.ne_of_mem_erase hj
        have := habs (Ne.symm hji)
        have := neg_abs_le (F i j)
        linarith
      have hsumge := Finset.card_nsmul_le_sum ((S.erase k).erase i) (fun j => F i j) (-(F i i / 2)) hge
      rw [nsmul_eq_mul] at hsumge
      have hc : (((S.erase k).erase i).card : ℝ) ≤ 2 := by exact_mod_cast hcardle
      have hi' := hpos i
      nlinarith [mul_nonneg (sub_nonneg.2 hc) hi'.le]
    have hbk : (b k : ℝ) = a k := by
      have hk' : k ∉ S.erase k := Finset.notMem_erase _ _
      rw [hb k, hw k, if_neg hk']; simp
    have hsumb : (a k : ℝ) * Q k ≤ ∑ i, (b i : ℝ) * Q i := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), hbk]
      have hrest : 0 ≤ ∑ i ∈ Finset.univ.erase k, (b i : ℝ) * Q i := by
        apply Finset.sum_nonneg
        intro i hi'
        have hik : i ≠ k := (Finset.mem_erase.1 hi').1
        by_cases hi : i ∈ S.erase k
        · exact mul_nonneg (Nat.cast_nonneg _) (hQnn i hi)
        · have hiS : i ∉ S := fun h => hi (Finset.mem_erase.2 ⟨hik, h⟩)
          have hai : a i = 0 := by
            by_contra h; exact hiS ((hmemS i).2 h)
          have : b i = 0 := by rw [hb, hw, if_neg hi]; simp [hai]
          simp [this]
      linarith
    have hB0 : (0 : ℝ) < a k := by exact_mod_cast hBpos
    have h2Q : 0 ≤ 2 * Q k + val F W := by linarith
    have hp1 := mul_le_mul_of_nonneg_left hsumb (by linarith : (0 : ℝ) ≤ 2 * (a k : ℝ))
    have hp2 := mul_nonneg (sq_nonneg (a k : ℝ)) h2Q
    nlinarith

/-- Helper: the value of the sign-changed form: $f(D\vec{x})$ for $D = \mathrm{diag}(d)$. -/
private theorem l12_val_act_diag (d : Fin n → ℤ) (F : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    val (act (Matrix.diagonal d) F) x = val F (fun i => (d i : ℝ) * x i) := by
  rw [val_act]
  congr 1
  have : castM (Matrix.diagonal d) = Matrix.diagonal (fun i => (d i : ℝ)) := by
    ext i j; by_cases h : i = j <;> simp [castM, Matrix.diagonal_apply, h]
  rw [this]
  funext i
  simp [Matrix.mulVec_diagonal]

/-- Helper: a sign change preserves the diagonal. -/
private theorem l12_act_sign_diag (d : Fin n → ℤ) (hd : ∀ i, d i = 1 ∨ d i = -1)
    (F : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : act (Matrix.diagonal d) F i i = F i i := by
  have hdsq : (d i : ℝ) ^ 2 = 1 := by rcases hd i with h | h <;> simp [h]
  rw [← val_single (act (Matrix.diagonal d) F) i, l12_val_act_diag]
  have : (fun j => (d j : ℝ) * (Pi.single i 1 : Fin n → ℝ) j) = (d i : ℝ) • (Pi.single i 1 : Fin n → ℝ) := by
    funext j; by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_apply, h]
  rw [this, val_smul, hdsq, one_mul, val_single]

/-- Helper: sign changes $x_i \mapsto \pm x_i$ preserve symmetry, (i) and (ii). -/
private theorem Cond12.act_sign {F : Matrix (Fin n) (Fin n) ℝ} (hC : Cond12 F) (d : Fin n → ℤ)
    (hd : ∀ i, d i = 1 ∨ d i = -1) : Cond12 (act (Matrix.diagonal d) F) := by
  obtain ⟨hs, h0, hm, ht⟩ := hC
  refine ⟨?_, fun i hi => by rw [l12_act_sign_diag d hd]; exact h0 i hi,
    fun i j hij => by rw [l12_act_sign_diag d hd, l12_act_sign_diag d hd]; exact hm i j hij, ?_⟩
  · have hs' : Fᵀ = F := hs
    show (act (Matrix.diagonal d) F)ᵀ = act (Matrix.diagonal d) F
    unfold act
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hs', Matrix.transpose_transpose, Matrix.mul_assoc]
  · intro j s hs_mem
    rw [l12_act_sign_diag d hd, l12_val_act_diag]
    obtain ⟨hs1, hs2, hs3⟩ := hs_mem
    obtain ⟨e, he⟩ : ∃ e : ℤ, e = d j := ⟨_, rfl⟩
    have hu : (fun i => e * (d i * s i)) ∈ minkowskiTestVectors j := by
      refine ⟨fun i hi => ?_, ?_, fun i hi => ?_⟩
      · rcases hd j with h | h <;> rcases hd i with h' | h' <;> rcases hs1 i hi with h'' | h'' | h'' <;>
          simp [he, h, h', h'']
      · simp only [hs2, mul_one, he]
        rcases hd j with h | h <;> simp [h]
      · simp [hs3 i hi]
    have h := ht j _ hu
    have hc : cast (fun i => e * (d i * s i)) = (e : ℝ) • (fun i => (d i : ℝ) * (s i : ℝ)) := by
      funext i; simp [cast, mul_assoc]
    have he2 : (e : ℝ) ^ 2 = 1 := by rw [he]; rcases hd j with h | h <;> simp [h]
    rw [hc, val_smul, he2, one_mul] at h
    exact h

/-- Helper: **the main claim for integral coefficients of arbitrary sign**: if $a_\ell \ne 0$ and $a_i = 0$ for
$i > \ell$ then $f(\vec{a}) \ge f_{\ell\ell}$ (after the sign change $x_i \mapsto \pm x_i$ making $\vec{a} \ge 0$). -/
private theorem l12_core_int (hn : n ≤ 4) {F : Matrix (Fin n) (Fin n) ℝ} (hC : Cond12 F) (a : Fin n → ℤ)
    (ℓ : Fin n) (hℓ : a ℓ ≠ 0) (hz : ∀ i, ℓ < i → a i = 0) : F ℓ ℓ ≤ val F (cast a) := by
  obtain ⟨d, hdd⟩ : ∃ d : Fin n → ℤ, ∀ i, d i = if 0 ≤ a i then 1 else -1 := ⟨_, fun _ => rfl⟩
  have hd : ∀ i, d i = 1 ∨ d i = -1 := by intro i; rw [hdd]; split_ifs <;> simp
  have hG := hC.act_sign d hd
  have h := l12_core_nat hn hG _ (fun i => (a i).natAbs) rfl ℓ (by simpa using hℓ)
    (fun i hi => by simp [hz i hi])
  rw [l12_act_sign_diag d hd, l12_val_act_diag] at h
  have hv : (fun i => (d i : ℝ) * (((a i).natAbs : ℕ) : ℝ)) = cast a := by
    funext i
    have : d i * ((a i).natAbs : ℤ) = a i := by
      rw [hdd]; split_ifs with h <;> omega
    have h2 := congrArg (fun t : ℤ => (t : ℝ)) this
    simpa only [Int.cast_mul, Int.cast_natCast] using h2
  rw [hv] at h
  exact h

/-- Helper: the largest index carrying a nonzero coordinate. -/
private theorem l12_exists_top {b : Fin n → ℤ} {k : Fin n} (hk : b k ≠ 0) :
    ∃ ℓ, k ≤ ℓ ∧ b ℓ ≠ 0 ∧ ∀ i, ℓ < i → b i = 0 := by
  classical
  have hne : (Finset.univ.filter fun i => b i ≠ 0).Nonempty := ⟨k, by simp [hk]⟩
  refine ⟨(Finset.univ.filter fun i => b i ≠ 0).max' hne, Finset.le_max' _ k (by simp [hk]), ?_, fun i hi => ?_⟩
  · have := Finset.max'_mem _ hne
    simpa using this
  · by_contra h
    have := Finset.le_max' (Finset.univ.filter fun i => b i ≠ 0) i (by simp [h])
    exact absurd hi (not_lt.2 this)

/-- Helper: if $f \ge 0$ on integral vectors then $f \ge 0$ on all real vectors (approximate $\vec{x}$ by
$\lfloor (m+1)\vec{x}\rfloor/(m+1)$ and use continuity). -/
private theorem l12_nonneg_of_int {F : Matrix (Fin n) (Fin n) ℝ} (hint : ∀ z : Fin n → ℤ, 0 ≤ val F (cast z))
    (x : Fin n → ℝ) : 0 ≤ val F x := by
  have hcont : Continuous (fun x : Fin n → ℝ => val F x) := by
    unfold val Matrix.mulVec dotProduct
    fun_prop
  obtain ⟨z, hz⟩ : ∃ z : ℕ → Fin n → ℤ, ∀ (m : ℕ) (i : Fin n), z m i = ⌊((m : ℝ) + 1) * x i⌋ :=
    ⟨fun m i => ⌊((m : ℝ) + 1) * x i⌋, fun _ _ => rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℕ → Fin n → ℝ, ∀ m : ℕ, u m = (1 / ((m : ℝ) + 1)) • cast (z m) := ⟨_, fun _ => rfl⟩
  have hlim : Filter.Tendsto u Filter.atTop (nhds x) := by
    rw [tendsto_pi_nhds]
    intro i
    have hy : ∀ m : ℕ, (0 : ℝ) < (m : ℝ) + 1 := fun m => by positivity
    have hui : ∀ m : ℕ, u m i = ((z m i : ℤ) : ℝ) / ((m : ℝ) + 1) := by
      intro m; rw [hu]; simp [cast]; ring
    have hup : ∀ m : ℕ, u m i ≤ x i := by
      intro m
      rw [hui, div_le_iff₀ (hy m), hz]
      have := Int.floor_le (((m : ℝ) + 1) * x i)
      linarith
    have hlow : ∀ m : ℕ, x i - 1 / ((m : ℝ) + 1) ≤ u m i := by
      intro m
      rw [hui, le_div_iff₀ (hy m), hz]
      have := Int.lt_floor_add_one (((m : ℝ) + 1) * x i)
      have h2 : (x i - 1 / ((m : ℝ) + 1)) * ((m : ℝ) + 1) = ((m : ℝ) + 1) * x i - 1 := by
        field_simp
      rw [h2]
      linarith
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ tendsto_const_nhds hlow hup
    simpa using (tendsto_const_nhds (x := x i)).sub tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim2 : Filter.Tendsto (fun m => val F (u m)) Filter.atTop (nhds (val F x)) :=
    (hcont.tendsto x).comp hlim
  refine ge_of_tendsto' hlim2 (fun m => ?_)
  rw [hu, val_smul]
  exact mul_nonneg (sq_nonneg _) (hint _)

/-- Helper: under symmetry, (i) and (ii), for $n \le 4$ the form is strictly positive definite (via Lemma 5.4). -/
private theorem l12_posDef (hn : n ≤ 4) {F : Matrix (Fin n) (Fin n) ℝ} (hC : Cond12 F) : F.PosDef := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · rw [posDef_iff]
    exact ⟨hC.1, fun x hx => absurd (Subsingleton.elim x 0) hx⟩
  · have h0 : 0 < F ⟨0, hpos⟩ ⟨0, hpos⟩ := hC.2.1 _ rfl
    have hbd : ∀ b : Fin n → ℤ, b ≠ 0 → F ⟨0, hpos⟩ ⟨0, hpos⟩ ≤ val F (cast b) := by
      intro b hb
      obtain ⟨k, hk⟩ : ∃ k, b k ≠ 0 := by
        by_contra h
        push Not at h
        exact hb (funext h)
      obtain ⟨ℓ, -, hℓ, hz⟩ := l12_exists_top hk
      exact (hC.2.2.1 _ ℓ (by simp [Fin.le_def])).trans (l12_core_int hn hC b ℓ hℓ hz)
    have hint : ∀ z : Fin n → ℤ, 0 ≤ val F (cast z) := by
      intro z
      by_cases hz : z = 0
      · subst hz
        have : cast (0 : Fin n → ℤ) = 0 := by funext i; simp [cast]
        rw [this]; simp [val]
      · exact h0.le.trans (hbd z hz)
    have hsd : F.PosSemidef := (posSemidef_iff F).2 ⟨hC.1, l12_nonneg_of_int hint⟩
    by_contra hnd
    obtain ⟨b, hb, hlt⟩ := lemma_5_4 hsd hnd h0
    exact absurd (hbd b hb) (not_le.2 hlt)

/-- Helper: a vector with $s_j = 1$ has tail gcd $1$. -/
private theorem l12_tailGcd_one {j : Fin n} {s : Fin n → ℤ} (h : s j = 1) : tailGcd j s = 1 := by
  have h1 : tailGcd j s ∣ s j := Finset.gcd_dvd (Finset.mem_filter.2 ⟨Finset.mem_univ _, le_rfl⟩)
  rw [h] at h1
  exact Int.eq_one_of_dvd_one (Int.nonneg_of_normalize_eq_self Finset.normalize_gcd) h1

/-- **Lemma 1.2** (Cassels, Ch. 12, §1, pp. 257–258): for $n \le 4$, a real symmetric $F$ is (strictly positive definite
and) Minkowski-reduced iff (i) $0 < f_{00} \le f_{11} \le \dots \le f_{n-1,n-1}$ and (ii) $f(\vec{s}) \ge f_{jj}$ for every $j$
and every $\vec{s}$ in `minkowskiTestVectors j`. -/
@[kb "cassels1978" "Ch. 12, §1, Lemma 1.2, pp. 257–258"]
theorem lemma_1_2 (hn : n ≤ 4) {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsSymm) :
    IsMinkowskiReduced F ↔
      (∀ i : Fin n, i.val = 0 → 0 < F i i) ∧ (∀ i j : Fin n, i ≤ j → F i i ≤ F j j) ∧
        ∀ j : Fin n, ∀ s ∈ minkowskiTestVectors j, F j j ≤ val F (cast s) := by
  constructor
  · intro hR
    refine ⟨fun i hi => ?_, fun i j hij => hR.diag_mono hij, fun j s hs => ?_⟩
    · have hne : (Pi.single i 1 : Fin n → ℝ) ≠ 0 := by
        intro h0
        have := congrFun h0 i
        simp at this
      have := ((posDef_iff F).1 hR.1).2 _ hne
      rwa [val_single] at this
    · exact ((isMinkowskiReduced_iff_gcd F).1 hR).2 j s (l12_tailGcd_one hs.2.1)
  · rintro ⟨h1, h2, h3⟩
    have hC : Cond12 F := ⟨hF, h1, h2, h3⟩
    rw [isMinkowskiReduced_iff_gcd]
    refine ⟨l12_posDef hn hC, fun j b hb => ?_⟩
    obtain ⟨k, hjk, hk⟩ : ∃ k, j ≤ k ∧ b k ≠ 0 := by
      by_contra h
      push Not at h
      have : tailGcd j b = 0 := Finset.gcd_eq_zero_iff.2 (fun k hk => h k (Finset.mem_filter.1 hk).2)
      rw [hb] at this
      exact one_ne_zero this
    obtain ⟨ℓ, hkℓ, hℓ, hz⟩ := l12_exists_top hk
    exact (h2 j ℓ (hjk.trans hkℓ)).trans (l12_core_int hn hC b ℓ hℓ hz)

end QuadFormsKB.Reduction
