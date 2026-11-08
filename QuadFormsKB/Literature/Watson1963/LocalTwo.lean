/-
# Watson (1963), §2: a Watson-minimal form is $2$-adically square-free

Watson, *The class-number of a positive quadratic form*, Proc. London Math. Soc. (3) 13 (1963), §2, proof of
Theorem 2, p. 551, at $p = 2$. If $f$ is a Watson-minimal positive definite integral form, then in a Jordan
decomposition of $f$ over $\mathbb Z_2$ (`exists_jordanForm_isGLEquiv`: 1-dimensional blocks $2^{\nu} u\,x^2$ and
2-dimensional blocks $2^{\nu}(a x^2 + b x y + c y^2)$ with $b$ a unit) every scale exponent satisfies $\nu \le 1$,
i.e. no Jordan block has Hessian scale $\ge 4$.

*Proof outline.* Let $Z_0$ be the coordinates in 2-dimensional blocks with $\nu = 0$, $W_0$ the unpaired
coordinates with $\nu = 0$, $N_1$ those with $\nu = 1$ and $N_2$ those with $\nu \ge 2$. Then
$r_2(f) \le |Z_0| + [W_0 \ne \emptyset]$ (the radical mod 2 contains the vectors vanishing on $Z_0$ with
$\sum_{W_0} y_j = 0$). For the derived form $g$ (basis matrix $B$ of $\Lambda_2(f)$, $f(B\vec x) = 2 g(\vec x)$),
the columns of $M = T^{-1}B$ vanish mod 2 on $Z_0$ and sum to $0$ mod 2 over $W_0$, and every $\vec x$ with
$(M \vec x)_j$ even for all $j$ with $\nu_j \le 1$ lies in the radical of $g$ mod 2 (all terms of
$Q(M\vec x)$ and of the polar form are $\equiv 0 \pmod 4$). This gives $r_2(g) \le |W_0| - [W_0 \ne \emptyset] +
|N_1|$, so $r_2(f) + r_2(g) \le n - |N_2|$ and minimality ($n \le r_2(f) + r_2(g)$) forces $N_2 = \emptyset$.
-/
import QuadFormsKB.Literature.Watson1963.LocalOdd

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Watson1963

open Siegel DefiniteForms QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR

open Classical

/-! ### Divisibility by 2 in $\mathbb Z_2$ -/

/-- $2 \mid x$ in $\mathbb Z_2$ iff $x$ reduces to $0$ in $\mathbb F_2$. -/
theorem two_dvd_iff (x : ℤ_[2]) : (2 : ℤ_[2]) ∣ x ↔ PadicInt.toZMod x = 0 := by
  rw [toZMod_eq_zero_iff_dvd]
  norm_num

theorem zmod_two_eq_one_of_ne_zero (a : ZMod 2) (h : a ≠ 0) : a = 1 := by
  revert a; decide

/-! ### Combinatorics of the Jordan form at $2$ -/

section Jordan

variable {n : ℕ} {Q : QuadForm ℤ_[2] n} {P : Finset (Fin n × Fin n)} {ν : Fin n → ℕ}

/-- **Divisibility of the coefficients:** $2^{\nu_j} \mid c_{jk}$ and $2^{\nu_k} \mid c_{jk}$. -/
theorem jordan_dvd (hJ : IsJordanForm Q (2 : ℤ_[2]) P ν) (j k : Fin n) :
    (2 : ℤ_[2]) ^ ν j ∣ Q.coeff j k ∧ (2 : ℤ_[2]) ^ ν k ∣ Q.coeff j k := by
  obtain ⟨-, h1, h2, h3, h4, h5⟩ := hJ
  rcases lt_trichotomy j k with h | rfl | h
  · by_cases hP : (j, k) ∈ P
    · obtain ⟨hν, ⟨b, hb, -⟩, -⟩ := h4 _ hP
      simp only at hν hb
      rw [hb]
      exact ⟨dvd_mul_right _ _, by rw [← hν]; exact dvd_mul_right _ _⟩
    · rw [h3 j k h hP]; simp
  · by_cases hp : IsPaired P j
    · obtain ⟨e, he, hej⟩ := hp
      obtain ⟨hν, -, hd1, hd2⟩ := h4 e he
      rcases hej with rfl | rfl
      · exact ⟨hd1, hd1⟩
      · rw [hν] at hd2; exact ⟨hd2, hd2⟩
    · obtain ⟨u, hu, -⟩ := h5 j hp
      rw [hu]; exact ⟨dvd_mul_right _ _, dvd_mul_right _ _⟩
  · rw [Q.upper (show id k < id j from h)]; simp

/-- A nonzero off-diagonal coefficient comes from a pair of `P`. -/
theorem jordan_offdiag (hJ : IsJordanForm Q (2 : ℤ_[2]) P ν) {j k : Fin n} (hjk : j ≠ k)
    (h : Q.coeff j k ≠ 0) : j < k ∧ (j, k) ∈ P := by
  rcases lt_or_gt_of_ne hjk with hlt | hgt
  · refine ⟨hlt, ?_⟩
    by_contra hP
    exact h (hJ.2.2.2.1 j k hlt hP)
  · exact absurd (Q.upper (show id k < id j from hgt)) h

theorem jordan_offdiag_paired (hJ : IsJordanForm Q (2 : ℤ_[2]) P ν) {j k : Fin n} (hjk : j ≠ k)
    (h : Q.coeff j k ≠ 0) : IsPaired P j ∧ IsPaired P k ∧ ν j = ν k := by
  obtain ⟨-, hP⟩ := jordan_offdiag hJ hjk h
  exact ⟨⟨(j, k), hP, Or.inl rfl⟩, ⟨(j, k), hP, Or.inr rfl⟩, (hJ.2.2.2.2.1 _ hP).1⟩

theorem hessian_apply' (Q : QuadForm ℤ_[2] n) (i j : Fin n) : Q.hessian i j = Q.coeff i j + Q.coeff j i := rfl

/-- **Even Hessian rows:** if $\nu_j \ge 1$ or $j$ is unpaired then every Hessian entry $H_{jk}$ is even. -/
theorem jordan_hessian_even (hJ : IsJordanForm Q (2 : ℤ_[2]) P ν) {j : Fin n}
    (hj : 1 ≤ ν j ∨ ¬ IsPaired P j) (k : Fin n) : (2 : ℤ_[2]) ∣ Q.hessian j k := by
  rw [hessian_apply']
  rcases hj with hj | hj
  · have h2 : (2 : ℤ_[2]) ∣ 2 ^ ν j := dvd_pow_self 2 (by omega)
    exact dvd_add (h2.trans (jordan_dvd hJ j k).1) (h2.trans (jordan_dvd hJ k j).2)
  · by_cases hjk : j = k
    · subst hjk; rw [← two_mul]; exact dvd_mul_right _ _
    · have e1 : Q.coeff j k = 0 := by
        by_contra h; exact hj (jordan_offdiag_paired hJ hjk h).1
      have e2 : Q.coeff k j = 0 := by
        by_contra h; exact hj (jordan_offdiag_paired hJ (Ne.symm hjk) h).2.1
      rw [e1, e2]; simp

/-- **The partner of a unimodular paired coordinate:** if $j$ is paired with $\nu_j = 0$ there is $k \ne j$ with
$H_{jk}$ a unit and $H_{ik} = 0$ for all $i \ne j, k$. -/
theorem jordan_partner (hJ : IsJordanForm Q (2 : ℤ_[2]) P ν) {j : Fin n} (hp : IsPaired P j) (h0 : ν j = 0) :
    ∃ k, k ≠ j ∧ IsUnit (Q.hessian j k) ∧ ∀ i, i ≠ j → i ≠ k → Q.hessian i k = 0 := by
  obtain ⟨-, h1, h2, h3, h4, h5⟩ := hJ
  obtain ⟨⟨a, b⟩, he, hej⟩ := hp
  have hab : a < b := h1 _ he
  obtain ⟨hν, ⟨c, hc, hcu⟩, -⟩ := h4 _ he
  simp only at hν hc hej
  have hoff : ∀ i k : Fin n, i ≠ k → Q.coeff i k ≠ 0 → i < k ∧ (i, k) ∈ P := by
    intro i k hik h
    rcases lt_or_gt_of_ne hik with hlt | hgt
    · refine ⟨hlt, ?_⟩
      by_contra hP; exact h (h3 i k hlt hP)
    · exact absurd (Q.upper (show id k < id i from hgt)) h
  rcases hej with rfl | rfl
  · -- j = a, partner b
    refine ⟨b, hab.ne', ?_, fun i hij hib => ?_⟩
    · rw [hessian_apply', Q.upper (show id a < id b from hab), add_zero, hc, h0]
      simpa using hcu
    · rw [hessian_apply']
      have e1 : Q.coeff i b = 0 := by
        by_contra h
        obtain ⟨-, hP⟩ := hoff i b hib h
        have := h2 _ he _ hP (fun h' => hij (by simpa using (congrArg Prod.fst h').symm))
        exact this.2.2.2 rfl
      have e2 : Q.coeff b i = 0 := by
        by_contra h
        obtain ⟨-, hP⟩ := hoff b i (Ne.symm hib) h
        have := h2 _ he _ hP (fun h' => hab.ne (by simpa using (congrArg Prod.fst h')))
        exact this.2.2.1 rfl
      rw [e1, e2]; simp
  · -- j = b, partner a
    refine ⟨a, hab.ne, ?_, fun i hij hia => ?_⟩
    · rw [hessian_apply', Q.upper (show id a < id b from hab), zero_add, hc, hν, h0]
      simpa using hcu
    · rw [hessian_apply']
      have e1 : Q.coeff i a = 0 := by
        by_contra h
        obtain ⟨-, hP⟩ := hoff i a hia h
        have := h2 _ he _ hP (fun h' => hia (by simpa using (congrArg Prod.fst h').symm))
        exact this.2.1 rfl
      have e2 : Q.coeff a i = 0 := by
        by_contra h
        obtain ⟨-, hP⟩ := hoff a i (Ne.symm hia) h
        have := h2 _ he _ hP (fun h' => hij (by simpa using (congrArg Prod.snd h').symm))
        exact this.1 rfl
      rw [e1, e2]; simp

/-- The paired coordinates with $\nu = 0$ ($Z_0$: unimodular 2-dimensional blocks). -/
def pairedUnimod (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun j => IsPaired P j ∧ ν j = 0

/-- The unpaired coordinates with $\nu = 0$ ($W_0$: unit 1-dimensional blocks $u x^2$). -/
def unpairedUnimod (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun j => ¬ IsPaired P j ∧ ν j = 0

theorem mem_pairedUnimod {P : Finset (Fin n × Fin n)} {ν : Fin n → ℕ} {j : Fin n} :
    j ∈ pairedUnimod P ν ↔ IsPaired P j ∧ ν j = 0 := by simp [pairedUnimod]

theorem mem_unpairedUnimod {P : Finset (Fin n × Fin n)} {ν : Fin n → ℕ} {j : Fin n} :
    j ∈ unpairedUnimod P ν ↔ ¬ IsPaired P j ∧ ν j = 0 := by simp [unpairedUnimod]

theorem eval_eq_sum2 (Q : QuadForm ℤ_[2] n) (y : Fin n → ℤ_[2]) :
    Q.eval y = ∑ j, ∑ k, y j * (Q.coeff j k * y k) := by
  rw [QuadForm.eval_eq_dotProduct']
  simp [dotProduct, mulVec, Finset.mul_sum]

theorem eval_zero2 (Q : QuadForm ℤ_[2] n) : Q.eval 0 = 0 := by
  rw [eval_eq_sum2]; simp

/-- **$Q(y) \equiv \sum_{W_0} y_j \pmod 2$** when $y$ is even on $Z_0$. -/
theorem jordan_Qmod (hJ : IsJordanForm Q (2 : ℤ_[2]) P ν) (y : Fin n → ℤ_[2])
    (hy : ∀ j ∈ pairedUnimod P ν, (2 : ℤ_[2]) ∣ y j) :
    (2 : ℤ_[2]) ∣ Q.eval y - ∑ j ∈ unpairedUnimod P ν, y j := by
  have hw : ∑ j ∈ unpairedUnimod P ν, y j =
      ∑ j, ∑ k, (if j = k then (if (¬ IsPaired P j ∧ ν j = 0) then y j else 0) else 0) := by
    simp only [unpairedUnimod, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp
  rw [eval_eq_sum2, hw, ← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun j _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun k _ => ?_
  by_cases hj1 : 1 ≤ ν j
  · have h2 : (2 : ℤ_[2]) ∣ Q.coeff j k := (dvd_pow_self 2 (by omega)).trans (jordan_dvd hJ j k).1
    have hn : ν j ≠ 0 := by omega
    have : (if j = k then (if (¬ IsPaired P j ∧ ν j = 0) then y j else 0) else 0) = 0 := by simp [hn]
    rw [this, sub_zero]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right h2 _) _
  by_cases hk1 : 1 ≤ ν k
  · have h2 : (2 : ℤ_[2]) ∣ Q.coeff j k := (dvd_pow_self 2 (by omega)).trans (jordan_dvd hJ j k).2
    have : (if j = k then (if (¬ IsPaired P j ∧ ν j = 0) then y j else 0) else 0) = 0 := by
      by_cases hjk : j = k
      · subst hjk; exact absurd hk1 hj1
      · simp [hjk]
    rw [this, sub_zero]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right h2 _) _
  have hj0 : ν j = 0 := by omega
  have hk0 : ν k = 0 := by omega
  by_cases hpj : IsPaired P j
  · have : (if j = k then (if (¬ IsPaired P j ∧ ν j = 0) then y j else 0) else 0) = 0 := by simp [hpj]
    rw [this, sub_zero]
    exact Dvd.dvd.mul_right (hy j (mem_pairedUnimod.2 ⟨hpj, hj0⟩)) _
  by_cases hpk : IsPaired P k
  · have : (if j = k then (if (¬ IsPaired P j ∧ ν j = 0) then y j else 0) else 0) = 0 := by
      by_cases hjk : j = k
      · subst hjk; exact absurd hpk hpj
      · simp [hjk]
    rw [this, sub_zero]
    obtain ⟨b, hb⟩ := hy k (mem_pairedUnimod.2 ⟨hpk, hk0⟩)
    exact ⟨y j * Q.coeff j k * b, by rw [hb]; ring⟩
  by_cases hjk : j = k
  · subst hjk
    obtain ⟨u, hu, huu⟩ := hJ.2.2.2.2.2 j hpj
    have hne : PadicInt.toZMod u ≠ 0 := toZMod_ne_zero_of_isUnit 2 huu
    have h1 := zmod_two_eq_one_of_ne_zero _ hne
    have : (if j = j then (if (¬ IsPaired P j ∧ ν j = 0) then y j else 0) else 0) = y j := by
      simp [hpj, hj0]
    rw [this, hu, hj0, pow_zero, one_mul, two_dvd_iff]
    simp only [map_sub, map_mul, h1]
    generalize PadicInt.toZMod (y j) = a
    revert a; decide
  · have hC : Q.coeff j k = 0 := by
      by_contra h; exact hpj (jordan_offdiag_paired hJ hjk h).1
    simp [hC, hjk]

/-- **Even Hessian pairing:** $y^{\mathsf T} H w$ is even when $y$ is even on $Z_0$. -/
theorem jordan_polar_even (hJ : IsJordanForm Q (2 : ℤ_[2]) P ν) (y w : Fin n → ℤ_[2])
    (hy : ∀ j ∈ pairedUnimod P ν, (2 : ℤ_[2]) ∣ y j) : (2 : ℤ_[2]) ∣ y ⬝ᵥ (Q.hessian *ᵥ w) := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine Finset.dvd_sum fun j _ => Finset.dvd_sum fun k _ => ?_
  by_cases hj : IsPaired P j ∧ ν j = 0
  · exact Dvd.dvd.mul_right (hy j (mem_pairedUnimod.2 hj)) _
  · have hc : 1 ≤ ν j ∨ ¬ IsPaired P j := by
      by_cases hp : IsPaired P j
      · left; have : ν j ≠ 0 := fun h => hj ⟨hp, h⟩
        omega
      · right; exact hp
    have h2 := jordan_hessian_even hJ hc k
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right h2 _) _

/-- **Rows of $H$ at unimodular coordinates:** $H_{jk}$ is even or $k \in Z_0$ (when $\nu_j = 0$). -/
theorem jordan_hessian_even_or (hJ : IsJordanForm Q (2 : ℤ_[2]) P ν) {j : Fin n} (hj : ν j = 0) (k : Fin n) :
    (2 : ℤ_[2]) ∣ Q.hessian j k ∨ (IsPaired P k ∧ ν k = 0) := by
  by_cases hjk : j = k
  · subst hjk; left; rw [hessian_apply', ← two_mul]; exact dvd_mul_right _ _
  by_cases h1 : Q.coeff j k = 0
  · by_cases h2 : Q.coeff k j = 0
    · left; rw [hessian_apply', h1, h2]; simp
    · obtain ⟨hpk, -, hν⟩ := jordan_offdiag_paired hJ (Ne.symm hjk) h2
      right; exact ⟨hpk, by omega⟩
  · obtain ⟨-, hpk, hν⟩ := jordan_offdiag_paired hJ hjk h1
    right; exact ⟨hpk, by omega⟩

/-- **$Q(y) \equiv 0 \pmod 4$** when $y_j$ is even whenever $\nu_j \le 1$. -/
theorem jordan_Q4 (hJ : IsJordanForm Q (2 : ℤ_[2]) P ν) (y : Fin n → ℤ_[2])
    (hy : ∀ j, ν j ≤ 1 → (2 : ℤ_[2]) ∣ y j) : (2 : ℤ_[2]) ^ 2 ∣ Q.eval y := by
  rw [eval_eq_sum2]
  refine Finset.dvd_sum fun j _ => Finset.dvd_sum fun k _ => ?_
  by_cases hj : 2 ≤ ν j
  · have h2 : (2 : ℤ_[2]) ^ 2 ∣ Q.coeff j k := (pow_dvd_pow 2 hj).trans (jordan_dvd hJ j k).1
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right h2 _) _
  by_cases hk : 2 ≤ ν k
  · have h2 : (2 : ℤ_[2]) ^ 2 ∣ Q.coeff j k := (pow_dvd_pow 2 hk).trans (jordan_dvd hJ j k).2
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right h2 _) _
  obtain ⟨a, ha⟩ := hy j (by omega)
  obtain ⟨b, hb⟩ := hy k (by omega)
  exact ⟨a * Q.coeff j k * b, by rw [ha, hb]; ring⟩

/-- **$y^{\mathsf T} H w \equiv 0 \pmod 4$** when $y_j$ is even whenever $\nu_j \le 1$ and $w$ is even on $Z_0$. -/
theorem jordan_polar4 (hJ : IsJordanForm Q (2 : ℤ_[2]) P ν) (y w : Fin n → ℤ_[2])
    (hy : ∀ j, ν j ≤ 1 → (2 : ℤ_[2]) ∣ y j) (hw : ∀ k ∈ pairedUnimod P ν, (2 : ℤ_[2]) ∣ w k) :
    (2 : ℤ_[2]) ^ 2 ∣ y ⬝ᵥ (Q.hessian *ᵥ w) := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine Finset.dvd_sum fun j _ => Finset.dvd_sum fun k _ => ?_
  by_cases hj : 2 ≤ ν j
  · have h2 : (2 : ℤ_[2]) ^ 2 ∣ Q.hessian j k := by
      rw [hessian_apply']
      exact dvd_add ((pow_dvd_pow 2 hj).trans (jordan_dvd hJ j k).1)
        ((pow_dvd_pow 2 hj).trans (jordan_dvd hJ k j).2)
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right h2 _) _
  obtain ⟨a, ha⟩ := hy j (by omega)
  by_cases hj0 : ν j = 0
  · rcases jordan_hessian_even_or hJ hj0 k with h | h
    · obtain ⟨c, hc⟩ := h
      exact ⟨a * c * w k, by rw [ha, hc]; ring⟩
    · obtain ⟨b, hb⟩ := hw k (mem_pairedUnimod.2 h)
      exact ⟨a * Q.hessian j k * b, by rw [ha, hb]; ring⟩
  · obtain ⟨c, hc⟩ := jordan_hessian_even hJ (Or.inl (by omega : 1 ≤ ν j)) k
    exact ⟨a * c * w k, by rw [ha, hc]; ring⟩

/-- **The radical condition in Jordan coordinates:** if $Q(y + w) \equiv Q(w) \pmod 2$ for all $w$, then $y$ is
even on $Z_0$ and $\sum_{W_0} y_j$ is even. -/
theorem jordan_rad (hJ : IsJordanForm Q (2 : ℤ_[2]) P ν) (y : Fin n → ℤ_[2])
    (h : ∀ w, (2 : ℤ_[2]) ∣ Q.eval (y + w) - Q.eval w) :
    (∀ j ∈ pairedUnimod P ν, (2 : ℤ_[2]) ∣ y j) ∧ (2 : ℤ_[2]) ∣ ∑ j ∈ unpairedUnimod P ν, y j := by
  have h0 : (2 : ℤ_[2]) ∣ Q.eval y := by
    have := h 0
    rwa [add_zero, eval_zero2, sub_zero] at this
  have hpol : ∀ w, (2 : ℤ_[2]) ∣ y ⬝ᵥ (Q.hessian *ᵥ w) := fun w => by
    rw [← QuadForm.eval_polar Q y w]
    have : Q.eval (y + w) - Q.eval y - Q.eval w = (Q.eval (y + w) - Q.eval w) - Q.eval y := by ring
    rw [this]
    exact dvd_sub (h w) h0
  have hZ : ∀ j ∈ pairedUnimod P ν, (2 : ℤ_[2]) ∣ y j := by
    intro j hj
    obtain ⟨hp, hj0⟩ := mem_pairedUnimod.1 hj
    obtain ⟨k, hkj, hu, hz⟩ := jordan_partner hJ hp hj0
    have h1 := hpol (Pi.single k 1)
    have hs : y ⬝ᵥ (Q.hessian *ᵥ Pi.single k 1) = ∑ i, y i * Q.hessian i k := by
      simp [dotProduct, mulVec, Pi.single_apply]
    rw [hs, Finset.sum_eq_add j k (Ne.symm hkj)] at h1
    · have hkk : (2 : ℤ_[2]) ∣ y k * Q.hessian k k := by
        apply Dvd.dvd.mul_left
        rw [hessian_apply', ← two_mul]; exact dvd_mul_right _ _
      have := (dvd_add_left hkk).1 h1
      exact (IsUnit.dvd_mul_right hu).1 this
    · intro c _ ⟨hc1, hc2⟩
      rw [hz c hc1 hc2, mul_zero]
    · intro h'; exact absurd (Finset.mem_univ _) h'
    · intro h'; exact absurd (Finset.mem_univ _) h'
  refine ⟨hZ, ?_⟩
  have := dvd_sub h0 (jordan_Qmod hJ y hZ)
  simpa using this

end Jordan

end QuadFormsKB.Watson1963
