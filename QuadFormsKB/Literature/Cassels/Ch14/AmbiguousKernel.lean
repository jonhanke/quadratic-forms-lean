/-
# Cassels, Chapter 14, §6: the kernel of $\mathcal B \to \mathcal A$ and Pell's equation (14.r11)

Cassels, *Rational Quadratic Forms* (1978), Ch. 14, §6, pp. 348–350.

A primitive ambiguous form $h \in \mathcal B$ lies in the kernel of $\mathcal B \to \mathcal A$ iff it represents $1$
(`FormClass.mk_eq_one_iff`).

* **$D < 0$** (p. 348): the kernel has exactly two elements (`ncard_kernel_of_neg`); for $D \ne -4$ they are $e$ and
  $e'$ (`eq_principalForm_or_ePrime_of_represents_one`). For $D = -4$, $e = e' = [1, 0, 1]$ and the second element is
  $g(2) = [2, 2, 1]$ (Cassels: "the remaining case $D = -4$ is anomalous").
* **Pell's equation** $t^2 - Du^2 = 4$ (6.18) gives a representation of $1$ by an ambiguous form through the
  factorization $(t + 2)(t - 2) = Du^2$ (6.19), in three cases (pp. 349–350):
  (i) $t$ odd: $t + 2 = D_1u_1^2$, $t - 2 = D_2u_2^2$, $D_1D_2 = D$, $u_1 = u_2 + 2v$ and $g(D_1)(v, u_2) = 1$
  (`pell_case_odd`);
  (ii) $t \equiv 2 \pmod 4$: $t + 2 = 4X$, $t - 2 = 4Y$; for $D = 4d$ and $u = 2u'$ even (an added hypothesis,
  automatic unless $8 \mid d$), $X = d_1u_1^2$, $Y = d_2u_2^2$,
  $d_1d_2 = d$ and $f(d_1)(u_1, u_2) = 1$ (`pell_case_two_even`); for $D$ odd, $u = 4u'$, $X = D_1u_1^2$,
  $Y = D_2u_2^2$, $D_1D_2 = D$ and $g(D_1)(u_1 - u_2, 2u_2) = 1$ (`pell_case_two_odd`);
  (iii) $t \equiv 0 \pmod 4$: $t + 2 = 2X$, $t - 2 = 2Y$; for $D = 4d$, $X = d_1u_1^2$, $Y = d_2u_2^2$, $d_1d_2 = d$,
  $u_1 = u_2 + 2v$ and $g(2d_1)(v, u_2) = 1$ (`pell_case_zero_even`); for $D$ odd this case does not occur
  (`pell_case_zero_odd`).

*Reconstruction.* Several displays of pp. 349–350 are garbled in the machine-read text (the definitions of
$X, Y$ and the arguments of $g(D_1)$ in case (ii)); they are reconstructed from the surrounding argument as above.
The statements hold for every discriminant $D \ne 0$, $D \equiv 0, 1 \pmod 4$ (Cassels assumes $D > 0$ not a square);
only the hypotheses stated are used.

*Not formalized.* For $D > 0$ not a square, that the kernel has order $4$ (Lemma 4.3), the converse direction
(representations of $1$ by $h \in \mathcal B$ give solutions of Pell's equation, "left to the reader"), and that
$h \in \{e, e'\}$ only for "square" solutions.
-/
import QuadFormsKB.Literature.Cassels.Ch14.AmbiguousFG

namespace QuadFormsKB.Composition

open BinQF Binary FormClass

variable {D : ℤ}

/-! ### Helpers -/

private lemma ak_step {A B D u p : ℤ} (hp : Prime p) (hpA : p ∣ A) (hc : IsCoprime A B)
    (h : A * B = D * (p * u) ^ 2) : ∃ a : ℤ, A = p ^ 2 * a ∧ a * B = D * u ^ 2 := by
  obtain ⟨a, rfl⟩ := hpA
  have hpB : IsCoprime p B := hc.of_isCoprime_of_dvd_left (dvd_mul_right _ _)
  have h1 : a * B = D * p * u ^ 2 := by
    apply mul_left_cancel₀ hp.ne_zero
    linear_combination h
  have hpa : p ∣ a := hpB.dvd_of_dvd_mul_right ⟨D * u ^ 2, by rw [h1]; ring⟩
  obtain ⟨a', rfl⟩ := hpa
  refine ⟨a', by ring, ?_⟩
  apply mul_left_cancel₀ hp.ne_zero
  linear_combination h1

private lemma ak_fact : ∀ (n : ℕ) (A B D u : ℤ), u.natAbs = n → IsCoprime A B → A * B = D * u ^ 2 →
    ∃ D₁ D₂ u₁ u₂ : ℤ, D₁ * D₂ = D ∧ A = D₁ * u₁ ^ 2 ∧ B = D₂ * u₂ ^ 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A B D u hn hc hAB
  by_cases hu0 : u = 0
  · subst hu0
    have h0 : A * B = 0 := by simpa using hAB
    rcases mul_eq_zero.1 h0 with h | h
    · subst h
      have hB : IsUnit B := isCoprime_zero_left.1 hc
      rcases Int.isUnit_iff.1 hB with rfl | rfl
      · exact ⟨D, 1, 0, 1, by ring, by ring, by ring⟩
      · exact ⟨-D, -1, 0, 1, by ring, by ring, by ring⟩
    · subst h
      have hA : IsUnit A := isCoprime_zero_right.1 hc
      rcases Int.isUnit_iff.1 hA with rfl | rfl
      · exact ⟨1, D, 1, 0, by ring, by ring, by ring⟩
      · exact ⟨-1, -D, 1, 0, by ring, by ring, by ring⟩
  by_cases hu1 : u.natAbs = 1
  · have : u = 1 ∨ u = -1 := by omega
    rcases this with rfl | rfl
    · exact ⟨A, B, 1, 1, by linear_combination hAB, by ring, by ring⟩
    · exact ⟨A, B, 1, 1, by linear_combination hAB, by ring, by ring⟩
  obtain ⟨p, hp, u', rfl⟩ := Int.exists_prime_and_dvd hu1
  have hu'0 : u' ≠ 0 := fun h => hu0 (by simp [h])
  have hlt : u'.natAbs < n := by
    rw [← hn, Int.natAbs_mul]
    have := (Int.prime_iff_natAbs_prime.1 hp).two_le
    have : 0 < u'.natAbs := Int.natAbs_pos.2 hu'0
    nlinarith
  have hpAB : p ∣ A * B := ⟨D * p * u' ^ 2, by rw [hAB]; ring⟩
  rcases hp.dvd_or_dvd hpAB with hpA | hpB
  · obtain ⟨a, rfl, ha⟩ := ak_step hp hpA hc hAB
    obtain ⟨D₁, D₂, u₁, u₂, h1, h2, h3⟩ := ih _ hlt a B D u' rfl
      (hc.of_isCoprime_of_dvd_left ⟨p ^ 2, by ring⟩) ha
    exact ⟨D₁, D₂, p * u₁, u₂, h1, by rw [h2]; ring, h3⟩
  · obtain ⟨b, rfl, hb⟩ := ak_step (A := B) (B := A) hp hpB hc.symm (by rw [mul_comm]; exact hAB)
    obtain ⟨D₁, D₂, u₁, u₂, h1, h2, h3⟩ := ih _ hlt A b D u' rfl
      (hc.of_isCoprime_of_dvd_right ⟨p ^ 2, by ring⟩) (by rw [mul_comm]; exact hb)
    exact ⟨D₁, D₂, u₁, p * u₂, h1, h2, by rw [h3]; ring⟩

private lemma ak_cop_two {a : ℤ} (ha : a % 2 = 1) : IsCoprime a 2 :=
  ⟨1, -(a / 2), by omega⟩

private lemma ak_cop_four {a : ℤ} (ha : a % 2 = 1) : IsCoprime a 4 := by
  have := (ak_cop_two ha).mul_right (ak_cop_two ha)
  norm_num at this
  exact this

private lemma ak_cop_sub_mul {a c k : ℤ} (hk : IsCoprime a k) : IsCoprime a (a - k * c) ↔ IsCoprime a c := by
  constructor
  · rintro ⟨u, v, h⟩
    exact ⟨u + v, -(k * v), by linarith⟩
  · intro hc
    obtain ⟨u, v, h⟩ := hk.mul_right hc
    exact ⟨u + v, -v, by linarith⟩

private lemma ak_sq_odd {u : ℤ} (hu : u % 2 = 1) : ∃ s, u ^ 2 = 8 * s + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, u = 2 * m + 1 := ⟨u / 2, by omega⟩
  rcases Int.emod_two_eq_zero_or_one m with h | h
  · obtain ⟨j, rfl⟩ : ∃ j, m = 2 * j := ⟨m / 2, by omega⟩
    exact ⟨j * (2 * j + 1), by ring⟩
  · obtain ⟨j, rfl⟩ : ∃ j, m = 2 * j + 1 := ⟨m / 2, by omega⟩
    exact ⟨(2 * j + 1) * (j + 1), by ring⟩

private lemma ak_odd_of_mul_sq {a u n : ℤ} (h : a * u ^ 2 = n) (hn : n % 2 = 1) :
    a % 2 = 1 ∧ u % 2 = 1 := by
  constructor
  · by_contra hne
    obtain ⟨k, hk⟩ : ∃ k, a = 2 * k := ⟨a / 2, by omega⟩
    have : n = 2 * (k * u ^ 2) := by rw [← h, hk]; ring
    omega
  · by_contra hne
    obtain ⟨k, hk⟩ : ∃ k, u = 2 * k := ⟨u / 2, by omega⟩
    have : n = 2 * (2 * a * k ^ 2) := by rw [← h, hk]; ring
    omega

private lemma ak_even_of_mul {a u n : ℤ} (ha : a % 2 = 1) (h : a * u ^ 2 = 2 * n) : u % 2 = 0 := by
  by_contra hne
  obtain ⟨k, rfl⟩ : ∃ k, u = 2 * k + 1 := ⟨u / 2, by omega⟩
  have : a = 2 * (n - a * (2 * k ^ 2 + 2 * k)) := by linear_combination h
  omega

private lemma ak_sub_mod_four {a e : ℤ} (h : (a * e) % 4 = 1) : (a - e) % 4 = 0 := by
  have h' : (a % 4) * (e % 4) % 4 = 1 := by rw [← Int.mul_emod]; exact h
  have ha : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
  have he : e % 4 = 0 ∨ e % 4 = 1 ∨ e % 4 = 2 ∨ e % 4 = 3 := by omega
  rcases ha with ha | ha | ha | ha <;> rcases he with he | he | he | he <;>
    simp [ha, he] at h' <;> omega

private lemma ak_g (D a c : ℤ) (ha : a ≠ 0) (hD : a * (a - 4 * c) = D) (hc : IsCoprime a c) :
    ambG D a = BinQF.mk a a c ∧ (ambG D a).IsPrimitive ∧ (ambG D a).disc = D := by
  have e : ambG D a = BinQF.mk a a c := by
    have h1 : D / a = a - 4 * c := by rw [← hD]; exact Int.mul_ediv_cancel_left _ ha
    have h2 : (a - (a - 4 * c)) / 4 = c := by omega
    simp only [ambG, h1, h2]
  refine ⟨e, ?_, ?_⟩
  · rw [e]
    intro d h1 _ h3
    simp only [a_mk] at h1
    simp only [c_mk] at h3
    exact hc.isUnit_of_dvd' h1 h3
  · rw [e]
    simp only [BinQF.disc, a_mk, b_mk, c_mk]
    linear_combination hD

private lemma ak_f (D a c : ℤ) (ha : a ≠ 0) (hD : D = -4 * a * c) (hc : IsCoprime a c) :
    ambF D a = BinQF.mk a 0 c ∧ (ambF D a).IsPrimitive ∧ (ambF D a).disc = D := by
  have e : ambF D a = BinQF.mk a 0 c := by
    have h1 : -D / (4 * a) = c := by
      rw [show -D = c * (4 * a) by linarith]
      exact Int.mul_ediv_cancel _ (by omega)
    simp only [ambF, h1]
  refine ⟨e, ?_, ?_⟩
  · rw [e]
    intro d h1 _ h3
    simp only [a_mk] at h1
    simp only [c_mk] at h3
    exact hc.isUnit_of_dvd' h1 h3
  · rw [e]
    simp only [BinQF.disc, a_mk, b_mk, c_mk]
    linarith

private lemma ak_ePrime_odd {D : ℤ} (h2 : D % 2 = 1) :
    ePrime D = BinQF.mk (-D) (-D) ((-D + 1) / 4) := by
  have hD : D ≠ 0 := by omega
  have e : D / -D = -1 := by rw [Int.ediv_neg, Int.ediv_self hD]
  simp only [ePrime, h2, ↓reduceIte, ambG, e, sub_neg_eq_add]

private lemma ak_ePrime_even {D : ℤ} (h2 : D % 2 ≠ 1) (h4 : D % 4 = 0) (h0 : D ≠ 0) :
    ePrime D = BinQF.mk (-(D / 4)) 0 1 := by
  have := ak_f D (-(D / 4)) 1 (by omega) (by omega) isCoprime_one_right
  simp only [ePrime, h2, ↓reduceIte]
  exact this.1

/-! ### $D < 0$: the kernel has order $2$ -/

private lemma ak_classify (hD : D < 0) {h : BinQF}
    (hd : h.disc = D) (ha : IsAmbiguousForm h) (h1 : h.Represents 1) :
    h = principalForm D ∨ h = ePrime D ∨ (D = -4 ∧ h = BinQF.mk 2 2 1) := by
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c, h = BinQF.mk a b c :=
    ⟨h.a, h.b, h.c, BinQF.ext_abc (by simp) (by simp) (by simp)⟩
  simp only [BinQF.disc, a_mk, b_mk, c_mk] at hd
  unfold IsAmbiguousForm at ha
  simp only [a_mk, b_mk] at ha
  obtain ⟨x, y, hxy⟩ := h1
  rw [eval_eq] at hxy
  simp only [a_mk, b_mk, c_mk] at hxy
  rcases ha with hb | hb
  · -- first kind `[a, 0, c]`
    rw [hb] at hd hxy ⊢
    have hac : 0 < a * c := by linarith
    have hDe : D = -4 * a * c := by linarith
    have ha0 : a ≠ 0 := by rintro rfl; simp at hac
    have hapos : 0 < a := by
      rcases lt_or_gt_of_ne ha0 with hneg | hpos
      · exfalso
        have hcn : c < 0 := by
          by_contra hh; push Not at hh; nlinarith
        have h1 := mul_nonneg (neg_nonneg.2 hneg.le) (sq_nonneg x)
        have h2 := mul_nonneg (neg_nonneg.2 hcn.le) (sq_nonneg y)
        nlinarith
      · exact hpos
    have hcpos : 0 < c := (pos_iff_pos_of_mul_pos hac).1 hapos
    by_cases hx : x = 0
    · subst hx
      have h1 : c * y ^ 2 = 1 := by nlinarith
      have hc1 : c = 1 := Int.eq_one_of_mul_eq_one_right hcpos.le h1
      subst hc1
      right; left
      rw [ak_ePrime_even (by omega) (by omega) (by omega)]
      exact BinQF.ext_abc (by simp only [a_mk]; omega) (by simp) (by simp)
    · have hx2 : 0 < x ^ 2 := by positivity
      have hc0 := mul_nonneg hcpos.le (sq_nonneg y)
      have ha1 : a = 1 := by nlinarith
      subst ha1
      left
      exact BinQF.ext_abc (by simp [principalForm]) (by simp only [b_mk, principalForm]; omega)
        (by simp only [c_mk, principalForm]; omega)
  · -- second kind `[a, a, c]`
    rw [hb] at hd hxy ⊢
    have ha0 : a ≠ 0 := by rintro rfl; apply hD.ne; linarith
    have E4 : 4 * a = (a * (2 * x + y)) ^ 2 - D * y ^ 2 := by
      linear_combination (-4 * a) * hxy - y ^ 2 * hd
    have hDy := mul_nonneg (by linarith : (0 : ℤ) ≤ -D) (sq_nonneg y)
    have hapos : 0 < a := by
      have := sq_nonneg (a * (2 * x + y))
      have : 0 ≤ a := by nlinarith
      omega
    obtain ⟨m, hm⟩ : ∃ m, m = 4 * c - a := ⟨_, rfl⟩
    have hDm : D = -a * m := by rw [hm]; linear_combination (-1 : ℤ) * hd
    have hmpos : 0 < m := by
      by_contra hh; push Not at hh
      nlinarith [mul_nonneg hapos.le (neg_nonneg.2 hh)]
    have E : 4 = a * (2 * x + y) ^ 2 + m * y ^ 2 := by
      apply mul_left_cancel₀ ha0
      linear_combination E4 - y ^ 2 * hDm
    have hz := mul_nonneg hapos.le (sq_nonneg (2 * x + y))
    by_cases hy : y = 0
    · subst hy
      have h1 : a * x ^ 2 = 1 := by nlinarith
      have ha1 : a = 1 := Int.eq_one_of_mul_eq_one_right hapos.le h1
      subst ha1
      left
      exact BinQF.ext_abc (by simp [principalForm]) (by simp only [b_mk, principalForm]; omega)
        (by simp only [c_mk, principalForm]; omega)
    · have hy2 : 1 ≤ y ^ 2 := by
        have : 0 < y ^ 2 := by positivity
        omega
      have hm4 : m ≤ 4 := by nlinarith [mul_nonneg hmpos.le (sub_nonneg.2 hy2)]
      interval_cases m
      · right; left
        rw [ak_ePrime_odd (by omega)]
        exact BinQF.ext_abc (by simp only [a_mk]; omega) (by simp only [b_mk]; omega)
          (by simp only [c_mk]; omega)
      · by_cases hz0 : 2 * x + y = 0
        · exfalso
          have hyx : y = -2 * x := by omega
          have : (4 : ℤ) = 8 * x ^ 2 := by rw [hyx] at E; linarith
          omega
        · have hz1 : 1 ≤ (2 * x + y) ^ 2 := by
            have : 0 < (2 * x + y) ^ 2 := by positivity
            omega
          have : a ≤ 2 := by nlinarith [mul_le_mul_of_nonneg_left hz1 hapos.le]
          have ha2 : a = 2 := by omega
          have hc1 : c = 1 := by omega
          subst ha2; subst hc1
          right; right
          exact ⟨by rw [hDm]; norm_num, rfl⟩
      · left
        have hy1 : y ^ 2 ≤ 1 := by nlinarith
        have h1 : a * (2 * x + y) ^ 2 = 1 := by nlinarith
        have ha1 : a = 1 := Int.eq_one_of_mul_eq_one_right hapos.le h1
        subst ha1
        exact BinQF.ext_abc (by simp [principalForm]) (by simp only [b_mk, principalForm]; omega)
          (by simp only [c_mk, principalForm]; omega)
      · exfalso
        have h0 : a * (2 * x + y) ^ 2 = 0 := by nlinarith
        rcases mul_eq_zero.1 h0 with h | h
        · exact ha0 h
        · have hz0 : 2 * x + y = 0 := pow_eq_zero_iff two_ne_zero |>.1 h
          have hyx : y = -2 * x := by omega
          have : (4 : ℤ) = 16 * x ^ 2 := by rw [hyx] at E; linarith
          omega

/-- **The kernel of $\mathcal B \to \mathcal A$ for $D < 0$, $D \ne -4$** (Cassels, Ch. 14, §6, p. 348): *$e$ and
$e'$ are the only elements of $\mathcal B$ which can represent $+1$.* -/
@[kb "cassels1978" "Ch. 14, §6, p. 348 (kernel of 𝓑 → 𝒜 for D < 0)"]
theorem eq_principalForm_or_ePrime_of_represents_one (hD : D < 0) (hD4 : D ≠ -4) {h : BinQF}
    (hp : h.IsPrimitive) (hd : h.disc = D) (ha : IsAmbiguousForm h) (h1 : h.Represents 1) :
    h = principalForm D ∨ h = ePrime D := by
  rcases ak_classify hD hd ha h1 with h | h | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h hD4

/-- **The kernel of $\mathcal B \to \mathcal A$ has order $2$ for $D < 0$** (Cassels, Ch. 14, §6, p. 348: "when
$D < 0$ … the kernel of the map $\mathcal B \to \mathcal A$ has order precisely $2$", including the anomalous case
$D = -4$). -/
@[kb "cassels1978" "Ch. 14, §6, p. 348 (kernel of 𝓑 → 𝒜 has order 2 for D < 0)"]
theorem ncard_kernel_of_neg (hD : D < 0) (hD4 : D % 4 = 0 ∨ D % 4 = 1) :
    {h : BinQF | h.IsPrimitive ∧ h.disc = D ∧ IsAmbiguousForm h ∧ h.Represents 1}.ncard = 2 := by
  by_cases hneg : D = -4
  · subst hneg
    have hS : {h : BinQF | h.IsPrimitive ∧ h.disc = -4 ∧ IsAmbiguousForm h ∧ h.Represents 1} =
        {BinQF.mk 1 0 1, BinQF.mk 2 2 1} := by
      ext h
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨-, hd, ha, h1⟩
        rcases ak_classify hD hd ha h1 with h | h | ⟨-, h⟩
        · left; rw [h]
          exact BinQF.ext_abc (by simp only [principalForm, a_mk]) (by simp only [principalForm, b_mk]; decide)
            (by simp only [principalForm, c_mk]; decide)
        · left; rw [h, ak_ePrime_even (by decide) (by decide) (by decide)]
          exact BinQF.ext_abc (by simp only [a_mk]; decide) (by simp) (by simp)
        · right; exact h
      · rintro (rfl | rfl)
        · refine ⟨?_, ?_, Or.inl (by simp only [b_mk]), ⟨1, 0, ?_⟩⟩
          · intro d h1 _ _
            simp only [a_mk] at h1
            exact isUnit_of_dvd_one h1
          · simp only [BinQF.disc, a_mk, b_mk, c_mk]; norm_num
          · rw [eval_eq]; simp only [a_mk, b_mk, c_mk]; norm_num
        · refine ⟨?_, ?_, Or.inr (by simp only [a_mk, b_mk]), ⟨0, 1, ?_⟩⟩
          · intro d _ _ h3
            simp only [c_mk] at h3
            exact isUnit_of_dvd_one h3
          · simp only [BinQF.disc, a_mk, b_mk, c_mk]; norm_num
          · rw [eval_eq]; simp only [a_mk, b_mk, c_mk]; norm_num
    rw [hS]
    apply Set.ncard_pair
    intro h
    have := congrArg BinQF.a h
    simp only [a_mk] at this
    omega
  · have hS : {h : BinQF | h.IsPrimitive ∧ h.disc = D ∧ IsAmbiguousForm h ∧ h.Represents 1} =
        {principalForm D, ePrime D} := by
      ext h
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hp, hd, ha, h1⟩
        exact eq_principalForm_or_ePrime_of_represents_one hD hneg hp hd ha h1
      · rintro (rfl | rfl)
        · obtain ⟨hp, hd⟩ := principalForm_spec hD4
          refine ⟨hp, hd, ?_, ⟨1, 0, ?_⟩⟩
          · simp only [IsAmbiguousForm, principalForm, a_mk, b_mk]; omega
          · rw [eval_eq]; simp only [principalForm, a_mk, b_mk, c_mk]; ring
        · exact represents_one_ePrime (by omega) hD4
    rw [hS]
    apply Set.ncard_pair
    intro heq
    have ha := congrArg BinQF.a heq
    simp only [principalForm, a_mk] at ha
    by_cases h2 : D % 2 = 1
    · rw [ak_ePrime_odd h2, a_mk] at ha
      omega
    · rw [ak_ePrime_even h2 (by omega) (by omega), a_mk] at ha
      omega

/-! ### Pell's equation $t^2 - Du^2 = 4$ -/

/-- **Case (i), $t$ odd** (Cassels, Ch. 14, §6, p. 349): *if $t^2 - Du^2 = 4$ with $t$ odd, then $t + 2 = D_1u_1^2$,
$t - 2 = D_2u_2^2$ with $D_1D_2 = D$, and with $u_1 = u_2 + 2v$, $1 = g(D_1)(v, u_2)$*, where $g(D_1)$ is a
primitive ambiguous form of discriminant $D$. -/
@[kb "cassels1978" "Ch. 14, §6, p. 349 (Pell's equation, case (i))"]
theorem pell_case_odd {t u : ℤ} (h : t ^ 2 - D * u ^ 2 = 4) (ht : t % 2 = 1) :
    ∃ D₁ D₂ u₁ u₂ v : ℤ, D₁ * D₂ = D ∧ t + 2 = D₁ * u₁ ^ 2 ∧ t - 2 = D₂ * u₂ ^ 2 ∧ u₁ = u₂ + 2 * v ∧
      (ambG D D₁).IsPrimitive ∧ (ambG D D₁).disc = D ∧ (ambG D D₁).eval v u₂ = 1 := by
  have hA : (t + 2) * (t - 2) = D * u ^ 2 := by linear_combination h
  have hcop : IsCoprime (t + 2) (t - 2) := by
    obtain ⟨x, y, hxy⟩ := ak_cop_four (a := t + 2) (by omega)
    exact ⟨x + y, -y, by linear_combination hxy⟩
  obtain ⟨D₁, D₂, u₁, u₂, hDD, h1, h2⟩ := ak_fact _ _ _ _ _ rfl hcop hA
  obtain ⟨hD1, hu1⟩ := ak_odd_of_mul_sq h1.symm (by omega)
  obtain ⟨hD2, hu2⟩ := ak_odd_of_mul_sq h2.symm (by omega)
  obtain ⟨s1, hs1⟩ := ak_sq_odd hu1
  obtain ⟨s2, hs2⟩ := ak_sq_odd hu2
  have e : D₁ * u₁ ^ 2 - D₂ * u₂ ^ 2 = 4 := by linarith
  obtain ⟨c, hc⟩ : ∃ c, D₁ - D₂ = 4 * c :=
    ⟨1 - 2 * D₁ * s1 + 2 * D₂ * s2, by linear_combination e - D₁ * hs1 + D₂ * hs2⟩
  have hcopD : IsCoprime D₁ D₂ :=
    (hcop.of_isCoprime_of_dvd_left ⟨u₁ ^ 2, h1⟩).of_isCoprime_of_dvd_right ⟨u₂ ^ 2, h2⟩
  have hD1ne : D₁ ≠ 0 := by rintro rfl; omega
  have hD2e : D₁ - 4 * c = D₂ := by linarith
  have hDe : D₁ * (D₁ - 4 * c) = D := by rw [hD2e]; exact hDD
  have hcc : IsCoprime D₁ c := by
    have : IsCoprime D₁ (D₁ - 4 * c) := by rw [hD2e]; exact hcopD
    exact (ak_cop_sub_mul (ak_cop_four hD1)).1 this
  obtain ⟨he, hp, hdisc⟩ := ak_g D D₁ c hD1ne hDe hcc
  obtain ⟨v, hv⟩ : ∃ v, u₁ = u₂ + 2 * v := ⟨(u₁ - u₂) / 2, by omega⟩
  refine ⟨D₁, D₂, u₁, u₂, v, hDD, h1, h2, hv, hp, hdisc, ?_⟩
  rw [he, eval_eq]
  simp only [a_mk, b_mk, c_mk]
  rw [hv] at e
  have key : 4 * (D₁ * v ^ 2 + D₁ * v * u₂ + c * u₂ ^ 2) = 4 := by
    linear_combination e - u₂ ^ 2 * hc
  linarith

/-- **Case (ii), $t \equiv 2 \pmod 4$, $D = 4d$** (Cassels, Ch. 14, §6, p. 349; displays reconstructed): *with
$t + 2 = 4X$, $t - 2 = 4Y$: $X = d_1u_1^2$, $Y = d_2u_2^2$, $d_1d_2 = d$, and $1 = f(d_1)(u_1, u_2)$*, where
$f(d_1) = [d_1, 0, -d_2]$ is a primitive ambiguous form of discriminant $D$.

*Update (proof gap).* Cassels' factorization $16XY = Du^2$, $X = d_1u_1^2$, $Y = d_2u_2^2$ with $d_1d_2 = d$ needs $u$
even (hypothesis `hu`). This is automatic unless $8 \mid d$; for $8 \mid d$, $u$ can be odd: $D = 32$, $(t, u) = (6, 1)$
gives $X = 2$, $Y = 1$, no factorization of this shape exists, and the new form of the kernel is
$g(8) = [8, 8, 1]$, not of the shape $f(d_1)$. -/
@[kb "cassels1978" "Ch. 14, §6, p. 349 (Pell's equation, case (ii), D even)"]
theorem pell_case_two_even {d t u : ℤ} (hD : D = 4 * d) (hD0 : D ≠ 0) (h : t ^ 2 - D * u ^ 2 = 4) (ht : t % 4 = 2)
    (hu : 2 ∣ u) :
    ∃ d₁ d₂ u₁ u₂ : ℤ, d₁ * d₂ = d ∧ t + 2 = 4 * (d₁ * u₁ ^ 2) ∧ t - 2 = 4 * (d₂ * u₂ ^ 2) ∧
      (ambF D d₁).IsPrimitive ∧ (ambF D d₁).disc = D ∧ (ambF D d₁).eval u₁ u₂ = 1 := by
  obtain ⟨w, rfl⟩ := hu
  obtain ⟨Y, hY⟩ : ∃ Y, t = 4 * Y + 2 := ⟨t / 4, by omega⟩
  have hA : (Y + 1) * Y = d * w ^ 2 := by
    rw [hD, hY] at h
    have : 16 * ((Y + 1) * Y) = 16 * (d * w ^ 2) := by linear_combination h
    linarith
  have hcop : IsCoprime (Y + 1) Y := ⟨1, -1, by ring⟩
  obtain ⟨d₁, d₂, u₁, u₂, hdd, h1, h2⟩ := ak_fact _ _ _ _ _ rfl hcop hA
  have hd0 : d ≠ 0 := by rintro rfl; apply hD0; rw [hD]; ring
  have hd1ne : d₁ ≠ 0 := by rintro rfl; apply hd0; rw [← hdd]; ring
  have hcopD : IsCoprime d₁ d₂ :=
    (hcop.of_isCoprime_of_dvd_left ⟨u₁ ^ 2, h1⟩).of_isCoprime_of_dvd_right ⟨u₂ ^ 2, h2⟩
  obtain ⟨he, hp, hdisc⟩ := ak_f D d₁ (-d₂) hd1ne (by rw [hD, ← hdd]; ring) hcopD.neg_right
  refine ⟨d₁, d₂, u₁, u₂, hdd, by linarith, by linarith, hp, hdisc, ?_⟩
  rw [he, eval_eq]
  simp only [a_mk, b_mk, c_mk]
  linarith

/-- **Case (ii), $t \equiv 2 \pmod 4$, $D$ odd** (Cassels, Ch. 14, §6, p. 349; displays reconstructed): *with
$t + 2 = 4X$, $t - 2 = 4Y$: $X = D_1u_1^2$, $Y = D_2u_2^2$, $D_1D_2 = D$, $1 = D_1u_1^2 - D_2u_2^2 = g(D_1)(u_1 - u_2,
2u_2)$*, where $g(D_1)$ is a primitive ambiguous form of discriminant $D$. -/
@[kb "cassels1978" "Ch. 14, §6, p. 349 (Pell's equation, case (ii), D odd)"]
theorem pell_case_two_odd {t u : ℤ} (hD : D % 4 = 1) (h : t ^ 2 - D * u ^ 2 = 4) (ht : t % 4 = 2) :
    ∃ D₁ D₂ u₁ u₂ : ℤ, D₁ * D₂ = D ∧ t + 2 = 4 * (D₁ * u₁ ^ 2) ∧ t - 2 = 4 * (D₂ * u₂ ^ 2) ∧
      (ambG D D₁).IsPrimitive ∧ (ambG D D₁).disc = D ∧ (ambG D D₁).eval (u₁ - u₂) (2 * u₂) = 1 := by
  obtain ⟨Y, hY⟩ : ∃ Y, t = 4 * Y + 2 := ⟨t / 4, by omega⟩
  have hDo : D % 2 = 1 := by omega
  have h16 : D * u ^ 2 = 2 * (8 * ((Y + 1) * Y)) := by
    rw [hY] at h
    linear_combination (-1 : ℤ) * h
  have hu2 := ak_even_of_mul hDo h16
  obtain ⟨m, rfl⟩ : ∃ m, u = 2 * m := ⟨u / 2, by omega⟩
  have h4 : D * m ^ 2 = 2 * (2 * ((Y + 1) * Y)) := by linarith
  have hm2 := ak_even_of_mul hDo h4
  obtain ⟨w, rfl⟩ : ∃ w, m = 2 * w := ⟨m / 2, by omega⟩
  have hA : (Y + 1) * Y = D * w ^ 2 := by linarith
  have hcop : IsCoprime (Y + 1) Y := ⟨1, -1, by ring⟩
  obtain ⟨D₁, D₂, u₁, u₂, hDD, h1, h2⟩ := ak_fact _ _ _ _ _ rfl hcop hA
  have hD1 : D₁ % 2 = 1 := by
    by_contra hne
    obtain ⟨k, hk⟩ : ∃ k, D₁ = 2 * k := ⟨D₁ / 2, by omega⟩
    have : D = 2 * (k * D₂) := by rw [← hDD, hk]; ring
    omega
  have hD2 : D₂ % 2 = 1 := by
    by_contra hne
    obtain ⟨k, hk⟩ : ∃ k, D₂ = 2 * k := ⟨D₂ / 2, by omega⟩
    have : D = 2 * (k * D₁) := by rw [← hDD, hk]; ring
    omega
  have hmod : (D₁ * D₂) % 4 = 1 := by rw [hDD]; exact hD
  have hsub := ak_sub_mod_four hmod
  have e : D₁ * u₁ ^ 2 - D₂ * u₂ ^ 2 = 1 := by linarith
  obtain ⟨c, hc⟩ : ∃ c, D₁ - D₂ = 4 * c := ⟨(D₁ - D₂) / 4, by omega⟩
  have hcopD : IsCoprime D₁ D₂ :=
    (hcop.of_isCoprime_of_dvd_left ⟨u₁ ^ 2, h1⟩).of_isCoprime_of_dvd_right ⟨u₂ ^ 2, h2⟩
  have hD1ne : D₁ ≠ 0 := by rintro rfl; omega
  have hD2e : D₁ - 4 * c = D₂ := by linarith
  have hDe : D₁ * (D₁ - 4 * c) = D := by rw [hD2e]; exact hDD
  have hcc : IsCoprime D₁ c := by
    have : IsCoprime D₁ (D₁ - 4 * c) := by rw [hD2e]; exact hcopD
    exact (ak_cop_sub_mul (ak_cop_four hD1)).1 this
  obtain ⟨he, hp, hdisc⟩ := ak_g D D₁ c hD1ne hDe hcc
  refine ⟨D₁, D₂, u₁, u₂, hDD, by linarith, by linarith, hp, hdisc, ?_⟩
  rw [he, eval_eq]
  simp only [a_mk, b_mk, c_mk]
  linear_combination e - u₂ ^ 2 * hc

/-- **Case (iii), $t \equiv 0 \pmod 4$, $D = 4d$** (Cassels, Ch. 14, §6, p. 349): *with $t + 2 = 2X$, $t - 2 = 2Y$:
$X = d_1u_1^2$, $Y = d_2u_2^2$, $d_1d_2 = d \equiv 3 \pmod 4$, and with $u_1 = u_2 + 2v$, $1 = g(2d_1)(v, u_2)$*,
where $g(2d_1)$ is a primitive ambiguous form of discriminant $D$. -/
@[kb "cassels1978" "Ch. 14, §6, p. 349 (Pell's equation, case (iii), D even)"]
theorem pell_case_zero_even {d t u : ℤ} (hD : D = 4 * d) (h : t ^ 2 - D * u ^ 2 = 4) (ht : t % 4 = 0) :
    d % 4 = 3 ∧ ∃ d₁ d₂ u₁ u₂ v : ℤ, d₁ * d₂ = d ∧ t + 2 = 2 * (d₁ * u₁ ^ 2) ∧ t - 2 = 2 * (d₂ * u₂ ^ 2) ∧
      u₁ = u₂ + 2 * v ∧ (ambG D (2 * d₁)).IsPrimitive ∧ (ambG D (2 * d₁)).disc = D ∧
      (ambG D (2 * d₁)).eval v u₂ = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, t = 4 * k := ⟨t / 4, by omega⟩
  have hdu : d * u ^ 2 = 4 * k ^ 2 - 1 := by
    rw [hD] at h
    linarith
  obtain ⟨-, hu⟩ := ak_odd_of_mul_sq hdu (by omega)
  obtain ⟨s, hs⟩ := ak_sq_odd hu
  have hd3 : d % 4 = 3 := by
    have : d = 4 * (k ^ 2 - 2 * d * s) - 1 := by
      rw [hs] at hdu
      linear_combination hdu
    omega
  refine ⟨hd3, ?_⟩
  have hA : (2 * k + 1) * (2 * k - 1) = d * u ^ 2 := by rw [hdu]; ring
  have hcop : IsCoprime (2 * k + 1) (2 * k - 1) := by
    obtain ⟨x, y, hxy⟩ := ak_cop_two (a := 2 * k + 1) (by omega)
    exact ⟨x + y, -y, by linear_combination hxy⟩
  obtain ⟨d₁, d₂, u₁, u₂, hdd, h1, h2⟩ := ak_fact _ _ _ _ _ rfl hcop hA
  obtain ⟨hd1, hu1⟩ := ak_odd_of_mul_sq h1.symm (by omega)
  obtain ⟨hd2, hu2⟩ := ak_odd_of_mul_sq h2.symm (by omega)
  obtain ⟨s1, hs1⟩ := ak_sq_odd hu1
  obtain ⟨s2, hs2⟩ := ak_sq_odd hu2
  have e : d₁ * u₁ ^ 2 - d₂ * u₂ ^ 2 = 2 := by linarith
  obtain ⟨c, hc⟩ : ∃ c, d₁ - d₂ = 2 * c ∧ c % 2 = 1 :=
    ⟨1 - 4 * d₁ * s1 + 4 * d₂ * s2, by linear_combination e - d₁ * hs1 + d₂ * hs2, by
      rw [show (1 - 4 * d₁ * s1 + 4 * d₂ * s2) = 1 + 2 * (2 * d₂ * s2 - 2 * d₁ * s1) by ring]
      generalize 2 * d₂ * s2 - 2 * d₁ * s1 = z
      omega⟩
  obtain ⟨hc, hcodd⟩ := hc
  have hcopD : IsCoprime d₁ d₂ :=
    (hcop.of_isCoprime_of_dvd_left ⟨u₁ ^ 2, h1⟩).of_isCoprime_of_dvd_right ⟨u₂ ^ 2, h2⟩
  have hd1ne : d₁ ≠ 0 := by rintro rfl; omega
  have hd2e : d₁ - 2 * c = d₂ := by linarith
  have hDe : 2 * d₁ * (2 * d₁ - 4 * c) = D := by
    rw [hD, ← hdd]
    have : 2 * d₁ - 4 * c = 2 * d₂ := by linarith
    rw [this]; ring
  have hc1 : IsCoprime d₁ c := by
    have : IsCoprime d₁ (d₁ - 2 * c) := by rw [hd2e]; exact hcopD
    exact (ak_cop_sub_mul (ak_cop_two hd1)).1 this
  have hcc : IsCoprime (2 * d₁) c := IsCoprime.mul_left (ak_cop_two hcodd).symm hc1
  obtain ⟨he, hp, hdisc⟩ := ak_g D (2 * d₁) c (by omega) hDe hcc
  obtain ⟨v, hv⟩ : ∃ v, u₁ = u₂ + 2 * v := ⟨(u₁ - u₂) / 2, by omega⟩
  refine ⟨d₁, d₂, u₁, u₂, v, hdd, by linarith, by linarith, hv, hp, hdisc, ?_⟩
  rw [he, eval_eq]
  simp only [a_mk, b_mk, c_mk]
  rw [hv] at e
  have key : 2 * (2 * d₁ * v ^ 2 + 2 * d₁ * v * u₂ + c * u₂ ^ 2) = 2 := by
    linear_combination e - u₂ ^ 2 * hc
  linarith

/-- **Case (iii) does not occur for $D$ odd** (Cassels, Ch. 14, §6, p. 350: "this is a contradiction since an odd
discriminant satisfies $D \equiv 1 \pmod 4$"). -/
@[kb "cassels1978" "Ch. 14, §6, p. 350 (Pell's equation, case (iii), D odd)"]
theorem pell_case_zero_odd {t u : ℤ} (hD : D % 4 = 1) (h : t ^ 2 - D * u ^ 2 = 4) : t % 4 ≠ 0 := by
  intro ht
  obtain ⟨k, rfl⟩ : ∃ k, t = 4 * k := ⟨t / 4, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, D = 4 * m + 1 := ⟨D / 4, by omega⟩
  have hu : u % 2 = 0 := by
    by_contra hne
    obtain ⟨j, rfl⟩ : ∃ j, u = 2 * j + 1 := ⟨u / 2, by omega⟩
    have : 2 * (8 * m * j ^ 2 + 8 * m * j + 2 * m + 2 * j ^ 2 + 2 * j) + 1 = 2 * (8 * k ^ 2 - 2) := by
      linear_combination (-1 : ℤ) * h
    omega
  obtain ⟨w, rfl⟩ : ∃ w, u = 2 * w := ⟨u / 2, by omega⟩
  rcases Int.emod_two_eq_zero_or_one w with hw | hw
  · obtain ⟨j, rfl⟩ : ∃ j, w = 2 * j := ⟨w / 2, by omega⟩
    have : 4 * (4 * (k ^ 2 - (4 * m + 1) * j ^ 2)) = 4 * 1 := by linear_combination h
    omega
  · obtain ⟨j, rfl⟩ : ∃ j, w = 2 * j + 1 := ⟨w / 2, by omega⟩
    have : 4 * (4 * (k ^ 2 - (4 * m + 1) * (j ^ 2 + j) - m)) = 4 * 2 := by linear_combination h
    omega

end QuadFormsKB.Composition
