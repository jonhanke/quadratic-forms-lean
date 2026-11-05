/-
# Cassels, Chapter 14: the negative Pell equation and improper equivalence; representations of $1$ by ambiguous forms

Cassels, *Rational Quadratic Forms* (1978), Ch. 14, §1, p. 333 and §6, p. 350.

* (§1, p. 333, after (1.16)) If $t^2 - Du^2 = -4$ is soluble, then every form $f$ of discriminant $D$ is improperly
  equivalent to $-f$ (`improperIntEquiv_neg_of_negPell`). Cassels refers to Chapter 13; the proof here is the
  explicit matrix $\begin{pmatrix} (t - bu)/2 & -cu \\ au & (t + bu)/2 \end{pmatrix}$ of determinant
  $(t^2 - Du^2)/4 = -1$.
* (§6, p. 350) "A representation of $1$ by an $h \in \mathcal B$ gives rise to a solution $(t, u)$ of Pell's equation
  [$t^2 - Du^2 = 4$, (6.18)]. Further, if $h = e$ or $h = e'$, then $(t, u)$ is the 'square' of another solution."
  Cassels leaves the details to the reader. The solution attached to $h(x, y) = 1$ is `pellOfRep h x y`:
  for $h = f(a) = [a, 0, c]$ it is $(4ax^2 - 2,\ 2xy)$, for $h = g(a) = [a, a, c]$ it is
  $(a(2x + y)^2 - 2,\ (2x + y)y)$ (`pellOfRep_spec`); for $h = e, e'$ it is a square (`IsPellSquare`,
  `isPellSquare_pellOfRep_principalForm`, `isPellSquare_pellOfRep_ePrime`). Here "square" is in the group of
  solutions, $(t + u\sqrt D)/2 = \pm\bigl((t_1 + u_1\sqrt D)/2\bigr)^2$; the sign is needed for $e'$ (Cassels: "in an
  appropriate sense").
-/
import QuadFormsKB.Literature.Cassels.Ch14.AmbiguousKernel
import QuadFormsKB.Literature.Cassels.Ch9Sec1
import QuadFormsKB.Binary.FormsIdeals

namespace QuadFormsKB.Composition

open BinQF Binary FormClass

/-! ### §1: the negative Pell equation and improper equivalence of $f$ and $-f$ -/

private theorem exists_half_aux (t s m : ℤ) (h : t ^ 2 - s ^ 2 = 4 * m) : ∃ k, t = s + 2 * k := by
  have h2 : (t - s) * (t + s) = 4 * m := by linear_combination h
  have h0 : (t - s) % 2 = 0 := by
    by_contra hne
    have h1 : (t - s) % 2 = 1 := by omega
    have h3 : (t + s) % 2 = 1 := by omega
    have h4 : ((t - s) * (t + s)) % 2 = 1 := by rw [Int.mul_emod, h1, h3]; norm_num
    rw [h2] at h4
    omega
  exact ⟨(t - s) / 2, by omega⟩

/-- **Cassels, Ch. 14, §1** (p. 333): *if the negative Pell equation $t^2 - Du^2 = -4$ (1.16) is soluble, then every
form $f$ of discriminant $D$ is improperly equivalent to $-f$*: there is $T \in \mathrm{GL}_2(\mathbb Z)$ with
$\det T = -1$ and $f(T\vec x) = -f(\vec x)$. No primitivity is needed. -/
@[kb "cassels1978" "Ch. 14, §1, p. 333 (t² − Du² = −4 soluble ⇒ f improperly equivalent to −f)"]
theorem improperIntEquiv_neg_of_negPell {f : BinQF} {t u : ℤ} (h : t ^ 2 - f.disc * u ^ 2 = -4) :
    Siegel.ImproperIntEquiv f f.neg := by
  simp only [BinQF.disc] at h
  obtain ⟨k, hk⟩ := exists_half_aux t (f.b * u) (-1 - f.a * f.c * u ^ 2) (by linear_combination h)
  have h4 : 4 * (k * (f.b * u + k) - (-(f.c * u)) * (f.a * u)) = 4 * (-1) := by
    rw [hk] at h; linear_combination h
  have hd : k * (f.b * u + k) - (-(f.c * u)) * (f.a * u) = -1 := by linarith
  refine ⟨Binary.glOf k (-(f.c * u)) (f.a * u) (f.b * u + k) (by rw [hd]; norm_num), ?_, ?_⟩
  · rw [Binary.glOf_val, Matrix.det_fin_two_of]; exact hd
  · rw [Binary.forall_eval_mulVec_iff, Binary.glOf_val]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    refine ext_abc ?_ ?_ ?_ <;> simp only [BinQF.subst, a_mk, b_mk, c_mk, a_neg, b_neg, c_neg]
    · linear_combination f.a * hd
    · linear_combination f.b * hd
    · linear_combination f.c * hd

/-! ### §6, p. 350: representations of $1$ by ambiguous forms and solutions of Pell's equation -/

/-- **The solution of Pell's equation attached to a representation $h(x, y) = 1$** by an ambiguous form
(Cassels, Ch. 14, §6, p. 350): $(4ax^2 - 2,\ 2xy)$ if $h = [a, 0, c]$ and $(a(2x + y)^2 - 2,\ (2x + y)y)$ otherwise
(used for $h = [a, a, c]$). -/
def pellOfRep (h : BinQF) (x y : ℤ) : ℤ × ℤ :=
  if h.b = 0 then (4 * h.a * x ^ 2 - 2, 2 * x * y) else (h.a * (2 * x + y) ^ 2 - 2, (2 * x + y) * y)

/-- **Cassels, Ch. 14, §6** (p. 350): *a representation of $1$ by an ambiguous form $h \in \mathcal B$ gives rise to a
solution $(t, u)$ of Pell's equation $t^2 - Du^2 = 4$* (6.18), $D = \operatorname{disc} h$. -/
@[kb "cassels1978" "Ch. 14, §6, p. 350 (a representation of 1 by h ∈ 𝓑 gives a solution of (6.18))"]
theorem pellOfRep_spec {h : BinQF} (hamb : IsAmbiguousForm h) {x y : ℤ} (h1 : h.eval x y = 1) :
    (pellOfRep h x y).1 ^ 2 - h.disc * (pellOfRep h x y).2 ^ 2 = 4 := by
  rw [eval_eq] at h1
  unfold pellOfRep BinQF.disc
  rcases hamb with hb | hb
  · rw [if_pos hb]
    rw [hb] at h1 ⊢
    simp only
    linear_combination (16 * h.a * x ^ 2) * h1
  · by_cases hb0 : h.b = 0
    · rw [if_pos hb0]
      rw [hb0] at h1 ⊢
      simp only
      linear_combination (16 * h.a * x ^ 2) * h1
    · rw [if_neg hb0]
      rw [hb] at h1 ⊢
      simp only
      linear_combination (4 * h.a * (2 * x + y) ^ 2) * h1

/-- **$(t, u)$ is a "square"** of a solution of $t^2 - Du^2 = 4$ (Cassels, Ch. 14, §6, p. 350, "in an appropriate
sense"): $(t + u\sqrt D)/2 = \varepsilon\bigl((t_1 + u_1\sqrt D)/2\bigr)^2$ with $t_1^2 - Du_1^2 = 4$ and
$\varepsilon = \pm 1$, i.e. $2t = \varepsilon(t_1^2 + Du_1^2)$ and $u = \varepsilon t_1u_1$. -/
def IsPellSquare (D t u : ℤ) : Prop :=
  ∃ t₁ u₁ ε : ℤ, t₁ ^ 2 - D * u₁ ^ 2 = 4 ∧ (ε = 1 ∨ ε = -1) ∧ 2 * t = ε * (t₁ ^ 2 + D * u₁ ^ 2) ∧
    u = ε * (t₁ * u₁)

/-- **Cassels, Ch. 14, §6** (p. 350), $h = e$: *if the principal form $e$ (1.11) represents $1$, the attached solution
of Pell's equation is the "square" of another solution.* -/
@[kb "cassels1978" "Ch. 14, §6, p. 350 (h = e: the solution is a square)"]
theorem isPellSquare_pellOfRep_principalForm {D : ℤ} (hD4 : D % 4 = 0 ∨ D % 4 = 1) {x y : ℤ}
    (h1 : (principalForm D).eval x y = 1) :
    IsPellSquare D (pellOfRep (principalForm D) x y).1 (pellOfRep (principalForm D) x y).2 := by
  rw [eval_eq] at h1
  rcases hD4 with h4 | h4
  · obtain ⟨d, rfl⟩ : ∃ d, D = 4 * d := ⟨D / 4, by omega⟩
    have ha : (principalForm (4 * d)).a = 1 := by simp [principalForm]
    have hb : (principalForm (4 * d)).b = 0 := by simp [principalForm]; omega
    have hc : (principalForm (4 * d)).c = -d := by simp [principalForm]; omega
    rw [ha, hb, hc] at h1
    have hp : pellOfRep (principalForm (4 * d)) x y = (4 * x ^ 2 - 2, 2 * x * y) := by
      unfold pellOfRep; rw [if_pos hb, ha]; simp
    rw [hp]
    refine ⟨2 * x, y, 1, ?_, Or.inl rfl, ?_, ?_⟩
    · linear_combination 4 * h1
    · simp only; linear_combination 4 * h1
    · simp only; ring
  · obtain ⟨k, rfl⟩ : ∃ k, D = 4 * k + 1 := ⟨D / 4, by omega⟩
    have ha : (principalForm (4 * k + 1)).a = 1 := by simp [principalForm]
    have hb : (principalForm (4 * k + 1)).b = 1 := by simp [principalForm]; omega
    have hc : (principalForm (4 * k + 1)).c = -k := by simp [principalForm]; omega
    rw [ha, hb, hc] at h1
    have hp : pellOfRep (principalForm (4 * k + 1)) x y = ((2 * x + y) ^ 2 - 2, (2 * x + y) * y) := by
      unfold pellOfRep; rw [if_neg (by rw [hb]; norm_num), ha]; simp
    rw [hp]
    refine ⟨2 * x + y, y, 1, ?_, Or.inl rfl, ?_, ?_⟩
    · linear_combination 4 * h1
    · simp only; linear_combination 4 * h1
    · simp only; ring

/-- **Cassels, Ch. 14, §6** (p. 350), $h = e'$: *if $e'$ (6.15) represents $1$, the attached solution of Pell's
equation is the "square" of another solution.* -/
@[kb "cassels1978" "Ch. 14, §6, p. 350 (h = e′: the solution is a square)"]
theorem isPellSquare_pellOfRep_ePrime {D : ℤ} (hD : D ≠ 0) (hD4 : D % 4 = 0 ∨ D % 4 = 1) {x y : ℤ}
    (h1 : (ePrime D).eval x y = 1) :
    IsPellSquare D (pellOfRep (ePrime D) x y).1 (pellOfRep (ePrime D) x y).2 := by
  rw [eval_eq] at h1
  by_cases h2 : D % 2 = 1
  · obtain ⟨k, rfl⟩ : ∃ k, D = 4 * k + 1 := ⟨D / 4, by omega⟩
    have hc : (-(4 * k + 1) - (4 * k + 1) / -(4 * k + 1)) / 4 = -k := by
      rw [Int.ediv_neg, Int.ediv_self hD]; omega
    have hE : ePrime (4 * k + 1) = BinQF.mk (-(4 * k + 1)) (-(4 * k + 1)) (-k) := by
      simp only [ePrime, h2, ↓reduceIte, ambG, hc]
    rw [hE] at h1 ⊢
    simp only [a_mk, b_mk, c_mk] at h1
    have hb0 : ¬ (-(4 * k + 1) : ℤ) = 0 := by omega
    have hp : pellOfRep (BinQF.mk (-(4 * k + 1)) (-(4 * k + 1)) (-k)) x y
        = (-(4 * k + 1) * (2 * x + y) ^ 2 - 2, (2 * x + y) * y) := by
      unfold pellOfRep; simp only [a_mk, b_mk]; rw [if_neg hb0]
    rw [hp]
    have hy : y ^ 2 - (4 * k + 1) * (2 * x + y) ^ 2 = 4 := by linear_combination 4 * h1
    refine ⟨y, -(2 * x + y), -1, ?_, Or.inr rfl, ?_, ?_⟩
    · linear_combination hy
    · simp only; linear_combination hy
    · simp only; ring
  · obtain ⟨d, rfl⟩ : ∃ d, D = 4 * d := ⟨D / 4, by omega⟩
    have hd : d ≠ 0 := by omega
    have hd4 : 4 * d / 4 = d := by omega
    have hc : -(4 * d) / (4 * -d) = 1 := by
      rw [show -(4 * d) = (-d) * 4 by ring, show 4 * -d = (-d) * 4 by ring]
      exact Int.ediv_self (by omega)
    have hE : ePrime (4 * d) = BinQF.mk (-d) 0 1 := by
      unfold ePrime ambF; rw [if_neg h2, hd4, hc]
    rw [hE] at h1 ⊢
    simp only [a_mk, b_mk, c_mk] at h1
    have hp : pellOfRep (BinQF.mk (-d) 0 1) x y = (4 * (-d) * x ^ 2 - 2, 2 * x * y) := by
      unfold pellOfRep; simp only [a_mk, b_mk, if_true]
    rw [hp]
    refine ⟨2 * y, -x, -1, ?_, Or.inr rfl, ?_, ?_⟩
    · linear_combination 4 * h1
    · simp only; linear_combination 4 * h1
    · simp only; ring

/-- **Cassels, Ch. 14, §6** (p. 350): *if the solution attached to a representation of $1$ by $h \in \mathcal B$ is not
a "square" (for example a fundamental solution), then $h$ is an element of the kernel of $\mathcal B \to \mathcal A$
other than $e$ and $e'$.* -/
@[kb "cassels1978" "Ch. 14, §6, p. 350 (a non-square solution gives h ≠ e, e′ in the kernel)"]
theorem ne_principalForm_ePrime_of_not_isPellSquare {D : ℤ} (hD : D ≠ 0) (hD4 : D % 4 = 0 ∨ D % 4 = 1)
    {h : BinQF} {x y : ℤ} (h1 : h.eval x y = 1)
    (hns : ¬ IsPellSquare D (pellOfRep h x y).1 (pellOfRep h x y).2) :
    h ≠ principalForm D ∧ h ≠ ePrime D := by
  constructor
  · rintro rfl; exact hns (isPellSquare_pellOfRep_principalForm hD4 h1)
  · rintro rfl; exact hns (isPellSquare_pellOfRep_ePrime hD hD4 h1)

end QuadFormsKB.Composition
