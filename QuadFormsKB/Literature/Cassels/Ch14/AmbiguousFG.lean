/-
# Cassels, Chapter 14, §6: the ambiguous forms $f(a)$, $g(a)$ and $e'$ ((6.5)–(6.7), (6.15)–(6.17))

Cassels, *Rational Quadratic Forms* (1978), Ch. 14, §6, pp. 346–348.

Cassels' notation for the primitive ambiguous forms of discriminant $D$: $f(a) = [a, 0, c]$ with $D = -4ac$ (6.5)
(`ambF`) and $g(a) = [a, a, c]$ with $D = a(a - 4c)$ (6.6) (`ambG`); the principal form is $e = f(1)$ or $g(1)$ (6.7);
the form $e' = g(-D)$ or $f(-d)$ (6.15) (`ePrime`) represents $1$; $f(a) \sim f(a')$ for $4aa' = -D$ (6.16) and
$g(a) \sim g(a')$ for $aa' = D$ (6.17). The composition law (Lemma 6.1) is in `Ch14/AmbiguousGroup.lean`, the kernel of
$\mathcal B \to \mathcal A$ and Pell's equation (14.r11) in `Ch14/AmbiguousKernel.lean`.
-/
import QuadFormsKB.Literature.Cassels.Ch14.Ambiguous

namespace QuadFormsKB.Composition

open BinQF Binary FormClass

variable {D : ℤ}

/-- **Cassels' ambiguous form $f(a) = [a, 0, c]$ with $D = -4ac$** (Cassels, Ch. 14, (6.5), p. 346). The coefficient
$c = -D/(4a)$ is an integer division; it is the right one exactly when $4a \mid D$, which the hypothesis
$\operatorname{disc} f(a) = D$ (e.g. `f.1 = ambF D a` for `f : PrimForm D`) guarantees. -/
@[kb "cassels1978" "Ch. 14, §6, (6.5), p. 346"]
def ambF (D a : ℤ) : BinQF := BinQF.mk a 0 (-D / (4 * a))

/-- **Cassels' ambiguous form $g(a) = [a, a, c]$ with $D = a(a - 4c)$** (Cassels, Ch. 14, (6.6), p. 346):
$c = (a - D/a)/4$ (integer divisions, exact when $\operatorname{disc} g(a) = D$). -/
@[kb "cassels1978" "Ch. 14, §6, (6.6), p. 346"]
def ambG (D a : ℤ) : BinQF := BinQF.mk a a ((a - D / a) / 4)

/-- **The unit $e$ for $D$ even** (Cassels, Ch. 14, (6.7), p. 346): the principal form is $f(1) = [1, 0, -D/4]$. -/
@[kb "cassels1978" "Ch. 14, §6, (6.7), p. 346 (D even)"]
theorem principalForm_eq_ambF (hD : D % 4 = 0) : principalForm D = ambF D 1 := by
  have h2 : D % 2 = 0 := by omega
  have h3 : (D % 2 - D) / 4 = -D / (4 * 1) := by omega
  simp only [principalForm, ambF, h2]
  rw [← h2, h3]

/-- **The unit $e$ for $D$ odd** (Cassels, Ch. 14, (6.7), p. 346): the principal form is
$g(1) = [1, 1, (1 - D)/4]$. -/
@[kb "cassels1978" "Ch. 14, §6, (6.7), p. 346 (D odd)"]
theorem principalForm_eq_ambG (hD : D % 4 = 1) : principalForm D = ambG D 1 := by
  have h2 : D % 2 = 1 := by omega
  simp only [principalForm, ambG, h2, Int.ediv_one]

/-! ### (6.15)–(6.17): the element $e'$ -/

/-- **The ambiguous form $e'$** (Cassels, Ch. 14, (6.15), p. 348): $e' = g(-D) = [-D, -D, (1 - D)/4]$ if $D$ is odd,
and $e' = f(-d) = [-d, 0, 1]$ if $D = 4d$. -/
@[kb "cassels1978" "Ch. 14, §6, (6.15), p. 348"]
def ePrime (D : ℤ) : BinQF := if D % 2 = 1 then ambG D (-D) else ambF D (-(D / 4))

/-- **$e'$ is a primitive ambiguous form of discriminant $D$ which represents $1$** (Cassels, Ch. 14, (6.15),
p. 348: "$g(-D)(1, -2) = 1$ and $f(-d)(0, 1) = 1$"), so it lies in the kernel of $\mathcal B \to \mathcal A$. -/
@[kb "cassels1978" "Ch. 14, §6, (6.15), p. 348"]
theorem represents_one_ePrime (hD : D ≠ 0) (hD4 : D % 4 = 0 ∨ D % 4 = 1) :
    (ePrime D).IsPrimitive ∧ (ePrime D).disc = D ∧ IsAmbiguousForm (ePrime D) ∧ (ePrime D).Represents 1 := by
  by_cases h2 : D % 2 = 1
  · obtain ⟨k, rfl⟩ : ∃ k, D = 4 * k + 1 := ⟨D / 4, by omega⟩
    have hc : (-(4 * k + 1) - (4 * k + 1) / -(4 * k + 1)) / 4 = -k := by
      rw [Int.ediv_neg, Int.ediv_self hD]; omega
    simp only [ePrime, h2, ↓reduceIte, ambG, hc]
    refine ⟨?_, ?_, Or.inr (by simp), ⟨1, -2, by rw [eval_eq]; simp only [a_mk, b_mk, c_mk]; ring⟩⟩
    · intro d ha _ hc1
      rw [a_mk] at ha; rw [c_mk] at hc1
      have h1 : d ∣ 4 * k + 1 := dvd_neg.1 ha
      have h4 : d ∣ 4 * k := Dvd.dvd.mul_left (dvd_neg.1 hc1) 4
      have := dvd_sub h1 h4
      rw [show 4 * k + 1 - 4 * k = 1 by ring] at this
      exact isUnit_of_dvd_one this
    · simp only [BinQF.disc, a_mk, b_mk, c_mk]; ring
  · have h0 : D % 4 = 0 := by omega
    have hk : D = 4 * (D / 4) := by omega
    have hd0 : D / 4 ≠ 0 := by omega
    have hc : -D / (4 * -(D / 4)) = 1 := by
      rw [show -D = (-(D / 4)) * 4 by omega, show 4 * -(D / 4) = (-(D / 4)) * 4 by ring]
      exact Int.ediv_self (by simpa using hd0)
    simp only [ePrime, h2, ↓reduceIte, ambF, hc]
    refine ⟨?_, ?_, Or.inl (by simp), ⟨0, 1, by rw [eval_eq]; simp⟩⟩
    · intro d _ _ hc1
      exact isUnit_of_dvd_one (by simpa using hc1)
    · simp only [BinQF.disc, a_mk, b_mk, c_mk]; omega

/-- **(6.16): $f(a) \sim f(a')$ with $4aa' = -D$** (Cassels, Ch. 14, (6.16), p. 348, "it is easy to verify directly
that $f(a) \sim f(a')$"): for a form $f(a)$ of discriminant $D$, $f(a)$ is properly equivalent to $f(a')$,
$a' = -D/(4a)$. -/
@[kb "cassels1978" "Ch. 14, §6, (6.16), p. 348"]
theorem sLEquiv_ambF {a : ℤ} (h : (ambF D a).disc = D) (hD : D ≠ 0) :
    SLEquiv (ambF D a) (ambF D (-D / (4 * a))) ∧ (ambF D (-D / (4 * a))).disc = D ∧ 4 * a * (-D / (4 * a)) = -D := by
  unfold ambF at h ⊢
  set c := -D / (4 * a) with hc
  have hdisc : D = -4 * a * c := by
    simp only [BinQF.disc, a_mk, b_mk, c_mk] at h; linarith
  have hc0 : c ≠ 0 := by rintro h0; rw [h0] at hdisc; simp at hdisc; exact hD hdisc
  have hc' : -D / (4 * c) = a := by
    rw [hdisc, show -(-4 * a * c) = a * (4 * c) by ring]
    exact Int.mul_ediv_cancel _ (by positivity)
  rw [hc']
  refine ⟨by simpa using sLEquiv_swap a 0 c, ?_, by linarith⟩
  simp only [BinQF.disc, a_mk, b_mk, c_mk]; linarith

/-- **(6.17): $g(a) \sim g(a')$ with $aa' = -D$** (Cassels, Ch. 14, (6.17), p. 348): for a form $g(a)$ of
discriminant $D$, $g(a)$ is properly equivalent to $g(a')$, $a' = -D/a$; explicitly $[a, a, c] \sim
[4c - a, 4c - a, c]$ by $(x, y) \mapsto (x, y - 2x)$ and a translation.

*Reconstruction.* The machine-read text has "$aa' = D$"; the sign is lost: the rule (6.13) gives
$e' * g(a) = g(a')$ with $a' = (-D)a/\gcd(-D, a)^2 = -D/a$, and for $D = -15$, $g(3) = [3, 3, 2] \sim g(5) = [5, 5, 2]$
while $g(-5)$ is negative definite. -/
@[kb "cassels1978" "Ch. 14, §6, (6.17), p. 348 (sign reconstructed)"]
theorem sLEquiv_ambG {a : ℤ} (h : (ambG D a).disc = D) (hD : D ≠ 0) :
    SLEquiv (ambG D a) (ambG D (-D / a)) ∧ (ambG D (-D / a)).disc = D ∧ a * (-D / a) = -D := by
  unfold ambG at h ⊢
  set c := (a - D / a) / 4 with hc
  have hdisc : D = a * (a - 4 * c) := by
    simp only [BinQF.disc, a_mk, b_mk, c_mk] at h; linarith
  have ha : a ≠ 0 := by rintro rfl; simp at hdisc; exact hD hdisc
  have ha' : 4 * c - a ≠ 0 := by
    intro h0; apply hD; rw [hdisc, show a - 4 * c = -(4 * c - a) by ring, h0]; ring
  have h1 : -D / a = 4 * c - a := by
    rw [hdisc, show -(a * (a - 4 * c)) = (4 * c - a) * a by ring]
    exact Int.mul_ediv_cancel _ ha
  have h2 : (4 * c - a - D / (4 * c - a)) / 4 = c := by
    rw [hdisc, show a * (a - 4 * c) = (-a) * (4 * c - a) by ring, Int.mul_ediv_cancel _ ha',
      show 4 * c - a - -a = c * 4 by ring]
    exact Int.mul_ediv_cancel _ (by norm_num)
  rw [h1, h2]
  refine ⟨?_, ?_, by rw [hdisc]; ring⟩
  · have e1 : SLEquiv (BinQF.mk a a c) (BinQF.mk (4 * c - a) (a - 4 * c) c) := by
      refine (sLEquiv_iff _ _).2 ⟨1, 0, -2, 1, by norm_num, ?_⟩
      refine ext_abc ?_ ?_ ?_ <;> simp only [subst, a_mk, b_mk, c_mk] <;> ring
    have e2 := sLEquiv_translate (4 * c - a) (a - 4 * c) c 1
    refine e1.trans ?_
    convert e2 using 2 <;> ring
  · simp only [BinQF.disc, a_mk, b_mk, c_mk]; rw [hdisc]; ring

end QuadFormsKB.Composition
