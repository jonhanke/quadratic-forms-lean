import QuadFormsKB.Literature.Cassels.Ch8.Bases
import QuadFormsKB.Literature.Cassels.Ch8.Primitive
import QuadFormsKB.Literature.Cassels.Ch8.Congruent
import QuadFormsKB.Siegel.UnimodularPadic

/-!
# Cassels, Chapter 8, §§2–3: running-text claims and citations

**Setting** (as in `Ch8/Bases.lean`): a form $f(\vec x) = \vec x^{t}F\vec x$ with $F \in M_n(\mathbb Q_p)$ (`qf F x`),
$2f(\vec a, \vec b) = f(\vec a + \vec b) - f(\vec a) - f(\vec b)$ (`bil F a b`), vectors of $\mathbb Z_p^n$ viewed in
$\mathbb Q_p^n$ by `toQ`.

**Proves** (Cassels, Ch. 8, §3, p. 113, read from the page image on 2026-10-30):
- `sup_bil_le_sup_qf` ((3.2)–(3.5)): there is $\vec c \in \mathbb Z_p^n$ with
  $\lvert f(\vec c)\rvert = \sup_{\vec a}\lvert f(\vec a)\rvert$ and $\lvert 2f(\vec a, \vec b)\rvert \le \lvert f(\vec c)\rvert$ for
  all $\vec a, \vec b \in \mathbb Z_p^n$ ((3.3));
- `isPrimitive_of_qf_max`: such a $\vec c$ is primitive ($\max_i\lvert c_i\rvert = 1$) when $f(\vec c) \ne 0$
  (if $\vec c = p\vec b$ then $\lvert f(\vec b)\rvert = p^{2}\lvert f(\vec c)\rvert$).

**Citations** (`attribute [kb …]`, the declarations are unchanged): $\mathbb Z_p$ is a principal ideal domain with
nonzero ideals $p^m\mathbb Z_p$ (§2, p. 112; Mathlib); the symmetry $\tau_{\vec b}$ ((3.7), p. 113); Lemma 3.4 in its
exact form and the two steps of its proof (p. 115).
-/

namespace QuadFormsKB.Cassels

open Matrix

variable {n : ℕ} {p : ℕ} [hp : Fact p.Prime]

/-- **Cassels, Ch. 8, (3.2)–(3.5)** (p. 113): *the suprema in $\sup_{\vec a, \vec b}\lvert 2f(\vec a, \vec b)\rvert \le
\sup_{\vec a}\lvert f(\vec a)\rvert$ (3.3), over $\vec a, \vec b \in \mathbb Z_p^n$ (3.4), are attained; in particular there
is $\vec c \in \mathbb Z_p^n$ with $\lvert f(\vec c)\rvert = \sup_{\vec a}\lvert f(\vec a)\rvert$ (3.5).* Here
$2f(\vec a, \vec b) = f(\vec a + \vec b) - f(\vec a) - f(\vec b)$ is `bil F a b` ((3.2), `qf_add`). Cassels assumes $f$
regular; this is not needed. -/
@[kb "cassels1978" "Ch. 8, §3, (3.2)–(3.5), p. 113"]
theorem sup_bil_le_sup_qf (F : Matrix (Fin n) (Fin n) ℚ_[p]) :
    ∃ c : Fin n → ℤ_[p], (∀ a, ‖qf F (toQ a)‖ ≤ ‖qf F (toQ c)‖) ∧
      ∀ a b : Fin n → ℤ_[p], ‖bil F (toQ a) (toQ b)‖ ≤ ‖qf F (toQ c)‖ := by
  obtain ⟨c, hc⟩ := exists_qf_max F
  refine ⟨c, hc, fun a b => ?_⟩
  have e : bil F (toQ a) (toQ b) = qf F (toQ (a + b)) - qf F (toQ a) - qf F (toQ b) := by
    have : toQ (a + b) = toQ a + toQ b := by ext i; simp [toQ]
    rw [this, qf_add]; ring
  rw [e, sub_eq_add_neg, sub_eq_add_neg]
  refine (Padic.nonarchimedean _ _).trans (max_le ((Padic.nonarchimedean _ _).trans (max_le (hc _) ?_)) ?_)
  · rw [norm_neg]; exact hc a
  · rw [norm_neg]; exact hc b

/-- **Cassels, Ch. 8, §3** (p. 113): *$\vec c$ with $\lvert f(\vec c)\rvert = \sup_{\vec a}\lvert f(\vec a)\rvert$ must be
primitive, since if $\vec c = p\vec b$ with $\vec b \in \mathbb Z_p^n$ then $\lvert f(\vec b)\rvert = p^{2}\lvert f(\vec c)\rvert$*
(assuming $f(\vec c) \ne 0$, which holds for regular $f$). Primitive: $\max_i\lvert c_i\rvert_p = 1$. -/
@[kb "cassels1978" "Ch. 8, §3, p. 113 (a vector attaining the supremum is primitive)"]
theorem isPrimitive_of_qf_max (F : Matrix (Fin n) (Fin n) ℚ_[p]) {c : Fin n → ℤ_[p]}
    (hc : ∀ a, ‖qf F (toQ a)‖ ≤ ‖qf F (toQ c)‖) (h0 : qf F (toQ c) ≠ 0) : ∃ i, ‖c i‖ = 1 := by
  by_contra hne
  push_neg at hne
  have hdvd : ∀ i, (p : ℤ_[p]) ∣ c i := fun i =>
    PadicInt.norm_lt_one_iff_dvd _ |>.1 (lt_of_le_of_ne (PadicInt.norm_le_one _) (hne i))
  choose b hb using hdvd
  have hcb : toQ c = (p : ℚ_[p]) • toQ b := by ext i; simp [toQ, hb i]
  have hq : qf F (toQ c) = (p : ℚ_[p]) ^ 2 * qf F (toQ b) := by
    rw [hcb]; simp only [qf, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]; ring
  have h1 := hc b
  rw [hq, norm_mul, norm_pow, Padic.norm_p] at h1
  have hb0 : 0 < ‖qf F (toQ b)‖ := norm_pos_iff.2 (fun h => h0 (by rw [hq, h, mul_zero]))
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have : (p : ℝ)⁻¹ ^ 2 < 1 := by
    rw [inv_pow]; exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ hp1 (by norm_num))
  nlinarith

end QuadFormsKB.Cassels

namespace QuadFormsKB

-- 8.r7: ℤ_p is a principal ideal domain whose nonzero ideals are the p^m ℤ_p (Mathlib).
attribute [kb "cassels1978" "Ch. 8, §2, p. 112 (the nonzero ideals of ℤ_p are p^m ℤ_p; Mathlib)"]
  PadicInt.ideal_eq_span_pow_p

-- 8.r10: the symmetry τ_b(x) = x - (2f(b, x)/f(b)) b, a ℚ_p-automorphism of f (recalled from Ch. 2, §4).
attribute [kb "cassels1978" "Ch. 8, §3, (3.7), p. 113 (the symmetry τ_b)"] Cassels.tauFun
attribute [kb "cassels1978" "Ch. 8, §3, (3.7), p. 113 (τ_b is a ℚ_p-automorphism of f)"] Cassels.qf_tauFun

-- 8:Lemma 3.4, exact form: ⟨u₀, …, u_k⟩ ≅ ⟨1, …, 1, u₀ ⋯ u_k⟩ over ℤ_p for units, p odd (0-based: Cassels' u₁, …, uₙ).
attribute [kb "cassels1978" "Ch. 8, Lemma 3.4, p. 115 (exact form; 0-based indices)"]
  Siegel.Kneser.isometricGL_diag_normal

-- 8.p1: proof of Lemma 3.4 (n = 2): u₁x² + u₂y² represents 1 (Hensel), and the representation extends to an
-- equivalence (here by the explicit rotation).
attribute [kb "cassels1978" "Ch. 8, proof of Lemma 3.4, p. 115 (u₁x² + u₂y² represents 1)"]
  Siegel.Kneser.exists_binary_one
attribute [kb "cassels1978" "Ch. 8, proof of Lemma 3.4, p. 115 (the representation extends to an equivalence)"]
  Siegel.Kneser.isometricGL_diag_rot

-- 8.p3: proof of Lemma 5.1 (pp. 123–124): one step F ↦ F₁ = (I + S)ᵗF(I + S) with S = ½F⁻¹(G − F) ((5.8)), the error
-- G − F₁ = −SᵗFS being of the square size ((5.9), (5.10)); and the successive approximation.
attribute [kb "cassels1978" "Ch. 8, proof of Lemma 5.1, (5.8)–(5.10), pp. 123–124 (one approximation step)"]
  Cassels.newton_step
attribute [kb "cassels1978" "Ch. 8, proof of Lemma 5.1, pp. 123–124 (successive approximation)"]
  Cassels.exists_approx

end QuadFormsKB
