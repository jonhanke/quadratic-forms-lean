import QuadFormsKB.Historical.Gauss.Forms

/-!
# All proper transformations of a form into a contained form (Disquisitiones Arithmeticae, Arts. 213-214)

(Gauss, *Disq. Arith.* Art. 214), with the set $\Omega$ of Art. 213.

A form $f$ **properly contains** $F$ (Art. 157) if $F = f(\alpha x + \beta y, \gamma x + \delta y)$ with
$\alpha\delta - \beta\gamma = e > 0$; then $\det F = e^2 \det f$. For each factorization $e = M N$ ($M, N > 0$) and
$0 \le K < M$, Gauss writes $(M; K)$ for the form into which $f$ goes by the proper substitution
$\begin{pmatrix} M & K \\ 0 & N \end{pmatrix}$ ($x = M x' + K y'$, $y = N y'$); the finite set of these forms is
$\Omega$ (Art. 213).

**Art. 214.** All proper transformations of $f$ into $F$ are obtained, each exactly once, as follows: for each
$\Phi = (M; K) \in \Omega$ properly equivalent to $F$ and each proper transformation $(a, b, c, d)$ ($ad - bc = 1$)
of $\Phi$ into $F$, the substitution
$$\bigl(M a + K c,\ M b + K d,\ N c,\ N d\bigr).$$

In matrix language: every integer matrix $T$ of determinant $e > 0$ factors uniquely as
$T = \begin{pmatrix} M & K \\ 0 & N \end{pmatrix}\gamma$ with $\gamma \in \mathrm{SL}_2(\mathbb{Z})$, $MN = e$,
$M, N > 0$ and $0 \le K < M$ (the Hermite normal form; `exists_unique_hermite`). The form-theoretic statement is
`art214_proper_transformations`. Gauss's remark that the transformations are finite in number for $D < 0$ is not
formalized here.

Gauss's coefficients $(a, b, c)$ play no role: the statement holds for every binary form, in particular for Gauss's
forms $a x^2 + 2bxy + cy^2$, and is stated for the library's `BinQF`.
-/

namespace QuadFormsKB.Historical.Gauss

open BinQF Binary

/-- Existence half of the Hermite normal form. -/
private theorem hermite_exists {α β γ δ e : ℤ} (he : 0 < e) (hdet : α * δ - β * γ = e) :
    ∃ M K N a b c d : ℤ, 0 < M ∧ 0 ≤ K ∧ K < M ∧ M * N = e ∧ a * d - b * c = 1 ∧
      α = M * a + K * c ∧ β = M * b + K * d ∧ γ = N * c ∧ δ = N * d := by
  set g : ℤ := (Int.gcd γ δ : ℤ) with hg
  have hgc : g ∣ γ := Int.gcd_dvd_left γ δ
  have hgd : g ∣ δ := Int.gcd_dvd_right γ δ
  have hgb : g = γ * Int.gcdA γ δ + δ * Int.gcdB γ δ := Int.gcd_eq_gcd_ab γ δ
  have hg0 : 0 ≤ g := by positivity
  have hgpos : 0 < g := by
    rcases hg0.lt_or_eq with h | h
    · exact h
    · exfalso
      obtain ⟨c, hc⟩ := hgc
      obtain ⟨d, hd⟩ := hgd
      rw [← h] at hc hd
      simp at hc hd
      subst hc; subst hd
      simp at hdet; omega
  obtain ⟨c, hc⟩ := hgc
  obtain ⟨d, hd⟩ := hgd
  set u := Int.gcdA γ δ
  set v := Int.gcdB γ δ
  have hcd : c * u + d * v = 1 := by
    have : g * (c * u + d * v) = g * 1 := by
      calc g * (c * u + d * v) = γ * u + δ * v := by rw [hc, hd]; ring
        _ = g * 1 := by rw [← hgb]; ring
    exact mul_left_cancel₀ hgpos.ne' this
  have hMN : (α * d - β * c) * g = e := by rw [← hdet, hc, hd]; ring
  have hM : 0 < α * d - β * c := by
    by_contra h
    push Not at h
    nlinarith
  set M := α * d - β * c with hMdef
  set K' := α * u + β * v with hK'
  refine ⟨M, K' % M, g, v + (K' / M) * c, -u + (K' / M) * d, c, d, hM,
    Int.emod_nonneg _ hM.ne', Int.emod_lt_of_pos _ hM, hMN, ?_, ?_, ?_, hc, hd⟩
  · linear_combination hcd
  · have h1 := Int.emod_add_mul_ediv K' M
    have h2 : α = M * v + K' * c := by rw [hMdef, hK']; linear_combination (-α) * hcd
    rw [← h1] at h2
    linear_combination h2
  · have h1 := Int.emod_add_mul_ediv K' M
    have h2 : β = M * (-u) + K' * d := by rw [hMdef, hK']; linear_combination (-β) * hcd
    rw [← h1] at h2
    linear_combination h2

/-- Uniqueness half of the Hermite normal form. -/
private theorem hermite_unique {α β γ δ e : ℤ} (he : 0 < e)
    {M K N a b c d M' K' N' a' b' c' d' : ℤ}
    (hM : 0 < M) (hK0 : 0 ≤ K) (hK : K < M) (hMN : M * N = e) (hab : a * d - b * c = 1)
    (hα : α = M * a + K * c) (hβ : β = M * b + K * d) (hγ : γ = N * c) (hδ : δ = N * d)
    (hM' : 0 < M') (hK0' : 0 ≤ K') (hK' : K' < M') (hMN' : M' * N' = e)
    (hab' : a' * d' - b' * c' = 1)
    (hα' : α = M' * a' + K' * c') (hβ' : β = M' * b' + K' * d') (hγ' : γ = N' * c')
    (hδ' : δ = N' * d') :
    M = M' ∧ K = K' ∧ N = N' ∧ a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have hN : 0 < N := by
    by_contra h; push Not at h; nlinarith
  have hN' : 0 < N' := by
    by_contra h; push Not at h; nlinarith
  have hNe : N = a * δ - b * γ := by rw [hγ, hδ]; linear_combination (-N) * hab
  have hNe' : N' = a' * δ - b' * γ := by rw [hγ', hδ']; linear_combination (-N') * hab'
  have h1 : N ∣ N' := by
    rw [hNe']; exact dvd_sub (dvd_mul_of_dvd_right ⟨d, hδ⟩ _) (dvd_mul_of_dvd_right ⟨c, hγ⟩ _)
  have h2 : N' ∣ N := by
    rw [hNe]; exact dvd_sub (dvd_mul_of_dvd_right ⟨d', hδ'⟩ _) (dvd_mul_of_dvd_right ⟨c', hγ'⟩ _)
  have hNN : N = N' := Int.dvd_antisymm hN.le hN'.le h1 h2
  subst hNN
  have hc : c = c' := mul_left_cancel₀ hN.ne' (hγ.symm.trans hγ')
  have hd : d = d' := mul_left_cancel₀ hN.ne' (hδ.symm.trans hδ')
  subst hc; subst hd
  have hMM : M = M' := mul_right_cancel₀ hN.ne' (hMN.trans hMN'.symm)
  subst hMM
  have e1 : M * (a - a') = (K' - K) * c := by linear_combination hα' - hα
  have e2 : M * (b - b') = (K' - K) * d := by linear_combination hβ' - hβ
  have e3 : K' - K = M * (a * (b - b') - b * (a - a')) := by
    linear_combination (-(K' - K)) * hab - a * e2 + b * e1
  have hKK : K = K' := by
    obtain ⟨k, hk⟩ : M ∣ K' - K := ⟨_, e3⟩
    have : k = 0 := by
      by_contra hk0
      rcases lt_or_gt_of_ne hk0 with h | h
      · nlinarith
      · nlinarith
    subst this; omega
  subst hKK
  have haa : a = a' := by
    have : M * (a - a') = 0 := by rw [e1]; ring
    rcases mul_eq_zero.mp this with h | h
    · omega
    · omega
  have hbb : b = b' := by
    have : M * (b - b') = 0 := by rw [e2]; ring
    rcases mul_eq_zero.mp this with h | h
    · omega
    · omega
  exact ⟨rfl, rfl, rfl, haa, hbb, rfl, rfl⟩

/-- **The Hermite normal form of a $2 \times 2$ integer matrix of positive determinant** (the matrix content of
*Disq. Arith.* Arts. 213-214): if $\alpha\delta - \beta\gamma = e > 0$, there are unique integers $M, K, N$ and a
unique $(a, b, c, d)$ with $ad - bc = 1$ such that $M > 0$, $0 \le K < M$, $MN = e$ and
$$\begin{pmatrix} \alpha & \beta \\ \gamma & \delta \end{pmatrix} =
  \begin{pmatrix} M & K \\ 0 & N \end{pmatrix} \begin{pmatrix} a & b \\ c & d \end{pmatrix},$$
i.e. $\alpha = Ma + Kc$, $\beta = Mb + Kd$, $\gamma = Nc$, $\delta = Nd$. The tuple is
$((M, K, N), (a, b, c, d))$. -/
@[kb "gauss1801" "Art. 214, pp. 291-293"]
theorem exists_unique_hermite {α β γ δ e : ℤ} (he : 0 < e) (hdet : α * δ - β * γ = e) :
    ∃! t : (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ),
      0 < t.1.1 ∧ 0 ≤ t.1.2.1 ∧ t.1.2.1 < t.1.1 ∧ t.1.1 * t.1.2.2 = e ∧
      t.2.1 * t.2.2.2.2 - t.2.2.1 * t.2.2.2.1 = 1 ∧
      α = t.1.1 * t.2.1 + t.1.2.1 * t.2.2.2.1 ∧ β = t.1.1 * t.2.2.1 + t.1.2.1 * t.2.2.2.2 ∧
      γ = t.1.2.2 * t.2.2.2.1 ∧ δ = t.1.2.2 * t.2.2.2.2 := by
  obtain ⟨M, K, N, a, b, c, d, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hermite_exists he hdet
  refine ⟨((M, K, N), (a, b, c, d)), ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, ?_⟩
  rintro ⟨⟨M', K', N'⟩, ⟨a', b', c', d'⟩⟩ ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩
  obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := hermite_unique he h1 h2 h3 h4 h5 h6 h7 h8 h9
    g1 g2 g3 g4 g5 g6 g7 g8 g9
  subst r1 r2 r3 r4 r5 r6 r7
  rfl

/-- **Gauss, *Disq. Arith.* Art. 214: all proper transformations of $f$ into $F$**.
Let $f$ properly contain $F$ by the substitution $(\alpha, \beta, \gamma, \delta)$ of determinant $e > 0$, i.e.
$F(x, y) = f(\alpha x + \beta y, \gamma x + \delta y)$. Then there is exactly one choice of
$\Phi = (M; K) \in \Omega$ (that is $MN = e$, $M > 0$, $0 \le K < M$, $\Phi = f \circ
\begin{pmatrix} M & K \\ 0 & N\end{pmatrix}$) and of a proper transformation $(a, b, c, d)$ ($ad - bc = 1$) of $\Phi$
into $F$ such that
$$(\alpha, \beta, \gamma, \delta) = (Ma + Kc,\ Mb + Kd,\ Nc,\ Nd).$$
In particular $\Phi$ is properly equivalent to $F$. The converse (every such pair gives a proper transformation of
$f$ into $F$ of determinant $e$) is `art214_transformation_of`. -/
@[kb "gauss1801" "Art. 214, pp. 291-293"]
theorem art214_proper_transformations (f F : BinQF) {α β γ δ e : ℤ} (he : 0 < e)
    (hdet : α * δ - β * γ = e) (hF : subst α β γ δ f = F) :
    ∃! t : (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ),
      (0 < t.1.1 ∧ 0 ≤ t.1.2.1 ∧ t.1.2.1 < t.1.1 ∧ t.1.1 * t.1.2.2 = e) ∧
      (t.2.1 * t.2.2.2.2 - t.2.2.1 * t.2.2.2.1 = 1 ∧
        subst t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2 (subst t.1.1 t.1.2.1 0 t.1.2.2 f) = F) ∧
      (α = t.1.1 * t.2.1 + t.1.2.1 * t.2.2.2.1 ∧ β = t.1.1 * t.2.2.1 + t.1.2.1 * t.2.2.2.2 ∧
        γ = t.1.2.2 * t.2.2.2.1 ∧ δ = t.1.2.2 * t.2.2.2.2) := by
  obtain ⟨t, ht, hu⟩ := exists_unique_hermite he hdet
  obtain ⟨⟨M, K, N⟩, ⟨a, b, c, d⟩⟩ := t
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := ht
  simp only at h1 h2 h3 h4 h5 h6 h7 h8 h9
  have hsub : subst a b c d (subst M K 0 N f) = F := by
    rw [subst_subst, ← hF]
    have e1 : M * a + K * c = α := by rw [h6]
    have e2 : M * b + K * d = β := by rw [h7]
    have e3 : (0:ℤ) * a + N * c = γ := by rw [h8]; ring
    have e4 : (0:ℤ) * b + N * d = δ := by rw [h9]; ring
    rw [e1, e2, e3, e4]
  refine ⟨((M, K, N), (a, b, c, d)), ⟨⟨h1, h2, h3, h4⟩, ⟨h5, hsub⟩, ⟨h6, h7, h8, h9⟩⟩, ?_⟩
  rintro ⟨⟨M', K', N'⟩, ⟨a', b', c', d'⟩⟩ ⟨⟨g1, g2, g3, g4⟩, ⟨g5, -⟩, ⟨g6, g7, g8, g9⟩⟩
  exact hu _ ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩

/-- **The converse half of Art. 214:** if $\Phi = (M; K) = f \circ \begin{pmatrix} M & K \\ 0 & N\end{pmatrix}$ goes
into $F$ by the proper substitution $(a, b, c, d)$ ($ad - bc = 1$), then $f$ goes into $F$ by
$(Ma + Kc, Mb + Kd, Nc, Nd)$, a substitution of determinant $MN$. -/
@[kb "gauss1801" "Art. 214, p. 292"]
theorem art214_transformation_of (f F : BinQF) {M K N a b c d : ℤ} (hdet : a * d - b * c = 1)
    (hF : subst a b c d (subst M K 0 N f) = F) :
    subst (M * a + K * c) (M * b + K * d) (N * c) (N * d) f = F ∧
      (M * a + K * c) * (N * d) - (M * b + K * d) * (N * c) = M * N := by
  rw [← hF, subst_subst]
  refine ⟨?_, by linear_combination (M * N) * hdet⟩
  congr 1 <;> ring

end QuadFormsKB.Historical.Gauss
