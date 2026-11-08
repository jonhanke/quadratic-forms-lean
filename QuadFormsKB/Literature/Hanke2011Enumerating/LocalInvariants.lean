/-
# Hanke 2011, §5: Gan–Hanke–Yu local invariants and the standard local invariants (Lemma 5.1)

J. Hanke, *Enumerating maximal definite quadratic forms of bounded class number over $\mathbb Z$ in $n\ge3$ variables*,
arXiv:1110.1876v1 (bib key `hanke2011enumerating`), §5, pp. 8–9.

**Setting.** $K$ is a local field in the sense of `PadicClass.LocalHilbertField` (bimultiplicative Hilbert symbol; for
example $\mathbb Q_p$, `PadicClass.localHilbertField_padic`). A quadratic space is a diagonal form
$\langle a_0,\dots,a_{n-1}\rangle$, $a_i\in K^\times$ (every non-degenerate space over $K$ is one); its standard invariants are
$(n, d, c)$ with $d = \prod_ia_i$ (modulo squares) and $c$ Serre's Hasse invariant $\prod_{i<j}(a_i, a_j)$
(`PadicClass.hasseVec`). The paper's formula $(n,d,c)\oplus(n',d',c') = (n+n', dd', cc'(d,d'))$ is
`hasseVec_append` here. $\varepsilon := (-1,-1)_K$. $H^k$ is the sum of $k$ hyperbolic planes $\langle1,-1\rangle$
(`hypCons k w` $= H^k\perp\langle w\rangle$).

**Proves** the table of Lemma 5.1: the standard invariants of the five model spaces
$H^r$, $H^{r-2}\oplus D$, $H^{r-1}\oplus\alpha\langle1,-\delta\rangle$, $H^r\oplus\langle\delta\rangle$,
$H^{r-1}\oplus-\delta\langle a, b, ab\rangle$ (`lemma_5_1_row_H`, `lemma_5_1_row_D`, `lemma_5_1_row_binary`,
`lemma_5_1_row_unary`, `lemma_5_1_row_ternary`), with $D = \langle1,-a,-b,ab\rangle$, $(a,b) = -1$ (the anisotropic
quaternary space) and $(-a,-b) = -1$ (so that $\langle a,b,ab\rangle$ is anisotropic); and the explicit bijection
$(n,\delta,w)\leftrightarrow(n,d,c)$ (`stdOfGHY`, `ghyOfStd`, `ghyOfStd_stdOfGHY`, `stdOfGHY_ghyOfStd`) under which
each model space with Gan–Hanke–Yu invariants $(n,\delta,w)$ of the table has standard invariants `stdOfGHY n δ w`
(`lemma_5_1_H`, …). *Deviation:* Gan–Hanke–Yu's $w_v$ is not defined in the library from the space; here the table is the
definition (`ghyOfStd`), and the rows show it gives each model space the $w$ listed by the paper.
-/
import QuadFormsKB.Literature.LocalGlobal.PadicClassification
import QuadFormsKB.Citation

open QuadFormsKB.PadicClass

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2011Enumerating

variable {K : Type*} [Field K] [CharZero K]

/-! ### Hyperbolic planes and the direct-sum formula -/

/-- $H^k\perp\langle w\rangle$: the diagonal form $\langle1,-1,\dots,1,-1, w_0,\dots,w_{m-1}\rangle$ with $k$ hyperbolic planes
$\langle1,-1\rangle$ in front. -/
def hypCons {m : ℕ} : (k : ℕ) → (Fin m → K) → (Fin (m + 2 * k) → K)
  | 0, w => w
  | k + 1, w => Fin.cons 1 (Fin.cons (-1) (hypCons k w))

theorem hypCons_ne_zero {m : ℕ} {w : Fin m → K} (hw : ∀ i, w i ≠ 0) : ∀ k i, hypCons k w i ≠ 0 := by
  intro k
  induction k with
  | zero => exact hw
  | succ k ih =>
    intro i
    refine Fin.cases (by simp [hypCons]) (fun j => ?_) i
    refine Fin.cases (by simp [hypCons]) (fun l => ?_) j
    simpa [hypCons] using ih l

theorem prod_hypCons {m : ℕ} (w : Fin m → K) : ∀ k, ∏ i, hypCons k w i = (-1) ^ k * ∏ i, w i := by
  intro k
  induction k with
  | zero => simp [hypCons]
  | succ k ih =>
    show ∏ i, (Fin.cons 1 (Fin.cons (-1) (hypCons k w)) : Fin (m + 2 * k + 1 + 1) → K) i = _
    rw [Fin.prod_cons, Fin.prod_cons, ih, pow_succ]; ring

/-- $\varepsilon^k\varepsilon^{\lfloor k/2\rfloor} = \varepsilon^{\lfloor(k+1)/2\rfloor}$ for $\varepsilon = \pm1$. -/
theorem pm_pow_floor {s : ℤ} (hs : s = 1 ∨ s = -1) (k : ℕ) : s ^ k * s ^ (k / 2) = s ^ ((k + 1) / 2) := by
  rcases hs with rfl | rfl
  · simp
  · obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
    · have h1 : (2 * j + 1) / 2 = j := by omega
      have h2 : 2 * j / 2 = j := by omega
      rw [h1, h2, pow_mul]; simp
    · have h1 : (2 * j + 1 + 1) / 2 = j + 1 := by omega
      have h2 : (2 * j + 1) / 2 = j := by omega
      rw [h1, h2, pow_succ, pow_succ, pow_mul]; simp

variable (hK : LocalHilbertField K)
include hK

theorem hs_negpow_left {y : K} (hy : y ≠ 0) (k : ℕ) :
    hilbertSymbol K ((-1) ^ k) y = hilbertSymbol K (-1) y ^ k := by
  induction k with
  | zero => simp [hs_one_left]
  | succ k ih =>
    rw [pow_succ, hK.mul_left _ _ _ (pow_ne_zero _ (by norm_num)) (by norm_num) hy, ih, pow_succ]

/-- **The Hasse invariant of $H^k\perp W$** (Hanke 2011, Lemma 5.1, proof: "$(n,d,c)\oplus(n',d',c') =
(n+n', dd', cc'(d,d')_v)$" and "$H^r$ has standard invariants $(2r, (-1)^r, (-1,-1)_v^{\lfloor r/2\rfloor})$"):
$c(H^k\perp W) = \varepsilon^{\lfloor k/2\rfloor}\,((-1)^k, dW)\,c(W)$. -/
@[kb "hanke2011enumerating" "Lemma 5.1, proof, p. 8 (standard invariants of H^r ⊕ W)"]
theorem hasseVec_hypCons {m : ℕ} {w : Fin m → K} (hw : ∀ i, w i ≠ 0) (k : ℕ) :
    hasseVec (hypCons k w) =
      hilbertSymbol K (-1) (-1) ^ (k / 2) * hilbertSymbol K ((-1) ^ k) (∏ i, w i) * hasseVec w := by
  have hP : (∏ i, w i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hw i
  induction k with
  | zero => simp [hypCons, hs_one_left]
  | succ k ih =>
    have hX := hypCons_ne_zero hw k
    have hX' : ∀ i, (Fin.cons (-1) (hypCons k w) : Fin (m + 2 * k + 1) → K) i ≠ 0 :=
      fun i => Fin.cases (by norm_num) (fun j => hX j) i
    show hasseVec (Fin.cons 1 (Fin.cons (-1) (hypCons k w)) : Fin (m + 2 * k + 1 + 1) → K) = _
    rw [hasseVec_cons hK one_ne_zero hX', hs_one_left, one_mul, hasseVec_cons hK (by norm_num) hX, ih,
      prod_hypCons, hK.mul_right (by norm_num) (pow_ne_zero _ (by norm_num)) hP]
    rw [hilbertSymbol_comm K (-1) ((-1) ^ k), hs_negpow_left hK (by norm_num : (-1 : K) ≠ 0) k,
      hs_negpow_left hK hP k, hs_negpow_left hK hP (k + 1), ← pm_pow_floor (hs_pm (-1 : K) (-1)) k, pow_succ]
    ring

/-! ### The rows of the table of Lemma 5.1 -/

/-- **Lemma 5.1, row $H^r$** (Hanke 2011, p. 9): $d(H^r) = (-1)^r$, $c(H^r) = \varepsilon^{\lfloor r/2\rfloor}$. -/
@[kb "hanke2011enumerating" "Lemma 5.1, table, p. 9 (row H^r)"]
theorem lemma_5_1_row_H (r : ℕ) :
    ∏ i, hypCons r (![] : Fin 0 → K) i = (-1) ^ r ∧
      hasseVec (hypCons r (![] : Fin 0 → K)) = hilbertSymbol K (-1) (-1) ^ (r / 2) := by
  refine ⟨by simp [prod_hypCons], ?_⟩
  rw [hasseVec_hypCons hK (fun i => Fin.elim0 i)]
  simp [hilbertSymbol_one_right, hasseVec]

/-- $c(\langle1,-a,-b,ab\rangle) = (a,b)\,\varepsilon$. -/
theorem hasseVec_quaternary {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    hasseVec ![1, -a, -b, a * b] = hilbertSymbol K a b * hilbertSymbol K (-1) (-1) := by
  have m1 : (-1 : K) ≠ 0 := by norm_num
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  have hv : ∀ i, (![-a, -b, a * b] : Fin 3 → K) i ≠ 0 := by
    intro i; fin_cases i <;> simp [ha, hb]
  rw [show (![1, -a, -b, a * b] : Fin 4 → K) = Fin.cons 1 ![-a, -b, a * b] from rfl,
    hasseVec_cons hK one_ne_zero hv, hs_one_left, one_mul, hasseVec_three]
  have e1 : hilbertSymbol K (-a) (-b) = hilbertSymbol K (-1) (-1) * hilbertSymbol K b (-1) *
      hilbertSymbol K a (-1) * hilbertSymbol K a b := by
    rw [show -a = -1 * a by ring, show -b = -1 * b by ring, hK.mul_left (-1) a (-1 * b) m1 ha (mul_ne_zero m1 hb),
      hK.mul_right m1 m1 hb, hK.mul_right ha m1 hb, hilbertSymbol_comm K (-1) b]; ring
  have e2 : hilbertSymbol K (-a) (a * b) = hilbertSymbol K a (-1) * hilbertSymbol K b (-1) *
      hilbertSymbol K a (-1) * hilbertSymbol K a b := by
    rw [show -a = -1 * a by ring, hK.mul_left (-1) a (a * b) m1 ha hab, hK.mul_right m1 ha hb, hK.mul_right ha ha hb,
      hK.self ha, hilbertSymbol_comm K (-1) a, hilbertSymbol_comm K (-1) b]; ring
  have e3 : hilbertSymbol K (-b) (a * b) = hilbertSymbol K a (-1) * hilbertSymbol K b (-1) *
      hilbertSymbol K a b * hilbertSymbol K b (-1) := by
    rw [show -b = -1 * b by ring, hK.mul_left (-1) b (a * b) m1 hb hab, hK.mul_right m1 ha hb, hK.mul_right hb ha hb,
      hK.self hb, hilbertSymbol_comm K (-1) a, hilbertSymbol_comm K (-1) b, hilbertSymbol_comm K b a]; ring
  rw [e1, e2, e3]
  rcases hs_pm (-1 : K) (-1) with h1 | h1 <;> rcases hs_pm a (-1 : K) with h2 | h2 <;>
    rcases hs_pm b (-1 : K) with h3 | h3 <;> rcases hs_pm a b with h4 | h4 <;> simp [h1, h2, h3, h4]

/-- $c(\langle-\delta a,-\delta b,-\delta ab\rangle) = (-1,\delta)\,(-a,-b)$. -/
theorem hasseVec_ternary {δ a b : K} (hδ : δ ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    hasseVec ![-δ * a, -δ * b, -δ * (a * b)] = hilbertSymbol K (-1) δ * hilbertSymbol K (-a) (-b) := by
  have m1 : (-1 : K) ≠ 0 := by norm_num
  have hu : -δ ≠ 0 := neg_ne_zero.2 hδ
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  set u := -δ with hudef
  rw [hasseVec_three]
  have f1 : hilbertSymbol K (u * a) (u * b) = hilbertSymbol K u (-1) * hilbertSymbol K u b *
      hilbertSymbol K u a * hilbertSymbol K a b := by
    rw [hK.mul_left u a (u * b) hu ha (mul_ne_zero hu hb), hK.mul_right hu hu hb, hK.mul_right ha hu hb, hK.self hu,
      hilbertSymbol_comm K a u]; ring
  have f2 : hilbertSymbol K (u * a) (u * (a * b)) = hilbertSymbol K u (-1) * hilbertSymbol K u a *
      hilbertSymbol K u b * hilbertSymbol K u a * hilbertSymbol K a (-1) * hilbertSymbol K a b := by
    rw [hK.mul_left u a (u * (a * b)) hu ha (mul_ne_zero hu hab), hK.mul_right hu hu hab, hK.mul_right ha hu hab,
      hK.mul_right hu ha hb, hK.mul_right ha ha hb, hK.self hu, hK.self ha, hilbertSymbol_comm K a u]; ring
  have f3 : hilbertSymbol K (u * b) (u * (a * b)) = hilbertSymbol K u (-1) * hilbertSymbol K u a *
      hilbertSymbol K u b * hilbertSymbol K u b * hilbertSymbol K a b * hilbertSymbol K b (-1) := by
    rw [hK.mul_left u b (u * (a * b)) hu hb (mul_ne_zero hu hab), hK.mul_right hu hu hab, hK.mul_right hb hu hab,
      hK.mul_right hu ha hb, hK.mul_right hb ha hb, hK.self hu, hK.self hb, hilbertSymbol_comm K b u,
      hilbertSymbol_comm K b a]; ring
  have g1 : hilbertSymbol K (-a) (-b) = hilbertSymbol K (-1) (-1) * hilbertSymbol K b (-1) *
      hilbertSymbol K a (-1) * hilbertSymbol K a b := by
    rw [show -a = -1 * a by ring, show -b = -1 * b by ring, hK.mul_left (-1) a (-1 * b) m1 ha (mul_ne_zero m1 hb),
      hK.mul_right m1 m1 hb, hK.mul_right ha m1 hb, hilbertSymbol_comm K (-1) b]; ring
  have g2 : hilbertSymbol K u (-1) = hilbertSymbol K (-1) (-1) * hilbertSymbol K (-1) δ := by
    rw [hudef, show -δ = -1 * δ by ring, hK.mul_left (-1) δ (-1) m1 hδ m1, hilbertSymbol_comm K δ (-1)]
  rw [f1, f2, f3, g1, g2]
  rcases hs_pm (-1 : K) (-1) with h1 | h1 <;> rcases hs_pm (-1 : K) δ with h2 | h2 <;>
    rcases hs_pm u a with h3 | h3 <;> rcases hs_pm u b with h4 | h4 <;> rcases hs_pm a b with h5 | h5 <;>
    rcases hs_pm a (-1 : K) with h6 | h6 <;> rcases hs_pm b (-1 : K) with h7 | h7 <;>
    simp [h1, h2, h3, h4, h5, h6, h7]

/-- **Lemma 5.1, row $H^{r-2}\oplus D$** (Hanke 2011, p. 9; Gan–Hanke–Yu type I, $\delta = 1$, $w = -1$), $r = k + 2$, for the
anisotropic quaternary space $D = \langle1,-a,-b,ab\rangle$ ($(a,b) = -1$): $d = (-1)^r$ (modulo squares) and
$c = -\varepsilon^{\lfloor r/2\rfloor}$. -/
@[kb "hanke2011enumerating" "Lemma 5.1, table, p. 9 (row H^{r-2} ⊕ D)"]
theorem lemma_5_1_row_D (k : ℕ) {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) (hab : hilbertSymbol K a b = -1) :
    ∏ i, hypCons k ![1, -a, -b, a * b] i = (-1) ^ (k + 2) * (a * b) ^ 2 ∧
      hasseVec (hypCons k ![1, -a, -b, a * b]) = -hilbertSymbol K (-1) (-1) ^ ((k + 2) / 2) := by
  have hv : ∀ i, (![1, -a, -b, a * b] : Fin 4 → K) i ≠ 0 := by
    intro i; fin_cases i <;> simp [ha, hb]
  have hP : ∏ i, (![1, -a, -b, a * b] : Fin 4 → K) i = (a * b) ^ 2 := by
    simp [Fin.prod_univ_four]; ring
  refine ⟨by rw [prod_hypCons, hP]; ring, ?_⟩
  rw [hasseVec_hypCons hK hv, hP, hs_sq _ _ (mul_ne_zero ha hb), hasseVec_quaternary hK ha hb, hab,
    show (k + 2) / 2 = k / 2 + 1 by omega, pow_succ]
  ring

/-- **Lemma 5.1, row $H^{r-1}\oplus\alpha\langle1,-\delta\rangle$** (Hanke 2011, p. 9; Gan–Hanke–Yu types II, III), $r = k + 1$:
$d = (-1)^r\alpha^2\delta$ and $c = \varepsilon^{\lfloor(r-1)/2\rfloor}\,w\,((-1)^{r-1},-\delta)$ with $w = c_{\mathrm{aniso}} =
(\alpha,-\alpha\delta)$. -/
@[kb "hanke2011enumerating" "Lemma 5.1, table, p. 9 (row H^{r-1} ⊕ α(x² - δy²))"]
theorem lemma_5_1_row_binary (k : ℕ) {α δ : K} (hα : α ≠ 0) (hδ : δ ≠ 0) :
    ∏ i, hypCons k ![α, -α * δ] i = (-1) ^ (k + 1) * α ^ 2 * δ ∧
      hasseVec (hypCons k ![α, -α * δ]) =
        hilbertSymbol K (-1) (-1) ^ (k / 2) * hilbertSymbol K α (-α * δ) * hilbertSymbol K ((-1) ^ k) (-δ) := by
  have hv : ∀ i, (![α, -α * δ] : Fin 2 → K) i ≠ 0 := by
    intro i; fin_cases i <;> simp [hα, hδ]
  have hP : ∏ i, (![α, -α * δ] : Fin 2 → K) i = α ^ 2 * (-δ) := by
    simp [Fin.prod_univ_two]; ring
  refine ⟨by rw [prod_hypCons, hP]; ring, ?_⟩
  rw [hasseVec_hypCons hK hv, hP, hs_sq_right _ _ _ hα, hasseVec_two]
  ring

/-- **Lemma 5.1, row $H^r\oplus\langle\delta\rangle$** (Hanke 2011, p. 9; Gan–Hanke–Yu types –, I, $w = 1$): $d = (-1)^r\delta$ and
$c = \varepsilon^{\lfloor r/2\rfloor}((-1)^r,\delta)$. -/
@[kb "hanke2011enumerating" "Lemma 5.1, table, p. 9 (row H^r ⊕ δx²)"]
theorem lemma_5_1_row_unary (r : ℕ) {δ : K} (hδ : δ ≠ 0) :
    ∏ i, hypCons r ![δ] i = (-1) ^ r * δ ∧
      hasseVec (hypCons r ![δ]) = hilbertSymbol K (-1) (-1) ^ (r / 2) * hilbertSymbol K ((-1) ^ r) δ := by
  have hv : ∀ i, (![δ] : Fin 1 → K) i ≠ 0 := by intro i; fin_cases i; simpa using hδ
  refine ⟨by rw [prod_hypCons]; simp, ?_⟩
  rw [hasseVec_hypCons hK hv]
  simp [hasseVec]

/-- **Lemma 5.1, row $H^{r-1}\oplus-\delta\langle a,b,ab\rangle$** (Hanke 2011, p. 9; Gan–Hanke–Yu types II$^\pm$, $w = -1$), $r = k + 1$,
for the anisotropic ternary space ($(-a,-b) = -1$): $d = (-1)^r\delta$ (modulo squares) and
$c = -\varepsilon^{\lfloor(r-1)/2\rfloor}((-1)^{r-1},-\delta)(-1,\delta)$. -/
@[kb "hanke2011enumerating" "Lemma 5.1, table, p. 9 (row H^{r-1} ⊕ -δ(ax² + by² + abz²))"]
theorem lemma_5_1_row_ternary (k : ℕ) {δ a b : K} (hδ : δ ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : hilbertSymbol K (-a) (-b) = -1) :
    ∏ i, hypCons k ![-δ * a, -δ * b, -δ * (a * b)] i = (-1) ^ (k + 1) * δ * (δ * a * b) ^ 2 ∧
      hasseVec (hypCons k ![-δ * a, -δ * b, -δ * (a * b)]) =
        -(hilbertSymbol K (-1) (-1) ^ (k / 2) * hilbertSymbol K ((-1) ^ k) (-δ) * hilbertSymbol K (-1) δ) := by
  have hv : ∀ i, (![-δ * a, -δ * b, -δ * (a * b)] : Fin 3 → K) i ≠ 0 := by
    intro i; fin_cases i <;> simp [hδ, ha, hb]
  have hP : ∏ i, (![-δ * a, -δ * b, -δ * (a * b)] : Fin 3 → K) i = (δ * a * b) ^ 2 * (-δ) := by
    simp [Fin.prod_univ_three]; ring
  refine ⟨by rw [prod_hypCons, hP]; ring, ?_⟩
  rw [hasseVec_hypCons hK hv, hP, hs_sq_right _ _ _ (mul_ne_zero (mul_ne_zero hδ ha) hb),
    hasseVec_ternary hK hδ ha hb, hab]
  ring

omit hK in
/-! ### The bijection $(n,\delta,w)\leftrightarrow(n,d,c)$ -/

/-- The factor $\mu(n,\delta)$ of the table of Lemma 5.1 (Hanke 2011, p. 9): $c = w\,\mu(n,\delta)$ with
$\mu(2r,\delta) = \varepsilon^{\lfloor(r-1)/2\rfloor}((-1)^{r-1},-\delta)$ and $\mu(2r+1,\delta) = \varepsilon^{\lfloor r/2\rfloor}((-1)^r,\delta)$
(the even formula covers the rows $H^r$, $H^{r-2}\oplus D$ with $\delta = 1$ and the row of types II, III; the odd one
both odd rows). -/
@[kb "hanke2011enumerating" "Lemma 5.1, table, p. 9 (c as a function of (n, δ, w))"]
def ghyMu (n : ℕ) (δ : K) : ℤ :=
  if n % 2 = 0 then hilbertSymbol K (-1) (-1) ^ ((n / 2 - 1) / 2) * hilbertSymbol K ((-1) ^ (n / 2 - 1)) (-δ)
  else hilbertSymbol K (-1) (-1) ^ (n / 2 / 2) * hilbertSymbol K ((-1) ^ (n / 2)) δ

omit hK in
theorem ghyMu_pm (n : ℕ) (δ : K) : ghyMu n δ = 1 ∨ ghyMu n δ = -1 := by
  have pmpow : ∀ (s : ℤ) (k : ℕ), (s = 1 ∨ s = -1) → (s ^ k = 1 ∨ s ^ k = -1) := by
    intro s k hs
    rcases hs with rfl | rfl
    · simp
    · rcases neg_one_pow_eq_or ℤ k with h | h <;> simp [h]
  have pmmul : ∀ x y : ℤ, (x = 1 ∨ x = -1) → (y = 1 ∨ y = -1) → (x * y = 1 ∨ x * y = -1) := by
    rintro x y (rfl | rfl) (rfl | rfl) <;> simp
  unfold ghyMu
  split_ifs
  · exact pmmul _ _ (pmpow _ _ (hs_pm _ _)) (hs_pm _ _)
  · exact pmmul _ _ (pmpow _ _ (hs_pm _ _)) (hs_pm _ _)

omit hK in
/-- **Gan–Hanke–Yu invariants to standard invariants** (Hanke 2011, Lemma 5.1, table, p. 9): $(n,\delta,w)\mapsto(n,d,c)$ with
$d = (-1)^{\lfloor n/2\rfloor}\delta$ and $c = w\,\mu(n,\delta)$ (`ghyMu`). -/
@[kb "hanke2011enumerating" "Lemma 5.1, p. 8 (Gan–Hanke–Yu invariants ↦ standard invariants)"]
def stdOfGHY (n : ℕ) (δ : K) (w : ℤ) : K × ℤ := ((-1) ^ (n / 2) * δ, w * ghyMu n δ)

omit hK in
/-- **Standard invariants to Gan–Hanke–Yu invariants** (Hanke 2011, Lemma 5.1, p. 8): $(n,d,c)\mapsto(n,\delta,w)$ with
$\delta = (-1)^{\lfloor n/2\rfloor}d$ and $w = c\,\mu(n,\delta)$. This is the definition of Gan–Hanke–Yu's $w_v$ used here (see the
file header). -/
@[kb "hanke2011enumerating" "Lemma 5.1, p. 8 (standard invariants ↦ Gan–Hanke–Yu invariants)"]
def ghyOfStd (n : ℕ) (d : K) (c : ℤ) : K × ℤ :=
  ((-1) ^ (n / 2) * d, c * ghyMu n ((-1) ^ (n / 2) * d))

omit hK in
theorem neg_one_pow_mul_self (m : ℕ) : ((-1 : K) ^ m) * (-1) ^ m = 1 := by
  rw [← mul_pow]; simp

omit hK in
/-- **Lemma 5.1, the bijection** (Hanke 2011, p. 8): `ghyOfStd` inverts `stdOfGHY`. -/
@[kb "hanke2011enumerating" "Lemma 5.1, p. 8 (the bijection (n, δ, w) ↔ (n, d, c))"]
theorem ghyOfStd_stdOfGHY (n : ℕ) (δ : K) (w : ℤ) :
    ghyOfStd n (stdOfGHY n δ w).1 (stdOfGHY n δ w).2 = (δ, w) := by
  simp only [ghyOfStd, stdOfGHY]
  rw [← mul_assoc, neg_one_pow_mul_self, one_mul, mul_assoc]
  rcases ghyMu_pm n δ with h | h <;> rw [h] <;> simp

omit hK in
/-- **Lemma 5.1, the bijection** (Hanke 2011, p. 8): `stdOfGHY` inverts `ghyOfStd`. -/
@[kb "hanke2011enumerating" "Lemma 5.1, p. 8 (the bijection (n, d, c) ↔ (n, δ, w))"]
theorem stdOfGHY_ghyOfStd (n : ℕ) (d : K) (c : ℤ) :
    stdOfGHY n (ghyOfStd n d c).1 (ghyOfStd n d c).2 = (d, c) := by
  simp only [ghyOfStd, stdOfGHY]
  rw [← mul_assoc, neg_one_pow_mul_self, one_mul, mul_assoc]
  rcases ghyMu_pm n ((-1) ^ (n / 2) * d) with h | h <;> rw [h] <;> simp

/-! ### The table in Gan–Hanke–Yu form: each model space has standard invariants `stdOfGHY n δ w` -/

/-- **Lemma 5.1, $H^r$** ($r\ge1$; Gan–Hanke–Yu: $\delta = 1$, $w = 1$): $(d, c) = $ `stdOfGHY (2r) 1 1`. -/
@[kb "hanke2011enumerating" "Lemma 5.1, table, p. 9 (H^r: δ = 1, w = 1)"]
theorem lemma_5_1_H (k : ℕ) :
    (∏ i, hypCons (k + 1) (![] : Fin 0 → K) i, hasseVec (hypCons (k + 1) (![] : Fin 0 → K))) =
      stdOfGHY (0 + 2 * (k + 1)) 1 1 := by
  obtain ⟨h1, h2⟩ := lemma_5_1_row_H hK (k + 1)
  have hn : (0 + 2 * (k + 1)) / 2 = k + 1 := by omega
  simp only [stdOfGHY, ghyMu, hn, show (0 + 2 * (k + 1)) % 2 = 0 by omega, ite_true, add_tsub_cancel_right,
    mul_one, one_mul, h1, h2, Prod.mk.injEq, true_and]
  rw [hilbertSymbol_comm, hs_negpow_left hK (by norm_num), ← pm_pow_floor (hs_pm (-1 : K) (-1)) k]
  ring

/-- **Lemma 5.1, $H^{r-2}\oplus D$** ($r = k + 2$; Gan–Hanke–Yu type I: $\delta = 1$, $w = -1$): $d$ is `(stdOfGHY (2r) 1 (-1)).1` up to the
square $(ab)^2$ and $c = $ `(stdOfGHY (2r) 1 (-1)).2`. -/
@[kb "hanke2011enumerating" "Lemma 5.1, table, p. 9 (H^{r-2} ⊕ D: δ = 1, w = -1)"]
theorem lemma_5_1_D (k : ℕ) {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) (hab : hilbertSymbol K a b = -1) :
    ∏ i, hypCons k ![1, -a, -b, a * b] i = (a * b) ^ 2 * (stdOfGHY (4 + 2 * k) 1 (-1)).1 ∧
      hasseVec (hypCons k ![1, -a, -b, a * b]) = (stdOfGHY (4 + 2 * k) (1 : K) (-1)).2 := by
  obtain ⟨h1, h2⟩ := lemma_5_1_row_D hK k ha hb hab
  have hn : (4 + 2 * k) / 2 = k + 2 := by omega
  refine ⟨by rw [h1]; simp only [stdOfGHY, hn]; ring, ?_⟩
  simp only [stdOfGHY, ghyMu, hn, show (4 + 2 * k) % 2 = 0 by omega, ite_true, show k + 2 - 1 = k + 1 by omega, h2]
  rw [hilbertSymbol_comm, hs_negpow_left hK (by norm_num), ← pm_pow_floor (hs_pm (-1 : K) (-1)) (k + 1)]
  ring

/-- **Lemma 5.1, $H^{r-1}\oplus\alpha\langle1,-\delta\rangle$** ($r = k + 1$; Gan–Hanke–Yu types II, III: $\delta$, $w = (\alpha,-\alpha\delta)$):
$d$ is `(stdOfGHY (2r) δ w).1` up to the square $\alpha^2$, and $c = $ `(stdOfGHY (2r) δ w).2`. -/
@[kb "hanke2011enumerating" "Lemma 5.1, table, p. 9 (H^{r-1} ⊕ α(x² - δy²): δ, w = c_aniso)"]
theorem lemma_5_1_binary (k : ℕ) {α δ : K} (hα : α ≠ 0) (hδ : δ ≠ 0) :
    ∏ i, hypCons k ![α, -α * δ] i = α ^ 2 * (stdOfGHY (2 + 2 * k) δ (hilbertSymbol K α (-α * δ))).1 ∧
      hasseVec (hypCons k ![α, -α * δ]) = (stdOfGHY (2 + 2 * k) δ (hilbertSymbol K α (-α * δ))).2 := by
  obtain ⟨h1, h2⟩ := lemma_5_1_row_binary hK k hα hδ
  have hn : (2 + 2 * k) / 2 = k + 1 := by omega
  refine ⟨by rw [h1]; simp only [stdOfGHY, hn]; ring, ?_⟩
  simp only [stdOfGHY, ghyMu, hn, show (2 + 2 * k) % 2 = 0 by omega, ite_true, add_tsub_cancel_right, h2]
  ring

/-- **Lemma 5.1, $H^r\oplus\langle\delta\rangle$** (Gan–Hanke–Yu types –, I: $\delta$, $w = 1$): $(d, c) = $ `stdOfGHY (2r + 1) δ 1`. -/
@[kb "hanke2011enumerating" "Lemma 5.1, table, p. 9 (H^r ⊕ δx²: δ, w = 1)"]
theorem lemma_5_1_unary (r : ℕ) {δ : K} (hδ : δ ≠ 0) :
    (∏ i, hypCons r ![δ] i, hasseVec (hypCons r ![δ])) = stdOfGHY (1 + 2 * r) δ 1 := by
  obtain ⟨h1, h2⟩ := lemma_5_1_row_unary hK r hδ
  have hn : (1 + 2 * r) / 2 = r := by omega
  simp only [stdOfGHY, ghyMu, hn, show ¬ (1 + 2 * r) % 2 = 0 by omega, ite_false, one_mul, h1, h2]

/-- **Lemma 5.1, $H^{r-1}\oplus-\delta\langle a,b,ab\rangle$** ($r = k + 1$; Gan–Hanke–Yu types II$^\pm$: $\delta$, $w = -1$): $d$ is
`(stdOfGHY (2r + 1) δ (-1)).1` up to the square $(\delta ab)^2$, and $c = $ `(stdOfGHY (2r + 1) δ (-1)).2`. -/
@[kb "hanke2011enumerating" "Lemma 5.1, table, p. 9 (H^{r-1} ⊕ -δ(ax² + by² + abz²): δ, w = -1)"]
theorem lemma_5_1_ternary (k : ℕ) {δ a b : K} (hδ : δ ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : hilbertSymbol K (-a) (-b) = -1) :
    ∏ i, hypCons k ![-δ * a, -δ * b, -δ * (a * b)] i = (δ * a * b) ^ 2 * (stdOfGHY (3 + 2 * k) δ (-1)).1 ∧
      hasseVec (hypCons k ![-δ * a, -δ * b, -δ * (a * b)]) = (stdOfGHY (3 + 2 * k) δ (-1)).2 := by
  obtain ⟨h1, h2⟩ := lemma_5_1_row_ternary hK k hδ ha hb hab
  have hn : (3 + 2 * k) / 2 = k + 1 := by omega
  refine ⟨by rw [h1]; simp only [stdOfGHY, hn]; ring, ?_⟩
  simp only [stdOfGHY, ghyMu, hn, show ¬ (3 + 2 * k) % 2 = 0 by omega, ite_false, h2]
  have m1 : (-1 : K) ≠ 0 := by norm_num
  rw [show (-δ) = -1 * δ by ring, hK.mul_right (pow_ne_zero _ m1) m1 hδ]
  rw [hs_negpow_left hK m1 k, hs_negpow_left hK hδ k,
    hs_negpow_left hK hδ (k + 1), ← pm_pow_floor (hs_pm (-1 : K) (-1)) k, pow_succ]
  ring

/-! ### The Gan–Hanke–Yu invariants of a space classify it -/

omit hK in
/-- Gan–Hanke–Yu's $\delta$ of $\langle a\rangle$: $(-1)^{\lfloor n/2\rfloor}\prod_ia_i$. -/
def ghyDelta {n : ℕ} (a : Fin n → K) : K := (ghyOfStd n (∏ i, a i) (hasseVec a)).1

omit hK in
/-- Gan–Hanke–Yu's $w$ of $\langle a\rangle$, via Lemma 5.1 (`ghyOfStd`). -/
def ghyW {n : ℕ} (a : Fin n → K) : ℤ := (ghyOfStd n (∏ i, a i) (hasseVec a)).2

theorem ghyMu_sq (n : ℕ) {δ t : K} (hδ : δ ≠ 0) (ht : t ≠ 0) : ghyMu n (t ^ 2 * δ) = ghyMu n δ := by
  have m1 : (-1 : K) ≠ 0 := by norm_num
  unfold ghyMu
  split_ifs
  · rw [show -(t ^ 2 * δ) = t ^ 2 * -δ by ring, hs_sq_right _ _ _ ht]
  · rw [hs_sq_right _ _ _ ht]

/-- **Lemma 5.1: the Gan–Hanke–Yu invariants classify local spaces** (Hanke 2011, p. 8, the bijection with the standard invariants,
which classify spaces over a local field): $\langle a\rangle\cong\langle b\rangle$ if and only if their $\delta$ agree modulo
squares and their $w$ agree. (From `PadicClass.isometric_iff_invariants` and `stdOfGHY_ghyOfStd`.) -/
@[kb "hanke2011enumerating" "Lemma 5.1, p. 8 ((n, δ_v, w_v) classify local spaces)"]
theorem lemma_5_1_classify {n : ℕ} {a b : Fin n → K} (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) :
    (QuadForm.diag a).IsometricIn K (QuadForm.diag b) ↔
      (∃ t : K, t ≠ 0 ∧ ghyDelta b = t ^ 2 * ghyDelta a) ∧ ghyW a = ghyW b := by
  have hPa : (∏ i, a i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => ha i
  have hPb : (∏ i, b i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hb i
  have m1 : ((-1 : K) ^ (n / 2)) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [isometric_iff_invariants hK ha hb]
  simp only [ghyDelta, ghyW, ghyOfStd]
  have hdisc : (∃ t : K, t ≠ 0 ∧ ∏ i, b i = t ^ 2 * ∏ i, a i) ↔
      (∃ t : K, t ≠ 0 ∧ (-1) ^ (n / 2) * ∏ i, b i = t ^ 2 * ((-1) ^ (n / 2) * ∏ i, a i)) := by
    refine exists_congr fun t => and_congr_right fun _ => ?_
    constructor
    · intro h; rw [h]; ring
    · intro h
      have h' : (-1) ^ (n / 2) * ∏ i, b i = (-1) ^ (n / 2) * (t ^ 2 * ∏ i, a i) := h.trans (by ring)
      exact mul_left_cancel₀ m1 h'
  rw [hdisc]
  constructor
  · rintro ⟨⟨t, ht, hdt⟩, hc⟩
    refine ⟨⟨t, ht, hdt⟩, ?_⟩
    rw [hdt, ghyMu_sq hK n (mul_ne_zero m1 hPa) ht, hc]
  · rintro ⟨⟨t, ht, hdt⟩, hw⟩
    refine ⟨⟨t, ht, hdt⟩, ?_⟩
    rw [hdt, ghyMu_sq hK n (mul_ne_zero m1 hPa) ht] at hw
    rcases ghyMu_pm n ((-1) ^ (n / 2) * ∏ i, a i) with h | h <;> rw [h] at hw <;> linarith

end QuadFormsKB.Hanke2011Enumerating
