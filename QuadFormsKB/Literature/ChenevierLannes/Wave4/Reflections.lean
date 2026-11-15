/-
# Chenevier–Lannes, §3.1 and §3.4.2: reflections and neighbours (Propositions 3.1.14 (a), (b); Lemma 3.4.2.12)

Source: Chenevier–Lannes 2019 (`chenevierlannes2019`), §3.1, Proposition 3.1.14, p. 53; §3.4.2, Lemma 3.4.2.12, p. 71.
Printed page numbers. Conventions of the book: $q(x) = $ `Q.eval x`, $x \cdot y = $ `bZ Q x y`, $x \cdot x = 2q(x)$.

**Layer.** `Siegel/Neighbors.lean` (`cv`, `stdLat`, `bZ`, `bQ`) and `Wave3/Statements.lean` (`voisLat`).

**Defines:** `reflQ Q u` (the orthogonal reflection $s_u(x) = x - \frac{x \cdot u}{q(u)}\,u$ of $\mathbb{Q}^n$ in the
hyperplane $u^\perp$, for $q(u) \neq 0$; the book's $s_u$, p. 53), `reflLat Q u` ($= s_u(\mathbb{Z}^n)$).

**Proves (all unconditional):**
- `reflQ_reflQ`, `evalIn_reflQ`: $s_u$ is an involutive isometry;
- Proposition 3.1.14 (a) (`voisLat_eq_reflLat`): if $q(u) = d$ and $u \cdot v \equiv 1 \bmod d$ then
  $\mathrm{vois}_d(L; u) = s_u(L)$;
- Proposition 3.1.14 (b) (`voisLat_eq_map_reflQ`): if $q(u) = d_1 d_2$ and $u \cdot v \equiv 1 \bmod d_1 d_2$ then
  $\mathrm{vois}_{d_2}(L; u) = s_u(\mathrm{vois}_{d_1}(L; u))$ (the book assumes $d_1, d_2 \ge 2$; the proof needs only
  $d_1, d_2 \ge 1$);
- Lemma 3.4.2.12 (`voisLat_mem_clearing`): for $x \in \mathrm{vois}_d(L; u)$, $q(u)\,x \in M_d(L; u)$ and
  $q(u)\,x \equiv (u \cdot x)\,u \bmod d$.
-/
import QuadFormsKB.Literature.ChenevierLannes.Wave3.Statements

open Matrix

namespace QuadFormsKB.ChenevierLannes

open QuadFormsKB.Siegel QuadFormsKB.Siegel.Kneser

variable {n : ℕ}

/-! ### Right-hand linearity of `bZ` -/

theorem bZ_add_right' (Q : QuadForm ℤ n) (u x y : Fin n → ℤ) : bZ Q u (x + y) = bZ Q u x + bZ Q u y := by
  simp [bZ, mulVec_add, dotProduct_add]

theorem bZ_sub_right' (Q : QuadForm ℤ n) (u x y : Fin n → ℤ) : bZ Q u (x - y) = bZ Q u x - bZ Q u y := by
  simp [bZ, mulVec_sub, dotProduct_sub]

theorem bZ_smul_right' (Q : QuadForm ℤ n) (c : ℤ) (u x : Fin n → ℤ) : bZ Q u (c • x) = c * bZ Q u x := by
  simp only [bZ, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

/-! ### The reflection $s_u$ -/

/-- **The orthogonal reflection $s_u$** (Chenevier–Lannes, p. 53) of $\mathbb{Q}^n$ in the hyperplane $u^\perp$:
$s_u(x) = x - \dfrac{x \cdot u}{q(u)}\,u$, where $x \cdot u$ is the rational polar form `bQ Q x (cv u)` and
$q(u) = $ `Q.eval u`. It is defined for every $u$ (division by $0$ giving $0$) and meaningful for $q(u) \neq 0$. -/
noncomputable def reflQ (Q : QuadForm ℤ n) (u : Fin n → ℤ) : (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℚ) where
  toFun x := x - (bQ Q x (cv u) / (Q.eval u : ℚ)) • cv u
  map_add' x y := by
    rw [bQ_add_left, add_div, add_smul]; abel
  map_smul' c x := by
    rw [bQ_smul_left, RingHom.id_apply, smul_sub, smul_smul, mul_div_assoc]

theorem reflQ_apply (Q : QuadForm ℤ n) (u : Fin n → ℤ) (x : Fin n → ℚ) :
    reflQ Q u x = x - (bQ Q x (cv u) / (Q.eval u : ℚ)) • cv u := rfl

/-- $u \cdot u = 2q(u)$ over $\mathbb{Q}$. -/
theorem bQ_cv_self (Q : QuadForm ℤ n) (u : Fin n → ℤ) : bQ Q (cv u) (cv u) = 2 * (Q.eval u : ℚ) := by
  rw [bQ_cv, bZ_self]; push_cast; ring

/-- $s_u(x) \cdot u = -\,x \cdot u$ (for $q(u) \ne 0$). -/
theorem bQ_reflQ (Q : QuadForm ℤ n) {u : Fin n → ℤ} (hu : Q.eval u ≠ 0) (x : Fin n → ℚ) :
    bQ Q (reflQ Q u x) (cv u) = - bQ Q x (cv u) := by
  have hu' : (Q.eval u : ℚ) ≠ 0 := by exact_mod_cast hu
  rw [reflQ_apply, sub_eq_add_neg, bQ_add_left, ← neg_smul, bQ_smul_left, bQ_cv_self]
  field_simp
  ring

/-- **$s_u$ is an involution** ($s_u \circ s_u = \mathrm{id}$ for $q(u) \neq 0$; Chenevier–Lannes, p. 53). -/
theorem reflQ_reflQ (Q : QuadForm ℤ n) {u : Fin n → ℤ} (hu : Q.eval u ≠ 0) (x : Fin n → ℚ) :
    reflQ Q u (reflQ Q u x) = x := by
  conv_lhs => rw [reflQ_apply, bQ_reflQ Q hu, reflQ_apply]
  rw [neg_div, neg_smul, sub_neg_eq_add, sub_add_cancel]

/-- **$s_u$ is an isometry** of $(\mathbb{Q}^n, q)$ ($q(u) \neq 0$; Chenevier–Lannes, p. 53). -/
theorem evalIn_reflQ (Q : QuadForm ℤ n) {u : Fin n → ℤ} (hu : Q.eval u ≠ 0) (x : Fin n → ℚ) :
    Q.evalIn ℚ (reflQ Q u x) = Q.evalIn ℚ x := by
  have hu' : (Q.eval u : ℚ) ≠ 0 := by exact_mod_cast hu
  rw [reflQ_apply, sub_eq_add_neg, ← neg_smul, evalIn_add_smulQ, evalIn_cv]
  field_simp
  ring

/-- **The lattice $s_u(L)$**, $L = \mathbb{Z}^n$: the image of the standard lattice under the reflection `reflQ Q u`. -/
noncomputable def reflLat (Q : QuadForm ℤ n) (u : Fin n → ℤ) : Submodule ℤ (Fin n → ℚ) :=
  (stdLat n).map ((reflQ Q u).restrictScalars ℤ)

/-- On integer vectors: $s_u(y) = y - \dfrac{u \cdot y}{q(u)}\,u$ with integral pairing. -/
theorem reflQ_cv (Q : QuadForm ℤ n) (u y : Fin n → ℤ) :
    reflQ Q u (cv y) = cv y - ((bZ Q u y : ℚ) / (Q.eval u : ℚ)) • cv u := by
  rw [reflQ_apply, bQ_cv, bZ_comm]

/-! ### Proposition 3.1.14 (b), and (a) as its case $d_1 = 1$ -/

/-- Helper for Proposition 3.1.14 (b): $s_u(\mathrm{vois}_{d_1}(L;u)) \subseteq \mathrm{vois}_{d_2}(L;u)$ when
$q(u) = d_1 d_2$ and $u \cdot v \equiv 1 \bmod d_1 d_2$. -/
theorem map_reflQ_voisLat_le {Q : QuadForm ℤ n} {d₁ d₂ : ℕ} (h₁ : 1 ≤ d₁) (h₂ : 1 ≤ d₂) {u v : Fin n → ℤ}
    (hq : Q.eval u = (d₁ : ℤ) * d₂) (hv : ((d₁ : ℤ) * d₂) ∣ bZ Q u v - 1) :
    (voisLat Q d₁ u v).map ((reflQ Q u).restrictScalars ℤ) ≤ voisLat Q d₂ u v := by
  have hd₁ : (d₁ : ℚ) ≠ 0 := by exact_mod_cast (by omega : d₁ ≠ 0)
  have hd₂ : (d₂ : ℚ) ≠ 0 := by exact_mod_cast (by omega : d₂ ≠ 0)
  have hqQ : (Q.eval u : ℚ) = (d₁ : ℚ) * d₂ := by rw [hq]; push_cast; ring
  obtain ⟨m, hm⟩ := hv
  have hb : (bZ Q u v : ℚ) = (d₁ : ℚ) * d₂ * m + 1 := by
    have : bZ Q u v = (d₁ : ℤ) * d₂ * m + 1 := by linarith
    exact_mod_cast this
  rw [Submodule.map_le_iff_le_comap, voisLat, Submodule.span_le]
  rintro x (⟨y, rfl, k0, hk0⟩ | rfl)
  · -- generator `cv y` with `d₁ ∣ u · y`
    show reflQ Q u (cv y) ∈ voisLat Q d₂ u v
    have hk : (bZ Q u y : ℚ) = d₁ * k0 := by exact_mod_cast hk0
    have e : reflQ Q u (cv y) =
        cv (y - (k0 * d₁) • v) - (k0 : ℤ) • ((1 / (d₂ : ℚ)) • cv (u - Q.eval u • v)) := by
      rw [reflQ_cv, hk, hqQ]
      ext i
      simp [hq, cv_apply]
      field_simp
      ring
    rw [e]
    refine Submodule.sub_mem _ (Submodule.subset_span (Or.inl ⟨_, rfl, ?_⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr rfl)))
    rw [bZ_sub_right', bZ_smul_right', hk0]
    exact ⟨-(k0 * d₁ * d₁ * m), by linear_combination (-(k0 * d₁)) * hm⟩
  · -- generator `(1/d₁) • (u - q v)`
    show reflQ Q u ((1 / (d₁ : ℚ)) • cv (u - Q.eval u • v)) ∈ voisLat Q d₂ u v
    have e : reflQ Q u ((1 / (d₁ : ℚ)) • cv (u - Q.eval u • v)) =
        cv ((d₂ : ℤ) • (m • u - v)) := by
      rw [map_smul, reflQ_cv]
      have : (bZ Q u (u - Q.eval u • v) : ℚ) = 2 * (d₁ * d₂) - (d₁ * d₂) * (bZ Q u v) := by
        rw [bZ_sub_right', bZ_smul_right', bZ_comm Q u u, bZ_self]
        push_cast
        rw [hq]; push_cast; ring
      rw [this, hqQ, hb]
      ext i
      simp [hq, cv_apply]
      field_simp
      ring
    rw [e]
    refine Submodule.subset_span (Or.inl ⟨_, rfl, ?_⟩)
    rw [bZ_smul_right']
    exact dvd_mul_right _ _

/-- **Proposition 3.1.14 (b)** (Chenevier–Lannes, p. 53): let $d_1, d_2 \ge 1$ (the book: $\ge 2$), $u \in L = \mathbb{Z}^n$
with $q(u) = d_1 d_2$, and $v \in L$ with $u \cdot v \equiv 1 \bmod d_1 d_2$. Then
$\mathrm{vois}_{d_2}(L; u) = s_u\bigl(\mathrm{vois}_{d_1}(L; u)\bigr)$, where $s_u$ is the reflection `reflQ Q u`. -/
@[kb "chenevierlannes2019" "Prop. 3.1.14 (b), p. 53"]
theorem voisLat_eq_map_reflQ {Q : QuadForm ℤ n} {d₁ d₂ : ℕ} (h₁ : 1 ≤ d₁) (h₂ : 1 ≤ d₂) {u v : Fin n → ℤ}
    (hq : Q.eval u = (d₁ : ℤ) * d₂) (hv : ((d₁ : ℤ) * d₂) ∣ bZ Q u v - 1) :
    voisLat Q d₂ u v = (voisLat Q d₁ u v).map ((reflQ Q u).restrictScalars ℤ) := by
  have hu : Q.eval u ≠ 0 := by
    rw [hq]; exact mul_ne_zero (by exact_mod_cast (by omega : d₁ ≠ 0)) (by exact_mod_cast (by omega : d₂ ≠ 0))
  refine le_antisymm ?_ (map_reflQ_voisLat_le h₁ h₂ hq hv)
  intro x hx
  have hq' : Q.eval u = (d₂ : ℤ) * d₁ := by rw [hq, mul_comm]
  have hv' : ((d₂ : ℤ) * d₁) ∣ bZ Q u v - 1 := by rw [mul_comm]; exact hv
  have hsx : (reflQ Q u x) ∈ voisLat Q d₁ u v :=
    map_reflQ_voisLat_le h₂ h₁ hq' hv' ⟨x, hx, rfl⟩
  exact ⟨reflQ Q u x, hsx, reflQ_reflQ Q hu x⟩

/-- $\mathrm{vois}_1(L; u) = L$. -/
theorem voisLat_one (Q : QuadForm ℤ n) (u v : Fin n → ℤ) : voisLat Q 1 u v = stdLat n := by
  apply le_antisymm
  · rw [voisLat, Submodule.span_le]
    rintro x (⟨y, rfl, -⟩ | rfl)
    · exact ⟨y, rfl⟩
    · exact ⟨u - Q.eval u • v, by rw [Nat.cast_one, div_one, one_smul]⟩
  · rintro x ⟨y, rfl⟩
    exact Submodule.subset_span (Or.inl ⟨y, rfl, one_dvd _⟩)

/-- **Proposition 3.1.14 (a)** (Chenevier–Lannes, p. 53): let $d \ge 1$, $u \in L = \mathbb{Z}^n$ with $q(u) = d$ and
$v \in L$ with $u \cdot v \equiv 1 \bmod d$. Then $\mathrm{vois}_d(L; u) = s_u(L)$, $s_u(x) = x - \frac{x \cdot u}{d}\,u$
(the reflection `reflQ Q u`; `reflLat Q u`). Special case $d_1 = 1$ of (b). -/
@[kb "chenevierlannes2019" "Prop. 3.1.14 (a), p. 53"]
theorem voisLat_eq_reflLat {Q : QuadForm ℤ n} {d : ℕ} (hd : 1 ≤ d) {u v : Fin n → ℤ}
    (hq : Q.eval u = d) (hv : (d : ℤ) ∣ bZ Q u v - 1) : voisLat Q d u v = reflLat Q u := by
  have h := voisLat_eq_map_reflQ (Q := Q) (d₁ := 1) (d₂ := d) le_rfl hd (u := u) (v := v)
    (by simp [hq]) (by simpa using hv)
  rw [h, voisLat_one]
  rfl

/-- Proposition 3.1.14 (a), isometric form: under the hypotheses of (a), $s_u$ is an isometry of $\mathbb{Q}^n$ carrying
$L = \mathbb{Z}^n$ onto $\mathrm{vois}_d(L; u)$. -/
theorem voisLat_isometric {Q : QuadForm ℤ n} {d : ℕ} (hd : 1 ≤ d) {u v : Fin n → ℤ}
    (hq : Q.eval u = d) (hv : (d : ℤ) ∣ bZ Q u v - 1) :
    voisLat Q d u v = (stdLat n).map ((reflQ Q u).restrictScalars ℤ) ∧
      ∀ x, Q.evalIn ℚ (reflQ Q u x) = Q.evalIn ℚ x := by
  refine ⟨voisLat_eq_reflLat hd hq hv, evalIn_reflQ Q ?_⟩
  rw [hq]; exact_mod_cast (by omega : d ≠ 0)

/-! ### Lemma 3.4.2.12 -/

/-- **Lemma 3.4.2.12** (Chenevier–Lannes, p. 71): let $d \ge 1$ with $d \mid q(u)$ and $u \cdot v \equiv 1 \bmod d$, and
$x \in \mathrm{vois}_d(L; u)$. Then $q(u)\,x \in M_d(L; u)$ (it is `cv y` with $d \mid u \cdot y$) and
$q(u)\,x \equiv (u \cdot x)\,u \bmod d$ (here $u \cdot x = k \in \mathbb{Z}$ and $d \mid y_i - k u_i$ for all $i$). -/
@[kb "chenevierlannes2019" "Lemma 3.4.2.12, p. 71"]
theorem voisLat_mem_clearing {Q : QuadForm ℤ n} {d : ℕ} (hd : 1 ≤ d) {u v : Fin n → ℤ}
    (hqd : (d : ℤ) ∣ Q.eval u) (hv : (d : ℤ) ∣ bZ Q u v - 1) {x : Fin n → ℚ} (hx : x ∈ voisLat Q d u v) :
    ∃ (y : Fin n → ℤ) (k : ℤ), (Q.eval u : ℚ) • x = cv y ∧ bQ Q (cv u) x = k ∧ (d : ℤ) ∣ bZ Q u y ∧
      ∀ i, (d : ℤ) ∣ y i - k * u i := by
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  obtain ⟨m, hm⟩ := hqd
  obtain ⟨c, hc⟩ := hv
  refine Submodule.span_induction (p := fun x _ => ∃ (y : Fin n → ℤ) (k : ℤ), (Q.eval u : ℚ) • x = cv y ∧
      bQ Q (cv u) x = k ∧ (d : ℤ) ∣ bZ Q u y ∧ ∀ i, (d : ℤ) ∣ y i - k * u i) ?_ ?_ ?_ ?_ hx
  · rintro x (⟨y, rfl, hy⟩ | rfl)
    · refine ⟨Q.eval u • y, bZ Q u y, ?_, ?_, ?_, ?_⟩
      · rw [cv_smul]
      · rw [bQ_cv]
      · rw [bZ_smul_right']; exact Dvd.dvd.mul_right ⟨m, hm⟩ _
      · intro i
        exact dvd_sub (by simpa using Dvd.dvd.mul_right ⟨m, hm⟩ (y i)) (Dvd.dvd.mul_right hy _)
    · have hmq : (Q.eval u : ℚ) = d * m := by rw [hm]; push_cast; ring
      have hbq : (bZ Q u (u - Q.eval u • v) : ℚ) = Q.eval u * (2 - bZ Q u v) := by
        rw [bZ_sub_right', bZ_smul_right', bZ_comm Q u u, bZ_self]
        push_cast; ring
      have hbq' : bZ Q u (u - Q.eval u • v) = Q.eval u * (2 - bZ Q u v) := by exact_mod_cast hbq
      refine ⟨m • (u - Q.eval u • v), m * (2 - bZ Q u v), ?_, ?_, ?_, ?_⟩
      · rw [cv_smul, hmq, smul_smul]
        have : (d : ℚ) * m * (1 / (d : ℚ)) = m := by field_simp
        rw [this]
      · rw [bQ_smul_right, bQ_cv, hbq']
        push_cast
        rw [hmq]
        field_simp
      · rw [bZ_smul_right', hbq']
        exact ⟨m * m * (2 - bZ Q u v), by rw [hm]; ring⟩
      · intro i
        refine ⟨m * c * u i - m * m * v i, ?_⟩
        simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        rw [hm]
        linear_combination (m * u i) * hc
  · exact ⟨0, 0, by simp [cv_zero], by simp [bQ], by simp [bZ], fun i => by simp⟩
  · rintro x x' - - ⟨y, k, h1, h2, h3, h4⟩ ⟨y', k', h1', h2', h3', h4'⟩
    refine ⟨y + y', k + k', ?_, ?_, ?_, ?_⟩
    · rw [smul_add, h1, h1', cv_add]
    · rw [bQ_add_right, h2, h2']; push_cast; ring
    · rw [bZ_add_right']; exact dvd_add h3 h3'
    · intro i
      show (d : ℤ) ∣ (y i + y' i) - (k + k') * u i
      rw [show y i + y' i - (k + k') * u i = (y i - k * u i) + (y' i - k' * u i) by ring]
      exact dvd_add (h4 i) (h4' i)
  · rintro a x - ⟨y, k, h1, h2, h3, h4⟩
    refine ⟨a • y, a * k, ?_, ?_, ?_, ?_⟩
    · rw [cv_smul, ← h1, ← Int.cast_smul_eq_zsmul ℚ a x, smul_comm]
    · rw [← Int.cast_smul_eq_zsmul ℚ a x, bQ_smul_right, h2]; push_cast; ring
    · rw [bZ_smul_right']; exact Dvd.dvd.mul_left h3 _
    · intro i
      have := Dvd.dvd.mul_left (h4 i) a
      simpa [mul_sub, mul_assoc] using this

end QuadFormsKB.ChenevierLannes
