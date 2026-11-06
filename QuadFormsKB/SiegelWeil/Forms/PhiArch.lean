/-
# The archimedean determinant for Siegel's $\Phi$ operator on Eisenstein series ($\Phi E^{(r+1)} = E^{(r)}$)

**Layer:** real and complex linear algebra (no arithmetic input).

**Setting.** A real *symmetric coprime pair* $(C, D)$ of size $n$ (the bottom blocks of a real symplectic matrix):
$C D^{\mathsf T} = D C^{\mathsf T}$, and no nonzero real row vector $u$ has $uC = 0 = uD$.  For $Z \in \mathbb H_r$ in the Siegel
upper half space and a complex number $s$, put $Z_s = \operatorname{diag}(i s, Z)$ of size $r + 1$: the new variable has index $0$
(`zt`) and the variables $1, \dots, r$ carry $Z$.  We study $s \mapsto \det(C Z_s + D)$ (`W`), the archimedean factor of
$\Phi E^{(r+1)}$.

**Results.**
* `det_ne_zero`: $\det(CZ + D) \ne 0$ for $Z \in \mathbb H_n$ (the denominator of the Eisenstein series never vanishes);
* `det_zt_affine`: $\det(C Z_s + D) = \det(C Z_0 + D) + s\,\alpha$ is affine in $s$, with $\alpha$ explicit (`det_zt_of_col_zero`:
  it is constant in $s$ when the column $0$ of $C$ vanishes);
* `zt_mem`: $Z_s \in \mathbb H_{r+1}$ for $Z \in \mathbb H_r$ and $\operatorname{Re}s > 0$;
* `monotoneOn_norm_det`: $t \mapsto \lVert\det(C Z_t + D)\rVert$ is monotone on $(0, \infty)$ (the unique root of an affine function
  lies in $\operatorname{Re} \le 0$ by `det_ne_zero` and `zt_mem`);
* **`tendsto_norm_det`**: if column $0$ of $C$ is nonzero, then $\lVert\det(C Z_t + D)\rVert \to \infty$ as $t \to \infty$ (the
  coefficient $\alpha$ is nonzero: the matrix $[c_0 \mid C_1Z + D_1]$ is invertible).

Source: Klingen, *Introductory lectures on Siegel modular forms* (1990), §5 (Φ of Eisenstein series) [unverified];
Freitag, *Siegelsche Modulfunktionen* (1983), Ch. I [unverified].
-/
import QuadFormsKB.Weil.Genus.SiegelSpace

open Matrix Complex Filter Topology
open QuadFormsKB.WeilRep.Genus

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms.PhiArch

/-- $\operatorname{diag}(i s, Z)$: the variable $0$ gets $i s$, the variables $1, \dots, r$ get $Z$. -/
def zt {r : ℕ} (Z : Matrix (Fin r) (Fin r) ℂ) (s : ℂ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  Matrix.of fun i j => Fin.cases (Fin.cases (Complex.I * s) (fun _ => 0) j)
    (fun i' => Fin.cases 0 (fun j' => Z i' j') j) i

/-- $W(Z) = CZ + D$ as a complex matrix, for real $C$, $D$. -/
def W {n : ℕ} (C D : Matrix (Fin n) (Fin n) ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  C.map (↑) * Z + D.map (↑)

/-- The row vector $w^{\mathsf T}P$ as an explicit sum: $A(P, w)_k = \sum_i w_i P_{ik}$. -/
def A {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℂ) (k : Fin n) : ℂ :=
  ∑ i, w i * (P i k : ℂ)

/-- Core positivity lemma: if $Za = -b$ with $Z \in \mathbb H_n$ and $a^{\mathsf T}\bar b = b^{\mathsf T}\bar a$, then $a = 0$. -/
lemma eq_zero_of_form {n : ℕ} {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : Z ∈ siegelH n)
    (a b : Fin n → ℂ) (hb : ∀ j, ∑ k, Z j k * a k = -b j)
    (h : ∑ k, a k * (starRingEnd ℂ) (b k) = ∑ k, b k * (starRingEnd ℂ) (a k)) : a = 0 := by
  have hY : (Z.map Complex.im).PosDef := hZ.2
  have hsymm : ∀ i j, Z i j = Z j i := fun i j => (congrFun₂ hZ.1 i j).symm
  have hbk : ∀ k, b k = -∑ j, Z k j * a j := fun k => by rw [hb k]; ring
  have e1 : ∑ k, a k * (starRingEnd ℂ) (b k)
      = -∑ i, ∑ j, a i * (starRingEnd ℂ) (Z i j) * (starRingEnd ℂ) (a j) := by
    have : ∀ k, (starRingEnd ℂ) (b k) = -∑ j, (starRingEnd ℂ) (Z k j) * (starRingEnd ℂ) (a j) := by
      intro k; rw [hbk k]; simp [map_sum]
    simp only [this, Finset.mul_sum, mul_neg, Finset.sum_neg_distrib]
    refine congrArg _ (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)
  have e2 : ∑ k, b k * (starRingEnd ℂ) (a k)
      = -∑ i, ∑ j, a i * Z i j * (starRingEnd ℂ) (a j) := by
    simp only [hbk, neg_mul, Finset.sum_mul, Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine congrArg _ (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_)
    rw [hsymm j i]; ring
  have e3 : ∑ i, ∑ j, a i * (2 * Complex.I * ((Z.map Complex.im i j : ℝ) : ℂ)) *
      (starRingEnd ℂ) (a j) = 0 := by
    have : ∑ i, ∑ j, a i * (2 * Complex.I * ((Z.map Complex.im i j : ℝ) : ℂ)) *
        (starRingEnd ℂ) (a j) = ∑ i, ∑ j, a i * Z i j * (starRingEnd ℂ) (a j)
          - ∑ i, ∑ j, a i * (starRingEnd ℂ) (Z i j) * (starRingEnd ℂ) (a j) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have := Complex.sub_conj (Z i j)
      simp only [Matrix.map_apply]
      have h2 : (2 * Complex.I * ((Z i j).im : ℂ)) = Z i j - (starRingEnd ℂ) (Z i j) := by
        rw [this]; push_cast; ring
      rw [h2]; ring
    rw [this]; linear_combination h - e1 + e2
  have e4 : ∑ i, ∑ j, a i * ((Z.map Complex.im i j : ℝ) : ℂ) * (starRingEnd ℂ) (a j) = 0 := by
    have : (2 * Complex.I) * ∑ i, ∑ j, a i * ((Z.map Complex.im i j : ℝ) : ℂ) *
        (starRingEnd ℂ) (a j) = 0 := by
      rw [← e3, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    exact (mul_eq_zero.mp this).resolve_left (by simp [Complex.ext_iff])
  have e5 := congrArg Complex.re e4
  rw [Complex.zero_re] at e5
  have e6 : ∑ i, ∑ j, (a j).re * (Z.map Complex.im i j) * (a i).re +
      ∑ i, ∑ j, (a j).im * (Z.map Complex.im i j) * (a i).im = 0 := by
    rw [← e5, Complex.re_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im]
    ring
  have hpos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < ∑ i, ∑ j, x j * (Z.map Complex.im i j) * x i := by
    intro x hx
    have := hY.dotProduct_mulVec_pos hx
    simp only [star_trivial, dotProduct, mulVec] at this
    refine lt_of_lt_of_eq this (Finset.sum_congr rfl fun i _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hnn : ∀ x : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, x j * (Z.map Complex.im i j) * x i := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · exact (hpos x hx).le
  have hre : (fun i => (a i).re) = 0 := by
    by_contra hx
    have := hpos _ hx
    have := hnn (fun i => (a i).im)
    linarith
  have him : (fun i => (a i).im) = 0 := by
    by_contra hx
    have := hpos _ hx
    have := hnn (fun i => (a i).re)
    linarith
  ext i
  exact Complex.ext (congrFun hre i) (congrFun him i)

/-- Symmetry of the pair $(C, D)$ in row-vector form:
$\sum_k A(C,w)_k D_{jk} = \sum_k A(D,w)_k C_{jk}$. -/
lemma row_sym {n : ℕ} {C D : Matrix (Fin n) (Fin n) ℝ} (hsym : C * Dᵀ = D * Cᵀ)
    (w : Fin n → ℂ) (j : Fin n) :
    ∑ k, A C w k * (D j k : ℂ) = ∑ k, A D w k * (C j k : ℂ) := by
  have h : ∀ i, ∑ k, (C i k : ℂ) * (D j k : ℂ) = ∑ k, (D i k : ℂ) * (C j k : ℂ) := by
    intro i
    have := congrFun₂ hsym i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply] at this
    exact_mod_cast this
  have e : ∀ (P Q : Matrix (Fin n) (Fin n) ℝ),
      ∑ k, A P w k * (Q j k : ℂ) = ∑ i, w i * ∑ k, (P i k : ℂ) * (Q j k : ℂ) := by
    intro P Q
    simp only [A, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  rw [e, e]
  exact Finset.sum_congr rfl fun i _ => by rw [h i]

/-- Quadratic-form version of `row_sym`: $\sum_k a_k\bar b_k = \sum_k b_k \bar a_k$ for
$a = w^{\mathsf T}C$, $b = w^{\mathsf T}D$. -/
lemma form_sym {n : ℕ} {C D : Matrix (Fin n) (Fin n) ℝ} (hsym : C * Dᵀ = D * Cᵀ)
    (w : Fin n → ℂ) :
    ∑ k, A C w k * (starRingEnd ℂ) (A D w k) = ∑ k, A D w k * (starRingEnd ℂ) (A C w k) := by
  have hconj : ∀ (P : Matrix (Fin n) (Fin n) ℝ) k,
      (starRingEnd ℂ) (A P w k) = ∑ j, (starRingEnd ℂ) (w j) * (P j k : ℂ) := by
    intro P k; simp [A, map_sum]
  have key : ∀ (P Q : Matrix (Fin n) (Fin n) ℝ),
      ∑ k, A P w k * (starRingEnd ℂ) (A Q w k)
        = ∑ j, (starRingEnd ℂ) (w j) * ∑ k, A P w k * (Q j k : ℂ) := by
    intro P Q
    simp only [hconj, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  rw [key, key]
  exact Finset.sum_congr rfl fun j _ => by rw [row_sym hsym w j]

/-- A complex vector $w$ with $w^{\mathsf T}C = 0 = w^{\mathsf T}D$ is zero. -/
lemma w_eq_zero {n : ℕ} {C D : Matrix (Fin n) (Fin n) ℝ}
    (hrank : ∀ u : Fin n → ℝ, u ᵥ* C = 0 → u ᵥ* D = 0 → u = 0)
    (w : Fin n → ℂ) (ha : A C w = 0) (hb : A D w = 0) : w = 0 := by
  have hre : ∀ (P : Matrix (Fin n) (Fin n) ℝ), A P w = 0 →
      (fun i => (w i).re) ᵥ* P = 0 ∧ (fun i => (w i).im) ᵥ* P = 0 := by
    intro P hP
    have key : ∀ k, (∑ i, (w i).re * P i k = 0) ∧ (∑ i, (w i).im * P i k = 0) := by
      intro k
      have := congrFun hP k
      simp only [A, Pi.zero_apply] at this
      have h1 := congrArg Complex.re this
      have h2 := congrArg Complex.im this
      simp [Complex.re_sum, Complex.im_sum] at h1 h2
      exact ⟨h1, h2⟩
    exact ⟨funext fun k => by simpa [Matrix.vecMul, dotProduct] using (key k).1,
      funext fun k => by simpa [Matrix.vecMul, dotProduct] using (key k).2⟩
  have h1 := hrank _ (hre C ha).1 (hre D hb).1
  have h2 := hrank _ (hre C ha).2 (hre D hb).2
  ext i
  exact Complex.ext (congrFun h1 i) (congrFun h2 i)

variable {n : ℕ}

/-- For $Z \in \mathbb H_n$, $\det(CZ + D) \ne 0$. -/
theorem det_ne_zero {C D : Matrix (Fin n) (Fin n) ℝ} (hsym : C * Dᵀ = D * Cᵀ)
    (hrank : ∀ u : Fin n → ℝ, u ᵥ* C = 0 → u ᵥ* D = 0 → u = 0)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : Z ∈ siegelH n) : (W C D Z).det ≠ 0 := by
  intro hdet
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  have hcol : ∀ j, ∑ k, A C w k * Z k j + A D w j = 0 := by
    intro j
    have := congrFun hw j
    simp only [Matrix.vecMul, dotProduct, W, Matrix.add_apply, Matrix.mul_apply, Matrix.map_apply,
      Pi.zero_apply, mul_add, Finset.sum_add_distrib] at this
    unfold A
    rw [← this]
    congr 1
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
  have hsymm : ∀ i j, Z i j = Z j i := fun i j => (congrFun₂ hZ.1 i j).symm
  have ha : A C w = 0 := by
    refine eq_zero_of_form hZ _ _ (fun j => ?_) (form_sym hsym w)
    have := hcol j
    rw [eq_neg_iff_add_eq_zero, ← this]
    exact congrArg (· + _) (Finset.sum_congr rfl fun k _ => by rw [hsymm j k]; ring)
  have hb : A D w = 0 := by
    funext j
    have := hcol j
    simpa [ha] using this
  exact hw0 (w_eq_zero hrank w ha hb)

/-- Column $0$ of $C Z_s + D$ is column $0$ of $C Z_0 + D$ plus $(is)\cdot c_0$. -/
lemma W_zt_eq {C D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {Z : Matrix (Fin n) (Fin n) ℂ} (s : ℂ) :
    W C D (zt Z s) = (W C D (zt Z 0)).updateCol 0
      (fun i => (W C D (zt Z 0)) i 0 + (Complex.I * s) * (C i 0 : ℂ)) := by
  ext i j
  refine Fin.cases ?_ (fun j' => ?_) j
  · simp [W, zt, Matrix.mul_apply, Fin.sum_univ_succ]; ring
  · simp [W, zt, Matrix.mul_apply, Fin.sum_univ_succ,
      Fin.succ_ne_zero]

/-- $\det(CZ_s + D)$ is affine in $s$: $\det W(Z_s) = \det W(Z_0) + s\,\alpha$ with
$\alpha = i\det[c_0 \mid \text{columns } 1, \dots, r \text{ of } W(Z_0)]$. -/
theorem det_zt_affine {C D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {Z : Matrix (Fin n) (Fin n) ℂ}
    (s : ℂ) :
    (W C D (zt Z s)).det = (W C D (zt Z 0)).det + s * (Complex.I *
      ((W C D (zt Z 0)).updateCol 0 (fun i => (C i 0 : ℂ))).det) := by
  have hadd := Matrix.det_updateCol_add (W C D (zt Z 0)) 0 (fun i => (W C D (zt Z 0)) i 0)
    (fun i => (Complex.I * s) * (C i 0 : ℂ))
  rw [W_zt_eq s]
  refine hadd.trans ?_
  have : (W C D (zt Z 0)).updateCol 0 (fun i => (W C D (zt Z 0)) i 0) = W C D (zt Z 0) :=
    Matrix.updateCol_eq_self _ _
  rw [this]
  have h2 : (fun i => (Complex.I * s) * (C i 0 : ℂ)) = (Complex.I * s) • (fun i => (C i 0 : ℂ)) := by
    funext i; simp
  rw [h2, Matrix.det_updateCol_smul]
  ring

/-- If column $0$ of $C$ vanishes, $\det(CZ_s + D)$ does not depend on $s$. -/
theorem det_zt_of_col_zero {C D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {Z : Matrix (Fin n) (Fin n) ℂ} (h : ∀ i, C i 0 = 0) (s : ℂ) :
    (W C D (zt Z s)).det = (W C D (zt Z 0)).det := by
  rw [det_zt_affine s]
  have : ((W C D (zt Z 0)).updateCol 0 (fun i => (C i 0 : ℂ))).det = 0 := by
    apply Matrix.det_eq_zero_of_column_eq_zero 0
    intro i; simp [h]
  rw [this]; simp

/-- $Z_s \in \mathbb H_{r+1}$ for $Z \in \mathbb H_r$ and $\operatorname{Re}s > 0$. -/
theorem zt_mem {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : Z ∈ siegelH n) {s : ℂ} (hs : 0 < s.re) :
    zt Z s ∈ siegelH (n + 1) := by
  have hsymm : ∀ i j, Z i j = Z j i := fun i j => (congrFun₂ hZ.1 i j).symm
  refine ⟨?_, ?_⟩
  · ext i j
    refine Fin.cases ?_ (fun i' => ?_) i
    · refine Fin.cases ?_ (fun j' => ?_) j <;> simp [zt]
    · refine Fin.cases ?_ (fun j' => ?_) j
      · simp [zt]
      · simpa [zt] using hsymm j' i'
  · have hY := hZ.2
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x hx => ?_⟩
    · ext i j
      refine Fin.cases ?_ (fun i' => ?_) i
      · refine Fin.cases ?_ (fun j' => ?_) j <;> simp [zt, Matrix.conjTranspose_apply]
      · refine Fin.cases ?_ (fun j' => ?_) j
        · simp [zt, Matrix.conjTranspose_apply]
        · simp [zt, Matrix.conjTranspose_apply, hsymm j' i']
    · have hq : star x ⬝ᵥ ((zt Z s).map Complex.im *ᵥ x)
          = s.re * (x 0) ^ 2 + (fun i : Fin n => x i.succ) ⬝ᵥ ((Z.map Complex.im) *ᵥ (fun i : Fin n => x i.succ)) := by
        simp [dotProduct, mulVec, Fin.sum_univ_succ, zt, Finset.mul_sum]
        ring
      rw [hq]
      by_cases ht : (fun i : Fin n => x i.succ) = 0
      · have h0 : x 0 ≠ 0 := by
          intro h0
          apply hx
          funext i
          refine Fin.cases h0 (fun i' => congrFun ht i') i
        rw [ht]
        simp only [Matrix.mulVec_zero, dotProduct_zero, add_zero]
        have := sq_pos_of_ne_zero h0
        positivity
      · have h1 := hY.dotProduct_mulVec_pos ht
        simp only [star_trivial] at h1
        have h2 : 0 ≤ s.re * (x 0) ^ 2 := by positivity
        linarith

/-- The affine function $s \mapsto \det W(Z_s)$ does not vanish on $\operatorname{Re}s > 0$. -/
lemma det_zt_ne_zero {C D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hsym : C * Dᵀ = D * Cᵀ)
    (hrank : ∀ u : Fin (n + 1) → ℝ, u ᵥ* C = 0 → u ᵥ* D = 0 → u = 0)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : Z ∈ siegelH n) {s : ℂ} (hs : 0 < s.re) :
    (W C D (zt Z s)).det ≠ 0 :=
  det_ne_zero hsym hrank (zt_mem hZ hs)

/-- $t \mapsto \lVert\det(CZ_t + D)\rVert$ is monotone on $(0, \infty)$. -/
theorem monotoneOn_norm_det {C D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hsym : C * Dᵀ = D * Cᵀ)
    (hrank : ∀ u : Fin (n + 1) → ℝ, u ᵥ* C = 0 → u ᵥ* D = 0 → u = 0)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : Z ∈ siegelH n) :
    MonotoneOn (fun t : ℝ => ‖(W C D (zt Z t)).det‖) (Set.Ioi 0) := by
  have hne := fun {s : ℂ} (hs : 0 < s.re) => det_zt_ne_zero hsym hrank hZ hs
  set β := (W C D (zt Z 0)).det
  set α := Complex.I * ((W C D (zt Z 0)).updateCol 0 (fun i => (C i 0 : ℂ))).det
  intro t₁ ht₁ t₂ ht₂ hle
  beta_reduce
  rw [det_zt_affine (s := (t₁ : ℂ)), det_zt_affine (s := (t₂ : ℂ))]
  change ‖β + (t₁ : ℂ) * α‖ ≤ ‖β + (t₂ : ℂ) * α‖
  by_cases hα : α = 0
  · simp [hα]
  · set s' : ℂ := -β / α
    have hre : s'.re ≤ 0 := by
      by_contra hpos
      push Not at hpos
      apply hne hpos
      rw [det_zt_affine]
      have : β + s' * α = 0 := by simp only [s']; field_simp; ring
      exact this
    have hform : ∀ t : ℝ, ‖β + (t : ℂ) * α‖ = ‖α‖ * ‖(t : ℂ) - s'‖ := by
      intro t
      rw [← norm_mul]
      congr 1
      simp only [s']; field_simp; ring
    rw [hform, hform]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    have ht1 : (0:ℝ) < t₁ := ht₁
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
      Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im]
    nlinarith

/-- If column $0$ of $C$ is nonzero, the coefficient $\alpha$ in `det_zt_affine` is nonzero. -/
lemma alpha_ne_zero {C D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hsym : C * Dᵀ = D * Cᵀ)
    (hrank : ∀ u : Fin (n + 1) → ℝ, u ᵥ* C = 0 → u ᵥ* D = 0 → u = 0)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : Z ∈ siegelH n) (hc : ∃ i, C i 0 ≠ 0) :
    Complex.I * ((W C D (zt Z 0)).updateCol 0 (fun i => (C i 0 : ℂ))).det ≠ 0 := by
  refine mul_ne_zero Complex.I_ne_zero ?_
  intro hdet
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  have hsymm : ∀ i j, Z i j = Z j i := fun i j => (congrFun₂ hZ.1 i j).symm
  -- column 0
  have h0 : A C w 0 = 0 := by
    have := congrFun hw 0
    simpa [Matrix.vecMul, dotProduct, A] using this
  -- columns j + 1
  have hentry : ∀ (i : Fin (n + 1)) (j : Fin n), W C D (zt Z 0) i j.succ
      = ∑ k : Fin n, (C i k.succ : ℂ) * Z k j + (D i j.succ : ℂ) := by
    intro i j
    simp [W, zt, Matrix.mul_apply, Fin.sum_univ_succ]
  have hcol : ∀ j : Fin n, ∑ k : Fin n, A C w k.succ * Z k j + A D w j.succ = 0 := by
    intro j
    have := congrFun hw j.succ
    simp only [Matrix.vecMul, dotProduct, Matrix.updateCol_apply, Fin.succ_ne_zero,
      ↓reduceIte, hentry, Pi.zero_apply] at this
    rw [← this]
    unfold A
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
  have hform := form_sym hsym w
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, h0] at hform
  simp only [zero_mul, map_zero, mul_zero, zero_add] at hform
  have ha' : (fun k : Fin n => A C w k.succ) = 0 := by
    refine eq_zero_of_form hZ _ _ (fun j => ?_) hform
    have := hcol j
    rw [eq_neg_iff_add_eq_zero, ← this]
    exact congrArg (· + _) (Finset.sum_congr rfl fun k _ => by rw [hsymm j k]; ring)
  have hb' : (fun k : Fin n => A D w k.succ) = 0 := by
    funext j
    have := hcol j
    have h' : ∀ k : Fin n, A C w k.succ = 0 := fun k => congrFun ha' k
    simpa [h'] using this
  have hA : A C w = 0 := by
    funext k
    refine Fin.cases h0 (fun k' => congrFun ha' k') k
  have hrow := row_sym hsym w
  have hb0 : A D w 0 = 0 := by
    obtain ⟨i, hi⟩ := hc
    have := hrow i
    rw [hA] at this
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero] at this
    rw [Fin.sum_univ_succ] at this
    have h' : ∀ k : Fin n, A D w k.succ = 0 := fun k => congrFun hb' k
    simp only [h', zero_mul, Finset.sum_const_zero, add_zero] at this
    have := this.symm
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd (by exact_mod_cast h) hi
  have hB : A D w = 0 := by
    funext k
    refine Fin.cases hb0 (fun k' => congrFun hb' k') k
  exact hw0 (w_eq_zero hrank w hA hB)

/-- If column $0$ of $C$ is nonzero, $\lVert\det(CZ_t + D)\rVert \to \infty$ as $t \to \infty$. -/
theorem tendsto_norm_det {C D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hsym : C * Dᵀ = D * Cᵀ)
    (hrank : ∀ u : Fin (n + 1) → ℝ, u ᵥ* C = 0 → u ᵥ* D = 0 → u = 0)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : Z ∈ siegelH n) (hc : ∃ i, C i 0 ≠ 0) :
    Tendsto (fun t : ℝ => ‖(W C D (zt Z t)).det‖) atTop atTop := by
  have hα := alpha_ne_zero hsym hrank hZ hc
  set β := (W C D (zt Z 0)).det
  set α := Complex.I * ((W C D (zt Z 0)).updateCol 0 (fun i => (C i 0 : ℂ))).det
  have hpos : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have h1 : Tendsto (fun t : ℝ => t * ‖α‖ - ‖β‖) atTop atTop :=
    tendsto_atTop_add_const_right _ _ ((tendsto_id.atTop_mul_const hpos))
  refine tendsto_atTop_mono (fun t => ?_) h1
  rw [det_zt_affine]
  have h2 : ‖(t : ℂ) * α‖ ≤ ‖β + (t : ℂ) * α‖ + ‖β‖ := by
    calc ‖(t : ℂ) * α‖ = ‖(β + (t : ℂ) * α) - β‖ := by congr 1; ring
      _ ≤ ‖β + (t : ℂ) * α‖ + ‖β‖ := norm_sub_le _ _
  by_cases ht : 0 ≤ t
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht] at h2
    linarith
  · push Not at ht
    have : t * ‖α‖ - ‖β‖ ≤ 0 := by nlinarith [norm_nonneg β]
    exact this.trans (norm_nonneg _)

end QuadFormsKB.SiegelWeil.Forms.PhiArch
