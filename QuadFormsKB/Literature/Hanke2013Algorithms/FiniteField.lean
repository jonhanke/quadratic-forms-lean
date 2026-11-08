/-
# Hanke 2013, §3.2: isotropy and maximal totally isotropic subspaces over finite fields

J. Hanke, *Algorithms for computing maximal lattices in bilinear (and quadratic) spaces over number fields*,
Contemp. Math. 587 (2013); source used: arXiv:1208.2481v3 (bib key `hanke2013algorithms`), §3.2, pp. 10–13.

**Setting.** $K$ is a field (a finite field $\mathbb F_q$ where stated), $V$ a finite-dimensional $K$-vector space and
$B$ = `B : LinearMap.BilinForm K V` a symmetric bilinear form (hypothesis `hB : ∀ x y, B x y = B y x`), with
$Q_B(x) := B(x, x)$. *Non-degenerate* means `hnd : ∀ x, (∀ y, B x y = 0) → x = 0` (the radical is $0$). A vector
$v\ne0$ is *isotropic* if $Q_B(v) = 0$ (`IsIsoVec`); a subspace $W$ is *totally isotropic* if $Q_B(W) = 0$ (`IsTotIso`,
the paper's §1 definition) and *maximal totally isotropic* if no strictly larger subspace is (`IsMaxTotIso`).

**Proves.**
* **Remark 3.9** (char $2$): $Q_B$ is additive and $Q_B(\alpha x) = \alpha^2Q_B(x)$ (`remark_3_9_add`, `remark_3_9_smul`);
  its kernel is a subspace (`kerQ`); over a finite field of characteristic $2$ it has codimension $\le1$, and exactly
  $1$ when $Q_B\ne0$ (`remark_3_9_finrank`).
* **Lemma 3.10** (`lemma_3_10_dim_ge_three`, `lemma_3_10_dim_two_odd`, `lemma_3_10_dim_two_char_two`,
  `lemma_3_10_dim_one`).
* **Algorithm 3.11** (`algorithm_3_11`): a point of the line $\vec a + t\vec m$ ($\vec a,\vec m$ independent) with
  $Q_B = 0$ is an isotropic vector. (The random choice is not formalized.)
* **Algorithm 3.12** (`algorithm_3_12`), with an *Erratum* in the shear step (see below).
* **Algorithm 3.13** (`algorithm_3_13`): $M = R + L$ is maximal totally isotropic (characteristic $\ne2$).
* **Algorithm 3.14** (`algorithm_3_14_shear`, `algorithm_3_14`), and in characteristic $2$ the kernel of $Q_B$ is the
  unique maximal totally isotropic subspace (`isMaxTotIso_kerQ`, `le_kerQ_of_isTotIso`).
* **Remark 3.15** (`remark_3_15`): in characteristic $2$ over a finite field, $\dim(V/\ker Q_B)\le1$.

*Erratum (Algorithm 3.12, step 4):* after scaling to $B(\vec v,\vec w) = 1$, the printed shear
$\vec w\mapsto\vec w - B(\vec v,\vec w)\vec v = \vec w - \vec v$ gives $Q_B = B(\vec w,\vec w) - 2$, not $0$; the shear that
works is $\vec w\mapsto\vec w - \frac{B(\vec w,\vec w)}2\vec v$ (characteristic $\ne2$). *Erratum (proof of Algorithm 3.12):*
"some $B(\vec v,\vec v_i) = 0$" should read "$\ne0$".
-/
import Mathlib
import QuadFormsKB.Citation

open Module Polynomial

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2013Algorithms

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-! ### Definitions -/

/-- **Isotropic vector** (Hanke 2013, §1, p. 4): $\vec v\ne0$ with $Q_B(\vec v) = B(\vec v,\vec v) = 0$. -/
@[kb "hanke2013algorithms" "§1, p. 4 (isotropic vector; Lemma 3.10)"]
def IsIsoVec (B : LinearMap.BilinForm K V) (v : V) : Prop := v ≠ 0 ∧ B v v = 0

/-- **Totally isotropic subspace** (Hanke 2013, §1, p. 4): $Q_B(W) = \{0\}$. -/
@[kb "hanke2013algorithms" "§1, p. 4 (totally isotropic subspace)"]
def IsTotIso (B : LinearMap.BilinForm K V) (W : Submodule K V) : Prop := ∀ w ∈ W, B w w = 0

/-- **Maximal totally isotropic subspace** (Hanke 2013, Algorithms 3.13, 3.14, p. 12): totally isotropic and not
properly contained in a totally isotropic subspace. -/
@[kb "hanke2013algorithms" "Algorithms 3.13, 3.14, p. 12 (maximal totally isotropic subspace)"]
def IsMaxTotIso (B : LinearMap.BilinForm K V) (M : Submodule K V) : Prop :=
  IsTotIso B M ∧ ∀ M' : Submodule K V, M ≤ M' → IsTotIso B M' → M' = M

/-- Polarization: $Q_B(x + y) = Q_B(x) + 2B(x, y) + Q_B(y)$ for symmetric $B$. -/
theorem qB_add (B : LinearMap.BilinForm K V) (hB : ∀ x y, B x y = B y x) (x y : V) :
    B (x + y) (x + y) = B x x + 2 * B x y + B y y := by
  simp only [map_add, LinearMap.add_apply, hB y x]; ring

/-- In characteristic $\ne2$, a totally isotropic subspace has $B(W, W) = 0$. -/
theorem IsTotIso.bil_eq_zero {B : LinearMap.BilinForm K V} (hB : ∀ x y, B x y = B y x) (h2 : (2 : K) ≠ 0)
    {W : Submodule K V} (hW : IsTotIso B W) {x y : V} (hx : x ∈ W) (hy : y ∈ W) : B x y = 0 := by
  have h := qB_add B hB x y
  rw [hW _ (W.add_mem hx hy), hW x hx, hW y hy] at h
  have : 2 * B x y = 0 := by linear_combination -h
  exact (mul_eq_zero.1 this).resolve_left h2

/-! ### Remark 3.9: $Q_B$ in characteristic $2$ -/

section CharTwo

variable (B : LinearMap.BilinForm K V) (hB : ∀ x y, B x y = B y x) (h2 : (2 : K) = 0)
include hB h2

/-- **Remark 3.9** (Hanke 2013, p. 10): in characteristic $2$, $Q_B(x + y) = Q_B(x) + Q_B(y)$. -/
@[kb "hanke2013algorithms" "Remark 3.9, p. 10 (Q_B additive in characteristic 2)"]
theorem remark_3_9_add (x y : V) : B (x + y) (x + y) = B x x + B y y := by
  rw [qB_add B hB, h2]; ring

omit hB h2 in
/-- **Remark 3.9** (Hanke 2013, p. 10): $Q_B(\alpha x) = \alpha^2Q_B(x)$ (Frobenius-semilinear in characteristic $2$). -/
@[kb "hanke2013algorithms" "Remark 3.9, p. 10 (Q_B(αx) = α²Q_B(x))"]
theorem remark_3_9_smul (a : K) (x : V) : B (a • x) (a • x) = a ^ 2 * B x x := by
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]; ring

/-- **The kernel of $Q_B$** in characteristic $2$, a subspace (Hanke 2013, Remark 3.9, p. 10). -/
@[kb "hanke2013algorithms" "Remark 3.9, p. 10 (Ker(Q_B) is a subspace)"]
def kerQ : Submodule K V where
  carrier := {x | B x x = 0}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at *
    rw [remark_3_9_add B hB h2, hx, hy, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    intro a x hx
    simp only [Set.mem_setOf_eq] at *
    rw [remark_3_9_smul, hx, mul_zero]

theorem mem_kerQ {x : V} : x ∈ kerQ B hB h2 ↔ B x x = 0 := Iff.rfl

/-- In characteristic $2$, every totally isotropic subspace lies in $\ker Q_B$. -/
theorem le_kerQ_of_isTotIso {W : Submodule K V} (hW : IsTotIso B W) : W ≤ kerQ B hB h2 := fun w hw => hW w hw

/-- **In characteristic $2$, $\ker Q_B$ is the (unique) maximal totally isotropic subspace.** -/
@[kb "hanke2013algorithms" "Remark 3.9 and Algorithm 3.14, pp. 10–13 (characteristic 2)"]
theorem isMaxTotIso_kerQ : IsMaxTotIso B (kerQ B hB h2) :=
  ⟨fun _ hw => hw, fun M' hM hM' => le_antisymm (le_kerQ_of_isTotIso B hB h2 hM') hM⟩

variable [Fintype K] [FiniteDimensional K V]

/-- Over a finite field of characteristic $2$: if $Q_B(u)\ne0$ then $V = \ker Q_B\oplus Ku$ (every $y$ is
$(y - cu) + cu$ with $c^2 = Q_B(y)/Q_B(u)$). -/
theorem isCompl_kerQ_span (hK : ringChar K = 2) {u : V} (hu : B u u ≠ 0) :
    IsCompl (kerQ B hB h2) (K ∙ u) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hxu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hxu
    rw [mem_kerQ, remark_3_9_smul] at hx
    rcases mul_eq_zero.1 hx with h | h
    · rw [pow_eq_zero_iff two_ne_zero] at h; simp [h]
    · exact absurd h hu
  · rw [codisjoint_iff, eq_top_iff]
    intro y _
    obtain ⟨c, hc⟩ := FiniteField.isSquare_of_char_two hK (B y y / B u u)
    have hy : y - c • u ∈ kerQ B hB h2 := by
      have hc2 : c ^ 2 = B y y / B u u := by rw [sq]; exact hc.symm
      rw [mem_kerQ, sub_eq_add_neg, remark_3_9_add B hB h2, ← neg_smul, remark_3_9_smul, neg_sq, hc2,
        div_mul_cancel₀ _ hu]
      have : (2 : K) * B y y = 0 := by rw [h2, zero_mul]
      linear_combination this
    have : y = (y - c • u) + c • u := by abel
    rw [this]
    exact Submodule.add_mem_sup hy (Submodule.mem_span_singleton.2 ⟨c, rfl⟩)

/-- **Remark 3.9, dimensions** (Hanke 2013, p. 10: $\dim\mathrm{Im}(Q_B) + \dim\mathrm{Ker}(Q_B) = \dim V$): over a finite
field of characteristic $2$, $\dim\ker Q_B + 1 = \dim V$ if $Q_B\ne0$ (the image is then all of $K$), and
$\ker Q_B = V$ if $Q_B = 0$. -/
@[kb "hanke2013algorithms" "Remark 3.9, p. 10 (dim Im(Q_B) + dim Ker(Q_B) = dim V)"]
theorem remark_3_9_finrank (hK : ringChar K = 2) :
    (∃ u, B u u ≠ 0) → finrank K (kerQ B hB h2) + 1 = finrank K V := by
  rintro ⟨u, hu⟩
  have hc := isCompl_kerQ_span B hB h2 hK hu
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  rw [← Submodule.finrank_add_eq_of_isCompl hc, finrank_span_singleton hu0]

/-- **Remark 3.15** (Hanke 2013, p. 13): in characteristic $2$ (finite field), $\dim V - \dim\ker Q_B\le1$: the
anisotropic part has dimension $\le1$. -/
@[kb "hanke2013algorithms" "Remark 3.15, p. 13 (dim A ≤ 1 in characteristic 2)"]
theorem remark_3_15 (hK : ringChar K = 2) : finrank K V ≤ finrank K (kerQ B hB h2) + 1 := by
  by_cases h : ∃ u, B u u ≠ 0
  · rw [remark_3_9_finrank B hB h2 hK h]
  · push_neg at h
    have : kerQ B hB h2 = ⊤ := eq_top_iff.2 fun x _ => h x
    rw [this, finrank_top]; omega

end CharTwo

/-! ### Lemma 3.10: isotropy over $\mathbb F_q$ -/

section Lemma310

variable [Fintype K] [FiniteDimensional K V]

/-- **Lemma 3.10 (1)** (Hanke 2013, p. 10): over a finite field, a symmetric bilinear space of dimension $\ge3$ is
isotropic. (Non-degeneracy is not needed.) *Proof*: odd characteristic: an orthogonal basis $\vec v_0,\vec v_1,\vec v_2,\dots$
with $d_i = Q_B(\vec v_i)$; if some $d_i = 0$ it is isotropic, otherwise $d_0a^2 + d_1b^2 + d_2 = 0$ has a solution
(Mathlib's `FiniteField.exists_root_sum_quadratic`, the counting argument behind O'Meara 62:1b) and
$a\vec v_0 + b\vec v_1 + \vec v_2$ is isotropic; characteristic $2$: $\ker Q_B$ has dimension $\ge\dim V - 1\ge2$
(Remark 3.9), the paper's argument. -/
@[kb "hanke2013algorithms" "Lemma 3.10 (1), p. 10"]
theorem lemma_3_10_dim_ge_three (B : LinearMap.BilinForm K V) (hB : ∀ x y, B x y = B y x)
    (hd : 3 ≤ finrank K V) : ∃ v, IsIsoVec B v := by
  classical
  by_cases hK : ringChar K = 2
  · -- characteristic 2
    have h2 : (2 : K) = 0 := by
      have := (ringChar.spec K 2).2 (by rw [hK])
      exact_mod_cast this
    have hle := remark_3_15 B hB h2 hK
    have hpos : 0 < finrank K (kerQ B hB h2) := by omega
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (Submodule.one_le_finrank_iff.1 hpos)
    exact ⟨v, hv0, hv⟩
  · have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
    haveI : Invertible (2 : K) := invertibleOfNonzero h2
    obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis (B := B)
      ((LinearMap.isSymm_def).2 fun x y => by rw [RingHom.id_apply]; exact hB x y)
    set i0 : Fin (finrank K V) := ⟨0, by omega⟩
    set i1 : Fin (finrank K V) := ⟨1, by omega⟩
    set i2 : Fin (finrank K V) := ⟨2, by omega⟩
    have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
    have h02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
    have h12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
    have hort : ∀ i j, i ≠ j → B (b i) (b j) = 0 := fun i j hij => hb hij
    by_cases hz : ∃ i, B (b i) (b i) = 0
    · obtain ⟨i, hi⟩ := hz
      exact ⟨b i, b.ne_zero i, hi⟩
    push_neg at hz
    set d0 := B (b i0) (b i0)
    set d1 := B (b i1) (b i1)
    set d2 := B (b i2) (b i2)
    have hf : (C d0 * X ^ 2 : K[X]).degree = 2 := by
      rw [degree_C_mul (hz i0), degree_X_pow]; rfl
    have hg : (C d1 * X ^ 2 + C d2 : K[X]).degree = 2 := by
      rw [degree_add_C (by rw [degree_C_mul (hz i1), degree_X_pow]; norm_num), degree_C_mul (hz i1),
        degree_X_pow]; rfl
    obtain ⟨a, c, hac⟩ := FiniteField.exists_root_sum_quadratic hf hg (FiniteField.odd_card_of_char_ne_two hK)
    simp only [eval_mul, eval_C, eval_pow, eval_X, eval_add] at hac
    refine ⟨a • b i0 + c • b i1 + b i2, ?_, ?_⟩
    · intro h0
      have := congrArg (fun x => b.repr x i2) h0
      simp only [map_add, map_smul, Basis.repr_self, Finsupp.add_apply, Finsupp.smul_apply,
        Finsupp.single_apply, if_neg h02, if_neg h12, if_pos rfl, smul_eq_mul, mul_zero, zero_add,
        map_zero, Finsupp.coe_zero, Pi.zero_apply] at this
      exact one_ne_zero this
    · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        hort _ _ h01, hort _ _ h02, hort _ _ h12, hort _ _ h01.symm, hort _ _ h02.symm, hort _ _ h12.symm]
      linear_combination hac

/-- **Lemma 3.10 (2), odd characteristic** (Hanke 2013, p. 10): a non-degenerate symmetric bilinear plane over $\mathbb F_q$,
$q$ odd, is isotropic iff $\det(B) = -1$ up to squares, i.e. $-\det$ of its Gram matrix in an orthogonal basis is a
square. (Here in an orthogonal basis $\vec v_0,\vec v_1$: $-Q_B(\vec v_0)Q_B(\vec v_1)$ is a square.) -/
@[kb "hanke2013algorithms" "Lemma 3.10 (2), p. 10 (dim 2, odd characteristic)"]
theorem lemma_3_10_dim_two_odd (B : LinearMap.BilinForm K V) (hB : ∀ x y, B x y = B y x)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) (b : Basis (Fin 2) K V) (hb : B (b 0) (b 1) = 0) :
    (∃ v, IsIsoVec B v) ↔ IsSquare (-(B (b 0) (b 0) * B (b 1) (b 1))) := by
  have hb' : B (b 1) (b 0) = 0 := by rw [hB]; exact hb
  have hd0 : B (b 0) (b 0) ≠ 0 := by
    intro h
    apply b.ne_zero 0
    apply hnd
    intro y
    have hy := b.sum_repr y
    rw [← hy, Fin.sum_univ_two, map_add, map_smul, map_smul, h, hb, smul_zero, smul_zero, add_zero]
  have hd1 : B (b 1) (b 1) ≠ 0 := by
    intro h
    apply b.ne_zero 1
    apply hnd
    intro y
    have hy := b.sum_repr y
    rw [← hy, Fin.sum_univ_two, map_add, map_smul, map_smul, h, hb', smul_zero, smul_zero, add_zero]
  set d0 := B (b 0) (b 0)
  set d1 := B (b 1) (b 1)
  have hQ : ∀ x y : K, B (x • b 0 + y • b 1) (x • b 0 + y • b 1) = x ^ 2 * d0 + y ^ 2 * d1 := by
    intro x y
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hb, hb']
    ring
  constructor
  · rintro ⟨v, hv0, hv⟩
    have hy := b.sum_repr v
    rw [Fin.sum_univ_two] at hy
    rw [← hy, hQ] at hv
    set x := b.repr v 0
    set y := b.repr v 1
    have hx : x ≠ 0 := by
      intro hx
      rw [hx] at hv
      have : y ^ 2 * d1 = 0 := by simpa using hv
      have hy0 : y = 0 := by simpa [hd1] using this
      apply hv0
      rw [← hy, hx, hy0, zero_smul, zero_smul, add_zero]
    refine ⟨d1 * y / x, ?_⟩
    rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hx hx)]
    linear_combination (-d1) * hv
  · rintro ⟨s, hs⟩
    refine ⟨s • b 0 + d0 • b 1, ?_, ?_⟩
    · intro h0
      have := congrArg (fun x => b.repr x 1) h0
      simp at this
      exact hd0 this
    · rw [hQ]
      linear_combination (-d0) * hs

/-- **Lemma 3.10 (2), characteristic $2$** (Hanke 2013, p. 10): a bilinear space of dimension $\ge2$ over a finite field of
characteristic $2$ is isotropic (the kernel of $Q_B$ has dimension $\ge\dim V - 1$). -/
@[kb "hanke2013algorithms" "Lemma 3.10 (2), p. 10 (characteristic 2)"]
theorem lemma_3_10_dim_two_char_two (B : LinearMap.BilinForm K V) (hB : ∀ x y, B x y = B y x)
    (hK : ringChar K = 2) (hd : 2 ≤ finrank K V) : ∃ v, IsIsoVec B v := by
  have h2 : (2 : K) = 0 := by
    have := (ringChar.spec K 2).2 (by rw [hK])
    exact_mod_cast this
  have hle := remark_3_15 B hB h2 hK
  have hpos : 0 < finrank K (kerQ B hB h2) := by omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (Submodule.one_le_finrank_iff.1 hpos)
  exact ⟨v, hv0, hv⟩

end Lemma310

/-- **Lemma 3.10 (3)** (Hanke 2013, p. 11): a non-degenerate bilinear line is not isotropic (any field). -/
@[kb "hanke2013algorithms" "Lemma 3.10 (3), p. 11"]
theorem lemma_3_10_dim_one [FiniteDimensional K V] (B : LinearMap.BilinForm K V)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) (hd : finrank K V = 1) : ¬ ∃ v, IsIsoVec B v := by
  rintro ⟨v, hv0, hv⟩
  apply hv0
  apply hnd
  intro y
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' v hv0).1 hd y
  rw [map_smul, hv, smul_zero]

/-! ### Algorithms 3.11, 3.12 -/

/-- **Algorithm 3.11, correctness** (Hanke 2013, p. 11): if $\vec a,\vec m$ are linearly independent and
$Q_B(\vec a + t_0\vec m) = 0$, then $\vec v = \vec a + t_0\vec m$ is an isotropic vector (non-zero). The random choice
of $\vec a,\vec m$ (success probability about $\frac12$) is not formalized. -/
@[kb "hanke2013algorithms" "Algorithm 3.11, p. 11"]
theorem algorithm_3_11 (B : LinearMap.BilinForm K V) {a m : V} (hli : LinearIndependent K ![a, m]) {t : K}
    (ht : B (a + t • m) (a + t • m) = 0) : IsIsoVec B (a + t • m) := by
  refine ⟨fun h => ?_, ht⟩
  have := LinearIndependent.pair_iff.1 hli 1 t (by simpa using h)
  exact one_ne_zero this.1

/-- **Algorithm 3.12, corrected** (Hanke 2013, pp. 11–12; *Erratum*, see the module docstring): in characteristic
$\ne2$, for a non-degenerate symmetric $(V, B)$ and an isotropic $\vec v$ there is $\vec w$ with $B(\vec v,\vec w) = 1$ and
$Q_B(\vec w) = 0$, so $\{\vec v,\vec w\}$ spans a hyperbolic plane. Steps: choose $\vec u$ with $B(\vec v,\vec u)\ne0$
(non-degeneracy), scale to $B(\vec v,\vec u) = 1$, and shear $\vec w = \vec u - \frac{Q_B(\vec u)}2\vec v$. -/
@[kb "hanke2013algorithms" "Algorithm 3.12, pp. 11–12 (corrected shear)"]
theorem algorithm_3_12 (B : LinearMap.BilinForm K V) (hB : ∀ x y, B x y = B y x) (h2 : (2 : K) ≠ 0)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) {v : V} (hv : IsIsoVec B v) :
    ∃ w, B v w = 1 ∧ B w w = 0 ∧ LinearIndependent K ![v, w] := by
  obtain ⟨hv0, hvv⟩ := hv
  have : ∃ u, B v u ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv0 (hnd v h)
  obtain ⟨u, hu⟩ := this
  set u' := (B v u)⁻¹ • u
  have hu' : B v u' = 1 := by simp [u', hu]
  set w := u' - (B u' u' / 2) • v
  have hvw : B v w = 1 := by
    simp only [w, map_sub, map_smul, smul_eq_mul, hu', hvv, mul_zero, sub_zero]
  have hww : B w w = 0 := by
    have hvu : B u' v = 1 := by rw [hB]; exact hu'
    simp only [w, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hu', hvu, hvv]
    field_simp
    ring
  refine ⟨w, hvw, hww, ?_⟩
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1 : B v (s • v + t • w) = 0 := by rw [hst, map_zero]
  simp only [map_add, map_smul, smul_eq_mul, hvv, hvw, mul_zero, zero_add, mul_one] at h1
  subst h1
  rw [zero_smul, add_zero] at hst
  exact ⟨(smul_eq_zero.1 hst).resolve_right hv0, rfl⟩

/-! ### Algorithms 3.13, 3.14: maximal totally isotropic subspaces -/

/-- **Algorithm 3.13, maximality** (Hanke 2013, p. 12), characteristic $\ne2$: suppose $V = R + L + L' + A$ (`hsup`)
with $R$ in the radical (`hRad`: $B(\vec r,\cdot) = 0$ for $\vec r\in R$), $L$ totally isotropic (`hL`), $A$ anisotropic
(`hA`: $Q_B(\vec a) = 0\Rightarrow\vec a = 0$ for $\vec a\in A$), $B(L, A) = 0$ (`hLA`), and $L'$ paired with $L$
(`hpair`: every $\vec l'\in L'\setminus0$ has some $\vec l_0\in L$ with $B(\vec l',\vec l_0)\ne0$); this is the
decomposition $V = R\perp(L\oplus L')\perp A$ of the paper, $H = L\oplus L'$ hyperbolic. Then $M = R + L$ is a maximal
totally isotropic subspace (the paper's proof). The decomposition itself is produced by Lemma 3.10 and Algorithms
3.11, 3.12; its existence is not formalized here. -/
@[kb "hanke2013algorithms" "Algorithm 3.13, p. 12 (M = R + L is maximal totally isotropic)"]
theorem algorithm_3_13 (B : LinearMap.BilinForm K V) (hB : ∀ x y, B x y = B y x) (h2 : (2 : K) ≠ 0)
    (R L L' A : Submodule K V) (hRad : ∀ r ∈ R, ∀ x, B r x = 0) (hL : IsTotIso B L)
    (hA : ∀ a ∈ A, B a a = 0 → a = 0) (hLA : ∀ l ∈ L, ∀ a ∈ A, B l a = 0)
    (hpair : ∀ l' ∈ L', l' ≠ 0 → ∃ l₀ ∈ L, B l' l₀ ≠ 0) (hsup : R ⊔ L ⊔ L' ⊔ A = ⊤) :
    IsMaxTotIso B (R ⊔ L) := by
  have hrad' : ∀ r ∈ R, ∀ x, B x r = 0 := fun r hr x => by rw [hB]; exact hRad r hr x
  have hLL : ∀ l ∈ L, ∀ l₀ ∈ L, B l l₀ = 0 := fun l hl l₀ hl₀ => hL.bil_eq_zero hB h2 hl hl₀
  have hiso : IsTotIso B (R ⊔ L) := by
    intro x hx
    obtain ⟨r, hr, l, hl, rfl⟩ := Submodule.mem_sup.1 hx
    simp only [map_add, LinearMap.add_apply, hRad r hr, hrad' r hr, hL l hl, zero_add]
  refine ⟨hiso, fun M' hM hM' => le_antisymm (fun v hv => ?_) hM⟩
  have hvt : v ∈ R ⊔ L ⊔ L' ⊔ A := hsup ▸ Submodule.mem_top
  obtain ⟨x, hx, a, ha, rfl⟩ := Submodule.mem_sup.1 hvt
  obtain ⟨y, hy, l', hl', rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨r, hr, l, hl, rfl⟩ := Submodule.mem_sup.1 hy
  -- l' = 0
  have hl'0 : l' = 0 := by
    by_contra hne
    obtain ⟨l₀, hl₀, hB0⟩ := hpair l' hl' hne
    have hl₀M : l₀ ∈ M' := hM (Submodule.mem_sup_right hl₀)
    have h0 := hM'.bil_eq_zero hB h2 hv hl₀M
    have hal : B a l₀ = 0 := by rw [hB]; exact hLA l₀ hl₀ a ha
    simp only [map_add, LinearMap.add_apply, hRad r hr, hLL l hl l₀ hl₀, hal, zero_add, add_zero] at h0
    exact hB0 h0
  subst hl'0
  -- a = 0
  have hrl : r + l ∈ M' := hM (Submodule.add_mem_sup hr hl)
  have ha' : a ∈ M' := by
    have := M'.sub_mem hv hrl
    simpa using this
  have haa := hM' a ha'
  have ha0 := hA a ha haa
  subst ha0
  simpa using Submodule.add_mem_sup hr hl

/-- **Algorithm 3.14, the shear** (Hanke 2013, p. 13), characteristic $2$: $Q_B(\vec v_i - c\,\vec v_n) = 0$ when
$c^2 = Q_B(\vec v_i)/Q_B(\vec v_n)$ (such $c$ exists over a finite field of characteristic $2$). -/
@[kb "hanke2013algorithms" "Algorithm 3.14, step 3, p. 13 (the shear)"]
theorem algorithm_3_14_shear (B : LinearMap.BilinForm K V) (hB : ∀ x y, B x y = B y x) (h2 : (2 : K) = 0)
    {vi vn : V} (hn : B vn vn ≠ 0) {c : K} (hc : c ^ 2 = B vi vi / B vn vn) : B (vi - c • vn) (vi - c • vn) = 0 := by
  rw [sub_eq_add_neg, remark_3_9_add B hB h2, ← neg_smul, remark_3_9_smul, neg_sq, hc, div_mul_cancel₀ _ hn]
  have : (2 : K) * B vi vi = 0 := by rw [h2, zero_mul]
  linear_combination this

/-- **Algorithm 3.14, maximality** (Hanke 2013, p. 13), characteristic $2$: if $R$ is in the radical, $Q_B(I) = 0$ and
$R + I + Ku = V$ for some $\vec u$ (with $Q_B(\vec u)\ne0$, or $\vec u = 0$ when $A = 0$), then $M = R + I$ is maximal
totally isotropic; it equals $\ker Q_B$ (`isMaxTotIso_kerQ`). -/
@[kb "hanke2013algorithms" "Algorithm 3.14, p. 13 (M = R + I is maximal totally isotropic)"]
theorem algorithm_3_14 (B : LinearMap.BilinForm K V) (hB : ∀ x y, B x y = B y x) (h2 : (2 : K) = 0)
    (R I : Submodule K V) (u : V) (hRad : ∀ r ∈ R, ∀ x, B r x = 0) (hI : IsTotIso B I)
    (hu : u ≠ 0 → B u u ≠ 0) (hsup : R ⊔ I ⊔ (K ∙ u) = ⊤) :
    IsMaxTotIso B (R ⊔ I) ∧ R ⊔ I = kerQ B hB h2 := by
  have hiso : IsTotIso B (R ⊔ I) := by
    intro x hx
    obtain ⟨r, hr, i, hi, rfl⟩ := Submodule.mem_sup.1 hx
    rw [remark_3_9_add B hB h2, hRad r hr, hI i hi, add_zero]
  have hker : R ⊔ I = kerQ B hB h2 := by
    refine le_antisymm (le_kerQ_of_isTotIso B hB h2 hiso) fun v hv => ?_
    have hvt : v ∈ R ⊔ I ⊔ (K ∙ u) := hsup ▸ Submodule.mem_top
    obtain ⟨x, hx, a, ha, rfl⟩ := Submodule.mem_sup.1 hvt
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 ha
    rw [mem_kerQ, remark_3_9_add B hB h2, hiso x hx, zero_add, remark_3_9_smul] at hv
    by_cases hu0 : u = 0
    · simpa [hu0] using hx
    · rcases mul_eq_zero.1 hv with h | h
      · rw [pow_eq_zero_iff two_ne_zero] at h
        simpa [h] using hx
      · exact absurd h (hu hu0)
  exact ⟨hker ▸ isMaxTotIso_kerQ B hB h2, hker⟩

end QuadFormsKB.Hanke2013Algorithms
