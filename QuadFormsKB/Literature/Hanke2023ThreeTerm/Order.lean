import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.Hanke2023ThreeTerm.Basic

/-!
# Saha–Hanke, three-term theta relations: the partial order on strongly primitive vectors

Source: R. Saha and J. Hanke, *On three-term linear relations for theta series of positive-definite
binary quadratic forms*, arXiv:2307.00747v1 (bib key `hanke2023threeterm`), §2–§3.

* Definition 2.4, Remarks 2.5, 2.6: the polyhedral cone $P(A,B)$, the description of $V$ as
  $P(A,B)$, its closure and its edges $E_1 = y^2$, $E_2 = x^2 + y^2$, $E_3 = x^2 + xy + y^2$.
* Definition 3.4, Lemma 3.5: the relation $\vec x \preceq \vec y$ iff $Q(\vec x) \le Q(\vec y)$
  for all $Q \in V$, and its explicit test through $E_1, E_2, E_3$.
* Remark 3.6, Lemma 3.7: it is a partial order on strongly primitive vectors (not on $\mathbb{Z}^2$).
* Definition 3.8, Lemmas 3.9, 3.10, 3.12: the minimal subset $\mathrm{MIN}(X)$.

Vectors are `ℤ × ℤ` with 0-based coordinates: $\vec x = (x_0, x_1)$ is `x.1, x.2` (the paper's
$(x_1, x_2)$).
-/

namespace QuadFormsKB.Hanke2023ThreeTerm

open QuadFormsKB QuadFormsKB.Siegel Topology Filter

/-! ### §2: the cone $V$ -/

/-- **Definition 2.4 (polyhedral cone $P(A,B)$).** For finite $A, B \subseteq \mathbb{R}^n$,
$P(A,B) = \{\vec x \in \mathbb{R}^n : \vec a \cdot \vec x \ge 0\ \forall \vec a \in A,\
\vec b \cdot \vec x > 0\ \forall \vec b \in B\}$, where $\cdot$ is the dot product
(`dotProduct`, `⬝ᵥ`). -/
@[kb "hanke2023threeterm" "§2, Definition 2.4, p. 3"]
def polyhedralCone {n : ℕ} (A B : Finset (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {x | (∀ a ∈ A, 0 ≤ a ⬝ᵥ x) ∧ ∀ b ∈ B, 0 < b ⬝ᵥ x}

/-- The coordinate vector $(q_{11}, q_{22}, q_{12}) \in \mathbb{R}^3$ of a form, as a function
`Fin 3 → ℝ` (0-based: coordinate $0$ is $q_{11}$, $1$ is $q_{22}$, $2$ is $q_{12}$). -/
def RForm.toVec (Q : RForm) : Fin 3 → ℝ := ![Q.1, Q.2.1, Q.2.2]

open scoped Classical in
/-- **Remark 2.5 ($V$ as a polyhedral cone).** $V = P(A,B)$ with
$A = \{(-1,1,0), (1,0,-1), (0,0,1)\}$ and $B = \{(1,0,0)\}$, under the identification
$Q \mapsto (q_{11}, q_{22}, q_{12})$ of Convention 2.1 (`RForm.toVec`). -/
@[kb "hanke2023threeterm" "§2, Remark 2.5, p. 4"]
theorem domainV_eq_polyhedralCone :
    domainV = RForm.toVec ⁻¹'
      polyhedralCone ({![-1, 1, 0], ![1, 0, -1], ![0, 0, 1]} : Finset (Fin 3 → ℝ))
        ({![1, 0, 0]} : Finset (Fin 3 → ℝ)) := by
  ext Q
  simp only [domainV, polyhedralCone, RForm.toVec, Set.mem_ofPred_eq, Set.mem_preimage,
    Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq, dotProduct,
    Fin.sum_univ_three]
  simp
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨by linarith, by linarith, h2⟩, h4⟩
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    exact ⟨by linarith, h3, by linarith, h4⟩

/-- **Remark 2.6, closure of $V$:** the closed cone
$\overline V = \{q_{22} - q_{11} \ge 0,\ q_{12} \ge 0,\ q_{11} - q_{12} \ge 0,\ q_{11} \ge 0\}$.
(`closure_domainV` shows it is the topological closure of `domainV`.) -/
@[kb "hanke2023threeterm" "§2, Remark 2.6, p. 4"]
def domainVbar : Set RForm :=
  {Q | 0 ≤ Q.2.1 - Q.1 ∧ 0 ≤ Q.2.2 ∧ 0 ≤ Q.1 - Q.2.2 ∧ 0 ≤ Q.1}

/-- **Edge $E_1(x,y) = y^2$** of $V$, as the triple $(0, 1, 0)$ (Remark 2.6). -/
def E1 : RForm := (0, 1, 0)
/-- **Edge $E_2(x,y) = x^2 + y^2$** of $V$, as the triple $(1, 1, 0)$ (Remark 2.6). -/
def E2 : RForm := (1, 1, 0)
/-- **Edge $E_3(x,y) = x^2 + xy + y^2$** of $V$, as the triple $(1, 1, 1)$ (Remark 2.6). -/
def E3 : RForm := (1, 1, 1)

@[simp] lemma E1_eval (v : ℤ × ℤ) : E1.eval v = (v.2 : ℝ) ^ 2 := by simp [RForm.eval, E1]
@[simp] lemma E2_eval (v : ℤ × ℤ) : E2.eval v = (v.1 : ℝ) ^ 2 + (v.2 : ℝ) ^ 2 := by
  simp [RForm.eval, E2]
@[simp] lemma E3_eval (v : ℤ × ℤ) :
    E3.eval v = (v.1 : ℝ) ^ 2 + (v.1 : ℝ) * v.2 + (v.2 : ℝ) ^ 2 := by simp [RForm.eval, E3]

lemma E2_mem : E2 ∈ domainV := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [E2]
lemma E3_mem : E3 ∈ domainV := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [E3]

lemma domainV_subset_bar : domainV ⊆ domainVbar := by
  rintro Q ⟨h1, h2, h3, h4⟩
  exact ⟨h1, h2, h3, h4.le⟩

/-- **Remark 2.6 (closure of $V$ and its edges).** The closed cone `domainVbar` is the closure of
`domainV` in $\mathbb{R}^3$. -/
@[kb "hanke2023threeterm" "§2, Remark 2.6, p. 4"]
theorem closure_domainV : closure domainV = domainVbar := by
  apply Set.Subset.antisymm
  · apply closure_minimal domainV_subset_bar
    have : domainVbar = {Q : RForm | 0 ≤ Q.2.1 - Q.1} ∩ ({Q : RForm | 0 ≤ Q.2.2} ∩
        ({Q : RForm | 0 ≤ Q.1 - Q.2.2} ∩ {Q : RForm | 0 ≤ Q.1})) := rfl
    rw [this]
    refine (isClosed_le continuous_const (by fun_prop)).inter
      ((isClosed_le continuous_const (by fun_prop)).inter
        ((isClosed_le continuous_const (by fun_prop)).inter
          (isClosed_le continuous_const (by fun_prop))))
  · intro Q hQ
    obtain ⟨h1, h2, h3, h4⟩ := hQ
    let f : ℝ → RForm := fun ε => (Q.1 + ε, Q.2.1 + ε, Q.2.2)
    have hf : Continuous f := by fun_prop
    have h0 : f 0 = Q := by simp [f]
    have ht : Tendsto f (𝓝[>] 0) (𝓝 Q) := by
      have := hf.tendsto 0
      rw [h0] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto ht ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : 0 < ε := hε
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [f] <;> linarith

/-- **Remark 2.6 (edges of $V$).** Every element of $\overline V$ is a non-negative combination
$\lambda_1 E_1 + \lambda_2 E_2 + \lambda_3 E_3$ of the three edges
$E_1 = (0,1,0)$, $E_2 = (1,1,0)$, $E_3 = (1,1,1)$ (here with
$\lambda_1 = q_{22} - q_{11}$, $\lambda_2 = q_{11} - q_{12}$, $\lambda_3 = q_{12}$). -/
@[kb "hanke2023threeterm" "§2, Remark 2.6, p. 4"]
theorem domainVbar_edges {Q : RForm} (hQ : Q ∈ domainVbar) :
    ∃ l₁ l₂ l₃ : ℝ, 0 ≤ l₁ ∧ 0 ≤ l₂ ∧ 0 ≤ l₃ ∧ Q = l₁ • E1 + l₂ • E2 + l₃ • E3 := by
  obtain ⟨h1, h2, h3, -⟩ := hQ
  refine ⟨Q.2.1 - Q.1, Q.1 - Q.2.2, Q.2.2, h1, h3, h2, ?_⟩
  ext <;> simp [E1, E2, E3]

/-- The decomposition of the values of a form along the edges. -/
lemma eval_decomp (Q : RForm) (v : ℤ × ℤ) :
    Q.eval v = (Q.2.1 - Q.1) * E1.eval v + (Q.1 - Q.2.2) * E2.eval v + Q.2.2 * E3.eval v := by
  rw [E1_eval, E2_eval, E3_eval]
  simp only [RForm.eval]
  ring

/-! ### §3.2: the relation $\preceq$ -/

/-- **Definition 3.4 (the relation $\vec x \preceq \vec y$).** For $\vec x, \vec y \in
\mathbb{Z}^2$: $Q(\vec x) \le Q(\vec y)$ for all $Q \in V$ (`domainV`). -/
@[kb "hanke2023threeterm" "§3.2, Definition 3.4, p. 5"]
def Preceq (x y : ℤ × ℤ) : Prop := ∀ Q ∈ domainV, RForm.eval Q x ≤ RForm.eval Q y

/-- **Lemma 3.5 (determining $\vec x \preceq \vec y$).** $\vec x \preceq \vec y$ iff
$E_i(\vec x) \le E_i(\vec y)$ for each $i \in \{1,2,3\}$ ($E_1 = y^2$, $E_2 = x^2+y^2$,
$E_3 = x^2 + xy + y^2$). -/
@[kb "hanke2023threeterm" "§3.2, Lemma 3.5, p. 5"]
theorem preceq_iff (x y : ℤ × ℤ) :
    Preceq x y ↔ E1.eval x ≤ E1.eval y ∧ E2.eval x ≤ E2.eval y ∧ E3.eval x ≤ E3.eval y := by
  constructor
  · intro h
    refine ⟨?_, h E2 E2_mem, h E3 E3_mem⟩
    have h1 : x.2 ^ 2 ≤ y.2 ^ 2 := by
      by_contra hlt
      have hlt : y.2 ^ 2 + 1 ≤ x.2 ^ 2 := by omega
      have hlt' : (y.2 : ℝ) ^ 2 + 1 ≤ (x.2 : ℝ) ^ 2 := by exact_mod_cast hlt
      have hy : (0 : ℝ) < (y.1 : ℝ) ^ 2 + 1 := by positivity
      set t : ℝ := 1 / ((y.1 : ℝ) ^ 2 + 1) with ht_def
      have ht : 0 < t := by positivity
      have ht1 : t ≤ 1 := by
        rw [ht_def, div_le_one hy]; nlinarith [sq_nonneg (y.1 : ℝ)]
      have hty : t * (y.1 : ℝ) ^ 2 < 1 := by
        rw [ht_def, one_div, inv_mul_eq_div, div_lt_one hy]; linarith
      have hmem : ((t, 1, 0) : RForm) ∈ domainV := by
        refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only <;> linarith
      have := h _ hmem
      simp only [RForm.eval] at this
      nlinarith [mul_nonneg ht.le (sq_nonneg (x.1 : ℝ))]
    simpa using (by exact_mod_cast h1 : (x.2 : ℝ) ^ 2 ≤ (y.2 : ℝ) ^ 2)
  · rintro ⟨h1, h2, h3⟩ Q hQ
    obtain ⟨q1, q2, q3, -⟩ := hQ
    rw [eval_decomp Q x, eval_decomp Q y]
    have a1 : 0 ≤ Q.2.1 - Q.1 := q1
    have a3 : 0 ≤ Q.1 - Q.2.2 := q3
    have a2 : 0 ≤ Q.2.2 := q2
    gcongr

/-- The test of Lemma 3.5 in integers: $\vec x \preceq \vec y$ iff
$x_1^2 \le y_1^2$, $x_0^2 + x_1^2 \le y_0^2 + y_1^2$ and
$x_0^2 + x_0 x_1 + x_1^2 \le y_0^2 + y_0 y_1 + y_1^2$ (0-based coordinates `.1`, `.2`). -/
theorem preceq_iff_int (x y : ℤ × ℤ) :
    Preceq x y ↔ x.2 ^ 2 ≤ y.2 ^ 2 ∧ x.1 ^ 2 + x.2 ^ 2 ≤ y.1 ^ 2 + y.2 ^ 2 ∧
      x.1 ^ 2 + x.1 * x.2 + x.2 ^ 2 ≤ y.1 ^ 2 + y.1 * y.2 + y.2 ^ 2 := by
  rw [preceq_iff]
  simp only [E1_eval, E2_eval, E3_eval]
  constructor
  · rintro ⟨a, b, c⟩
    exact ⟨by exact_mod_cast a, by exact_mod_cast b, by exact_mod_cast c⟩
  · rintro ⟨a, b, c⟩
    exact ⟨by exact_mod_cast a, by exact_mod_cast b, by exact_mod_cast c⟩

/-- **Remark 3.6 (failure of antisymmetry on $\mathbb{Z}^2$).** $\vec x \preceq -\vec x$ and
$-\vec x \preceq \vec x$ for every $\vec x \in \mathbb{Z}^2$. -/
@[kb "hanke2023threeterm" "§3.2, Remark 3.6, p. 5"]
theorem preceq_neg (x : ℤ × ℤ) : Preceq x (-x) ∧ Preceq (-x) x := by
  have : ∀ Q : RForm, Q.eval (-x) = Q.eval x := fun Q => by simp [RForm.eval]
  exact ⟨fun Q _ => (this Q).symm.le, fun Q _ => (this Q).le⟩

/-- Reflexivity of $\preceq$ (Lemma 3.7, 1); holds on all of $\mathbb{Z}^2$. -/
theorem Preceq.refl' (x : ℤ × ℤ) : Preceq x x := fun _ _ => le_rfl

/-- Transitivity of $\preceq$ (Lemma 3.7, 3); holds on all of $\mathbb{Z}^2$. -/
theorem Preceq.trans' {x y z : ℤ × ℤ} (h₁ : Preceq x y) (h₂ : Preceq y z) : Preceq x z :=
  fun Q hQ => (h₁ Q hQ).trans (h₂ Q hQ)

/-- Antisymmetry of $\preceq$ on strongly primitive vectors (Lemma 3.7, 2): if $\vec x, \vec y$
are strongly primitive, $\vec x \preceq \vec y$ and $\vec y \preceq \vec x$, then $\vec x = \vec y$.
(Only the sign condition of strong primitivity is used.) -/
theorem Preceq.antisymm' {x y : ℤ × ℤ} (hx : StronglyPrimitive x) (hy : StronglyPrimitive y)
    (hxy : Preceq x y) (hyx : Preceq y x) : x = y := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  obtain ⟨-, hx⟩ := hx
  obtain ⟨-, hy⟩ := hy
  simp only at hx hy
  obtain ⟨a1, a2, a3⟩ := (preceq_iff_int _ _).mp hxy
  obtain ⟨b1, b2, b3⟩ := (preceq_iff_int _ _).mp hyx
  simp only at a1 a2 a3 b1 b2 b3
  have e1 : x2 ^ 2 = y2 ^ 2 := le_antisymm a1 b1
  have e2 : x1 ^ 2 = y1 ^ 2 := by nlinarith
  have e3 : x1 * x2 = y1 * y2 := by nlinarith
  simp only [Prod.mk.injEq]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp e1 with h2 | h2 <;>
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp e2 with h1 | h1
  · exact ⟨h1, h2⟩
  · have : y1 * y2 = 0 := by rw [h1, h2] at e3; linarith
    rcases mul_eq_zero.mp this with h | h
    · exact ⟨by omega, h2⟩
    · exfalso; omega
  · have : y1 * y2 = 0 := by rw [h1, h2] at e3; linarith
    rcases mul_eq_zero.mp this with h | h
    · exfalso; omega
    · exact ⟨h1, by omega⟩
  · exfalso; omega

/-- **Lemma 3.7 (partial ordering on $\widetilde{\mathbb{Z}^2_*}$).** $\preceq$ is a partial order
(reflexive, transitive, antisymmetric) on the set of strongly primitive vectors. -/
@[kb "hanke2023threeterm" "§3.2, Lemma 3.7, p. 5"]
theorem preceq_isPartialOrder :
    IsPartialOrder {v : ℤ × ℤ // StronglyPrimitive v} (fun a b => Preceq a.1 b.1) where
  refl a := Preceq.refl' a.1
  trans _ _ _ h₁ h₂ := Preceq.trans' h₁ h₂
  antisymm a b h₁ h₂ := Subtype.ext (Preceq.antisymm' a.2 b.2 h₁ h₂)

/-! ### §3.3: the minimal subset -/

/-- **Definition 3.8 (minimal subset $\mathrm{MIN}(X)$).** For $X \subseteq \mathbb{Z}^2$,
$\mathrm{MIN}(X)$ is the set of $\vec x \in X$ such that no other element of $X$ lies below it:
$\vec y \not\preceq \vec x$ for every $\vec y \in X \setminus \{\vec x\}$. (In the source the
relation is written with the opposite symbol, $\vec x \not\succeq \vec y$, which is the same
condition.) -/
@[kb "hanke2023threeterm" "§3.3, Definition 3.8, p. 6"]
def MIN (X : Set (ℤ × ℤ)) : Set (ℤ × ℤ) :=
  {x | x ∈ X ∧ ∀ y ∈ X, y ≠ x → ¬ Preceq y x}

lemma MIN_subset (X : Set (ℤ × ℤ)) : MIN X ⊆ X := fun _ h => h.1

lemma slice_upper {X : Set (ℤ × ℤ)} {a : ℤ} {p q : ℤ × ℤ} (hp : p ∈ MIN X) (hq : q ∈ MIN X)
    (hp2 : p.2 = a) (hq2 : q.2 = a) (hpa : |a| ≤ p.1) (hpq : p.1 ≤ q.1) : p = q := by
  by_contra hne
  refine hq.2 p hp.1 hne ((preceq_iff_int _ _).mpr ?_)
  rw [hp2, hq2]
  have h0 : 0 ≤ q.1 + p.1 + a := by linarith [neg_abs_le a, abs_nonneg a]
  have h1 : 0 ≤ p.1 + q.1 := by linarith [abs_nonneg a]
  refine ⟨le_rfl, ?_, ?_⟩
  · nlinarith [mul_nonneg (sub_nonneg.2 hpq) h1]
  · nlinarith [mul_nonneg (sub_nonneg.2 hpq) h0]

lemma slice_lower {X : Set (ℤ × ℤ)} {a : ℤ} {p q : ℤ × ℤ} (hp : p ∈ MIN X) (hq : q ∈ MIN X)
    (hp2 : p.2 = a) (hq2 : q.2 = a) (hpa : p.1 ≤ -|a|) (hqa : q.1 ≤ -|a|) (hpq : p.1 ≤ q.1) :
    p = q := by
  by_contra hne
  refine hp.2 q hq.1 (Ne.symm hne) ((preceq_iff_int _ _).mpr ?_)
  rw [hp2, hq2]
  have h0 : p.1 + q.1 + a ≤ 0 := by linarith [le_abs_self a, abs_nonneg a]
  have h1 : p.1 + q.1 ≤ 0 := by linarith [abs_nonneg a]
  refine ⟨le_rfl, ?_, ?_⟩
  · nlinarith [mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 hpq) h1]
  · nlinarith [mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 hpq) h0]

/-- **Lemma 3.9.** For every $X \subseteq \mathbb{Z}^2$ and $a \in \mathbb{Z}$, the slice
$\mathrm{MIN}(X) \cap \{(x, y) : y = a\}$ is finite. (Here $y$ is the second coordinate `.2`.) -/
@[kb "hanke2023threeterm" "§3.3, Lemma 3.9, p. 6"]
theorem MIN_slice_finite (X : Set (ℤ × ℤ)) (a : ℤ) :
    {p : ℤ × ℤ | p ∈ MIN X ∧ p.2 = a}.Finite := by
  have hUs : {p : ℤ × ℤ | p ∈ MIN X ∧ p.2 = a ∧ |a| ≤ p.1}.Subsingleton := by
    intro p hp q hq
    rcases le_total p.1 q.1 with h | h
    · exact slice_upper hp.1 hq.1 hp.2.1 hq.2.1 hp.2.2 h
    · exact (slice_upper hq.1 hp.1 hq.2.1 hp.2.1 hq.2.2 h).symm
  have hLs : {p : ℤ × ℤ | p ∈ MIN X ∧ p.2 = a ∧ p.1 ≤ -|a|}.Subsingleton := by
    intro p hp q hq
    rcases le_total p.1 q.1 with h | h
    · exact slice_lower hp.1 hq.1 hp.2.1 hq.2.1 hp.2.2 hq.2.2 h
    · exact (slice_lower hq.1 hp.1 hq.2.1 hp.2.1 hq.2.2 hp.2.2 h).symm
  have hM : ((fun x : ℤ => (x, a)) '' Set.Icc (-|a|) |a|).Finite :=
    (Set.finite_Icc _ _).image _
  refine ((hUs.finite.union hLs.finite).union hM).subset ?_
  rintro ⟨p1, p2⟩ ⟨hp, hp2⟩
  simp only at hp2
  subst hp2
  by_cases h1 : |p2| ≤ p1
  · exact Or.inl (Or.inl ⟨hp, rfl, h1⟩)
  by_cases h2 : p1 ≤ -|p2|
  · exact Or.inl (Or.inr ⟨hp, rfl, h2⟩)
  push_neg at h1 h2
  exact Or.inr ⟨p1, ⟨by linarith, by linarith⟩, rfl⟩

lemma finite_sumSq_le (c : ℤ) : {p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 2 ≤ c}.Finite := by
  refine ((Set.finite_Icc (-c) c).prod (Set.finite_Icc (-c) c)).subset ?_
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp
  have a1 := Int.le_self_sq p.1
  have a2 := Int.le_self_sq (-p.1)
  have a3 := Int.le_self_sq p.2
  have a4 := Int.le_self_sq (-p.2)
  simp only [neg_sq] at a2 a4
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> nlinarith [sq_nonneg p.1, sq_nonneg p.2]

/-- **Lemma 3.10(1).** For every $X \subseteq \mathbb{Z}^2$, $\mathrm{MIN}(X)$ is finite. -/
@[kb "hanke2023threeterm" "§3.3, Lemma 3.10(1), p. 6"]
theorem MIN_finite (X : Set (ℤ × ℤ)) : (MIN X).Finite := by
  rcases (MIN X).eq_empty_or_nonempty with h | ⟨x0, hx0⟩
  · simp [h]
  set c : ℤ := (x0.1 ^ 2 + x0.2 ^ 2) + 2 * (x0.1 ^ 2 + x0.1 * x0.2 + x0.2 ^ 2) with hc
  have hfin : (({x0} : Set (ℤ × ℤ)) ∪ {p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 2 ≤ c} ∪
      ⋃ a ∈ Set.Icc (-|x0.2|) |x0.2|, {p : ℤ × ℤ | p ∈ MIN X ∧ p.2 = a}).Finite :=
    ((Set.finite_singleton _).union (finite_sumSq_le c)).union
      ((Set.finite_Icc _ _).biUnion fun a _ => MIN_slice_finite X a)
  refine hfin.subset ?_
  intro p hp
  by_cases hpx : p = x0
  · exact Or.inl (Or.inl hpx)
  have hn := hp.2 x0 hx0.1 (Ne.symm hpx)
  rw [preceq_iff_int] at hn
  have hcase : p.2 ^ 2 < x0.2 ^ 2 ∨ p.1 ^ 2 + p.2 ^ 2 < x0.1 ^ 2 + x0.2 ^ 2 ∨
      p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 < x0.1 ^ 2 + x0.1 * x0.2 + x0.2 ^ 2 := by
    by_contra hcon
    simp only [not_or, not_lt] at hcon
    exact hn ⟨hcon.1, hcon.2.1, hcon.2.2⟩
  rcases hcase with h | h | h
  · refine Or.inr ?_
    simp only [Set.mem_iUnion]
    refine ⟨p.2, ?_, hp, rfl⟩
    have := abs_lt.mp (sq_lt_sq.mp h)
    exact ⟨this.1.le, this.2.le⟩
  · refine Or.inl (Or.inr ?_)
    show p.1 ^ 2 + p.2 ^ 2 ≤ c
    nlinarith [sq_nonneg (x0.1 + x0.2), sq_nonneg x0.1, sq_nonneg x0.2]
  · refine Or.inl (Or.inr ?_)
    show p.1 ^ 2 + p.2 ^ 2 ≤ c
    nlinarith [sq_nonneg (p.1 + p.2), sq_nonneg p.1, sq_nonneg p.2, sq_nonneg (x0.1 + x0.2),
      sq_nonneg x0.1, sq_nonneg x0.2]

/-- Well-founded descent: a non-empty set of strongly primitive vectors has an element
$\vec v$ with $\vec y \preceq \vec v \Rightarrow \vec y = \vec v$ for all $\vec y$ in the set. -/
lemma exists_preceq_minimal {X : Set (ℤ × ℤ)} (hX : ∀ v ∈ X, StronglyPrimitive v)
    (hne : X.Nonempty) : ∃ v ∈ X, ∀ y ∈ X, Preceq y v → y = v := by
  let s : ℤ × ℤ → ℤ := fun v => v.2 ^ 2 + (v.1 ^ 2 + v.2 ^ 2) +
    (v.1 ^ 2 + v.1 * v.2 + v.2 ^ 2)
  have hs0 : ∀ v, 0 ≤ s v := fun v => by
    simp only [s]; nlinarith [sq_nonneg (v.1 + v.2), sq_nonneg v.1, sq_nonneg v.2]
  let f : ℤ × ℤ → ℕ := fun v => (s v).natAbs
  obtain ⟨v, hv, hmin⟩ := (InvImage.wf f wellFounded_lt).has_min X hne
  refine ⟨v, hv, fun y hy hyv => ?_⟩
  by_contra hne'
  have hlt : s y < s v := by
    by_contra hge
    push_neg at hge
    obtain ⟨a, b, c⟩ := (preceq_iff_int _ _).mp hyv
    have hv' : Preceq v y := by
      rw [preceq_iff_int]
      simp only [s] at hge
      refine ⟨by linarith, by linarith, by linarith⟩
    exact hne' (Preceq.antisymm' (hX y hy) (hX v hv) hyv hv')
  have : f y < f v := Int.natAbs_lt_natAbs_of_nonneg_of_lt (hs0 y) hlt
  exact hmin y hy this

/-- **Lemma 3.10(2).** If $X \subseteq \widetilde{\mathbb{Z}^2_*}$ (strongly primitive vectors) is
non-empty, then $\mathrm{MIN}(X) \ne \emptyset$. -/
@[kb "hanke2023threeterm" "§3.3, Lemma 3.10(2), p. 6"]
theorem MIN_nonempty {X : Set (ℤ × ℤ)} (hX : ∀ v ∈ X, StronglyPrimitive v) (hne : X.Nonempty) :
    (MIN X).Nonempty := by
  obtain ⟨v, hv, h⟩ := exists_preceq_minimal hX hne
  exact ⟨v, hv, fun y hy hne' hyv => hne' (h y hy hyv)⟩

/-- **Lemma 3.10(3).** Let $X \subseteq \widetilde{\mathbb{Z}^2_*}$ and $W \subseteq
\widetilde{\mathbb{Z}^2_*}$ (strongly primitive vectors), and suppose there is a non-empty
auxiliary set $Y_W$ with $Y_W \subseteq X$ and
$W \supseteq \{\vec x \in X : \vec y \not\preceq \vec x \text{ for all } \vec y \in Y_W\} \cup Y_W$.
Then $\mathrm{MIN}(X) = \mathrm{MIN}(X \cap W)$.
(Reading note: the source's relation symbol in the displayed set is lost in the text extraction;
we read it as "$\vec x \not\succeq \vec y$", i.e. $\vec y \not\preceq \vec x$, the only reading
consistent with Lemma 3.10(4).) -/
@[kb "hanke2023threeterm" "§3.3, Lemma 3.10(3), p. 6"]
theorem MIN_eq_MIN_inter {X W Y : Set (ℤ × ℤ)} (hW : ∀ v ∈ W, StronglyPrimitive v)
    (hY : Y.Nonempty) (hYX : Y ⊆ X) (hX : ∀ v ∈ X, StronglyPrimitive v)
    (hWsup : {x | x ∈ X ∧ ∀ y ∈ Y, ¬ Preceq y x} ∪ Y ⊆ W) :
    MIN X = MIN (X ∩ W) := by
  have _ := hW
  have _ := hY
  ext x
  constructor
  · intro hx
    have hxW : x ∈ W := by
      by_cases hxY : x ∈ Y
      · exact hWsup (Or.inr hxY)
      · refine hWsup (Or.inl ⟨hx.1, fun y hy => ?_⟩)
        exact hx.2 y (hYX hy) (fun h => hxY (h ▸ hy))
    exact ⟨⟨hx.1, hxW⟩, fun y hy => hx.2 y hy.1⟩
  · intro hx
    refine ⟨hx.1.1, fun y hy hne hyx => ?_⟩
    by_cases hyW : y ∈ W
    · exact hx.2 y ⟨hy, hyW⟩ hne hyx
    · have hex : ∃ y' ∈ Y, Preceq y' y := by
        by_contra hcon
        push_neg at hcon
        exact hyW (hWsup (Or.inl ⟨hy, hcon⟩))
      obtain ⟨y', hy'Y, hy'y⟩ := hex
      have hy'x : Preceq y' x := hy'y.trans' hyx
      by_cases hyx' : y' = x
      · subst hyx'
        exact hne (Preceq.antisymm' (hX _ hy) (hX _ (hYX hy'Y)) hyx hy'y)
      · exact hx.2 y' ⟨hYX hy'Y, hWsup (Or.inr hy'Y)⟩ hyx' hy'x

/-- **The set $W_{0,a}$ of Lemma 3.10(4).**
$W_{0,a} = \{\vec x \in \widetilde{\mathbb{Z}^2_*} : (a,1) \not\preceq \vec x\} \cup \{(a,1)\}$
(source: $\vec x \not\succeq (a, 1)$). -/
@[kb "hanke2023threeterm" "§3.3, Lemma 3.10(4), p. 6"]
def W0 (a : ℤ) : Set (ℤ × ℤ) :=
  {x | StronglyPrimitive x ∧ ¬ Preceq (a, 1) x} ∪ {(a, 1)}

lemma stronglyPrimitive_a_one (a : ℤ) : StronglyPrimitive (a, 1) := by
  refine ⟨?_, Or.inl one_pos⟩
  simp

/-- **Lemma 3.10(4i).** If $(a, 1) \in X \subseteq \widetilde{\mathbb{Z}^2_*}$, then
$\mathrm{MIN}(X) = \mathrm{MIN}(X \cap W_{0,a})$. -/
@[kb "hanke2023threeterm" "§3.3, Lemma 3.10(4i), p. 6"]
theorem MIN_eq_MIN_inter_W0 {X : Set (ℤ × ℤ)} {a : ℤ} (hX : ∀ v ∈ X, StronglyPrimitive v)
    (ha : (a, 1) ∈ X) : MIN X = MIN (X ∩ W0 a) := by
  refine MIN_eq_MIN_inter (Y := {(a, 1)}) ?_ ⟨_, rfl⟩ (by simpa using ha) hX ?_
  · rintro v (h | h)
    · exact h.1
    · rw [Set.mem_singleton_iff.mp h]; exact stronglyPrimitive_a_one a
  · rintro x (⟨hxX, hx⟩ | hx)
    · exact Or.inl ⟨hX x hxX, hx (a, 1) rfl⟩
    · exact Or.inr hx

/-- The sup norm $\|(x,y)\|_\infty = \max\{|x|, |y|\}$ on $\mathbb{Z}^2$. -/
def supNorm (v : ℤ × ℤ) : ℤ := max |v.1| |v.2|

/-- **Lemma 3.10(4ii).** $W_{0,a} \subseteq \{\vec x \in \widetilde{\mathbb{Z}^2_*} :
\|\vec x\|_\infty \le \sqrt{2(a^2 + \max(a,0) + 1)}\}$. -/
@[kb "hanke2023threeterm" "§3.3, Lemma 3.10(4ii), p. 6"]
theorem W0_subset (a : ℤ) :
    W0 a ⊆ {x | StronglyPrimitive x ∧
      (supNorm x : ℝ) ≤ Real.sqrt (2 * ((a : ℝ) ^ 2 + max (a : ℝ) 0 + 1))} := by
  have hB0 : (0 : ℝ) ≤ 2 * ((a : ℝ) ^ 2 + max (a : ℝ) 0 + 1) := by
    have := le_max_right (a : ℝ) 0
    positivity
  rintro x (⟨hsp, hx⟩ | hx)
  · refine ⟨hsp, ?_⟩
    by_contra hlt
    push_neg at hlt
    have hsq : 2 * ((a : ℝ) ^ 2 + max (a : ℝ) 0 + 1) < (supNorm x : ℝ) ^ 2 := by
      have h0 : 0 < (supNorm x : ℝ) := lt_of_le_of_lt (Real.sqrt_nonneg _) hlt
      exact (Real.sqrt_lt' h0).mp hlt
    -- integer form of the bound: 2(a² + max a 0 + 1) < (supNorm x)²
    have hsqZ : 2 * (a ^ 2 + max a 0 + 1) < (supNorm x) ^ 2 := by
      have : ((2 * (a ^ 2 + max a 0 + 1) : ℤ) : ℝ) < (((supNorm x) ^ 2 : ℤ) : ℝ) := by
        push_cast; exact hsq
      exact_mod_cast this
    apply hx
    obtain ⟨hg0, hy⟩ := hsp
    rw [preceq_iff_int]
    simp only
    have hm : a ≤ max a 0 := le_max_left a 0
    have hm0 : 0 ≤ max a 0 := le_max_right a 0
    unfold supNorm at hsq hsqZ
    have key : x.1 ^ 2 > 2 * (a ^ 2 + max a 0 + 1) ∨ x.2 ^ 2 > 2 * (a ^ 2 + max a 0 + 1) := by
      rcases max_cases |x.1| |x.2| with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] at hsqZ
      · left; rwa [sq_abs] at hsqZ
      · right; rwa [sq_abs] at hsqZ
    rcases hy with hy | ⟨hy0, hx1⟩
    · have hy1 : 1 ≤ x.2 := hy
      have hy2 : 1 ≤ x.2 ^ 2 := by nlinarith
      refine ⟨by simpa using hy2, ?_, ?_⟩
      · rcases key with k | k <;> nlinarith [sq_nonneg x.1, sq_nonneg x.2]
      · rcases key with k | k <;>
          nlinarith [sq_nonneg (x.1 + 2 * x.2), sq_nonneg (2 * x.1 + x.2), sq_nonneg x.1,
            sq_nonneg x.2]
    · exfalso
      have hg := hg0
      have h1 : x.1 = 1 := by
        have : Int.gcd x.1 x.2 = 1 := hg
        rw [hy0] at this
        simp at this
        omega
      rcases key with k | k
      · rw [h1] at k; nlinarith
      · rw [hy0] at k; nlinarith
  · rw [Set.mem_singleton_iff.mp hx]
    refine ⟨stronglyPrimitive_a_one a, ?_⟩
    simp only [supNorm]
    rw [Int.cast_max, Int.cast_abs, Int.cast_abs]
    have h1 : |(a : ℝ)| ≤ Real.sqrt (2 * ((a : ℝ) ^ 2 + max (a : ℝ) 0 + 1)) := by
      apply Real.le_sqrt_of_sq_le
      rw [sq_abs]; nlinarith [le_max_right (a : ℝ) 0]
    have h2 : |((1 : ℤ) : ℝ)| ≤ Real.sqrt (2 * ((a : ℝ) ^ 2 + max (a : ℝ) 0 + 1)) := by
      apply Real.le_sqrt_of_sq_le
      simp; nlinarith [le_max_right (a : ℝ) 0, sq_nonneg (a : ℝ)]
    exact max_le h1 h2

/-! ### Lemma 3.12 -/

/-- For $Q \in V$: $Q(\vec v) \ge \tfrac{q_{11}}{2}(v_0^2 + v_1^2)$. -/
lemma eval_ge {Q : RForm} (hQ : Q ∈ domainV) (v : ℤ × ℤ) :
    Q.1 / 2 * ((v.1 : ℝ) ^ 2 + (v.2 : ℝ) ^ 2) ≤ Q.eval v := by
  obtain ⟨h1, h2, h3, h4⟩ := hQ
  rw [eval_decomp]
  simp only [E1_eval, E2_eval, E3_eval]
  have he3 : ((v.1 : ℝ) ^ 2 + (v.2 : ℝ) ^ 2) / 2 ≤
      (v.1 : ℝ) ^ 2 + (v.1 : ℝ) * v.2 + (v.2 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((v.1 : ℝ) + v.2)]
  have he2 : 0 ≤ (v.1 : ℝ) ^ 2 + (v.2 : ℝ) ^ 2 := by positivity
  nlinarith [mul_nonneg h1 (sq_nonneg (v.2 : ℝ)), mul_nonneg h3 he2,
    mul_nonneg h2 (sub_nonneg.mpr he3)]

/-- A form $Q \in V$ attains its minimum over any non-empty set of integer vectors. -/
lemma exists_min_eval {Q : RForm} (hQ : Q ∈ domainV) {X : Set (ℤ × ℤ)} (hne : X.Nonempty) :
    ∃ z ∈ X, ∀ w ∈ X, Q.eval z ≤ Q.eval w := by
  obtain ⟨x0, hx0⟩ := hne
  have hq : 0 < Q.1 := hQ.2.2.2
  set r : ℝ := 2 * Q.eval x0 / Q.1 with hr
  have hfin : {v ∈ X | Q.eval v ≤ Q.eval x0}.Finite := by
    refine (finite_sumSq_le ⌈r⌉).subset ?_
    rintro v ⟨-, hv⟩
    have h := eval_ge hQ v
    have h' : (v.1 : ℝ) ^ 2 + (v.2 : ℝ) ^ 2 ≤ r := by
      rw [hr, le_div_iff₀ hq]; nlinarith
    have h'' : ((v.1 ^ 2 + v.2 ^ 2 : ℤ) : ℝ) ≤ r := by push_cast; exact h'
    exact Int.cast_le.mp (h''.trans (Int.le_ceil r))
  obtain ⟨z, ⟨hzX, hz⟩, hmin⟩ := Set.exists_min_image _ (RForm.eval Q) hfin ⟨x0, hx0, le_rfl⟩
  refine ⟨z, hzX, fun w hw => ?_⟩
  by_cases hwle : Q.eval w ≤ Q.eval x0
  · exact hmin w ⟨hw, hwle⟩
  · push_neg at hwle; exact hz.trans hwle.le

/-- **Lemma 3.12 (MIN attains minimum values).** Let $Q \in V$ and let $X$ be a non-empty set of
strongly primitive vectors. Then $Q$ attains a minimum $m$ on $X$, and the same value $m$ is the
minimum of $Q$ on $\mathrm{MIN}(X)$: $\min Q(\mathrm{MIN}(X)) = \min Q(X)$.

*Deviation:* the source states this for arbitrary $X \subseteq \mathbb{Z}^2$, but then it is false
(for $X = \{(1,0), (-1,0)\}$, each element lies below the other, so $\mathrm{MIN}(X) = \emptyset$
by Definition 3.8); we assume, as in Lemma 3.10(2), that $X$ is a non-empty set of strongly
primitive vectors. -/
@[kb "hanke2023threeterm" "§3.3, Lemma 3.12, p. 7"]
theorem MIN_attains_min {X : Set (ℤ × ℤ)} (hX : ∀ v ∈ X, StronglyPrimitive v)
    (hne : X.Nonempty) {Q : RForm} (hQ : Q ∈ domainV) :
    ∃ m : ℝ, IsLeast (RForm.eval Q '' X) m ∧ IsLeast (RForm.eval Q '' MIN X) m := by
  obtain ⟨z, hzX, hz⟩ := exists_min_eval hQ hne
  set Xm : Set (ℤ × ℤ) := {v | v ∈ X ∧ Q.eval v = Q.eval z} with hXm
  obtain ⟨v, hv, hvmin⟩ := exists_preceq_minimal (X := Xm) (fun v hv => hX v hv.1) ⟨z, hzX, rfl⟩
  have hvMIN : v ∈ MIN X := by
    refine ⟨hv.1, fun y hy hne' hyv => hne' ?_⟩
    have h1 : Q.eval y ≤ Q.eval v := hyv Q hQ
    have h2 : Q.eval z ≤ Q.eval y := hz y hy
    exact hvmin y ⟨hy, by rw [hv.2] at h1; exact le_antisymm h1 h2⟩ hyv
  refine ⟨Q.eval z, ⟨⟨z, hzX, rfl⟩, ?_⟩, ⟨⟨v, hvMIN, hv.2⟩, ?_⟩⟩
  · rintro _ ⟨w, hw, rfl⟩; exact hz w hw
  · rintro _ ⟨w, hw, rfl⟩; exact hz w hw.1

end QuadFormsKB.Hanke2023ThreeTerm
