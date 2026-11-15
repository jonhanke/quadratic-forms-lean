/-
# Chenevier–Lannes, §3.4.1–§3.4.2: heights, regular vectors and Borcherds' inequalities

Source: Chenevier–Lannes 2019 (`chenevierlannes2019`), §3.4.1, the definitions of regular and $d$-regular vectors before
Scholium 3.4.1.4, p. 64; §3.4.2, the paragraph on Weyl vectors, p. 65, Proposition 3.4.2.8 (a), pp. 67–68,
Proposition 3.4.2.9 (Borcherds), pp. 68–69, Theorem 3.4.2.10 (a), p. 69, and Proposition 3.4.2.16, p. 73. Printed page
numbers.

**Layer.** As in `Wave4/WeylVectors.lean`: a lattice is an integral form $Q = q_L$ on $L = \mathbb{Z}^n$, the
inner product is $x \cdot y$ = `bQ Q x y` on $V = \mathbb{Q}^n$ (`bZ` on $L$), the roots are the $\alpha \in L$ with
$q(\alpha) = 1$, a chamber is given by a vector $\xi$ orthogonal to no root, with positive roots
$R^+ = \{\alpha : \alpha \cdot \xi > 0\}$ (`posRoots Q ξ`), and the Weyl vector of that chamber is $\rho$ with
$2\rho = \sum_{\alpha \in R^+} \alpha$.

**The height function.** The book (p. 68) uses Bourbaki, Chap. VI, §1, Théorème 3 and Proposition 31 for the
height $H(\beta) = \beta \cdot \rho$ of a positive root: $1 \le H(\beta) \le h - 1$, and $H(\beta) = 1$ for the simple
roots. Here these are **proved** without the theory of bases: $\rho \cdot \alpha \ge 1$ for $\alpha \in R^+$ by the
injection $\beta \mapsto \beta + \alpha$ from $\{\beta \in R^+ : \beta \cdot \alpha = -1\}$ to
$\{\beta \in R^+ : \beta \cdot \alpha = 1\}$ (`one_le_weyl_dot`); a positive root with least $\alpha \cdot \xi$ has
$\rho \cdot \alpha = 1$ (`exists_weyl_dot_eq_one`; it is simple); and $\rho \cdot \alpha \le h - 1$ for every root from
Borcherds' identity (Proposition 3.4.2.2 (b)) at $x = \alpha$ (`weyl_dot_le`).

**Proves.**
- Unconditional (any positive definite integral form, any $n$): `one_le_weyl_dot`, `exists_weyl_dot_eq_one`,
  `weyl_isRegular` ($\rho$ is regular).
- **Conditional** on `VenkovRootSum 24` (Proposition 2.3.2; as in wave 4): `weyl_dot_le`, `prop_3_4_2_8_a`
  (Proposition 3.4.2.8 (a): $\rho \in L$ is primitive and $h$-regular), `prop_3_4_2_9_a`, `prop_3_4_2_9_b`,
  `prop_3_4_2_9_c` (Proposition 3.4.2.9, Borcherds; (c) as (i) ⇔ (ii) with $\Pi$ described by $\alpha \cdot \xi \in
  \{0, 1\}$ for $\alpha \in R^+$).
- **Conditional** on `VenkovRootSum 24` and `WeylVectorNorm` (Proposition 3.4.2.5): `prop_3_4_2_9_b_norm`
  ($q(\rho - h\xi) \ge h(h + 1)$), `holyConstructions_a` (Theorem 3.4.2.10 (a) in full: $\rho$ is $d$-primitive and
  isotropic mod $d$ for $d = h, h + 1$; wave 4 had only the isotropy), `prop_3_4_2_16`
  ($q(\rho - (h + 1)x) \ge (h + 1)(h + 2)$ for $x \in L$ nonzero).
-/
import QuadFormsKB.Literature.ChenevierLannes.Wave4.Statements

open Matrix

namespace QuadFormsKB.ChenevierLannes

open QuadFormsKB.Siegel QuadFormsKB.Siegel.Kneser

variable {n : ℕ}

/-! ### Regular and $d$-regular vectors -/

/-- **Regular vectors** (Chenevier–Lannes, §3.4.1, p. 64): $x \in V$ is regular if $\alpha \cdot x \ne 0$ for every
root $\alpha$ of $L$ (that is, $x$ lies in a chamber). -/
@[kb "chenevierlannes2019" "§3.4.1, p. 64 (regular vectors)"]
def IsRegularVec (Q : QuadForm ℤ n) (x : Fin n → ℚ) : Prop :=
  ∀ α ∈ rootSet Q, bQ Q (cv α) x ≠ 0

/-- **$d$-regular vectors** (Chenevier–Lannes, §3.4.1, p. 64): for an integer $d \ge 1$, $x \in V$ is $d$-regular if
$\alpha \cdot x \notin d\mathbb{Z}$ for every root $\alpha$ of $L$ (that is, $\frac1d x$ lies in an alcove). -/
@[kb "chenevierlannes2019" "§3.4.1, p. 64 (d-regular vectors)"]
def IsDRegular (Q : QuadForm ℤ n) (d : ℕ) (x : Fin n → ℚ) : Prop :=
  ∀ α ∈ rootSet Q, ∀ k : ℤ, bQ Q (cv α) x ≠ (d : ℚ) * k

/-- **Primitive vectors** of $L = \mathbb{Z}^n$ (Chenevier–Lannes, §3.1, p. 47): $u \ne 0$ and $u = k y$ with
$k \in \mathbb{Z}$, $y \in L$ forces $k = \pm 1$. -/
def IsPrimitiveVec (u : Fin n → ℤ) : Prop := u ≠ 0 ∧ ∀ (k : ℤ) (y : Fin n → ℤ), u = k • y → IsUnit k

/-! ### Inner products of two roots -/

/-- For roots $\alpha \ne \beta$, $\alpha \cdot \beta \le 1$ (positive definiteness: $q(\alpha - \beta) = 2 - \alpha
\cdot \beta > 0$). -/
theorem root_bZ_le_one {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q) {α β : Fin n → ℤ} (hα : α ∈ rootSet Q)
    (hβ : β ∈ rootSet Q) (hne : α ≠ β) : bZ Q α β ≤ 1 := by
  have hα1 : Q.eval α = 1 := hα
  have hβ1 : Q.eval β = 1 := hβ
  have e := eval_add_smulZ Q α β (-1)
  have hpos := hQ (α + (-1 : ℤ) • β) (by
    rw [neg_one_smul, ← sub_eq_add_neg]; exact sub_ne_zero.mpr hne)
  rw [e, hα1, hβ1] at hpos
  linarith

/-- For roots $\alpha \ne -\beta$, $\alpha \cdot \beta \ge -1$. -/
theorem neg_one_le_root_bZ {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q) {α β : Fin n → ℤ} (hα : α ∈ rootSet Q)
    (hβ : β ∈ rootSet Q) (hne : α ≠ -β) : -1 ≤ bZ Q α β := by
  have h := root_bZ_le_one hQ hα (neg_mem_rootSet hβ) hne
  have : bZ Q α (-β) = -bZ Q α β := by rw [bZ_comm, bZ_neg_left, bZ_comm]
  linarith

/-- If $\alpha, \beta$ are roots with $\alpha \cdot \beta = -1$, then $\alpha + \beta$ is a root. -/
theorem add_mem_rootSet {Q : QuadForm ℤ n} {α β : Fin n → ℤ} (hα : α ∈ rootSet Q) (hβ : β ∈ rootSet Q)
    (h : bZ Q α β = -1) : α + β ∈ rootSet Q := by
  have hα1 : Q.eval α = 1 := hα
  have hβ1 : Q.eval β = 1 := hβ
  have e := eval_add_smulZ Q α β 1
  rw [one_smul, hα1, hβ1, h] at e
  show Q.eval (α + β) = 1
  rw [e]; norm_num

/-- If $\alpha, \beta$ are roots with $\alpha \cdot \beta = 1$, then $\alpha - \beta$ is a root. -/
theorem sub_mem_rootSet {Q : QuadForm ℤ n} {α β : Fin n → ℤ} (hα : α ∈ rootSet Q) (hβ : β ∈ rootSet Q)
    (h : bZ Q α β = 1) : α - β ∈ rootSet Q := by
  have h' : bZ Q α (-β) = -1 := by rw [bZ_comm, bZ_neg_left, bZ_comm, h]
  have := add_mem_rootSet hα (neg_mem_rootSet hβ) h'
  rwa [← sub_eq_add_neg] at this

theorem bZ_root_self {Q : QuadForm ℤ n} {α : Fin n → ℤ} (hα : α ∈ rootSet Q) : bZ Q α α = 2 := by
  have hα1 : Q.eval α = 1 := hα
  rw [bZ_self, hα1]; norm_num

/-! ### Heights of positive roots -/

section Heights

variable {Q : QuadForm ℤ n} {ξ : Fin n → ℚ}

theorem mem_posRoots {hQ : IntQF.PosDef Q} {α : Fin n → ℤ} :
    α ∈ posRoots Q ξ ↔ α ∈ rootSet Q ∧ 0 < bQ Q (cv α) ξ := by
  simp [posRoots, mem_rootFin hQ]

/-- $2\,\rho \cdot \alpha = \sum_{\beta \in R^+} \beta \cdot \alpha$. -/
theorem two_weyl_dot {ρ : Fin n → ℚ} (hρ : (2 : ℚ) • ρ = ∑ β ∈ posRoots Q ξ, cv β) (α : Fin n → ℤ) :
    2 * bQ Q ρ (cv α) = ((∑ β ∈ posRoots Q ξ, bZ Q β α : ℤ) : ℚ) := by
  rw [← bQ_smul_left, hρ, bQ_sum_left]
  push_cast
  exact Finset.sum_congr rfl fun β _ => bQ_cv Q β α

/-- For $\alpha \in R^+$: the sum $\sum_{\beta \in R^+} \beta \cdot \alpha$ equals
$2 + \#\{\beta \in R^+ : \beta \cdot \alpha = 1\} - \#\{\beta \in R^+ : \beta \cdot \alpha = -1\}$. -/
theorem sum_bZ_posRoots (hQ : IntQF.PosDef Q) (hξ : ∀ α ∈ rootSet Q, bQ Q (cv α) ξ ≠ 0) {α : Fin n → ℤ}
    (hα : α ∈ posRoots Q ξ) :
    ∑ β ∈ posRoots Q ξ, bZ Q β α = 2 + ((posRoots Q ξ).filter fun β => bZ Q β α = 1).card -
      ((posRoots Q ξ).filter fun β => bZ Q β α = -1).card := by
  classical
  have hαR := ((mem_posRoots (hQ := hQ)).mp hα)
  have hpt : ∀ β ∈ posRoots Q ξ, bZ Q β α =
      (if β = α then 2 else 0) + (if bZ Q β α = 1 then 1 else 0) - (if bZ Q β α = -1 then 1 else 0) := by
    intro β hβ
    have hβR := (mem_posRoots (hQ := hQ)).mp hβ
    by_cases hb : β = α
    · subst hb; rw [bZ_root_self hβR.1]; simp
    · have hneg : β ≠ -α := by
        rintro rfl
        rw [cv_neg', bQ_neg_left] at hβR
        linarith [hβR.2, hαR.2]
      have h1 := root_bZ_le_one hQ hβR.1 hαR.1 hb
      have h2 := neg_one_le_root_bZ hQ hβR.1 hαR.1 hneg
      rcases (by omega : bZ Q β α = -1 ∨ bZ Q β α = 0 ∨ bZ Q β α = 1) with h | h | h <;> simp [hb, h]
  rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq' _ _,
    if_pos hα, Finset.sum_boole, Finset.sum_boole]

/-- The injection $\beta \mapsto \beta + \alpha$ of $\{\beta \in R^+ : \beta \cdot \alpha = -1\}$ into
$\{\beta \in R^+ : \beta \cdot \alpha = 1\}$, for $\alpha \in R^+$. -/
theorem card_neg_le_card_pos (hQ : IntQF.PosDef Q) {α : Fin n → ℤ} (hα : α ∈ posRoots Q ξ) :
    ((posRoots Q ξ).filter fun β => bZ Q β α = -1).card ≤
      ((posRoots Q ξ).filter fun β => bZ Q β α = 1).card := by
  have hαR := (mem_posRoots (hQ := hQ)).mp hα
  refine Finset.card_le_card_of_injOn (fun β => β + α) ?_ ?_
  · intro β hβ
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hβ ⊢
    have hβR := (mem_posRoots (hQ := hQ)).mp hβ.1
    refine ⟨(mem_posRoots (hQ := hQ)).mpr ⟨add_mem_rootSet hβR.1 hαR.1 hβ.2, ?_⟩, ?_⟩
    · rw [cv_add, bQ_add_left]; linarith [hβR.2, hαR.2]
    · rw [bZ_add_left, hβ.2, bZ_root_self hαR.1]; norm_num
  · intro β _ γ _ h
    simpa using h

/-- **Heights are positive** (Chenevier–Lannes, p. 68, the property $H(\beta) \ge 1$; the book cites Bourbaki,
Chap. VI, §1, Théorème 3): for a positive definite integral form, a chamber $\xi$ and its Weyl vector $\rho$
($2\rho = \sum_{\beta \in R^+} \beta$), every positive root $\alpha$ has $\rho \cdot \alpha \ge 1$. Unconditional.
*Proof.* $2\rho \cdot \alpha = 2 + \#\{\beta \in R^+ : \beta \cdot \alpha = 1\} - \#\{\beta \in R^+ : \beta \cdot \alpha
= -1\}$ (the other inner products of roots are $0$, and $\pm 2$ only for $\beta = \pm\alpha$), and
$\beta \mapsto \beta + \alpha$ injects the second set into the first. -/
@[kb "chenevierlannes2019" "§3.4.2, p. 68 (heights: H(β) ≥ 1)"]
theorem one_le_weyl_dot (hQ : IntQF.PosDef Q) (hξ : ∀ α ∈ rootSet Q, bQ Q (cv α) ξ ≠ 0) {ρ : Fin n → ℚ}
    (hρ : (2 : ℚ) • ρ = ∑ β ∈ posRoots Q ξ, cv β) {α : Fin n → ℤ} (hα : α ∈ posRoots Q ξ) :
    1 ≤ bQ Q ρ (cv α) := by
  have h2 := two_weyl_dot hρ α
  rw [sum_bZ_posRoots hQ hξ hα] at h2
  have hc := card_neg_le_card_pos hQ hα
  have : (2 : ℤ) ≤ 2 + ((posRoots Q ξ).filter fun β => bZ Q β α = 1).card -
      ((posRoots Q ξ).filter fun β => bZ Q β α = -1).card := by omega
  have : (2 : ℚ) ≤ ((2 + ((posRoots Q ξ).filter fun β => bZ Q β α = 1).card -
      ((posRoots Q ξ).filter fun β => bZ Q β α = -1).card : ℤ) : ℚ) := by exact_mod_cast this
  linarith

/-- The positive roots are nonempty when there are roots. -/
theorem posRoots_nonempty (hQ : IntQF.PosDef Q) (hξ : ∀ α ∈ rootSet Q, bQ Q (cv α) ξ ≠ 0)
    (hR : (rootSet Q).Nonempty) : (posRoots Q ξ).Nonempty := by
  obtain ⟨α, hα⟩ := hR
  rcases lt_or_gt_of_ne (hξ α hα) with h | h
  · refine ⟨-α, (mem_posRoots (hQ := hQ)).mpr ⟨neg_mem_rootSet hα, ?_⟩⟩
    rw [cv_neg', bQ_neg_left]; linarith
  · exact ⟨α, (mem_posRoots (hQ := hQ)).mpr ⟨hα, h⟩⟩

/-- **A simple root** (Chenevier–Lannes, p. 65: "$\alpha \in B$ if and only if $\rho \cdot \alpha = 1$"; existence
part): if $L$ has roots, some root $\alpha$ has $\rho \cdot \alpha = 1$. Unconditional. *Proof.* Take $\alpha \in R^+$
with $\alpha \cdot \xi$ least. For $\gamma \in R^+$ with $\gamma \cdot \alpha = 1$, $\gamma - \alpha$ is a root, and it is
positive (otherwise $\alpha - \gamma \in R^+$ would have $(\alpha - \gamma) \cdot \xi < \alpha \cdot \xi$), with
$(\gamma - \alpha) \cdot \alpha = -1$; so $\beta \mapsto \beta + \alpha$ is a bijection in `sum_bZ_posRoots` and
$2\rho \cdot \alpha = 2$. -/
@[kb "chenevierlannes2019" "§3.4.2, p. 65 (a simple root: ρ.α = 1)"]
theorem exists_weyl_dot_eq_one (hQ : IntQF.PosDef Q) (hξ : ∀ α ∈ rootSet Q, bQ Q (cv α) ξ ≠ 0) {ρ : Fin n → ℚ}
    (hρ : (2 : ℚ) • ρ = ∑ β ∈ posRoots Q ξ, cv β) (hR : (rootSet Q).Nonempty) :
    ∃ α ∈ posRoots Q ξ, bQ Q ρ (cv α) = 1 := by
  obtain ⟨α, hα, hmin⟩ := (posRoots Q ξ).exists_min_image (fun β => bQ Q (cv β) ξ) (posRoots_nonempty hQ hξ hR)
  refine ⟨α, hα, ?_⟩
  have hαR := (mem_posRoots (hQ := hQ)).mp hα
  have hle : ((posRoots Q ξ).filter fun β => bZ Q β α = 1).card ≤
      ((posRoots Q ξ).filter fun β => bZ Q β α = -1).card := by
    refine Finset.card_le_card_of_injOn (fun β => β - α) ?_ ?_
    · intro γ hγ
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hγ ⊢
      have hγR := (mem_posRoots (hQ := hQ)).mp hγ.1
      have hsub := sub_mem_rootSet hγR.1 hαR.1 hγ.2
      refine ⟨(mem_posRoots (hQ := hQ)).mpr ⟨hsub, ?_⟩, ?_⟩
      · rcases lt_or_gt_of_ne (hξ _ hsub) with h | h
        · exfalso
          have hneg : α - γ ∈ posRoots Q ξ := by
            refine (mem_posRoots (hQ := hQ)).mpr ⟨?_, ?_⟩
            · have := neg_mem_rootSet hsub; rwa [neg_sub] at this
            · have : cv (α - γ) = -cv (γ - α) := by rw [← cv_neg', neg_sub]
              rw [this, bQ_neg_left]; linarith
          have := hmin _ hneg
          rw [cv_sub, sub_eq_add_neg, bQ_add_left, bQ_neg_left] at this
          linarith [hγR.2]
        · exact h
      · rw [sub_eq_add_neg, ← neg_one_smul ℤ α, bZ_add_left, bZ_smul_left, hγ.2, bZ_root_self hαR.1]; norm_num
    · intro β _ γ _ h
      simpa using h
  have h2 := two_weyl_dot hρ α
  rw [sum_bZ_posRoots hQ hξ hα] at h2
  have hc := card_neg_le_card_pos hQ hα
  have he : (2 + ((posRoots Q ξ).filter fun β => bZ Q β α = 1).card -
      ((posRoots Q ξ).filter fun β => bZ Q β α = -1).card : ℤ) = 2 := by omega
  rw [he] at h2
  push_cast at h2
  linarith

/-- **The Weyl vector is regular** (Chenevier–Lannes, p. 65: $\rho$ lies in its chamber): unconditional. -/
theorem weyl_isRegular (hQ : IntQF.PosDef Q) (hξ : ∀ α ∈ rootSet Q, bQ Q (cv α) ξ ≠ 0) {ρ : Fin n → ℚ}
    (hρ : (2 : ℚ) • ρ = ∑ β ∈ posRoots Q ξ, cv β) : IsRegularVec Q ρ := by
  intro α hα h0
  rw [bQ_symm] at h0
  rcases lt_or_gt_of_ne (hξ α hα) with h | h
  · have hm : -α ∈ posRoots Q ξ := (mem_posRoots (hQ := hQ)).mpr ⟨neg_mem_rootSet hα, by
      rw [cv_neg', bQ_neg_left]; linarith⟩
    have := one_le_weyl_dot hQ hξ hρ hm
    rw [cv_neg', bQ_symm, bQ_neg_left, bQ_symm, h0] at this
    linarith
  · have := one_le_weyl_dot hQ hξ hρ ((mem_posRoots (hQ := hQ)).mpr ⟨hα, h⟩)
    rw [h0] at this
    linarith

end Heights

/-! ### The upper bound $\rho \cdot \alpha \le h - 1$ (conditional on Venkov) -/

/-- $\frac{t^2 - t}{2} \ge 0$ for $t \in \mathbb{Z}$. -/
theorem half_sq_sub_nonneg (t : ℤ) : 0 ≤ (((t : ℚ) ^ 2 - t) / 2) := by
  have : (0 : ℤ) ≤ t ^ 2 - t := by nlinarith [sq_nonneg (2 * t - 1)]
  have : (0 : ℚ) ≤ (t : ℚ) ^ 2 - t := by exact_mod_cast this
  linarith

/-- $\frac{t^2 - t}{2} \ge 1$ for $t \in \mathbb{Z} \setminus \{0, 1\}$. -/
theorem one_le_half_sq_sub (t : ℤ) (h0 : t ≠ 0) (h1 : t ≠ 1) : 1 ≤ (((t : ℚ) ^ 2 - t) / 2) := by
  have : (2 : ℤ) ≤ t ^ 2 - t := by
    rcases (by omega : t ≤ -1 ∨ 2 ≤ t) with h | h <;> nlinarith
  have : (2 : ℚ) ≤ (t : ℚ) ^ 2 - t := by exact_mod_cast this
  linarith

/-- Borcherds' identity at $x \in L$, in integers: $h\,q(x) - \rho \cdot x = \sum_{\alpha \in R^+}
\frac{(\alpha \cdot x)^2 - \alpha \cdot x}{2}$ with $\alpha \cdot x = $ `bZ Q α x`. -/
theorem borcherds_int (hV : VenkovRootSum 24) {Q : QuadForm ℤ 24} (hQ : IsEvenUnimodular Q) {ξ ρ : Fin 24 → ℚ}
    (hξ : ∀ α ∈ rootSet Q, bQ Q (cv α) ξ ≠ 0) (hρ : (2 : ℚ) • ρ = ∑ α ∈ posRoots Q ξ, cv α) (x : Fin 24 → ℤ) :
    coxeterNumber Q * Q.eval x - bQ Q ρ (cv x) =
      ∑ α ∈ posRoots Q ξ, (((bZ Q α x : ℚ)) ^ 2 - bZ Q α x) / 2 := by
  have := prop_3_4_2_2_b hV hQ hξ hρ (cv x)
  rw [evalIn_cv] at this
  rw [this]
  exact Finset.sum_congr rfl fun α _ => by rw [bQ_cv]

/-- **Heights are at most $h - 1$** (Chenevier–Lannes, p. 68, the property $H(\beta) \le h - 1$; the book cites
Bourbaki, Chap. VI, §1, Proposition 31): **conditional** on `VenkovRootSum 24`. For a Niemeier lattice, a chamber
$\xi$ and its Weyl vector $\rho$, every root $\alpha$ has $\rho \cdot \alpha \le h - 1$. *Proof.* Borcherds' identity
at $x = \alpha$ reads $h - \rho \cdot \alpha = \sum_{\beta \in R^+} \frac{(\beta \cdot \alpha)^2 - \beta \cdot
\alpha}{2}$; all terms are $\ge 0$ and the term of $\beta = \pm\alpha \in R^+$ is $1$ or $3$. -/
@[kb "chenevierlannes2019" "§3.4.2, p. 68 (heights: H(β) ≤ h − 1; conditional)"]
theorem weyl_dot_le (hV : VenkovRootSum 24) {Q : QuadForm ℤ 24} (hQ : IsEvenUnimodular Q) {ξ ρ : Fin 24 → ℚ}
    (hξ : ∀ α ∈ rootSet Q, bQ Q (cv α) ξ ≠ 0) (hρ : (2 : ℚ) • ρ = ∑ α ∈ posRoots Q ξ, cv α) {α : Fin 24 → ℤ}
    (hα : α ∈ rootSet Q) : bQ Q ρ (cv α) ≤ coxeterNumber Q - 1 := by
  have hb := borcherds_int hV hQ hξ hρ α
  have hα1 : Q.eval α = 1 := hα
  rw [hα1] at hb
  have hnn : ∀ β ∈ posRoots Q ξ, 0 ≤ (((bZ Q β α : ℚ)) ^ 2 - bZ Q β α) / 2 :=
    fun β _ => half_sq_sub_nonneg _
  have key : ∃ β ∈ posRoots Q ξ, 1 ≤ (((bZ Q β α : ℚ)) ^ 2 - bZ Q β α) / 2 := by
    rcases lt_or_gt_of_ne (hξ α hα) with h | h
    · refine ⟨-α, (mem_posRoots (hQ := hQ.posDef)).mpr ⟨neg_mem_rootSet hα, by
        rw [cv_neg', bQ_neg_left]; linarith⟩, ?_⟩
      rw [bZ_neg_left, bZ_root_self hα]; norm_num
    · refine ⟨α, (mem_posRoots (hQ := hQ.posDef)).mpr ⟨hα, h⟩, ?_⟩
      rw [bZ_root_self hα]; norm_num
  obtain ⟨β, hβ, h1⟩ := key
  have := Finset.single_le_sum hnn hβ
  push_cast at hb
  linarith

/-! ### Proposition 3.4.2.8 (a) -/

/-- The Weyl vector of a Niemeier lattice with roots, with $h \in \mathbb{N}$ and $\rho \in L$. -/
theorem weyl_data (hV : VenkovRootSum 24) {Q : QuadForm ℤ 24} (hQ : IsNiemeier Q) (hR : (rootSet Q).Nonempty)
    {ρ : Fin 24 → ℚ} (hρ : IsWeylVector Q ρ) :
    ∃ (r : Fin 24 → ℤ) (h : ℕ) (ξ : Fin 24 → ℚ), ρ = cv r ∧ coxeterNumber Q = h ∧
      (∀ α ∈ rootSet Q, bQ Q (cv α) ξ ≠ 0) ∧ (2 : ℚ) • ρ = ∑ α ∈ posRoots Q ξ, cv α := by
  have hQ' : IsEvenUnimodular Q := hQ
  obtain ⟨r, hr⟩ := weylVector_mem_lattice hV hQ hR hρ
  obtain ⟨h, hh⟩ := coxeterNumber_eq_nat hV hQ' hR
  obtain ⟨ξ, hξ, h2⟩ := hρ.exists_posRoots hQ'.posDef
  exact ⟨r, h, ξ, hr, hh, hξ, h2⟩

/-- For $\alpha$ a root: $1 \le |\rho \cdot \alpha| \le h - 1$ (in integers, with $\rho = r \in L$). -/
theorem weyl_dot_bounds (hV : VenkovRootSum 24) {Q : QuadForm ℤ 24} (hQ : IsEvenUnimodular Q) {ξ : Fin 24 → ℚ}
    {r : Fin 24 → ℤ} {h : ℕ} (hh : coxeterNumber Q = h) (hξ : ∀ α ∈ rootSet Q, bQ Q (cv α) ξ ≠ 0)
    (hρ : (2 : ℚ) • cv r = ∑ α ∈ posRoots Q ξ, cv α) {α : Fin 24 → ℤ} (hα : α ∈ rootSet Q) :
    (1 ≤ bZ Q r α ∨ bZ Q r α ≤ -1) ∧ bZ Q r α ≤ h - 1 ∧ -(h - 1 : ℤ) ≤ bZ Q r α := by
  have hup := weyl_dot_le hV hQ hξ hρ hα
  have hup' := weyl_dot_le hV hQ hξ hρ (neg_mem_rootSet hα)
  rw [bQ_cv, hh] at hup
  rw [bQ_cv, hh, bZ_comm, bZ_neg_left, bZ_comm] at hup'
  have hreg := weyl_isRegular hQ.posDef hξ hρ α hα
  rw [bQ_symm, bQ_cv] at hreg
  refine ⟨?_, by exact_mod_cast hup, ?_⟩
  · have : bZ Q r α ≠ 0 := by exact_mod_cast hreg
    omega
  · have : -(bZ Q r α : ℚ) ≤ h - 1 := by push_cast at hup'; linarith
    have : -(bZ Q r α) ≤ (h : ℤ) - 1 := by exact_mod_cast this
    linarith

/-- **Proposition 3.4.2.8 (a)** (Chenevier–Lannes, p. 67): **conditional** on `VenkovRootSum 24`. A Weyl vector $\rho$
of a Niemeier lattice $L$ with roots lies in $L$, is primitive (a fortiori $d$-primitive for every $d$: some
$v \in L$, a simple root, has $\rho \cdot v = 1$) and is $h$-regular ($\alpha \cdot \rho \notin h\mathbb{Z}$ for every
root $\alpha$). -/
@[kb "chenevierlannes2019" "Prop. 3.4.2.8 (a), p. 67 (conditional)"]
theorem prop_3_4_2_8_a (hV : VenkovRootSum 24) {Q : QuadForm ℤ 24} (hQ : IsNiemeier Q) (hR : (rootSet Q).Nonempty)
    {ρ : Fin 24 → ℚ} (hρ : IsWeylVector Q ρ) :
    ∃ r : Fin 24 → ℤ, ρ = cv r ∧ IsPrimitiveVec r ∧ (∃ v ∈ rootSet Q, bZ Q r v = 1) ∧
      ∃ h : ℕ, coxeterNumber Q = h ∧ IsDRegular Q h ρ := by
  have hQ' : IsEvenUnimodular Q := hQ
  obtain ⟨r, h, ξ, rfl, hh, hξ, h2⟩ := weyl_data hV hQ hR hρ
  obtain ⟨α, hα, h1⟩ := exists_weyl_dot_eq_one hQ'.posDef hξ h2 hR
  have hαR := ((mem_posRoots (hQ := hQ'.posDef)).mp hα).1
  rw [bQ_cv] at h1
  have h1' : bZ Q r α = 1 := by exact_mod_cast h1
  refine ⟨r, rfl, ⟨?_, ?_⟩, ⟨α, hαR, h1'⟩, h, hh, ?_⟩
  · rintro rfl
    simp [bZ] at h1'
  · intro k y hy
    rw [hy, bZ_smul_left] at h1'
    exact IsUnit.of_mul_eq_one (b := bZ Q y α) h1'
  · intro β hβ k hk
    rw [bQ_symm, bQ_cv] at hk
    have hk' : bZ Q r β = h * k := by exact_mod_cast hk
    obtain ⟨hnz, hle, hge⟩ := weyl_dot_bounds hV hQ' hh hξ h2 hβ
    rw [hk'] at hnz hle hge
    rcases hnz with hnz | hnz
    · have : 0 < k := by
        by_contra hk0; push Not at hk0; nlinarith
      nlinarith
    · have : k < 0 := by
        by_contra hk0; push Not at hk0; nlinarith
      nlinarith

/-! ### Theorem 3.4.2.10 (a) in full -/

/-- **Theorem 3.4.2.10 (a)** (Chenevier–Lannes, p. 69): **conditional** on `VenkovRootSum 24` and `WeylVectorNorm`.
For a Niemeier lattice $L$ with roots, a Weyl vector $\rho \in L$ and $d \in \{h, h + 1\}$, the class of $\rho$ lies
on the quadric $C_L(\mathbb{Z}/d)$: $\rho$ is $d$-primitive (some $v \in L$ has $\rho \cdot v \equiv 1 \bmod d$) and
$q(\rho) \equiv 0 \bmod d$. This is the first conjunct of `HolyConstructions`; wave 4
(`coxeter_dvd_weylVector_norm`) had only the isotropy. -/
@[kb "chenevierlannes2019" "Thm. 3.4.2.10 (a), p. 69 (conditional)"]
theorem holyConstructions_a (hV : VenkovRootSum 24) (hN : WeylVectorNorm) {Q : QuadForm ℤ 24} (hQ : IsNiemeier Q)
    (hR : (rootSet Q).Nonempty) {ρ : Fin 24 → ℤ} (hρ : IsWeylVector Q (cv ρ)) (d : ℕ)
    (hd : (d : ℚ) = coxeterNumber Q ∨ (d : ℚ) = coxeterNumber Q + 1) :
    (∃ v : Fin 24 → ℤ, (d : ℤ) ∣ bZ Q ρ v - 1) ∧ (d : ℤ) ∣ Q.eval ρ := by
  obtain ⟨r, hr, -, ⟨v, -, hv⟩, -⟩ := prop_3_4_2_8_a hV hQ hR hρ
  have hrρ : r = ρ := cv_injective hr.symm
  subst hrρ
  refine ⟨⟨v, by rw [hv]; simp⟩, ?_⟩
  obtain ⟨r', h, hr', hh, hdh, hdh1⟩ := coxeter_dvd_weylVector_norm hV hN hQ hR hρ
  have : r' = r := cv_injective hr'.symm
  subst this
  rw [hh] at hd
  rcases hd with hd | hd
  · have : d = h := by exact_mod_cast hd
    subst this; exact hdh
  · have : (d : ℤ) = h + 1 := by exact_mod_cast hd
    rw [this]; exact hdh1

/-! ### Proposition 3.4.2.9 (Borcherds) -/

/-- $q(\rho - t\eta) = q(\rho) - t\,\rho \cdot \eta + t^2 q(\eta)$. -/
theorem evalIn_sub_smul (Q : QuadForm ℤ n) (ρ η : Fin n → ℚ) (t : ℚ) :
    Q.evalIn ℚ (ρ - t • η) = Q.evalIn ℚ ρ - t * bQ Q ρ η + t ^ 2 * Q.evalIn ℚ η := by
  have := evalIn_add_smulQ Q ρ η (-t)
  rw [neg_smul, ← sub_eq_add_neg] at this
  rw [this]; ring

/-- The root lattice $Q(R)$ lies in $L$. -/
theorem rootSpan_le_stdLat (Q : QuadForm ℤ n) : Submodule.span ℤ (cv '' rootSet Q) ≤ stdLat n := by
  rw [Submodule.span_le]
  rintro _ ⟨α, -, rfl⟩
  exact ⟨α, rfl⟩

/-- **Proposition 3.4.2.9 (a)** (Chenevier–Lannes, p. 68): **conditional** on `VenkovRootSum 24`. For a Niemeier
lattice $L$ with roots, Coxeter number $h$, a Weyl vector $\rho$ and $\eta \in Q(R)^\sharp$ ($\alpha \cdot \eta \in
\mathbb{Z}$ for every root; the book's $\xi$), $\rho - h\eta$ lies in $L$ and is $h$-regular. -/
@[kb "chenevierlannes2019" "Prop. 3.4.2.9 (a), p. 68 (conditional)"]
theorem prop_3_4_2_9_a (hV : VenkovRootSum 24) {Q : QuadForm ℤ 24} (hQ : IsNiemeier Q) (hR : (rootSet Q).Nonempty)
    {h : ℕ} (hh : coxeterNumber Q = h) {ρ : Fin 24 → ℚ} (hρ : IsWeylVector Q ρ) {η : Fin 24 → ℚ}
    (hη : ∀ α ∈ rootSet Q, ∃ k : ℤ, bQ Q (cv α) η = k) :
    (∃ s : Fin 24 → ℤ, ρ - (h : ℚ) • η = cv s) ∧ IsDRegular Q h (ρ - (h : ℚ) • η) := by
  have hQ' : IsEvenUnimodular Q := hQ
  obtain ⟨r, hr, -, -, h', hh', hreg⟩ := prop_3_4_2_8_a hV hQ hR hρ
  have hhh : h' = h := by exact_mod_cast hh'.symm.trans hh
  subst hhh
  constructor
  · have hmem := rootSpan_le_stdLat Q (coxeter_smul_mem_rootSpan hV hQ' hη)
    rw [hh] at hmem
    obtain ⟨s, hs⟩ := hmem
    exact ⟨r - s, by rw [hr, cv_sub, hs]⟩
  · intro α hα m hm
    obtain ⟨k, hk⟩ := hη α hα
    rw [sub_eq_add_neg, bQ_symm, bQ_add_left, bQ_neg_left, bQ_smul_left, bQ_symm _ η, hk, bQ_symm] at hm
    exact hreg α hα (m + k) (by push_cast; linarith)

/-- $q(\rho - h\eta) - q(\rho) = h\,(h\,q(\eta) - \rho \cdot \eta) = h \sum_{\alpha \in R^+}
\frac{(\alpha \cdot \eta)^2 - \alpha \cdot \eta}{2}$ (the book's computation, p. 69). -/
theorem evalIn_weyl_sub (hV : VenkovRootSum 24) {Q : QuadForm ℤ 24} (hQ : IsEvenUnimodular Q) {ξ ρ : Fin 24 → ℚ}
    (hξ : ∀ α ∈ rootSet Q, bQ Q (cv α) ξ ≠ 0) (hρ : (2 : ℚ) • ρ = ∑ α ∈ posRoots Q ξ, cv α) (η : Fin 24 → ℚ) :
    Q.evalIn ℚ (ρ - coxeterNumber Q • η) - Q.evalIn ℚ ρ =
      coxeterNumber Q * ∑ α ∈ posRoots Q ξ, (bQ Q (cv α) η ^ 2 - bQ Q (cv α) η) / 2 := by
  rw [evalIn_sub_smul, ← prop_3_4_2_2_b hV hQ hξ hρ η]
  ring

/-- The sum $\sum_{\alpha \in R^+} \frac{(\alpha \cdot \eta)^2 - \alpha \cdot \eta}{2}$ is $\ge 0$ for $\eta \in
Q(R)^\sharp$, and $= 0$ exactly when $\alpha \cdot \eta \in \{0, 1\}$ for every $\alpha \in R^+$. -/
theorem sum_half_sq_sub {S : Finset (Fin 24 → ℤ)} {f : (Fin 24 → ℤ) → ℚ} (hf : ∀ α ∈ S, ∃ k : ℤ, f α = k) :
    0 ≤ ∑ α ∈ S, (f α ^ 2 - f α) / 2 ∧
      (∑ α ∈ S, (f α ^ 2 - f α) / 2 = 0 ↔ ∀ α ∈ S, f α = 0 ∨ f α = 1) := by
  have hnn : ∀ α ∈ S, 0 ≤ (f α ^ 2 - f α) / 2 := fun α hα => by
    obtain ⟨k, hk⟩ := hf α hα; rw [hk]; exact half_sq_sub_nonneg k
  refine ⟨Finset.sum_nonneg hnn, ?_⟩
  rw [Finset.sum_eq_zero_iff_of_nonneg hnn]
  refine forall₂_congr fun α hα => ?_
  obtain ⟨k, hk⟩ := hf α hα
  rw [hk]
  constructor
  · intro h0
    by_contra hc
    push Not at hc
    have := one_le_half_sq_sub k (by exact_mod_cast hc.1) (by exact_mod_cast hc.2)
    linarith
  · rintro (h | h) <;> rw [h] <;> norm_num

/-- **Proposition 3.4.2.9 (b), (c) (Borcherds)** (Chenevier–Lannes, pp. 68–69): **conditional** on
`VenkovRootSum 24`. For a Niemeier lattice $L$ with roots, a chamber $\xi$ with Weyl vector $\rho$, and
$\eta \in Q(R)^\sharp$:
(b) $q(\rho - h\eta) \ge q(\rho)$;
(c) (i) ⇔ (ii): equality holds if and only if $\alpha \cdot \eta \in \{0, 1\}$ for every $\alpha \in R^+$, which is
the book's description of $\eta \in \Pi = Q(R)^\sharp \cap \overline{\mathrm{Alc}}$ (proof of Proposition 2.3.8 (a),
p. 39). Condition (iii) ($\rho - h\eta$ is a Weyl vector) is not formalized (it uses Scholium 3.4.2.7, whose proof
needs Bourbaki's positivity of the dual basis of a basis). -/
@[kb "chenevierlannes2019" "Prop. 3.4.2.9 (b), (c), pp. 68–69 (conditional)"]
theorem prop_3_4_2_9_bc (hV : VenkovRootSum 24) {Q : QuadForm ℤ 24} (hQ : IsEvenUnimodular Q) {ξ ρ : Fin 24 → ℚ}
    (hξ : ∀ α ∈ rootSet Q, bQ Q (cv α) ξ ≠ 0) (hρ : (2 : ℚ) • ρ = ∑ α ∈ posRoots Q ξ, cv α)
    (hR : (rootSet Q).Nonempty) {η : Fin 24 → ℚ} (hη : ∀ α ∈ rootSet Q, ∃ k : ℤ, bQ Q (cv α) η = k) :
    Q.evalIn ℚ ρ ≤ Q.evalIn ℚ (ρ - coxeterNumber Q • η) ∧
      (Q.evalIn ℚ (ρ - coxeterNumber Q • η) = Q.evalIn ℚ ρ ↔
        ∀ α ∈ posRoots Q ξ, bQ Q (cv α) η = 0 ∨ bQ Q (cv α) η = 1) := by
  have he := evalIn_weyl_sub hV hQ hξ hρ η
  have hf : ∀ α ∈ posRoots Q ξ, ∃ k : ℤ, bQ Q (cv α) η = k := fun α hα =>
    hη α ((mem_posRoots (hQ := hQ.posDef)).mp hα).1
  obtain ⟨hnn, hiff⟩ := sum_half_sq_sub hf
  have hpos : 0 < coxeterNumber Q := by
    unfold coxeterNumber
    obtain ⟨α, hα⟩ := hR
    have : 0 < repNum Q 1 := by
      rw [← ncard_rootSet]
      exact (Set.ncard_pos (rootSet_finite hQ.posDef)).mpr ⟨α, hα⟩
    positivity
  refine ⟨by nlinarith, ?_⟩
  rw [← hiff, ← sub_eq_zero, he, mul_eq_zero]
  exact ⟨fun h => h.resolve_left hpos.ne', Or.inr⟩

/-- **Proposition 3.4.2.9 (b) with Venkov's norm** (Chenevier–Lannes, p. 68): **conditional** on `VenkovRootSum 24`
and `WeylVectorNorm`. For $\eta \in Q(R)^\sharp$, $q(\rho - h\eta) \ge q(\rho) = h(h + 1)$. -/
@[kb "chenevierlannes2019" "Prop. 3.4.2.9 (b), p. 68 (with q(ρ) = h(h + 1); conditional)"]
theorem prop_3_4_2_9_b_norm (hV : VenkovRootSum 24) (hN : WeylVectorNorm) {Q : QuadForm ℤ 24} (hQ : IsNiemeier Q)
    (hR : (rootSet Q).Nonempty) {ρ : Fin 24 → ℚ} (hρ : IsWeylVector Q ρ) {η : Fin 24 → ℚ}
    (hη : ∀ α ∈ rootSet Q, ∃ k : ℤ, bQ Q (cv α) η = k) :
    coxeterNumber Q * (coxeterNumber Q + 1) ≤ Q.evalIn ℚ (ρ - coxeterNumber Q • η) := by
  have hQ' : IsEvenUnimodular Q := hQ
  obtain ⟨ξ, hξ, h2⟩ := hρ.exists_posRoots hQ'.posDef
  rw [← hN Q hQ hR ρ hρ]
  exact (prop_3_4_2_9_bc hV hQ' hξ h2 hR hη).1

/-! ### Proposition 3.4.2.16 -/

/-- **Proposition 3.4.2.16** (Chenevier–Lannes, p. 73): **conditional** on `VenkovRootSum 24` and `WeylVectorNorm`.
For a Niemeier lattice $L$ with roots, Coxeter number $h$, a Weyl vector $\rho$ and $x \in L$ nonzero,
$$q(\rho - (h + 1)x) \ge (h + 1)(h + 2).$$
*Proof* (the book's adaptation of Borcherds' argument): $q(\rho - (h + 1)x) = (h + 1)\bigl(h + q(x) +
\sum_{\alpha \in R^+} \frac{(\alpha \cdot x)^2 - \alpha \cdot x}{2}\bigr)$; if some $\alpha \cdot x \notin \{0, 1\}$ the
sum is $\ge 1$ and $q(x) \ge 1$; otherwise $x$ is not a root (for $\beta = \pm x \in R^+$, $\beta \cdot x = \pm 2$),
so $q(x) \ge 2$. -/
@[kb "chenevierlannes2019" "Prop. 3.4.2.16, p. 73 (conditional)"]
theorem prop_3_4_2_16 (hV : VenkovRootSum 24) (hN : WeylVectorNorm) {Q : QuadForm ℤ 24} (hQ : IsNiemeier Q)
    (hR : (rootSet Q).Nonempty) {ρ : Fin 24 → ℚ} (hρ : IsWeylVector Q ρ) {x : Fin 24 → ℤ} (hx : x ≠ 0) :
    (coxeterNumber Q + 1) * (coxeterNumber Q + 2) ≤ Q.evalIn ℚ (ρ - (coxeterNumber Q + 1) • cv x) := by
  have hQ' : IsEvenUnimodular Q := hQ
  obtain ⟨ξ, hξ, h2⟩ := hρ.exists_posRoots hQ'.posDef
  have hn := hN Q hQ hR ρ hρ
  have hb := borcherds_int hV hQ' hξ h2 x
  rw [evalIn_sub_smul, evalIn_cv, hn]
  set h := coxeterNumber Q
  set S := ∑ α ∈ posRoots Q ξ, (((bZ Q α x : ℚ)) ^ 2 - bZ Q α x) / 2
  have hS := sum_half_sq_sub (S := posRoots Q ξ) (f := fun α => (bZ Q α x : ℚ)) (fun α _ => ⟨_, rfl⟩)
  have hqx : 1 ≤ Q.eval x := hQ'.posDef x hx
  have hh0 : 0 ≤ h := by unfold h coxeterNumber; positivity
  have key : 2 ≤ (Q.eval x : ℚ) + S := by
    by_cases hall : ∀ α ∈ posRoots Q ξ, (bZ Q α x : ℚ) = 0 ∨ (bZ Q α x : ℚ) = 1
    · have h2x : 2 ≤ Q.eval x := by
        by_contra hlt
        have hx1 : Q.eval x = 1 := by omega
        have hxR : x ∈ rootSet Q := hx1
        rcases lt_or_gt_of_ne (hξ x hxR) with hneg | hpos
        · have hm : -x ∈ posRoots Q ξ := (mem_posRoots (hQ := hQ'.posDef)).mpr ⟨neg_mem_rootSet hxR, by
            rw [cv_neg', bQ_neg_left]; linarith⟩
          have := hall _ hm
          rw [bZ_neg_left, bZ_root_self hxR] at this
          norm_num at this
        · have hm : x ∈ posRoots Q ξ := (mem_posRoots (hQ := hQ'.posDef)).mpr ⟨hxR, hpos⟩
          have := hall _ hm
          rw [bZ_root_self hxR] at this
          norm_num at this
      have : (2 : ℚ) ≤ Q.eval x := by exact_mod_cast h2x
      linarith [hS.1]
    · push Not at hall
      obtain ⟨α, hα, h0, h1⟩ := hall
      have hle := Finset.single_le_sum (f := fun α => (((bZ Q α x : ℚ)) ^ 2 - bZ Q α x) / 2)
        (fun β _ => half_sq_sub_nonneg _) hα
      have := one_le_half_sq_sub (bZ Q α x) (by exact_mod_cast h0) (by exact_mod_cast h1)
      have : (1 : ℚ) ≤ Q.eval x := by exact_mod_cast hqx
      linarith
  -- $q(\rho - (h+1)x) = h(h+1) - (h+1)\,\rho \cdot x + (h+1)^2 q(x) = (h+1)(h + q(x) + S)$
  have hid : h * (h + 1) - (h + 1) * bQ Q ρ (cv x) + (h + 1) ^ 2 * (Q.eval x : ℚ) =
      (h + 1) * (h + Q.eval x + S) := by
    rw [← hb]; ring
  rw [hid]
  nlinarith

end QuadFormsKB.ChenevierLannes
