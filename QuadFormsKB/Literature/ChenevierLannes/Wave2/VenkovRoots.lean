/-
# Chenevier–Lannes: inner products of roots and Venkov's identity

Source: Chenevier–Lannes 2019 (`chenevierlannes2019`), §2.3, Proposition 2.3.2 and Proposition-Definition 2.3.3,
p. 35 (the proof of (b): evaluating Venkov's identity at a root), Scholium 2.3.4, p. 36; Corollary 2.3.14, p. 40.
Printed page numbers.

**Layer.** As in `Venkov.lean`: an even unimodular lattice $L$ is its integral form $Q = q_L$, the inner product of
$x, y \in \mathbb{Z}^n$ is $x \cdot y = x^{\mathsf T}Hy$ (`Siegel.Kneser.bZ`, $H$ the Hessian), $x \cdot x = 2Q(x)$, and
$R(L)$ (`rootSet`) is the set of $\alpha \in \mathbb{Z}^n$ with $Q(\alpha) = 1$.

**Proves:**
- `root_dot_le_one`, `neg_one_le_root_dot` (unconditional): for roots $\alpha, \beta$ of a positive definite lattice,
  $\beta \cdot \alpha \le 1$ unless $\beta = \alpha$ and $\beta \cdot \alpha \ge -1$ unless $\beta = -\alpha$ (from
  $Q(\beta \mp \alpha) = 2 \mp \beta \cdot \alpha > 0$);
- `card_root_dot_pm_one` (**conditional** on `VenkovRootSum n`): for a root $\alpha$ of an even unimodular $L$ of
  dimension $n$, the number of roots $\beta$ with $\beta \cdot \alpha = \pm 1$ is $4|R(L)|/n - 8$ (Venkov's identity at
  $x = \alpha$, the step of the book's proof of Proposition-Definition 2.3.3 (b));
- `card_root_dot_pm_one_twentyFour` (**conditional** on `VenkovRootSum 24`): for $n = 24$ this number is $4h(L) - 8$;
- `card_root_dot_pm_one_eight`, `card_root_dot_pm_one_sixteen` (**conditional** on `VenkovRootSum 8`, resp. `16`): the
  number is $112$ for $n = 8$ and $112$ for $n = 16$ ($|R(L)| = 240, 480$ proved unconditionally).

**States** (named statement, not proved):
- `NiemeierRootLatticeDetermines` (the injectivity in Corollary 2.3.14): two Niemeier lattices with roots whose root
  lattices are isometric are isomorphic.
-/
import QuadFormsKB.Literature.ChenevierLannes.Wave2.Venkov

open Matrix

namespace QuadFormsKB.ChenevierLannes

open QuadFormsKB.Siegel QuadFormsKB.Siegel.Kneser

variable {n : ℕ}

/-- At an integral vector, `latDot` is the integer inner product: $\alpha \cdot \beta = \alpha^{\mathsf T}H\beta$. -/
theorem latDot_intCast (Q : QuadForm ℤ n) (α β : Fin n → ℤ) :
    latDot Q α (fun i => (β i : ℝ)) = (bZ Q α β : ℝ) := by
  simp [latDot, bZ, dotProduct, mulVec, Matrix.map_apply]

/-- **$\beta \cdot \alpha \le 1$ for roots $\beta \ne \alpha$** of a positive definite lattice:
$0 < Q(\beta - \alpha) = 2 - \beta \cdot \alpha$. Unconditional. -/
theorem root_dot_le_one {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q) {α β : Fin n → ℤ} (hα : α ∈ rootSet Q)
    (hβ : β ∈ rootSet Q) (hne : β ≠ α) : bZ Q β α ≤ 1 := by
  have hα' : Q.eval α = 1 := hα
  have hβ' : Q.eval β = 1 := hβ
  have h := eval_add_smulZ Q β α (-1)
  have hpos := hQ (β + (-1 : ℤ) • α) (by
    intro h0
    apply hne
    rw [neg_one_smul, ← sub_eq_add_neg] at h0
    exact sub_eq_zero.mp h0)
  rw [h, hα', hβ'] at hpos
  norm_num at hpos
  omega

/-- **$\beta \cdot \alpha \ge -1$ for roots $\beta \ne -\alpha$** of a positive definite lattice:
$0 < Q(\beta + \alpha) = 2 + \beta \cdot \alpha$. Unconditional. -/
theorem neg_one_le_root_dot {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q) {α β : Fin n → ℤ} (hα : α ∈ rootSet Q)
    (hβ : β ∈ rootSet Q) (hne : β ≠ -α) : -1 ≤ bZ Q β α := by
  have hα' : Q.eval α = 1 := hα
  have hβ' : Q.eval β = 1 := hβ
  have h := eval_add_smulZ Q β α 1
  have hpos := hQ (β + (1 : ℤ) • α) (by
    intro h0
    apply hne
    rw [one_smul] at h0
    exact eq_neg_of_add_eq_zero_left h0)
  rw [h, hα', hβ'] at hpos
  norm_num at hpos
  omega

/-- $-\alpha$ is a root when $\alpha$ is. -/
theorem neg_mem_rootSet {Q : QuadForm ℤ n} {α : Fin n → ℤ} (hα : α ∈ rootSet Q) : -α ∈ rootSet Q := by
  have h := eval_smulZ (Q := Q) (-1) α
  show Q.eval (-α) = 1
  rw [← neg_one_smul ℤ α, h, show Q.eval α = 1 from hα]
  norm_num

/-- A root is not $0$, so $\alpha \ne -\alpha$. -/
theorem root_ne_neg {Q : QuadForm ℤ n} {α : Fin n → ℤ} (hα : α ∈ rootSet Q) : α ≠ -α := by
  intro h
  have h0 : α = 0 := by
    funext i
    have := congrFun h i
    simp only [Pi.neg_apply] at this
    simp only [Pi.zero_apply]
    omega
  have : Q.eval α = 1 := hα
  rw [h0] at this
  simp [QuadForm.evalIn] at this

/-- **The roots with $\beta \cdot \alpha = \pm 1$** (Chenevier–Lannes, proof of Proposition-Definition 2.3.3 (b), p. 35):
**conditional** on `VenkovRootSum n` (Proposition 2.3.2). For a root $\alpha$ of an even unimodular lattice $L$ of
dimension $n \ge 1$,
$$\#\{\beta \in R(L) : \beta \cdot \alpha = \pm 1\} = \frac{4\,|R(L)|}{n} - 8.$$
*Proof.* Venkov's identity at $x = \alpha$ gives $\sum_{\beta}(\beta \cdot \alpha)^2 = \frac{2|R(L)|}{n}\cdot 2$; the
terms are $4$ for $\beta = \pm\alpha$, and $1$ or $0$ otherwise (`root_dot_le_one`, `neg_one_le_root_dot`). -/
@[kb "chenevierlannes2019" "Prop.-Def. 2.3.3 (b), proof, p. 35 (conditional)"]
theorem card_root_dot_pm_one (hV : VenkovRootSum n) {Q : QuadForm ℤ n} (hQ : IsEvenUnimodular Q)
    {α : Fin n → ℤ} (hα : α ∈ rootSet Q) :
    ((((rootSet_finite hQ.posDef).toFinset.filter (fun β => bZ Q β α = 1 ∨ bZ Q β α = -1)).card : ℕ) : ℝ) =
      4 * ((rootSet Q).ncard : ℝ) / n - 8 := by
  classical
  set hfin := rootSet_finite hQ.posDef
  have hV' := hV.root_sum Q hQ (fun i => (α i : ℝ))
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, evalIn_intCast, show Q.eval α = 1 from hα] at hV'
  simp only [latDot_intCast] at hV'
  have hne := root_ne_neg hα
  have hpt : ∀ β ∈ hfin.toFinset, ((bZ Q β α : ℝ)) ^ 2 =
      ((if β = α then 4 else 0) + (if β = -α then 4 else 0) +
        (if bZ Q β α = 1 ∨ bZ Q β α = -1 then 1 else 0) : ℝ) := by
    intro β hβ
    rw [Set.Finite.mem_toFinset] at hβ
    by_cases h1 : β = α
    · subst h1
      have : bZ Q β β = 2 := by rw [bZ_self, show Q.eval β = 1 from hα]; rfl
      simp [this, hne]
      norm_num
    by_cases h2 : β = -α
    · subst h2
      have : bZ Q (-α) α = -2 := by
        rw [← neg_one_smul ℤ α, bZ_smul_left, bZ_self, show Q.eval α = 1 from hα]
        rfl
      simp [this, h1]
      norm_num
    · have hb1 := root_dot_le_one hQ.posDef hα hβ h1
      have hb2 := neg_one_le_root_dot hQ.posDef hα hβ h2
      simp only [h1, h2, if_false, zero_add]
      rcases (by omega : bZ Q β α = 1 ∨ bZ Q β α = -1 ∨ bZ Q β α = 0) with h | h | h <;> simp [h]
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.sum_ite_eq', Finset.sum_boole] at hV'
  have hmα : α ∈ hfin.toFinset := by rw [Set.Finite.mem_toFinset]; exact hα
  have hmnα : -α ∈ hfin.toFinset := by rw [Set.Finite.mem_toFinset]; exact neg_mem_rootSet hα
  rw [if_pos hmα, if_pos hmnα] at hV'
  push_cast at hV'
  have e : ∀ c : ℝ, 4 + 4 + c = 2 * ((rootSet Q).ncard : ℝ) / n * (2 * 1) →
      c = 4 * ((rootSet Q).ncard : ℝ) / n - 8 := fun c h => by
    rw [show 2 * ((rootSet Q).ncard : ℝ) / n * (2 * 1) = 4 * ((rootSet Q).ncard : ℝ) / n by ring] at h
    linarith
  convert e _ hV' using 3

/-- **Scholium 2.3.4 at a root** (Chenevier–Lannes, p. 36, with Proposition-Definition 2.3.3 (c)): **conditional** on
`VenkovRootSum 24`. For a root $\alpha$ of a Niemeier lattice $L$, the number of roots $\beta$ with
$\beta \cdot \alpha = \pm 1$ is $4h(L) - 8$, $h(L) = |R(L)|/24$ the Coxeter number (`coxeterNumber`). -/
@[kb "chenevierlannes2019" "Scholium 2.3.4, p. 36 (at a root; conditional)"]
theorem card_root_dot_pm_one_twentyFour (hV : VenkovRootSum 24) {Q : QuadForm ℤ 24} (hQ : IsEvenUnimodular Q)
    {α : Fin 24 → ℤ} (hα : α ∈ rootSet Q) :
    ((((rootSet_finite hQ.posDef).toFinset.filter (fun β => bZ Q β α = 1 ∨ bZ Q β α = -1)).card : ℕ) : ℝ) =
      4 * (coxeterNumber Q : ℝ) - 8 := by
  rw [card_root_dot_pm_one hV hQ hα, coxeterNumber, ← ncard_rootSet]
  push_cast
  ring

/-- **Dimension 8** (Chenevier–Lannes, Proposition 2.3.2 with $|R(E_8)| = 240$): **conditional** on `VenkovRootSum 8`.
Each root $\alpha$ has exactly $112$ roots $\beta$ with $\beta \cdot \alpha = \pm 1$. -/
theorem card_root_dot_pm_one_eight (hV : VenkovRootSum 8) {Q : QuadForm ℤ 8} (hQ : IsEvenUnimodular Q)
    {α : Fin 8 → ℤ} (hα : α ∈ rootSet Q) :
    ((rootSet_finite hQ.posDef).toFinset.filter (fun β => bZ Q β α = 1 ∨ bZ Q β α = -1)).card = 112 := by
  have h := card_root_dot_pm_one hV hQ hα
  rw [card_rootSet_eight hQ] at h
  norm_num at h
  exact_mod_cast h

/-- **Dimension 16** (Chenevier–Lannes, Proposition 2.3.2 with $|R(L)| = 480$): **conditional** on
`VenkovRootSum 16`. Each root $\alpha$ has exactly $112$ roots $\beta$ with $\beta \cdot \alpha = \pm 1$. -/
theorem card_root_dot_pm_one_sixteen (hV : VenkovRootSum 16) {Q : QuadForm ℤ 16} (hQ : IsEvenUnimodular Q)
    {α : Fin 16 → ℤ} (hα : α ∈ rootSet Q) :
    ((rootSet_finite hQ.posDef).toFinset.filter (fun β => bZ Q β α = 1 ∨ bZ Q β α = -1)).card = 112 := by
  have h := card_root_dot_pm_one hV hQ hα
  rw [card_rootSet_sixteen hQ] at h
  norm_num at h
  exact_mod_cast h

/-! ### Corollary 2.3.14 (statement) -/

/-- **The root lattice $Q(R(L))$** (Chenevier–Lannes, §2.3, p. 34): the $\mathbb{Z}$-span of the roots $R(L)$ inside
$L = \mathbb{Z}^n$. -/
@[kb "chenevierlannes2019" "§2.3, p. 34 (the root lattice Q(R))"]
def rootLattice (Q : QuadForm ℤ n) : Submodule ℤ (Fin n → ℤ) := Submodule.span ℤ (rootSet Q)

/-- **Corollary 2.3.14, injectivity** (Chenevier–Lannes, p. 40; named statement, not proved): if two even unimodular
lattices $L, L'$ of dimension $24$ have roots and isometric root lattices $Q(R(L)) \cong Q(R(L'))$ (equivalently,
isomorphic root systems, §2.3, p. 34), then $L \cong L'$. Here the isometry is a $\mathbb{Z}$-linear bijection
$f : Q(R(L)) \to Q(R(L'))$ with $Q'(f(x)) = Q(x)$. The book proves it with the uniqueness of the Lagrangians of the
Venkov module (Proposition 2.3.13 (b), case by case); not formalized here. -/
@[kb "chenevierlannes2019" "Cor. 2.3.14, p. 40 (injectivity)"]
def NiemeierRootLatticeDetermines : Prop :=
  ∀ Q Q' : QuadForm ℤ 24, IsEvenUnimodular Q → IsEvenUnimodular Q' → (rootSet Q).Nonempty →
    (∃ f : rootLattice Q ≃ₗ[ℤ] rootLattice Q', ∀ x : rootLattice Q, Q'.eval (f x) = Q.eval x) → IntEquiv Q Q'

end QuadFormsKB.ChenevierLannes
