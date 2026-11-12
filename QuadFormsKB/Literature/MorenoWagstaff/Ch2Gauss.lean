/-
# Moreno–Wagstaff 2005, §2.10: Gauss's three-square theorem via Hurwitz class numbers

**Source.** C. J. Moreno and S. S. Wagstaff Jr., *Sums of Squares of Integers* (2005), Theorem 2.8
(Gauss, *Disquisitiones* Art. 291; p. 50–54).

**Proves**
* `theorem28` (**proved**, unconditional): for every $k \equiv 3 \pmod 8$, $\rho_3(k) = H(k)$ and
  $r_3(k) = 8H(k)$.

**Method.** The book's Kronecker-style counting proof, using Lemma 2.6 (`lemma26`) and Remark 2.1
(`remark21`), pp. 50–54. The key identity (2.39) is $\sigma(n) = \sum_{x > 0 \text{ odd}} H(4n - x^2)$ for odd
$n > 0$ (`Gauss.main_identity`). It is proved by a chain of explicit bijections between finite sets of integer
quadruples: the solutions $(a,b,c,x)$ are traded (via $y = (b+x)/2$, $z = (b-x)/2$) for
$T = \{n = ac - yz, \dots\}$, half of which is a set $A$; $A = B \setminus C$ with $B \cong D$ and
$C \cong 2F$; $D$ has $\sigma(n)$ elements with $u = 0$ plus $2|E|$ others, and $|E| = |F|$ by Lemma 2.6
(summed over the pairs $(u, a)$). Then $\rho_4(4n) = \sigma(n)$ (Remark 2.1) and strong induction on
$k \equiv 3 \pmod 8$ gives $\rho_3(k) = H(k)$ (`Gauss.rho3_eq_hurwitz`), and finally $r_3(k) = 8\rho_3(k)$ by
choosing signs.

**Notes on the book's proof.**
* The sets $T, A, B, C$ (p. 51) use $y \not\equiv z \pmod 2$ (as printed on the scan; the machine-read text
  drops the slash and reads "$y \equiv z$").
* *Erratum:* in the set $F$ (p. 53) the book prints "$u > |w|$"; it must be $u > |v|$ (the condition derived
  two lines earlier). Also p. 52: "$= u^2 + au + uw$" should read $u^2 + av + uw$ (the set $D$ just below has
  the correct form).
-/
import QuadFormsKB.Literature.MorenoWagstaff.Ch2Proofs
import QuadFormsKB.Literature.MorenoWagstaff.Ch2ProofsD

namespace QuadFormsKB.MorenoWagstaff

open scoped ArithmeticFunction.sigma
open QuadFormsKB.Siegel

namespace Gauss

open Set

/-! ### Generic helpers -/

lemma ncard_eq_of_inv {α β : Type*} {s : Set α} {t : Set β} (f : α → β) (g : β → α)
    (hf : ∀ a ∈ s, f a ∈ t) (hg : ∀ b ∈ t, g b ∈ s)
    (h1 : ∀ a ∈ s, g (f a) = a) (h2 : ∀ b ∈ t, f (g b) = b) : s.ncard = t.ncard := by
  refine Set.ncard_congr (fun a _ => f a) hf ?_ ?_
  · intro a b ha hb h
    rw [← h1 a ha, ← h1 b hb]
    exact congrArg g h
  · intro b hb
    exact ⟨g b, hg b hb, h2 b hb⟩

lemma finite_of_inv {α β : Type*} {s : Set α} {t : Set β} (f : α → β) (g : β → α)
    (hg : ∀ b ∈ t, g b ∈ s) (h2 : ∀ b ∈ t, f (g b) = b) (hs : s.Finite) : t.Finite :=
  (hs.image f).subset fun b hb => ⟨g b, hg b hb, h2 b hb⟩

lemma ncard_split {α : Type*} {s s1 s2 : Set α} (hs : s.Finite) (h : s = s1 ∪ s2)
    (hd : Disjoint s1 s2) : s.ncard = s1.ncard + s2.ncard := by
  subst h
  exact Set.ncard_union_eq hd (hs.subset subset_union_left) (hs.subset subset_union_right)

/-- Counting a family of finite fibres over a finite index set. -/
lemma ncard_fibers {α β : Type*} (F : Finset α) (f : α → Set β) (hf : ∀ x ∈ F, (f x).Finite) :
    {p : α × β | p.1 ∈ F ∧ p.2 ∈ f p.1}.Finite ∧
      {p : α × β | p.1 ∈ F ∧ p.2 ∈ f p.1}.ncard = ∑ x ∈ F, (f x).ncard := by
  classical
  revert hf
  induction F using Finset.induction_on with
  | empty => intro _; simp
  | insert x F hx ih =>
    intro hf
    have ih := ih (fun y hy => hf y (Finset.mem_insert_of_mem hy))
    have e : {p : α × β | p.1 ∈ insert x F ∧ p.2 ∈ f p.1} =
        (fun y => (x, y)) '' f x ∪ {p : α × β | p.1 ∈ F ∧ p.2 ∈ f p.1} := by
      ext ⟨a, b⟩
      simp only [Set.mem_ofPred_eq, Finset.mem_insert, Set.mem_union, Set.mem_image, Prod.mk.injEq]
      constructor
      · rintro ⟨h | h, hb⟩
        · subst h; exact Or.inl ⟨b, hb, rfl, rfl⟩
        · exact Or.inr ⟨h, hb⟩
      · rintro (⟨y, hy, rfl, rfl⟩ | ⟨h, hb⟩)
        · exact ⟨Or.inl rfl, hy⟩
        · exact ⟨Or.inr h, hb⟩
    have hd : Disjoint ((fun y => (x, y)) '' f x) {p : α × β | p.1 ∈ F ∧ p.2 ∈ f p.1} := by
      rw [Set.disjoint_left]
      rintro ⟨a, b⟩ ⟨y, hy, h⟩ ⟨ha, _⟩
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact hx ha
    have hfin : ((fun y => (x, y)) '' f x).Finite := (hf x (Finset.mem_insert_self _ _)).image _
    rw [e]
    refine ⟨hfin.union ih.1, ?_⟩
    rw [Set.ncard_union_eq hd hfin ih.1, Finset.sum_insert hx, ih.2,
      Set.ncard_image_of_injective _ (fun y y' h => by simpa using h)]

lemma mul_par (x y : ℤ) : (x * y) % 2 = 1 ↔ (x % 2 = 1 ∧ y % 2 = 1) := by
  rw [Int.mul_emod]
  rcases Int.emod_two_eq_zero_or_one x with h | h <;>
    rcases Int.emod_two_eq_zero_or_one y with h' | h' <;> simp [h, h']

/-! ### The sets of the proof (all for a fixed integer `n`) -/

/-- $T = \{(a,c,y,z) : n = ac - yz,\ 0 < y+z < 2a,\ y+z < 2c,\ y \not\equiv z \pmod 2\}$.
(Printed correctly on p. 51 of the scan; the machine-read text drops the slash of $\not\equiv$.) -/
def Tset (n : ℤ) : Set (ℤ × ℤ × ℤ × ℤ) :=
  {p | n = p.1 * p.2.1 - p.2.2.1 * p.2.2.2 ∧ 0 < p.2.2.1 + p.2.2.2 ∧ p.2.2.1 + p.2.2.2 < 2 * p.1 ∧
    p.2.2.1 + p.2.2.2 < 2 * p.2.1 ∧ (p.2.2.1 - p.2.2.2) % 2 = 1}

/-- $T \cap \{y > z\}$ (this is $x = y - z > 0$). -/
def Tpos (n : ℤ) : Set (ℤ × ℤ × ℤ × ℤ) := Tset n ∩ {p | p.2.2.2 < p.2.2.1}

/-- $T \cap \{y < z\}$. -/
def Tneg (n : ℤ) : Set (ℤ × ℤ × ℤ × ℤ) := Tset n ∩ {p | p.2.2.1 < p.2.2.2}

/-- $A = T \cap \{a - y < c - z\}$. -/
def Aset (n : ℤ) : Set (ℤ × ℤ × ℤ × ℤ) := Tset n ∩ {p | p.1 - p.2.2.1 < p.2.1 - p.2.2.2}

/-- $A' = T \cap \{c - z < a - y\}$. -/
def Aset' (n : ℤ) : Set (ℤ × ℤ × ℤ × ℤ) := Tset n ∩ {p | p.2.1 - p.2.2.2 < p.1 - p.2.2.1}

/-- $B = \{(a,c,y,z) : n = ac - yz,\ 0 < y+z < 2a,\ |a - y| < c - z,\ y \not\equiv z \pmod 2\}$. -/
def Bset (n : ℤ) : Set (ℤ × ℤ × ℤ × ℤ) :=
  {p | n = p.1 * p.2.1 - p.2.2.1 * p.2.2.2 ∧ 0 < p.2.2.1 + p.2.2.2 ∧ p.2.2.1 + p.2.2.2 < 2 * p.1 ∧
    |p.1 - p.2.2.1| < p.2.1 - p.2.2.2 ∧ (p.2.2.1 - p.2.2.2) % 2 = 1}

/-- $C = B \cap \{y + z > 2c\}$. -/
def Cset (n : ℤ) : Set (ℤ × ℤ × ℤ × ℤ) := Bset n ∩ {p | 2 * p.2.1 < p.2.2.1 + p.2.2.2}

/-- $C' = \{(c,u,v,w) : n = u^2 + cv + uw,\ |c| < w,\ |v| < u,\ w \not\equiv c \pmod 2\}$. -/
def C'set (n : ℤ) : Set (ℤ × ℤ × ℤ × ℤ) :=
  {p | n = p.2.1 ^ 2 + p.1 * p.2.2.1 + p.2.1 * p.2.2.2 ∧ |p.1| < p.2.2.2 ∧ |p.2.2.1| < p.2.1 ∧
    (p.2.2.2 - p.1) % 2 = 1}

/-- $F = \{(c,u,v,w) : n - u^2 = cv + uw,\ w > c > 0,\ u > |v|,\ c \text{ odd},\ w \text{ even}\}$.
*Erratum:* the book (p. 53) prints "$u > |w|$"; it must be $u > |v|$. -/
def Fset (n : ℤ) : Set (ℤ × ℤ × ℤ × ℤ) :=
  {p | n - p.2.1 ^ 2 = p.1 * p.2.2.1 + p.2.1 * p.2.2.2 ∧ p.1 < p.2.2.2 ∧ 0 < p.1 ∧
    |p.2.2.1| < p.2.1 ∧ p.1 % 2 = 1 ∧ p.2.2.2 % 2 = 0}

/-- $F^- = C' \cap \{c < 0\}$. -/
def Fneg (n : ℤ) : Set (ℤ × ℤ × ℤ × ℤ) := C'set n ∩ {p | p.1 < 0}

/-- $D = \{(a,u,v,w) : n = u^2 + av + uw,\ |w| < a,\ |u| < v,\ a \not\equiv w \pmod 2\}$. -/
def Dset (n : ℤ) : Set (ℤ × ℤ × ℤ × ℤ) :=
  {p | n = p.2.1 ^ 2 + p.1 * p.2.2.1 + p.2.1 * p.2.2.2 ∧ |p.2.2.2| < p.1 ∧ |p.2.1| < p.2.2.1 ∧
    (p.1 - p.2.2.2) % 2 = 1}

/-- $D \cap \{u = 0\}$. -/
def D0set (n : ℤ) : Set (ℤ × ℤ × ℤ × ℤ) := Dset n ∩ {p | p.2.1 = 0}

/-- $E = D \cap \{u > 0\}$. -/
def Eset (n : ℤ) : Set (ℤ × ℤ × ℤ × ℤ) := Dset n ∩ {p | 0 < p.2.1}

/-- $E^- = D \cap \{u < 0\}$. -/
def Eneg (n : ℤ) : Set (ℤ × ℤ × ℤ × ℤ) := Dset n ∩ {p | p.2.1 < 0}

/-! ### Parity facts -/

lemma T_parity {n a c y z : ℤ} (hn : n % 2 = 1) (h : n = a * c - y * z) (hyz : (y - z) % 2 = 1) :
    a % 2 = 1 ∧ c % 2 = 1 := by
  have h1 := mul_par a c
  have h2 := mul_par y z
  omega

lemma C'_parity {n c u v w : ℤ} (hn : n % 2 = 1) (h : n = u ^ 2 + c * v + u * w)
    (hw : (w - c) % 2 = 1) : c % 2 = 1 ∧ w % 2 = 0 := by
  rw [pow_two] at h
  have h1 := mul_par u u
  have h2 := mul_par c v
  have h3 := mul_par u w
  omega

lemma D_parity {n a u v w : ℤ} (hn : n % 2 = 1) (h : n = u ^ 2 + a * v + u * w)
    (hw : (a - w) % 2 = 1) : a % 2 = 1 ∧ w % 2 = 0 ∧ v % 2 = (u + 1) % 2 := by
  rw [pow_two] at h
  have h1 := mul_par u u
  have h2 := mul_par a v
  have h3 := mul_par u w
  omega

/-! ### $B \cong D$ and the bound on $D$ -/

lemma D_bound {n a u v w : ℤ} (hn : 0 < n) (h : n = u ^ 2 + a * v + u * w) (hw : |w| < a)
    (hu : |u| < v) : a + |u| ≤ n ∧ v ≤ n + n ^ 2 := by
  have ha : 0 < a := lt_of_le_of_lt (abs_nonneg w) hw
  have hv : 0 < v := lt_of_le_of_lt (abs_nonneg u) hu
  have key : a + |u| ≤ a * v + u * w := by
    rcases le_or_gt 0 u with h0 | h0
    · rw [abs_of_nonneg h0] at hu ⊢
      have hw' := (abs_lt.mp hw).1
      nlinarith [mul_nonneg ha.le (show (0:ℤ) ≤ v - u - 1 by omega),
        mul_nonneg h0 (show (0:ℤ) ≤ w + a - 1 by omega)]
    · rw [abs_of_neg h0] at hu ⊢
      have hw' := (abs_lt.mp hw).2
      nlinarith [mul_nonneg ha.le (show (0:ℤ) ≤ v + u - 1 by omega),
        mul_nonneg (show (0:ℤ) ≤ -u by omega) (show (0:ℤ) ≤ a - 1 - w by omega)]
  have h1 : a + |u| ≤ n := by nlinarith [sq_nonneg u]
  refine ⟨h1, ?_⟩
  have hu_n : |u| ≤ n := by linarith [abs_nonneg u]
  have hw_n : |w| ≤ n := by linarith [abs_nonneg u]
  have h2 : |u * w| ≤ n * n := by
    rw [abs_mul]; exact mul_le_mul hu_n hw_n (abs_nonneg _) (by linarith)
  have h3 : -(u * w) ≤ n * n := (neg_le_abs _).trans h2
  have h4 : a * v ≤ n + n * n := by nlinarith [sq_nonneg u]
  nlinarith [mul_le_mul_of_nonneg_right (show (1:ℤ) ≤ a by omega) hv.le]

lemma Dset_finite (n : ℤ) (hn : 0 < n) : (Dset n).Finite := by
  refine ((Finset.Icc 1 n ×ˢ Finset.Icc (-n) n ×ˢ Finset.Icc 1 (n + n ^ 2) ×ˢ
    Finset.Icc (-n) n).finite_toSet).subset ?_
  rintro ⟨a, u, v, w⟩ hp
  simp only [Dset, Set.mem_ofPred_eq] at hp
  obtain ⟨h, hw, hu, -⟩ := hp
  have hb := D_bound hn h hw hu
  have ha : 0 < a := lt_of_le_of_lt (abs_nonneg w) hw
  have hv : 0 < v := lt_of_le_of_lt (abs_nonneg u) hu
  have h1 := abs_lt.mp hw
  have h2 := le_abs_self u
  have h3 := neg_le_abs u
  simp only [Finset.coe_product, Finset.coe_Icc, Set.mem_prod, Set.mem_Icc]
  omega

/-- The map $B \to D$: $(a,c,y,z) \mapsto (a, a-y, c-z, z-a+y)$. -/
def BtoD (p : ℤ × ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ × ℤ :=
  (p.1, p.1 - p.2.2.1, p.2.1 - p.2.2.2, p.2.2.2 - p.1 + p.2.2.1)

/-- The map $D \to B$: $(a,u,v,w) \mapsto (a, u+v+w, a-u, u+w)$. -/
def DtoB (q : ℤ × ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ × ℤ :=
  (q.1, q.2.1 + q.2.2.1 + q.2.2.2, q.1 - q.2.1, q.2.1 + q.2.2.2)

lemma BD (n : ℤ) (hn : 0 < n) : (Bset n).ncard = (Dset n).ncard ∧ (Bset n).Finite := by
  have hf : ∀ p ∈ Bset n, BtoD p ∈ Dset n := by
    rintro ⟨a, c, y, z⟩ hp
    simp only [Bset, Set.mem_ofPred_eq, abs_lt] at hp
    obtain ⟨h, h1, h2, h3, h4⟩ := hp
    simp only [Dset, BtoD, Set.mem_ofPred_eq, abs_lt]
    refine ⟨by linear_combination h, ?_⟩
    omega
  have hg : ∀ q ∈ Dset n, DtoB q ∈ Bset n := by
    rintro ⟨a, u, v, w⟩ hp
    simp only [Dset, Set.mem_ofPred_eq, abs_lt] at hp
    obtain ⟨h, h1, h2, h3⟩ := hp
    simp only [Bset, DtoB, Set.mem_ofPred_eq, abs_lt]
    refine ⟨by linear_combination h, ?_⟩
    omega
  have h1 : ∀ p ∈ Bset n, DtoB (BtoD p) = p := by
    rintro ⟨a, c, y, z⟩ -
    simp only [DtoB, BtoD, Prod.mk.injEq, true_and]
    omega
  have h2 : ∀ q ∈ Dset n, BtoD (DtoB q) = q := by
    rintro ⟨a, u, v, w⟩ -
    simp only [DtoB, BtoD, Prod.mk.injEq, true_and]
    omega
  exact ⟨ncard_eq_of_inv BtoD DtoB hf hg h1 h2, finite_of_inv DtoB BtoD hf h1 (Dset_finite n hn)⟩

/-! ### $A$, $B$, $C$, $T$ -/

lemma A_eq (n : ℤ) : Aset n = Bset n ∩ {p | p.2.2.1 + p.2.2.2 < 2 * p.2.1} := by
  ext ⟨a, c, y, z⟩
  simp only [Aset, Bset, Tset, Set.mem_inter_iff, Set.mem_ofPred_eq, abs_lt]
  constructor
  · rintro ⟨⟨h, h1, h2, h3, h4⟩, h5⟩
    exact ⟨⟨h, h1, h2, by omega, h4⟩, h3⟩
  · rintro ⟨⟨h, h1, h2, h3, h4⟩, h5⟩
    exact ⟨⟨h, h1, h2, h5, h4⟩, by omega⟩

lemma B_split (n : ℤ) : Bset n = Aset n ∪ Cset n ∧ Disjoint (Aset n) (Cset n) := by
  constructor
  · ext ⟨a, c, y, z⟩
    simp only [A_eq, Cset, Bset, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h, h1, h2, h3, h4⟩
      by_cases hc : y + z < 2 * c
      · exact Or.inl ⟨⟨h, h1, h2, h3, h4⟩, hc⟩
      · exact Or.inr ⟨⟨h, h1, h2, h3, h4⟩, by omega⟩
    · rintro (⟨hB, -⟩ | ⟨hB, -⟩) <;> exact hB
  · rw [Set.disjoint_left]
    rintro ⟨a, c, y, z⟩ h1 h2
    simp only [A_eq, Cset, Set.mem_inter_iff, Set.mem_ofPred_eq] at h1 h2
    omega

/-- The swap $(a,c,y,z) \mapsto (c,a,z,y)$. -/
def sw (p : ℤ × ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ × ℤ := (p.2.1, p.1, p.2.2.2, p.2.2.1)

lemma sw_sw (p : ℤ × ℤ × ℤ × ℤ) : sw (sw p) = p := rfl

lemma sw_T {n : ℤ} {p : ℤ × ℤ × ℤ × ℤ} (hp : p ∈ Tset n) : sw p ∈ Tset n := by
  obtain ⟨a, c, y, z⟩ := p
  simp only [Tset, sw, Set.mem_ofPred_eq] at hp ⊢
  obtain ⟨h, h1, h2, h3, h4⟩ := hp
  refine ⟨by linear_combination h, ?_⟩
  omega

lemma sw_Tpos {n : ℤ} {p : ℤ × ℤ × ℤ × ℤ} (hp : p ∈ Tpos n) : sw p ∈ Tneg n := by
  obtain ⟨a, c, y, z⟩ := p
  obtain ⟨h, h'⟩ := hp
  refine ⟨sw_T h, ?_⟩
  simp only [sw, Set.mem_ofPred_eq] at h' ⊢
  exact h'

lemma sw_Tneg {n : ℤ} {p : ℤ × ℤ × ℤ × ℤ} (hp : p ∈ Tneg n) : sw p ∈ Tpos n := by
  obtain ⟨a, c, y, z⟩ := p
  obtain ⟨h, h'⟩ := hp
  refine ⟨sw_T h, ?_⟩
  simp only [sw, Set.mem_ofPred_eq] at h' ⊢
  exact h'

lemma sw_A {n : ℤ} {p : ℤ × ℤ × ℤ × ℤ} (hp : p ∈ Aset n) : sw p ∈ Aset' n := by
  obtain ⟨a, c, y, z⟩ := p
  obtain ⟨h, h'⟩ := hp
  refine ⟨sw_T h, ?_⟩
  simp only [sw, Set.mem_ofPred_eq] at h' ⊢
  exact h'

lemma sw_A' {n : ℤ} {p : ℤ × ℤ × ℤ × ℤ} (hp : p ∈ Aset' n) : sw p ∈ Aset n := by
  obtain ⟨a, c, y, z⟩ := p
  obtain ⟨h, h'⟩ := hp
  refine ⟨sw_T h, ?_⟩
  simp only [sw, Set.mem_ofPred_eq] at h' ⊢
  exact h'

/-- $|T^+| = |A|$ (the book's "$2X_n = |T|$" and "$X_n = |A|$" combined). -/
lemma Tpos_card (n : ℤ) (hn : 0 < n) (hodd : n % 2 = 1) :
    (Tpos n).ncard = (Aset n).ncard := by
  have hAfin : (Aset n).Finite := (BD n hn).2.subset (by rw [A_eq]; exact Set.inter_subset_left)
  have hA'fin : (Aset' n).Finite :=
    finite_of_inv sw sw (fun b hb => sw_A' hb) (fun b _ => sw_sw b) hAfin
  have hT : Tset n = Aset n ∪ Aset' n := by
    ext ⟨a, c, y, z⟩
    simp only [Aset, Aset', Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro hT
      have hT' := hT
      simp only [Tset, Set.mem_ofPred_eq] at hT'
      obtain ⟨h, h1, h2, h3, h4⟩ := hT'
      have := T_parity hodd h h4
      rcases lt_trichotomy (a - y) (c - z) with h5 | h5 | h5
      · exact Or.inl ⟨hT, h5⟩
      · omega
      · exact Or.inr ⟨hT, h5⟩
    · rintro (⟨hT, -⟩ | ⟨hT, -⟩) <;> exact hT
  have hTfin : (Tset n).Finite := by rw [hT]; exact hAfin.union hA'fin
  have hdA : Disjoint (Aset n) (Aset' n) := by
    rw [Set.disjoint_left]
    rintro ⟨a, c, y, z⟩ ⟨-, h1⟩ ⟨-, h2⟩
    simp only [Set.mem_ofPred_eq] at h1 h2
    omega
  have hP : Tset n = Tpos n ∪ Tneg n := by
    ext ⟨a, c, y, z⟩
    simp only [Tpos, Tneg, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro hT
      have hT' := hT
      simp only [Tset, Set.mem_ofPred_eq] at hT'
      obtain ⟨h, h1, h2, h3, h4⟩ := hT'
      rcases lt_trichotomy z y with h5 | h5 | h5
      · exact Or.inl ⟨hT, h5⟩
      · omega
      · exact Or.inr ⟨hT, h5⟩
    · rintro (⟨hT, -⟩ | ⟨hT, -⟩) <;> exact hT
  have hdP : Disjoint (Tpos n) (Tneg n) := by
    rw [Set.disjoint_left]
    rintro ⟨a, c, y, z⟩ ⟨-, h1⟩ ⟨-, h2⟩
    simp only [Set.mem_ofPred_eq] at h1 h2
    omega
  have e1 := ncard_split hTfin hT hdA
  have e2 := ncard_split hTfin hP hdP
  have e3 : (Aset n).ncard = (Aset' n).ncard :=
    ncard_eq_of_inv sw sw (fun a ha => sw_A ha) (fun b hb => sw_A' hb) (fun a _ => sw_sw a)
      (fun b _ => sw_sw b)
  have e4 : (Tpos n).ncard = (Tneg n).ncard :=
    ncard_eq_of_inv sw sw (fun a ha => sw_Tpos ha) (fun b hb => sw_Tneg hb) (fun a _ => sw_sw a)
      (fun b _ => sw_sw b)
  omega

lemma B_card (n : ℤ) (hn : 0 < n) :
    (Bset n).ncard = (Aset n).ncard + (Cset n).ncard :=
  ncard_split (BD n hn).2 (B_split n).1 (B_split n).2

/-! ### $C \cong C' \cong F \sqcup F^-$ -/

/-- $(a,c,y,z) \mapsto (c, c-z, a-y, y+z-c)$. -/
def CtoC' (p : ℤ × ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ × ℤ :=
  (p.2.1, p.2.1 - p.2.2.2, p.1 - p.2.2.1, p.2.2.1 + p.2.2.2 - p.2.1)

/-- $(c,u,v,w) \mapsto (u+v+w, c, u+w, c-u)$. -/
def C'toC (q : ℤ × ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ × ℤ :=
  (q.2.1 + q.2.2.1 + q.2.2.2, q.1, q.2.1 + q.2.2.2, q.1 - q.2.1)

lemma CC' (n : ℤ) (hn : 0 < n) : (Cset n).ncard = (C'set n).ncard ∧ (C'set n).Finite := by
  have hf : ∀ p ∈ Cset n, CtoC' p ∈ C'set n := by
    rintro ⟨a, c, y, z⟩ hp
    simp only [Cset, Bset, Set.mem_inter_iff, Set.mem_ofPred_eq, abs_lt] at hp
    obtain ⟨⟨h, h1, h2, h3, h4⟩, h5⟩ := hp
    simp only [C'set, CtoC', Set.mem_ofPred_eq, abs_lt]
    refine ⟨by linear_combination h, ?_⟩
    omega
  have hg : ∀ q ∈ C'set n, C'toC q ∈ Cset n := by
    rintro ⟨c, u, v, w⟩ hp
    simp only [C'set, Set.mem_ofPred_eq, abs_lt] at hp
    obtain ⟨h, h1, h2, h3⟩ := hp
    simp only [Cset, Bset, C'toC, Set.mem_inter_iff, Set.mem_ofPred_eq, abs_lt]
    refine ⟨⟨by linear_combination h, ?_⟩, ?_⟩ <;> omega
  have h1 : ∀ p ∈ Cset n, C'toC (CtoC' p) = p := by
    rintro ⟨a, c, y, z⟩ -
    simp only [C'toC, CtoC', Prod.mk.injEq, true_and]
    omega
  have h2 : ∀ q ∈ C'set n, CtoC' (C'toC q) = q := by
    rintro ⟨c, u, v, w⟩ -
    simp only [C'toC, CtoC', Prod.mk.injEq, true_and]
    omega
  have hCfin : (Cset n).Finite :=
    (BD n hn).2.subset (fun p hp => hp.1)
  exact ⟨ncard_eq_of_inv CtoC' C'toC hf hg h1 h2, finite_of_inv CtoC' C'toC hg h2 hCfin⟩

/-- $(c,u,v,w) \mapsto (-c,u,-v,w)$. -/
def nu (q : ℤ × ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ × ℤ := (-q.1, q.2.1, -q.2.2.1, q.2.2.2)

lemma nu_nu (q : ℤ × ℤ × ℤ × ℤ) : nu (nu q) = q := by
  obtain ⟨c, u, v, w⟩ := q
  simp [nu]

lemma nu_Fneg {n : ℤ} (hodd : n % 2 = 1) {q : ℤ × ℤ × ℤ × ℤ} (hq : q ∈ Fneg n) : nu q ∈ Fset n := by
  obtain ⟨c, u, v, w⟩ := q
  obtain ⟨hq, hc⟩ := hq
  simp only [C'set, Set.mem_ofPred_eq, abs_lt] at hq hc
  obtain ⟨h, h1, h2, h3⟩ := hq
  have := C'_parity hodd h h3
  simp only [Fset, nu, Set.mem_ofPred_eq, abs_lt]
  refine ⟨by linear_combination h, ?_⟩
  omega

lemma nu_Fset {n : ℤ} {q : ℤ × ℤ × ℤ × ℤ} (hq : q ∈ Fset n) : nu q ∈ Fneg n := by
  obtain ⟨c, u, v, w⟩ := q
  simp only [Fset, Set.mem_ofPred_eq, abs_lt] at hq
  obtain ⟨h, h1, h2, h3, h4, h5⟩ := hq
  simp only [Fneg, C'set, nu, Set.mem_inter_iff, Set.mem_ofPred_eq, abs_lt]
  refine ⟨⟨by linear_combination h, ?_⟩, ?_⟩ <;> omega

lemma C_card (n : ℤ) (hn : 0 < n) (hodd : n % 2 = 1) : (Cset n).ncard = 2 * (Fset n).ncard := by
  obtain ⟨e1, hfin⟩ := CC' n hn
  have hU : C'set n = Fset n ∪ Fneg n := by
    ext ⟨c, u, v, w⟩
    simp only [Fneg, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro hq
      have hq' := hq
      simp only [C'set, Set.mem_ofPred_eq, abs_lt] at hq'
      obtain ⟨h, h1, h2, h3⟩ := hq'
      have := C'_parity hodd h h3
      rcases lt_trichotomy c 0 with h5 | h5 | h5
      · exact Or.inr ⟨hq, h5⟩
      · omega
      · left
        simp only [Fset, Set.mem_ofPred_eq, abs_lt]
        refine ⟨by linear_combination h, ?_⟩
        omega
    · rintro (hq | ⟨hq, -⟩)
      · simp only [Fset, Set.mem_ofPred_eq, abs_lt] at hq
        obtain ⟨h, h1, h2, h3, h4, h5⟩ := hq
        simp only [C'set, Set.mem_ofPred_eq, abs_lt]
        refine ⟨by linear_combination h, ?_⟩
        omega
      · exact hq
  have hd : Disjoint (Fset n) (Fneg n) := by
    rw [Set.disjoint_left]
    rintro ⟨c, u, v, w⟩ h1 ⟨-, h2⟩
    simp only [Fset, Set.mem_ofPred_eq] at h1 h2
    omega
  have e2 := ncard_split hfin hU hd
  have e3 : (Fset n).ncard = (Fneg n).ncard :=
    ncard_eq_of_inv nu nu (fun a ha => nu_Fset ha) (fun b hb => nu_Fneg hodd hb)
      (fun a _ => nu_nu a) (fun b _ => nu_nu b)
  omega

/-! ### $D = D_0 \sqcup E \sqcup E^-$ -/

/-- $(a,u,v,w) \mapsto (a,-u,v,-w)$. -/
def mu (q : ℤ × ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ × ℤ := (q.1, -q.2.1, q.2.2.1, -q.2.2.2)

lemma mu_mu (q : ℤ × ℤ × ℤ × ℤ) : mu (mu q) = q := by
  obtain ⟨a, u, v, w⟩ := q
  simp [mu]

lemma mu_D {n : ℤ} {q : ℤ × ℤ × ℤ × ℤ} (hq : q ∈ Dset n) : mu q ∈ Dset n := by
  obtain ⟨a, u, v, w⟩ := q
  simp only [Dset, mu, Set.mem_ofPred_eq, abs_lt] at hq ⊢
  obtain ⟨h, h1, h2, h3⟩ := hq
  refine ⟨by linear_combination h, ?_⟩
  omega

lemma mu_E {n : ℤ} {q : ℤ × ℤ × ℤ × ℤ} (hq : q ∈ Eset n) : mu q ∈ Eneg n := by
  obtain ⟨a, u, v, w⟩ := q
  obtain ⟨h, h'⟩ := hq
  refine ⟨mu_D h, ?_⟩
  simp only [mu, Set.mem_ofPred_eq] at h' ⊢
  omega

lemma mu_Eneg {n : ℤ} {q : ℤ × ℤ × ℤ × ℤ} (hq : q ∈ Eneg n) : mu q ∈ Eset n := by
  obtain ⟨a, u, v, w⟩ := q
  obtain ⟨h, h'⟩ := hq
  refine ⟨mu_D h, ?_⟩
  simp only [mu, Set.mem_ofPred_eq] at h' ⊢
  omega

lemma D_card (n : ℤ) (hn : 0 < n) :
    (Dset n).ncard = (D0set n).ncard + 2 * (Eset n).ncard := by
  have hfin := Dset_finite n hn
  have hU : Dset n = D0set n ∪ (Eset n ∪ Eneg n) := by
    ext ⟨a, u, v, w⟩
    simp only [D0set, Eset, Eneg, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro hq
      rcases lt_trichotomy u 0 with h5 | h5 | h5
      · exact Or.inr (Or.inr ⟨hq, h5⟩)
      · exact Or.inl ⟨hq, h5⟩
      · exact Or.inr (Or.inl ⟨hq, h5⟩)
    · rintro (⟨hq, -⟩ | ⟨hq, -⟩ | ⟨hq, -⟩) <;> exact hq
  have hd1 : Disjoint (Eset n) (Eneg n) := by
    rw [Set.disjoint_left]
    rintro ⟨a, u, v, w⟩ ⟨-, h1⟩ ⟨-, h2⟩
    simp only [Set.mem_ofPred_eq] at h1 h2
    omega
  have hd2 : Disjoint (D0set n) (Eset n ∪ Eneg n) := by
    rw [Set.disjoint_left]
    rintro ⟨a, u, v, w⟩ ⟨-, h1⟩ (⟨-, h2⟩ | ⟨-, h2⟩) <;>
      simp only [Set.mem_ofPred_eq] at h1 h2 <;> omega
  have hfin2 : (Eset n ∪ Eneg n).Finite := hfin.subset (by rw [hU]; exact Set.subset_union_right)
  have e1 := ncard_split hfin hU hd2
  have e2 := ncard_split hfin2 rfl hd1
  have e3 : (Eset n).ncard = (Eneg n).ncard :=
    ncard_eq_of_inv mu mu (fun a ha => mu_E ha) (fun b hb => mu_Eneg hb) (fun a _ => mu_mu a)
      (fun b _ => mu_mu b)
  omega

/-! ### $|D_0| = \sigma(n)$ -/

/-- The even integers $w$ with $|w| < d$ (for odd $d$): $d$ of them. -/
def Wset (d : ℕ) : Set ℤ := {w | |w| < (d : ℤ) ∧ ((d : ℤ) - w) % 2 = 1}

lemma Wset_finite (d : ℕ) : (Wset d).Finite := by
  refine (Set.finite_Icc (-(d : ℤ)) d).subset ?_
  intro w hw
  simp only [Wset, Set.mem_ofPred_eq, abs_lt] at hw
  exact ⟨by omega, by omega⟩

lemma Wset_card (d : ℕ) (hd : d % 2 = 1) : (Wset d).ncard = d := by
  have : (Wset d).ncard = (↑(Finset.range d) : Set ℕ).ncard := by
    refine ncard_eq_of_inv (fun w => ((w + d - 1) / 2).toNat) (fun j => 2 * (j : ℤ) - d + 1) ?_ ?_ ?_ ?_
    · intro w hw
      simp only [Wset, Set.mem_ofPred_eq, abs_lt] at hw
      simp only [Finset.coe_range, Set.mem_Iio]
      omega
    · intro j hj
      simp only [Finset.coe_range, Set.mem_Iio] at hj
      simp only [Wset, Set.mem_ofPred_eq, abs_lt]
      omega
    · intro w hw
      simp only [Wset, Set.mem_ofPred_eq, abs_lt] at hw
      omega
    · intro j hj
      simp only [Finset.coe_range, Set.mem_Iio] at hj
      omega
  rw [this, Set.ncard_coe_finset, Finset.card_range]

lemma D0_card (n : ℕ) (hn : 0 < n) (hodd : n % 2 = 1) : (D0set (n : ℤ)).ncard = σ 1 n := by
  have hfib := ncard_fibers n.divisors Wset (fun d _ => Wset_finite d)
  have hsum : ∑ d ∈ n.divisors, (Wset d).ncard = σ 1 n := by
    rw [ArithmeticFunction.sigma_one_apply]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hdn := (Nat.mem_divisors.mp hd).1
    have : d % 2 = 1 := Nat.odd_iff.mp (Odd.of_dvd_nat (Nat.odd_iff.mpr hodd) hdn)
    exact Wset_card d this
  rw [← hsum, ← hfib.2]
  refine ncard_eq_of_inv (fun p => (p.1.toNat, p.2.2.2))
    (fun q => ((q.1 : ℤ), 0, (n : ℤ) / q.1, q.2)) ?_ ?_ ?_ ?_
  · rintro ⟨a, u, v, w⟩ hp
    obtain ⟨hq, hu⟩ := hp
    simp only [Dset, Set.mem_ofPred_eq, abs_lt] at hq hu
    obtain ⟨h, h1, h2, h3⟩ := hq
    subst hu
    have ha : (a.toNat : ℤ) = a := Int.toNat_of_nonneg (by omega)
    have hdvd : (a.toNat : ℤ) ∣ (n : ℤ) := ⟨v, by rw [ha]; linarith⟩
    simp only [Set.mem_ofPred_eq, Wset, abs_lt]
    refine ⟨Nat.mem_divisors.mpr ⟨Int.natCast_dvd_natCast.mp hdvd, by omega⟩, ?_⟩
    rw [ha]
    omega
  · rintro ⟨d, w⟩ hq
    simp only [Set.mem_ofPred_eq, Wset, abs_lt] at hq
    obtain ⟨hd, h1, h2⟩ := hq
    obtain ⟨hdn, -⟩ := Nat.mem_divisors.mp hd
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
    have hdvd : (d : ℤ) ∣ (n : ℤ) := Int.natCast_dvd_natCast.mpr hdn
    have hmul : (d : ℤ) * ((n : ℤ) / d) = n := Int.mul_ediv_cancel' hdvd
    have hpos : 0 < (n : ℤ) / d := Int.ediv_pos_of_pos_of_dvd (by omega) (by omega) hdvd
    simp only [D0set, Dset, Set.mem_inter_iff, Set.mem_ofPred_eq, abs_lt]
    refine ⟨⟨?_, ?_⟩, by simp⟩
    · linear_combination -hmul
    · omega
  · rintro ⟨a, u, v, w⟩ hp
    obtain ⟨hq, hu⟩ := hp
    simp only [Dset, Set.mem_ofPred_eq, abs_lt] at hq hu
    obtain ⟨h, h1, h2, h3⟩ := hq
    subst hu
    have ha : (a.toNat : ℤ) = a := Int.toNat_of_nonneg (by omega)
    simp only [Prod.mk.injEq, ha, true_and]
    simp only [Int.zero_pow two_ne_zero, zero_mul, add_zero, zero_add] at h
    rw [h]
    exact ⟨Int.mul_ediv_cancel_left v (show a ≠ 0 by omega), trivial⟩
  · rintro ⟨d, w⟩ -
    simp

/-! ### Lemma 2.6 and $|E| = |F|$ -/

/-- The solution set counted by `phiCount`. -/
def PhiSet (a b α β m : ℤ) : Set (ℤ × ℤ) :=
  {xy | a * xy.1 + b * xy.2 = m ∧ |xy.1| < b ∧ a < xy.2 ∧ xy.1 ≡ α [ZMOD 2] ∧
    xy.2 ≡ β [ZMOD 2] ∧ ¬ xy.2 ≡ a [ZMOD 2 * a]}

lemma phiCount_eq (a b α β m : ℤ) : phiCount a b α β m = (PhiSet a b α β m).ncard :=
  Nat.card_coe_set_eq (PhiSet a b α β m)

lemma PhiSet_finite (a b α β m : ℤ) (ha : 0 < a) (hb : 0 < b) : (PhiSet a b α β m).Finite := by
  refine ((Set.finite_Icc (-b) b).prod (Set.finite_Icc a (|m| + a * b))).subset ?_
  rintro ⟨x, y⟩ hp
  simp only [PhiSet, Set.mem_ofPred_eq, abs_lt] at hp
  obtain ⟨h, ⟨h1, h2⟩, h3, -⟩ := hp
  have e1 : -(a * b) ≤ a * x := by nlinarith
  have e2 : y ≤ b * y := by nlinarith
  have e3 := le_abs_self m
  simp only [Set.mem_prod, Set.mem_Icc]
  refine ⟨⟨by omega, by omega⟩, by omega, ?_⟩
  nlinarith

lemma not_modEq_of_par {x a : ℤ} (h : (x - a) % 2 = 1) : ¬ x ≡ a [ZMOD 2 * a] := by
  intro hm
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hm
  have : (a - x) % 2 = 0 := by rw [hk, mul_assoc]; exact Int.mul_emod_right 2 (a * k)
  omega

lemma F_parity {n u c v w : ℤ} (hn : n % 2 = 1) (h : n - u ^ 2 = c * v + u * w) (hc : c % 2 = 1)
    (hw : w % 2 = 0) : v % 2 = (u + 1) % 2 := by
  rw [pow_two] at h
  have h1 := mul_par u u
  have h2 := mul_par c v
  have h3 := mul_par u w
  omega

lemma F_bound {n c u v w : ℤ} (h : n - u ^ 2 = c * v + u * w) (hcw : c < w) (hc : 0 < c)
    (hv : |v| < u) : c + u ≤ n := by
  have hu : 0 < u := lt_of_le_of_lt (abs_nonneg v) hv
  have hv' := abs_lt.mp hv
  nlinarith [mul_nonneg hc.le (show (0:ℤ) ≤ v + u - 1 by omega),
    mul_nonneg hu.le (show (0:ℤ) ≤ w - c - 1 by omega), sq_nonneg u]

/-- Index set $(u, a)$ for $E$: $1 \le u \le n$, $a$ odd, $1 \le a \le n$. -/
def FE (n : ℤ) : Finset (ℤ × ℤ) := Finset.Icc 1 n ×ˢ (Finset.Icc 1 n).filter (fun a => a % 2 = 1)

/-- Index set $(c, u)$ for $F$. -/
def FF (n : ℤ) : Finset (ℤ × ℤ) := (Finset.Icc 1 n).filter (fun a => a % 2 = 1) ×ˢ Finset.Icc 1 n

/-- Fibre of $E$ over $(u, a)$: pairs $(w, v)$. -/
def fE (n : ℤ) (x : ℤ × ℤ) : Set (ℤ × ℤ) := PhiSet x.1 x.2 0 ((x.1 + 1) % 2) (n - x.1 ^ 2)

/-- Fibre of $F$ over $(c, u)$: pairs $(v, w)$. -/
def fF (n : ℤ) (x : ℤ × ℤ) : Set (ℤ × ℤ) := PhiSet x.1 x.2 ((x.2 + 1) % 2) 0 (n - x.2 ^ 2)

lemma E_card (n : ℤ) (hn : 0 < n) (hodd : n % 2 = 1) :
    (Eset n).ncard = ∑ x ∈ FE n, phiCount x.1 x.2 0 ((x.1 + 1) % 2) (n - x.1 ^ 2) := by
  have hfib := ncard_fibers (FE n) (fE n) (fun x hx => by
    simp only [FE, Finset.mem_product, Finset.mem_Icc, Finset.mem_filter] at hx
    exact PhiSet_finite _ _ _ _ _ (by omega) (by omega))
  have : (Eset n).ncard = {p : (ℤ × ℤ) × (ℤ × ℤ) | p.1 ∈ FE n ∧ p.2 ∈ fE n p.1}.ncard := by
    refine ncard_eq_of_inv (fun q => ((q.2.1, q.1), (q.2.2.2, q.2.2.1)))
      (fun p => (p.1.2, p.1.1, p.2.2, p.2.1)) ?_ ?_ ?_ ?_
    · rintro ⟨a, u, v, w⟩ hp
      obtain ⟨hq, hu⟩ := hp
      simp only [Set.mem_ofPred_eq] at hu
      have hq' := hq
      simp only [Dset, Set.mem_ofPred_eq] at hq'
      obtain ⟨h, hw, huv, h3⟩ := hq'
      have hb := D_bound hn h hw huv
      have hpar := D_parity hodd h h3
      have e1 := abs_nonneg w
      have e2 := le_abs_self u
      have e3 := abs_nonneg u
      have e4 : u < v := by rwa [abs_of_pos hu] at huv
      have hw' := abs_lt.mp hw
      simp only [Set.mem_ofPred_eq, fE, FE, PhiSet, Finset.mem_product, Finset.mem_Icc,
        Finset.mem_filter]
      and_intros
      all_goals first
        | omega
        | (unfold Int.ModEq; omega)
        | exact not_modEq_of_par (by omega)
    · rintro ⟨⟨u, a⟩, ⟨w, v⟩⟩ hq
      simp only [Set.mem_ofPred_eq, fE, FE, PhiSet, Finset.mem_product, Finset.mem_Icc,
        Finset.mem_filter] at hq
      obtain ⟨⟨⟨hu1, hu2⟩, ⟨ha1, ha2⟩, ha3⟩, h, h1, h2, h3, h4, -⟩ := hq
      unfold Int.ModEq at h3 h4
      have h1' := abs_lt.mp h1
      simp only [Eset, Dset, Set.mem_inter_iff, Set.mem_ofPred_eq]
      refine ⟨⟨by linear_combination (-1 : ℤ) * h, ?_, ?_, ?_⟩, ?_⟩
      · exact h1
      · rw [abs_of_pos (by omega)]; exact h2
      · omega
      · omega
    · rintro ⟨a, u, v, w⟩ -
      rfl
    · rintro ⟨⟨u, a⟩, ⟨w, v⟩⟩ -
      rfl
  rw [this, hfib.2]
  exact Finset.sum_congr rfl fun x _ => (phiCount_eq _ _ _ _ _).symm

lemma F_card (n : ℤ) (_hn : 0 < n) (hodd : n % 2 = 1) :
    (Fset n).ncard = ∑ x ∈ FF n, phiCount x.1 x.2 ((x.2 + 1) % 2) 0 (n - x.2 ^ 2) := by
  have hfib := ncard_fibers (FF n) (fF n) (fun x hx => by
    simp only [FF, Finset.mem_product, Finset.mem_Icc, Finset.mem_filter] at hx
    exact PhiSet_finite _ _ _ _ _ (by omega) (by omega))
  have : (Fset n).ncard = {p : (ℤ × ℤ) × (ℤ × ℤ) | p.1 ∈ FF n ∧ p.2 ∈ fF n p.1}.ncard := by
    refine ncard_eq_of_inv (fun q => ((q.1, q.2.1), (q.2.2.1, q.2.2.2)))
      (fun p => (p.1.1, p.1.2, p.2.1, p.2.2)) ?_ ?_ ?_ ?_
    · rintro ⟨c, u, v, w⟩ hq
      simp only [Fset, Set.mem_ofPred_eq] at hq
      obtain ⟨h, hcw, hc, hv, hc2, hw2⟩ := hq
      have hb := F_bound h hcw hc hv
      have hpar := F_parity hodd h hc2 hw2
      have hu : 0 < u := lt_of_le_of_lt (abs_nonneg v) hv
      have hv' := abs_lt.mp hv
      simp only [Set.mem_ofPred_eq, fF, FF, PhiSet, Finset.mem_product, Finset.mem_Icc,
        Finset.mem_filter]
      and_intros
      all_goals first
        | omega
        | (unfold Int.ModEq; omega)
        | exact not_modEq_of_par (by omega)
    · rintro ⟨⟨c, u⟩, ⟨v, w⟩⟩ hq
      simp only [Set.mem_ofPred_eq, fF, FF, PhiSet, Finset.mem_product, Finset.mem_Icc,
        Finset.mem_filter] at hq
      obtain ⟨⟨⟨⟨hc1, hc2⟩, hc3⟩, hu1, hu2⟩, h, h1, h2, h3, h4, -⟩ := hq
      unfold Int.ModEq at h3 h4
      simp only [Fset, Set.mem_ofPred_eq]
      refine ⟨by linear_combination (-1 : ℤ) * h, h2, by omega, h1, hc3, by omega⟩
    · rintro ⟨a, u, v, w⟩ -
      rfl
    · rintro ⟨⟨u, a⟩, ⟨w, v⟩⟩ -
      rfl
  rw [this, hfib.2]
  exact Finset.sum_congr rfl fun x _ => (phiCount_eq _ _ _ _ _).symm

/-- $|E| = |F|$, by Lemma 2.6 applied fibre by fibre. -/
lemma E_eq_F (n : ℤ) (hn : 0 < n) (hodd : n % 2 = 1) : (Eset n).ncard = (Fset n).ncard := by
  rw [E_card n hn hodd, F_card n hn hodd, FE, FF, Finset.sum_product, Finset.sum_product,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun a ha => ?_
  simp only [Finset.mem_Icc, Finset.mem_filter] at hu ha
  exact lemma26 a u _ 0 ((a + 1) % 2) (by omega) (by omega) (by simp) (by
    rcases Int.emod_two_eq_zero_or_one (a + 1) with h | h <;> simp [h])

/-! ### Hurwitz triples and the main identity -/

/-- The set of triples counted by $H(j)$. -/
def Hset (j : ℤ) : Set (ℤ × ℤ × ℤ) :=
  {t | j = 4 * t.1 * t.2.2 - t.2.1 ^ 2 ∧ 0 < t.2.1 ∧ t.2.1 < 2 * t.1 ∧ t.2.1 < 2 * t.2.2 ∧
    Odd t.2.1}

lemma hurwitz_eq (j : ℤ) : hurwitzTriples j = (Hset j).ncard := by
  unfold hurwitzTriples
  exact Nat.card_coe_set_eq (Hset j)

lemma H_pos {j a b c : ℤ} (h : j = 4 * a * c - b ^ 2) (hb : 0 < b) (h1 : b < 2 * a)
    (h2 : b < 2 * c) : 0 < j := by
  have e1 : 0 < 2 * a - b := by omega
  have e2 : 0 < 2 * c - b := by omega
  nlinarith [mul_pos e1 e2, mul_pos hb e1, mul_pos hb e2]

lemma H_bound {j a b c : ℤ} (h : j = 4 * a * c - b ^ 2) (hb : 0 < b) (h1 : b < 2 * a)
    (h2 : b < 2 * c) : 2 * a ≤ j ∧ 2 * c ≤ j := by
  have e1 : 0 ≤ 2 * a - b - 1 := by omega
  have e2 : 0 ≤ 2 * c - b - 1 := by omega
  have e3 : 0 ≤ b - 1 := by omega
  have k1 : j - 2 * a = (2 * a - b) * (2 * c - b) + (2 * a - b) * (b - 1) + b * (2 * c - b - 1) := by
    rw [h]; ring
  have k2 : j - 2 * c = (2 * a - b) * (2 * c - b) + (2 * c - b) * (b - 1) + b * (2 * a - b - 1) := by
    rw [h]; ring
  have p1 : 0 ≤ (2 * a - b) * (2 * c - b) := mul_nonneg (by omega) (by omega)
  have p2 : 0 ≤ (2 * a - b) * (b - 1) := mul_nonneg (by omega) e3
  have p3 : 0 ≤ b * (2 * c - b - 1) := mul_nonneg hb.le e2
  have p4 : 0 ≤ (2 * c - b) * (b - 1) := mul_nonneg (by omega) e3
  have p5 : 0 ≤ b * (2 * a - b - 1) := mul_nonneg hb.le e1
  constructor <;> linarith

lemma Hset_finite (j : ℤ) : (Hset j).Finite := by
  refine ((Set.finite_Icc 0 j).prod ((Set.finite_Icc 0 j).prod (Set.finite_Icc 0 j))).subset ?_
  rintro ⟨a, b, c⟩ hp
  simp only [Hset, Set.mem_ofPred_eq] at hp
  obtain ⟨h, hb, h1, h2, -⟩ := hp
  have := H_bound h hb h1 h2
  simp only [Set.mem_prod, Set.mem_Icc]
  omega

lemma Hset_empty {j : ℤ} (hj : j ≤ 0) : Hset j = ∅ := by
  ext ⟨a, b, c⟩
  simp only [Hset, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨h, hb, h1, h2, -⟩
  have := H_pos h hb h1 h2
  omega

lemma hurwitz_nonpos {j : ℤ} (hj : j ≤ 0) : hurwitzTriples j = 0 := by
  rw [hurwitz_eq, Hset_empty hj]; simp

/-- Odd positive $x \le 4n$: the index set for $X_n$. -/
def Fx (n : ℤ) : Finset ℤ := (Finset.Icc 1 (4 * n)).filter (fun x => x % 2 = 1)

/-- The set of pairs $(x, (a,b,c))$ with $x > 0$ odd and $(a,b,c)$ counted by $H(4n - x^2)$. -/
def S1 (n : ℤ) : Set (ℤ × ℤ × ℤ × ℤ) := {p | p.1 ∈ Fx n ∧ p.2 ∈ Hset (4 * n - p.1 ^ 2)}

lemma S1_card (n : ℤ) (_hn : 0 < n) : (S1 n).ncard = (Tpos n).ncard := by
  refine ncard_eq_of_inv (fun p => (p.2.1, p.2.2.2, (p.2.2.1 + p.1) / 2, (p.2.2.1 - p.1) / 2))
    (fun q => (q.2.2.1 - q.2.2.2, q.1, q.2.2.1 + q.2.2.2, q.2.1)) ?_ ?_ ?_ ?_
  · rintro ⟨x, a, b, c⟩ hp
    simp only [S1, Fx, Hset, Set.mem_ofPred_eq, Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨hx1, hx2⟩, hx3⟩, h, hb, h1, h2, h3⟩ := hp
    rw [Int.odd_iff] at h3
    have hy : 2 * ((b + x) / 2) = b + x := by omega
    have hz : 2 * ((b - x) / 2) = b - x := by omega
    simp only [Tpos, Tset, Set.mem_inter_iff, Set.mem_ofPred_eq]
    generalize (b + x) / 2 = y at *
    generalize (b - x) / 2 = z at *
    have h4 : 4 * n = 4 * (a * c - y * z) := by
      linear_combination h + (2 * z) * hy + (b + x) * hz
    refine ⟨⟨by omega, ?_⟩, ?_⟩ <;> omega
  · rintro ⟨a, c, y, z⟩ hp
    simp only [Tpos, Tset, Set.mem_inter_iff, Set.mem_ofPred_eq] at hp
    obtain ⟨⟨hT, h1, h2, h3, h4⟩, h5⟩ := hp
    have h : 4 * n - (y - z) ^ 2 = 4 * a * c - (y + z) ^ 2 := by linear_combination 4 * hT
    have hpos := H_pos h h1 h2 h3
    have hx : y - z ≤ (y - z) ^ 2 := by nlinarith
    simp only [S1, Fx, Hset, Set.mem_ofPred_eq, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨⟨by omega, by omega⟩, by omega⟩, h, h1, h2, h3, ?_⟩
    rw [Int.odd_iff]; omega
  · rintro ⟨x, a, b, c⟩ hp
    simp only [S1, Fx, Hset, Set.mem_ofPred_eq, Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨hx1, hx2⟩, hx3⟩, h, hb, h1, h2, h3⟩ := hp
    rw [Int.odd_iff] at h3
    simp only [Prod.mk.injEq, true_and, and_true]
    omega
  · rintro ⟨a, c, y, z⟩ -
    simp only [Prod.mk.injEq, true_and]
    omega

/-- **The main identity (2.39)**: $\sigma(n) = \sum_{x > 0 \text{ odd}} H(4n - x^2)$ for odd $n > 0$. -/
theorem main_identity (n : ℕ) (hn : 0 < n) (hodd : n % 2 = 1) :
    ∑ x ∈ Fx n, hurwitzTriples (4 * (n : ℤ) - x ^ 2) = σ 1 n := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hodd' : (n : ℤ) % 2 = 1 := by omega
  have hfib := ncard_fibers (Fx n) (fun x => Hset (4 * (n : ℤ) - x ^ 2)) (fun x _ => Hset_finite _)
  have e0 : ∑ x ∈ Fx n, hurwitzTriples (4 * (n : ℤ) - x ^ 2) = (S1 n).ncard := by
    rw [S1]
    simp only [Fx] at hfib ⊢
    rw [hfib.2]
    exact Finset.sum_congr rfl fun x _ => hurwitz_eq _
  have e1 := S1_card n hn'
  have e2 := Tpos_card n hn' hodd'
  have e3 := B_card n hn'
  have e4 := (BD n hn').1
  have e5 := D_card n hn'
  have e6 := D0_card n hn hodd
  have e7 := C_card n hn' hodd'
  have e8 := E_eq_F n hn' hodd'
  omega

/-! ### Step 0: from $\rho_4$ to $\rho_3$ and the induction -/

/-- The set counted by $\rho_k(m)$. -/
def Rset (k : ℕ) (m : ℤ) : Set (Fin k → ℤ) :=
  {x | (∀ i, 0 < x i ∧ Odd (x i)) ∧ ∑ i, x i ^ 2 = m}

lemma oddSqRep_eq (k : ℕ) (m : ℤ) : oddSqRep k m = (Rset k m).ncard := by
  unfold oddSqRep
  exact Nat.card_coe_set_eq (Rset k m)

lemma Rset_le {k : ℕ} {m : ℤ} {x : Fin k → ℤ} (hx : x ∈ Rset k m) (i : Fin k) :
    x i ≤ x i ^ 2 ∧ x i ^ 2 ≤ m := by
  obtain ⟨h1, h2⟩ := hx
  refine ⟨by nlinarith [(h1 i).1], ?_⟩
  rw [← h2]
  exact Finset.single_le_sum (f := fun i => x i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ i)

lemma Rset_finite (k : ℕ) (m : ℤ) : (Rset k m).Finite := by
  refine (Set.finite_Icc (0 : Fin k → ℤ) (fun _ => m)).subset ?_
  intro x hx
  refine ⟨fun i => (hx.1 i).1.le, fun i => ?_⟩
  have := Rset_le hx i
  show x i ≤ m
  omega

lemma Rset_three_nonpos {j : ℤ} (hj : j ≤ 0) : Rset 3 j = ∅ := by
  ext x
  simp only [Rset, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨h1, h2⟩
  have a0 := (h1 0).1
  have a1 := (h1 1).1
  have a2 := (h1 2).1
  rw [Fin.sum_univ_three] at h2
  nlinarith

lemma oddSqRep_three_nonpos {j : ℤ} (hj : j ≤ 0) : oddSqRep 3 j = 0 := by
  rw [oddSqRep_eq, Rset_three_nonpos hj]; simp

/-- $\rho_4(4n) = \sum_{x > 0 \text{ odd}} \rho_3(4n - x^2)$: split off the first coordinate. -/
lemma rho4_sum (n : ℕ) :
    oddSqRep 4 (4 * (n : ℤ)) = ∑ x ∈ Fx n, oddSqRep 3 (4 * (n : ℤ) - x ^ 2) := by
  have hfib := ncard_fibers (Fx n) (fun x => Rset 3 (4 * (n : ℤ) - x ^ 2))
    (fun x _ => Rset_finite _ _)
  have : (Rset 4 (4 * (n : ℤ))).ncard =
      {p : ℤ × (Fin 3 → ℤ) | p.1 ∈ Fx n ∧ p.2 ∈ Rset 3 (4 * (n : ℤ) - p.1 ^ 2)}.ncard := by
    refine ncard_eq_of_inv (fun x => (x 0, fun i => x i.succ))
      (fun p => Fin.cons p.1 p.2) ?_ ?_ ?_ ?_
    · intro x hx
      have hle := Rset_le hx 0
      obtain ⟨h1, h2⟩ := hx
      rw [Fin.sum_univ_succ] at h2
      simp only [Fx, Finset.mem_filter, Finset.mem_Icc, Set.mem_ofPred_eq, Rset]
      refine ⟨⟨⟨(h1 0).1, by omega⟩, Int.odd_iff.mp (h1 0).2⟩, fun i => h1 i.succ, by linarith⟩
    · rintro ⟨a, y⟩ hp
      simp only [Fx, Finset.mem_filter, Finset.mem_Icc, Set.mem_ofPred_eq, Rset] at hp
      obtain ⟨⟨⟨ha1, ha2⟩, ha3⟩, hy1, hy2⟩ := hp
      simp only [Set.mem_ofPred_eq, Rset]
      refine ⟨?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using ⟨by omega, Int.odd_iff.mpr ha3⟩
        · simpa using hy1 j
      · rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        linarith
    · intro x _
      exact Fin.cons_self_tail x
    · rintro ⟨a, y⟩ _
      simp
  rw [oddSqRep_eq, this, hfib.2]
  exact Finset.sum_congr rfl fun x _ => oddSqRep_eq _ _ ▸ rfl

lemma sq_mod8_odd (x : ℤ) (h : x % 2 = 1) : x ^ 2 % 8 = 1 := by
  have e : x ^ 2 % 8 = ((x % 8) ^ 2) % 8 := by rw [pow_two, pow_two, Int.mul_emod]
  have : x % 8 = 1 ∨ x % 8 = 3 ∨ x % 8 = 5 ∨ x % 8 = 7 := by omega
  rcases this with h' | h' | h' | h' <;> rw [e, h'] <;> norm_num

lemma sq_mod8_even (x : ℤ) (h : x % 2 = 0) : x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 4 := by
  have e : x ^ 2 % 8 = ((x % 8) ^ 2) % 8 := by rw [pow_two, pow_two, Int.mul_emod]
  have : x % 8 = 0 ∨ x % 8 = 2 ∨ x % 8 = 4 ∨ x % 8 = 6 := by omega
  rcases this with h' | h' | h' | h' <;> rw [e, h'] <;> norm_num

/-- **Strong induction**: $\rho_3(k) = H(k)$ for $k \equiv 3 \pmod 8$. -/
theorem rho3_eq_hurwitz : ∀ k : ℕ, k % 8 = 3 → oddSqRep 3 k = hurwitzTriples k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk
  obtain ⟨n, hn4⟩ : ∃ n : ℕ, k + 1 = 4 * n := ⟨(k + 1) / 4, by omega⟩
  have hnpos : 0 < n := by omega
  have hnodd : n % 2 = 1 := by omega
  have hsig : oddSqRep 4 (4 * (n : ℤ)) = σ 1 n := by
    have := (remark21 n (Nat.odd_iff.mpr hnodd)).2
    exact_mod_cast this
  have hmain := main_identity n hnpos hnodd
  have hr4 := rho4_sum n
  have hsum : ∑ x ∈ Fx n, oddSqRep 3 (4 * (n : ℤ) - x ^ 2) =
      ∑ x ∈ Fx n, hurwitzTriples (4 * (n : ℤ) - x ^ 2) := by rw [← hr4, hsig, hmain]
  have h1mem : (1 : ℤ) ∈ Fx n := by
    simp only [Fx, Finset.mem_filter, Finset.mem_Icc]; omega
  rw [← Finset.add_sum_erase _ _ h1mem, ← Finset.add_sum_erase (Fx n)
    (fun x => hurwitzTriples (4 * (n : ℤ) - x ^ 2)) h1mem] at hsum
  have hrest : ∑ x ∈ (Fx n).erase 1, oddSqRep 3 (4 * (n : ℤ) - x ^ 2) =
      ∑ x ∈ (Fx n).erase 1, hurwitzTriples (4 * (n : ℤ) - x ^ 2) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    obtain ⟨hx1, hx2⟩ := Finset.mem_erase.mp hx
    simp only [Fx, Finset.mem_filter, Finset.mem_Icc] at hx2
    obtain ⟨⟨hxa, hxb⟩, hxc⟩ := hx2
    have hsq := sq_mod8_odd x hxc
    have hx3 : 3 ≤ x := by omega
    have h9 : 9 ≤ x ^ 2 := by nlinarith
    by_cases hj : 4 * (n : ℤ) - x ^ 2 ≤ 0
    · rw [oddSqRep_three_nonpos hj, hurwitz_nonpos hj]
    · rw [not_le] at hj
      have hj' : ((4 * (n : ℤ) - x ^ 2).toNat : ℤ) = 4 * (n : ℤ) - x ^ 2 := Int.toNat_of_nonneg hj.le
      have := ih (4 * (n : ℤ) - x ^ 2).toNat (by omega) (by omega)
      rw [← hj'] 
      exact this
  have hk' : (k : ℤ) = 4 * (n : ℤ) - 1 ^ 2 := by omega
  rw [hk']
  omega

/-! ### $r_3(k) = 8\rho_3(k)$ for $k \equiv 3 \pmod 8$ -/

lemma odd_of_three {k : ℤ} (hk : k % 8 = 3) (x : Fin 3 → ℤ) (h : ∑ i, x i ^ 2 = k) (i : Fin 3) :
    x i % 2 = 1 := by
  rw [Fin.sum_univ_three] at h
  have e : ∀ y : ℤ, (y % 2 = 1 ∧ y ^ 2 % 8 = 1) ∨ (y % 2 = 0 ∧ (y ^ 2 % 8 = 0 ∨ y ^ 2 % 8 = 4)) := by
    intro y
    rcases Int.emod_two_eq_zero_or_one y with h | h
    · exact Or.inr ⟨h, sq_mod8_even y h⟩
    · exact Or.inl ⟨h, sq_mod8_odd y h⟩
  have e0 := e (x 0)
  have e1 := e (x 1)
  have e2 := e (x 2)
  fin_cases i <;> simp <;> omega

lemma abs_mem {k : ℤ} (hk : k % 8 = 3) {x : Fin 3 → ℤ} (hx : ∑ i, x i ^ 2 = k) :
    (fun i => |x i|) ∈ Rset 3 k := by
  have hodd := odd_of_three hk x hx
  refine ⟨fun i => ⟨?_, ?_⟩, ?_⟩
  · have := hodd i
    exact abs_pos.mpr (by omega)
  · have := hodd i
    show Odd |x i|
    rw [Int.odd_iff]
    rcases abs_cases (x i) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega
  · simpa [sq_abs] using hx

lemma sgn_mem {k : ℤ} (b : Fin 3 → Bool) {y : Fin 3 → ℤ} (hy : y ∈ Rset 3 k) :
    (fun i => if b i then y i else -y i) ∈ repSet (sumSq 3) k := by
  rw [mem_repSet_sumSq, ← hy.2]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> ring

lemma r3_eq (k : ℕ) (hk : k % 8 = 3) : repNum (sumSq 3) k = 8 * oddSqRep 3 k := by
  have hk' : (k : ℤ) % 8 = 3 := by omega
  let e : repSet (sumSq 3) (k : ℤ) ≃ (Fin 3 → Bool) × Rset 3 (k : ℤ) :=
    { toFun := fun x => (fun i => decide (0 < x.1 i),
        ⟨fun i => |x.1 i|, abs_mem hk' ((mem_repSet_sumSq _ _).mp x.2)⟩)
      invFun := fun p => ⟨fun i => if p.1 i then p.2.1 i else -p.2.1 i, sgn_mem p.1 p.2.2⟩
      left_inv := by
        rintro ⟨x, hx⟩
        have hodd := odd_of_three hk' x ((mem_repSet_sumSq _ _).mp hx)
        apply Subtype.ext
        funext i
        have := hodd i
        by_cases h : 0 < x i
        · simp [h, abs_of_pos h]
        · simp [h, abs_of_nonpos (not_lt.mp h)]
      right_inv := by
        rintro ⟨b, y, hy⟩
        apply Prod.ext
        · funext i
          have hpos := (hy.1 i).1
          cases hb : b i <;> simp [hb] <;> omega
        · apply Subtype.ext
          funext i
          have hpos := (hy.1 i).1
          cases hb : b i <;> simp [hb, abs_of_pos hpos] }
  have h8 : Nat.card (Fin 3 → Bool) = 8 := by simp [Nat.card_eq_fintype_card]
  unfold repNum
  rw [Nat.card_congr e, Nat.card_prod, h8, oddSqRep_eq, Nat.card_coe_set_eq]

end Gauss

/-- **Moreno–Wagstaff, Theorem 2.8** (Gauss, *Disquisitiones* Art. 291; p. 50), proved unconditionally:
for every $k \equiv 3 \pmod 8$, $\rho_3(k) = H(k)$ and $r_3(k) = 8H(k)$.

The proof is the book's (pp. 50–54): the identity $\sigma(n) = \sum_{x > 0 \text{ odd}} H(4n - x^2)$ for odd
$n$ (`Gauss.main_identity`, by a chain of bijections and Lemma 2.6), combined with
$\rho_4(4n) = \sigma(n)$ (Remark 2.1), gives $\rho_3(k) = H(k)$ by strong induction
(`Gauss.rho3_eq_hurwitz`); then $r_3(k) = 8\rho_3(k)$ by choice of signs (`Gauss.r3_eq`).
*Erratum:* the book's set $T$ should read "$y \not\equiv z \pmod 2$" and its $F$ should read
"$u > |v|$"; see the file header. -/
theorem theorem28 : Theorem28 := by
  intro k hk
  have h := Gauss.rho3_eq_hurwitz k hk
  exact ⟨h, by rw [Gauss.r3_eq k hk, h]⟩

end QuadFormsKB.MorenoWagstaff
