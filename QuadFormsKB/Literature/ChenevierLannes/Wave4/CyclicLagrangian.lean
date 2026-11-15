/-
# Chenevier–Lannes, §3.1: the transverse Lagrangian of $H(\mathbb{Z}/d)$

Source: Chenevier–Lannes 2019 (`chenevierlannes2019`), §3.1, Proposition 3.1.3, p. 46 (and the definitions of §2.1,
pp. 25–27: qe-modules, Lagrangians, the hyperbolic qe-module $H(I) = I \oplus I^\vee$, Proposition-Definition 2.1.3).
Printed page numbers.

For a finite cyclic group $A = \mathbb{Z}/d$ ($d \ge 1$), the hyperbolic qe-module $H(A) = A \oplus A^\vee$, with
$A^\vee = \mathrm{Hom}(A, \mathbb{Q}/\mathbb{Z})$, carries the quadratic linking form $q(x, f) = f(x)$. Identifying
$A^\vee$ with $\mathbb{Z}/d$ by $f \mapsto d\,f(1)$ and the values $\frac1d\mathbb{Z}/\mathbb{Z}$ of $q$ with
$\mathbb{Z}/d$, $H(A)$ becomes $(\mathbb{Z}/d)^2$ with $q(x, y) = xy$ and polar form
$b((x, y), (x', y')) = xy' + x'y$ (`hypQ`, `hypB`). A Lagrangian is a subgroup $I$ with $q(I) = 0$ and $I = I^\perp$
(p. 26); $I$ and $J$ are transverse if $I \cap J = 0$ (Proposition-Definition 2.1.3).

**Proves** (unconditional) Proposition 3.1.3: $A^\vee = 0 \oplus \mathbb{Z}/d$ is the unique Lagrangian of $H(A)$
transverse to the Lagrangian $A = \mathbb{Z}/d \oplus 0$ (`prop_3_1_3`, with `isLagrangian_dual`,
`isLagrangian_A`).
-/
import QuadFormsKB.Citation
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace QuadFormsKB.ChenevierLannes

/-- The quadratic linking form of $H(\mathbb{Z}/d) = \mathbb{Z}/d \oplus (\mathbb{Z}/d)^\vee$, $q(x, f) = f(x)$, in the
coordinates $(x, y) \in (\mathbb{Z}/d)^2$ ($f(1) = y/d$): $q(x, y) = xy \in \mathbb{Z}/d \cong
\tfrac1d\mathbb{Z}/\mathbb{Z}$. -/
def hypQ (d : ℕ) (p : ZMod d × ZMod d) : ZMod d := p.1 * p.2

/-- The associated bilinear form $b(p, p') = q(p + p') - q(p) - q(p') = xy' + x'y$. -/
def hypB (d : ℕ) (p p' : ZMod d × ZMod d) : ZMod d := p.1 * p'.2 + p'.1 * p.2

theorem hypB_eq (d : ℕ) (p p' : ZMod d × ZMod d) :
    hypB d p p' = hypQ d (p + p') - hypQ d p - hypQ d p' := by
  simp only [hypB, hypQ, Prod.fst_add, Prod.snd_add]; ring

/-- **Lagrangians of $H(\mathbb{Z}/d)$** (Chenevier–Lannes, §2.1, p. 26): subgroups $I$ with $q(I) = 0$ and
$I = I^\perp$ for the polar form. -/
@[kb "chenevierlannes2019" "§2.1, p. 26 (Lagrangians of a qe-module; H(Z/d))"]
def IsHypLagrangian (d : ℕ) (I : AddSubgroup (ZMod d × ZMod d)) : Prop :=
  (∀ p ∈ I, hypQ d p = 0) ∧ ∀ p, (∀ p' ∈ I, hypB d p p' = 0) ↔ p ∈ I

/-- The Lagrangian $A = \mathbb{Z}/d \oplus 0$. -/
def lagA (d : ℕ) : AddSubgroup (ZMod d × ZMod d) := (⊤ : AddSubgroup (ZMod d)).prod ⊥

/-- The Lagrangian $A^\vee = 0 \oplus (\mathbb{Z}/d)^\vee$. -/
def lagDual (d : ℕ) : AddSubgroup (ZMod d × ZMod d) := (⊥ : AddSubgroup (ZMod d)).prod ⊤

theorem mem_lagA {d : ℕ} {p : ZMod d × ZMod d} : p ∈ lagA d ↔ p.2 = 0 := by
  simp [lagA, AddSubgroup.mem_prod]

theorem mem_lagDual {d : ℕ} {p : ZMod d × ZMod d} : p ∈ lagDual d ↔ p.1 = 0 := by
  simp [lagDual, AddSubgroup.mem_prod]

/-- $A = \mathbb{Z}/d \oplus 0$ is a Lagrangian of $H(\mathbb{Z}/d)$. -/
theorem isLagrangian_A (d : ℕ) : IsHypLagrangian d (lagA d) := by
  refine ⟨fun p hp => by rw [mem_lagA] at hp; simp [hypQ, hp], fun p => ⟨fun h => ?_, fun hp p' hp' => ?_⟩⟩
  · have := h (1, 0) (mem_lagA.mpr rfl)
    simpa [hypB, mem_lagA] using this
  · rw [mem_lagA] at hp hp'; simp [hypB, hp, hp']

/-- $A^\vee = 0 \oplus (\mathbb{Z}/d)^\vee$ is a Lagrangian of $H(\mathbb{Z}/d)$, transverse to $A$. -/
theorem isLagrangian_dual (d : ℕ) : IsHypLagrangian d (lagDual d) ∧ lagDual d ⊓ lagA d = ⊥ := by
  refine ⟨⟨fun p hp => by rw [mem_lagDual] at hp; simp [hypQ, hp], fun p => ⟨fun h => ?_, fun hp p' hp' => ?_⟩⟩, ?_⟩
  · have := h (0, 1) (mem_lagDual.mpr rfl)
    simpa [hypB, mem_lagDual] using this
  · rw [mem_lagDual] at hp hp'; simp [hypB, hp, hp']
  · rw [eq_bot_iff]
    rintro p ⟨h1, h2⟩
    have h1' : p ∈ lagDual d := h1
    have h2' : p ∈ lagA d := h2
    rw [mem_lagDual] at h1'
    rw [mem_lagA] at h2'
    exact Prod.ext h1' h2'

/-- In $\mathbb{Z}/d$ ($d \ge 1$), a subgroup $S$ whose annihilator $\{t : tS = 0\}$ is $0$ contains $1$. -/
theorem one_mem_of_ann_eq_zero {d : ℕ} [NeZero d] (S : AddSubgroup (ZMod d))
    (hS : ∀ t : ZMod d, (∀ y ∈ S, t * y = 0) → t = 0) : (1 : ZMod d) ∈ S := by
  -- $g$: the least positive integer with $g \in S$
  have hex : ∃ g : ℕ, 0 < g ∧ (g : ZMod d) ∈ S := ⟨d, Nat.pos_of_ne_zero (NeZero.ne d), by simp⟩
  classical
  let g := Nat.find hex
  obtain ⟨hg0, hgS⟩ := Nat.find_spec hex
  have hmin : ∀ m : ℕ, 0 < m → m < g → (m : ZMod d) ∉ S := fun m hm hlt hmS =>
    Nat.find_min hex hlt ⟨hm, hmS⟩
  -- every element of $S$ is a multiple of $g$
  have hmul : ∀ y ∈ S, ∃ q : ℕ, y = (q : ZMod d) * g := by
    intro y hy
    refine ⟨y.val / g, ?_⟩
    have hr : ((y.val % g : ℕ) : ZMod d) ∈ S := by
      have e : ((y.val % g : ℕ) : ZMod d) = y - (y.val / g : ℕ) • (g : ZMod d) := by
        rw [nsmul_eq_mul, ← Nat.cast_mul, eq_sub_iff_add_eq, ← Nat.cast_add, Nat.mod_add_div', ZMod.natCast_zmod_val]
      rw [e]
      exact S.sub_mem hy (S.nsmul_mem hgS _)
    have hr0 : y.val % g = 0 := by
      by_contra h
      exact hmin _ (Nat.pos_of_ne_zero h) (Nat.mod_lt _ hg0) hr
    conv_lhs => rw [← ZMod.natCast_zmod_val y, ← Nat.div_add_mod y.val g, hr0, add_zero, Nat.cast_mul]
    ring
  -- $g \mid d$
  have hgd : g ∣ d := by
    have hd := hmul 0 S.zero_mem
    have hr : ((d % g : ℕ) : ZMod d) ∈ S := by
      have e : ((d % g : ℕ) : ZMod d) = -((d / g : ℕ) • (g : ZMod d)) := by
        rw [nsmul_eq_mul, ← Nat.cast_mul, eq_neg_iff_add_eq_zero, ← Nat.cast_add, Nat.mod_add_div',
          ZMod.natCast_self]
      rw [e]
      exact S.neg_mem (S.nsmul_mem hgS _)
    by_contra h
    exact hmin _ (Nat.pos_of_ne_zero (fun h0 => h (Nat.dvd_of_mod_eq_zero h0))) (Nat.mod_lt _ hg0) hr
  -- $t = d/g$ annihilates $S$, so $t = 0$, i.e. $d \mid d/g$, so $g = 1$
  obtain ⟨e, he⟩ := hgd
  have ht := hS (e : ZMod d) (fun y hy => by
    obtain ⟨q, rfl⟩ := hmul y hy
    rw [mul_left_comm, ← Nat.cast_mul, mul_comm e, ← he, ZMod.natCast_self, mul_zero])
  rw [ZMod.natCast_eq_zero_iff] at ht
  have hd0 : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have he0 : 0 < e := Nat.pos_of_ne_zero (by rintro rfl; simp at he; omega)
  have hg1 : g = 1 := by
    obtain ⟨c, hc⟩ := ht
    rw [he] at hc
    have : g * c = 1 := by
      have : e * (g * c) = e * 1 := by rw [mul_one]; nth_rewrite 2 [hc]; ring
      exact Nat.eq_of_mul_eq_mul_left he0 this
    exact Nat.eq_one_of_mul_eq_one_right this
  have hgS' : ((g : ℕ) : ZMod d) ∈ S := hgS
  rw [hg1, Nat.cast_one] at hgS'
  exact hgS'

/-- **Proposition 3.1.3** (Chenevier–Lannes, p. 46): for a finite cyclic group $A = \mathbb{Z}/d$ ($d \ge 1$),
$A^\vee$ is the unique Lagrangian of the hyperbolic qe-module $H(A)$ transverse to the Lagrangian $A$: a Lagrangian
$I$ with $I \cap A = 0$ is $A^\vee$. Unconditional. *Proof.* The second projection is injective on $I$; its image $S$
has annihilator $0$ (if $tS = 0$ then $(t, 0) \in I^\perp = I$, so $t = 0$ by transversality), hence contains $1$; an
element $(x, 1) \in I$ has $q = x = 0$, so $(0, 1) \in I$, and then $(x, y) - y(0, 1) = (x, 0) \in I \cap A$ gives
$x = 0$. -/
@[kb "chenevierlannes2019" "Prop. 3.1.3, p. 46"]
theorem prop_3_1_3 {d : ℕ} [NeZero d] (I : AddSubgroup (ZMod d × ZMod d)) (hI : IsHypLagrangian d I)
    (htr : I ⊓ lagA d = ⊥) : I = lagDual d := by
  obtain ⟨hiso, hperp⟩ := hI
  have htr' : ∀ x : ZMod d, ((x, 0) : ZMod d × ZMod d) ∈ I → x = 0 := by
    intro x hx
    have : ((x, 0) : ZMod d × ZMod d) ∈ I ⊓ lagA d := ⟨hx, mem_lagA.mpr rfl⟩
    rw [htr, AddSubgroup.mem_bot] at this
    exact congrArg Prod.fst this
  let S : AddSubgroup (ZMod d) := I.map (AddMonoidHom.snd _ _)
  have h1 : (1 : ZMod d) ∈ S := by
    apply one_mem_of_ann_eq_zero
    intro t ht
    apply htr'
    rw [← hperp]
    intro p' hp'
    have : p'.2 ∈ S := ⟨p', hp', rfl⟩
    simp [hypB, ht _ this]
  obtain ⟨⟨x, y⟩, hxy, hy1⟩ := h1
  simp only [AddMonoidHom.coe_snd] at hy1
  subst hy1
  have hx : x = 0 := by simpa [hypQ] using hiso _ hxy
  subst hx
  ext ⟨a, b⟩
  rw [mem_lagDual]
  have h0b : ((0, b) : ZMod d × ZMod d) ∈ I := by
    have := I.nsmul_mem hxy b.val
    simpa [ZMod.natCast_zmod_val] using this
  constructor
  · intro hab
    apply htr'
    have := I.sub_mem hab h0b
    simpa using this
  · rintro rfl
    exact h0b

end QuadFormsKB.ChenevierLannes
