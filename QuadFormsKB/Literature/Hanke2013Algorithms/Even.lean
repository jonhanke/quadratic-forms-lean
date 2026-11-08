/-
# Hanke 2013, §4–§5: even bilinear lattices, $\mathfrak p$-neighbours and residual quadrics

J. Hanke, *Algorithms for computing maximal lattices in bilinear (and quadratic) spaces over number fields*,
Contemp. Math. 587 (2013); source used: arXiv:1208.2481v3 (bib key `hanke2013algorithms`), §4, pp. 15–16, and §5,
pp. 17–19.

**Setting.** $R$ is a commutative ring with an algebra map to the field $F$ (for a number field, $R = \mathcal O_F$),
$2\in F^\times$, $Q$ a quadratic form on the $F$-vector space $V$, and $H(x, y) = Q(x + y) - Q(x) - Q(y)$ its Hessian
bilinear form (Mathlib's `QuadraticMap.polar Q`), so $H(x, x) = 2Q(x)$. $\mathfrak a$ is an $R$-submodule of $F$ (a non-zero
fractional ideal in the paper), $2\mathfrak a = \{2y : y\in\mathfrak a\}$ (`twoA`), $\mathfrak p$ a prime ideal of $R$, and
$\mathfrak a_{\mathfrak p} = \{x\in F : sx\in\mathfrak a\text{ for some }s\notin\mathfrak p\}$ (`locAt`), so that
"$x\in\mathfrak p^{\mathrm{ord}_{\mathfrak p}(2\mathfrak a)}$" is $x\in(2\mathfrak a)_{\mathfrak p}$. $L$ is an $R$-submodule of
$V$; *$\mathfrak a$-valued* for $H$ means $H(L, L)\subseteq\mathfrak a$ (`IsHValued`; the paper's convention that bilinear
notions on a quadratic space refer to $H$).

**Defines** the full and partial $\mathfrak a$-even sublattices (`evenSub`, `evenAtSub`, **Definition 4.1**),
$\mathfrak p$-neighbours (`IsPNeighbor`, **Definition 5.1**), the residual quadric and its singular points
(`IsResidualPoint`, `IsSingularPoint`, **Definition 5.2**, Lemma 5.4).

**Proves** **Remark 4.2** (`remark_4_2`), **Remark 4.3** (`remark_4_3`, `remark_4_3_odd`), **Lemma 4.4** (`lemma_4_4`),
and step 2) of **Theorem 5.6** in part: the lattice $L' = L'' + \mathfrak p^{-1}\vec v_P$ is $\mathfrak a$-valued for $Q$
and contains $L''$ (`theorem_5_6_valued`), and $L\cap L' = L''$ (`theorem_5_6_inter`). The index statements of
Theorem 5.6 and Lemma 4.5 are not formalized.
-/
import Mathlib
import QuadFormsKB.Citation

open QuadraticMap Submodule

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2013Algorithms

variable {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-! ### $2\mathfrak a$ and localization -/

/-- $2\mathfrak a = \{2y : y\in\mathfrak a\}$. -/
def twoA (a : Submodule R F) : Submodule R F := a.map (LinearMap.mulLeft R (2 : F))

theorem mem_twoA {a : Submodule R F} {x : F} : x ∈ twoA a ↔ ⅟(2 : F) * x ∈ a := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [LinearMap.mulLeft_apply, ← mul_assoc] using hy
  · intro h
    exact ⟨⅟(2 : F) * x, h, by simp [LinearMap.mulLeft_apply, ← mul_assoc]⟩

theorem two_mul_mem_twoA {a : Submodule R F} {x : F} (hx : x ∈ a) : 2 * x ∈ twoA a := by
  rw [mem_twoA, ← mul_assoc, invOf_mul_self, one_mul]; exact hx

/-- **The localization** $\mathfrak a_{\mathfrak p} = \{x\in F : sx\in\mathfrak a\text{ for some }s\in R\setminus\mathfrak p\}$, an
$R$-submodule of $F$ ($\mathfrak p$ prime). For a fractional ideal of a Dedekind domain, $x\in\mathfrak a_{\mathfrak p}$ iff
$\mathrm{ord}_{\mathfrak p}(x)\ge\mathrm{ord}_{\mathfrak p}(\mathfrak a)$. -/
def locAt (p : Ideal R) [p.IsPrime] (I : Submodule R F) : Submodule R F where
  carrier := {x | ∃ s : R, s ∉ p ∧ s • x ∈ I}
  add_mem' := by
    rintro x y ⟨s, hs, hsx⟩ ⟨t, ht, hty⟩
    refine ⟨s * t, fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hs ht, ?_⟩
    rw [smul_add, mul_comm s t, mul_smul, mul_comm t s, mul_smul s t]
    exact I.add_mem (I.smul_mem t hsx) (I.smul_mem s hty)
  zero_mem' := ⟨1, fun h => (Ideal.IsPrime.ne_top ‹_›) ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  smul_mem' := by
    rintro c x ⟨s, hs, hsx⟩
    exact ⟨s, hs, by rw [smul_comm]; exact I.smul_mem c hsx⟩

theorem le_locAt (p : Ideal R) [p.IsPrime] (I : Submodule R F) : I ≤ locAt p I := fun x hx =>
  ⟨1, fun h => (Ideal.IsPrime.ne_top ‹_›) ((Ideal.eq_top_iff_one _).2 h), by simpa using hx⟩

/-- **A submodule is the intersection of its localizations at the maximal ideals:** if $x\in I_{\mathfrak m}$ for every
maximal ideal $\mathfrak m$ then $x\in I$ (the ideal $\{r : rx\in I\}$ is not contained in any maximal ideal). -/
theorem mem_of_forall_locAt {I : Submodule R F} {x : F}
    (h : ∀ (m : Ideal R) (hm : m.IsMaximal), haveI := hm.isPrime; x ∈ locAt m I) : x ∈ I := by
  set J : Ideal R := { carrier := {r | r • x ∈ I}
                       add_mem' := fun ha hb => by simp only [Set.mem_setOf_eq, add_smul] at *; exact I.add_mem ha hb
                       zero_mem' := by simp
                       smul_mem' := fun c r hr => by
                         simp only [Set.mem_setOf_eq, smul_eq_mul, mul_smul] at *; exact I.smul_mem c hr }
  by_cases hJ : J = ⊤
  · have : (1 : R) ∈ J := hJ ▸ Submodule.mem_top
    simpa [J] using this
  · obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hJ
    haveI := hm.isPrime
    obtain ⟨s, hs, hsx⟩ := h m hm
    exact absurd (hJm hsx) hs

/-! ### Definition 4.1, Remarks 4.2, 4.3, Lemma 4.4 -/

/-- **$\mathfrak a$-valued for the Hessian form** (Hanke 2013, §1 convention and Definition 4.1, p. 15):
$H(L, L)\subseteq\mathfrak a$. -/
@[kb "hanke2013algorithms" "§1, p. 4 and Def. 4.1, p. 15 (a-valued for the Hessian bilinear form H)"]
def IsHValued (a : Submodule R F) (L : Submodule R V) : Prop := ∀ x ∈ L, ∀ y ∈ L, polar Q x y ∈ a

/-- **$\mathfrak a$-even** (Hanke 2013, Definition 4.1, p. 15): $H(\vec x,\vec x)\in2\mathfrak a$ for all $\vec x\in L$. -/
@[kb "hanke2013algorithms" "Definition 4.1, p. 15 (L is a-even)"]
def IsAEven (a : Submodule R F) (L : Submodule R V) : Prop := ∀ x ∈ L, polar Q x x ∈ twoA a

/-- **$\mathfrak a$-even at $\mathfrak p$** (Hanke 2013, Definition 4.1, p. 15): $H(\vec x,\vec x)\in\mathfrak p^{\mathrm{ord}_{\mathfrak p}(2\mathfrak a)}$
for all $\vec x\in L$, i.e. $H(\vec x,\vec x)\in(2\mathfrak a)_{\mathfrak p}$. -/
@[kb "hanke2013algorithms" "Definition 4.1, p. 15 (L is a-even at p)"]
def IsAEvenAt (a : Submodule R F) (p : Ideal R) [p.IsPrime] (L : Submodule R V) : Prop :=
  ∀ x ∈ L, polar Q x x ∈ locAt p (twoA a)

theorem polar_add_self (x y : V) : polar Q (x + y) (x + y) = polar Q x x + polar Q y y + 2 * polar Q x y := by
  simp only [polar_add_left, polar_add_right, polar_comm Q y x]; ring

/-- **The full $\mathfrak a$-even sublattice** $L^{\mathfrak a\text{-even}} = \{\vec x\in L : H(\vec x,\vec x)\in2\mathfrak a\}$
(Hanke 2013, Definition 4.1, p. 15), a submodule when $L$ is $\mathfrak a$-valued (the paper's argument
$H(\vec x+\vec y,\vec x+\vec y) = H(\vec x,\vec x) + H(\vec y,\vec y) + 2H(\vec x,\vec y)$). -/
@[kb "hanke2013algorithms" "Definition 4.1, p. 15 (L^{a-even})"]
def evenSub {a : Submodule R F} {L : Submodule R V} (hL : IsHValued Q a L) : Submodule R V where
  carrier := {x | x ∈ L ∧ polar Q x x ∈ twoA a}
  add_mem' := by
    rintro x y ⟨hx, hxx⟩ ⟨hy, hyy⟩
    refine ⟨L.add_mem hx hy, ?_⟩
    rw [polar_add_self]
    exact (twoA a).add_mem ((twoA a).add_mem hxx hyy) (two_mul_mem_twoA (hL x hx y hy))
  zero_mem' := ⟨L.zero_mem, by simp⟩
  smul_mem' := by
    rintro c x ⟨hx, hxx⟩
    refine ⟨L.smul_mem c hx, ?_⟩
    have : polar Q (c • x) (c • x) = c • c • polar Q x x := by
      rw [← algebraMap_smul F c x, polar_smul_left, polar_smul_right, smul_eq_mul, smul_eq_mul,
        Algebra.smul_def, Algebra.smul_def]
    rw [this]
    exact (twoA a).smul_mem c ((twoA a).smul_mem c hxx)

/-- **The partial $\mathfrak a$-even sublattice at $\mathfrak p$** $L^{\mathfrak a\text{-even at }\mathfrak p}$ (Hanke 2013,
Definition 4.1, p. 15), a submodule when $L$ is $\mathfrak a$-valued. -/
@[kb "hanke2013algorithms" "Definition 4.1, p. 15 (L^{a-even at p})"]
def evenAtSub {a : Submodule R F} (p : Ideal R) [p.IsPrime] {L : Submodule R V} (hL : IsHValued Q a L) :
    Submodule R V where
  carrier := {x | x ∈ L ∧ polar Q x x ∈ locAt p (twoA a)}
  add_mem' := by
    rintro x y ⟨hx, hxx⟩ ⟨hy, hyy⟩
    refine ⟨L.add_mem hx hy, ?_⟩
    rw [polar_add_self]
    exact (locAt p _).add_mem ((locAt p _).add_mem hxx hyy) (le_locAt p _ (two_mul_mem_twoA (hL x hx y hy)))
  zero_mem' := ⟨L.zero_mem, by simp⟩
  smul_mem' := by
    rintro c x ⟨hx, hxx⟩
    refine ⟨L.smul_mem c hx, ?_⟩
    have : polar Q (c • x) (c • x) = c • c • polar Q x x := by
      rw [← algebraMap_smul F c x, polar_smul_left, polar_smul_right, smul_eq_mul, smul_eq_mul,
        Algebra.smul_def, Algebra.smul_def]
    rw [this]
    exact (locAt p _).smul_mem c ((locAt p _).smul_mem c hxx)

/-- **Remark 4.2** (Hanke 2013, p. 15): an $\mathfrak a$-even lattice is $\mathfrak a$-valued:
$H(\vec x,\vec y) = \frac12\big(H(\vec x+\vec y,\vec x+\vec y) - H(\vec x,\vec x) - H(\vec y,\vec y)\big)\in\frac{2\mathfrak a}2 = \mathfrak a$. -/
@[kb "hanke2013algorithms" "Remark 4.2, p. 15"]
theorem remark_4_2 {a : Submodule R F} {L : Submodule R V} (h : IsAEven Q a L) : IsHValued Q a L := by
  intro x hx y hy
  have h1 := h _ (L.add_mem hx hy)
  have h2 : 2 * polar Q x y = polar Q (x + y) (x + y) - polar Q x x - polar Q y y := by
    rw [polar_add_self]; ring
  have h3 : 2 * polar Q x y ∈ twoA a := by
    rw [h2]; exact (twoA a).sub_mem ((twoA a).sub_mem h1 (h x hx)) (h y hy)
  rw [mem_twoA, ← mul_assoc, invOf_mul_self, one_mul] at h3
  exact h3

/-- **Remark 4.3** (Hanke 2013, p. 15): $L^{\mathfrak a\text{-even}} = \bigcap_{\mathfrak p}L^{\mathfrak a\text{-even at }\mathfrak p}$
(over the maximal ideals $\mathfrak p$; for a Dedekind domain that is not a field these are the non-zero primes). -/
@[kb "hanke2013algorithms" "Remark 4.3, p. 15 (L^{a-even} = ∩_p L^{a-even at p})"]
theorem remark_4_3 [Nontrivial R] {a : Submodule R F} {L : Submodule R V} (hL : IsHValued Q a L) (x : V) :
    x ∈ evenSub Q hL ↔ ∀ (p : Ideal R) (hp : p.IsMaximal), haveI := hp.isPrime; x ∈ evenAtSub Q p hL := by
  constructor
  · rintro ⟨hx, hxx⟩ p hp
    exact ⟨hx, le_locAt p _ hxx⟩
  · intro h
    obtain ⟨m, hm⟩ := Ideal.exists_maximal R
    haveI := hm.isPrime
    exact ⟨(h m hm).1, mem_of_forall_locAt fun p hp => (h p hp).2⟩

/-- **Remark 4.3** (Hanke 2013, p. 15): an $\mathfrak a$-valued $L$ is $\mathfrak a$-even at every $\mathfrak p\nmid2$. -/
@[kb "hanke2013algorithms" "Remark 4.3, p. 15 (L is a-even at all p ∤ 2)"]
theorem remark_4_3_odd {a : Submodule R F} {L : Submodule R V} (hL : IsHValued Q a L) (p : Ideal R) [p.IsPrime]
    (hp : (2 : R) ∉ p) : evenAtSub Q p hL = L := by
  ext x
  refine ⟨fun h => h.1, fun hx => ⟨hx, 2, hp, ?_⟩⟩
  rw [ofNat_smul_eq_nsmul (R := R) (n := 2), ← ofNat_smul_eq_nsmul (R := F) (n := 2), smul_eq_mul]
  exact two_mul_mem_twoA (hL x hx x hx)

/-- **Lemma 4.4** (Hanke 2013, p. 15): $L$ is an $\mathfrak a$-even lattice for the Hessian form $H$ if and only if $L$ is an
$\mathfrak a$-valued quadratic lattice, $Q(L)\subseteq\mathfrak a$ (since $H(\vec x,\vec x) = 2Q(\vec x)$). -/
@[kb "hanke2013algorithms" "Lemma 4.4, p. 15"]
theorem lemma_4_4 (a : Submodule R F) (L : Submodule R V) : IsAEven Q a L ↔ ∀ x ∈ L, Q x ∈ a := by
  have e : ∀ x, polar Q x x ∈ twoA a ↔ Q x ∈ a := fun x => by
    rw [polar_self, mem_twoA, nsmul_eq_mul, Nat.cast_ofNat, ← mul_assoc, invOf_mul_self, one_mul]
  exact forall₂_congr fun x _ => e x

/-! ### Definitions 5.1, 5.2 and Theorem 5.6 (part) -/

/-- **$\mathfrak p$-neighbouring $\mathfrak a$-lattices** (Hanke 2013, Definition 5.1, p. 17): $L$, $L'$ are $\mathfrak a$-valued
quadratic lattices (`valued`, `valued'`: $Q(L), Q(L')\subseteq\mathfrak a$), $[L : L\cap L'] = [L' : L\cap L'] = N(\mathfrak p)$
(`index`, `index'`; $N(\mathfrak p) = \#(R/\mathfrak p)$, indices as `AddSubgroup.relIndex`) and $H(L, L')\not\subseteq\mathfrak a$
(`not_valued`). -/
@[kb "hanke2013algorithms" "Definition 5.1, p. 17"]
structure IsPNeighbor (a : Submodule R F) (p : Ideal R) (L L' : Submodule R V) : Prop where
  valued : ∀ x ∈ L, Q x ∈ a
  valued' : ∀ x ∈ L', Q x ∈ a
  index : (L ⊓ L').toAddSubgroup.relIndex L.toAddSubgroup = Nat.card (R ⧸ p)
  index' : (L ⊓ L').toAddSubgroup.relIndex L'.toAddSubgroup = Nat.card (R ⧸ p)
  not_valued : ∃ x ∈ L, ∃ y ∈ L', polar Q x y ∉ a

/-- **Points of the residual $\mathfrak a$-quadric at $\mathfrak p$** (Hanke 2013, Definition 5.2 and Remark 5.3, pp. 17–18),
in terms of the lattice: $\vec x\in L$ with $\vec x\notin\mathfrak pL$ and $Q(\vec x)\in\mathfrak a\mathfrak p$ (here
$\mathfrak a\mathfrak p$ = `p • a`, $\mathfrak pL$ = `p • L`); the point is the line $\mathbb F_{\mathfrak p}\bar{\vec x}$ in
$L/\mathfrak pL$. -/
@[kb "hanke2013algorithms" "Definition 5.2 and Remark 5.3, pp. 17–18"]
def IsResidualPoint (a : Submodule R F) (p : Ideal R) (L : Submodule R V) (x : V) : Prop :=
  x ∈ L ∧ x ∉ p • L ∧ Q x ∈ p • a

/-- **Singular point** (Hanke 2013, Lemma 5.4, p. 18, the Hessian criterion taken as the definition): the
$(\mathfrak a/\mathfrak a\mathfrak p)$-valued linear form $H(\vec v_P,\cdot)$ vanishes on $L$, i.e. $H(\vec v_P, L)\subseteq\mathfrak a\mathfrak p$. -/
@[kb "hanke2013algorithms" "Lemma 5.4, p. 18 (singular points: H(v_P, ·) ≡ 0 mod ap)"]
def IsSingularPoint (a : Submodule R F) (p : Ideal R) (L : Submodule R V) (x : V) : Prop :=
  ∀ y ∈ L, polar Q x y ∈ p • a

/-- $\mathfrak p^{-1} = \{c\in F : c\,\mathfrak p\subseteq R\}$, as an $R$-submodule of $F$. -/
def pInv (p : Ideal R) : Submodule R F where
  carrier := {c | ∀ r ∈ p, ∃ s : R, c * algebraMap R F r = algebraMap R F s}
  add_mem' := by
    intro c d hc hd r hr
    obtain ⟨s, hs⟩ := hc r hr
    obtain ⟨t, ht⟩ := hd r hr
    exact ⟨s + t, by rw [add_mul, hs, ht, map_add]⟩
  zero_mem' := fun r _ => ⟨0, by simp⟩
  smul_mem' := by
    intro e c hc r hr
    obtain ⟨s, hs⟩ := hc r hr
    exact ⟨e * s, by rw [Algebra.smul_def, mul_assoc, hs, map_mul]⟩

/-- $c\in\mathfrak p^{-1}$, $y\in\mathfrak p\mathfrak a$ gives $cy\in\mathfrak a$. -/
theorem mul_mem_of_mem_pInv {a : Submodule R F} {p : Ideal R} {c y : F} (hc : c ∈ pInv p) (hy : y ∈ p • a) :
    c * y ∈ a := by
  refine Submodule.smul_induction_on (p := fun y => c * y ∈ a) hy (fun r hr z hz => ?_) (fun y z ihy ihz => ?_)
  · obtain ⟨s, hs⟩ := hc r hr
    rw [Algebra.smul_def, ← mul_assoc, hs, ← Algebra.smul_def]
    exact a.smul_mem s hz
  · rw [mul_add]; exact a.add_mem ihy ihz

/-- **The sublattice $L'' = \{\vec x\in L : H(\vec v_P,\vec x)\in\mathfrak a\mathfrak p\}$** (Hanke 2013, Theorem 5.6, p. 18). -/
@[kb "hanke2013algorithms" "Theorem 5.6, p. 18 (L'' = {x ∈ L : H(v_P, x) ≡ 0 mod ap})"]
def nbCore (a : Submodule R F) (p : Ideal R) (L : Submodule R V) (v : V) : Submodule R V where
  carrier := {x | x ∈ L ∧ polar Q v x ∈ p • a}
  add_mem' := by
    rintro x y ⟨hx, hvx⟩ ⟨hy, hvy⟩
    exact ⟨L.add_mem hx hy, by rw [polar_add_right]; exact (p • a).add_mem hvx hvy⟩
  zero_mem' := ⟨L.zero_mem, by simp⟩
  smul_mem' := by
    rintro c x ⟨hx, hvx⟩
    refine ⟨L.smul_mem c hx, ?_⟩
    rw [← algebraMap_smul F c x, polar_smul_right, smul_eq_mul, ← Algebra.smul_def]
    exact (p • a).smul_mem c hvx

/-- **The neighbour** $\eta(P) = L' := L'' + \mathfrak p^{-1}\vec v_P$ (Hanke 2013, Theorem 5.6, p. 18): the sum of $L''$ and
the $R$-module $\{c\,\vec v_P : c\in\mathfrak p^{-1}\}$. -/
@[kb "hanke2013algorithms" "Theorem 5.6, p. 18 (η(P) = L'' + p⁻¹ v_P)"]
def nbLatP (a : Submodule R F) (p : Ideal R) (L : Submodule R V) (v : V) : Submodule R V :=
  nbCore Q a p L v ⊔ (pInv p).map ((LinearMap.toSpanSingleton F V v).restrictScalars R)

theorem mem_pInv_line {p : Ideal R} {v w : V} :
    w ∈ (pInv (F := F) p).map ((LinearMap.toSpanSingleton F V v).restrictScalars R) ↔
      ∃ c ∈ pInv (F := F) p, c • v = w := by
  simp [Submodule.mem_map]

/-- **Theorem 5.6, step 2), valuedness** (Hanke 2013, pp. 18–19): if $L$ is an $\mathfrak a$-valued quadratic lattice
($Q(L)\subseteq\mathfrak a$) and $\vec v_P\in L$ has $Q(\vec v_P)\in\mathfrak p^2\mathfrak a$, then $L' = L'' + \mathfrak p^{-1}\vec v_P$
is an $\mathfrak a$-valued quadratic lattice containing $L''$: $Q(\vec x + c\vec v_P) = Q(\vec x) + cH(\vec x,\vec v_P) +
c^2Q(\vec v_P)$ with each term in $\mathfrak a$. -/
@[kb "hanke2013algorithms" "Theorem 5.6, proof step 2), pp. 18–19 (L' is a-valued)"]
theorem theorem_5_6_valued {a : Submodule R F} {p : Ideal R} {L : Submodule R V} (hL : ∀ x ∈ L, Q x ∈ a)
    {v : V} (hvQ : Q v ∈ p • p • a) :
    nbCore Q a p L v ≤ nbLatP Q a p L v ∧ ∀ w ∈ nbLatP Q a p L v, Q w ∈ a := by
  refine ⟨le_sup_left, fun w hw => ?_⟩
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hw
  obtain ⟨c, hc, rfl⟩ := mem_pInv_line.1 hy
  obtain ⟨hxL, hvx⟩ := hx
  have e : Q (x + c • v) = Q x + c * polar Q v x + c * (c * Q v) := by
    rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, polar_smul_right, polar_comm Q x v, smul_eq_mul, smul_eq_mul]
    ring
  rw [e]
  refine a.add_mem (a.add_mem (hL x hxL) (mul_mem_of_mem_pInv hc hvx)) ?_
  exact mul_mem_of_mem_pInv hc (mul_mem_of_mem_pInv' hc hvQ)
where
  /-- $c\in\mathfrak p^{-1}$, $y\in\mathfrak p(\mathfrak p\mathfrak a)$ gives $cy\in\mathfrak p\mathfrak a$. -/
  mul_mem_of_mem_pInv' {a : Submodule R F} {p : Ideal R} {c y : F} (hc : c ∈ pInv p) (hy : y ∈ p • p • a) :
      c * y ∈ p • a := mul_mem_of_mem_pInv (a := p • a) hc hy

/-- **Theorem 5.6, $L'' = L\cap L'$** (Hanke 2013, p. 18: "and also $L'' = L\cap L'$"): for $\vec v_P\in L$ with
$Q(\vec v_P)\in\mathfrak p^2\mathfrak a$, $L\cap(L'' + \mathfrak p^{-1}\vec v_P) = L''$. *Proof*: for $\vec x = \vec y + c\vec v_P\in L$
($\vec y\in L''$, $c\in\mathfrak p^{-1}$), $H(\vec v_P,\vec x) = H(\vec v_P,\vec y) + 2cQ(\vec v_P)\in\mathfrak a\mathfrak p$. -/
@[kb "hanke2013algorithms" "Theorem 5.6, p. 18 (L'' = L ∩ L')"]
theorem theorem_5_6_inter {a : Submodule R F} {p : Ideal R} {L : Submodule R V} {v : V}
    (hvQ : Q v ∈ p • p • a) : L ⊓ nbLatP Q a p L v = nbCore Q a p L v := by
  apply le_antisymm
  · rintro x ⟨hxL, hx⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, hc, rfl⟩ := mem_pInv_line.1 hz
    refine ⟨hxL, ?_⟩
    rw [polar_add_right, polar_smul_right, polar_self, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
    refine (p • a).add_mem hy.2 ?_
    have h1 : c * Q v ∈ p • a := mul_mem_of_mem_pInv (a := p • a) hc hvQ
    have h2 : (2 : R) • (c * Q v) ∈ p • a := (p • a).smul_mem 2 h1
    rw [ofNat_smul_eq_nsmul (R := R) (n := 2), nsmul_eq_mul, Nat.cast_ofNat] at h2
    convert h2 using 1
    ring
  · exact le_inf (fun x hx => hx.1) le_sup_left

end QuadFormsKB.Hanke2013Algorithms
