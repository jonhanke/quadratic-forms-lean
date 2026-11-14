/-
# Kitaoka 1993, Corollary 3.1.4: square classes of $\mathbb Q_p^\times$

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), Chapter 3, §3.1, Corollary 3.1.4
(printed p. 34; the repository locator is "§3.1, Cor. 3.1.4, p. 62").

**Statement (book's terms).** The group $\mathbb Q_p^\times / (\mathbb Q_p^\times)^2$ has representatives
$1, \varepsilon, p, \varepsilon p$ if $p \ne 2$, and $1, 3, 5, 7, 2\cdot 1, 2\cdot 3, 2\cdot 5, 2\cdot 7$ if
$p = 2$, where $\varepsilon$ is any fixed element of $\mathbb Z_p$ that is not a square modulo $p$.
"Representatives" is formalized faithfully as two facts about the list $R$ of length $4$ (respectively
$8$): (a) completeness, every $x \in \mathbb Q_p^\times$ is $R_i c^2$ for some index $i$ and some
$c \in \mathbb Q_p^\times$; (b) irredundancy, if $R_i = R_j c^2$ with $c \in \mathbb Q_p^\times$ then $i = j$.
Indices are 0-based (the book's list entries are `R 0`, `R 1`, ...). For odd $p$ the hypothesis "not a
square modulo $p$" forces $\varepsilon$ to be a unit (residue $0$ is a square), so no extra hypothesis is
needed (`isUnit_of_not_isSquare_toZMod`).

**Proof sketch** (as in the book). Every $x \in \mathbb Q_p^\times$ is $c^2 p^r u$ with $r \in \{0, 1\}$ and
$u \in \mathbb Z_p^\times$. For $p$ odd, a unit is a square in $\mathbb Q_p$ iff its residue is a square in
$\mathbb F_p$; two non-squares of $\mathbb F_p$ multiply to a square (quadratic character), so $u$ or
$\varepsilon u$ is a square, giving completeness. For irredundancy, $R_i R_j = (R_j c)^2$ is a square
$p^{k} u$, forcing $k$ even and the residue of $u$ a square. For $p = 2$, a unit is a square iff it is
$\equiv 1 \bmod 8$; every odd residue $k$ mod $8$ satisfies $k^2 \equiv 1$, so $u k$ is a square when
$u \equiv k$.

**Repository results used.** `QuadFormsKB.PadicClass.padic_decomp` (the decomposition
$c^2 p^r u$), `QuadFormsKB.HilbertLocal.isSquare_unit_iff`,
`QuadFormsKB.HilbertLocal.isSquare_zpow_mul_unit_iff` (odd $p$),
`QuadFormsKB.HilbertLocal.isSquare_two_adic_unit_iff` and
`QuadFormsKB.HilbertLocal.isSquare_two_zpow_mul_unit_iff` ($p = 2$).

**Lean.** `corollary314_odd` and `corollary314_two` are the two book statements.
-/
import QuadFormsKB.Literature.LocalGlobal.HilbertLocal
import QuadFormsKB.Literature.LocalGlobal.PadicClassification
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import QuadFormsKB.Citation

noncomputable section

namespace QuadFormsKB.Kitaoka

/-- If the residue of $\varepsilon \in \mathbb Z_p$ is not a square in $\mathbb F_p$, then $\varepsilon$ is a
unit of $\mathbb Z_p$ (the residue $0$ is a square). -/
theorem isUnit_of_not_isSquare_toZMod (p : ℕ) [Fact p.Prime] (ε : ℤ_[p])
    (hε : ¬ IsSquare (PadicInt.toZMod ε)) : IsUnit ε := by
  by_contra h
  apply hε
  have hm : ε ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
    rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal]
    exact h
  rw [RingHom.mem_ker] at hm
  exact ⟨0, by rw [hm]; simp⟩

/-- **Kitaoka 1993, Corollary 3.1.4 ($p$ odd).** For an odd prime $p$ and $\varepsilon \in \mathbb Z_p$ whose
residue is not a square modulo $p$, the list $1, \varepsilon, p, \varepsilon p$ is a complete and irredundant
set of representatives of $\mathbb Q_p^\times / (\mathbb Q_p^\times)^2$: every nonzero $x$ equals $R_i c^2$ for
some index $i$ and some $c \ne 0$, and $R_i = R_j c^2$ with $c \ne 0$ forces $i = j$. -/
@[kb "kitaoka1993" "§3.1, Cor. 3.1.4, p. 62"]
theorem corollary314_odd (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (ε : ℤ_[p])
    (hε : ¬ IsSquare (PadicInt.toZMod ε)) :
    let R : Fin 4 → ℚ_[p] := ![1, (ε : ℚ_[p]), (p : ℚ_[p]), (ε : ℚ_[p]) * (p : ℚ_[p])]
    (∀ x : ℚ_[p], x ≠ 0 → ∃ i, ∃ c : ℚ_[p], c ≠ 0 ∧ x = R i * c ^ 2) ∧
    (∀ i j, (∃ c : ℚ_[p], c ≠ 0 ∧ R i = R j * c ^ 2) → i = j) := by
  intro R
  have hεu : IsUnit ε := isUnit_of_not_isSquare_toZMod p ε hε
  set η : ℤ_[p]ˣ := hεu.unit with hη
  have hηv : (η : ℤ_[p]) = ε := hεu.unit_spec
  have hpne : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hε0 : (ε : ℚ_[p]) ≠ 0 := by
    intro h
    have h' : ε = 0 := by simpa using h
    exact hε ⟨0, by rw [h']; simp⟩
  constructor
  · intro x hx
    obtain ⟨c, r, u, hc, hr, hxe⟩ := QuadFormsKB.PadicClass.padic_decomp p x hx
    by_cases hs : IsSquare (PadicInt.toZMod (u : ℤ_[p]))
    · obtain ⟨w, hw⟩ := (QuadFormsKB.HilbertLocal.isSquare_unit_iff hp u).2 hs
      have hw0 : w ≠ 0 := by
        rintro rfl
        simp at hw
      interval_cases r
      · refine ⟨0, c * w, mul_ne_zero hc hw0, ?_⟩
        rw [hxe, hw]
        simp [R]
        ring
      · refine ⟨2, c * w, mul_ne_zero hc hw0, ?_⟩
        rw [hxe, hw]
        simp [R]
        ring
    · have hu0 : PadicInt.toZMod (u : ℤ_[p]) ≠ 0 := by
        intro h
        exact hs ⟨0, by rw [h]; simp⟩
      have he0 : PadicInt.toZMod ε ≠ 0 := by
        intro h
        exact hε ⟨0, by rw [h]; simp⟩
      have h1 : quadraticChar (ZMod p) (PadicInt.toZMod (u : ℤ_[p])) = -1 :=
        quadraticChar_neg_one_iff_not_isSquare.2 hs
      have h2 : quadraticChar (ZMod p) (PadicInt.toZMod ε) = -1 :=
        quadraticChar_neg_one_iff_not_isSquare.2 hε
      have h3 : IsSquare (PadicInt.toZMod (u : ℤ_[p]) * PadicInt.toZMod ε) := by
        rw [← quadraticChar_one_iff_isSquare (mul_ne_zero hu0 he0), map_mul, h1, h2]
        norm_num
      have h4 : IsSquare (PadicInt.toZMod ((u * η : ℤ_[p]ˣ) : ℤ_[p])) := by
        rw [Units.val_mul, hηv, map_mul]
        exact h3
      obtain ⟨w, hw⟩ := (QuadFormsKB.HilbertLocal.isSquare_unit_iff hp (u * η)).2 h4
      rw [Units.val_mul, hηv] at hw
      push_cast at hw
      have hw0 : w ≠ 0 := by
        rintro rfl
        have := mul_eq_zero.1 (by simpa using hw : ((u : ℤ_[p]) : ℚ_[p]) * (ε : ℚ_[p]) = 0)
        rcases this with h | h
        · exact u.ne_zero (by simpa using h)
        · exact hε0 h
      have hu : ((u : ℤ_[p]) : ℚ_[p]) = (ε : ℚ_[p]) * (w / (ε : ℚ_[p])) ^ 2 := by
        field_simp
        linear_combination hw
      interval_cases r
      · refine ⟨1, c * (w / (ε : ℚ_[p])), mul_ne_zero hc (div_ne_zero hw0 hε0), ?_⟩
        rw [hxe, hu]
        simp [R]
        ring
      · refine ⟨3, c * (w / (ε : ℚ_[p])), mul_ne_zero hc (div_ne_zero hw0 hε0), ?_⟩
        rw [hxe, hu]
        simp [R]
        ring
  · -- irredundancy
    let rr : Fin 4 → ℕ := ![0, 0, 1, 1]
    let U : Fin 4 → ℤ_[p]ˣ := ![1, η, 1, η]
    have hR : ∀ i, R i = (p : ℚ_[p]) ^ (rr i : ℤ) * ((U i : ℤ_[p]) : ℚ_[p]) := by
      intro i
      fin_cases i <;> simp [R, rr, U, hηv] <;> ring
    rintro i j ⟨c, hc, hij⟩
    have hsq : IsSquare (R i * R j) := ⟨R j * c, by rw [hij]; ring⟩
    have hprod : R i * R j = (p : ℚ_[p]) ^ ((rr i + rr j : ℕ) : ℤ) * (((U i * U j : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) := by
      rw [hR i, hR j]
      push_cast
      rw [zpow_add₀ hpne]
      ring
    rw [hprod] at hsq
    obtain ⟨hev, hres⟩ := (QuadFormsKB.HilbertLocal.isSquare_zpow_mul_unit_iff hp _ (U i * U j)).1 hsq
    rw [Units.val_mul, map_mul] at hres
    have hev' : Even (rr i + rr j) := by exact_mod_cast hev
    have hηres : PadicInt.toZMod (η : ℤ_[p]) = PadicInt.toZMod ε := by rw [hηv]
    fin_cases i <;> fin_cases j <;>
      simp [rr, U, hηres, hε] at hres hev' ⊢

/-- Auxiliary: for $k$ odd with $k^2 \equiv 1 \pmod 8$ and a $2$-adic unit $u \equiv k \pmod 8$, $u = k d^2$
for some $d \ne 0$ in $\mathbb Q_2$. -/
theorem two_adic_unit_eq_mul_sq (u : ℤ_[2]ˣ) (k : ℕ) (hk : Nat.Coprime 2 k)
    (h : PadicInt.toZModPow 3 (u : ℤ_[2]) = (k : ZMod (2 ^ 3)))
    (hk2 : (k : ZMod (2 ^ 3)) * k = 1) :
    ∃ d : ℚ_[2], d ≠ 0 ∧ ((u : ℤ_[2]) : ℚ_[2]) = (k : ℚ_[2]) * d ^ 2 := by
  have hku : IsUnit (k : ℤ_[2]) := PadicInt.isUnit_iff.2 (by simpa using hk)
  have hres : PadicInt.toZModPow 3 ((u * hku.unit : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
    rw [Units.val_mul, IsUnit.unit_spec, map_mul, h, map_natCast]
    exact hk2
  obtain ⟨w, hw⟩ := (QuadFormsKB.HilbertLocal.isSquare_two_adic_unit_iff (u * hku.unit)).2 hres
  rw [Units.val_mul, IsUnit.unit_spec] at hw
  push_cast at hw
  have hk0 : (k : ℚ_[2]) ≠ 0 := by
    have : (k : ℤ_[2]) ≠ 0 := hku.ne_zero
    exact_mod_cast this
  refine ⟨w / k, ?_, ?_⟩
  · intro h0
    have : w = 0 := by
      rcases div_eq_zero_iff.1 h0 with h | h
      · exact h
      · exact absurd h hk0
    rw [this] at hw
    have := mul_eq_zero.1 (by simpa using hw : ((u : ℤ_[2]) : ℚ_[2]) * (k : ℚ_[2]) = 0)
    rcases this with h | h
    · exact u.ne_zero (by simpa using h)
    · exact hk0 h
  · field_simp
    linear_combination hw

/-- **Kitaoka 1993, Corollary 3.1.4 ($p = 2$).** The list $1, 3, 5, 7, 2\cdot 1, 2\cdot 3, 2\cdot 5, 2\cdot 7$
is a complete and irredundant set of representatives of $\mathbb Q_2^\times / (\mathbb Q_2^\times)^2$: every
nonzero $x$ equals $R_i c^2$ for some index $i$ and some $c \ne 0$, and $R_i = R_j c^2$ with $c \ne 0$ forces
$i = j$. -/
@[kb "kitaoka1993" "§3.1, Cor. 3.1.4, p. 62"]
theorem corollary314_two :
    let R : Fin 8 → ℚ_[2] := ![1, 3, 5, 7, 2, 6, 10, 14]
    (∀ x : ℚ_[2], x ≠ 0 → ∃ i, ∃ c : ℚ_[2], c ≠ 0 ∧ x = R i * c ^ 2) ∧
    (∀ i j, (∃ c : ℚ_[2], c ≠ 0 ∧ R i = R j * c ^ 2) → i = j) := by
  intro R
  have h2ne : (2 : ℚ_[2]) ≠ 0 := two_ne_zero
  constructor
  · intro x hx
    obtain ⟨c, r, u, hc, hr, hxe⟩ := QuadFormsKB.PadicClass.padic_decomp 2 x hx
    have hunit : IsUnit (PadicInt.toZModPow 3 (u : ℤ_[2])) := (u.isUnit).map _
    have hcases : ∀ m : ZMod (2 ^ 3), IsUnit m → m = 1 ∨ m = 3 ∨ m = 5 ∨ m = 7 := by decide
    have key : ∀ k : ℕ, Nat.Coprime 2 k → PadicInt.toZModPow 3 (u : ℤ_[2]) = (k : ZMod (2 ^ 3)) →
        (k : ZMod (2 ^ 3)) * k = 1 →
        ∃ d : ℚ_[2], d ≠ 0 ∧ ((u : ℤ_[2]) : ℚ_[2]) = (k : ℚ_[2]) * d ^ 2 :=
      fun k hk h hk2 => two_adic_unit_eq_mul_sq u k hk h hk2
    have hxe' : x = c ^ 2 * ((2 : ℚ_[2]) ^ r * ((u : ℤ_[2]) : ℚ_[2])) := by
      simpa using hxe
    interval_cases r
    · rcases hcases _ hunit with h | h | h | h
      · obtain ⟨d, hd, hd2⟩ := key 1 (by decide) (by simpa using h) (by decide)
        refine ⟨0, c * d, mul_ne_zero hc hd, ?_⟩
        rw [hxe', hd2]; simp [R]; ring
      · obtain ⟨d, hd, hd2⟩ := key 3 (by decide) (by rw [h]; decide) (by decide)
        refine ⟨1, c * d, mul_ne_zero hc hd, ?_⟩
        rw [hxe', hd2]; simp [R]; ring
      · obtain ⟨d, hd, hd2⟩ := key 5 (by decide) (by rw [h]; decide) (by decide)
        refine ⟨2, c * d, mul_ne_zero hc hd, ?_⟩
        rw [hxe', hd2]; simp [R]; ring
      · obtain ⟨d, hd, hd2⟩ := key 7 (by decide) (by rw [h]; decide) (by decide)
        refine ⟨3, c * d, mul_ne_zero hc hd, ?_⟩
        rw [hxe', hd2]; simp [R]; ring
    · rcases hcases _ hunit with h | h | h | h
      · obtain ⟨d, hd, hd2⟩ := key 1 (by decide) (by simpa using h) (by decide)
        refine ⟨4, c * d, mul_ne_zero hc hd, ?_⟩
        rw [hxe', hd2]; simp [R]; ring
      · obtain ⟨d, hd, hd2⟩ := key 3 (by decide) (by rw [h]; decide) (by decide)
        refine ⟨5, c * d, mul_ne_zero hc hd, ?_⟩
        rw [hxe', hd2]; simp [R]; norm_num; ring
      · obtain ⟨d, hd, hd2⟩ := key 5 (by decide) (by rw [h]; decide) (by decide)
        refine ⟨6, c * d, mul_ne_zero hc hd, ?_⟩
        rw [hxe', hd2]; simp [R]; norm_num; ring
      · obtain ⟨d, hd, hd2⟩ := key 7 (by decide) (by rw [h]; decide) (by decide)
        refine ⟨7, c * d, mul_ne_zero hc hd, ?_⟩
        rw [hxe', hd2]; simp [R]; norm_num; ring
  · let rr : Fin 8 → ℕ := ![0, 0, 0, 0, 1, 1, 1, 1]
    let kk : Fin 8 → ℕ := ![1, 3, 5, 7, 1, 3, 5, 7]
    have hcop : ∀ i, Nat.Coprime 2 (kk i) := by decide
    let U : Fin 8 → ℤ_[2]ˣ := fun i =>
      (PadicInt.isUnit_iff.2 (by simpa using hcop i) : IsUnit ((kk i : ℕ) : ℤ_[2])).unit
    have hR : ∀ i, R i = (2 : ℚ_[2]) ^ (rr i : ℤ) * ((U i : ℤ_[2]) : ℚ_[2]) := by
      intro i
      have hU : ((U i : ℤ_[2]) : ℚ_[2]) = ((kk i : ℕ) : ℚ_[2]) := by
        simp [U]
      rw [hU]
      fin_cases i <;> simp [R, rr, kk] <;> norm_num
    rintro i j ⟨c, hc, hij⟩
    have hsq : IsSquare (R i * R j) := ⟨R j * c, by rw [hij]; ring⟩
    have hprod : R i * R j = (2 : ℚ_[2]) ^ ((rr i + rr j : ℕ) : ℤ) *
        (((U i * U j : ℤ_[2]ˣ) : ℤ_[2]) : ℚ_[2]) := by
      rw [hR i, hR j]
      push_cast
      rw [zpow_add₀ h2ne]
      ring
    rw [hprod] at hsq
    obtain ⟨hev, hres⟩ :=
      (QuadFormsKB.HilbertLocal.isSquare_two_zpow_mul_unit_iff _ (U i * U j)).1 hsq
    rw [Units.val_mul, map_mul] at hres
    have hev' : Even (rr i + rr j) := by exact_mod_cast hev
    have hUk : ∀ i, PadicInt.toZModPow 3 ((U i : ℤ_[2])) = ((kk i : ℕ) : ZMod (2 ^ 3)) := by
      intro i
      simp [U]
    rw [hUk i, hUk j] at hres
    have fin : ∀ i j : Fin 8, Even (rr i + rr j) →
        ((kk i : ℕ) : ZMod (2 ^ 3)) * ((kk j : ℕ) : ZMod (2 ^ 3)) = 1 → i = j := by decide
    exact fin i j hev' hres

end QuadFormsKB.Kitaoka
