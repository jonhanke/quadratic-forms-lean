/-
# Hanke 2013, Algorithm 4.6, step 2: every $\eta(P)$ is a $\mathfrak p$-neighbour in the Hessian space

J. Hanke, *Algorithms for computing maximal lattices in bilinear (and quadratic) spaces over number fields*,
Contemp. Math. 587 (2013); source used: arXiv:1208.2481v3 (bib key `hanke2013algorithms`), Theorem 5.6 (pp. 18–19)
as used in step 2 of Algorithm 4.6 (p. 16).

**Setting** as in `Algorithm46.lean`: $R$ a Dedekind domain with fraction field $F$, $2\in F^\times$, $H$ the Hessian
bilinear form of $Q$, $\mathfrak a$ a non-zero fractional ideal, $\mathfrak p$ a non-zero prime of $R$.

In step 2 of Algorithm 4.6 the lattice $L$ is $\mathfrak a$-valued for $H$ but not $\mathfrak a$-even at $\mathfrak p$, and the paper
searches its $\mathfrak p$-neighbours with Theorem 5.6. `isHPNeighbor_eq_nbLatP` (Algorithm46.lean) shows that every
such neighbour is some $\eta(P) = L'' + \mathfrak p^{-1}\vec v_P$. This file proves the **converse**
(`theorem_5_6_isHPNeighbor`): for $\vec v_P\in L\setminus\mathfrak pL$ giving a non-singular point, with the local
condition $Q(\vec v_P)\in(\mathfrak p^2\mathfrak a)_{\mathfrak p}$, the lattice $\eta(P)$ is a $\mathfrak p$-neighbour of $L$ in the Hessian
space (`IsHPNeighbor`). So the neighbours of step 2 are exactly these $\eta(P)$ (`isHPNeighbor_iff_nbLatP`).

The proof is the paper's proof of step 2 of Theorem 5.6; the only new point is that $Q(\vec v_P)$ is controlled only
at $\mathfrak p$: away from $\mathfrak p$ the factor $\mathfrak p^{-1}$ is harmless because $H(\vec v_P,\vec v_P)\in\mathfrak a$
(`mul_polar_self_mem`, using `mem_of_smul_mem_of_pow` with $\mathfrak p^2$).
-/
import QuadFormsKB.Literature.Hanke2013Algorithms.Algorithm46
import QuadFormsKB.Citation

open QuadraticMap Submodule

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2013Algorithms

open QuadFormsKB.OMeara

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

theorem one_mem_pInv (p : Ideal R) : (1 : F) ∈ pInv (F := F) p := fun r _ => ⟨r, by rw [one_mul]⟩

/-- **The key estimate.** If $H(\vec v,\vec v)\in\mathfrak a$ and $Q(\vec v)\in(\mathfrak p^2\mathfrak a)_{\mathfrak p}$, then
$c\,H(\vec v,\vec v)\in\mathfrak p\mathfrak a$ for every $c\in\mathfrak p^{-1}$. At $\mathfrak p$ this is the local condition; away from
$\mathfrak p$ it holds because $\mathfrak p^2c\subseteq\mathfrak p$ (`mem_of_smul_mem_of_pow` with $k = 2$). -/
theorem mul_polar_self_mem {a : Submodule R F} {p : Ideal R} [hp : p.IsMaximal] {v : V}
    (hvv : polar Q v v ∈ a) (hvQ : Q v ∈ locAt p (p • p • a)) {c : F} (hc : c ∈ pInv (F := F) p) :
    c * polar Q v v ∈ p • a := by
  obtain ⟨t, ht, htv⟩ := hvQ
  refine mem_of_smul_mem_of_pow hp ht ?_ (k := 2) ?_
  · have e : t • (c * polar Q v v) = (2 : R) • (c * (t • Q v)) := by
      rw [polar_self, nsmul_eq_mul, Nat.cast_ofNat]
      simp only [Algebra.smul_def, map_ofNat]; ring
    rw [e]
    exact (p • a).smul_mem 2 (mul_mem_of_mem_pInv (a := p • a) hc htv)
  · intro r hr
    rw [pow_two] at hr
    refine Submodule.mul_induction_on hr (fun r₁ hr₁ r₂ hr₂ => ?_) (fun x y hx hy => by
      rw [add_smul]; exact add_mem hx hy)
    obtain ⟨s, hs⟩ := hc r₂ hr₂
    have e : (r₁ * r₂) • (c * polar Q v v) = r₁ • s • polar Q v v := by
      simp only [Algebra.smul_def, map_mul, ← hs]; ring
    rw [e]
    exact Submodule.smul_mem_smul hr₁ (a.smul_mem s hvv)

/-- $L\cap\eta(P) = L''$ for lattices $\mathfrak a$-valued for $H$, under the local condition at $\mathfrak p$ (as
`theorem_5_6_inter`). -/
@[kb "hanke2013algorithms" "Theorem 5.6, p. 18 (L'' = L ∩ L'; lattices a-valued for H, local condition at p)"]
theorem theorem_5_6_inter_gen {a : Submodule R F} {p : Ideal R} [p.IsMaximal] {L : Submodule R V} {v : V}
    (hvv : polar Q v v ∈ a) (hvQ : Q v ∈ locAt p (p • p • a)) : L ⊓ nbLatP Q a p L v = nbCore Q a p L v := by
  apply le_antisymm
  · rintro x ⟨hxL, hx⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, hc, rfl⟩ := mem_pInv_line.1 hz
    refine ⟨hxL, ?_⟩
    rw [polar_add_right, polar_smul_right, smul_eq_mul]
    exact (p • a).add_mem hy.2 (mul_polar_self_mem Q hvv hvQ hc)
  · exact le_inf (fun x hx => hx.1) le_sup_left

/-- **$\eta(P)$ is $\mathfrak a$-valued for $H$**: $H(\vec x + c\vec v_P, \vec y + c'\vec v_P) = H(\vec x,\vec y) + c'H(\vec x,\vec v_P)
+ cH(\vec v_P,\vec y) + cc'H(\vec v_P,\vec v_P)$, each term in $\mathfrak a$. -/
@[kb "hanke2013algorithms" "Theorem 5.6, proof step 2), pp. 18–19 (L' is a-valued; lattices a-valued for H)"]
theorem theorem_5_6_valued_gen {a : Submodule R F} {p : Ideal R} [p.IsMaximal] {L : Submodule R V}
    (hL : IsHValued Q a L) {v : V} (hv : v ∈ L) (hvQ : Q v ∈ locAt p (p • p • a)) :
    IsHValued Q a (nbLatP Q a p L v) := by
  intro w₁ hw₁ w₂ hw₂
  obtain ⟨x₁, hx₁, y₁, hy₁, rfl⟩ := Submodule.mem_sup.1 hw₁
  obtain ⟨c₁, hc₁, rfl⟩ := mem_pInv_line.1 hy₁
  obtain ⟨x₂, hx₂, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hw₂
  obtain ⟨c₂, hc₂, rfl⟩ := mem_pInv_line.1 hy₂
  have e : polar Q (x₁ + c₁ • v) (x₂ + c₂ • v) = polar Q x₁ x₂ + c₂ * polar Q v x₁ + c₁ * polar Q v x₂ +
      c₁ * (c₂ * polar Q v v) := by
    simp only [polar_add_left, polar_add_right, polar_smul_left, polar_smul_right, smul_eq_mul,
      polar_comm Q x₁ v]
    ring
  rw [e]
  refine a.add_mem (a.add_mem (a.add_mem (hL x₁ hx₁.1 x₂ hx₂.1) (mul_mem_of_mem_pInv hc₂ hx₁.2))
    (mul_mem_of_mem_pInv hc₁ hx₂.2)) (mul_mem_of_mem_pInv hc₁ (mul_polar_self_mem Q (hL v hv v hv) hvQ hc₂))

/-- **Every $\eta(P)$ is a $\mathfrak p$-neighbour in the Hessian space** (Hanke 2013, Theorem 5.6, step 2, as used in step 2 of
Algorithm 4.6). Let $L$ be $\mathfrak a$-valued for $H$ ($\mathfrak a$ a non-zero fractional ideal, $\mathfrak p$ a non-zero prime)
and $\vec v_P\in L\setminus\mathfrak pL$ with $H(\vec v_P, L)\not\subseteq\mathfrak a\mathfrak p$ (a non-singular point) and
$Q(\vec v_P)\in(\mathfrak p^2\mathfrak a)_{\mathfrak p}$. Then $L' = \eta(P) = L'' + \mathfrak p^{-1}\vec v_P$ is a $\mathfrak p$-neighbour of $L$
in the sense of `IsHPNeighbor` (corrected Definition 5.1 read for $H$): $L'$ is $\mathfrak a$-valued for $H$,
$[L : L\cap L'] = [L' : L\cap L'] = N(\mathfrak p)$, $\mathfrak pL\subseteq L'$, $\mathfrak pL'\subseteq L$ and $H(L, L')\not\subseteq\mathfrak a$. -/
@[kb "hanke2013algorithms" "Theorem 5.6, proof step 2), pp. 18–19, and Algorithm 4.6, step 2, p. 16 (η(P) is a p-neighbour for H)"]
theorem theorem_5_6_isHPNeighbor {a : Submodule R F} (ha : a.FG) (ha0 : a ≠ ⊥) {p : Ideal R} [hp : p.IsMaximal]
    (hp0 : p ≠ ⊥) {L : Submodule R V} (hL : IsHValued Q a L) {v : V} (hv : v ∈ L) (hvp : v ∉ p • L)
    (hvQ : Q v ∈ locAt p (p • p • a)) (hns : ¬ IsSingularPoint Q a p L v) :
    IsHPNeighbor Q a p L (nbLatP Q a p L v) := by
  have hvv : v ∈ nbCore Q a p L v := ⟨hv, by
    simpa using mul_polar_self_mem Q (hL v hv v hv) hvQ (one_mem_pInv p)⟩
  have hinter := theorem_5_6_inter_gen Q (L := L) (hL v hv v hv) hvQ
  refine
    { valued := hL
      valued' := theorem_5_6_valued_gen Q hL hv hvQ
      index := by rw [hinter]; exact theorem_5_6_index_gen Q ha ha0 hp (fun x hx => hL v hv x hx) hns
      index' := by rw [hinter]; exact theorem_5_6_index'_gen Q hp hp0 hvv hvp
      smul_le := ?_
      smul_le' := (theorem_5_6_smul_le_gen Q hvv).trans fun x hx => hx.1
      not_valued := ?_ }
  · rw [Submodule.smul_le]
    intro r hr x hx
    refine Submodule.mem_sup_left ⟨L.smul_mem r hx, ?_⟩
    rw [polar_rsmul_right]
    exact Submodule.smul_mem_smul hr (hL v hv x hx)
  · by_contra hcon
    push Not at hcon
    apply hns
    intro y hy
    refine mem_smul_of_pInv_mul hp0 fun c hc => ?_
    have := hcon y hy (c • v) (Submodule.mem_sup_right (mem_pInv_line.2 ⟨c, hc, rfl⟩))
    rwa [polar_smul_right, polar_comm, smul_eq_mul] at this

/-- **The $\mathfrak p$-neighbours searched in step 2 of Algorithm 4.6, exactly** (Hanke 2013, Algorithm 4.6, step 2 and
Theorem 5.6): for $L$ $\mathfrak a$-valued for $H$ and $\mathfrak p$ a non-zero prime with finite residue field, a lattice $L'$
that is $\mathfrak a$-even at $\mathfrak p$ is a $\mathfrak p$-neighbour of $L$ in the Hessian space if and only if
$L' = \eta(P)$ for some $\vec v_P\in L\setminus\mathfrak pL$ with $Q(\vec v_P)\in(\mathfrak p^2\mathfrak a)_{\mathfrak p}$ whose point is
non-singular. (`isHPNeighbor_eq_nbLatP` and `theorem_5_6_isHPNeighbor`.) -/
@[kb "hanke2013algorithms" "Algorithm 4.6, step 2, p. 16, with Theorem 5.6 (the a-even p-neighbours are the η(P))"]
theorem isHPNeighbor_iff_nbLatP {a : Submodule R F} (ha : a.FG) (ha0 : a ≠ ⊥) {p : Ideal R} [hp : p.IsMaximal]
    (hp0 : p ≠ ⊥) [Finite (R ⧸ p)] {L L' : Submodule R V} (hL : IsHValued Q a L) (hL' : IsAEvenAt Q a p L') :
    IsHPNeighbor Q a p L L' ↔ ∃ v ∈ L, v ∉ p • L ∧ Q v ∈ locAt p (p • p • a) ∧
      ¬ IsSingularPoint Q a p L v ∧ nbLatP Q a p L v = L' := by
  constructor
  · intro hN
    obtain ⟨v, hv, hvp, hvQ, hns, heq⟩ := isHPNeighbor_eq_nbLatP Q hp0 hN
    exact ⟨v, hv, hvp, hvQ hL', hns, heq⟩
  · rintro ⟨v, hv, hvp, hvQ, hns, rfl⟩
    exact theorem_5_6_isHPNeighbor Q ha ha0 hp0 hL hv hvp hvQ hns

end QuadFormsKB.Hanke2013Algorithms
