/-
# Chenevier–Lannes, §1.1 and §3.4.1: the root system $R(L)$, and Niemeier lattices with a rootless $2$-neighbour

Source: Chenevier–Lannes 2019 (`chenevierlannes2019`), §1.1, p. 1 ("With each element $L$ of $\mathcal{L}_n$ is
associated a root system $R(L) := \{x \in L ;\ x \cdot x = 2\}$ of rank at most $n$"), §1.2, p. 5 ("if the Leech
lattice is a $2$-neighbor of a Niemeier lattice $L$ (with roots), then $L$ has an index $2$ subgroup without any
roots. In particular, $R(L)$ has the property that the sum of two roots is not a root, so that its irreducible
components are of rank $1$, which implies that $R(L) = 24A_1$"), §3.4.1, Proposition 3.4.1.1, p. 62. Printed pages.

**Layer.** An even unimodular (or just positive definite integral) lattice $L$ is its integral form $Q$ on
$\mathbb{Z}^n$; $x \cdot y = x^{\mathsf T}Hy$ (`Siegel.Kneser.bZ`), $x \cdot x = 2Q(x)$; $R(L)$ = `rootSet Q`. The
reflection in a root $\alpha$ is $s_\alpha(x) = x - (x \cdot \alpha)\,\alpha$ (`rootReflect`). A $2$-neighbour of $L$
isomorphic to $M$ is `Siegel.Kneser.NbrStep 2 Q M`.

**Proves** (all unconditional unless said):
- `eval_rootReflect`, `rootReflect_mem_rootSet`: $s_\alpha$ preserves $q_L$, hence $R(L)$;
- `rootSet_isSimplyLaced`: $R(L)$ is a finite, symmetric set of nonzero vectors, stable under the reflections
  $s_\alpha$ ($\alpha \in R(L)$), with $\beta \cdot \alpha \in \{-1, 0, 1\}$ for $\beta \ne \pm\alpha$: a reduced,
  crystallographic, simply-laced root system in the span of $R(L)$ (`IsSimplyLacedRootSet`), the property behind the
  book's "of type ADE" (the classification of such root systems as sums of $A_m, D_m, E_6, E_7, E_8$ is
  Bourbaki's and is not formalized);
- `root_dot_eq_zero_of_nbrStep_two`: if $L$ has a $2$-neighbour without roots, any two roots $\alpha \ne \pm\beta$ of
  $L$ are orthogonal (the sum of two roots is not a root);
- `ncard_rootSet_le_of_nbrStep_two`, `coxeterNumber_le_two_of_nbrStep_two`: then $|R(L)| \le 2n$ and
  $h(L) = |R(L)|/n \le 2$;
- `neighborWithoutRoots_two` (Proposition 3.4.1.1 for $d = 2$): a Niemeier lattice with roots having the Leech lattice
  (any rootless Niemeier lattice) as a $2$-neighbour has $h(L) \le 2$;
- `coxeterNumber_eq_two_of_nbrStep_two` (**conditional** on `VenkovRootSum 24`): then $h(L) = 2$, the Coxeter number
  of $24A_1$, as in §1.2, p. 5.
-/
import QuadFormsKB.Literature.ChenevierLannes.Wave2.VenkovRoots
import QuadFormsKB.Literature.ChenevierLannes.Wave2.ThetaSeries
import QuadFormsKB.Siegel.KneserClosure

open Matrix

namespace QuadFormsKB.ChenevierLannes

open QuadFormsKB.Siegel QuadFormsKB.Siegel.Kneser

variable {n : ℕ}

/-! ### $R(L)$ is a simply-laced root system -/

/-- **The reflection in a root** $s_\alpha(x) = x - (x \cdot \alpha)\,\alpha$ (for $\alpha \cdot \alpha = 2$ this is the
orthogonal reflection in the hyperplane $\alpha^\perp$). -/
def rootReflect (Q : QuadForm ℤ n) (α x : Fin n → ℤ) : Fin n → ℤ := x - bZ Q x α • α

/-- $s_\alpha$ preserves $q_L$ when $\alpha$ is a root. -/
theorem eval_rootReflect {Q : QuadForm ℤ n} {α : Fin n → ℤ} (hα : α ∈ rootSet Q) (x : Fin n → ℤ) :
    Q.eval (rootReflect Q α x) = Q.eval x := by
  have hα' : Q.eval α = 1 := hα
  have h := eval_add_smulZ Q x α (-bZ Q x α)
  rw [hα', neg_smul, ← sub_eq_add_neg] at h
  unfold rootReflect
  rw [h]
  ring

/-- **$R(L)$ is stable under the reflections $s_\alpha$**, $\alpha \in R(L)$. -/
theorem rootReflect_mem_rootSet {Q : QuadForm ℤ n} {α β : Fin n → ℤ} (hα : α ∈ rootSet Q) (hβ : β ∈ rootSet Q) :
    rootReflect Q α β ∈ rootSet Q := by
  show Q.eval _ = 1
  rw [eval_rootReflect hα]
  exact hβ

/-- **A reduced, crystallographic, simply-laced root set** in $\mathbb{Z}^n$ for the inner product $x \cdot y$ of $Q$
(the root systems "of type ADE" of Chenevier–Lannes, §1.1, p. 1, in elementary terms; Bourbaki, Chap. VI, §1).
Fields: `finite` ($S$ is finite), `ne_zero` ($0 \notin S$), `norm_two` ($\alpha \cdot \alpha = 2$), `neg_mem`
($S = -S$), `reflect_mem` ($s_\alpha(S) = S$), `dot_mem` ($\beta \cdot \alpha \in \{-1, 0, 1\}$ for $\beta \ne \pm\alpha$:
all roots of one length, the root strings of length at most $2$, no multiples other than $\pm\alpha$). -/
structure IsSimplyLacedRootSet (Q : QuadForm ℤ n) (S : Set (Fin n → ℤ)) : Prop where
  /-- $S$ is finite. -/
  finite : S.Finite
  /-- $0 \notin S$. -/
  ne_zero : ∀ α ∈ S, α ≠ 0
  /-- $\alpha \cdot \alpha = 2$. -/
  norm_two : ∀ α ∈ S, bZ Q α α = 2
  /-- $-\alpha \in S$. -/
  neg_mem : ∀ α ∈ S, -α ∈ S
  /-- $s_\alpha(\beta) \in S$. -/
  reflect_mem : ∀ α ∈ S, ∀ β ∈ S, rootReflect Q α β ∈ S
  /-- $\beta \cdot \alpha \in \{-1, 0, 1\}$ for $\beta \ne \pm\alpha$. -/
  dot_mem : ∀ α ∈ S, ∀ β ∈ S, β ≠ α → β ≠ -α → bZ Q β α = -1 ∨ bZ Q β α = 0 ∨ bZ Q β α = 1

/-- **$R(L)$ is a root system of type ADE** (Chenevier–Lannes, §1.1, p. 1; §2.3, p. 34): for a positive definite
integral lattice, $R(L)$ is a finite, reduced, crystallographic, simply-laced root set (`IsSimplyLacedRootSet`).
Unconditional. Its rank is at most $n$ since it lies in $\mathbb{Z}^n$. -/
@[kb "chenevierlannes2019" "§1.1, p. 1; §2.3, p. 34 (R(L) is a root system of type ADE)"]
theorem rootSet_isSimplyLaced {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q) : IsSimplyLacedRootSet Q (rootSet Q) where
  finite := rootSet_finite hQ
  ne_zero α hα h := by
    have : Q.eval α = 1 := hα
    rw [h] at this
    simp [QuadForm.evalIn] at this
  norm_two α hα := by rw [bZ_self, show Q.eval α = 1 from hα]; rfl
  neg_mem _ hα := neg_mem_rootSet hα
  reflect_mem _ hα _ hβ := rootReflect_mem_rootSet hα hβ
  dot_mem α hα β hβ h1 h2 := by
    have := root_dot_le_one hQ hα hβ h1
    have := neg_one_le_root_dot hQ hα hβ h2
    omega

/-! ### Lattices with a rootless $2$-neighbour -/

/-- If $Q''$ is equivalent to a form without roots, it has no roots. -/
theorem rootSet_eq_empty_of_intEquiv {Q Q' : QuadForm ℤ n} (h : IntEquiv Q Q') (hQ' : rootSet Q' = ∅) :
    rootSet Q = ∅ := by
  obtain ⟨g, hg⟩ := h
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  have hmem : (g⁻¹ : GL (Fin n) ℤ).val *ᵥ x ∈ rootSet Q' := by
    show Q'.eval _ = 1
    rw [← hg, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    exact hx
  rw [hQ'] at hmem
  exact hmem

/-- **The sum of two roots is not a root** (Chenevier–Lannes, §1.2, p. 5): if $L$ has a $2$-neighbour without roots,
then for roots $\alpha, \beta$ of $L$, $\alpha + \beta$ lies in the index-$2$ sublattice $L \cap L'$, which has no
roots; so $\alpha \cdot \beta \ne -1$, and (applied to $-\beta$) $\alpha \cdot \beta \ne 1$: distinct roots
$\alpha \ne \pm\beta$ are orthogonal. Unconditional. -/
theorem root_dot_eq_zero_of_nbrStep_two {Q M : QuadForm ℤ n} (hQ : IntQF.PosDef Q) (hM : rootSet M = ∅)
    (h : NbrStep 2 Q M) {α β : Fin n → ℤ} (hα : α ∈ rootSet Q) (hβ : β ∈ rootSet Q) (h1 : β ≠ α) (h2 : β ≠ -α) :
    bZ Q β α = 0 := by
  obtain ⟨Q', ⟨g, -, hN, hQ'⟩, he⟩ := h
  have hQ'0 : rootSet Q' = ∅ := rootSet_eq_empty_of_intEquiv he hM
  -- the neighbour has no vector of norm 2
  have key : ∀ y : Fin n → ℤ, cv y ∈ imgLat g → Q.eval y ≠ 1 := by
    intro y hy hy1
    obtain ⟨c, hc⟩ := hy
    have h1 := hQ' (cv c)
    rw [← hc, evalIn_cv, evalIn_cv, hy1] at h1
    have hmem : c ∈ rootSet Q' := by
      show Q'.eval c = 1
      exact_mod_cast h1
    rw [hQ'0] at hmem
    exact hmem
  have hK : ((imgLat g).toAddSubgroup.addSubgroupOf (stdLat n).toAddSubgroup).index = 2 := hN.relIndex_std
  have hnot : ∀ y : Fin n → ℤ, Q.eval y = 1 →
      (⟨cv y, ⟨y, rfl⟩⟩ : (stdLat n).toAddSubgroup) ∉
        (imgLat g).toAddSubgroup.addSubgroupOf (stdLat n).toAddSubgroup := by
    intro y hy hk
    exact key y (AddSubgroup.mem_addSubgroupOf.mp hk) hy
  -- the sum of two roots lies in the index-2 sublattice, so it is not a root
  have hsum : ∀ γ δ : Fin n → ℤ, Q.eval γ = 1 → Q.eval δ = 1 → Q.eval (γ + δ) ≠ 1 := by
    intro γ δ hγ hδ
    have hs := (AddSubgroup.add_mem_iff_of_index_two hK).mpr (iff_of_false (hnot γ hγ) (hnot δ hδ))
    refine key (γ + δ) ?_
    have := AddSubgroup.mem_addSubgroupOf.mp hs
    simpa [cv_add] using this
  have hα' : Q.eval α = 1 := hα
  have hβ' : Q.eval β = 1 := hβ
  have hnβ : Q.eval (-β) = 1 := neg_mem_rootSet hβ
  have e1 := eval_add_smulZ Q β α 1
  have e2 := eval_add_smulZ Q (-β) α 1
  rw [one_smul] at e1 e2
  have n1 := hsum β α hβ' hα'
  have n2 := hsum (-β) α hnβ hα'
  have hneg : bZ Q (-β) α = -bZ Q β α := by
    rw [← neg_one_smul ℤ β, bZ_smul_left]; ring
  rw [e1, hβ', hα'] at n1
  rw [e2, hnβ, hα', hneg] at n2
  have := (rootSet_isSimplyLaced hQ).dot_mem α hα β hβ h1 h2
  omega

/-- **At most $2n$ roots** when $L$ has a rootless $2$-neighbour: the roots are pairwise orthogonal up to sign
(`root_dot_eq_zero_of_nbrStep_two`), so one root out of each pair $\pm\alpha$ gives a linearly independent family in
$\mathbb{Z}^n$. Unconditional. -/
theorem ncard_rootSet_le_of_nbrStep_two {Q M : QuadForm ℤ n} (hQ : IntQF.PosDef Q) (hM : rootSet M = ∅)
    (h : NbrStep 2 Q M) : (rootSet Q).ncard ≤ 2 * n := by
  classical
  have hfin := rootSet_finite hQ
  -- one root out of each pair ±α: the lexicographically larger one
  set P : Finset (Fin n → ℤ) := hfin.toFinset.filter fun α => toLex (-α) < toLex α with hP
  have hPR : ∀ α ∈ P, α ∈ rootSet Q := fun α hα => hfin.mem_toFinset.mp (Finset.mem_filter.mp hα).1
  have hsplit : hfin.toFinset = P ∪ P.image Neg.neg := by
    ext α
    simp only [Finset.mem_union, Finset.mem_image, hP, Finset.mem_filter, Set.Finite.mem_toFinset]
    constructor
    · intro hα
      rcases lt_trichotomy (toLex (-α)) (toLex α) with hlt | heq | hgt
      · exact Or.inl ⟨hα, hlt⟩
      · exact absurd (toLex.injective heq).symm (root_ne_neg hα)
      · exact Or.inr ⟨-α, ⟨neg_mem_rootSet hα, by rwa [neg_neg]⟩, neg_neg α⟩
    · rintro (⟨hα, -⟩ | ⟨β, ⟨hβ, -⟩, rfl⟩)
      · exact hα
      · exact neg_mem_rootSet hβ
  have hdisj : Disjoint P (P.image Neg.neg) := by
    rw [Finset.disjoint_left]
    intro α hα hα'
    obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.mp hα'
    have h1 := (Finset.mem_filter.mp hα).2
    have h2 := (Finset.mem_filter.mp hβ).2
    rw [neg_neg] at h1
    exact lt_asymm h1 h2
  have hcard : (rootSet Q).ncard = 2 * P.card := by
    rw [Set.ncard_eq_toFinset_card _ hfin, hsplit, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ neg_injective]
    ring
  -- the chosen roots are pairwise orthogonal, hence linearly independent
  have hli : LinearIndependent ℤ (fun α : P => (α : Fin n → ℤ)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have hdot : bZ Q (∑ i : P, c i • (i : Fin n → ℤ)) (j : Fin n → ℤ) =
        ∑ i : P, c i * bZ Q (i : Fin n → ℤ) (j : Fin n → ℤ) := by
      simp only [bZ, sum_dotProduct, smul_dotProduct, smul_eq_mul]
    rw [hc] at hdot
    have hterm : ∀ i : P, c i * bZ Q (i : Fin n → ℤ) (j : Fin n → ℤ) = if i = j then 2 * c j else 0 := by
      intro i
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl, bZ_self, show Q.eval (i : Fin n → ℤ) = 1 from hPR _ i.2]; ring
      · rw [if_neg hij]
        have hne : (i : Fin n → ℤ) ≠ j := fun e => hij (Subtype.ext e)
        have hne' : (i : Fin n → ℤ) ≠ -(j : Fin n → ℤ) := by
          intro e
          have hi := (Finset.mem_filter.mp i.2).2
          have hj := (Finset.mem_filter.mp j.2).2
          rw [e, neg_neg] at hi
          exact lt_asymm hi hj
        rw [root_dot_eq_zero_of_nbrStep_two hQ hM h (hPR _ j.2) (hPR _ i.2) hne hne', mul_zero]
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_ite_eq'] at hdot
    simp only [Finset.mem_univ, if_true] at hdot
    simp [bZ] at hdot
    omega
  have hle := hli.fintype_card_le_finrank
  rw [Module.finrank_fin_fun, Fintype.card_coe] at hle
  omega

/-- **$h(L) \le 2$** when $L$ (of dimension $n > 0$) has a rootless $2$-neighbour, $h(L) = |R(L)|/n$
(`coxeterNumber`). Unconditional. -/
theorem coxeterNumber_le_two_of_nbrStep_two {Q M : QuadForm ℤ n} (hn : 0 < n) (hQ : IntQF.PosDef Q)
    (hM : rootSet M = ∅) (h : NbrStep 2 Q M) : coxeterNumber Q ≤ 2 := by
  have hc := ncard_rootSet_le_of_nbrStep_two hQ hM h
  rw [ncard_rootSet] at hc
  unfold coxeterNumber
  rw [div_le_iff₀ (by exact_mod_cast hn)]
  exact_mod_cast hc

/-- **Proposition 3.4.1.1 for $d = 2$** (Chenevier–Lannes, p. 62; the observation of §1.2, p. 5): if a Niemeier lattice
$L$ with roots has a $2$-neighbour without roots (the Leech lattice), then $2 \ge h(L)$. Unconditional; the general
prime case is `NeighborWithoutRoots` (stated). -/
@[kb "chenevierlannes2019" "Prop. 3.4.1.1, p. 62, for d = 2; §1.2, p. 5"]
theorem neighborWithoutRoots_two {L M : QuadForm ℤ 24} (hL : IsNiemeier L) (hM : IsNiemeier M)
    (hM0 : rootSet M = ∅) (h : NbrStep 2 L M) : coxeterNumber L ≤ 2 :=
  coxeterNumber_le_two_of_nbrStep_two (by norm_num) hL.posDef hM0 h

/-- **A Niemeier lattice with roots and a rootless $2$-neighbour has Coxeter number $2$** (Chenevier–Lannes, §1.2, p. 5:
"$R(L) = 24A_1$ … the only one with Coxeter number 2, in accordance with statement (i)"): **conditional** on
`VenkovRootSum 24` (Proposition 2.3.2). *Proof:* for a root $\alpha$, the number of roots $\beta$ with
$\beta \cdot \alpha = \pm 1$ is $4h(L) - 8$ (`card_root_dot_pm_one_twentyFour`), and it is $0$ here. -/
@[kb "chenevierlannes2019" "§1.2, p. 5 (h(L) = 2; conditional on Venkov)"]
theorem coxeterNumber_eq_two_of_nbrStep_two (hV : VenkovRootSum 24) {L M : QuadForm ℤ 24} (hL : IsNiemeier L)
    (hR : (rootSet L).Nonempty) (hM0 : rootSet M = ∅) (h : NbrStep 2 L M) : coxeterNumber L = 2 := by
  classical
  obtain ⟨α, hα⟩ := hR
  have hc := card_root_dot_pm_one_twentyFour hV hL hα
  have hempty : ((rootSet_finite hL.posDef).toFinset.filter
      (fun β => bZ L β α = 1 ∨ bZ L β α = -1)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro β hβ
    rw [Set.Finite.mem_toFinset] at hβ
    by_cases h1 : β = α
    · subst h1
      rw [bZ_self, show L.eval β = 1 from hα]; omega
    by_cases h2 : β = -α
    · subst h2
      rw [← neg_one_smul ℤ α, bZ_smul_left, bZ_self, show L.eval α = 1 from hα]; omega
    rw [root_dot_eq_zero_of_nbrStep_two hL.posDef hM0 h hα hβ h1 h2]; omega
  rw [hempty, Finset.card_empty] at hc
  have : (coxeterNumber L : ℝ) = 2 := by push_cast at hc; linarith
  exact_mod_cast this

end QuadFormsKB.ChenevierLannes
