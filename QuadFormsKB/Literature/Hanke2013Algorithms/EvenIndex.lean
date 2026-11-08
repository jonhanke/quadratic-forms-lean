/-
# Hanke 2013, Lemma 4.5: the index of the partial even sublattice

J. Hanke, *Algorithms for computing maximal lattices in bilinear (and quadratic) spaces over number fields*,
Contemp. Math. 587 (2013); source used: arXiv:1208.2481v3 (bib key `hanke2013algorithms`), §4, p. 16.

**Setting** as in `Even.lean` and `Neighbors.lean`: $R$ a Dedekind domain with fraction field $F$ (for a number
field, $R = \mathcal O_F$), $Q$ a quadratic form on $V$ with Hessian form $H$ = `polar Q`, $\mathfrak a$ a non-zero
fractional ideal, $\mathfrak p$ a non-zero prime of $R$ with finite residue field $\mathbb F_{\mathfrak p} = R/\mathfrak p$, and
$e_{\mathfrak p} = \mathrm{ord}_{\mathfrak p}(2)\le1$ written as $2\notin\mathfrak p^2$.

**Proves Lemma 4.5 in corrected form** (`lemma_4_5`): if $L$ is $\mathfrak a$-valued for $H$, not $\mathfrak a$-even at
$\mathfrak p$, and $2\notin\mathfrak p^2$, then $\vec x\mapsto H(\vec x,\vec x)$ induces an isomorphism of abelian groups
$L/L^{\mathfrak a\text{-even at }\mathfrak p}\cong\mathfrak a/\mathfrak p\mathfrak a$ ($\cong\mathbb F_{\mathfrak p}$), so
$[L : L^{\mathfrak a\text{-even at }\mathfrak p}] = N(\mathfrak p)$. *Erratum:* the paper writes $L^{\mathfrak a\text{-even}}$; the
partial sublattice is meant (and used in Algorithm 4.6). The proof is the paper's: the map is additive (the cross
term $2H(\vec x,\vec y)$ lies in $2\mathfrak a\subseteq\mathfrak p\mathfrak a$), semilinear for $r\mapsto r^2$, and every element
of the finite field $\mathbb F_{\mathfrak p}$ of characteristic $2$ is a square, so its non-zero image is an
$\mathbb F_{\mathfrak p}$-subspace of the line $\mathfrak a/\mathfrak p\mathfrak a$.
-/
import QuadFormsKB.Literature.Hanke2013Algorithms.Neighbors

open QuadraticMap Submodule

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2013Algorithms

open QuadFormsKB.OMeara

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- $2\mathfrak a\subseteq\mathfrak p\mathfrak a$ when $2\in\mathfrak p$. -/
theorem twoA_le_smul {a : Submodule R F} {p : Ideal R} (h2 : (2 : R) ∈ p) : twoA a ≤ p • a := by
  rintro _ ⟨y, hy, rfl⟩
  have := Submodule.smul_mem_smul h2 hy
  rw [LinearMap.mulLeft_apply, ← map_ofNat (algebraMap R F) 2, ← Algebra.smul_def]
  exact this

/-- $\mathfrak a\cap(2\mathfrak a)_{\mathfrak p}\subseteq\mathfrak p\mathfrak a$ for a maximal ideal $\mathfrak p\ni2$. -/
theorem mem_smul_of_mem_locAt {a : Submodule R F} {p : Ideal R} (hp : p.IsMaximal) (h2 : (2 : R) ∈ p) {x : F}
    (hx : x ∈ a) (hx2 : x ∈ (haveI := hp.isPrime; locAt p (twoA a))) : x ∈ p • a := by
  have := hp.isPrime
  refine mem_of_forall_locAt fun m hm => ?_
  have := hm.isPrime
  by_cases hmp : m = p
  · subst hmp
    obtain ⟨s, hs, hsx⟩ := hx2
    exact ⟨s, hs, twoA_le_smul h2 hsx⟩
  · have : ¬ p ≤ m := fun h => hmp (hp.eq_of_le hm.ne_top h).symm
    obtain ⟨u, hu, hum⟩ := Set.not_subset.1 this
    exact ⟨u, hum, Submodule.smul_mem_smul hu hx⟩

/-- $\mathfrak p\mathfrak a\subseteq(2\mathfrak a)_{\mathfrak p}$ when $e_{\mathfrak p}\le1$ ($2\notin\mathfrak p^2$): with $2R = \mathfrak pJ$ and
$t\in J\setminus\mathfrak p$, $t\mathfrak p\mathfrak a\subseteq2\mathfrak a$. -/
theorem smul_le_locAt {a : Submodule R F} {p : Ideal R} (hp : p.IsMaximal) (h2 : (2 : R) ∈ p)
    (h22 : (2 : R) ∉ p ^ 2) : p • a ≤ (haveI := hp.isPrime; locAt p (twoA a)) := by
  have := hp.isPrime
  have hdvd : p ∣ Ideal.span {(2 : R)} := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 h2)
  obtain ⟨J, hJ⟩ := hdvd
  have hJp : ¬ J ≤ p := by
    intro h
    apply h22
    have : Ideal.span {(2 : R)} ≤ p ^ 2 := by rw [hJ, pow_two]; exact Ideal.mul_mono_right h
    exact this (Ideal.mem_span_singleton_self 2)
  obtain ⟨t, htJ, htp⟩ := Set.not_subset.1 hJp
  intro x hx
  refine ⟨t, htp, ?_⟩
  refine Submodule.smul_induction_on (p := fun x => t • x ∈ twoA a) hx (fun r hr y hy => ?_)
    (fun x y hx hy => by rw [smul_add]; exact add_mem hx hy)
  have hrt : r * t ∈ Ideal.span {(2 : R)} := hJ ▸ Ideal.mul_mem_mul hr htJ
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 hrt
  rw [smul_smul, mul_comm, ← hu, mul_smul]
  refine ⟨u • y, a.smul_mem u hy, ?_⟩
  show (2 : F) * (u • y) = u • (2 : R) • y
  rw [smul_comm u (2 : R) y, Algebra.smul_def (2 : R), map_ofNat]

/-- Every class in $R/\mathfrak p$ is a square when $R/\mathfrak p$ is finite of characteristic $2$: for $r\in R$ there is
$u\in R$ with $r - u^2\in\mathfrak p$ (the Frobenius $x\mapsto x^2$ is injective, hence bijective). -/
theorem exists_sq_sub_mem {p : Ideal R} (hp : p.IsMaximal) [Finite (R ⧸ p)] (h2 : (2 : R) ∈ p) (r : R) :
    ∃ u : R, r - u * u ∈ p := by
  let := Ideal.Quotient.field p
  have h20 : (2 : R ⧸ p) = 0 := by
    rw [← map_ofNat (Ideal.Quotient.mk p), Ideal.Quotient.eq_zero_iff_mem]; exact h2
  have hinj : Function.Injective (fun x : R ⧸ p => x * x) := by
    intro x y hxy
    simp only at hxy
    have : (x - y) * (x - y) = 0 := by
      have e : (x - y) * (x - y) = x * x - y * y - 2 * (x * y - y * y) := by ring
      rw [e, hxy, h20]; ring
    exact sub_eq_zero.1 (mul_self_eq_zero.1 this)
  obtain ⟨w, hw⟩ := (Finite.injective_iff_surjective.1 hinj) (Ideal.Quotient.mk p r)
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective w
  refine ⟨u, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul]
  simp only at hw
  rw [hw, sub_self]

/-- The additive map $L\to\mathfrak a/\mathfrak p\mathfrak a$, $\vec x\mapsto H(\vec x,\vec x)$ (the paper's $Q_H$). -/
def qH {a : Submodule R F} {p : Ideal R} (h2 : (2 : R) ∈ p) {L : Submodule R V} (hL : IsHValued Q a L) :
    L.toAddSubgroup →+ SubQuot (p • a) a where
  toFun x := Submodule.Quotient.mk ⟨polar Q x x, hL x x.2 x x.2⟩
  map_zero' := by
    rw [Submodule.Quotient.mk_eq_zero]; simp
  map_add' x y := by
    rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
    show polar Q (x + y : V) (x + y : V) - (polar Q x x + polar Q y y) ∈ p • a
    rw [polar_add_self, add_sub_cancel_left]
    exact twoA_le_smul h2 (two_mul_mem_twoA (hL x x.2 y y.2))

theorem qH_apply {a : Submodule R F} {p : Ideal R} (h2 : (2 : R) ∈ p) {L : Submodule R V} (hL : IsHValued Q a L)
    (x : L.toAddSubgroup) : qH Q h2 hL x = Submodule.Quotient.mk ⟨polar Q x x, hL x x.2 x x.2⟩ := rfl

/-- **Lemma 4.5, corrected** (Hanke 2013, p. 16). Let $L$ be $\mathfrak a$-valued for the Hessian form $H$
($\mathfrak a$ a non-zero fractional ideal) and $\mathfrak p$ a non-zero prime with finite residue field and
$e_{\mathfrak p} = \mathrm{ord}_{\mathfrak p}(2)\le1$ ($2\notin\mathfrak p^2$). If $L$ is not $\mathfrak a$-even at $\mathfrak p$, then
$\vec x\mapsto H(\vec x,\vec x)$ induces $L/L^{\mathfrak a\text{-even at }\mathfrak p}\cong\mathfrak a/\mathfrak p\mathfrak a\cong\mathbb F_{\mathfrak p}$ as
abelian groups; in particular $[L : L^{\mathfrak a\text{-even at }\mathfrak p}] = N(\mathfrak p)$. (Then $\mathfrak p\mid2$ necessarily, as in
the paper's proof.) *Erratum:* the paper writes $L/L^{\mathfrak a\text{-even}}$. -/
@[kb "hanke2013algorithms" "Lemma 4.5, p. 16 (corrected: L / L^{a-even at p} ≅ F_p)"]
theorem lemma_4_5 {a : Submodule R F} (ha : a.FG) (ha0 : a ≠ ⊥) {p : Ideal R} (hp : p.IsMaximal)
    [Finite (R ⧸ p)] (h22 : (2 : R) ∉ p ^ 2) {L : Submodule R V} (hL : IsHValued Q a L)
    (hnot : ¬ (haveI := hp.isPrime; IsAEvenAt Q a p L)) :
    (2 : R) ∈ p ∧
    (haveI := hp.isPrime; latIndex (evenAtSub Q p hL) L) = Nat.card (R ⧸ p) := by
  have := hp.isPrime
  have h2 : (2 : R) ∈ p := by
    by_contra h2
    apply hnot
    intro x hx
    have := remark_4_3_odd Q hL p h2
    rw [← this] at hx
    exact hx.2
  refine ⟨h2, ?_⟩
  set φ := qH Q h2 hL
  -- the kernel is the partial even sublattice
  have hker : φ.ker = (evenAtSub Q p hL).toAddSubgroup.addSubgroupOf L.toAddSubgroup := by
    ext x
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, qH_apply, Submodule.Quotient.mk_eq_zero]
    show polar Q x x ∈ p • a ↔ (x : V) ∈ L ∧ _
    exact ⟨fun h => ⟨x.2, smul_le_locAt hp h2 h22 h⟩,
      fun h => mem_smul_of_mem_locAt hp h2 (hL x x.2 x x.2) h.2⟩
  -- the image is all of `a / p a`
  have hsimple := (covBy_iff_quot_is_simple Submodule.smul_le_right).1 (covBy_smul ha ha0 hp)
  have hsurj : Function.Surjective φ := by
    let S : Submodule R (SubQuot (p • a) a) :=
      { carrier := Set.range φ
        add_mem' := by
          rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨x + y, map_add φ x y⟩
        zero_mem' := ⟨0, map_zero φ⟩
        smul_mem' := by
          rintro r _ ⟨x, rfl⟩
          obtain ⟨u, hu⟩ := exists_sq_sub_mem hp h2 r
          refine ⟨⟨u • (x : V), L.smul_mem u x.2⟩, ?_⟩
          rw [qH_apply, qH_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
          show polar Q (u • (x : V)) (u • (x : V)) - r • polar Q x x ∈ p • a
          have e : polar Q (u • (x : V)) (u • (x : V)) - r • polar Q x x = -((r - u * u) • polar Q x x) := by
            rw [← algebraMap_smul F u (x : V), polar_smul_left, polar_smul_right, smul_eq_mul, smul_eq_mul,
              sub_smul, Algebra.smul_def, Algebra.smul_def, map_mul]
            ring
          rw [e]
          exact neg_mem (Submodule.smul_mem_smul hu (hL x x.2 x x.2)) }
    rcases hsimple.eq_bot_or_eq_top S with h | h
    · exfalso
      apply hnot
      intro x hx
      have : φ ⟨x, hx⟩ ∈ S := ⟨_, rfl⟩
      rw [h, Submodule.mem_bot] at this
      have hk : (⟨x, hx⟩ : L.toAddSubgroup) ∈ φ.ker := this
      rw [hker, AddSubgroup.mem_addSubgroupOf] at hk
      exact hk.2
    · intro m
      have : m ∈ S := h ▸ Submodule.mem_top
      exact this
  show (evenAtSub Q p hL).toAddSubgroup.relIndex L.toAddSubgroup = _
  rw [AddSubgroup.relIndex, ← hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hsurj,
    AddSubgroup.card_top, card_subQuot_smul ha ha0 hp]

end QuadFormsKB.Hanke2013Algorithms
