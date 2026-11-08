/-
# Cassels, Chapter 10, §7: products of vectors in the Clifford algebra and commutators

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Ch. 10, §3 (Theorem 3.1, Corollary 1; Lemma 3.4) and §7
(the proof of Theorem 7.1 for $n \ge 4$, pp. 189–190, and Lemma 7.2).

**Setting.** A field $k$ with $2$ invertible, a quadratic space $(V, Q)$ over $k$, Mathlib's `CliffordAlgebra Q` and
`spinGroup Q`. Indices are 0-based.

**Proves** (tools for Cassels' proof of Theorem 7.1, $n \ge 4$):
* `vprod Q l` $= a_0a_1\cdots a_{r-1}$ for a list $l = [a_0, \dots, a_{r-1}]$ of vectors; $u u' = \prod_i Q(a_i)$
  (`vprod_mul_reverse`), $u\vec x u' \in V$ (`vprod_conj`), $u \in C_0(V)$ for even $r$ (`vprod_mem_even`), hence
  $u \in \operatorname{Spin}(V)$ when $r$ is even and $\prod_i Q(a_i) = 1$ (`vprod_mem_spinGroup`, Cassels p. 189: "$u = a_1\cdots a_r
  \in \operatorname{Spin}(V)$");
* Cassels' commutators $w = \{Q(a)\}^{-1}\{Q(b)\}^{-1}abab$ (p. 190, `vcomm`), which are the commutators
  $aba^{-1}b^{-1}$ of Lemma 3.4 (`commutatorElement_vecUnit`);
* for $\dim V > 1$ regular and isotropic, every $u \in \operatorname{Spin}(V)$ is a finite product of such commutators
  (`exists_list_vcomm`; Lemma 3.4 with Theorem 3.2, $\Omega(V) = \Theta(V)$ for isotropic $V$).
-/
import QuadFormsKB.Literature.Cassels.Ch10.Thm71Ternary
import QuadFormsKB.Literature.OMeara.Sec55

open CliffordAlgebra TensorProduct Module
open scoped commutatorElement

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Cassels.Thm71Spin

open QuadFormsKB.Cassels QuadFormsKB.OMeara

section Prod

variable {k V : Type*} [Field k] [Invertible (2 : k)] [AddCommGroup V] [Module k V] (Q : QuadraticForm k V)

/-- **The product $a_0a_1\cdots a_{r-1}$ of a list of vectors** in the Clifford algebra $C(V)$. Arguments: `Q` the form,
`l` the list. -/
noncomputable def vprod (l : List V) : CliffordAlgebra Q := (l.map (ι Q)).prod

variable {Q}

@[simp] theorem vprod_nil : vprod Q [] = 1 := rfl

theorem vprod_cons (a : V) (l : List V) : vprod Q (a :: l) = ι Q a * vprod Q l := by
  simp [vprod]

theorem vprod_append (l l' : List V) : vprod Q (l ++ l') = vprod Q l * vprod Q l' := by
  simp [vprod]

/-- $uu' = \prod_i Q(a_i)$ for $u = a_0\cdots a_{r-1}$. -/
theorem vprod_mul_reverse (l : List V) :
    vprod Q l * reverse (vprod Q l) = algebraMap k _ (l.map Q).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [vprod_cons, reverse.map_mul, reverse_ι, List.map_cons, List.prod_cons, map_mul]
    calc ι Q a * vprod Q l * (reverse (vprod Q l) * ι Q a)
        = ι Q a * (vprod Q l * reverse (vprod Q l)) * ι Q a := by simp only [mul_assoc]
      _ = algebraMap k _ (l.map Q).prod * (ι Q a * ι Q a) := by
          rw [ih, ← Algebra.commutes, mul_assoc]
      _ = _ := by rw [ι_sq_scalar, ← map_mul, ← map_mul, mul_comm]

/-- $u\vec xu' \in V$ for $u = a_0\cdots a_{r-1}$ (each factor acts by $\vec x \mapsto a\vec xa$, a multiple of a reflection). -/
theorem vprod_conj (l : List V) (x : V) : ∃ y, ι Q y = vprod Q l * ι Q x * reverse (vprod Q l) := by
  induction l generalizing x with
  | nil => exact ⟨x, by simp⟩
  | cons a l ih =>
    obtain ⟨y, hy⟩ := ih x
    refine ⟨QuadraticMap.polar Q a y • a - Q a • y, ?_⟩
    rw [← ι_mul_ι_mul_ι, vprod_cons, reverse.map_mul, reverse_ι, hy]
    simp only [mul_assoc]

/-- $a_0\cdots a_{r-1}$ lies in the graded piece of parity $r$. -/
theorem vprod_mem_evenOdd (l : List V) : vprod Q l ∈ evenOdd Q (l.length : ZMod 2) := by
  induction l with
  | nil => simpa using one_le_evenOdd_zero Q (Submodule.mem_one.2 ⟨1, map_one _⟩)
  | cons a l ih =>
    rw [vprod_cons, List.length_cons, Nat.cast_succ, add_comm]
    exact evenOdd_mul_le Q _ _ (Submodule.mul_mem_mul (ι_mem_evenOdd_one Q a) ih)

theorem vprod_mem_even {l : List V} (h : Even l.length) : vprod Q l ∈ evenOdd Q 0 := by
  have := vprod_mem_evenOdd (Q := Q) l
  rwa [(ZMod.natCast_eq_zero_iff_even).2 h] at this

/-- **A product of an even number of vectors with $\prod Q(a_i) = 1$ lies in $\operatorname{Spin}(V)$** (Cassels, p. 189).
Arguments: `hQ` regularity, `l` the list, `hev` even length, `h1` the norm condition. -/
theorem vprod_mem_spinGroup [FiniteDimensional k V] [Nontrivial V] (hQ : (QuadraticMap.associated Q).Nondegenerate)
    {l : List V} (hev : Even l.length) (h1 : (l.map Q).prod = 1) : vprod Q l ∈ spinGroup Q :=
  (mem_spinGroup_iff hQ).2 ⟨vprod_mem_even hev, by rw [vprod_mul_reverse, h1, map_one], vprod_conj l⟩

/-- The natural map $C(V) \to C(V_K)$ sends $a_0\cdots a_{r-1}$ to $(1 \otimes a_0)\cdots(1 \otimes a_{r-1})$. -/
theorem ofBaseChangeAux_vprod (K : Type*) [Field K] [Algebra k K] (l : List V) :
    ofBaseChangeAux K Q (vprod Q l) = vprod (Q.baseChange K) (l.map fun a => (1 : K) ⊗ₜ[k] a) := by
  simp only [vprod, map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun a _ => ?_
  simp [ofBaseChangeAux_ι]

variable (Q) in
/-- **Cassels' commutator** $w = \{Q(a)\}^{-1}\{Q(b)\}^{-1}abab$ (p. 190) as a product of four vectors:
$(Q(a)^{-1}a)(Q(b)^{-1}b)ab$. Arguments: `Q`, the vectors `a`, `b`. -/
noncomputable def vcommList (a b : V) : List V := [(Q a)⁻¹ • a, (Q b)⁻¹ • b, a, b]

theorem vcommList_length (a b : V) : (vcommList Q a b).length = 4 := rfl

theorem vcommList_prod {a b : V} (ha : Q a ≠ 0) (hb : Q b ≠ 0) : ((vcommList Q a b).map Q).prod = 1 := by
  simp only [vcommList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, QuadraticMap.map_smul,
    smul_eq_mul, mul_one]
  field_simp

/-- The commutator $aba^{-1}b^{-1}$ of the units $a, b$ of $C(V)$ (Lemma 3.4) is Cassels' $w$. -/
theorem commutatorElement_vecUnit {a b : V} (ha : Q a ≠ 0) (hb : Q b ≠ 0) :
    ((⁅vecUnit a ha, vecUnit b hb⁆ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = vprod Q (vcommList Q a b) := by
  simp only [commutatorElement_def, Units.val_mul, vecUnit, Units.inv_mk, vprod, vcommList, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one, map_smul]
  simp only [mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc]

/-- Helper: the commutator $aba^{-1}b^{-1}$ of the units $a$, $b$ for a pair of anisotropic vectors. -/
noncomputable def commU (ab : {ab : V × V // Q ab.1 ≠ 0 ∧ Q ab.2 ≠ 0}) : (CliffordAlgebra Q)ˣ :=
  ⁅vecUnit ab.1.1 ab.2.1, vecUnit ab.1.2 ab.2.2⁆

/-- **Lemma 3.4 as a list** (Cassels, Ch. 10, Lemma 3.4 with Theorem 3.2): if $V$ is regular, isotropic and $\dim V > 1$,
every $u \in \operatorname{Spin}(V)$ is a product $w_0 \cdots w_{s-1}$ of commutators $w_j = \{Q(a_j)\}^{-1}\{Q(b_j)\}^{-1}a_jb_ja_jb_j$
of anisotropic vectors. Arguments: `hQ`, `hn`, `hiso` a nonzero isotropic vector, `u`. -/
theorem exists_list_vcomm [FiniteDimensional k V] (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hn : 1 < finrank k V) (hiso : ∃ x : V, x ≠ 0 ∧ Q x = 0) (u : spinGroup Q) :
    ∃ L : List (V × V), (∀ ab ∈ L, Q ab.1 ≠ 0 ∧ Q ab.2 ≠ 0) ∧
      (u : CliffordAlgebra Q) = (L.map fun ab => vprod Q (vcommList Q ab.1 ab.2)).prod := by
  classical
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (lt_trans zero_lt_one hn)
  have hθ : spinConj u ∈ orthPrime Q := by rw [← range_spinConj hQ]; exact ⟨u, rfl⟩
  have hΩ : spinConj u ∈ omega Q := by rw [omega_eq_orthPrime_of_isotropic Q hQ hiso]; exact hθ
  have hcl := mem_closure_vecCommutators hQ hn u hΩ
  have key : ∀ x ∈ Subgroup.closure (vecCommutators Q), ∃ L : List {ab : V × V // Q ab.1 ≠ 0 ∧ Q ab.2 ≠ 0},
      x = (L.map commU).prod := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, b, ha, hb, rfl⟩ := hx
      exact ⟨[⟨(a, b), ha, hb⟩], by simp [commU]⟩
    | one => exact ⟨[], rfl⟩
    | mul x y _ _ hx hy =>
      obtain ⟨L, rfl⟩ := hx
      obtain ⟨L', rfl⟩ := hy
      exact ⟨L ++ L', by simp⟩
    | inv x _ hx =>
      obtain ⟨L, rfl⟩ := hx
      refine ⟨(L.map fun ab => ⟨(ab.1.2, ab.1.1), ab.2.2, ab.2.1⟩).reverse, ?_⟩
      rw [List.prod_inv_reverse, List.map_reverse, List.map_map, List.map_map]
      congr 2
      refine List.map_congr_left fun ab _ => ?_
      simp [commU, commutatorElement_inv]
  obtain ⟨L, hL⟩ := key _ hcl
  refine ⟨L.map Subtype.val, fun ab hab => ?_, ?_⟩
  · obtain ⟨ab', h, rfl⟩ := List.mem_map.1 hab
    exact ab'.2
  · have := congrArg (Units.coeHom (CliffordAlgebra Q)) hL
    rw [map_list_prod, List.map_map] at this
    change (u : CliffordAlgebra Q) = _ at this
    rw [this, List.map_map]
    congr 1
    refine List.map_congr_left fun ab _ => ?_
    exact commutatorElement_vecUnit ab.2.1 ab.2.2

end Prod

end QuadFormsKB.Cassels.Thm71Spin
