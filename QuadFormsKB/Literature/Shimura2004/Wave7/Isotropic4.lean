/-
# Shimura 2004, §7.4 (A): the isotropic case in dimension 4, (7.3c) and (7.3d)

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), Chapter II, §7.4 (A),
(7.3c), (7.3d) (printed p. 54). Page numbers in the tags are printed pages.

**Setting and dictionary.** $F$ a field of characteristic $\ne 2$, $V = U + Fe + Ff$ with `Q e = 0`, `Q f = 0`,
`QuadraticMap.polar Q e f = 1`, and $\dim U = 2$ given by an orthogonal basis $g, h$ of $U$ with
$\varphi[g] \ne 0$ (`hg`), $\varphi(g, h) = 0$ (`hgh`) and $U = Fg + Fh$ (`hspan`). Shimura's element $h$ of
$U = Kh$ (with $ha = a^*h$ for $a \in K$) is our `g`, the element used to build $\Xi$ (`xi`, (2.14)). By §7.2
(`LowDim.dim2_evenOdd_zero_iff`, `LowDim.dim2_comm_of_even`) $K = A^+(U) = F + F\,gh$ is commutative, and
$ga = a^*g$ for $a \in K$ (`LowDim.dim2_ι_mul_K`). $J$ = `matJ`, $J^{-1} = -J$.

**Proves** (all unconditional; standard axioms only):
* $a^\sigma = g^{-1}a^*g = a$ for $a \in K$ (`sigmaU_of_even`), so (15.16) specializes to (7.3c);
* **(7.3c)** for $\alpha \in A^+(V)$: $\Xi(\alpha^*) = J^{-1}\,{}^t\Xi(\alpha)J = \begin{pmatrix} d & -b \\ -c & a
  \end{pmatrix}$ if $\Xi(\alpha) = \begin{pmatrix} a & b \\ c & d\end{pmatrix}$, i.e. $\alpha \mapsto \alpha^*$ is the
  main involution of $M_2(K)$ (`formula_7_3c`);
* *Erratum:* (7.3c) is printed "for every $\alpha \in A(V)$"; it fails for odd $\alpha$, e.g. $\alpha = h$
  (`formula_7_3c_not_all`). Only the even case is used (to describe $A^+(V)$ and $G^+(V)$);
* **(7.3d)**, forward inclusion and the multiplier: for $\alpha \in G^+(V)$, $\xi = \Xi(\alpha) \in GL_2(K)$ and
  $\det\xi = ad - bc = \nu(\alpha)$ (`formula_7_3d_det`, `formula_7_3d_mem`);
* **(7.3a)**, **(7.3b)** in this isotropic setting (with $\varphi[h] \ne 0$ as well, i.e. $U$ nondegenerate):
  every odd $x$ with $x^* = x$ lies in $V$ (`formula_7_3a`), and every $\alpha \in A^+(V)$ with
  $\alpha\alpha^* \in F^\times$ lies in $G^+(V)$ (`formula_7_3b`); on the way, $A^-(U) = U$ (`odd_eq_ι`) and the
  fixed points of $*$ on $K$ are $F$ (`even_reverse_eq`);
* **(7.3d)**, converse inclusion: every $\xi \in M_2(K)$ with $\det\xi \in F^\times$ is $\Xi(\alpha)$ with
  $\alpha \in G^+(V)$ (`formula_7_3d_surj`). So $\Xi(G^+(V)) = \{\xi \in GL_2(K) \mid \det\xi \in F^\times\}$.

Shimura states (7.3a), (7.3b) for every 4-dimensional $V$; here they are proved only in the isotropic case
$V = U + Fe + Ff$ (recorded as a loose end).
-/
import QuadFormsKB.Literature.Shimura2004.Wave4.Formula1516
import QuadFormsKB.Literature.Shimura2004.Wave5.LowDim
import QuadFormsKB.Literature.Shimura2004.Wave4.MatrixGroup
import QuadFormsKB.Citation

open Module CliffordAlgebra

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.Cassels QuadFormsKB.OMeara

namespace Isotropic4

open MatrixModel LowDim

variable {F V : Type*} [Field F] [Invertible (2 : F)] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V} {e f : V} {g h : uSpace Q e f}

local notation "A" => CliffordAlgebra Q

section Hyp

variable (he : Q e = 0) (hf : Q f = 0) (hef : QuadraticMap.polar Q e f = 1) (hg : Q (g : V) ≠ 0)
  (hgh : QuadraticMap.polar (QU Q e f) g h = 0) (hspan : ∀ z : uSpace Q e f, ∃ x y : F, z = x • g + y • h)

include hg hgh hspan in
/-- $a^\sigma = g^{-1}a^*g = a$ for $a \in K = A^+(U)$ when $\dim U = 2$ (from $ga = a^*g$, §7.2). -/
theorem sigmaU_of_even (a : AU Q e f) (ha : a ∈ evenOdd (QU Q e f) 0) : sigmaU g a = a := by
  obtain ⟨r, s, rfl⟩ := (dim2_evenOdd_zero_iff hgh hspan a).1 ha
  rw [sigmaU, mul_assoc, ← dim2_ι_mul_K hgh hspan g r s, ← mul_assoc, ginv_mul hg, one_mul]

include he hf hef hg hgh hspan in
/-- **(7.3c)** (Shimura 2004, §7.4 (A), p. 54), for $\alpha \in A^+(V)$: $\Xi(\alpha^*) = J^{-1}\,{}^t\Xi(\alpha')J$
with $\alpha' = \alpha$, and this is the main involution of $M_2(K)$:
$\Xi(\alpha^*) = \begin{pmatrix} d & -b \\ -c & a\end{pmatrix}$ when
$\Xi(\alpha) = \begin{pmatrix} a & b \\ c & d\end{pmatrix}$. -/
@[kb "shimura2004" "(7.3c), p. 54 (Ξ(α*) = J⁻¹·ᵗΞ(α')J; α ↦ α* is the main involution of M₂(K) on A⁺(V))"]
theorem formula_7_3c (α : A) (hα : α ∈ evenOdd Q 0) :
    xi he hf hef hg (reverse α) = -matJ * (xi he hf hef hg (involute α)).transpose * matJ ∧
      xi he hf hef hg (reverse α) =
        !![xi he hf hef hg α 1 1, -xi he hf hef hg α 0 1; -xi he hf hef hg α 1 0, xi he hf hef hg α 0 0] := by
  have hK := (xi_mem_evenOdd_zero_iff he hf hef hg α).1 hα
  have hm : matStarSigma g (xi he hf hef hg α) = (xi he hf hef hg α).transpose := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matStarSigma, sigmaU_of_even hg hgh hspan _ (hK _ _)]
  rw [formula_15_16, involute_eq_of_mem_even hα, hm, matJ_mul_neg_matJ_apply]
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [matJ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp

include he hf hef hg hgh in
/-- *Erratum* to (7.3c) (Shimura 2004, p. 54): the identity $\Xi(\alpha^*) = J^{-1}\,{}^t\Xi(\alpha')J$ is printed
"for every $\alpha \in A(V)$", but it fails for odd $\alpha$: for $\alpha = h$ (with $h \perp g$, $h \ne 0$) the
$(0,0)$ entries are $-h$ and $h$. It holds for $\alpha \in A^+(V)$ (`formula_7_3c`), the only case used. -/
@[kb "shimura2004" "(7.3c), p. 54 (erratum: the identity fails for odd α, e.g. α = h ∈ U with h ⊥ g)"]
theorem formula_7_3c_not_all (hh : Q (h : V) ≠ 0) :
    ¬ ∀ α : A, xi he hf hef hg (reverse α) = -matJ * (xi he hf hef hg (involute α)).transpose * matJ := by
  intro H
  have k := congrArg (fun M => M 0 0) (H (ι Q (h : V)))
  simp only [reverse_ι, involute_ι, map_neg] at k
  rw [xi_apply_zero_zero, psi_ι_of_mem] at k
  simp only [matJ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.neg_apply] at k
  simp [xi_apply_one_one, psi_ι_of_mem] at k
  have hhg := ι_h_mul_ι_g (Q := QU Q e f) hgh
  rw [mul_assoc, hhg, mul_neg, ← mul_assoc, ginv_mul hg, one_mul] at k
  have hsum : ι (QU Q e f) h + ι (QU Q e f) h = 0 := by
    nth_rewrite 1 [← k]; exact neg_add_cancel _
  have h0 : ι (QU Q e f) h = 0 := by
    have h2 : (2 : F) • ι (QU Q e f) h = 0 := by rw [two_smul, hsum]
    have := congrArg (fun x => (⅟2 : F) • x) h2
    simpa [smul_smul] using this
  have : h = 0 := cliffordι_injective (QU Q e f) (by rw [h0, map_zero])
  exact hh (by rw [this]; simp)

variable (hQ : (QuadraticMap.associated Q).Nondegenerate)

include he hf hef hg hgh hspan hQ in
/-- **(7.3d)** (Shimura 2004, §7.4 (A), p. 54), the multiplier: for $\alpha \in G^+(V)$ and
$\xi = \Xi(\alpha) = \begin{pmatrix} a & b \\ c & d\end{pmatrix} \in GL_2(K)$,
$\nu(\alpha) = \det(\xi) = ad - bc$ (the determinant over the commutative algebra $K = A^+(U)$). -/
@[kb "shimura2004" "(7.3d), p. 54 (ν(α) = det(ξ) if ξ = Ξ(α) with α ∈ G⁺(V))"]
theorem formula_7_3d_det (α : M0 Q) :
    xi he hf hef hg ((α : Aˣ) : A) 0 0 * xi he hf hef hg ((α : Aˣ) : A) 1 1 -
        xi he hf hef hg ((α : Aˣ) : A) 0 1 * xi he hf hef hg ((α : Aˣ) : A) 1 0 =
      algebraMap F (AU Q e f) (multiplier hQ ⟨α, M0_le_homogeneous α.2⟩ : F) := by
  have hK := (xi_mem_evenOdd_zero_iff he hf hef hg _).1 α.2.1
  have hm : matStarSigma g (xi he hf hef hg ((α : Aˣ) : A)) = (xi he hf hef hg ((α : Aˣ) : A)).transpose := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matStarSigma, sigmaU_of_even hg hgh hspan _ (hK _ _)]
  have H := formula_15_17 he hf hef hQ hg α
  rw [hm] at H
  have k := congrArg (fun M => M 0 1) H
  simp [matJ, Matrix.mul_apply, Fin.sum_univ_two, Algebra.smul_def] at k
  rw [← neg_neg (algebraMap F (AU Q e f) _), ← k]
  abel

include he hf hef hg hgh hspan in
/-- **(7.3d)** (Shimura 2004, §7.4 (A), p. 54), forward inclusion: for $\alpha \in G^+(V)$, $\Xi(\alpha)$ is an
invertible matrix with entries in $K = A^+(U)$. -/
@[kb "shimura2004" "(7.3d), p. 54 (Ξ(G⁺(V)) ⊆ GL₂(K))"]
theorem formula_7_3d_mem (α : M0 Q) :
    (∀ i j, xi he hf hef hg ((α : Aˣ) : A) i j ∈ evenOdd (QU Q e f) 0) ∧
      IsUnit (xi he hf hef hg ((α : Aˣ) : A)) :=
  ⟨formula_15_17_mem he hf hef hg α, formula_15_17_isUnit he hf hef hg α⟩

/-! ### (7.3a), (7.3b) in the isotropic case, and the converse inclusion of (7.3d) -/

omit [FiniteDimensional F V] in
theorem odd_mul_odd {W : Type*} [AddCommGroup W] [Module F W] {Q' : QuadraticForm F W} {a b : CliffordAlgebra Q'}
    (ha : a ∈ evenOdd Q' 1) (hb : b ∈ evenOdd Q' 1) : a * b ∈ evenOdd Q' 0 := by
  have := SetLike.mul_mem_graded ha hb
  rwa [show (1 : ZMod 2) + 1 = 0 from rfl] at this

omit [FiniteDimensional F V] in
theorem even_mul_odd {W : Type*} [AddCommGroup W] [Module F W] {Q' : QuadraticForm F W} {a b : CliffordAlgebra Q'}
    (ha : a ∈ evenOdd Q' 0) (hb : b ∈ evenOdd Q' 1) : a * b ∈ evenOdd Q' 1 := by
  have := SetLike.mul_mem_graded ha hb
  rwa [zero_add] at this

omit [FiniteDimensional F V] in
theorem odd_mul_even {W : Type*} [AddCommGroup W] [Module F W] {Q' : QuadraticForm F W} {a b : CliffordAlgebra Q'}
    (ha : a ∈ evenOdd Q' 1) (hb : b ∈ evenOdd Q' 0) : a * b ∈ evenOdd Q' 1 := by
  have := SetLike.mul_mem_graded ha hb
  rwa [add_zero] at this

include hg hgh hspan in
/-- $A^-(U) = U$ when $\dim U = 2$. -/
theorem odd_eq_ι (a : AU Q e f) (ha : a ∈ evenOdd (QU Q e f) 1) : ∃ u : uSpace Q e f, a = ι (QU Q e f) u := by
  obtain ⟨r, s, hrs⟩ := (dim2_evenOdd_zero_iff hgh hspan _).1 (odd_mul_odd ha (ι_mem_evenOdd_one _ g))
  have hgg : ι (QU Q e f) g * ι (QU Q e f) g = (Q (g : V)) • (1 : AU Q e f) := ι_g_sq
  have hhg := ι_h_mul_ι_g (Q := QU Q e f) hgh
  refine ⟨(Q (g : V))⁻¹ • (r • g - (s * Q (g : V)) • h), ?_⟩
  have key : (Q (g : V)) • a = r • ι (QU Q e f) g - (s * Q (g : V)) • ι (QU Q e f) h := by
    have h1 : a * ι (QU Q e f) g * ι (QU Q e f) g = (Q (g : V)) • a := by
      rw [mul_assoc, hgg, mul_smul_comm, mul_one]
    rw [← h1, hrs, add_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_mul_assoc,
      mul_assoc, hhg, mul_neg, ← mul_assoc, hgg, smul_mul_assoc, one_mul, smul_neg, smul_smul,
      sub_eq_add_neg]
  rw [map_smul, map_sub, map_smul, map_smul, ← key, smul_smul, inv_mul_cancel₀ hg, one_smul]

include hg hgh hspan in
/-- The fixed points of $a \mapsto a^*$ on $K = A^+(U)$ are the scalars ($\dim U = 2$, $U$ nondegenerate). -/
theorem even_reverse_eq (hh : Q (h : V) ≠ 0) (a : AU Q e f) (ha : a ∈ evenOdd (QU Q e f) 0)
    (hr : reverse a = a) : ∃ c : F, a = algebraMap F _ c := by
  obtain ⟨r, s, rfl⟩ := (dim2_evenOdd_zero_iff hgh hspan _).1 ha
  refine ⟨r, ?_⟩
  rw [dim2_reverse_K hgh] at hr
  have h2 : (2 * s) • (ι (QU Q e f) g * ι (QU Q e f) h) = 0 := by
    have := congrArg (fun x => x - algebraMap F (AU Q e f) r) hr
    simp only [add_sub_cancel_left] at this
    rw [two_mul, add_smul]
    nth_rewrite 1 [← this]
    rw [neg_smul, neg_add_cancel]
  rcases smul_eq_zero.1 h2 with hs | hz
  · have : s = 0 := by
      rcases mul_eq_zero.1 hs with h | h
      · exact absurd h two_ne_zero
      · exact h
    rw [this, zero_smul, add_zero]
  · exfalso
    have : ι (QU Q e f) g * (ι (QU Q e f) g * ι (QU Q e f) h) = (Q (g : V)) • ι (QU Q e f) h := by
      rw [← mul_assoc, ι_g_sq, smul_mul_assoc, one_mul]; rfl
    rw [hz, mul_zero] at this
    have hh0 : ι (QU Q e f) h = 0 := by
      have := congrArg (fun x => (Q (g : V))⁻¹ • x) this
      simpa [smul_smul, inv_mul_cancel₀ hg] using this.symm
    have : h = 0 := cliffordι_injective (QU Q e f) (by rw [hh0, map_zero])
    exact hh (by rw [this]; simp)

include he hf hef hg hgh hspan in
/-- **(7.3a)** (Shimura 2004, §7.4, p. 54), in the isotropic case $V = U + Fe + Ff$, $\dim U = 2$:
$V = \{x \in A^-(V) \mid x^* = x\}$, i.e. every odd $x$ with $x^* = x$ lies in $V$. -/
@[kb "shimura2004" "(7.3a), p. 54 (V = {x ∈ A⁻(V) | x* = x} if dim V = 4; isotropic case)"]
theorem formula_7_3a (hh : Q (h : V) ≠ 0) (x : A) (hx : x ∈ evenOdd Q 1) (hxr : reverse x = x) :
    ∃ v : V, x = ι Q v := by
  have hpar := (psi_mem_evenOdd_one_iff he hf hef x).1 hx
  set P := psi he hf hef x with hP
  have hrev := psi_reverse he hf hef x
  rw [hxr, involute_eq_of_mem_odd hx, map_neg, ← hP, matStar_neg] at hrev
  have hrev2 : P = -(matJ * matStar P * -matJ) := by
    conv_lhs => rw [hrev]
    simp only [mul_neg, neg_mul, neg_neg]
  rw [matJ_mul_neg_matJ_apply] at hrev2
  replace hrev := hrev2
  have e00 := congrArg (fun M => M 0 0) hrev
  have e01 := congrArg (fun M => M 0 1) hrev
  have e10 := congrArg (fun M => M 1 0) hrev
  have e11 := congrArg (fun M => M 1 1) hrev
  simp only [matStar, Matrix.neg_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    neg_neg] at e00 e01 e10 e11
  obtain ⟨u, hu⟩ := odd_eq_ι hg hgh hspan _ hpar.1
  obtain ⟨β, hβ⟩ := even_reverse_eq hg hgh hspan hh _ hpar.2.1 e01.symm
  obtain ⟨γ, hγ⟩ := even_reverse_eq hg hgh hspan hh _ hpar.2.2.1 e10.symm
  have hd : P 1 1 = -ι (QU Q e f) u := by
    rw [e11, hu, reverse_ι]
  refine ⟨(u : V) + β • e + γ • f, ?_⟩
  apply (psi_bijective he hf hef).1
  rw [psi_ι, psiVec_apply]
  have hpu : proj he hf hef ((u : V) + β • e + γ • f) = u := by
    apply Subtype.ext
    rw [map_add, map_add, map_smul, map_smul]
    simp [proj_e he hf hef, proj_f he hf hef, proj_of_mem he hf hef u.2]
  have hpf : QuadraticMap.polar Q ((u : V) + β • e + γ • f) f = β := by
    simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, (mem_uSpace.1 u.2).2, hef,
      polar_f_f he hf hef, smul_eq_mul]
    ring
  have hpe : QuadraticMap.polar Q ((u : V) + β • e + γ • f) e = γ := by
    simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, (mem_uSpace.1 u.2).1,
      polar_e_e he hf hef, polar_f_e he hf hef, smul_eq_mul]
    ring
  rw [hpu, hpf, hpe, ← hd, ← hu, ← hβ, ← hγ]
  exact (P.eta_fin_two)

include he hf hef hg hgh hspan in
/-- **(7.3b)** (Shimura 2004, §7.4, p. 54), in the isotropic case: an element $\alpha \in A^+(V)$ with
$\alpha\alpha^* \in F^\times$ lies in $G^+(V)$ (the other inclusion holds in general: $\nu(\alpha) = \alpha\alpha^*$). -/
@[kb "shimura2004" "(7.3b), p. 54 (G⁺(V) = {α ∈ A⁺(V) | αα* ∈ F^×} if dim V = 4; isotropic case)"]
theorem formula_7_3b (hh : Q (h : V) ≠ 0) {α : A} (hα : α ∈ evenOdd Q 0) {c : F} (hc : c ≠ 0)
    (hαc : α * reverse α = algebraMap F A c) : ∃ u : Aˣ, (u : A) = α ∧ u ∈ M0 Q := by
  refine mem_M0_of_mul_reverse hα hc hαc fun x => ?_
  have hodd : α * ι Q x * reverse α ∈ evenOdd Q 1 :=
    odd_mul_even (even_mul_odd hα (ι_mem_evenOdd_one _ x)) ((reverse_mem_evenOdd_iff Q).2 hα)
  obtain ⟨v, hv⟩ := formula_7_3a he hf hef hg hgh hspan hh _ hodd (by
    rw [reverse.map_mul, reverse.map_mul, reverse_reverse, reverse_ι, mul_assoc])
  exact ⟨v, hv.symm⟩

include he hf hef hg hgh hspan in
/-- **(7.3d)** (Shimura 2004, §7.4 (A), p. 54), the converse inclusion: every $\xi \in M_2(K)$ with
$\det\xi = ad - bc \in F^\times$ is $\Xi(\alpha)$ for some $\alpha \in G^+(V)$. Together with `formula_7_3d_mem`
and `formula_7_3d_det`: $\Xi(G^+(V)) = \{\xi \in GL_2(K) \mid \det\xi \in F^\times\}$. -/
@[kb "shimura2004" "(7.3d), p. 54 (Ξ(G⁺(V)) = {ξ ∈ GL₂(K) | det(ξ) ∈ F^×}, the inclusion ⊇)"]
theorem formula_7_3d_surj (hh : Q (h : V) ≠ 0) (ξ : Matrix (Fin 2) (Fin 2) (AU Q e f))
    (hξ : ∀ i j, ξ i j ∈ evenOdd (QU Q e f) 0) {c : F} (hc : c ≠ 0)
    (hdet : ξ 0 0 * ξ 1 1 - ξ 0 1 * ξ 1 0 = algebraMap F _ c) :
    ∃ u : Aˣ, u ∈ M0 Q ∧ xi he hf hef hg (u : A) = ξ := by
  obtain ⟨α, hαξ⟩ := (xi_bijective he hf hef hg).2 ξ
  have hα : α ∈ evenOdd Q 0 := (xi_mem_evenOdd_zero_iff he hf hef hg α).2 (by rw [hαξ]; exact hξ)
  have hcomm : ∀ i j k l, ξ i j * ξ k l = ξ k l * ξ i j := fun i j k l =>
    dim2_comm_of_even hgh hspan (hξ i j) (hξ k l)
  have hmul : α * reverse α = algebraMap F A c := by
    apply (xi_bijective he hf hef hg).1
    rw [map_mul, (formula_7_3c he hf hef hg hgh hspan α hα).2, hαξ, AlgHom.commutes]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.algebraMap_matrix_apply]
    · rw [← hdet, sub_eq_add_neg]
    · rw [hcomm 0 1 0 0]; abel
    · rw [hcomm 1 1 1 0]; abel
    · rw [← hdet, hcomm 1 1 0 0, hcomm 1 0 0 1]; abel
  obtain ⟨u, hu, hM⟩ := formula_7_3b he hf hef hg hgh hspan hh hα hc hmul
  exact ⟨u, hM, by rw [hu, hαξ]⟩

end Hyp

end Isotropic4

end QuadFormsKB.Shimura2004
