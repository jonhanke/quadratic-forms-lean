/-
# Cassels, Chapter 10, Theorem 7.1 for $n = 3$: strong approximation for the spin group of a ternary space

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Ch. 10, §7, Theorem 7.1 (p. 186) and its proof for
$n = 3$ (p. 188), with Lemma 7.1 (p. 187, a reformulation of Ch. 9, Theorem 1.5).

**Setting** (as in `Ch10/Thm71.lean`). $V$ is a $3$-dimensional $\mathbb Q$-vector space with a regular quadratic form
$Q$ (Cassels' $\phi$), indefinite (isotropic over $\mathbb R$); $\Lambda$ is a $\mathbb Z$-lattice in $V$ with basis
$e_0, e_1, e_2$ (`exists_basis_of_fg_span`); $V_p = \mathbb Q_p \otimes V$ has the basis $1 \otimes e_i$.

**Cassels' proof for $n = 3$.** By (7.11) the even Clifford algebra $C_0(V)$ consists of the
$u = u_0 + u_1\epsilon_0 + u_2\epsilon_1 + u_3\epsilon_2$ ($\epsilon_i = e_{i+1}e_{i+2} - f_{i+1,i+2}$, Ch. 10, Ex. 7,
`ternEvenElt`), and $uu' = g(u_0, \dots, u_3)$ is a quaternary quadratic form, $g(\mathbf u) = u_0^2 + \sum_{i,j}F_{ij}u_{i+1}u_{j+1}$
with $(F_{ij})$ the adjugate of the Gram matrix (`reverse_mul_ternEvenElt`). For $n = 3$, $\operatorname{Spin}(V)$ consists of the
$u \in C_0(V)$ with $uu' = 1$ (Ch. 10, Thm. 3.1, Cor. 2, `mem_M0_iff_ternary`), and likewise over $\mathbb Q_p$. The form $g$ is
indefinite because $V$ is. Choose $u^{(p)} \in \mathcal U_p$ for the finitely many $p$ in a set $P$; by Lemma 7.1 there is a
rational solution of $g(\mathbf u) = 1$, arbitrarily close to the coordinates of the $u^{(p)}$ and integral at every $p \notin P$; the
corresponding $u$ is the required element of $\operatorname{Spin}(V)$.

**Formalization notes.** Lemma 7.1 is used in the form of `Siegel.exists_rep_approx` (Ch. 9, Theorem 1.5 with approximation,
for an integer-valued form $f$; here $f = D\,g$ with $D$ a common denominator), after Cassels' rescaling by
$m = \prod_{p \in P} p^s$. "Arbitrarily close" is closeness of the four coordinates $u_i$ in $\mathbb Q_p$; the coordinate map
$\mathbb Q_p^4 \to C(V_p)$ is continuous for the vector space topology. The set $P$ consists of the primes at which
$\mathcal U_p \ne \operatorname{Spin}(\Lambda_p)$ and the primes dividing a denominator of the Gram matrix (where $\epsilon_i$ need
not lie in $C(\Lambda_p)$); Cassels' further conditions on $P$ ((ii)–(iv), p. 188) are not needed in this form.
-/
import QuadFormsKB.Literature.Cassels.Ch10.Thm71
import QuadFormsKB.Literature.Cassels.Ch10.Ternary
import QuadFormsKB.Literature.Cassels.Ch7.NotesLattices
import QuadFormsKB.Literature.Cassels.Ch9Sec8Int

open CliffordAlgebra TensorProduct Module

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Cassels.Thm71Ternary

open QuadFormsKB.Cassels

section BaseChange

variable {k V : Type*} [Field k] [Invertible (2 : k)] [AddCommGroup V] [Module k V]
  (K : Type*) [Field K] [Algebra k K] [Invertible (2 : K)] (Q : QuadraticForm k V)

/-- Helper: the polar form of the base change on vectors $1 \otimes a$, $1 \otimes b$ is the image of the polar form:
$B_K(1 \otimes a, 1 \otimes b) = B(a, b)$. Arguments: `K` the extension field, `Q` the form, `a`, `b` the vectors. -/
theorem associated_baseChange_one_tmul (a b : V) :
    QuadraticMap.associated (Q.baseChange K) ((1 : K) ⊗ₜ[k] a) ((1 : K) ⊗ₜ[k] b) =
      algebraMap k K (QuadraticMap.associated Q a b) := by
  have h1 := congrArg (fun B => B ((1 : K) ⊗ₜ[k] a) ((1 : K) ⊗ₜ[k] b))
    (QuadraticMap.two_nsmul_associated K (Q.baseChange K))
  have h2 := congrArg (fun B => B a b) (QuadraticMap.two_nsmul_associated k Q)
  simp only [LinearMap.smul_apply, QuadraticMap.polarBilin_apply_apply] at h1 h2
  have h3 : QuadraticMap.polar (Q.baseChange K) ((1 : K) ⊗ₜ[k] a) ((1 : K) ⊗ₜ[k] b) =
      algebraMap k K (QuadraticMap.polar Q a b) := by
    simp only [QuadraticMap.polar, ← tmul_add, QuadraticForm.baseChange_tmul, mul_one, Algebra.smul_def, map_sub]
  have h22 : (2 : K) ≠ 0 := two_ne_zero
  apply mul_left_cancel₀ h22
  rw [two_nsmul] at h1 h2
  have h4 := congrArg (algebraMap k K) h2
  rw [map_add] at h4
  change 2 * (QuadraticMap.associatedHom K (Q.baseChange K)) ((1 : K) ⊗ₜ[k] a) ((1 : K) ⊗ₜ[k] b) =
    2 * algebraMap k K ((QuadraticMap.associatedHom k Q) a b)
  linear_combination h1 + h3 - h4

/-- Helper: the Gram entries of the base-changed basis $1 \otimes e_i$ are the images of the Gram entries of $e$.
Arguments: `K` the extension field, `Q` the form, `e` the three vectors, `i`, `j` the indices. -/
theorem ternGram_baseChange (e : Fin 3 → V) (i j : Fin 3) :
    ternGram (Q.baseChange K) (fun l => (1 : K) ⊗ₜ[k] e l) i j = algebraMap k K (ternGram Q e i j) :=
  associated_baseChange_one_tmul K Q (e i) (e j)

/-- Helper: the Gram matrix of the base-changed vectors is the image of the Gram matrix. -/
theorem ternGramMatrix_baseChange (e : Fin 3 → V) :
    ternGramMatrix (Q.baseChange K) (fun l => (1 : K) ⊗ₜ[k] e l) = (ternGramMatrix Q e).map (algebraMap k K) := by
  ext i j
  exact ternGram_baseChange K Q e i j

/-- Helper: the natural map $C(V) \to C(V_K)$ sends Cassels' $\epsilon_i$ (for the vectors $e$) to the $\epsilon_i$ of the
vectors $1 \otimes e_l$. Arguments: `K`, `Q`, `e`, the index `i`. -/
theorem ofBaseChangeAux_ternEpsI (e : Fin 3 → V) (i : Fin 3) :
    ofBaseChangeAux K Q (ternEpsI Q e i) = ternEpsI (Q.baseChange K) (fun l => (1 : K) ⊗ₜ[k] e l) i := by
  simp only [ternEpsI, map_sub, map_mul, ofBaseChangeAux_ι, map_smul, map_one]
  rw [ternGram_baseChange, algebraMap_smul]

/-- Helper: the natural map $C(V) \to C(V_K)$ sends $u = x_0 + x_1\epsilon_0 + x_2\epsilon_1 + x_3\epsilon_2$ to the element with
the same coordinates (mapped to $K$) for the vectors $1 \otimes e_l$. Arguments: `K`, `Q`, `e`, the coordinates `x`. -/
theorem ofBaseChangeAux_ternEvenElt (e : Fin 3 → V) (x : Fin 4 → k) :
    ofBaseChangeAux K Q (ternEvenElt Q e x) =
      ternEvenElt (Q.baseChange K) (fun l => (1 : K) ⊗ₜ[k] e l) (fun i => algebraMap k K (x i)) := by
  simp only [ternEvenElt, map_add, map_smul, map_one, ofBaseChangeAux_ternEpsI, algebraMap_smul]

end BaseChange

section Norm

variable {k V : Type*} [Field k] [Invertible (2 : k)] [AddCommGroup V] [Module k V]
  {Q : QuadraticForm k V}

/-- **Cassels' quaternary norm form $g$** (Ch. 10, p. 188, (7.11) and the line after it; Ex. 7 (ii)): for the Gram matrix
$G$ of $e_0, e_1, e_2$, $g(\mathbf u) = u_0^2 + \sum_{i,j}F_{ij}u_{i+1}u_{j+1}$ with $F = \operatorname{adj} G$, so that
$uu' = g(\mathbf u)$ for $u = u_0 + u_1\epsilon_0 + u_2\epsilon_1 + u_3\epsilon_2$ (`reverse_mul_ternEvenElt`). Arguments: `G` the Gram
matrix, `x` the coordinates. -/
noncomputable def gNorm {R : Type*} [CommRing R] (G : Matrix (Fin 3) (Fin 3) R) (x : Fin 4 → R) : R :=
  x 0 ^ 2 + ∑ i, ∑ j, G.adjugate i j * x i.succ * x j.succ

/-- Helper: $u = x_0 + x_1\epsilon_0 + x_2\epsilon_1 + x_3\epsilon_2$ is even. -/
theorem ternEvenElt_mem_even (e : Fin 3 → V) (x : Fin 4 → k) : ternEvenElt Q e x ∈ evenOdd Q 0 := by
  have h1 : (1 : CliffordAlgebra Q) ∈ evenOdd Q 0 := one_le_evenOdd_zero Q (Submodule.mem_one.2 ⟨1, map_one _⟩)
  unfold ternEvenElt
  refine add_mem (add_mem (add_mem (Submodule.smul_mem _ _ h1) (Submodule.smul_mem _ _ (ternEpsI_mem_even 0)))
    (Submodule.smul_mem _ _ (ternEpsI_mem_even 1))) (Submodule.smul_mem _ _ (ternEpsI_mem_even 2))

/-- **Cassels, Ch. 10, p. 188: for $n = 3$, $\operatorname{Spin}(V)$ consists of the $u \in C_0(V)$ with $g(\mathbf u) = 1$** (the
"if" direction). If $\dim V = 3$, $Q$ is regular and the coordinates $x$ satisfy $g(x) = 1$, then
$u = x_0 + x_1\epsilon_0 + x_2\epsilon_1 + x_3\epsilon_2 \in \operatorname{Spin}(V)$. Uses Ch. 10, Thm. 3.1, Cor. 2
(`mem_M0_iff_ternary`) and Cassels' definition of $\operatorname{Spin}$ (`mem_spinGroup_iff`). Arguments: `hQ` regularity,
`hn` $\dim V = 3$, `e` the three vectors, `x` the coordinates, `hx` $g(x) = 1$. -/
theorem ternEvenElt_mem_spinGroup [FiniteDimensional k V] (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hn : finrank k V = 3) (e : Fin 3 → V) (x : Fin 4 → k) (hx : gNorm (ternGramMatrix Q e) x = 1) :
    ternEvenElt Q e x ∈ spinGroup Q := by
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hn
  set u := ternEvenElt Q e x
  have hev : u ∈ evenOdd Q 0 := ternEvenElt_mem_even e x
  have h1 : u * reverse u = 1 := by
    rw [(reverse_mul_ternEvenElt x).2]
    have : x 0 ^ 2 + ∑ i, ∑ j, (ternGramMatrix Q e).adjugate i j * x i.succ * x j.succ = 1 := hx
    rw [this, one_smul]
  obtain ⟨U, hU, hUu⟩ := (mem_M0_iff_ternary hQ hn u).2 ⟨hev, by rw [h1]; exact one_ne_zero⟩
  rw [mem_spinGroup_iff hQ]
  refine ⟨hev, h1, fun y => ?_⟩
  obtain ⟨z, hz⟩ := hU.2 y
  have hinv : ((U⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = reverse u :=
    Units.inv_eq_of_mul_eq_one_right (by rw [hUu]; exact h1)
  exact ⟨z, by rw [hz, hinv, hUu]⟩

/-- **Coordinates of an element of $\operatorname{Spin}(V)$** (Cassels, Ch. 10, (7.11)): if $b$ is a basis of $V$ ($\dim V = 3$),
every $u \in \operatorname{Spin}(V)$ is $x_0 + x_1\epsilon_0 + x_2\epsilon_1 + x_3\epsilon_2$ with $g(x) = 1$. Arguments: `b` the basis,
`u` the element. -/
theorem exists_ternEvenElt_of_mem_spinGroup (b : Basis (Fin 3) k V) (u : spinGroup Q) :
    ∃ x : Fin 4 → k, (u : CliffordAlgebra Q) = ternEvenElt Q b x ∧ gNorm (ternGramMatrix Q b) x = 1 := by
  have : FiniteDimensional k V := Module.Finite.of_basis b
  have hev : (u : CliffordAlgebra Q) ∈ evenOdd Q 0 := spinGroup.mem_even u.2
  have hint : (u : CliffordAlgebra Q) ∈ intCliffordEven Q (ternLat k b) := by
    rw [mem_intCliffordEven]
    refine ⟨?_, hev⟩
    rw [ternLat, Basis.span_eq, intClifford_top]
    trivial
  have hspan := (mem_intCliffordEven_ternLat_iff (I := k) (f := ternGramMatrix Q b)
    (fun i j => by simp [ternGramMatrix]) _).1 hint
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 hspan
  have hu : (u : CliffordAlgebra Q) = ternEvenElt Q b c := by
    rw [← hc, Fin.sum_univ_four]
    simp [ternEvenElt]
  refine ⟨c, hu, ?_⟩
  have h1 := spinGroup_mul_reverse u
  rw [hu, (reverse_mul_ternEvenElt c).2] at h1
  have h2 : algebraMap k (CliffordAlgebra Q) (gNorm (ternGramMatrix Q b) c) = algebraMap k _ 1 := by
    rw [map_one, Algebra.algebraMap_eq_smul_one]
    exact h1
  exact (algebraMap k (CliffordAlgebra Q)).injective h2

end Norm

section IntForm

/-- **The integral multiple $f = D\,g$ of the norm form** (Cassels' rescaling in the proof of Lemma 7.1, p. 188): for an integer
$D$ and a symmetric integer matrix $N$ (in the application $N = D\operatorname{adj}G$), the integral quaternary form
$f(\mathbf x) = Dx_0^2 + \sum_{i,j}N_{ij}x_{i+1}x_{j+1}$ (as an upper triangular `QuadForm`). Arguments: `D`, `N`. -/
def intNormForm (D : ℤ) (N : Fin 3 → Fin 3 → ℤ) : QuadForm ℤ 4 :=
  QuadForm.ofUpper ![![D, 0, 0, 0], ![0, N 0 0, 2 * N 0 1, 2 * N 0 2], ![0, 0, N 1 1, 2 * N 1 2],
    ![0, 0, 0, N 2 2]]

/-- Helper: the value of `intNormForm D N` (for symmetric `N`) over any commutative ring. -/
theorem evalIn_intNormForm {K : Type*} [CommRing K] (D : ℤ) (N : Fin 3 → Fin 3 → ℤ) (hN : ∀ i j, N i j = N j i)
    (x : Fin 4 → K) :
    (intNormForm D N).evalIn K x = (D : K) * x 0 ^ 2 + ∑ i, ∑ j, (N i j : K) * x i.succ * x j.succ := by
  simp only [intNormForm, QuadForm.evalIn, QuadForm.ofUpper, Fin.sum_univ_four, Fin.sum_univ_three,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, algebraMap_int_eq, eq_intCast]
  have h3 : (2 : Fin 3).succ = 3 := rfl
  rw [h3, hN 1 0, hN 2 0, hN 2 1]
  simp only [show ¬ ((1 : Fin 4) ≤ 0) by decide, show ¬ ((2 : Fin 4) ≤ 0) by decide,
    show ¬ ((3 : Fin 4) ≤ 0) by decide, show ¬ ((2 : Fin 4) ≤ 1) by decide, show ¬ ((3 : Fin 4) ≤ 1) by decide,
    show ¬ ((3 : Fin 4) ≤ 2) by decide, show ((0 : Fin 4) ≤ 0) by decide, show ((0 : Fin 4) ≤ 1) by decide,
    show ((0 : Fin 4) ≤ 2) by decide, show ((0 : Fin 4) ≤ 3) by decide, show ((1 : Fin 4) ≤ 1) by decide,
    show ((1 : Fin 4) ≤ 2) by decide, show ((1 : Fin 4) ≤ 3) by decide, show ((2 : Fin 4) ≤ 2) by decide,
    show ((2 : Fin 4) ≤ 3) by decide, show ((3 : Fin 4) ≤ 3) by decide, ite_true, ite_false]
  push_cast
  ring

/-- Helper: the determinant of the Hessian of `intNormForm D N`, in $\mathbb Q$: $2^4D\det N$ (for symmetric `N`). -/
theorem det_hessian_intNormForm (D : ℤ) (N : Fin 3 → Fin 3 → ℤ) (hN : ∀ i j, N i j = N j i) :
    (intNormForm D N).hessian.det = 2 ^ 4 * D * (Matrix.of N).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_four, Matrix.det_fin_three, Matrix.det_fin_three,
    Matrix.det_fin_three, Matrix.det_fin_three, Matrix.det_fin_three]
  simp only [QuadForm.hessian, intNormForm, QuadForm.ofUpper, Matrix.add_apply, Matrix.transpose_apply,
    Matrix.submatrix_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.vecHead,
    Matrix.vecTail, Function.comp_apply]
  simp (config := { decide := true }) only [Fin.succAbove, Fin.succ, Fin.castSucc, Fin.castAdd, Fin.castLE,
    ite_true, ite_false]
  rw [hN 1 0, hN 2 0, hN 2 1]
  simp (config := { decide := true })
  ring

end IntForm

section Real

open Matrix

/-- **The norm form is indefinite when $V$ is** (Cassels, p. 188: "Since $V$ is indefinite, the form $g$ is also indefinite"),
in matrix form: if the real symmetric matrix $G$ is regular and $w^{\mathsf T}Gw = 0$ for some $w \ne 0$, then
$z^{\mathsf T}(\operatorname{adj}G)z < 0$ for some $z$. Proof: with $y = Gw \ne 0$ and $v = w + ty$,
$v^{\mathsf T}Gv = 2t\,y^{\mathsf T}y + t^2y^{\mathsf T}Gy$; for $z = Gv$, $z^{\mathsf T}(\operatorname{adj}G)z = \det G \cdot v^{\mathsf T}Gv$, and
$t = -\varepsilon\det G$ with $\varepsilon > 0$ small makes this negative. Arguments: `G`, `hG` symmetry, `hdet`, `w`, `hw`, `hiso`. -/
theorem exists_neg_adjugate {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : Gᵀ = G) (hdet : G.det ≠ 0) {w : Fin 3 → ℝ}
    (hw : w ≠ 0) (hiso : w ⬝ᵥ G *ᵥ w = 0) : ∃ z : Fin 3 → ℝ, z ⬝ᵥ G.adjugate *ᵥ z < 0 := by
  obtain ⟨y, hy⟩ : ∃ y, y = G *ᵥ w := ⟨_, rfl⟩
  have hy0 : y ≠ 0 := fun h => hw (Matrix.eq_zero_of_mulVec_eq_zero hdet (hy ▸ h))
  obtain ⟨s, hs⟩ : ∃ s, s = y ⬝ᵥ y := ⟨_, rfl⟩
  have hspos : 0 < s := by
    have h0 : 0 ≤ s := hs ▸ Finset.sum_nonneg fun i _ => mul_self_nonneg (y i)
    exact lt_of_le_of_ne h0 fun h => hy0 (dotProduct_self_eq_zero.mp (hs ▸ h.symm))
  have hsym : ∀ a b : Fin 3 → ℝ, a ⬝ᵥ G *ᵥ b = b ⬝ᵥ G *ᵥ a := by
    intro a b
    rw [dotProduct_mulVec, ← mulVec_transpose, hG, dotProduct_comm]
  have hwy : w ⬝ᵥ G *ᵥ y = s := by rw [hsym, hs, hy]
  set c := y ⬝ᵥ G *ᵥ y with hc
  set d := G.det with hd
  have hquad : ∀ t : ℝ, (w + t • y) ⬝ᵥ G *ᵥ (w + t • y) = 2 * t * s + t ^ 2 * c := by
    intro t
    simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct,
      smul_eq_mul, hiso, hwy]
    rw [hsym y w, hwy]
    ring
  have hadj : ∀ v : Fin 3 → ℝ, (G *ᵥ v) ⬝ᵥ G.adjugate *ᵥ (G *ᵥ v) = d * (v ⬝ᵥ G *ᵥ v) := by
    intro v
    rw [mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul, dotProduct_comm]
  set ε := s / (|d * c| + 1) with hε
  have hεpos : 0 < ε := div_pos hspos (by positivity)
  have hεs : |d * c| * ε < s := by
    rw [hε, mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg (d * c)]
  refine ⟨G *ᵥ (w + (-(ε * d)) • y), ?_⟩
  rw [hadj, hquad]
  have hd2 : 0 < d ^ 2 := by positivity
  have hle : d * ε * c ≤ |d * c| * ε := by
    have := le_abs_self (d * c)
    nlinarith
  have key : d * (2 * -(ε * d) * s + (-(ε * d)) ^ 2 * c) = d ^ 2 * ε * (-2 * s + d * ε * c) := by ring
  rw [key]
  have h1 : -2 * s + d * ε * c < 0 := by linarith
  have h2 : 0 < d ^ 2 * ε := mul_pos hd2 hεpos
  nlinarith

/-- Helper: $Q(x) = \xi^{\mathsf T}G\xi$ for the coordinates $\xi$ of $x$ in a basis $b$ with Gram matrix $G$. Arguments: `Q`,
`b` the basis, `x` the vector. -/
theorem eq_dotProduct_ternGram {K W : Type*} [Field K] [Invertible (2 : K)] [AddCommGroup W] [Module K W]
    (Q : QuadraticForm K W) (b : Basis (Fin 3) K W) (x : W) :
    Q x = b.equivFun x ⬝ᵥ ternGramMatrix Q b *ᵥ b.equivFun x := by
  rw [← QuadraticMap.associated_eq_self_apply K Q x]
  conv_lhs => rw [← b.sum_equivFun x]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, dotProduct, mulVec,
    ternGramMatrix, ternGram, Matrix.of_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  change b.equivFun x j * (b.equivFun x i * (QuadraticMap.associated Q (b i) (b j))) = _
  ring

/-- Helper: the Gram matrix of a basis of a regular space has nonzero determinant. -/
theorem det_ternGramMatrix_ne_zero {K W : Type*} [Field K] [Invertible (2 : K)] [AddCommGroup W] [Module K W]
    {Q : QuadraticForm K W} (hQ : (QuadraticMap.associated Q).Nondegenerate) (b : Basis (Fin 3) K W) :
    (ternGramMatrix Q b).det ≠ 0 := by
  have h := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).1 hQ
  have e : LinearMap.BilinForm.toMatrix b (QuadraticMap.associated Q) = ternGramMatrix Q b := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    rfl
  rwa [e] at h

/-- Helper: the Gram matrix is symmetric. -/
theorem ternGramMatrix_transpose {K W : Type*} [Field K] [Invertible (2 : K)] [AddCommGroup W] [Module K W]
    (Q : QuadraticForm K W) (e : Fin 3 → W) : (ternGramMatrix Q e)ᵀ = ternGramMatrix Q e := by
  ext i j
  exact ternGram_comm i j

/-- **The norm form of an indefinite ternary space is indefinite** (Cassels, p. 188): if $V$ (with basis $b$, Gram matrix $G$) is
isotropic over $\mathbb R$, then $z^{\mathsf T}(\operatorname{adj}G)z < 0$ for some real $z$. Arguments: `hQ` regularity, `b` the
basis, `hind` a nonzero real isotropic vector. -/
theorem exists_neg_adjugate_of_indef {V : Type*} [AddCommGroup V] [Module ℚ V] {Q : QuadraticForm ℚ V}
    (hQ : (QuadraticMap.associated Q).Nondegenerate) (b : Basis (Fin 3) ℚ V)
    (hind : ∃ x : ℝ ⊗[ℚ] V, x ≠ 0 ∧ Q.baseChange ℝ x = 0) :
    ∃ z : Fin 3 → ℝ, z ⬝ᵥ ((ternGramMatrix Q b).map (algebraMap ℚ ℝ)).adjugate *ᵥ z < 0 := by
  obtain ⟨x, hx0, hx⟩ := hind
  set bR := Algebra.TensorProduct.basis ℝ b
  have hG : ternGramMatrix (Q.baseChange ℝ) bR = (ternGramMatrix Q b).map (algebraMap ℚ ℝ) := by
    have : (bR : Fin 3 → ℝ ⊗[ℚ] V) = fun l => (1 : ℝ) ⊗ₜ[ℚ] b l := by
      funext l; exact Algebra.TensorProduct.basis_apply b l
    rw [this, ternGramMatrix_baseChange]
  refine exists_neg_adjugate (w := bR.equivFun x) ?_ ?_ ?_ ?_
  · rw [← hG]; exact ternGramMatrix_transpose _ _
  · have h := det_ternGramMatrix_ne_zero hQ b
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 h
  · intro h
    exact hx0 (bR.equivFun.injective (by rw [h, map_zero]))
  · rw [← hG, ← eq_dotProduct_ternGram]
    exact hx

end Real

section Local

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (Q : QuadraticForm ℚ V)
  (p : ℕ) [Fact p.Prime]

/-- Helper: the coordinate map $\mathbb Q_p^4 \to C(V_p)$, $x \mapsto x_0 + x_1\epsilon_0 + x_2\epsilon_1 + x_3\epsilon_2$, is continuous for the
vector space topology of $C(V_p)$. Arguments: `Q`, `p`, the vectors `e`. -/
theorem continuous_ternEvenElt (e : Fin 3 → ℚ_[p] ⊗[ℚ] V) :
    @Continuous _ _ _ (cliffordTopology (Q.baseChange ℚ_[p]))
      (fun x : Fin 4 → ℚ_[p] => ternEvenElt (Q.baseChange ℚ_[p]) e x) := by
  let _ : TopologicalSpace (CliffordAlgebra (Q.baseChange ℚ_[p])) := cliffordTopology (Q.baseChange ℚ_[p])
  have : IsModuleTopology ℚ_[p] (CliffordAlgebra (Q.baseChange ℚ_[p])) := ⟨rfl⟩
  have : ContinuousAdd (CliffordAlgebra (Q.baseChange ℚ_[p])) := IsModuleTopology.toContinuousAdd ℚ_[p] _
  have : ContinuousSMul ℚ_[p] (CliffordAlgebra (Q.baseChange ℚ_[p])) := IsModuleTopology.toContinuousSMul ℚ_[p] _
  unfold ternEvenElt
  fun_prop

/-- **Local step of the proof for $n = 3$** (Cassels, p. 188: "let $u^{(p)} \in \mathcal U_p$ ... with coordinates
$(u^{(p)}_0, \dots, u^{(p)}_3)$"): for a non-empty open $\mathcal U \subseteq \operatorname{Spin}(V_p)$ and a basis $b$ of $V_p$ there are
coordinates $x$ with $g(x) = 1$ and an exponent $K$ such that every $w \in \operatorname{Spin}(V_p)$ whose coordinates $y$ satisfy
$|y_i - x_i|_p \le p^{-K}$ lies in $\mathcal U$. Arguments: `Q`, `p`, the basis `b`, the set `U`, `hne`, `hopen`. -/
theorem exists_local_coords (b : Basis (Fin 3) ℚ_[p] (ℚ_[p] ⊗[ℚ] V)) (U : Set (spinGroup (Q.baseChange ℚ_[p])))
    (hne : U.Nonempty)
    (hopen : @IsOpen _ (@instTopologicalSpaceSubtype _ _ (cliffordTopology (Q.baseChange ℚ_[p]))) U) :
    ∃ x : Fin 4 → ℚ_[p], gNorm (ternGramMatrix (Q.baseChange ℚ_[p]) b) x = 1 ∧ ∃ K : ℕ,
      ∀ (w : spinGroup (Q.baseChange ℚ_[p])) (y : Fin 4 → ℚ_[p]),
        (w : CliffordAlgebra (Q.baseChange ℚ_[p])) = ternEvenElt (Q.baseChange ℚ_[p]) b y →
        (∀ i, ‖y i - x i‖ ≤ (p : ℝ) ^ (-(K : ℤ))) → w ∈ U := by
  let _ : TopologicalSpace (CliffordAlgebra (Q.baseChange ℚ_[p])) := cliffordTopology (Q.baseChange ℚ_[p])
  obtain ⟨O, hO, hOU⟩ := isOpen_induced_iff.1 hopen
  obtain ⟨w₀, hw₀⟩ := hne
  obtain ⟨x, hx, hxn⟩ := exists_ternEvenElt_of_mem_spinGroup b w₀
  refine ⟨x, hxn, ?_⟩
  have hc := continuous_ternEvenElt Q p (⇑b)
  have hpre : IsOpen ((fun y : Fin 4 → ℚ_[p] => ternEvenElt (Q.baseChange ℚ_[p]) b y) ⁻¹' O) := hO.preimage hc
  have hxO : x ∈ (fun y : Fin 4 → ℚ_[p] => ternEvenElt (Q.baseChange ℚ_[p]) b y) ⁻¹' O := by
    show ternEvenElt _ _ x ∈ O
    rw [← hx]
    have : w₀ ∈ Subtype.val ⁻¹' O := by rw [hOU]; exact hw₀
    exact this
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hpre x hxO
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hp1)
  refine ⟨K, fun w y hwy hy => ?_⟩
  have hdist : dist y x < ε := by
    rw [dist_pi_lt_iff hε]
    intro i
    rw [dist_eq_norm]
    refine lt_of_le_of_lt (hy i) ?_
    rwa [zpow_neg, zpow_natCast, ← inv_pow]
  have hmem := hball hdist
  rw [← hOU]
  show (w : CliffordAlgebra _) ∈ O
  rw [hwy]
  exact hmem

end Local

section Helpers

/-- Helper: a common denominator of finitely many rationals. -/
theorem exists_common_den {ι : Type*} [Fintype ι] (r : ι → ℚ) : ∃ D : ℕ, 0 < D ∧ ∀ i, ∃ z : ℤ, (z : ℚ) = D * r i := by
  classical
  refine ⟨∏ i, (r i).den, Finset.prod_pos fun i _ => (r i).den_pos, fun i => ?_⟩
  obtain ⟨m, hm⟩ : (r i).den ∣ ∏ j, (r j).den := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  refine ⟨m * (r i).num, ?_⟩
  rw [hm]
  push_cast
  rw [← Rat.mul_den_eq_num (r i)]
  ring

/-- Helper: $g(cx) = c^2g(x)$. -/
theorem gNorm_smul {R : Type*} [CommRing R] (G : Matrix (Fin 3) (Fin 3) R) (c : R) (x : Fin 4 → R) :
    gNorm G (c • x) = c ^ 2 * gNorm G x := by
  simp only [gNorm, Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

/-- Helper: `intNormForm D N` is $D\,g$ when $N = D\operatorname{adj}G$ (`hN`), over any field containing $\mathbb Q$. -/
theorem evalIn_intNormForm_eq {K : Type*} [Field K] [Algebra ℚ K] (G : Matrix (Fin 3) (Fin 3) ℚ) (D : ℕ)
    (N : Fin 3 → Fin 3 → ℤ) (hNs : ∀ i j, N i j = N j i) (hN : ∀ i j, (N i j : ℚ) = D * G.adjugate i j)
    (x : Fin 4 → K) :
    (intNormForm D N).evalIn K x = D * gNorm (G.map (algebraMap ℚ K)) x := by
  rw [evalIn_intNormForm _ _ hNs, gNorm]
  have hadj : (G.map (algebraMap ℚ K)).adjugate = G.adjugate.map (algebraMap ℚ K) := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, RingHom.map_adjugate]
  have hNK : ∀ i j, (N i j : K) = D * algebraMap ℚ K (G.adjugate i j) := by
    intro i j
    rw [← map_intCast (algebraMap ℚ K), hN, map_mul, map_natCast]
  simp only [hadj, Matrix.map_apply, hNK, mul_add, Finset.mul_sum]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Helper: the Hessian of `intNormForm D N` is regular when $D \ne 0$ and $N = D\operatorname{adj}G$ with $\det G \ne 0$. -/
theorem det_hessian_intNormForm_ne_zero (G : Matrix (Fin 3) (Fin 3) ℚ) (hG : G.det ≠ 0) (D : ℕ) (hD : 0 < D)
    (N : Fin 3 → Fin 3 → ℤ) (hNs : ∀ i j, N i j = N j i) (hN : ∀ i j, (N i j : ℚ) = D * G.adjugate i j) :
    (intNormForm D N).hessian.det ≠ 0 := by
  rw [det_hessian_intNormForm _ _ hNs]
  have hdetN : ((Matrix.of N).det : ℚ) = (D : ℚ) ^ 3 * G.det ^ 2 := by
    have h1 : (Int.castRingHom ℚ).mapMatrix (Matrix.of N) = (D : ℚ) • G.adjugate := by
      ext i j
      simp [hN]
    rw [← eq_intCast (Int.castRingHom ℚ), RingHom.map_det, h1, Matrix.det_smul, Matrix.det_adjugate]
    simp
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  intro h0
  have : ((2 ^ 4 * (D : ℤ) * (Matrix.of N).det : ℤ) : ℚ) = 0 := by rw [h0]; simp
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_natCast] at this
  rw [hdetN] at this
  have : (2 : ℚ) ^ 4 * D * (D ^ 3 * G.det ^ 2) ≠ 0 := by positivity
  contradiction

/-- Helper: the $p$-adic absolute value of $M = \prod_{q \in P} q^s$ is $p^{-s}$ for $p \in P$. -/
theorem norm_prod_pow_of_mem (P : Finset Nat.Primes) (s : ℕ) (p : Nat.Primes) (hp : p ∈ P) :
    ‖(((∏ q ∈ P, (q : ℕ) ^ s : ℕ)) : ℚ_[(p : ℕ)])‖ = ((p : ℕ) : ℝ) ^ (-(s : ℤ)) := by
  rw [← Finset.mul_prod_erase P _ hp, Nat.cast_mul, norm_mul, Nat.cast_pow, Padic.norm_p_pow]
  have : ‖(((∏ q ∈ P.erase p, (q : ℕ) ^ s : ℕ)) : ℚ_[(p : ℕ)])‖ = 1 := by
    rw [Padic.norm_natCast_eq_one_iff]
    refine Nat.Coprime.prod_right fun q hq => Nat.Coprime.pow_right _ ?_
    exact (Nat.coprime_primes p.2 q.2).2 fun h => (Finset.ne_of_mem_erase hq) (Subtype.ext h.symm)
  rw [this, mul_one]

/-- Helper: $M = \prod_{q \in P} q^s$ is a $p$-adic unit for $p \notin P$. -/
theorem norm_prod_pow_of_not_mem (P : Finset Nat.Primes) (s : ℕ) (p : Nat.Primes) (hp : p ∉ P) :
    ‖(((∏ q ∈ P, (q : ℕ) ^ s : ℕ)) : ℚ_[(p : ℕ)])‖ = 1 := by
  rw [Padic.norm_natCast_eq_one_iff]
  refine Nat.Coprime.prod_right fun q hq => Nat.Coprime.pow_right _ ?_
  exact (Nat.coprime_primes p.2 q.2).2 fun h => hp (by rwa [show p = q from Subtype.ext h])

/-- Helper: a $p$-adic number of absolute value at most $1$ as a $p$-adic integer ($0$ otherwise). -/
noncomputable def toZp {p : ℕ} [Fact p.Prime] (x : ℚ_[p]) : ℤ_[p] :=
  ⟨if ‖x‖ ≤ 1 then x else 0, by split_ifs with h <;> simp [h]⟩

theorem coe_toZp {p : ℕ} [Fact p.Prime] {x : ℚ_[p]} (h : ‖x‖ ≤ 1) : ((toZp x : ℤ_[p]) : ℚ_[p]) = x := by
  show (if ‖x‖ ≤ 1 then x else 0) = x
  simp [h]

end Helpers

section Main

open Matrix

/-- **Cassels, Ch. 10, Theorem 7.1 for $n = 3$** (Strong Approximation Theorem for the Spin Group, p. 186; proof for $n = 3$,
p. 188). Let $V$ be a $3$-dimensional regular indefinite quadratic space over $\mathbb Q$ and $\Lambda$ a $\mathbb Z$-lattice in $V$; for
every prime $p$ let $\mathcal U_p$ be a non-empty open subset of $\operatorname{Spin}(V_p)$, with $\mathcal U_p = \operatorname{Spin}(\Lambda_p)$
for almost all $p$ (7.3). Then some $u \in \operatorname{Spin}(V)$ lies in $\mathcal U_p$ for every $p$ (7.4). The hypotheses are those
of `SpinStrongApproximation` with $\dim V = 3$ (`hn`). Proof: Cassels' (module docstring). -/
@[kb "cassels1978" "Ch. 10, Thm. 7.1, p. 186; proof for n = 3, p. 188"]
theorem spinStrongApproximation_three (V : Type) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (Q : QuadraticForm ℚ V) (hn : Module.finrank ℚ V = 3) (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hind : ∃ x : ℝ ⊗[ℚ] V, x ≠ 0 ∧ Q.baseChange ℝ x = 0)
    (Λ : Submodule ℤ V) (hfg : Λ.FG) (hspan : Submodule.span ℚ (Λ : Set V) = ⊤)
    (U : ∀ (p : ℕ) [Fact p.Prime], Set (spinGroup (Q.baseChange ℚ_[p])))
    (hne : ∀ (p : ℕ) [Fact p.Prime], (U p).Nonempty)
    (hopen : ∀ (p : ℕ) [Fact p.Prime],
      @IsOpen _ (@instTopologicalSpaceSubtype _ _ (cliffordTopology (Q.baseChange ℚ_[p]))) (U p))
    (hcof : {p : ℕ | ∃ hp : p.Prime, haveI : Fact p.Prime := ⟨hp⟩;
      U p ≠ (intSpin (Q := Q.baseChange ℚ_[p]) (baseChangeLat ℚ_[p] ℤ_[p] Λ) : Set _)}.Finite) :
    ∃ u : spinGroup Q, ∀ (p : ℕ) [Fact p.Prime], spinBaseChange ℚ_[p] Q u ∈ U p := by
  classical
  -- a basis $e$ of $\Lambda$
  obtain ⟨b₀, hb₀li, hΛ⟩ := exists_basis_of_fg_span (I := ℤ) (k := ℚ) Λ hfg hspan
  set e : Fin 3 → V := fun i => b₀ (Fin.cast hn.symm i) with he
  have heli : LinearIndependent ℚ e := hb₀li.comp _ (Fin.cast_injective _)
  have hΛe : ∀ i, e i ∈ Λ := fun i => by rw [hΛ]; exact Submodule.subset_span ⟨_, rfl⟩
  set eV : Basis (Fin 3) ℚ V := basisOfLinearIndependentOfCardEqFinrank heli (by simp [hn]) with heVdef
  have heV : ⇑eV = e := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  -- the Gram matrix, its common denominators and the integral form $f = D g$
  set G := ternGramMatrix Q e with hGdef
  have hGt : Gᵀ = G := ternGramMatrix_transpose Q e
  have hGdet : G.det ≠ 0 := by
    have := det_ternGramMatrix_ne_zero hQ eV
    rwa [heV] at this
  obtain ⟨Dg, hDg, hDgz⟩ := exists_common_den (fun ij : Fin 3 × Fin 3 => G ij.1 ij.2)
  obtain ⟨D, hD, hDz⟩ := exists_common_den (fun ij : Fin 3 × Fin 3 => G.adjugate ij.1 ij.2)
  choose N₀ hN₀ using hDz
  set N : Fin 3 → Fin 3 → ℤ := fun i j => N₀ (i, j) with hNdef
  have hN : ∀ i j, (N i j : ℚ) = D * G.adjugate i j := fun i j => hN₀ (i, j)
  have hAs : ∀ i j, G.adjugate i j = G.adjugate j i := by
    intro i j
    have h := congrFun (congrFun (Matrix.adjugate_transpose G) i) j
    rw [hGt, Matrix.transpose_apply] at h
    exact h.symm
  have hNs : ∀ i j, N i j = N j i := by
    intro i j
    have : (N i j : ℚ) = N j i := by rw [hN, hN, hAs]
    exact_mod_cast this
  set f := intNormForm D N with hfdef
  have hfK : ∀ (K : Type) [Field K] [Algebra ℚ K] (x : Fin 4 → K),
      f.evalIn K x = D * gNorm (G.map (algebraMap ℚ K)) x :=
    fun K _ _ x => evalIn_intNormForm_eq G D N hNs hN x
  have hfdet : f.hessian.det ≠ 0 := det_hessian_intNormForm_ne_zero G hGdet D hD N hNs hN
  -- $f$ is indefinite over $\mathbb R$
  have hfind : ∃ x y : Fin 4 → ℝ, f.evalIn ℝ x < 0 ∧ 0 < f.evalIn ℝ y := by
    obtain ⟨z, hz⟩ := exists_neg_adjugate_of_indef hQ eV hind
    rw [heV] at hz
    refine ⟨Fin.cons 0 z, Fin.cons 1 0, ?_, ?_⟩
    · rw [hfK, gNorm]
      have hD' : (0 : ℝ) < D := by exact_mod_cast hD
      have e1 : (∑ i, ∑ j, (G.map (algebraMap ℚ ℝ)).adjugate i j * (Fin.cons 0 z : Fin 4 → ℝ) i.succ *
          (Fin.cons 0 z : Fin 4 → ℝ) j.succ) = z ⬝ᵥ (G.map (algebraMap ℚ ℝ)).adjugate *ᵥ z := by
        simp only [Fin.cons_succ, dotProduct, Matrix.mulVec, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      simp only [Fin.cons_zero, e1]
      nlinarith
    · rw [hfK, gNorm]
      simp only [Fin.cons_zero, Fin.cons_succ, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
        add_zero, one_pow, mul_one]
      exact_mod_cast hD
  -- local data
  have hbP : ∀ (p : ℕ) [Fact p.Prime], ⇑(Algebra.TensorProduct.basis ℚ_[p] eV) =
      fun l => (1 : ℚ_[p]) ⊗ₜ[ℚ] e l := by
    intro p _
    funext l
    rw [Algebra.TensorProduct.basis_apply, heV]
  have hGp : ∀ (p : ℕ) [Fact p.Prime], ternGramMatrix (Q.baseChange ℚ_[p]) (Algebra.TensorProduct.basis ℚ_[p] eV) =
      G.map (algebraMap ℚ ℚ_[p]) := by
    intro p _
    rw [hbP, ternGramMatrix_baseChange]
  have hloc : ∀ p : Nat.Primes, ∃ x : Fin 4 → ℚ_[(p : ℕ)], gNorm (G.map (algebraMap ℚ ℚ_[(p : ℕ)])) x = 1 ∧
      (∃ K : ℕ, ∀ (w : spinGroup (Q.baseChange ℚ_[(p : ℕ)])) (y : Fin 4 → ℚ_[(p : ℕ)]),
        (w : CliffordAlgebra (Q.baseChange ℚ_[(p : ℕ)])) =
          ternEvenElt (Q.baseChange ℚ_[(p : ℕ)]) (Algebra.TensorProduct.basis ℚ_[(p : ℕ)] eV) y →
        (∀ i, ‖y i - x i‖ ≤ ((p : ℕ) : ℝ) ^ (-(K : ℤ))) → w ∈ U p) ∧
      ∃ s : ℕ, ∀ i, ‖x i‖ ≤ ((p : ℕ) : ℝ) ^ (s : ℤ) := by
    intro p
    obtain ⟨x, hx, K, hK⟩ := exists_local_coords Q p (Algebra.TensorProduct.basis ℚ_[(p : ℕ)] eV) (U p) (hne p)
      (hopen p)
    rw [hGp] at hx
    have hp1 : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.one_lt
    obtain ⟨s, hs⟩ := pow_unbounded_of_one_lt ‖x‖ hp1
    exact ⟨x, hx, ⟨K, hK⟩, s, fun i => (norm_le_pi_norm x i).trans (by rw [zpow_natCast]; exact hs.le)⟩
  choose xp hxp hKp hsp using hloc
  choose Kp hKp using hKp
  choose sp hsp using hsp
  -- the finite set $P$ and Cassels' rescaling $M = \prod_{p \in P} p^s$
  set Pn : Finset ℕ := hcof.toFinset ∪ Dg.primeFactors with hPn
  set P : Finset Nat.Primes := Pn.subtype Nat.Prime with hP
  set s : ℕ := P.sup sp with hs
  set K : ℕ := P.sup Kp with hK
  set M : ℕ := ∏ q ∈ P, (q : ℕ) ^ s with hM
  have hMpos : 0 < M := Finset.prod_pos fun q _ => pow_pos q.2.pos _
  -- the local target vectors $M x^{(p)}$
  have hbint : ∀ p ∈ P, ∀ i, ‖(M : ℚ_[(p : ℕ)]) * xp p i‖ ≤ 1 := by
    intro p hp i
    rw [norm_mul, norm_prod_pow_of_mem P s p hp]
    have hp1 : (1 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.2.one_lt.le
    have h1 : ‖xp p i‖ ≤ ((p : ℕ) : ℝ) ^ (s : ℤ) :=
      (hsp p i).trans (zpow_le_zpow_right₀ hp1 (by exact_mod_cast Finset.le_sup (f := sp) hp))
    have hpos : (0 : ℝ) < ((p : ℕ) : ℝ) ^ (-(s : ℤ)) := by positivity
    calc ((p : ℕ) : ℝ) ^ (-(s : ℤ)) * ‖xp p i‖ ≤ ((p : ℕ) : ℝ) ^ (-(s : ℤ)) * ((p : ℕ) : ℝ) ^ (s : ℤ) :=
          mul_le_mul_of_nonneg_left h1 hpos.le
      _ = 1 := by rw [← zpow_add₀ (by positivity), neg_add_cancel, zpow_zero]
  set b : ∀ p : Nat.Primes, Fin 4 → ℤ_[(p : ℕ)] := fun p i => toZp ((M : ℚ_[(p : ℕ)]) * xp p i) with hbdef
  have hbval : ∀ p ∈ P, ∀ i, ((b p i : ℤ_[(p : ℕ)]) : ℚ_[(p : ℕ)]) = M * xp p i :=
    fun p hp i => coe_toZp (hbint p hp i)
  have hevalZp : ∀ (p : ℕ) [Fact p.Prime] (x : Fin 4 → ℤ_[p]),
      (((f.map (Int.castRingHom ℤ_[p])).eval x : ℤ_[p]) : ℚ_[p]) = f.evalIn ℚ_[p] (fun i => (x i : ℚ_[p])) := by
    intro p _ x
    have := Lattices.hom_eval_castHom f PadicInt.Coe.ringHom x
    rw [show ((f.map (Int.castRingHom ℤ_[p])).eval x : ℚ_[p]) =
      PadicInt.Coe.ringHom ((f.map (Int.castRingHom ℤ_[p])).eval x) from rfl, this]
    simp [QuadForm.evalIn, QuadForm.map, QuadForm.eval]
  have ha : ((D : ℤ) * (M : ℤ) ^ 2) ≠ 0 := by positivity
  have hlocrep : ∀ (p : ℕ) [Fact p.Prime], ∃ x : Fin 4 → ℤ_[p],
      (f.map (Int.castRingHom ℤ_[p])).eval x = ((D : ℤ) * (M : ℤ) ^ 2 : ℤ) := by
    intro p _
    refine ⟨Fin.cons (M : ℤ_[p]) 0, ?_⟩
    apply Subtype.ext
    rw [hevalZp, hfK, gNorm]
    simp only [Fin.cons_zero, Fin.cons_succ, Pi.zero_apply, PadicInt.coe_zero, mul_zero,
      Finset.sum_const_zero, add_zero]
    push_cast
    ring
  have hb : ∀ p ∈ P, (f.map (Int.castRingHom ℤ_[(p : ℕ)])).eval (b p) = ((D : ℤ) * (M : ℤ) ^ 2 : ℤ) := by
    intro p hp
    apply Subtype.ext
    rw [hevalZp, hfK]
    have : (fun i => ((b p i : ℤ_[(p : ℕ)]) : ℚ_[(p : ℕ)])) = (M : ℚ_[(p : ℕ)]) • xp p := by
      funext i; rw [hbval p hp i]; rfl
    rw [this, gNorm_smul, hxp]
    push_cast
    ring
  -- Lemma 7.1 (Ch. 9, Theorem 1.5 with approximation)
  obtain ⟨X, hX, hXc⟩ := Siegel.exists_rep_approx f (le_refl 4) hfdet hfind ha hlocrep P b hb (K + s)
  set y : Fin 4 → ℚ := fun i => (X i : ℚ) / M with hy
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hMpos.ne'
  have hgy : gNorm G y = 1 := by
    have h1 : f.evalIn ℚ (fun i => (X i : ℚ)) = (D : ℚ) * (M : ℚ) ^ 2 := by
      rw [Siegel.evalIn_intCast, hX]
      push_cast
      ring
    rw [hfK] at h1
    have hGid : G.map (algebraMap ℚ ℚ) = G := by ext i j; simp
    rw [hGid] at h1
    have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
    have h2 : gNorm G (fun i => (X i : ℚ)) = (M : ℚ) ^ 2 := mul_left_cancel₀ hD' h1
    have : y = (M : ℚ)⁻¹ • (fun i => (X i : ℚ)) := by
      funext i; simp [hy, div_eq_inv_mul]
    rw [this, gNorm_smul, h2, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hMq)]
  have hu : ternEvenElt Q e y ∈ spinGroup Q := ternEvenElt_mem_spinGroup hQ hn e y hgy
  refine ⟨⟨_, hu⟩, fun p _ => ?_⟩
  set pp : Nat.Primes := ⟨p, Fact.out⟩ with hpp
  have himg : (spinBaseChange ℚ_[p] Q ⟨_, hu⟩ : CliffordAlgebra (Q.baseChange ℚ_[p])) =
      ternEvenElt (Q.baseChange ℚ_[p]) (Algebra.TensorProduct.basis ℚ_[p] eV)
        (fun i => algebraMap ℚ ℚ_[p] (y i)) := by
    rw [coe_spinBaseChange, ofBaseChangeAux_ternEvenElt, hbP]
  by_cases hpP : pp ∈ P
  · -- $p \in P$: the approximation
    refine hKp pp _ _ himg fun i => ?_
    have hdiv := hXc pp hpP i
    have hnorm : ‖((X i : ℤ_[p]) - b pp i : ℤ_[p])‖ ≤ (p : ℝ) ^ (-((K + s : ℕ) : ℤ)) := by
      rw [PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]
      exact hdiv
    have heq : algebraMap ℚ ℚ_[p] (y i) - xp pp i =
        (((X i : ℤ_[p]) - b pp i : ℤ_[p]) : ℚ_[p]) / (M : ℚ_[p]) := by
      have hM' : (M : ℚ_[p]) ≠ 0 := by exact_mod_cast hMpos.ne'
      rw [PadicInt.coe_sub, hbval pp hpP i]
      simp only [hy, map_div₀, map_intCast, map_natCast, PadicInt.coe_intCast]
      field_simp
    rw [heq, norm_div, PadicInt.norm_coe, norm_prod_pow_of_mem P s pp hpP,
      div_le_iff₀ (zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _)]
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
    calc ‖((X i : ℤ_[p]) - b pp i : ℤ_[p])‖ ≤ (p : ℝ) ^ (-((K + s : ℕ) : ℤ)) := hnorm
      _ = (p : ℝ) ^ (-(K : ℤ)) * (p : ℝ) ^ (-(s : ℤ)) := by
          rw [← zpow_add₀ (by positivity)]; push_cast; ring_nf
      _ ≤ (p : ℝ) ^ (-(Kp pp : ℤ)) * (p : ℝ) ^ (-(s : ℤ)) := by
          refine mul_le_mul_of_nonneg_right (zpow_le_zpow_right₀ hp1 ?_) (by positivity)
          have : Kp pp ≤ K := Finset.le_sup (f := Kp) hpP
          omega
  · -- $p \notin P$: integrality
    have hpS : p ∉ hcof.toFinset := fun h => hpP (Finset.mem_subtype.2 (Finset.mem_union_left _ h))
    have hpD : p ∉ Dg.primeFactors := fun h => hpP (Finset.mem_subtype.2 (Finset.mem_union_right _ h))
    have hUp : U p = (intSpin (Q := Q.baseChange ℚ_[p]) (baseChangeLat ℚ_[p] ℤ_[p] Λ) : Set _) := by
      by_contra hne'
      exact hpS (hcof.mem_toFinset.2 ⟨Fact.out, hne'⟩)
    rw [hUp]
    show (spinBaseChange ℚ_[p] Q ⟨_, hu⟩ : CliffordAlgebra (Q.baseChange ℚ_[p])) ∈
      intClifford (Q.baseChange ℚ_[p]) (baseChangeLat ℚ_[p] ℤ_[p] Λ)
    rw [himg]
    -- the Gram entries are $p$-integral
    have hDgp : ‖(Dg : ℚ_[p])‖ = 1 := by
      rw [Padic.norm_natCast_eq_one_iff, Nat.Prime.coprime_iff_not_dvd Fact.out]
      intro hdvd
      exact hpD (Nat.mem_primeFactors.2 ⟨Fact.out, hdvd, hDg.ne'⟩)
    have hGint : ∀ i j, ‖algebraMap ℚ ℚ_[p] (G i j)‖ ≤ 1 := by
      intro i j
      obtain ⟨z, hz⟩ := hDgz (i, j)
      have : algebraMap ℚ ℚ_[p] (G i j) = (z : ℚ_[p]) / (Dg : ℚ_[p]) := by
        have hDg' : (Dg : ℚ) ≠ 0 := by exact_mod_cast hDg.ne'
        have : G i j = (z : ℚ) / Dg := by rw [hz]; field_simp
        rw [this, map_div₀, map_intCast, map_natCast]
      rw [this, norm_div, hDgp, div_one]
      exact Padic.norm_int_le_one z
    set g : Matrix (Fin 3) (Fin 3) ℤ_[p] := fun i j => ⟨_, hGint i j⟩ with hg
    have hf : ∀ i j, ternGram (Q.baseChange ℚ_[p]) (Algebra.TensorProduct.basis ℚ_[p] eV) i j =
        algebraMap ℤ_[p] ℚ_[p] (g i j) := by
      intro i j
      have := congrFun (congrFun (hGp p) i) j
      simp only [ternGramMatrix, Matrix.of_apply, Matrix.map_apply] at this
      rw [this]
      rfl
    -- the coordinates of $u$ are $p$-integral
    have hMp : ‖(M : ℚ_[p])‖ = 1 := norm_prod_pow_of_not_mem P s pp hpP
    have hyint : ∀ i, ‖algebraMap ℚ ℚ_[p] (y i)‖ ≤ 1 := by
      intro i
      simp only [hy, map_div₀, map_intCast, map_natCast, norm_div, hMp, div_one]
      exact Padic.norm_int_le_one _
    set c : Fin 4 → ℤ_[p] := fun i => ⟨_, hyint i⟩ with hc
    have hcoe : (fun i => algebraMap ℚ ℚ_[p] (y i)) = fun i => algebraMap ℤ_[p] ℚ_[p] (c i) := rfl
    have hmem : ternEvenElt (Q.baseChange ℚ_[p]) (Algebra.TensorProduct.basis ℚ_[p] eV)
        (fun i => algebraMap ℚ ℚ_[p] (y i)) ∈
        intCliffordEven (Q.baseChange ℚ_[p]) (ternLat ℤ_[p] (Algebra.TensorProduct.basis ℚ_[p] eV)) := by
      rw [mem_intCliffordEven_ternLat_iff hf, hcoe]
      simp only [ternEvenElt, algebraMap_smul]
      exact add_mem (add_mem (add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨2, rfl⟩)))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨3, rfl⟩))
    have hle : ternLat ℤ_[p] (Algebra.TensorProduct.basis ℚ_[p] eV) ≤ baseChangeLat ℚ_[p] ℤ_[p] Λ := by
      rw [ternLat, Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      rw [hbP]
      exact one_tmul_mem_baseChangeLat (hΛe l)
    exact intClifford_mono hle (intCliffordEven_le _ hmem)

end Main

end QuadFormsKB.Cassels.Thm71Ternary
