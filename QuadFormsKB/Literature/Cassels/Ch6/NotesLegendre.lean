/-
# Cassels, Chapter 6, Notes (pp. 98–99): Gauss' normal form, the lattice $\Gamma$, and the better constant

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Ch. 6, Notes, pp. 98–99. Cassels writes
$g(\vec x) = a_1x_1^2 + a_2x_2^2 + a_3x_3^2$ with $a_1a_2a_3$ squarefree; here the coefficients are
$a_0, a_1, a_2$ (`a : Fin 3 → ℤ`), indices of `Fin 3` are taken modulo $3$, and all variables are $x_0, x_1, x_2$.

**Proves**
* (A) [p. 98] Gauss' normal form of an indefinite classically integral ternary form of determinant $+1$:
  the form $-x_0^2 + 2x_1x_2$ (`gaussForm`) is classically integral, of determinant $+1$, indefinite and properly
  primitive (`isUnimodularCI_gaussForm`, `isIndefinite_gaussForm`, `isProperlyPrimitive_gaussForm`,
  `casselsMat_gaussForm`); every indefinite classically integral ternary form of determinant $+1$ is isotropic over
  $\mathbb Z$ (`isIsotropicZ_of_indefinite_three`, unconditional); and such a form is integrally equivalent to
  `gaussForm`, `gauss_indefinite_det_one`, **conditional on the named statement `Ex11_ii`** (Cassels, Ch. 9, Ex. 11 (ii),
  stated but not proved in the library) and on nothing else.
* (B) [p. 98] The lattice $\Gamma$ of $\vec z \in \mathbb Z^3$ with $z_j \equiv e_jz_{j+1} \pmod{a_{j+2}}$ (`gammaLattice`)
  for integers $e_j$ with $a_{j+2} \mid a_je_j^2 + a_{j+1}$ (the condition $(\pounds)$): on $\Gamma$ the bilinear form
  $\sum_i a_iz_iw_i$ is divisible by $a_0a_1a_2$ (`gamma_bilinear_dvd`, `gamma_quadratic_dvd`), and $\Gamma$ has index
  $\lvert a_0a_1a_2\rvert$ in $\mathbb Z^3$ (`gammaLattice_index`); a basis of $\Gamma$ gives $g = a_0a_1a_2K$ with $K$
  classically integral of determinant $+1$ (`exists_gamma_form`), which with (A) gives a second proof of Legendre's
  theorem in the indefinite case (`legendre_indefinite_of_gamma`).
* (C) [p. 99] The better constant: under the hypotheses of Legendre's Theorem 4.1 (`legendre`) there is a nonzero
  integral zero $\vec b$ with $\lvert a_0\rvert b_0^2 + \lvert a_1\rvert b_1^2 + \lvert a_2\rvert b_2^2 \le
  \frac43(\frac14)^{1/3}\cdot 4\lvert a_0a_1a_2\rvert$, and $\frac43(\frac14)^{1/3} < 1$
  (`legendre_small_zero_hermite`, `numeric_hermite`).

**Proof notes.** (C) follows Cassels: the five congruences of the proof of Theorem 4.1 define a sublattice $\Lambda$ of
$\mathbb Z^3$ of index at most $4\lvert a_0a_1a_2\rvert$ on which $g \equiv 0 \pmod{4\lvert a_0a_1a_2\rvert}$; in a basis
$\vec c_0, \vec c_1, \vec c_2$ of $\Lambda$ the positive definite form $M(\vec x) = \sum_j\lvert a_j\rvert
(\sum_i x_ic_{i,j})^2/(4\lvert a_0a_1a_2\rvert)$ has determinant at most $1/4$; Hermite's bound
(`QuadFormsKB.Reduction.hermiteConstantBound_hermite`, $n = 3$, constant $4/3$) gives a nonzero integral $\vec d$ with
$M(\vec d) \le \frac43(\frac14)^{1/3} < 1$, and $g(\sum d_i\vec c_i)/(4\lvert a_0a_1a_2\rvert)$ is an integer of absolute value
at most $M(\vec d) < 1$, hence $0$. The determinant of the basis matrix is the index (Mathlib's
`Submodule.natAbs_det_basis_change`). (A): the proper primitivity of a unimodular ternary form follows because the
determinant of a symmetric $3 \times 3$ integer matrix with even diagonal is even; the real equivalence of $f$ with
`gaussForm` goes through Ch. 9, Ex. 11 (i) (`ex11_i`: $f \cong y_0^2 - y_1^2 \pm y_2^2$, the sign being $-$ by the determinant)
and the real equivalence of the hyperbolic and odd planes. (B1): reduce modulo each $a_{j+2}$ and combine the three
pairwise coprime moduli; (B2): the map $\vec z \mapsto (z_j - e_jz_{j+1} \bmod a_{j+2})_j$ is surjective by an explicit
Chinese-remainder construction.

**Errata and updates.** *Erratum (candidate):* p. 98 prints Gauss' normal form as "$-x_1^2 + 2x_1x_2$", which is a
binary form of determinant $-1$; the ternary form of determinant $+1$ is $-x_1^2 + 2x_2x_3$ (0-based: `gaussForm`
$= -x_0^2 + 2x_1x_2$). Confirmed by computing the determinant of the Gram matrices (`gaussGram_det`).

**Reuse.** The congruences of the proof of Theorem 4.1 come from `legendre_cong_data` (`Sec4.lean`).
-/
import QuadFormsKB.Literature.Cassels.Ch6.Sec4
import QuadFormsKB.Literature.Cassels.Ch12.Hermite
import QuadFormsKB.Literature.Cassels.Ch9.Ex11

namespace QuadFormsKB.Cassels.Ch6

/-! ### (C) The better constant (p. 99) -/

section Better

open Matrix QuadFormsKB.Reduction

/-- **Numerical fact for the better constant** (Cassels, Ch. 6, Notes, p. 99): $\frac43\left(\frac14\right)^{1/3} < 1$, so
the bound $\frac43\left(\frac14\right)^{1/3}\cdot 4\lvert a_0a_1a_2\rvert$ of `legendre_small_zero_hermite` improves the
bound $4\lvert a_0a_1a_2\rvert$ of Corollary 1 to Theorem 4.1 (`legendre_small_zero`). *Proof:* $\frac14 < (\frac34)^3$. -/
@[kb "cassels1978" "Ch. 6, Notes, p. 99 ((4/3)(1/4)^{1/3} < 1)"]
theorem numeric_hermite : (4 / 3 : ℝ) * (1 / 4 : ℝ) ^ ((1 : ℝ) / 3) < 1 := by
  have h : (1 / 4 : ℝ) ^ ((1 : ℝ) / 3) < 3 / 4 := by
    have h1 : (1 / 4 : ℝ) < (3 / 4) ^ (3 : ℕ) := by norm_num
    have h2 := Real.rpow_lt_rpow (by norm_num) h1 (by norm_num : (0 : ℝ) < 1 / 3)
    have h3 : ((3 / 4 : ℝ) ^ (3 : ℕ)) ^ ((1 : ℝ) / 3) = 3 / 4 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    rwa [h3] at h2
  linarith

/-- Helper: a subgroup $A$ of $\mathbb Z^3$ of finite index has a basis matrix $C$ (columns $\vec c_0, \vec c_1,
\vec c_2$, a $\mathbb Z$-basis of $A$) with $\lvert\det C\rvert$ equal to the index of $A$, and $C\vec x \in A$ for every
$\vec x \in \mathbb Z^3$. Here `A` is the subgroup and `Cint` the basis matrix. -/
theorem exists_basis_matrix (A : AddSubgroup (Fin 3 → ℤ)) [A.FiniteIndex] :
    ∃ Cint : Matrix (Fin 3) (Fin 3) ℤ, (Cint.det).natAbs = A.index ∧ ∀ x : Fin 3 → ℤ, Cint *ᵥ x ∈ A := by
  classical
  set Λ : Submodule ℤ (Fin 3 → ℤ) := A.toIntSubmodule with hΛ
  have hr : Module.finrank ℤ Λ = 3 := by
    have := AddSubgroup.finrank_eq_of_finiteIndex A
    rw [Module.finrank_fin_fun] at this
    exact this
  set bN : Module.Basis (Fin 3) ℤ Λ := Module.finBasisOfFinrankEq ℤ Λ hr with hbN
  have hdet := Submodule.natAbs_det_basis_change (Pi.basisFun ℤ (Fin 3)) Λ bN
  have hcard : Nat.card ((Fin 3 → ℤ) ⧸ Λ) = A.index := rfl
  set Cint : Matrix (Fin 3) (Fin 3) ℤ := Matrix.of fun i j => (bN j : Fin 3 → ℤ) i with hCint
  refine ⟨Cint, ?_, fun x => ?_⟩
  · rw [← hcard, ← hdet, Module.Basis.det_apply]
    congr 2
  · have : Cint *ᵥ x = ((∑ j, x j • bN j : Λ) : Fin 3 → ℤ) := by
      ext i
      simp [hCint, Matrix.mulVec, dotProduct, mul_comm]
    rw [this]
    exact (∑ j, x j • bN j : Λ).2

/-- Helper: **Hermite's bound on a sublattice** (the core of the better constant). Let $A \le \mathbb Z^3$ be a subgroup of
finite index at most $4\lvert a_0a_1a_2\rvert$ (hypothesis `hidx`) on which the form $g = \sum_i a_ix_i^2$ (all
$a_i \ne 0$, `ha`) is divisible by $4\lvert a_0a_1a_2\rvert$ (`hdvd`). Then some $\vec b \in A$, $\vec b \ne \vec 0$, is a zero
of $g$ with $\sum_i\lvert a_i\rvert b_i^2 \le \frac43(\frac14)^{1/3}\cdot 4\lvert a_0a_1a_2\rvert$. -/
theorem lattice_hermite (a : Fin 3 → ℤ) (ha : ∀ i, a i ≠ 0) (A : AddSubgroup (Fin 3 → ℤ)) [A.FiniteIndex]
    (hidx : A.index ≤ 4 * (a 0 * a 1 * a 2).natAbs)
    (hdvd : ∀ u ∈ A, (4 * |a 0 * a 1 * a 2| : ℤ) ∣ ∑ i, a i * u i ^ 2) :
    ∃ b ∈ A, b ≠ 0 ∧ ∑ i, a i * b i ^ 2 = 0 ∧
      ∑ i, |(a i : ℝ)| * (b i : ℝ) ^ 2 ≤ (4 / 3 : ℝ) * (1 / 4 : ℝ) ^ ((1 : ℝ) / 3) *
        (4 * |((a 0 * a 1 * a 2 : ℤ) : ℝ)|) := by
  classical
  obtain ⟨Cint, hdetC, hmem⟩ := exists_basis_matrix A
  have hidx0 : A.index ≠ 0 := AddSubgroup.FiniteIndex.index_ne_zero
  have hD0 : Cint.det ≠ 0 := fun h => hidx0 (by rw [← hdetC, h]; rfl)
  set P : ℝ := |((a 0 * a 1 * a 2 : ℤ) : ℝ)| with hP
  have hP0 : 0 < P := by
    rw [hP]; apply abs_pos.2
    have := ha 0; have := ha 1; have := ha 2
    exact_mod_cast mul_ne_zero (mul_ne_zero (ha 0) (ha 1)) (ha 2)
  have hDle : |((Cint.det : ℤ) : ℝ)| ≤ 4 * P := by
    have h1 : (Cint.det).natAbs ≤ 4 * (a 0 * a 1 * a 2).natAbs := hdetC ▸ hidx
    have h2 : (((Cint.det).natAbs : ℕ) : ℝ) ≤ ((4 * (a 0 * a 1 * a 2).natAbs : ℕ) : ℝ) := by exact_mod_cast h1
    have e1 : |((Cint.det : ℤ) : ℝ)| = (((Cint.det).natAbs : ℕ) : ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs]
    have e2 : P = (((a 0 * a 1 * a 2).natAbs : ℕ) : ℝ) := by rw [hP, Nat.cast_natAbs, Int.cast_abs]
    rw [e1, e2]; exact_mod_cast h1
  set C : Matrix (Fin 3) (Fin 3) ℝ := Cint.map (Int.cast : ℤ → ℝ) with hC
  have hdetCr : C.det = ((Cint.det : ℤ) : ℝ) := by
    rw [hC]; exact (RingHom.map_det (Int.castRingHom ℝ) Cint).symm
  have hdetCr0 : C.det ≠ 0 := by rw [hdetCr]; exact_mod_cast hD0
  set W : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal (fun i => |(a i : ℝ)|) with hW
  set F : Matrix (Fin 3) (Fin 3) ℝ := (4 * P)⁻¹ • (Cᵀ * W * C) with hF
  have hval : ∀ x : Fin 3 → ℝ, val F x = (4 * P)⁻¹ * ∑ i, |(a i : ℝ)| * (C *ᵥ x) i ^ 2 := by
    intro x
    have e : x ⬝ᵥ (Cᵀ * W * C) *ᵥ x = (C *ᵥ x) ⬝ᵥ (W *ᵥ (C *ᵥ x)) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    simp only [val, hF, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    rw [e, hW]
    congr 1
    simp [dotProduct, Matrix.mulVec_diagonal, sq]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hpos : F.PosDef := by
    rw [posDef_iff]
    refine ⟨?_, fun x hx => ?_⟩
    · show Fᵀ = F
      simp [hF, hW, Matrix.transpose_mul, Matrix.mul_assoc, Matrix.transpose_smul]
    · rw [hval]
      have hy : C *ᵥ x ≠ 0 := fun h => hx (Matrix.eq_zero_of_mulVec_eq_zero hdetCr0 h)
      obtain ⟨i, hi⟩ : ∃ i, (C *ᵥ x) i ≠ 0 := by
        by_contra hcon; push Not at hcon; exact hy (funext hcon)
      have hwa : ∀ i, 0 < |(a i : ℝ)| := fun i => abs_pos.2 (by exact_mod_cast ha i)
      refine mul_pos (by positivity) ?_
      refine Finset.sum_pos' (fun j _ => by have := hwa j; positivity) ⟨i, Finset.mem_univ _, ?_⟩
      have := hwa i
      positivity
  have hdetF : F.det = (C.det) ^ 2 / (64 * P ^ 2) := by
    have hprod : ∏ i, |(a i : ℝ)| = P := by
      rw [hP, Fin.prod_univ_three]; push_cast; rw [abs_mul, abs_mul]
    rw [hF, Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hW, Matrix.det_diagonal, hprod]
    simp
    field_simp
    ring
  have hdetle : F.det ≤ 1 / 4 := by
    rw [hdetF, div_le_iff₀ (by positivity)]
    have : C.det ^ 2 ≤ (4 * P) ^ 2 := by
      rw [hdetCr]; exact sq_le_sq' (by linarith [abs_le.1 hDle]) (by linarith [abs_le.1 hDle])
    nlinarith
  obtain ⟨m, hm0, hm⟩ := hermiteConstantBound_hermite (n := 3) (by norm_num) F hpos
  have hgam : ((4 / 3 : ℝ) ^ ((((3 : ℕ) : ℝ) - 1) / 2)) = 4 / 3 := by
    norm_num
  have hroot : F.det ^ ((1 : ℝ) / ((3 : ℕ) : ℝ)) ≤ (1 / 4 : ℝ) ^ ((1 : ℝ) / 3) := by
    push_cast
    exact Real.rpow_le_rpow hpos.det_pos.le hdetle (by norm_num)
  rw [hgam] at hm
  set b : Fin 3 → ℤ := Cint *ᵥ m with hb
  have hbA : b ∈ A := hmem m
  have hb0 : b ≠ 0 := fun h => hm0 (Matrix.eq_zero_of_mulVec_eq_zero hD0 h)
  have hbr : ∀ i, (b i : ℝ) = (C *ᵥ (QuadFormsKB.Reduction.cast m)) i := by
    intro i
    simp [hb, hC, Matrix.mulVec, dotProduct, QuadFormsKB.Reduction.cast]
  have hS : ∑ i, |(a i : ℝ)| * (b i : ℝ) ^ 2 = 4 * P * val F (QuadFormsKB.Reduction.cast m) := by
    rw [hval]
    simp_rw [hbr]
    field_simp
  have hbound : ∑ i, |(a i : ℝ)| * (b i : ℝ) ^ 2 ≤ (4 / 3 : ℝ) * (1 / 4 : ℝ) ^ ((1 : ℝ) / 3) * (4 * P) := by
    rw [hS]
    have h1 := hm.trans (mul_le_mul_of_nonneg_left hroot (by norm_num))
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 4 * P)
    linarith
  refine ⟨b, hbA, hb0, ?_, hbound⟩
  have hlt : ∑ i, |a i| * b i ^ 2 < 4 * |a 0 * a 1 * a 2| := by
    have hk := numeric_hermite
    have h4 : (0 : ℝ) < 4 * P := by positivity
    have : ∑ i, |(a i : ℝ)| * (b i : ℝ) ^ 2 < 4 * P := by
      calc _ ≤ _ := hbound
        _ < 1 * (4 * P) := mul_lt_mul_of_pos_right hk h4
        _ = _ := one_mul _
    rw [hP] at this
    exact_mod_cast this
  refine Int.eq_zero_of_abs_lt_dvd (hdvd b hbA) ?_
  calc |∑ i, a i * b i ^ 2| ≤ ∑ i, |a i * b i ^ 2| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |a i| * b i ^ 2 := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [abs_mul, abs_pow, sq_abs]
    _ < 4 * |a 0 * a 1 * a 2| := hlt


/-- **Cassels, Ch. 6, Notes, p. 99 (the better constant)**: *under the hypotheses of Theorem 4.1 (`legendre`: $a_0a_1a_2$
squarefree and the conditions (i)–(iii) exactly as in `legendre_small_zero`) there is a zero $\vec b \ne \vec 0$ of
$g(\vec x) = a_0x_0^2 + a_1x_1^2 + a_2x_2^2$ with*
$$\lvert a_0\rvert b_0^2 + \lvert a_1\rvert b_1^2 + \lvert a_2\rvert b_2^2 \le \tfrac43\left(\tfrac14\right)^{1/3}\cdot
4\lvert a_0a_1a_2\rvert.$$
Since $\frac43(\frac14)^{1/3} < 1$ (`numeric_hermite`) this improves Corollary 1 (`legendre_small_zero`). The inequality is
stated in $\mathbb R$ (the exponent $1/3$ is real). *Proof:* the lattice $\Lambda$ of the five congruences of the proof of
`legendre` (`legendre_cong_data`, copied above) has index at most $4\lvert a_0a_1a_2\rvert$ and $g \equiv 0$ on it modulo
$4\lvert a_0a_1a_2\rvert$; apply `lattice_hermite` (Hermite's bound, $n = 3$, to a basis of $\Lambda$). Arguments: `a` the
coefficients; `hsq`, `hi`, `hii`, `hiii` the hypotheses of Theorem 4.1 (squarefree, and conditions (i), (ii), (iii)). -/
@[kb "cassels1978" "Ch. 6, Notes, p. 99 (better constant (4/3)(1/4)^{1/3} via Hermite's bound)"]
theorem legendre_small_zero_hermite (a : Fin 3 → ℤ) (hsq : Squarefree (a 0 * a 1 * a 2))
    (hi : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ j : Fin 3, (p : ℤ) ∣ a j →
      ∃ r : ℤ, (p : ℤ) ∣ a (j + 1) * r ^ 2 + a (j + 2))
    (hii : ∀ j : Fin 3, (2 : ℤ) ∣ a j → ∃ s : ℤ, (s = 0 ∨ s = 1) ∧ (8 : ℤ) ∣ a (j + 1) + a (j + 2) + s * a j)
    (hiii : ¬ (2 : ℤ) ∣ a 0 * a 1 * a 2 → ∃ j : Fin 3, (4 : ℤ) ∣ a j + a (j + 1)) :
    ∃ b : Fin 3 → ℤ, b ≠ 0 ∧ ∑ i, a i * b i ^ 2 = 0 ∧
      ∑ i, |(a i : ℝ)| * (b i : ℝ) ^ 2 ≤ (4 / 3 : ℝ) * (1 / 4 : ℝ) ^ ((1 : ℝ) / 3) *
        (4 * |((a 0 * a 1 * a 2 : ℤ) : ℝ)|) := by
  classical
  obtain ⟨m, h, hm, hprod, hdiv⟩ := legendre_cong_data a hsq hi hii hiii
  have ha : ∀ i, a i ≠ 0 := fun i => (sqfree_each a hsq i).ne_zero
  have hne : ∀ l, NeZero (m l) := fun l => ⟨(hm l).ne'⟩
  have hfin : Finite ((l : Fin 5) → ZMod (m l)) := inferInstance
  set A : AddSubgroup (Fin 3 → ℤ) := (congrHom h m).ker with hA
  have hidxeq : A.index = Nat.card (congrHom h m).range := AddSubgroup.index_ker _
  have : A.FiniteIndex := ⟨by
    rw [hidxeq]
    exact Nat.card_pos.ne'⟩
  have hidx : A.index ≤ 4 * (a 0 * a 1 * a 2).natAbs := by
    rw [hidxeq]
    calc Nat.card (congrHom h m).range ≤ Nat.card ((l : Fin 5) → ZMod (m l)) :=
          Nat.card_le_card_of_injective _ Subtype.val_injective
      _ = ∏ l, m l := by rw [Nat.card_pi]; simp
      _ = _ := hprod
  have hdvd : ∀ u ∈ A, (4 * |a 0 * a 1 * a 2| : ℤ) ∣ ∑ i, a i * u i ^ 2 := by
    intro u hu
    have hd := hdiv u ((mem_ker_congrHom h m u).1 hu)
    have hcast : ((4 * (a 0 * a 1 * a 2).natAbs : ℕ) : ℤ) = 4 * |a 0 * a 1 * a 2| := by
      push_cast; rfl
    rwa [hcast] at hd
  obtain ⟨b, -, hb0, hg, hbd⟩ := lattice_hermite a ha A hidx hdvd
  exact ⟨b, hb0, hg, hbd⟩

end Better

/-! ### (A) Gauss' normal form (p. 98) -/

section Gauss

open Matrix QuadFormsKB QuadFormsKB.Siegel QuadFormsKB.Cassels.Ch9Ex11

/-- **The Gram matrix of Gauss' normal form** $-x_0^2 + 2x_1x_2$ (Cassels, Ch. 6, Notes, p. 98): the symmetric matrix
$\begin{pmatrix}-1&0&0\\0&0&1\\0&1&0\end{pmatrix}$ with $\vec x^{\mathsf T}G\vec x = -x_0^2 + 2x_1x_2$. -/
def gaussGram : Matrix (Fin 3) (Fin 3) ℤ := !![-1, 0, 0; 0, 0, 1; 0, 1, 0]

/-- **Gauss' normal form** $-x_0^2 + 2x_1x_2$ (Cassels, Ch. 6, Notes, p. 98, 0-based variables $x_0, x_1, x_2$): the integral ternary
form with Gram matrix `gaussGram`. *Erratum (candidate):* the page prints "$-x_1^2 + 2x_1x_2$", which is a binary form of
determinant $-1$; the ternary form of determinant $+1$ (the one in Gauss' statement) is $-x_1^2 + 2x_2x_3$ in Cassels' 1-based
variables, that is $-x_0^2 + 2x_1x_2$ here (`gaussGram_det`: determinant $+1$). -/
@[kb "cassels1978" "Ch. 6, Notes, p. 98 (Gauss' normal form -x_1^2 + 2x_2x_3; printed with an erratum)"]
def gaussForm : QuadForm ℤ 3 := Siegel.ofGram gaussGram

/-- Helper: the Gram matrix of Gauss' normal form is symmetric. -/
theorem gaussGram_isSymm : gaussGram.IsSymm := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gaussGram]

/-- **(A1), determinant:** the determinant of the symmetric matrix of $-x_0^2 + 2x_1x_2$ is $+1$. -/
@[kb "cassels1978" "Ch. 6, Notes, p. 98 (Gauss' normal form has determinant +1)"]
theorem gaussGram_det : gaussGram.det = 1 := by
  simp [gaussGram, Matrix.det_fin_three]

/-- Helper: the values of Gauss' normal form, $-x_0^2 + 2x_1x_2$ (integral arguments `x`). -/
theorem eval_gaussForm (x : Fin 3 → ℤ) : gaussForm.eval x = -x 0 ^ 2 + 2 * x 1 * x 2 := by
  rw [gaussForm, Siegel.eval_ofGram gaussGram_isSymm]
  simp [gaussGram, dotProduct, Fin.sum_univ_three, Matrix.mulVec]
  ring

/-- **(A1), Cassels' matrix:** the matrix $(f_{ij})$ of `gaussForm` is `gaussGram`. -/
@[kb "cassels1978" "Ch. 6, Notes, p. 98 (Gauss' normal form: its matrix)"]
theorem casselsMat_gaussForm : Siegel.casselsMat gaussForm = gaussGram :=
  Siegel.casselsMat_ofGram gaussGram_isSymm

/-- **(A1), classically integral of determinant $+1$:** `gaussForm` is classically integral of determinant $+1$
(`IsUnimodularCI`: determinant $\pm 1$; here $+1$ by `gaussGram_det`). -/
@[kb "cassels1978" "Ch. 6, Notes, p. 98 (Gauss' normal form is classically integral of determinant 1)"]
theorem isUnimodularCI_gaussForm : IsUnimodularCI gaussForm := by
  refine ⟨Siegel.ci_ofGram gaussGram_isSymm, Or.inl ?_⟩
  rw [casselsMat_gaussForm, gaussGram_det]

/-- Helper: the real values of Gauss' normal form, $-x_0^2 + 2x_1x_2$ (real arguments `x`). -/
theorem evalIn_gaussForm (x : Fin 3 → ℝ) : gaussForm.evalIn ℝ x = -x 0 ^ 2 + 2 * x 1 * x 2 := by
  have hci : IsClassicallyIntegral gaussForm := Siegel.ci_ofGram gaussGram_isSymm
  rw [evalIn_eq_casselsMat ℝ hci, casselsMat_gaussForm]
  simp [gaussGram, dotProduct, Fin.sum_univ_three, Matrix.mulVec]
  ring

/-- **(A1), indefinite:** $-x_0^2 + 2x_1x_2$ takes both signs over $\mathbb R$ (at $(0,1,1)$ and $(1,0,0)$). -/
@[kb "cassels1978" "Ch. 6, Notes, p. 98 (Gauss' normal form is indefinite)"]
theorem isIndefinite_gaussForm : IsIndefinite gaussForm := by
  refine ⟨⟨![0, 1, 1], ?_⟩, ⟨![1, 0, 0], ?_⟩⟩
  · rw [evalIn_gaussForm]; norm_num
  · rw [evalIn_gaussForm]; norm_num

/-- **(A1), properly primitive:** `gaussForm` is primitive and has the odd diagonal coefficient $f_{00} = -1$; this is the
hypothesis needed to apply `Ex11_ii`. -/
@[kb "cassels1978" "Ch. 6, Notes, p. 98 (Gauss' normal form is properly primitive)"]
theorem isProperlyPrimitive_gaussForm : IsProperlyPrimitive (n := 3) gaussForm := by
  refine ⟨isPrimitiveCI_of_unimodular (by norm_num) isUnimodularCI_gaussForm, 0, ?_⟩
  rw [← casselsMat_diag, casselsMat_gaussForm]
  simp [gaussGram]

/-- Helper: a ternary classically integral form `f` of determinant $+1$ (`hf`, `hdet`) is properly primitive: a
symmetric $3 \times 3$ integer matrix with even diagonal has even determinant, so some diagonal coefficient is odd. -/
theorem isProperlyPrimitive_of_unimodular_three (f : QuadForm ℤ 3) (hf : IsUnimodularCI f)
    (hdet : (Siegel.casselsMat f).det = 1) : IsProperlyPrimitive f := by
  refine ⟨isPrimitiveCI_of_unimodular (by norm_num) hf, ?_⟩
  by_contra hcon
  push Not at hcon
  have hA := Siegel.casselsMat_isSymm f
  set A := Siegel.casselsMat f with hAdef
  have hs : ∀ i j, A i j = A j i := fun i j => by
    have := congrFun (congrFun hA i) j
    simpa [Matrix.transpose_apply] using this.symm
  obtain ⟨k0, hk0⟩ := hcon 0
  obtain ⟨k1, hk1⟩ := hcon 1
  obtain ⟨k2, hk2⟩ := hcon 2
  have h0 : A 0 0 = 2 * k0 := by rw [hAdef, casselsMat_diag]; exact hk0
  have h1 : A 1 1 = 2 * k1 := by rw [hAdef, casselsMat_diag]; exact hk1
  have h2 : A 2 2 = 2 * k2 := by rw [hAdef, casselsMat_diag]; exact hk2
  rw [Matrix.det_fin_three, hs 1 0, hs 2 0, hs 2 1, h0, h1, h2] at hdet
  have : (1 : ℤ) = 2 * (k0 * 2 * k1 * k2 * 2 + A 0 1 * A 1 2 * A 0 2 - A 0 2 * k1 * A 0 2 - A 0 1 * A 0 1 * k2 - k0 * A 1 2 * A 1 2) := by
    rw [← hdet]; ring
  omega


/-- **Cassels, Ch. 6, Notes, p. 98 (Gauss)**: *an indefinite classically integral form of determinant $+1$ is integrally
equivalent to $-x_1^2 + 2x_2x_3$* (Cassels' 1-based variables; the page prints $-x_1^2 + 2x_1x_2$, see the erratum in
`gaussForm`), for ternary forms. **Conditional on the named statement `Ex11_ii`** (`h2`; Cassels, Ch. 9, Ex. 11 (ii): indefinite
properly primitive classically integral forms of determinant $\pm 1$ that are equivalent over $\mathbb R$ are equivalent
over $\mathbb Z$), which is stated but not proved in the library, and on nothing else. Arguments: `f` the ternary form,
`hf` that it is classically integral of determinant $\pm 1$, `hdet` that the determinant of its matrix is $+1$, `hind` that it is
indefinite. *Proof:* `f` is properly primitive (a ternary unimodular form is odd); by Ex. 11 (i) (`ex11_i`) it is equivalent to
$y_0^2 - y_1^2 + g$ with $g$ in one variable, $g = -y_2^2$ by the determinant; over $\mathbb R$ this is equivalent to
$2y_0y_1 - y_2^2$ (`isometricIn_real_hyp_odd`), a cyclic permutation of the variables of `gaussForm`; apply `Ex11_ii`. -/
@[kb "cassels1978" "Ch. 6, Notes, p. 98 (Gauss: indefinite ternary of determinant 1 is equivalent to -x_1^2 + 2x_2x_3; conditional on Ex11_ii)"]
theorem gauss_indefinite_det_one (h2 : Ex11_ii) (f : QuadForm ℤ 3) (hf : IsUnimodularCI f)
    (hdet : (Siegel.casselsMat f).det = 1) (hind : IsIndefinite f) : IntEquiv f gaussForm := by
  have hprop := isProperlyPrimitive_of_unimodular_three f hf hdet
  obtain ⟨g, hg, e⟩ := ex11_i (m := 1) f hf hind hprop
  have hoc := isUnimodularCI_orthSum isUnimodularCI_oddPlane hg
  have hdet2 := det_casselsMat_of_intEquiv hf.1 hoc.1 e
  have hsA : (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℤ).IsSymm := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hos : QuadForm.orthSum oddPlane g = Siegel.ofGram (blockMat !![1, 0; 0, -1] (Siegel.casselsMat g)) := by
    have := orthSum_ofGram hsA (Siegel.casselsMat_isSymm g)
    rw [Siegel.ofGram_casselsMat hg.1] at this
    exact this
  have hcm : Siegel.casselsMat (QuadForm.orthSum oddPlane g) = blockMat !![1, 0; 0, -1] (Siegel.casselsMat g) := by
    rw [hos]; exact Siegel.casselsMat_ofGram (blockMat_isSymm hsA (Siegel.casselsMat_isSymm g))
  rw [hcm, det_blockMat, hdet, Matrix.det_fin_one] at hdet2
  have hg00 : Siegel.casselsMat g 0 0 = -1 := by
    simp [Matrix.det_fin_two] at hdet2
    linarith
  have hgmat : Siegel.casselsMat g = !![-1] := by
    ext i j; fin_cases i; fin_cases j; simpa using hg00
  have r1 := isometricIn_real_of_intEquiv hf.1 hoc.1 e
  have r2 := isometricIn_real_symm (isometricIn_real_hyp_odd g)
  have r3 : (QuadForm.orthSum hypPlane g).IsometricIn ℝ gaussForm := by
    refine ⟨!![0, 1, 0; 0, 0, 1; 1, 0, 0], ?_, fun x => ?_⟩
    · simp [Matrix.det_fin_three]
    · rw [QuadForm.evalIn_orthSum, evalIn_hypPlane, evalIn_gaussForm, evalIn_eq_casselsMat ℝ hg.1, hgmat]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      ring
  exact h2 1 f gaussForm hf isUnimodularCI_gaussForm hind isIndefinite_gaussForm hprop
    isProperlyPrimitive_gaussForm (isometricIn_real_trans r1 (isometricIn_real_trans r2 r3))

/-- **Cassels, Ch. 6, Notes, p. 98, unconditional consequence of Gauss' statement:** an indefinite classically integral
ternary form of determinant $\pm 1$ has a nonzero integral zero (`IsIsotropicZ`; this is `isIsotropicZ_of_indefinite` for
$2 + 1$ variables, proved from Hasse–Minkowski and Hilbert reciprocity). Argument `f` the form, `hf` unimodularity, `hind`
indefiniteness. -/
@[kb "cassels1978" "Ch. 6, Notes, p. 98 (indefinite unimodular ternary form is isotropic over Z)"]
theorem isIsotropicZ_of_indefinite_three (f : QuadForm ℤ 3) (hf : IsUnimodularCI f) (hind : IsIndefinite f) :
    IsIsotropicZ f := isIsotropicZ_of_indefinite (m := 1) f hf hind


end Gauss

/-! ### (B) The lattice $\Gamma$ (p. 98) -/

section Gamma

open Matrix QuadFormsKB QuadFormsKB.Siegel QuadFormsKB.Cassels.Ch9Ex11

/-- Helper: the coefficient row $(1 \text{ at } l,\ -e_l \text{ at } l + 1,\ 0 \text{ elsewhere})$ of the linear form
$z_l - e_lz_{l+1}$ (indices of `Fin 3` modulo $3$). Arguments: `e` the integers $e_0, e_1, e_2$, `l` the index. -/
def gammaRow (e : Fin 3 → ℤ) (l : Fin 3) : Fin 3 → ℤ :=
  fun k => if k = l then 1 else if k = l + 1 then -e l else 0

/-- Helper: $\sum_k (\text{gammaRow})_{lk}z_k = z_l - e_lz_{l+1}$. -/
theorem gammaRow_sum (e z : Fin 3 → ℤ) (l : Fin 3) :
    ∑ k, gammaRow e l k * z k = z l - e l * z (l + 1) := by
  fin_cases l <;> simp [gammaRow, Fin.sum_univ_three] <;> ring

/-- **The lattice $\Gamma$ of Cassels, Ch. 6, Notes, p. 98**: the points $\vec z \in \mathbb Z^3$ with
$$z_j \equiv e_jz_{j+1} \pmod{a_{j+2}}\qquad (j = 0, 1, 2,\ \text{indices modulo } 3)$$
(Cassels' $z_1 \equiv e_1z_2 \pmod{a_3}$, $z_2 \equiv e_2z_3 \pmod{a_1}$, $z_3 \equiv e_3z_1 \pmod{a_2}$ with 1-based indices),
as a subgroup of $\mathbb Z^3$: the kernel of the congruence map of Ch. 5, Theorem 2.3 (`congrHom`) for the three
congruences with moduli $\lvert a_{j+2}\rvert$. Arguments: `a` the coefficients $a_0, a_1, a_2$, `e` the integers
$e_0, e_1, e_2$. Membership: `mem_gammaLattice`. -/
noncomputable def gammaLattice (a e : Fin 3 → ℤ) : AddSubgroup (Fin 3 → ℤ) :=
  (congrHom (gammaRow e) (fun l => (a (l + 2)).natAbs)).ker

/-- Membership in $\Gamma$: $\vec z \in \Gamma$ iff $a_{j+2} \mid z_j - e_jz_{j+1}$ for $j = 0, 1, 2$ (indices modulo $3$). -/
theorem mem_gammaLattice (a e z : Fin 3 → ℤ) :
    z ∈ gammaLattice a e ↔ ∀ j : Fin 3, a (j + 2) ∣ z j - e j * z (j + 1) := by
  rw [gammaLattice, mem_ker_congrHom]
  refine forall_congr' fun j => ?_
  rw [gammaRow_sum, Int.natAbs_dvd]

/-- Helper: rotating the sum of a function on `Fin 3` so that it starts at the index `j`. -/
theorem sum_fin3_rot (c : Fin 3 → ℤ) (j : Fin 3) : ∑ i, c i = c j + c (j + 1) + c (j + 2) := by
  fin_cases j <;> simp [Fin.sum_univ_three] <;> ring

/-- Helper: the modulus $a_{j+2}$ divides the bilinear form $\sum_ia_iz_iw_i$ for $\vec z, \vec w$ satisfying the
$j$-th congruence of $\Gamma$ and the $j$-th condition $(\pounds)$ ($a_{j+2} \mid a_je_j^2 + a_{j+1}$). -/
theorem gamma_step (a e z w : Fin 3 → ℤ) (j : Fin 3) (he : a (j + 2) ∣ a j * e j ^ 2 + a (j + 1))
    (hz : a (j + 2) ∣ z j - e j * z (j + 1)) (hw : a (j + 2) ∣ w j - e j * w (j + 1)) :
    a (j + 2) ∣ ∑ i, a i * z i * w i := by
  obtain ⟨s, hs⟩ := hz
  obtain ⟨t, ht⟩ := hw
  obtain ⟨r, hr⟩ := he
  have hzj : z j = e j * z (j + 1) + a (j + 2) * s := by linarith
  have hwj : w j = e j * w (j + 1) + a (j + 2) * t := by linarith
  refine ⟨r * z (j + 1) * w (j + 1) + a j * (e j * z (j + 1) * t + s * e j * w (j + 1) + a (j + 2) * s * t) +
    z (j + 2) * w (j + 2), ?_⟩
  rw [sum_fin3_rot (fun i => a i * z i * w i) j]
  rw [hzj, hwj]
  linear_combination (z (j + 1) * w (j + 1)) * hr

/-- **Cassels, Ch. 6, Notes, p. 98 (B1)**: *for $\vec z, \vec w \in \Gamma$, the bilinear form $\sum_ia_iz_iw_i$ is divisible
by $a_0a_1a_2$.* Hypotheses: `hsq` that $a_0a_1a_2$ is squarefree (so the $a_j$ are pairwise coprime) and `he` the
conditions $(\pounds)$, $a_{j+2} \mid a_je_j^2 + a_{j+1}$ ($j = 0, 1, 2$). *Proof:* reduce modulo each $a_{j+2}$
(`gamma_step`) and combine the three pairwise coprime moduli. -/
@[kb "cassels1978" "Ch. 6, Notes, p. 98 (B1: on Γ the form sum a_i z_i w_i is divisible by a_1a_2a_3)"]
theorem gamma_bilinear_dvd (a e : Fin 3 → ℤ) (hsq : Squarefree (a 0 * a 1 * a 2))
    (he : ∀ j : Fin 3, a (j + 2) ∣ a j * e j ^ 2 + a (j + 1)) {z w : Fin 3 → ℤ}
    (hz : z ∈ gammaLattice a e) (hw : w ∈ gammaLattice a e) :
    a 0 * a 1 * a 2 ∣ ∑ i, a i * z i * w i := by
  have hc := coprime_pairs a hsq
  have h := fun j => gamma_step a e z w j (he j) ((mem_gammaLattice a e z).1 hz j) ((mem_gammaLattice a e w).1 hw j)
  have d2 : a 2 ∣ ∑ i, a i * z i * w i := by simpa using h 0
  have d0 : a 0 ∣ ∑ i, a i * z i * w i := by
    have := h 1; rwa [show (1 : Fin 3) + 2 = 0 from rfl] at this
  have d1 : a 1 ∣ ∑ i, a i * z i * w i := by
    have := h 2; rwa [show (2 : Fin 3) + 2 = 1 from rfl] at this
  have d01 := (hc 0 1 (by decide)).mul_dvd d0 d1
  exact ((hc 0 2 (by decide)).mul_left (hc 1 2 (by decide))).mul_dvd d01 d2

/-- **Cassels, Ch. 6, Notes, p. 98 (B1, quadratic form)**: *for $\vec z \in \Gamma$, $g(\vec z) = \sum_ia_iz_i^2$ is divisible
by $a_0a_1a_2$* (`gamma_bilinear_dvd` with $\vec w = \vec z$); same hypotheses `hsq`, `he`. -/
@[kb "cassels1978" "Ch. 6, Notes, p. 98 (B1: g(z) divisible by a_1a_2a_3 on Γ)"]
theorem gamma_quadratic_dvd (a e : Fin 3 → ℤ) (hsq : Squarefree (a 0 * a 1 * a 2))
    (he : ∀ j : Fin 3, a (j + 2) ∣ a j * e j ^ 2 + a (j + 1)) {z : Fin 3 → ℤ} (hz : z ∈ gammaLattice a e) :
    a 0 * a 1 * a 2 ∣ ∑ i, a i * z i ^ 2 := by
  have := gamma_bilinear_dvd a e hsq he hz hz
  convert this using 2 with i
  ring

/-- Helper: the congruence map of $\Gamma$, $\vec z \mapsto (z_j - e_jz_{j+1} \bmod \lvert a_{j+2}\rvert)_j$, is surjective
when $a_0a_1a_2$ is squarefree (explicit Chinese remainder construction: $z_0 = a_0a_1u_0\tau_0$, $z_1 = a_1a_2u_1\tau_1$,
$z_2 = a_2a_0u_2\tau_2$ with $u_0a_0a_1 \equiv 1 \pmod{a_2}$ etc.). -/
theorem gammaHom_surjective (a e : Fin 3 → ℤ) (hsq : Squarefree (a 0 * a 1 * a 2)) :
    Function.Surjective (congrHom (gammaRow e) (fun l => (a (l + 2)).natAbs)) := by
  intro t
  have hc := coprime_pairs a hsq
  choose τ hτ using fun l => ZMod.intCast_surjective (t l)
  obtain ⟨u0, v0, h0⟩ : IsCoprime (a 0 * a 1) (a 2) := (hc 0 2 (by decide)).mul_left (hc 1 2 (by decide))
  obtain ⟨u1, v1, h1⟩ : IsCoprime (a 1 * a 2) (a 0) :=
    (hc 1 0 (by decide)).mul_left (hc 2 0 (by decide))
  obtain ⟨u2, v2, h2⟩ : IsCoprime (a 2 * a 0) (a 1) :=
    (hc 2 1 (by decide)).mul_left (hc 0 1 (by decide))
  refine ⟨![a 0 * a 1 * u0 * τ 0, a 1 * a 2 * u1 * τ 1, a 2 * a 0 * u2 * τ 2], ?_⟩
  funext l
  show ((∑ k, gammaRow e l k * _ : ℤ) : ZMod (a (l + 2)).natAbs) = t l
  rw [gammaRow_sum, ← hτ l, ZMod.intCast_eq_intCast_iff_dvd_sub, Int.natAbs_dvd]
  fin_cases l
  · refine ⟨τ 0 * v0 + e 0 * a 1 * u1 * τ 1, ?_⟩
    simp
    linear_combination (-τ 0) * h0
  · refine ⟨τ 1 * v1 + e 1 * a 2 * u2 * τ 2, ?_⟩
    simp
    linear_combination (-τ 1) * h1
  · refine ⟨τ 2 * v2 + e 2 * a 0 * u0 * τ 0, ?_⟩
    simp
    linear_combination (-τ 2) * h2

/-- **Cassels, Ch. 6, Notes, p. 98 (B2)**: *$\Gamma$ has index $\lvert a_0a_1a_2\rvert$ in $\mathbb Z^3$* (for squarefree
$a_0a_1a_2$, `hsq`; the integers `e` are arbitrary for this statement). *Proof:* $\Gamma$ is the kernel of the surjective
congruence map onto $\prod_j\mathbb Z/\lvert a_{j+2}\rvert\mathbb Z$ (`gammaHom_surjective`). -/
@[kb "cassels1978" "Ch. 6, Notes, p. 98 (B2: Γ has index |a_1a_2a_3| in Z^3)"]
theorem gammaLattice_index (a e : Fin 3 → ℤ) (hsq : Squarefree (a 0 * a 1 * a 2)) :
    (gammaLattice a e).index = (a 0 * a 1 * a 2).natAbs := by
  rw [gammaLattice, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 (gammaHom_surjective a e hsq),
    AddSubgroup.card_top, Nat.card_pi]
  simp only [Nat.card_zmod, Fin.prod_univ_three, Int.natAbs_mul]
  have e0 : (0 : Fin 3) + 2 = 2 := rfl
  have e1 : (1 : Fin 3) + 2 = 0 := rfl
  have e2 : (2 : Fin 3) + 2 = 1 := rfl
  rw [e0, e1, e2]
  ring

/-- **Cassels, Ch. 6, Notes, p. 98 (B3)**: *on $\Gamma$, $g(x_0\vec b_0 + x_1\vec b_1 + x_2\vec b_2) = a_0a_1a_2K(\vec x)$
with $K$ classically integral of determinant $\pm 1$* ($\vec b_0, \vec b_1, \vec b_2$ a basis of $\Gamma$). Here: given
`hsq` ($a_0a_1a_2$ squarefree) and `he` (the conditions $(\pounds)$) there are an integer matrix $C$ (columns the basis
$\vec b_i$ of $\Gamma$) and a ternary form $K$ such that: $\lvert\det C\rvert = \lvert a_0a_1a_2\rvert$; $C\vec x \in \Gamma$;
$K$ is classically integral of determinant $+1$ (`IsUnimodularCI`, and `(casselsMat K).det = 1`); and
$a_0a_1a_2K(\vec x) = g(C\vec x)$ for integral $\vec x$ and for real $\vec x$ (`C.map` the matrix in $\mathbb R$). The
determinant is $+1$ rather than $\pm 1$: it is $\det(C)^2/(a_0a_1a_2)^2$. -/
@[kb "cassels1978" "Ch. 6, Notes, p. 98 (B3: g = a_1a_2a_3 K on a basis of Γ, K classically integral of determinant 1)"]
theorem exists_gamma_form (a e : Fin 3 → ℤ) (hsq : Squarefree (a 0 * a 1 * a 2))
    (he : ∀ j : Fin 3, a (j + 2) ∣ a j * e j ^ 2 + a (j + 1)) :
    ∃ (C : Matrix (Fin 3) (Fin 3) ℤ) (K : QuadForm ℤ 3), (C.det).natAbs = (a 0 * a 1 * a 2).natAbs ∧
      (∀ x, C *ᵥ x ∈ gammaLattice a e) ∧ IsUnimodularCI K ∧ (Siegel.casselsMat K).det = 1 ∧
      (∀ x : Fin 3 → ℤ, (a 0 * a 1 * a 2) * K.eval x = ∑ i, a i * (C *ᵥ x) i ^ 2) ∧
      (∀ x : Fin 3 → ℝ, ((a 0 * a 1 * a 2 : ℤ) : ℝ) * K.evalIn ℝ x =
        ∑ i, (a i : ℝ) * ((C.map (Int.castRingHom ℝ)) *ᵥ x) i ^ 2) := by
  classical
  set As : ℤ := a 0 * a 1 * a 2 with hAs
  have hne : ∀ i, a i ≠ 0 := fun i => (sqfree_each a hsq i).ne_zero
  have hAs0 : As ≠ 0 := mul_ne_zero (mul_ne_zero (hne 0) (hne 1)) (hne 2)
  have hidx : (gammaLattice a e).index = As.natAbs := gammaLattice_index a e hsq
  have : (gammaLattice a e).FiniteIndex := ⟨by rw [hidx]; exact Int.natAbs_ne_zero.2 hAs0⟩
  obtain ⟨C, hdetC, hmem⟩ := exists_basis_matrix (gammaLattice a e)
  rw [hidx] at hdetC
  have hdetsq : C.det ^ 2 = As ^ 2 := by
    rcases Int.natAbs_eq_natAbs_iff.1 hdetC with h | h
    · rw [h]
    · rw [h]; ring
  -- the entries of the Gram matrix of K
  have hcol : ∀ i j, As ∣ ∑ k, a k * C k i * C k j := by
    intro i j
    have := gamma_bilinear_dvd a e hsq he (hmem (Pi.single i 1)) (hmem (Pi.single j 1))
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
  set G : Matrix (Fin 3) (Fin 3) ℤ := Matrix.of fun i j => (∑ k, a k * C k i * C k j) / As with hG
  have hGe : ∀ i j, As * G i j = ∑ k, a k * C k i * C k j := fun i j => Int.mul_ediv_cancel' (hcol i j)
  have hGs : G.IsSymm := by
    ext i j
    simp only [Matrix.transpose_apply, hG, Matrix.of_apply]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  have hM : As • G = Cᵀ * Matrix.diagonal a * C := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, hGe, Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_congr rfl fun k _ => by
      have hd : ∑ x, C x i * Matrix.diagonal a x k = C k i * a k := by
        rw [Finset.sum_eq_single k]
        · simp
        · intro b _ hb; simp [hb]
        · simp
      rw [hd]; ring
  have hdetG : G.det = 1 := by
    have h1 := congrArg Matrix.det hM
    rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal,
      Fin.prod_univ_three, Fintype.card_fin] at h1
    have h2 : As ^ 3 * G.det = As ^ 3 * 1 := by
      rw [h1, mul_one]
      calc C.det * (a 0 * a 1 * a 2) * C.det = C.det ^ 2 * As := by rw [hAs]; ring
        _ = As ^ 3 := by rw [hdetsq]; ring
    exact mul_left_cancel₀ (pow_ne_zero 3 hAs0) h2
  have hci : IsClassicallyIntegral (Siegel.ofGram G) := Siegel.ci_ofGram hGs
  have hcm : Siegel.casselsMat (Siegel.ofGram G) = G := Siegel.casselsMat_ofGram hGs
  refine ⟨C, Siegel.ofGram G, hdetC, hmem, ⟨hci, Or.inl (by rw [hcm, hdetG])⟩, by rw [hcm, hdetG], ?_, ?_⟩
  · intro x
    rw [Siegel.eval_ofGram hGs]
    have h4 : x ⬝ᵥ (As • G) *ᵥ x = x ⬝ᵥ (Cᵀ * Matrix.diagonal a * C) *ᵥ x := by rw [hM]
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at h4
    rw [h4, ← bil_mulVec_gen]
    simp [dotProduct, Matrix.mulVec_diagonal, sq]
    exact Finset.sum_congr rfl fun i _ => by ring
  · intro x
    rw [evalIn_eq_casselsMat ℝ hci, hcm]
    have hR : ∀ i j, (As : ℝ) * (G i j : ℝ) = ∑ k, (a k : ℝ) * (C k i : ℝ) * (C k j : ℝ) := by
      intro i j
      exact_mod_cast hGe i j
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.map_apply, Int.coe_castRingHom]
    simp only [Fin.sum_univ_three] at hR
    linear_combination (x 0 * x 0) * hR 0 0 + (x 0 * x 1) * hR 0 1 + (x 0 * x 2) * hR 0 2 +
      (x 1 * x 0) * hR 1 0 + (x 1 * x 1) * hR 1 1 + (x 1 * x 2) * hR 1 2 +
      (x 2 * x 0) * hR 2 0 + (x 2 * x 1) * hR 2 1 + (x 2 * x 2) * hR 2 2

/-- **Cassels, Ch. 6, Notes, p. 98 (B3 with A3): a second proof of Legendre's theorem in the indefinite case.** *Let
$a_0a_1a_2$ be squarefree, let the integers $e_j$ satisfy $(\pounds)$ ($a_{j+2} \mid a_je_j^2 + a_{j+1}$), and let $g$ be
indefinite (some $a_i > 0$ and some $a_j < 0$); then $g$ has a zero $\vec b \in \mathbb Z^3$, $\vec b \ne \vec 0$.* Cassels'
route: on a basis of $\Gamma$, $g = a_0a_1a_2K$ with $K$ classically integral of determinant $1$ (`exists_gamma_form`),
$K$ is indefinite because $g$ is, so $K$ is isotropic over $\mathbb Z$ (`isIsotropicZ_of_indefinite_three`, from
Hasse–Minkowski). Unlike `legendre` this uses no congruence conditions modulo $8$ or $4$ and no geometry of numbers, but
requires the existence of the $e_j$ and indefiniteness (in the definite case no zero exists). -/
@[kb "cassels1978" "Ch. 6, Notes, p. 98 (second proof of Legendre's theorem, indefinite case, via Γ)"]
theorem legendre_indefinite_of_gamma (a e : Fin 3 → ℤ) (hsq : Squarefree (a 0 * a 1 * a 2))
    (he : ∀ j : Fin 3, a (j + 2) ∣ a j * e j ^ 2 + a (j + 1)) (hpos : ∃ i, 0 < a i) (hneg : ∃ j, a j < 0) :
    ∃ b : Fin 3 → ℤ, b ≠ 0 ∧ ∑ i, a i * b i ^ 2 = 0 := by
  classical
  obtain ⟨C, K, hdetC, -, hK, -, hint, hreal⟩ := exists_gamma_form a e hsq he
  have hne : ∀ i, a i ≠ 0 := fun i => (sqfree_each a hsq i).ne_zero
  have hAs0 : a 0 * a 1 * a 2 ≠ 0 := mul_ne_zero (mul_ne_zero (hne 0) (hne 1)) (hne 2)
  have hD0 : C.det ≠ 0 := fun h => hAs0 (Int.natAbs_eq_zero.1 (by rw [← hdetC, h]; rfl))
  have hCr : (C.map (Int.castRingHom ℝ)).det ≠ 0 := by
    have : (C.map (Int.castRingHom ℝ)).det = ((C.det : ℤ) : ℝ) :=
      (RingHom.map_det (Int.castRingHom ℝ) C).symm
    rw [this]; exact_mod_cast hD0
  -- real points where g takes the value a_i
  have hpt : ∀ i, ∃ x : Fin 3 → ℝ, ((a 0 * a 1 * a 2 : ℤ) : ℝ) * K.evalIn ℝ x = (a i : ℝ) := by
    intro i
    refine ⟨(C.map (Int.castRingHom ℝ))⁻¹ *ᵥ Pi.single i 1, ?_⟩
    rw [hreal, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hCr), Matrix.one_mulVec]
    simp [Pi.single_apply]
  have hKind : IsIndefinite K := by
    obtain ⟨i, hi⟩ := hpos
    obtain ⟨j, hj⟩ := hneg
    obtain ⟨x, hx⟩ := hpt i
    obtain ⟨y, hy⟩ := hpt j
    have hi' : (0 : ℝ) < a i := by exact_mod_cast hi
    have hj' : (a j : ℝ) < 0 := by exact_mod_cast hj
    rcases lt_or_gt_of_ne (show ((a 0 * a 1 * a 2 : ℤ) : ℝ) ≠ 0 by exact_mod_cast hAs0) with hs | hs
    · refine ⟨⟨y, ?_⟩, ⟨x, ?_⟩⟩
      · by_contra hcon
        push Not at hcon
        nlinarith [mul_nonneg_of_nonpos_of_nonpos hs.le hcon]
      · by_contra hcon
        push Not at hcon
        nlinarith [mul_nonpos_of_nonpos_of_nonneg hs.le hcon]
    · refine ⟨⟨x, ?_⟩, ⟨y, ?_⟩⟩
      · by_contra hcon
        push Not at hcon
        nlinarith [mul_nonpos_of_nonneg_of_nonpos hs.le hcon]
      · by_contra hcon
        push Not at hcon
        nlinarith [mul_nonneg hs.le hcon]
  obtain ⟨x, hx0, hx⟩ := isIsotropicZ_of_indefinite_three K hK hKind
  refine ⟨C *ᵥ x, fun h => hx0 (Matrix.eq_zero_of_mulVec_eq_zero hD0 h), ?_⟩
  have := hint x
  rw [hx, mul_zero] at this
  exact this.symm

end Gamma

end QuadFormsKB.Cassels.Ch6
