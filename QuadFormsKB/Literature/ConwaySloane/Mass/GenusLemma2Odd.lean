/-
# Conway–Sloane 1988, §11, Lemma 2 ("if") at the odd primes; the case $p = 2$ as a named statement

J. H. Conway and N. J. A. Sloane, *Low-dimensional lattices IV: the mass formula*, Proc. R. Soc. Lond. A **419** (1988),
259–286 (`conwaysloane1988`), §11, Lemma 2, p. 280. The "only if" half is proved in `GenusLemma2Easy.lean`; the "if"
half was the named statement `Lemma2IfStatement`. This file proves it at the real place and at every odd prime, and
shrinks the assumed part to the case $p = 2$ (`Lemma2IfDyadicStatement`).

**Statement proved.** Let $A, B \in M_n(\mathbb Z)$ be symmetric with $\det A = \det B \ne 0$, and let `DiscIso T A B`
(an additive isomorphism $\varphi : \mathbb Z^n/A\mathbb Z^n \to \mathbb Z^n/B\mathbb Z^n$ with
$z^{\mathsf T}B^{-1}z - y^{\mathsf T}A^{-1}y \in T\mathbb Z$ whenever $\varphi[y] = [z]$; any $T \in \mathbb N$). Then for every
odd prime $p$ the forms $x^{\mathsf T}Ax$, $x^{\mathsf T}Bx$ are $\mathrm{GL}_n(\mathbb Z_p)$-equivalent. For positive
definite $A$, $B$, $\det A = \det B$ follows from `DiscIso` ($\det A = |\mathbb Z^n/A\mathbb Z^n|$).

**Proof (the paper's route: the discriminant form determines the Jordan invariants, $p$ odd).**
1. *Matrix form of $\varphi$* (`exists_lift`, `qp_data`): $\varphi[y] = [\Phi y]$ for an integer matrix $\Phi$ with
   $\Phi A = BW$, and $X = \Phi^{\mathsf T}B^{-1}\Phi - A^{-1}$ has $y^{\mathsf T}Xy \in \mathbb Z$ for $y \in \mathbb Z^n$, so
   $2X$ is integral, hence $X$ is $p$-integral ($p$ odd).
2. *Diagonalize* (Conway–Sloane Ch. 15, Thm. 2 via `exists_isOddSymbolOf`): $A \sim D = \operatorname{diag}(p^{z_i}u_i)$,
   $B \sim D' = \operatorname{diag}(p^{z'_j}u'_j)$ over $\mathbb Z_p$, $u_i$, $u'_j$ units. Transporting (`transport`):
   integral $\Psi$, $W'$, $Y$ with $\Psi D = D'W'$ and $\Psi^{\mathsf T}D'^{-1}\Psi - D^{-1} = Y$.
3. *Scale $p^k$, $k \ge 1$* (`scale_congr`): multiply the entries $(i, i')$ with $z_i = z_{i'} = k$ by $p^k$ and reduce mod
   $p$. Terms with $z'_j < k$ keep a factor $p$; terms with $z'_j > k$ too, since $p^{z'_j - k} \mid \Psi_{ji}$ by
   $\Psi D = D'W'$. So $\bar P^{\mathsf T}\operatorname{diag}(\bar u'^{-1}_j)\bar P = \operatorname{diag}(\bar u_i^{-1})$ over
   $\mathbb F_p$ for the block $P = (\Psi_{ji})_{z'_j = k,\ z_i = k}$. By rank, $n_{p^k}(A) \le n_{p^k}(B)$, and the
   inverse isomorphism gives $\ge$ (`card_le_of_congr`); then $\det$ gives $\prod u_i \equiv \det(\bar P)^2\prod u'_j$,
   so by Hensel's lemma the signs $\varepsilon_{p^k}$ agree (`scale_eq`).
4. *Scale $1$* (`symbol_eq`): $n_1 = n - \sum_{k \ge 1}n_{p^k}$, and $\prod_i u_i$, $\prod_j u'_j$ differ by a square since
   $\det A = \det B$ (`det_rel`), which fixes $\varepsilon_1$.
5. Equal $p$-adic symbols give $A \sim B$ over $\mathbb Z_p$ (`zpEquiv_of_oddSymbol_eq`, Theorem 9), and
   `isometricGL_padic_iff` converts to the genus condition.

**Proves**
* `Lemma2Odd.zpEquiv_of_discIso`, `Lemma2Odd.isometricGL_padic_of_discIso`: the statement above (symmetric, any $T$).
* `lemma2_if_odd`: Lemma 2 "if" at the odd primes for positive definite lattices; `isometricGL_real_of_posDefGram`:
  the real place.
* `Lemma2IfDyadicStatement` (**named statement**: the "if" half at $p = 2$), `lemma2If_of_dyadic` (it implies
  `Lemma2IfStatement`), `dyadic_of_lemma2If` (the converse), `lemma2Statement_of_dyadic`, `lemma4_of_dyadic`.

**Inputs:** none for the odd primes (standard axioms only). Indices are 0-based.
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.ConwaySloane.Mass.GenusLemma2Easy

set_option linter.unusedSectionVars false

open Matrix QuadFormsKB QuadFormsKB.Siegel QuadFormsKB.LocalDensity QuadFormsKB.Cassels

namespace QuadFormsKB.ConwaySloane.Mass

namespace Lemma2Odd

variable {n : ℕ}

/-! ### Linear algebra over a field -/

section Field

variable {K : Type*} [Field K] {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']

/-- If $P^{\mathsf T}\operatorname{diag}(d')P = \operatorname{diag}(d)$ over a field, with $P$ of size $\iota' \times \iota$
and all $d_i \ne 0$, then $|\iota| \le |\iota'|$ (rank). -/
theorem card_le_of_congr (P : Matrix ι' ι K) (d' : ι' → K) (d : ι → K) (hd : ∀ i, d i ≠ 0)
    (h : Pᵀ * diagonal d' * P = diagonal d) : Fintype.card ι ≤ Fintype.card ι' := by
  have hu : IsUnit (diagonal d) := by
    rw [Matrix.isUnit_iff_isUnit_det, det_diagonal]
    exact (Finset.prod_ne_zero_iff.2 fun i _ => hd i).isUnit
  rw [← rank_of_isUnit _ hu, ← h]
  exact (rank_mul_le_right _ _).trans (rank_le_card_height P)

/-- If $P^{\mathsf T}\operatorname{diag}(d')P = \operatorname{diag}(d)$ and $e : \iota \simeq \iota'$, then
$\prod_i d_i = \det(\tilde P)^2\prod_j d'_j$ with the square matrix $\tilde P = (P_{e(i), i'})$. -/
theorem prod_eq_of_congr (P : Matrix ι' ι K) (d' : ι' → K) (d : ι → K) (e : ι ≃ ι')
    (h : Pᵀ * diagonal d' * P = diagonal d) :
    ∏ i, d i = (P.submatrix e id).det ^ 2 * ∏ j, d' j := by
  have h1 : (P.submatrix e id)ᵀ * diagonal (d' ∘ e) * P.submatrix e id = diagonal d := by
    rw [transpose_submatrix, ← submatrix_diagonal_equiv, submatrix_mul_equiv, submatrix_mul_equiv, h,
      submatrix_id_id]
  have h2 := congrArg det h1
  rw [det_mul, det_mul, det_transpose, det_diagonal, det_diagonal] at h2
  rw [← h2]
  simp only [Function.comp_apply, Equiv.prod_comp e d']
  ring

end Field

/-! ### Reduction modulo $p$ of integral elements of $\mathbb Q_p$ -/

section Red

variable {p : ℕ} [Fact p.Prime]

/-- The element of $\mathbb Z_p$ defined by $x \in \mathbb Q_p$ if $\lVert x\rVert \le 1$ (and $0$ otherwise). -/
noncomputable def toZp (x : ℚ_[p]) : ℤ_[p] := if h : ‖x‖ ≤ 1 then ⟨x, h⟩ else 0

/-- Reduction modulo $p$ of an integral $x \in \mathbb Q_p$ (and $0$ for non-integral $x$). -/
noncomputable def red (x : ℚ_[p]) : ZMod p := PadicInt.toZMod (toZp x)

theorem coe_toZp {x : ℚ_[p]} (h : ‖x‖ ≤ 1) : ((toZp x : ℤ_[p]) : ℚ_[p]) = x := by
  simp [toZp, h]

theorem toZp_coe (z : ℤ_[p]) : toZp (z : ℚ_[p]) = z :=
  Subtype.ext (coe_toZp (x := (z : ℚ_[p])) z.2)

theorem norm_coe_le (z : ℤ_[p]) : ‖(z : ℚ_[p])‖ ≤ 1 := z.2

theorem red_coe (z : ℤ_[p]) : red (z : ℚ_[p]) = PadicInt.toZMod z := by
  rw [red, toZp_coe]

theorem toZp_mul {x y : ℚ_[p]} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : toZp (x * y) = toZp x * toZp y := by
  conv_lhs => rw [← coe_toZp hx, ← coe_toZp hy]
  rw [← PadicInt.coe_mul, toZp_coe]

theorem toZp_add {x y : ℚ_[p]} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : toZp (x + y) = toZp x + toZp y := by
  conv_lhs => rw [← coe_toZp hx, ← coe_toZp hy]
  rw [← PadicInt.coe_add, toZp_coe]

theorem sum_eq_coe {ι : Type*} (s : Finset ι) {f : ι → ℚ_[p]} (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) :
    ∑ i ∈ s, f i = ((∑ i ∈ s, toZp (f i) : ℤ_[p]) : ℚ_[p]) := by
  rw [PadicInt.coe_sum]; exact Finset.sum_congr rfl fun i hi => (coe_toZp (hf i hi)).symm

theorem prod_eq_coe {ι : Type*} (s : Finset ι) {f : ι → ℚ_[p]} (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) :
    ∏ i ∈ s, f i = ((∏ i ∈ s, toZp (f i) : ℤ_[p]) : ℚ_[p]) := by
  have e := map_prod PadicInt.Coe.ringHom (fun i => toZp (f i)) s
  change ((∏ i ∈ s, toZp (f i) : ℤ_[p]) : ℚ_[p]) = ∏ i ∈ s, ((toZp (f i) : ℤ_[p]) : ℚ_[p]) at e
  rw [e]; exact Finset.prod_congr rfl fun i hi => (coe_toZp (hf i hi)).symm

theorem red_sum {ι : Type*} (s : Finset ι) {f : ι → ℚ_[p]} (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) :
    red (∑ i ∈ s, f i) = ∑ i ∈ s, red (f i) := by
  rw [sum_eq_coe s hf, red_coe, map_sum]; rfl

theorem red_prod {ι : Type*} (s : Finset ι) {f : ι → ℚ_[p]} (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) :
    red (∏ i ∈ s, f i) = ∏ i ∈ s, red (f i) := by
  rw [prod_eq_coe s hf, red_coe, map_prod]; rfl

theorem red_mul {x y : ℚ_[p]} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : red (x * y) = red x * red y := by
  rw [red, toZp_mul hx hy, map_mul]; rfl

theorem red_eq_zero {x : ℚ_[p]} (h : ‖x‖ < 1) : red x = 0 := by
  have h1 : ‖toZp x‖ < 1 := by
    rw [PadicInt.norm_def, coe_toZp h.le]; exact h
  obtain ⟨c, hc⟩ := (PadicInt.norm_lt_one_iff_dvd _).1 h1
  rw [red, hc, map_mul, map_natCast, ZMod.natCast_self, zero_mul]

theorem red_add_of_lt {x y : ℚ_[p]} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ < 1) : red (x + y) = red x := by
  rw [red, toZp_add hx hy.le, map_add]
  have := red_eq_zero hy
  rw [red] at this
  rw [this, add_zero]; rfl

theorem red_ne_zero {x : ℚ_[p]} (h : ‖x‖ = 1) : red x ≠ 0 := by
  have hu : IsUnit (toZp x) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_def, coe_toZp h.le]; exact h
  exact (hu.map PadicInt.toZMod).ne_zero

theorem norm_p_mul_lt {x : ℚ_[p]} (hx : ‖x‖ ≤ 1) : ‖(p : ℚ_[p]) * x‖ < 1 := by
  rw [norm_mul]
  have := Padic.norm_p_lt_one (p := p)
  nlinarith [norm_nonneg x, norm_nonneg (p : ℚ_[p])]

theorem norm_p_pow_le (k : ℕ) : ‖(p : ℚ_[p]) ^ k‖ ≤ 1 := by
  rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) Padic.norm_p_lt_one.le

theorem norm_mul_le_one {x y : ℚ_[p]} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x * y‖ ≤ 1 := by
  rw [norm_mul]; nlinarith [norm_nonneg x, norm_nonneg y]

end Red

/-! ### Integral matrices over $\mathbb Q_p$ -/

section Int

variable {p : ℕ} [Fact p.Prime]

/-- A matrix over $\mathbb Q_p$ is *integral* if all its entries lie in $\mathbb Z_p$ ($\lVert M_{ij}\rVert \le 1$). -/
def IsInt (M : Matrix (Fin n) (Fin n) ℚ_[p]) : Prop := ∀ i j, ‖M i j‖ ≤ 1

theorem IsInt.eq_map {M : Matrix (Fin n) (Fin n) ℚ_[p]} (hM : IsInt M) :
    M = (M.map toZp).map PadicInt.Coe.ringHom := by
  ext i j; exact (coe_toZp (hM i j)).symm

theorem isInt_map (M : Matrix (Fin n) (Fin n) ℤ_[p]) : IsInt (M.map PadicInt.Coe.ringHom) :=
  fun i j => norm_coe_le (M i j)

theorem IsInt.mul {M N : Matrix (Fin n) (Fin n) ℚ_[p]} (hM : IsInt M) (hN : IsInt N) : IsInt (M * N) := by
  rw [hM.eq_map, hN.eq_map, ← Matrix.map_mul]; exact isInt_map _

theorem IsInt.transpose {M : Matrix (Fin n) (Fin n) ℚ_[p]} (hM : IsInt M) : IsInt Mᵀ :=
  fun i j => hM j i

theorem IsInt.sub {M N : Matrix (Fin n) (Fin n) ℚ_[p]} (hM : IsInt M) (hN : IsInt N) : IsInt (M - N) := by
  rw [hM.eq_map, hN.eq_map, ← Matrix.map_sub _ (map_sub PadicInt.Coe.ringHom)]; exact isInt_map _

theorem isInt_intCast (M : Matrix (Fin n) (Fin n) ℤ) : IsInt (M.map (Int.castRingHom ℚ_[p])) :=
  fun i j => by simp only [Matrix.map_apply, eq_intCast]; exact Padic.norm_int_le_one _

end Int

/-! ### The scale-$p^k$ congruence -/

section Scale

variable {p : ℕ} [Fact p.Prime]

theorem ne_zero_of_norm_one {x : ℚ_[p]} (h : ‖x‖ = 1) : x ≠ 0 := by
  rintro rfl; simp at h

theorem p_ne_zero : (p : ℚ_[p]) ≠ 0 := by
  exact_mod_cast (Fact.out : p.Prime).ne_zero

/-- An entry of $\Psi D = D'W$ for diagonal $D = \operatorname{diag}(p^{z_i}u_i)$, $D' = \operatorname{diag}(p^{z'_j}u'_j)$. -/
theorem entry_eq {z z' : Fin n → ℕ} {u u' : Fin n → ℚ_[p]} {Ψ W : Matrix (Fin n) (Fin n) ℚ_[p]}
    (hΨD : Ψ * diagonal (fun i => (p : ℚ_[p]) ^ z i * u i) = diagonal (fun j => (p : ℚ_[p]) ^ z' j * u' j) * W)
    (j i : Fin n) : Ψ j i * ((p : ℚ_[p]) ^ z i * u i) = (p : ℚ_[p]) ^ z' j * u' j * W j i := by
  have := congrFun (congrFun hΨD j) i
  simpa [mul_diagonal, diagonal_mul] using this

/-- **The term of scale $p^k$**: for $z_i = z_{i'} = k$ and $z'_j = k$,
$p^k\,\Psi_{ji}(p^{z'_j}u'_j)^{-1}\Psi_{ji'} = \Psi_{ji}{u'_j}^{-1}\Psi_{ji'}$. -/
theorem term_eq {z' : Fin n → ℕ} {u' : Fin n → ℚ_[p]} (hu' : ∀ j, ‖u' j‖ = 1) (Ψ : Matrix (Fin n) (Fin n) ℚ_[p])
    {k : ℕ} {i i' j : Fin n} (hj : z' j = k) :
    (p : ℚ_[p]) ^ k * (Ψ j i * ((p : ℚ_[p]) ^ z' j * u' j)⁻¹ * Ψ j i') = Ψ j i * (u' j)⁻¹ * Ψ j i' := by
  have hp0 := p_ne_zero (p := p)
  have hu0 := ne_zero_of_norm_one (hu' j)
  rw [hj]; field_simp

/-- **The other terms are divisible by $p$**: for $z_i = z_{i'} = k$ and $z'_j \ne k$,
$\lVert p^k\,\Psi_{ji}(p^{z'_j}u'_j)^{-1}\Psi_{ji'}\rVert < 1$ (if $z'_j < k$ the factor $p^{k - z'_j}$ remains; if
$z'_j > k$ then $p^{z'_j - k}$ divides $\Psi_{ji}$ and $\Psi_{ji'}$ by $\Psi D = D'W$). -/
theorem term_lt {z z' : Fin n → ℕ} {u u' : Fin n → ℚ_[p]} (hu : ∀ i, ‖u i‖ = 1) (hu' : ∀ j, ‖u' j‖ = 1)
    {Ψ W : Matrix (Fin n) (Fin n) ℚ_[p]} (hΨ : IsInt Ψ) (hW : IsInt W)
    (hΨD : Ψ * diagonal (fun i => (p : ℚ_[p]) ^ z i * u i) = diagonal (fun j => (p : ℚ_[p]) ^ z' j * u' j) * W)
    {k : ℕ} {i i' j : Fin n} (hi : z i = k) (hi' : z i' = k) (hj : z' j ≠ k) :
    ‖(p : ℚ_[p]) ^ k * (Ψ j i * ((p : ℚ_[p]) ^ z' j * u' j)⁻¹ * Ψ j i')‖ < 1 := by
  have hp0 := p_ne_zero (p := p)
  have hu0 := ne_zero_of_norm_one (hu' j)
  have hinv : ‖(u' j)⁻¹‖ = 1 := by rw [norm_inv, hu' j, inv_one]
  rcases lt_or_gt_of_ne hj with hlt | hgt
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hlt
    have e : (p : ℚ_[p]) ^ k * (Ψ j i * ((p : ℚ_[p]) ^ z' j * u' j)⁻¹ * Ψ j i')
        = (p : ℚ_[p]) * ((p : ℚ_[p]) ^ d * Ψ j i * (u' j)⁻¹ * Ψ j i') := by
      rw [hd, pow_add, pow_add, pow_one]; field_simp
    rw [e]
    refine norm_p_mul_lt (norm_mul_le_one (norm_mul_le_one (norm_mul_le_one (norm_p_pow_le d) (hΨ j i))
      hinv.le) (hΨ j i'))
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hgt
    have hui := ne_zero_of_norm_one (hu i)
    have hui' := ne_zero_of_norm_one (hu i')
    have e1 := entry_eq hΨD j i
    have e2 := entry_eq hΨD j i'
    rw [hi] at e1
    rw [hi'] at e2
    rw [hd] at e1 e2
    have f1 : Ψ j i = (p : ℚ_[p]) ^ (d + 1) * (u' j * W j i * (u i)⁻¹) := by
      have : Ψ j i = (p : ℚ_[p]) ^ (k + d + 1) * u' j * W j i / ((p : ℚ_[p]) ^ k * u i) := by
        rw [eq_div_iff (mul_ne_zero (pow_ne_zero _ hp0) hui)]; exact e1
      rw [this, show k + d + 1 = k + (d + 1) by ring, pow_add]; field_simp
    have f2 : Ψ j i' = (p : ℚ_[p]) ^ (d + 1) * (u' j * W j i' * (u i')⁻¹) := by
      have : Ψ j i' = (p : ℚ_[p]) ^ (k + d + 1) * u' j * W j i' / ((p : ℚ_[p]) ^ k * u i') := by
        rw [eq_div_iff (mul_ne_zero (pow_ne_zero _ hp0) hui')]; exact e2
      rw [this, show k + d + 1 = k + (d + 1) by ring, pow_add]; field_simp
    have e : (p : ℚ_[p]) ^ k * (Ψ j i * ((p : ℚ_[p]) ^ z' j * u' j)⁻¹ * Ψ j i')
        = (p : ℚ_[p]) * ((p : ℚ_[p]) ^ d * (W j i * (u i)⁻¹) * (u' j * W j i' * (u i')⁻¹)) := by
      rw [f1, f2, hd]; field_simp; ring
    rw [e]
    have hi1 : ‖(u i)⁻¹‖ = 1 := by rw [norm_inv, hu i, inv_one]
    have hi1' : ‖(u i')⁻¹‖ = 1 := by rw [norm_inv, hu i', inv_one]
    refine norm_p_mul_lt (norm_mul_le_one (norm_mul_le_one (norm_p_pow_le d)
      (norm_mul_le_one (hW j i) hi1.le)) (norm_mul_le_one (norm_mul_le_one (hu' j).le (hW j i')) hi1'.le))

/-- **The scale-$p^k$ congruence** ($k \ge 1$). Let $D = \operatorname{diag}(p^{z_i}u_i)$ and
$D' = \operatorname{diag}(p^{z'_j}u'_j)$ with $p$-adic units $u_i$, $u'_j$, and let $\Psi$, $W$, $Y$ be integral with
$\Psi D = D'W$ and $\Psi^{\mathsf T}D'^{-1}\Psi - D^{-1} = Y$ (the matrix form of a homomorphism of discriminant forms).
Then modulo $p$, with $\iota = \{i : z_i = k\}$, $\iota' = \{j : z'_j = k\}$ and $P = (\Psi_{ji})_{j \in \iota', i \in \iota}$:
$\bar P^{\mathsf T}\operatorname{diag}(\bar u'^{-1}_j)\bar P = \operatorname{diag}(\bar u_i^{-1})$. -/
theorem scale_congr {z z' : Fin n → ℕ} {u u' : Fin n → ℚ_[p]} (hu : ∀ i, ‖u i‖ = 1) (hu' : ∀ j, ‖u' j‖ = 1)
    {Ψ W Y : Matrix (Fin n) (Fin n) ℚ_[p]} (hΨ : IsInt Ψ) (hW : IsInt W) (hY : IsInt Y)
    (hΨD : Ψ * diagonal (fun i => (p : ℚ_[p]) ^ z i * u i) = diagonal (fun j => (p : ℚ_[p]) ^ z' j * u' j) * W)
    (hX : Ψᵀ * diagonal (fun j => ((p : ℚ_[p]) ^ z' j * u' j)⁻¹) * Ψ
      - diagonal (fun i => ((p : ℚ_[p]) ^ z i * u i)⁻¹) = Y)
    {k : ℕ} (hk : 1 ≤ k) :
    (Matrix.of fun (j : {j // z' j = k}) (i : {i // z i = k}) => red (Ψ j i))ᵀ
        * diagonal (fun j : {j // z' j = k} => red (u' j)⁻¹)
        * (Matrix.of fun (j : {j // z' j = k}) (i : {i // z i = k}) => red (Ψ j i))
      = diagonal (fun i : {i // z i = k} => red (u i)⁻¹) := by
  classical
  ext ⟨i, hi⟩ ⟨i', hi'⟩
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.of_apply, Matrix.diagonal_apply,
    Subtype.mk.injEq]
  have hp0 := p_ne_zero (p := p)
  set t : Fin n → ℚ_[p] := fun j => (p : ℚ_[p]) ^ k * (Ψ j i * ((p : ℚ_[p]) ^ z' j * u' j)⁻¹ * Ψ j i') with ht
  set R : ℚ_[p] := if i = i' then (u i)⁻¹ else 0 with hR
  have hYe := congrFun (congrFun hX i) i'
  rw [Matrix.sub_apply, Matrix.mul_apply] at hYe
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.diagonal_apply] at hYe
  have hsum : ∑ j, t j = R + (p : ℚ_[p]) ^ k * Y i i' := by
    have e1 : ∑ j, t j = (p : ℚ_[p]) ^ k * ∑ j, Ψ j i * ((p : ℚ_[p]) ^ z' j * u' j)⁻¹ * Ψ j i' := by
      rw [Finset.mul_sum]
    have e2 : (p : ℚ_[p]) ^ k * (if i = i' then ((p : ℚ_[p]) ^ z i * u i)⁻¹ else 0) = R := by
      rw [hR]; split_ifs
      · rw [hi]; have := ne_zero_of_norm_one (hu i); field_simp
      · rw [mul_zero]
    rw [e1, ← e2, ← mul_add, ← hYe]; ring
  have hRint : ‖R‖ ≤ 1 := by
    rw [hR]; split_ifs
    · rw [norm_inv, hu i, inv_one]
    · simp
  have hsmall : ‖(p : ℚ_[p]) ^ k * Y i i'‖ < 1 := by
    obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le' hk
    rw [pow_succ, mul_comm _ (p : ℚ_[p]), mul_assoc]
    exact norm_p_mul_lt (norm_mul_le_one (norm_p_pow_le _) (hY i i'))
  have htint : ∀ j, ‖t j‖ ≤ 1 := by
    intro j
    by_cases hj : z' j = k
    · rw [ht]; dsimp only; rw [term_eq hu' Ψ hj]
      exact norm_mul_le_one (norm_mul_le_one (hΨ j i) (by rw [norm_inv, hu' j, inv_one])) (hΨ j i')
    · exact (term_lt hu hu' hΨ hW hΨD hi hi' hj).le
  have hred : red (∑ j, t j) = red R := by rw [hsum, red_add_of_lt hRint hsmall]
  rw [red_sum _ (fun j _ => htint j)] at hred
  have hterm : ∀ j, red (t j) = if z' j = k then red (Ψ j i) * red (u' j)⁻¹ * red (Ψ j i') else 0 := by
    intro j
    split_ifs with hj
    · rw [ht]; dsimp only; rw [term_eq hu' Ψ hj,
        red_mul (norm_mul_le_one (hΨ j i) (by rw [norm_inv, hu' j, inv_one])) (hΨ j i'),
        red_mul (hΨ j i) (by rw [norm_inv, hu' j, inv_one])]
    · exact red_eq_zero (term_lt hu hu' hΨ hW hΨD hi hi' hj)
  simp only [hterm] at hred
  rw [← Finset.sum_filter, Finset.sum_subtype (p := fun j => z' j = k)
    (Finset.univ.filter fun j => z' j = k) (fun j => by simp)
    (fun j => red (Ψ j i) * red (u' j)⁻¹ * red (Ψ j i'))] at hred
  rw [hred, hR]
  split_ifs
  · rfl
  · exact red_eq_zero (by simp)

end Scale

/-! ### From $\mathbb Z_p$-equivalence to diagonal forms -/

section Transport

variable {p : ℕ} [Fact p.Prime]

theorem isInt_gl (T : GL (Fin n) ℤ_[p]) : IsInt (T.val.map PadicInt.Coe.ringHom) := isInt_map _

/-- **Transport to the diagonal forms.** Let $F \sim D$ and $G \sim D'$ over $\mathbb Z_p$ (`ZpEquiv`), $F$, $G$
invertible, and let $\Phi$, $W$ be integral with $\Phi F = GW$ and $\Phi^{\mathsf T}G^{-1}\Phi - F^{-1}$ integral. Then
there are integral $\Psi$, $W'$, $Y$ with $\Psi D = D'W'$ and $\Psi^{\mathsf T}D'^{-1}\Psi - D^{-1} = Y$. -/
theorem transport {F G D D' Φ W : Matrix (Fin n) (Fin n) ℚ_[p]} (hF : IsUnit F.det)
    (hFD : ZpEquiv F D) (hGD : ZpEquiv G D') (hΦ : IsInt Φ) (hW : IsInt W) (hΦW : Φ * F = G * W)
    (hX : IsInt (Φᵀ * G⁻¹ * Φ - F⁻¹)) (hG : IsUnit G.det) :
    ∃ Ψ W' Y : Matrix (Fin n) (Fin n) ℚ_[p], IsInt Ψ ∧ IsInt W' ∧ IsInt Y ∧ Ψ * D = D' * W' ∧
      Ψᵀ * D'⁻¹ * Ψ - D⁻¹ = Y := by
  obtain ⟨T, hT⟩ := hFD
  obtain ⟨T', hT'⟩ := hGD
  set S := T.val.map PadicInt.Coe.ringHom with hS
  set Si := (T⁻¹).val.map PadicInt.Coe.ringHom with hSi
  set S' := T'.val.map PadicInt.Coe.ringHom with hS'
  set Si' := (T'⁻¹).val.map PadicInt.Coe.ringHom with hSi'
  have one_map : (1 : Matrix (Fin n) (Fin n) ℤ_[p]).map PadicInt.Coe.ringHom = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have h1 : S * Si = 1 := by
    rw [hS, hSi, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_map]
  have h2 : Si * S = 1 := by
    rw [hS, hSi, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_map]
  have h1' : S' * Si' = 1 := by
    rw [hS', hSi', ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_map]
  have h2' : Si' * S' = 1 := by
    rw [hS', hSi', ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_map]
  have c1 : ∀ X, S * (Si * X) = X := fun X => by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have c1' : ∀ X, S' * (Si' * X) = X := fun X => by rw [← Matrix.mul_assoc, h1', Matrix.one_mul]
  have t2 : ∀ X, Siᵀ * (Sᵀ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, h1, Matrix.transpose_one, Matrix.one_mul]
  have t2' : ∀ X, Si'ᵀ * (S'ᵀ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, h1', Matrix.transpose_one, Matrix.one_mul]
  have t1 : ∀ X, Sᵀ * (Siᵀ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, h2, Matrix.transpose_one, Matrix.one_mul]
  have t1' : ∀ X, S'ᵀ * (Si'ᵀ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, h2', Matrix.transpose_one, Matrix.one_mul]
  have hFF : ∀ X, F * (F⁻¹ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hF, Matrix.one_mul]
  have hGG : ∀ X, G * (G⁻¹ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hG, Matrix.one_mul]
  have hDi : D⁻¹ = Si * F⁻¹ * Siᵀ := by
    apply inv_eq_right_inv
    rw [← hT]
    simp only [Matrix.mul_assoc, c1, hFF]
    rw [← Matrix.transpose_mul, h2, Matrix.transpose_one]
  have hDi' : D'⁻¹ = Si' * G⁻¹ * Si'ᵀ := by
    apply inv_eq_right_inv
    rw [← hT']
    simp only [Matrix.mul_assoc, c1', hGG]
    rw [← Matrix.transpose_mul, h2', Matrix.transpose_one]
  refine ⟨S'ᵀ * Φ * Siᵀ, Si' * W * S, Si * (Φᵀ * G⁻¹ * Φ - F⁻¹) * Siᵀ, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((isInt_gl T').transpose.mul hΦ).mul (isInt_map _).transpose
  · exact ((isInt_map _).mul hW).mul (isInt_gl T)
  · exact ((isInt_map _).mul hX).mul (isInt_map _).transpose
  · rw [← hT, ← hT']
    simp only [Matrix.mul_assoc, t2, c1']
    rw [← Matrix.mul_assoc Φ, hΦW, Matrix.mul_assoc]
  · rw [hDi, hDi']
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, c1', t2', Matrix.mul_sub,
      Matrix.sub_mul]

/-- The inverse of $\operatorname{diag}(p^{z_i}u_i)$ ($u_i \ne 0$). -/
theorem inv_diag (z : Fin n → ℕ) {u : Fin n → ℚ_[p]} (hu : ∀ i, u i ≠ 0) :
    (diagonal fun i => (p : ℚ_[p]) ^ z i * u i)⁻¹ = diagonal fun i => ((p : ℚ_[p]) ^ z i * u i)⁻¹ := by
  apply inv_eq_right_inv
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext i
  exact mul_inv_cancel₀ (mul_ne_zero (pow_ne_zero _ p_ne_zero) (hu i))

end Transport

/-! ### Matrix data of an isomorphism of discriminant forms -/

section Integer

/-- An isomorphism of discriminant forms can be inverted (with the same $T$). -/
theorem discIso_symm {T : ℕ} {A B : Matrix (Fin n) (Fin n) ℤ} (h : DiscIso T A B) : DiscIso T B A := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ.symm, fun z y hzy => ?_⟩
  have : φ (QuotientAddGroup.mk y) = QuotientAddGroup.mk z := by rw [← hzy, AddEquiv.apply_symm_apply]
  obtain ⟨k, hk⟩ := hφ y z this
  exact ⟨-k, by rw [hk]; push_cast; ring⟩

/-- **Matrix form of an isomorphism of discriminant forms.** If `DiscIso T A B` (any $T$), there are integer matrices
$\Phi$, $W$ with $\Phi A = BW$ (so $[y] \mapsto [\Phi y]$ is well defined $\mathbb Z^n/A\mathbb Z^n \to \mathbb Z^n/B\mathbb Z^n$;
it is the given isomorphism) and $(\Phi y)^{\mathsf T}B^{-1}(\Phi y) - y^{\mathsf T}A^{-1}y \in \mathbb Z$ for all
$y \in \mathbb Z^n$. -/
theorem exists_lift {A B : Matrix (Fin n) (Fin n) ℤ} {T : ℕ} (h : DiscIso T A B) :
    ∃ Φ W : Matrix (Fin n) (Fin n) ℤ, Φ * A = B * W ∧
      ∀ y : Fin n → ℤ, ∃ m : ℤ, dualNorm B (Φ *ᵥ y) = dualNorm A y + m := by
  obtain ⟨φ, hφ⟩ := h
  set c : Fin n → (Fin n → ℤ) := fun j => Quotient.out (φ (QuotientAddGroup.mk (Pi.single j 1))) with hc
  set Φ : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j => c j i with hΦ
  have hmk : ∀ y, φ (QuotientAddGroup.mk y) = QuotientAddGroup.mk (Φ *ᵥ y) := by
    have key : (φ.toAddMonoidHom.comp (QuotientAddGroup.mk' (gramLat A))) =
        (QuotientAddGroup.mk' (gramLat B)).comp Φ.mulVecLin.toAddMonoidHom := by
      refine AddMonoidHom.functions_ext _ _ _ fun j x => ?_
      have e : (Pi.single j x : Fin n → ℤ) = x • Pi.single j (1 : ℤ) := by
        ext r; by_cases h : r = j
        · subst h; simp
        · simp [h]
      rw [e, map_zsmul, map_zsmul]
      congr 1
      have hcol : Φ *ᵥ Pi.single j 1 = c j := by
        rw [Matrix.mulVec_single_one]; ext i; simp [hΦ, Matrix.col]
      change φ (QuotientAddGroup.mk (Pi.single j 1)) = QuotientAddGroup.mk (Φ *ᵥ Pi.single j 1)
      rw [hcol, hc]
      exact (QuotientAddGroup.out_eq' _).symm
    intro y
    exact DFunLike.congr_fun key y
  have hw : ∀ j, ∃ w, B *ᵥ w = Φ *ᵥ (A *ᵥ Pi.single j 1) := by
    intro j
    have h0 : (QuotientAddGroup.mk (A *ᵥ Pi.single j 1) : DiscGroup A) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).2 (mem_gramLat.2 ⟨_, rfl⟩)
    have := hmk (A *ᵥ Pi.single j 1)
    rw [h0, map_zero] at this
    exact mem_gramLat.1 ((QuotientAddGroup.eq_zero_iff _).1 this.symm)
  choose w hw using hw
  refine ⟨Φ, Matrix.of fun i j => w j i, ?_, ?_⟩
  · ext i j
    have e1 : (Φ * A) i j = ((Φ * A) *ᵥ Pi.single j 1) i := by simp
    have e2 : (B * Matrix.of fun i j => w j i) i j = (B *ᵥ w j) i := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [e1, e2, ← Matrix.mulVec_mulVec, hw j]
  · intro y
    obtain ⟨k, hk⟩ := hφ y (Φ *ᵥ y) (hmk y)
    exact ⟨T * k, by rw [hk]; push_cast; ring⟩

variable {p : ℕ} [Fact p.Prime]

theorem inv_map_eq (A : Matrix (Fin n) (Fin n) ℤ) (hd : A.det ≠ 0) :
    ((gramQ A)⁻¹).map (Rat.castHom ℚ_[p]) = (A.map (Int.castRingHom ℚ_[p]))⁻¹ := by
  have hmap : (gramQ A).map (Rat.castHom ℚ_[p]) = A.map (Int.castRingHom ℚ_[p]) := by
    ext i j; simp [gramQ]
  rw [← hmap]; symm; apply inv_eq_right_inv
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (gramQ_det_ne hd)),
    Matrix.map_one _ (map_zero _) (map_one _)]

/-- The norm $y^{\mathsf T}A^{-1}y$ computed in $\mathbb Q_p$. -/
theorem dualNorm_cast (A : Matrix (Fin n) (Fin n) ℤ) (hd : A.det ≠ 0) (y : Fin n → ℤ) :
    ((dualNorm A y : ℚ) : ℚ_[p]) =
      (fun i => (y i : ℚ_[p])) ⬝ᵥ ((A.map (Int.castRingHom ℚ_[p]))⁻¹ *ᵥ fun i => (y i : ℚ_[p])) := by
  rw [← inv_map_eq A hd]
  simp [dualNorm, dotProduct, mulVec]

theorem conj_dot {R : Type*} [CommRing R] (M N : Matrix (Fin n) (Fin n) R) (v : Fin n → R) :
    (M *ᵥ v) ⬝ᵥ (N *ᵥ (M *ᵥ v)) = v ⬝ᵥ ((Mᵀ * N * M) *ᵥ v) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec v Mᵀ, vecMul_transpose]

theorem norm_two_eq_one (hp2 : p ≠ 2) : ‖((2 : ℤ) : ℚ_[p])‖ = 1 := by
  refine le_antisymm (Padic.norm_int_le_one _) (not_lt.1 fun hlt => hp2 ?_)
  have h := Padic.norm_intCast_lt_one_iff.1 hlt
  have h' : p ∣ 2 := by exact_mod_cast h
  exact (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h'

theorem cast_single (i : Fin n) : (fun r => ((Pi.single i (1 : ℤ) : Fin n → ℤ) r : ℚ_[p])) = Pi.single i 1 := by
  ext r; by_cases h : r = i
  · subst h; simp
  · simp [h]

/-- **The data over $\mathbb Q_p$, $p$ odd**: from `DiscIso T A B` ($A$, $B$ symmetric, $\det \ne 0$) we get integral
$\Phi$, $W$ over $\mathbb Q_p$ with $\Phi A = BW$ and $\Phi^{\mathsf T}B^{-1}\Phi - A^{-1}$ integral (its quadratic form
takes integer values on $\mathbb Z^n$, so twice each entry is an integer, and $2$ is a unit). -/
theorem qp_data (hp2 : p ≠ 2) {A B : Matrix (Fin n) (Fin n) ℤ} (hsA : Aᵀ = A) (hsB : Bᵀ = B)
    (hdA : A.det ≠ 0) (hdB : B.det ≠ 0) {T : ℕ} (h : DiscIso T A B) :
    ∃ Φ W : Matrix (Fin n) (Fin n) ℚ_[p], IsInt Φ ∧ IsInt W ∧
      Φ * A.map (Int.castRingHom ℚ_[p]) = B.map (Int.castRingHom ℚ_[p]) * W ∧
      IsInt (Φᵀ * (B.map (Int.castRingHom ℚ_[p]))⁻¹ * Φ - (A.map (Int.castRingHom ℚ_[p]))⁻¹) := by
  obtain ⟨Φ, W, hΦW, hm⟩ := exists_lift h
  set f := Int.castRingHom ℚ_[p] with hf
  refine ⟨Φ.map f, W.map f, isInt_intCast _, isInt_intCast _, by rw [← Matrix.map_mul, ← Matrix.map_mul, hΦW], ?_⟩
  set X := (Φ.map f)ᵀ * (B.map f)⁻¹ * Φ.map f - (A.map f)⁻¹ with hX
  have hQ : ∀ y : Fin n → ℤ, ∃ m : ℤ, (fun i => (y i : ℚ_[p])) ⬝ᵥ (X *ᵥ fun i => (y i : ℚ_[p])) = m := by
    intro y
    obtain ⟨m, hm⟩ := hm y
    refine ⟨m, ?_⟩
    have e1 := dualNorm_cast (p := p) B hdB (Φ *ᵥ y)
    have e2 := dualNorm_cast (p := p) A hdA y
    have e3 : (fun i => ((Φ *ᵥ y) i : ℚ_[p])) = Φ.map f *ᵥ fun i => (y i : ℚ_[p]) := by
      funext i; have := RingHom.map_mulVec f Φ y i; simpa [hf, Function.comp_def] using this
    rw [e3, conj_dot] at e1
    rw [hX, Matrix.sub_mulVec, dotProduct_sub, ← e1, ← e2, hm]; push_cast; ring
  have hsym : Xᵀ = X := by
    have hA' : (A.map f)ᵀ = A.map f := by rw [← Matrix.transpose_map, hsA]
    have hB' : (B.map f)ᵀ = B.map f := by rw [← Matrix.transpose_map, hsB]
    rw [hX, Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_nonsing_inv, Matrix.transpose_nonsing_inv, hA', hB', Matrix.mul_assoc]
  intro i j
  obtain ⟨m1, h1⟩ := hQ (Pi.single i 1 + Pi.single j 1)
  obtain ⟨m2, h2⟩ := hQ (Pi.single i 1)
  obtain ⟨m3, h3⟩ := hQ (Pi.single j 1)
  have ec : (fun r => (((Pi.single i 1 + Pi.single j 1 : Fin n → ℤ)) r : ℚ_[p])) =
      Pi.single i 1 + Pi.single j 1 := by
    rw [← cast_single i, ← cast_single j]; ext r; simp
  rw [ec] at h1
  rw [cast_single] at h2 h3
  have hji : X j i = X i j := by
    have := congrFun (congrFun hsym i) j; rwa [Matrix.transpose_apply] at this
  have q1 : (Pi.single i 1 + Pi.single j 1) ⬝ᵥ (X *ᵥ (Pi.single i 1 + Pi.single j 1))
      = X i i + X i j + X j i + X j j := by
    simp [mulVec_add, dotProduct_add, add_dotProduct]; ring
  have q2 : ∀ r : Fin n, (Pi.single r 1) ⬝ᵥ (X *ᵥ (Pi.single r 1)) = X r r := fun r => by simp
  rw [q1] at h1
  rw [q2] at h2 h3
  have e : ((2 : ℤ) : ℚ_[p]) * X i j = ((m1 - m2 - m3 : ℤ) : ℚ_[p]) := by
    push_cast; rw [← h1, ← h2, ← h3, hji]; ring
  have := congrArg norm e
  rw [norm_mul, norm_two_eq_one hp2, one_mul] at this
  rw [this]; exact Padic.norm_int_le_one _

end Integer

/-! ### Equal $p$-adic symbols -/

section Symbol

variable {p : ℕ} [Fact p.Prime]

theorem red_one : red (1 : ℚ_[p]) = 1 := by
  have := red_coe (p := p) 1
  rw [PadicInt.coe_one] at this; rw [this, map_one]

theorem norm_inv_one {x : ℚ_[p]} (h : ‖x‖ = 1) : ‖x⁻¹‖ = 1 := by rw [norm_inv, h, inv_one]

/-- **Scale $p^k$ from the two congruences**: if $P^{\mathsf T}\operatorname{diag}(\bar u'^{-1})P = \operatorname{diag}(\bar u^{-1})$
and $P'^{\mathsf T}\operatorname{diag}(\bar u^{-1})P' = \operatorname{diag}(\bar u'^{-1})$ over $\mathbb F_p$ (for the
blocks $\iota = \{i : z_i = k\}$, $\iota' = \{j : z'_j = k\}$), then $|\iota| = |\iota'|$ and
$\prod_{\iota}u_i = c^2\prod_{\iota'}u'_j$ for some $c \ne 0$ in $\mathbb Q_p$ (Hensel's lemma, $p$ odd). -/
theorem scale_eq (hp2 : p ≠ 2) {z z' : Fin n → ℕ} {u u' : Fin n → ℚ_[p]} (hu : ∀ i, ‖u i‖ = 1)
    (hu' : ∀ j, ‖u' j‖ = 1) {k : ℕ}
    {P : Matrix {j // z' j = k} {i // z i = k} (ZMod p)} {P' : Matrix {i // z i = k} {j // z' j = k} (ZMod p)}
    (h1 : Pᵀ * diagonal (fun j : {j // z' j = k} => red (u' j)⁻¹) * P = diagonal (fun i : {i // z i = k} => red (u i)⁻¹))
    (h2 : P'ᵀ * diagonal (fun i : {i // z i = k} => red (u i)⁻¹) * P' =
      diagonal (fun j : {j // z' j = k} => red (u' j)⁻¹)) :
    Fintype.card {i // z i = k} = Fintype.card {j // z' j = k} ∧
      ∃ c : ℚ_[p], c ≠ 0 ∧ ∏ i : {i // z i = k}, u i = c ^ 2 * ∏ j : {j // z' j = k}, u' j := by
  classical
  have hd : ∀ i : {i // z i = k}, red (u i)⁻¹ ≠ 0 := fun i => red_ne_zero (norm_inv_one (hu i))
  have hd' : ∀ j : {j // z' j = k}, red (u' j)⁻¹ ≠ 0 := fun j => red_ne_zero (norm_inv_one (hu' j))
  have hc : Fintype.card {i // z i = k} = Fintype.card {j // z' j = k} :=
    le_antisymm (card_le_of_congr P _ _ hd h1) (card_le_of_congr P' _ _ hd' h2)
  refine ⟨hc, ?_⟩
  set e := Fintype.equivOfCardEq hc
  have hprod := prod_eq_of_congr P _ _ e h1
  set s := (P.submatrix e id).det
  set a := ∏ i : {i // z i = k}, u i with ha
  set b := ∏ j : {j // z' j = k}, u' j with hb
  have hna : ‖a‖ = 1 := by rw [ha, norm_prod]; exact Finset.prod_eq_one fun i _ => hu i
  have hnb : ‖b‖ = 1 := by rw [hb, norm_prod]; exact Finset.prod_eq_one fun j _ => hu' j
  set q := a⁻¹ * b with hq
  have hnq : ‖q‖ = 1 := by rw [hq, norm_mul, norm_inv, hna, hnb]; norm_num
  have hred : red q = s ^ 2 := by
    rw [hq, red_mul (norm_inv_one hna).le hnb.le, ha, hb, ← Finset.prod_inv_distrib,
      red_prod (f := fun i : {i // z i = k} => (u i)⁻¹) _ (fun i _ => (norm_inv_one (hu i)).le),
      red_prod (f := fun j : {j // z' j = k} => u' j) _ (fun j _ => (hu' j).le), hprod, mul_assoc,
      ← Finset.prod_mul_distrib]
    have : ∀ j : {j // z' j = k}, red (u' j)⁻¹ * red (u' j) = 1 := fun j => by
      rw [← red_mul (norm_inv_one (hu' j)).le (hu' j).le, inv_mul_cancel₀ (ne_zero_of_norm_one (hu' j)),
        red_one]
    simp [this]
  have hs : s ≠ 0 := by
    intro h0; apply red_ne_zero hnq; rw [hred, h0]; ring
  obtain ⟨w, hw⟩ := Siegel.Kneser.exists_sq_eq_of_toZMod hp2 (toZp q) hs hred
  have hwq : ((w : ℚ_[p])) ^ 2 = q := by
    rw [← PadicInt.coe_pow, hw, coe_toZp hnq.le]
  have hq0 : q ≠ 0 := ne_zero_of_norm_one hnq
  have hw0 : (w : ℚ_[p]) ≠ 0 := by rintro h; rw [h] at hwq; simp at hwq; exact hq0 hwq.symm
  have ha0 : a ≠ 0 := ne_zero_of_norm_one hna
  have hb0 : b ≠ 0 := ne_zero_of_norm_one hnb
  refine ⟨(w : ℚ_[p])⁻¹, inv_ne_zero hw0, ?_⟩
  rw [inv_pow, hwq, hq]; field_simp

/-- Splitting $\prod_i u_i$ by the scale $z_i \in \{0\} \cup [1, M]$. -/
theorem prod_split (z : Fin n → ℕ) (u : Fin n → ℚ_[p]) {M : ℕ} (hM : ∀ i, z i ≤ M) :
    ∏ i, u i = (∏ i : {i // z i = 0}, u i) * ∏ k ∈ Finset.Icc 1 M, ∏ i : {i // z i = k}, u i := by
  classical
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => z i = 0)]
  congr 1
  · exact Finset.prod_subtype _ (by simp) _
  · rw [← Finset.prod_fiberwise_of_maps_to (s := Finset.univ.filter fun i => ¬ z i = 0)
      (t := Finset.Icc 1 M) (g := z) (fun i hi => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        simp only [Finset.mem_Icc]; exact ⟨Nat.one_le_iff_ne_zero.2 hi, hM i⟩)]
    refine Finset.prod_congr rfl fun k hk => ?_
    have hk0 : k ≠ 0 := by simp only [Finset.mem_Icc] at hk; omega
    rw [Finset.filter_filter]
    refine Finset.prod_subtype _ (fun i => ?_) _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨by rw [h]; exact hk0, h⟩

/-- Splitting $n$ by the scale $z_i \in \{0\} \cup [1, M]$. -/
theorem card_split (z : Fin n → ℕ) {M : ℕ} (hM : ∀ i, z i ≤ M) :
    n = Fintype.card {i // z i = 0} + ∑ k ∈ Finset.Icc 1 M, Fintype.card {i // z i = k} := by
  classical
  have := prod_split (p := 2) z (fun _ => (2 : ℚ_[2])) hM
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
  rw [Finset.prod_pow_eq_pow_sum, ← pow_add] at this
  have h2 : (2 : ℚ_[2]) ≠ 0 := two_ne_zero
  have h21 : ‖(2 : ℚ_[2])‖ < 1 := by
    have := Padic.norm_p_lt_one (p := 2); exact_mod_cast this
  have := congrArg norm this
  rw [norm_pow, norm_pow] at this
  exact pow_right_injective₀ (norm_pos_iff.2 h2) (ne_of_lt h21) this

/-- **The determinant relation**: if $F \sim \operatorname{diag}(p^{z_i}u_i)$ over $\mathbb Z_p$ then
$s^2\det F = p^{\sum_i z_i}\prod_i u_i$ for some $p$-adic unit $s$ ($s = \det$ of the change of basis). -/
theorem det_rel {F : Matrix (Fin n) (Fin n) ℚ_[p]} {z : Fin n → ℕ} {u : Fin n → ℚ_[p]}
    (h : ZpEquiv F (diagonal fun i => (p : ℚ_[p]) ^ z i * u i)) :
    ∃ s : ℚ_[p], ‖s‖ = 1 ∧ s ^ 2 * F.det = (p : ℚ_[p]) ^ (∑ i, z i) * ∏ i, u i := by
  obtain ⟨T, hT⟩ := h
  refine ⟨(T.val.map PadicInt.Coe.ringHom).det, ?_, ?_⟩
  · have e := RingHom.map_det PadicInt.Coe.ringHom T.val
    rw [RingHom.mapMatrix_apply] at e
    rw [← e]
    have hu : IsUnit T.val.det := (Matrix.isUnit_iff_isUnit_det _).1 T.isUnit
    rw [PadicInt.isUnit_iff, PadicInt.norm_def] at hu
    exact hu
  · have := congrArg det hT
    rw [det_mul, det_mul, det_transpose, det_diagonal, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum] at this
    rw [← this]; ring

/-- **The symbols agree.** Under the hypotheses of the scale congruences in both directions and the determinant
relation $\prod_i u_i = c^2\prod_j u'_j$, the $p$-adic symbols of $\operatorname{diag}(p^{z_i}u_i)$ and
$\operatorname{diag}(p^{z'_j}u'_j)$ coincide: scales $k \ge 1$ by `scale_eq`, the unimodular scale $k = 0$ by the
dimension $n$ and the determinant. -/
theorem symbol_eq {z z' : Fin n → ℕ} {u u' : Fin n → ℚ_[p]} (hu' : ∀ j, ‖u' j‖ = 1)
    (hk : ∀ k, 1 ≤ k → Fintype.card {i // z i = k} = Fintype.card {j // z' j = k} ∧
      ∃ c : ℚ_[p], c ≠ 0 ∧ ∏ i : {i // z i = k}, u i = c ^ 2 * ∏ j : {j // z' j = k}, u' j)
    (htot : ∃ c : ℚ_[p], c ≠ 0 ∧ ∏ i, u i = c ^ 2 * ∏ j, u' j) :
    oddSymbolOfDiag p z u = oddSymbolOfDiag p z' u' := by
  classical
  set M := ∑ i, z i + ∑ j, z' j
  have hM : ∀ i, z i ≤ M := fun i =>
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans (Nat.le_add_right _ _)
  have hM' : ∀ j, z' j ≤ M := fun j =>
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans (Nat.le_add_left _ _)
  have hc : ∀ k, ∃ c : ℚ_[p], c ≠ 0 ∧ (1 ≤ k → ∏ i : {i // z i = k}, u i = c ^ 2 * ∏ j : {j // z' j = k}, u' j) := by
    intro k
    by_cases h1 : 1 ≤ k
    · obtain ⟨c, hc0, hc⟩ := (hk k h1).2; exact ⟨c, hc0, fun _ => hc⟩
    · exact ⟨1, one_ne_zero, fun h => absurd h h1⟩
  choose c hc0 hcp using hc
  -- scale 0: dimension
  have hcard0 : Fintype.card {i // z i = 0} = Fintype.card {j // z' j = 0} := by
    have e1 := card_split z hM
    have e2 := card_split z' hM'
    have : ∑ k ∈ Finset.Icc 1 M, Fintype.card {i // z i = k} = ∑ k ∈ Finset.Icc 1 M, Fintype.card {j // z' j = k} :=
      Finset.sum_congr rfl fun k hk' => (hk k (Finset.mem_Icc.1 hk').1).1
    omega
  -- scale 0: determinant
  have hprod0 : ∃ c0 : ℚ_[p], c0 ≠ 0 ∧ ∏ i : {i // z i = 0}, u i = c0 ^ 2 * ∏ j : {j // z' j = 0}, u' j := by
    obtain ⟨c1, hc1, h1⟩ := htot
    rw [prod_split z u hM, prod_split z' u' hM'] at h1
    have e : ∏ k ∈ Finset.Icc 1 M, ∏ i : {i // z i = k}, u i =
        (∏ k ∈ Finset.Icc 1 M, c k) ^ 2 * ∏ k ∈ Finset.Icc 1 M, ∏ j : {j // z' j = k}, u' j := by
      rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k hk' => hcp k (Finset.mem_Icc.1 hk').1
    rw [e] at h1
    set C := ∏ k ∈ Finset.Icc 1 M, c k
    set Q := ∏ k ∈ Finset.Icc 1 M, ∏ j : {j // z' j = k}, u' j
    have hC : C ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc0 k
    have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ =>
      Finset.prod_ne_zero_iff.2 fun j _ => ne_zero_of_norm_one (hu' j)
    refine ⟨c1 / C, div_ne_zero hc1 hC, ?_⟩
    have h2 : (∏ i : {i // z i = 0}, u i) * C ^ 2 * Q = (c1 ^ 2 * ∏ j : {j // z' j = 0}, u' j) * Q := by
      linear_combination h1
    have h3 := mul_right_cancel₀ hQ h2
    rw [div_pow, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 2 hC)]
    linear_combination h3
  funext k
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · obtain ⟨c0, hc0', hp0⟩ := hprod0
    have hsq := isSquare_iff_of_eq hc0' hp0
    simp only [oddSymbolOfDiag, hcard0, hsq]
  · obtain ⟨hcard, c', hc', hp'⟩ := hk k hk1
    have hsq := isSquare_iff_of_eq hc' hp'
    simp only [oddSymbolOfDiag, hcard, hsq]

end Symbol

/-! ### Odd primes: the theorem -/

section Main

variable {p : ℕ} [Fact p.Prime]

/-- **$\mathbb Z_p$-equivalence from an isomorphism of discriminant forms, $p$ odd** (matrix form). For symmetric
$A$, $B \in M_n(\mathbb Z)$ with $\det A = \det B \ne 0$ and `DiscIso T A B` (any $T \in \mathbb N$), the Gram matrices
are $\mathbb Z_p$-equivalent for every odd prime $p$. -/
theorem zpEquiv_of_discIso (hp2 : p ≠ 2) {A B : Matrix (Fin n) (Fin n) ℤ} (hsA : Aᵀ = A) (hsB : Bᵀ = B)
    (hdA : A.det ≠ 0) (hdet : A.det = B.det) {T : ℕ} (h : DiscIso T A B) :
    ZpEquiv (A.map (Int.castRingHom ℚ_[p])) (B.map (Int.castRingHom ℚ_[p])) := by
  have hdB : B.det ≠ 0 := hdet ▸ hdA
  set F := A.map (Int.castRingHom ℚ_[p]) with hF
  set G := B.map (Int.castRingHom ℚ_[p]) with hG
  have hFu : IsUnit F.det := isUnit_iff_ne_zero.2 (det_map_ne hdA)
  have hGu : IsUnit G.det := isUnit_iff_ne_zero.2 (det_map_ne hdB)
  obtain ⟨σ, z, u, hu, hFD, rfl⟩ :=
    exists_isOddSymbolOf hp2 (transpose_map_of_symm _ hsA) (det_map_ne hdA) (isClassIntegral_map A)
  obtain ⟨τ, z', u', hu', hGD, rfl⟩ :=
    exists_isOddSymbolOf hp2 (transpose_map_of_symm _ hsB) (det_map_ne hdB) (isClassIntegral_map B)
  refine zpEquiv_of_oddSymbol_eq hp2 ⟨z, u, hu, hFD, rfl⟩ ⟨z', u', hu', hGD, ?_⟩
  have hu0 : ∀ i, u i ≠ 0 := fun i => ne_zero_of_norm_one (hu i)
  have hu0' : ∀ j, u' j ≠ 0 := fun j => ne_zero_of_norm_one (hu' j)
  obtain ⟨Φ, W, hΦ, hW, hΦW, hX⟩ := qp_data (p := p) hp2 hsA hsB hdA hdB h
  obtain ⟨Φ', W', hΦ', hW', hΦW', hX'⟩ := qp_data (p := p) hp2 hsB hsA hdB hdA (discIso_symm h)
  obtain ⟨Ψ, W1, Y, hΨ, hW1, hY, hΨD, hΨX⟩ := transport hFu hFD hGD hΦ hW hΦW hX hGu
  obtain ⟨Ψ', W1', Y', hΨ', hW1', hY', hΨD', hΨX'⟩ := transport hGu hGD hFD hΦ' hW' hΦW' hX' hFu
  rw [inv_diag z hu0, inv_diag z' hu0'] at hΨX hΨX'
  refine (symbol_eq hu' (fun k hk => scale_eq hp2 hu hu'
    (scale_congr hu hu' hΨ hW1 hY hΨD hΨX hk) (scale_congr hu' hu hΨ' hW1' hY' hΨD' hΨX' hk)) ?_)
  -- the determinant relation
  obtain ⟨s, hs, hsF⟩ := det_rel hFD
  obtain ⟨s', hs', hsG⟩ := det_rel hGD
  have hFG : F.det = G.det := by
    rw [hF, hG, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← RingHom.map_det,
      hdet]
  have hN : ∑ i, z i = ∑ j, z' j := by
    have e1 := congrArg norm hsF
    have e2 := congrArg norm hsG
    rw [norm_mul, norm_pow, hs, one_pow, one_mul, norm_mul, norm_prod,
      Finset.prod_eq_one (fun i _ => hu i), mul_one] at e1
    rw [norm_mul, norm_pow, hs', one_pow, one_mul, norm_mul, norm_prod,
      Finset.prod_eq_one (fun j _ => hu' j), mul_one, ← hFG, e1] at e2
    rw [norm_pow, norm_pow] at e2
    have hp0 : (0 : ℝ) < ‖(p : ℚ_[p])‖ := norm_pos_iff.2 p_ne_zero
    exact pow_right_injective₀ hp0 (ne_of_lt Padic.norm_p_lt_one) e2
  have hs0 : s ≠ 0 := ne_zero_of_norm_one hs
  have hs0' : s' ≠ 0 := ne_zero_of_norm_one hs'
  refine ⟨s / s', div_ne_zero hs0 hs0', ?_⟩
  rw [hN, hFG] at hsF
  have hpN : (p : ℚ_[p]) ^ (∑ j, z' j) ≠ 0 := pow_ne_zero _ p_ne_zero
  have h' : (p : ℚ_[p]) ^ (∑ j, z' j) * (s' ^ 2 * ∏ i, u i) =
      (p : ℚ_[p]) ^ (∑ j, z' j) * (s ^ 2 * ∏ j, u' j) := by
    linear_combination (-s' ^ 2) * hsF + s ^ 2 * hsG
  have h'' := mul_left_cancel₀ hpN h'
  rw [div_pow, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 2 hs0')]
  linear_combination h''

/-- **Lemma 2 ("if") at odd primes, in the form of the genus condition**: for symmetric integral $A$, $B$ with
$\det A = \det B \ne 0$ and an isomorphism of discriminant forms `DiscIso T A B` (any $T$), the forms
$x^{\mathsf T}Ax$ and $x^{\mathsf T}Bx$ are $\mathrm{GL}_n(\mathbb Z_p)$-equivalent for every odd prime $p$. -/
theorem isometricGL_padic_of_discIso (hp2 : p ≠ 2) {A B : Matrix (Fin n) (Fin n) ℤ} (hsA : Aᵀ = A)
    (hsB : Bᵀ = B) (hdA : A.det ≠ 0) (hdet : A.det = B.det) {T : ℕ} (h : DiscIso T A B) :
    IsometricGL ((ofMatrixZ A).map (Int.castRingHom ℤ_[p])) ((ofMatrixZ B).map (Int.castRingHom ℤ_[p])) :=
  (isometricGL_padic_iff hsA hsB).2 (zpEquiv_of_discIso hp2 hsA hsB hdA hdet h)

end Main

end Lemma2Odd

/-! ### Headline results -/

variable {n : ℕ}

theorem PosDefGram.intPosDef {A : Matrix (Fin n) (Fin n) ℤ} (hA : PosDefGram A) :
    IntQF.PosDef (ofMatrixZ A) := fun x hx => by
  rw [eval_ofMatrixZ]; exact hA.pos_int hx

/-- **Equal determinants**: positive definite lattices with isomorphic discriminant groups have the same
determinant ($|\det A| = |\mathbb Z^n/A\mathbb Z^n|$ and $\det A > 0$). -/
theorem det_eq_of_discIso {A B : Matrix (Fin n) (Fin n) ℤ} (hA : PosDefGram A) (hB : PosDefGram B) {T : ℕ}
    (h : DiscIso T A B) : A.det = B.det := by
  obtain ⟨φ, -⟩ := h
  have h1 := card_discGroup hA.det_ne
  have h2 := card_discGroup hB.det_ne
  have h3 := Nat.card_congr φ.toEquiv
  have pA := det_pos_of_posDef hA.1 hA.intPosDef
  have pB := det_pos_of_posDef hB.1 hB.intPosDef
  omega

/-- **Conway–Sloane 1988, §11, Lemma 2, "if", at the odd primes** (p. 280): positive definite lattices with Gram
matrices $A$, $B$ (same dimension $n$) and an isomorphism of discriminant forms `DiscIso (gramType A) A B` are
equivalent over $\mathbb Z_p$ for every odd prime $p$: the forms $x^{\mathsf T}Ax$ and $x^{\mathsf T}Bx$ are
$\mathrm{GL}_n(\mathbb Z_p)$-equivalent. Unconditional. Following the paper's proof ("the given information is enough to
determine the invariants of their Jordan decompositions"): the $p$-part of the discriminant form determines the Jordan
constituents of scale $p^k$, $k \ge 1$ (dimension and the square class of the determinant), the unimodular constituent
is then fixed by $n$ and $\det A = \det B$, and Conway–Sloane's Theorem 9 (Ch. 15) concludes. -/
@[kb "conwaysloane1988" "§11, Lemma 2, p. 280 (if, at the odd primes: equivalence over Z_p, p odd)"]
theorem lemma2_if_odd {A B : Matrix (Fin n) (Fin n) ℤ} (hA : PosDefGram A) (hB : PosDefGram B)
    (h : DiscIso (gramType A) A B) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    IsometricGL ((ofMatrixZ A).map (Int.castRingHom ℤ_[p])) ((ofMatrixZ B).map (Int.castRingHom ℤ_[p])) :=
  Lemma2Odd.isometricGL_padic_of_discIso hp2 hA.1 hB.1 hA.det_ne (det_eq_of_discIso hA hB h) h

/-- **The real place**: positive definite lattices of the same dimension are equivalent over $\mathbb R$. -/
theorem isometricGL_real_of_posDefGram {A B : Matrix (Fin n) (Fin n) ℤ} (hA : PosDefGram A) (hB : PosDefGram B) :
    IsometricGL ((ofMatrixZ A).map (Int.castRingHom ℝ)) ((ofMatrixZ B).map (Int.castRingHom ℝ)) := by
  refine Siegel.isometricGL_real_of_posDef ⟨A, hA.1, fun x => eval_ofMatrixZ A x⟩
    ⟨B, hB.1, fun x => eval_ofMatrixZ B x⟩ (fun x hx => ?_) (fun x hx => ?_)
  · rw [eval_ofMatrixZ]; exact hA.pos_int hx
  · rw [eval_ofMatrixZ]; exact hB.pos_int hx

/-- **Lemma 2, the "if" half, at $p = 2$** (§11, p. 280), as a **named statement**: positive definite lattices $L$, $M$
with Gram matrices $A$, $B$ of the same dimension $n$ and type $T$ (`gramType`), with an isomorphism
$L^*/L \cong M^*/M$ preserving norms mod $T$ (`DiscIso (gramType A) A B`), are equivalent over $\mathbb Z_2$: the forms
$x^{\mathsf T}Ax$ and $x^{\mathsf T}Bx$ are $\mathrm{GL}_n(\mathbb Z_2)$-equivalent.

* Field `imp`: for every $n$ and all $A, B \in M_n(\mathbb Z)$ with `PosDefGram A`, `PosDefGram B`,
  `gramType A = gramType B` and `DiscIso (gramType A) A B`, the forms are equivalent over $\mathbb Z_2$.

This is exactly what remains of `Lemma2IfStatement`: the odd primes are `lemma2_if_odd` and the real place is
`isometricGL_real_of_posDefGram`, so `lemma2If_of_dyadic` recovers `Lemma2IfStatement`, and conversely
(`dyadic_of_lemma2If`); the two named statements are equivalent.

*Why a global argument is needed.* Locally at $2$ the discriminant form does not determine the lattice: over
$\mathbb Z_2$, $\langle 1, 1\rangle$ and $\langle 3, 3\rangle$ have the same rank, parity and determinant class and
trivial discriminant forms, but different Hasse invariants (they are not $\mathbb Z_2$-equivalent). A proof must
therefore use that $L$, $M$ are global positive definite lattices: the $2$-adic Hasse invariant (equivalently the
oddity) is forced by the product formula (the oddity formula) from the real place and the odd primes, which the
discriminant form does determine (`lemma2_if_odd`). The paper says only that the case $p = 2$ is the nontrivial
one. -/
@[kb "conwaysloane1988" "§11, Lemma 2, p. 280 (if, at p = 2: equivalence over Z_2; stated)"]
structure Lemma2IfDyadicStatement : Prop where
  imp : ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℤ), PosDefGram A → PosDefGram B →
    gramType A = gramType B → DiscIso (gramType A) A B →
      IsometricGL ((ofMatrixZ A).map (Int.castRingHom ℤ_[2])) ((ofMatrixZ B).map (Int.castRingHom ℤ_[2]))

/-- **The "if" half of Lemma 2 from its dyadic part** (§11, p. 280): the odd primes (`lemma2_if_odd`) and the real place
are proved, so only the equivalence over $\mathbb Z_2$ (`Lemma2IfDyadicStatement`) is assumed. -/
@[kb "conwaysloane1988" "§11, Lemma 2, p. 280 (if, conditional on the case p = 2)"]
theorem lemma2If_of_dyadic (h : Lemma2IfDyadicStatement) : Lemma2IfStatement where
  imp n A B hA hB ht hi := by
    refine ⟨fun p _ => ?_, isometricGL_real_of_posDefGram hA hB⟩
    by_cases hp2 : p = 2
    · subst hp2; exact h.imp n A B hA hB ht hi
    · exact lemma2_if_odd hA hB hi p hp2

/-- The dyadic statement is no weaker than the "if" half: `Lemma2IfStatement` implies `Lemma2IfDyadicStatement`. -/
theorem dyadic_of_lemma2If (h : Lemma2IfStatement) : Lemma2IfDyadicStatement where
  imp n A B hA hB ht hi := (h.imp n A B hA hB ht hi).1 2

/-- **Lemma 2 from its dyadic "if" part** (the "only if" half and the odd primes are proved). -/
@[kb "conwaysloane1988" "§11, Lemma 2, p. 280 (conditional on the 'if' half at p = 2)"]
theorem lemma2Statement_of_dyadic (h : Lemma2IfDyadicStatement) : Lemma2Statement :=
  lemma2Statement_of_if (lemma2If_of_dyadic h)

/-- **Lemma 4 from the dyadic "if" part of Lemma 2** (with the proved Lemma 3). -/
@[kb "conwaysloane1988" "§11, Lemma 4, p. 280 (conditional on the 'if' half of Lemma 2 at p = 2)"]
theorem lemma4_of_dyadic (h : Lemma2IfDyadicStatement) : Lemma4Statement :=
  lemma4_of_lemma2If (lemma2If_of_dyadic h)

end QuadFormsKB.ConwaySloane.Mass
