/-
# Cassels, Chapter 8, Example 2: $\mathbb Z_p$-equivalence of four pairs of forms

Source: J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 8, *Examples*, Ex. 2 (i)–(iv), pp. 124–125.

**Setting** (as in `Ch8/Canonical.lean`). A form $f(\vec x) = \vec x^{t}F\vec x$ in $n$ variables is given by its
symmetric Gram matrix $F$ (so $2x_0x_1$ is $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ and a cross term $c\,x_ix_j$ is the
entry $c/2$ in positions $(i,j)$ and $(j,i)$), and two forms are $\mathbb Z_p$-equivalent (`ZpEquiv`) when
$G = T^{t}FT$ with $T \in \mathrm{GL}_n(\mathbb Z_p)$.  Cassels' variables $x_1, x_2, x_3$ are $x_0, x_1, x_2$ here.
Every statement below is for **all** primes $p$, written `∀ (p : ℕ) [Fact p.Prime], ...`.

**The four questions and the answers (proved)**, "for which $p$ are the following pairs $\mathbb Z_p$-equivalent?"

* (i) $2x_0x_1$ and $x_0^2 - x_1^2$: exactly for $p \ne 2$ (`ex2_i`).
* (ii) $2x_0x_1$ and $x_0^2 + x_1^2$: exactly for $p \equiv 1 \pmod 4$ (`ex2_ii`).
* (iii) $5x_0^2 + 13x_1^2 + 11x_2^2 + 2x_1x_2 + 2x_2x_0 + 16x_0x_1$ and
  $x_0^2 + 16x_1^2 + 10x_2^2 + 14x_1x_2 - 4x_2x_0 + 2x_0x_1$ (both of determinant $9$): exactly for $p \ne 2, 3$
  (`ex2_iii`).
* (iv) $x_0^2 + 2x_1^2 + 6x_2^2 + 6x_1x_2$ and $2x_0^2 + 3x_1^2 + 5x_2^2$ (determinants $3$ and $30$): exactly for
  $p \notin \{2, 3, 5\}$ with $10$ a square modulo $p$ (`ex2_iv`), i.e. $\left(\frac{10}{p}\right) = 1$; for example
  $p = 13, 31, 37, 41, 43$.

**Methods.**
* *Equivalences.* For $p$ odd and $p \nmid \det F$, unimodular symmetric forms with the same determinant are
  $\mathbb Z_p$-equivalent (`isometricGL_of_unimodular`, `Siegel/UnimodularPadic.lean`, via the form `gramForm`);
  `zp_unimodular` transfers this to Gram matrices, `zp_unimodular_scaled3` allows determinants differing by the
  square of a unit (Hensel's lemma gives the unit, `exists_sq_eq_of_toZMod`).  For (ii) one more substitution
  $x_1 \mapsto \sqrt{-1}\,x_1$.
* *Inequivalences.* At $p = 2$ in (i), (ii): $2x_0x_1$ takes only even values while $x_0^2 \pm x_1^2$ has a unit
  coefficient of $x_0^2$ (`hyp_entry_ne_one`).  At $p = 2$ in (iii): Cassels' Example 5 (`Ex5.ex5_iff`) with the
  characteristic vectors $(0,0,1)$ and $(1,0,1)$, values $11 \not\equiv 7 \pmod 8$.  Determinants: $G = T^{t}FT$
  gives $\det G = (\det T)^2\det F$ with $\det T$ a unit (`det_eq_sq_mul`); this settles (ii) for $p \equiv 3 \pmod 4$
  and (iv) for $p \ne 3$.  At $p = 3$ in (iii), (iv): the number of zeros of $\vec x^{t}F\vec x$ in $\mathbb F_3^3$ is
  invariant (`card_zeros_eq`): $3 \ne 9$ in (iii), $15 \ne 3$ in (iv).

Nothing is assumed: all results are unconditional.
-/
import QuadFormsKB.Literature.Cassels.Ch8.Ex5
import QuadFormsKB.Siegel.UnimodularPadic

open Matrix

noncomputable section

namespace QuadFormsKB.Cassels.Ch8Ex2

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Helpers: integral matrices -/

/-- Helper: $\mathbb Z_p$-equivalence of two matrices with entries in $\mathbb Z_p$ (viewed in $\mathbb Q_p$) means
$T^{t}FT = G$ for some $T \in \mathrm{GL}_n(\mathbb Z_p)$, as an identity of $\mathbb Z_p$-matrices. -/
theorem zpEquiv_iff_zp {n : ℕ} (F G : Matrix (Fin n) (Fin n) ℤ_[p]) :
    ZpEquiv (F.map PadicInt.Coe.ringHom) (G.map PadicInt.Coe.ringHom) ↔
      ∃ T : GL (Fin n) ℤ_[p], T.valᵀ * F * T.val = G := by
  have inj : Function.Injective (PadicInt.Coe.ringHom (p := p)) := Subtype.val_injective
  unfold ZpEquiv
  refine exists_congr fun T => ?_
  rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]
  exact (Matrix.map_injective inj).eq_iff

/-- Helper: $G = T^{t}FT$ gives $\det G = (\det T)^2 \det F$. -/
theorem det_eq_sq_mul {n : ℕ} {F G : Matrix (Fin n) (Fin n) ℤ_[p]} (T : GL (Fin n) ℤ_[p])
    (h : T.valᵀ * F * T.val = G) : G.det = T.val.det ^ 2 * F.det := by
  rw [← h, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]; ring

/-- Helper: the determinant of an element of $\mathrm{GL}_n(\mathbb Z_p)$ is a unit. -/
theorem isUnit_det_gl {n : ℕ} (T : GL (Fin n) ℤ_[p]) : IsUnit T.val.det :=
  (Matrix.isUnit_iff_isUnit_det T.val).1 T.isUnit

/-- Helper: a prime $q \ne p$ is a unit in $\mathbb Z_p$. -/
theorem isUnit_prime {q : ℕ} (hq : q.Prime) (h : p ≠ q) : IsUnit ((q : ℕ) : ℤ_[p]) :=
  PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2 ((Nat.coprime_primes hp.out hq).2 h))

/-- Helper: an integral matrix with unit determinant as an element of $\mathrm{GL}_n(\mathbb Z_p)$. -/
def glOf {n : ℕ} (T : Matrix (Fin n) (Fin n) ℤ_[p]) (h : IsUnit T.det) : GL (Fin n) ℤ_[p] :=
  ((Matrix.isUnit_iff_isUnit_det T).2 h).unit

/-! ### Helper: unimodular forms over $\mathbb Z_p$, $p$ odd, as Gram matrices -/

/-- Helper: the quadratic form $\vec x^{t}M\vec x$ of an arbitrary matrix $M$ over a commutative ring $R$, with
upper triangular coefficients $c_{ii} = M_{ii}$, $c_{ij} = M_{ij} + M_{ji}$ for $i < j$ (generalizes `ofMatrixZ`). -/
def gramForm {R : Type*} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) : QuadForm R n where
  coeff := Matrix.of fun i j => if i < j then M i j + M j i else if i = j then M i i else 0
  upper := by
    intro i j h
    simp only [id] at h
    simp [Matrix.of_apply, not_lt.mpr h.le, (ne_of_lt h).symm]

/-- Helper: the Hessian of `gramForm M` is $M + M^{t}$. -/
theorem hessian_gramForm {R : Type*} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) :
    (gramForm M).hessian = M + Mᵀ := by
  ext i j
  simp only [QuadForm.hessian, gramForm, Matrix.add_apply, Matrix.transpose_apply, Matrix.of_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, not_lt.mpr h.le, h.ne']
  · simp
  · simp [h, not_lt.mpr h.le, h.ne']; ring

/-- Helper: value-preserving substitutions preserve the Hessian, over any commutative ring (polarization). -/
theorem hessian_congr {R : Type*} [CommRing R] {n : ℕ} {Q Q' : QuadForm R n} {g : Matrix (Fin n) (Fin n) R}
    (hg : ∀ x, Q.eval (g *ᵥ x) = Q'.eval x) : gᵀ * Q.hessian * g = Q'.hessian := by
  have hpol : ∀ x y : Fin n → R,
      (g *ᵥ x) ⬝ᵥ (Q.hessian *ᵥ (g *ᵥ y)) = x ⬝ᵥ (Q'.hessian *ᵥ y) := by
    intro x y
    have h1 := QuadForm.polar_eq_hessian R Q (g *ᵥ x) (g *ᵥ y)
    have h2 := QuadForm.polar_eq_hessian R Q' x y
    rw [← Matrix.mulVec_add] at h1
    have e : ∀ M : Matrix (Fin n) (Fin n) R, M.map (algebraMap R R) = M := fun M => by
      ext; simp
    rw [e] at h1 h2
    have h3 : Q.evalIn R (g *ᵥ (x + y)) = Q'.evalIn R (x + y) := hg (x + y)
    have h4 : Q.evalIn R (g *ᵥ x) = Q'.evalIn R x := hg x
    have h5 : Q.evalIn R (g *ᵥ y) = Q'.evalIn R y := hg y
    rw [h3, h4, h5] at h1
    rw [← h1, ← h2]
  ext i j
  have := hpol (Pi.single i 1) (Pi.single j 1)
  have e2 : Pi.single i 1 ⬝ᵥ Q'.hessian *ᵥ Pi.single j 1 = Q'.hessian i j := by
    simp
  rw [e2] at this
  rw [← this]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  simp [Pi.single_apply]
  ring

/-- Helper: **unimodular symmetric forms over $\mathbb Z_p$, $p$ odd, with equal determinants are equivalent.**
If $F, G \in M_n(\mathbb Z_p)$ are symmetric, $\det F \in \mathbb Z_p^{\times}$ and $\det G = \det F$, then
$T^{t}FT = G$ for some $T \in \mathrm{GL}_n(\mathbb Z_p)$.  Consequence of `isometricGL_of_unimodular`
(O'Meara 92:1; Cassels Ch. 8, Lemma 3.4). -/
theorem zp_unimodular (hp2 : p ≠ 2) {n : ℕ} (F G : Matrix (Fin n) (Fin n) ℤ_[p]) (hF : Fᵀ = F) (hG : Gᵀ = G)
    (hdF : IsUnit F.det) (hdet : G.det = F.det) :
    ∃ T : GL (Fin n) ℤ_[p], T.valᵀ * F * T.val = G := by
  have h2 : IsUnit (2 : ℤ_[p]) :=
    Siegel.Kneser.isUnit_of_toZMod_ne_zero (Siegel.Kneser.toZMod_two_ne_zero hp2)
  have hH : ∀ M : Matrix (Fin n) (Fin n) ℤ_[p], Mᵀ = M → (gramForm M).hessian.det = 2 ^ n * M.det := by
    intro M hM
    rw [hessian_gramForm, hM, ← two_smul ℤ_[p] M, Matrix.det_smul, Fintype.card_fin]
  have hu : IsUnit (gramForm F).hessian.det := by
    rw [hH F hF]; exact (h2.pow n).mul hdF
  have hQ : ¬ (p : ℤ_[p]) ∣ (gramForm F).hessian.det := fun hd =>
    (PadicInt.irreducible_p (p := p)).not_isUnit (isUnit_of_dvd_unit hd hu)
  have hd' : (gramForm G).hessian.det = (gramForm F).hessian.det := by
    rw [hH F hF, hH G hG, hdet]
  obtain ⟨g, hg⟩ := Siegel.Kneser.isometricGL_of_unimodular hp2 (gramForm F) (gramForm G) hQ hd'
  have := hessian_congr hg
  rw [hessian_gramForm, hessian_gramForm, hF, hG, ← two_smul ℤ_[p] F, ← two_smul ℤ_[p] G,
    Matrix.mul_smul, Matrix.smul_mul] at this
  exact ⟨g, smul_right_injective _ h2.ne_zero this⟩

/-- Helper: like `zp_unimodular` for $3 \times 3$ matrices, with $\det G = w^2\det F$ for a unit $w \in
\mathbb Z_p$ (first scale the last variable by $w$). -/
theorem zp_unimodular_scaled3 (hp2 : p ≠ 2) (F G : Matrix (Fin 3) (Fin 3) ℤ_[p]) (hF : Fᵀ = F) (hG : Gᵀ = G)
    (hdF : IsUnit F.det) {w : ℤ_[p]} (hw : IsUnit w) (hdet : G.det = w ^ 2 * F.det) :
    ∃ T : GL (Fin 3) ℤ_[p], T.valᵀ * F * T.val = G := by
  set S : Matrix (Fin 3) (Fin 3) ℤ_[p] := !![1, 0, 0; 0, 1, 0; 0, 0, w] with hS
  have hSd : S.det = w := by simp [hS, Matrix.det_fin_three]
  have hSu : IsUnit S.det := hSd ▸ hw
  have hF' : (Sᵀ * F * S)ᵀ = Sᵀ * F * S := by
    simp [Matrix.transpose_mul, Matrix.mul_assoc, hF]
  have hd : (Sᵀ * F * S).det = w ^ 2 * F.det := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hSd]; ring
  obtain ⟨T2, hT2⟩ := zp_unimodular hp2 (Sᵀ * F * S) G hF' hG (by rw [hd]; exact (hw.pow 2).mul hdF)
    (by rw [hd, hdet])
  refine ⟨glOf S hSu * T2, ?_⟩
  rw [Units.val_mul, ← hT2]
  simp only [glOf, IsUnit.unit_spec, Matrix.transpose_mul, Matrix.mul_assoc]

/-! ### Helpers: reduction modulo $p$ -/

/-- Helper: $x^{t}(T^{t}FT)\,x = (Tx)^{t}F(Tx)$. -/
theorem quad_congr {R : Type*} [CommRing R] {n : ℕ} (T N : Matrix (Fin n) (Fin n) R) (x : Fin n → R) :
    x ⬝ᵥ ((Tᵀ * N * T) *ᵥ x) = (T *ᵥ x) ⬝ᵥ (N *ᵥ (T *ᵥ x)) := by
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x Tᵀ,
    Matrix.vecMul_transpose]

/-- Helper: **the number of zeros of the reduction modulo $p$ is invariant.**  If $T^{t}FT = G$ with
$T \in \mathrm{GL}_n(\mathbb Z_p)$, then $\vec x^{t}\bar F\vec x$ and $\vec x^{t}\bar G\vec x$ have the same number
of zeros $\vec x \in \mathbb F_p^n$ (bars: reduction modulo $p$, `PadicInt.toZMod`). -/
theorem card_zeros_eq {n : ℕ} {F G : Matrix (Fin n) (Fin n) ℤ_[p]} (T : GL (Fin n) ℤ_[p])
    (hT : T.valᵀ * F * T.val = G) :
    Nat.card {x : Fin n → ZMod p // x ⬝ᵥ (F.map PadicInt.toZMod *ᵥ x) = 0} =
      Nat.card {x : Fin n → ZMod p // x ⬝ᵥ (G.map PadicInt.toZMod *ᵥ x) = 0} := by
  have hmul : T.val.map (PadicInt.toZMod (p := p)) * (T⁻¹).val.map (PadicInt.toZMod (p := p)) = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hmul' : (T⁻¹).val.map (PadicInt.toZMod (p := p)) * T.val.map (PadicInt.toZMod (p := p)) = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  let e : (Fin n → ZMod p) ≃ (Fin n → ZMod p) :=
    { toFun := fun x => T.val.map PadicInt.toZMod *ᵥ x
      invFun := fun x => (T⁻¹).val.map PadicInt.toZMod *ᵥ x
      left_inv := fun x => by dsimp only; rw [Matrix.mulVec_mulVec, hmul', Matrix.one_mulVec]
      right_inv := fun x => by dsimp only; rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec] }
  have hG : G.map (PadicInt.toZMod (p := p)) =
      (T.val.map PadicInt.toZMod)ᵀ * F.map PadicInt.toZMod * T.val.map PadicInt.toZMod := by
    rw [← hT]; simp [Matrix.map_mul, Matrix.transpose_map]
  refine (Nat.card_congr (Equiv.subtypeEquiv e (fun x => ?_))).symm
  show x ⬝ᵥ (G.map PadicInt.toZMod *ᵥ x) = 0 ↔
    (T.val.map PadicInt.toZMod *ᵥ x) ⬝ᵥ (F.map PadicInt.toZMod *ᵥ (T.val.map PadicInt.toZMod *ᵥ x)) = 0
  rw [hG, quad_congr]

/-! ### The classical forms of the four pairs, over $\mathbb Z_p$ -/

/-- Helper: the Gram matrix of $2x_0x_1$ over $\mathbb Z_p$. -/
def hypZ : Matrix (Fin 2) (Fin 2) ℤ_[p] := !![0, 1; 1, 0]

/-- Helper: `2xy` has no unit coefficient: $(T^{t}\,\mathrm{hyp}\,T)_{00} = 2T_{00}T_{10} \ne 1$ at $p = 2$. -/
theorem hyp_entry_ne_one (T : Matrix (Fin 2) (Fin 2) ℤ_[2]) :
    (Tᵀ * (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ_[2]) * T) 0 0 ≠ 1 := by
  intro h
  have e : (Tᵀ * (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ_[2]) * T) 0 0 = 2 * (T 0 0 * T 1 0) := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
  rw [e] at h
  have := congrArg (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) h
  rw [map_mul, map_one] at this
  have h2 : (PadicInt.toZMod (2 : ℤ_[2])) = 0 := by
    have : (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) := by norm_num
    rw [this, map_natCast]; decide
  rw [h2, zero_mul] at this
  exact zero_ne_one this

/-- Helper: $-1$ is a square in $\mathbb Z_p$ when $p \equiv 1 \pmod 4$. -/
theorem exists_sq_neg_one (h : p % 4 = 1) : ∃ z : ℤ_[p], z ^ 2 = -1 := by
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at h
  obtain ⟨s, hs⟩ := ZMod.exists_sq_eq_neg_one_iff.2 (show p % 4 ≠ 3 by omega)
  refine Siegel.Kneser.exists_sq_eq_of_toZMod hp2 (-1) (s := s) ?_ ?_
  · rintro rfl
    simp at hs
  · simp [hs, sq]

/-- Helper: the literal matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ over $\mathbb Q_p$. -/
theorem lit_hyp : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ_[p]) =
    (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ_[p]).map PadicInt.Coe.ringHom := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

/-- Helper: the literal matrix $\mathrm{diag}(1,-1)$ over $\mathbb Q_p$. -/
theorem lit_hm : (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℚ_[p]) =
    (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℤ_[p]).map PadicInt.Coe.ringHom := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

/-- Helper: the literal matrix $\mathrm{diag}(1,1)$ over $\mathbb Q_p$. -/
theorem lit_hp : (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℚ_[p]) =
    (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ_[p]).map PadicInt.Coe.ringHom := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

/-! ### (i) and (ii) -/

/-- Helper: $2x_0x_1 \sim x_0^2 - x_1^2$ over $\mathbb Z_p$ for $p \ne 2$ (both unimodular of determinant $-1$). -/
theorem hyp_to_hm (hp2 : p ≠ 2) : ZpEquiv (p := p) !![0, 1; 1, 0] !![1, 0; 0, -1] := by
  rw [lit_hyp, lit_hm, zpEquiv_iff_zp]
  refine zp_unimodular hp2 _ _ ?_ ?_ ?_ ?_
  · ext i j; fin_cases i <;> fin_cases j <;> simp
  · ext i j; fin_cases i <;> fin_cases j <;> simp
  · simp [Matrix.det_fin_two]
  · simp [Matrix.det_fin_two]

/-- **Cassels, Ch. 8, Example 2 (i)** (pp. 124–125): *for which $p$ are $2x_0x_1$ and $x_0^2 - x_1^2$
$\mathbb Z_p$-equivalent?*  Exactly for $p \ne 2$ (Gram matrices $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ and
$\mathrm{diag}(1,-1)$, both of determinant $-1$; at $p = 2$ the first form takes only even values).  Here $p$ ranges
over all primes. -/
@[kb "cassels1978" "Ch. 8, Ex. 2 (i), pp. 124-125"]
theorem ex2_i : ∀ (p : ℕ) [Fact p.Prime],
    ZpEquiv (p := p) !![0, 1; 1, 0] !![1, 0; 0, -1] ↔ p ≠ 2 := by
  intro p hp
  constructor
  · intro h hp2
    subst hp2
    rw [lit_hyp, lit_hm, zpEquiv_iff_zp] at h
    obtain ⟨T, hT⟩ := h
    have := congrFun (congrFun hT 0) 0
    exact hyp_entry_ne_one T.val (by simpa using this)
  · exact hyp_to_hm

/-- **Cassels, Ch. 8, Example 2 (ii)** (pp. 124–125): *for which $p$ are $2x_0x_1$ and $x_0^2 + x_1^2$
$\mathbb Z_p$-equivalent?*  Exactly for $p \equiv 1 \pmod 4$ (Gram matrices $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ and
$\mathrm{diag}(1,1)$; the determinants $-1$ and $1$ differ by the square of a unit iff $-1$ is a square modulo $p$;
at $p = 2$ the first form takes only even values).  Here $p$ ranges over all primes. -/
@[kb "cassels1978" "Ch. 8, Ex. 2 (ii), pp. 124-125"]
theorem ex2_ii : ∀ (p : ℕ) [Fact p.Prime],
    ZpEquiv (p := p) !![0, 1; 1, 0] !![1, 0; 0, 1] ↔ p % 4 = 1 := by
  intro p hp
  constructor
  · intro h
    by_cases hp2 : p = 2
    · subst hp2
      rw [lit_hyp, lit_hp, zpEquiv_iff_zp] at h
      obtain ⟨T, hT⟩ := h
      have := congrFun (congrFun hT 0) 0
      exact absurd (by simpa using this) (hyp_entry_ne_one T.val)
    · rw [lit_hyp, lit_hp, zpEquiv_iff_zp] at h
      obtain ⟨T, hT⟩ := h
      have hd := det_eq_sq_mul T hT
      have hd' : (1 : ℤ_[p]) = T.val.det ^ 2 * (-1) := by
        simpa [Matrix.det_fin_two] using hd
      have hsq : (-1 : ZMod p) = (PadicInt.toZMod T.val.det) * (PadicInt.toZMod T.val.det) := by
        have := congrArg (PadicInt.toZMod : ℤ_[p] →+* ZMod p) hd'
        simp only [map_one, map_mul, map_pow, map_neg] at this
        linear_combination (-1 : ZMod p) * this
      have h3 : p % 4 ≠ 3 := ZMod.exists_sq_eq_neg_one_iff.1 ⟨_, hsq⟩
      have := hp.out.eq_two_or_odd
      omega
  · intro h
    have hp2 : p ≠ 2 := by rintro rfl; norm_num at h
    obtain ⟨z, hz⟩ := exists_sq_neg_one (p := p) h
    have hzu : IsUnit z := isUnit_iff_exists_inv.2 ⟨-z, by linear_combination (-1 : ℤ_[p]) * hz⟩
    refine (hyp_to_hm hp2).trans ?_
    rw [lit_hm, lit_hp, zpEquiv_iff_zp]
    have hz' : (z : ℚ_[p]) ^ 2 = -1 := by
      have := congrArg ((↑) : ℤ_[p] → ℚ_[p]) hz
      simpa using this
    set S : Matrix (Fin 2) (Fin 2) ℤ_[p] := !![1, 0; 0, z] with hS
    have hdz : S.det = z := by simp [hS, Matrix.det_fin_two]
    refine ⟨glOf S (by rw [hdz]; exact hzu), ?_⟩
    simp only [glOf, IsUnit.unit_spec]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hS, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals (try linear_combination (-1 : ℚ_[p]) * hz')

/-! ### (iii) -/

/-- Helper: the Gram matrix of the first form of (iii) over $\mathbb Z_p$
($5x_0^2 + 13x_1^2 + 11x_2^2 + 2x_1x_2 + 2x_2x_0 + 16x_0x_1$). -/
def A3 : Matrix (Fin 3) (Fin 3) ℤ_[p] := !![5, 8, 1; 8, 13, 1; 1, 1, 11]

/-- Helper: the Gram matrix of the second form of (iii) over $\mathbb Z_p$
($x_0^2 + 16x_1^2 + 10x_2^2 + 14x_1x_2 - 4x_2x_0 + 2x_0x_1$). -/
def B3 : Matrix (Fin 3) (Fin 3) ℤ_[p] := !![1, 1, -2; 1, 16, 7; -2, 7, 10]

/-- Helper: the literal Gram matrix of the first form of (iii) over $\mathbb Q_p$. -/
theorem lit_A3 : (!![5, 8, 1; 8, 13, 1; 1, 1, 11] : Matrix (Fin 3) (Fin 3) ℚ_[p]) =
    (A3 : Matrix (Fin 3) (Fin 3) ℤ_[p]).map PadicInt.Coe.ringHom := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [A3] <;> norm_cast

/-- Helper: the literal Gram matrix of the second form of (iii) over $\mathbb Q_p$. -/
theorem lit_B3 : (!![1, 1, -2; 1, 16, 7; -2, 7, 10] : Matrix (Fin 3) (Fin 3) ℚ_[p]) =
    (B3 : Matrix (Fin 3) (Fin 3) ℤ_[p]).map PadicInt.Coe.ringHom := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [B3] <;> norm_cast

/-- Helper: $\det A_3 = \det B_3 = 9$. -/
theorem det_A3 : (A3 : Matrix (Fin 3) (Fin 3) ℤ_[p]).det = 9 := by
  simp [A3, Matrix.det_fin_three]; norm_num

/-- Helper: $\det B_3 = 9$. -/
theorem det_B3 : (B3 : Matrix (Fin 3) (Fin 3) ℤ_[p]).det = 9 := by
  simp [B3, Matrix.det_fin_three]; norm_num

/-- Helper: $2$ is a unit of $\mathbb Z_p$ for $p \ne 2$. -/
theorem isUnit_two (h : p ≠ 2) : IsUnit (2 : ℤ_[p]) := by
  simpa using isUnit_prime (p := p) Nat.prime_two h

/-- Helper: $3$ is a unit of $\mathbb Z_p$ for $p \ne 3$. -/
theorem isUnit_three (h : p ≠ 3) : IsUnit (3 : ℤ_[p]) := by
  simpa using isUnit_prime (p := p) Nat.prime_three h

/-- Helper: $5$ is a unit of $\mathbb Z_p$ for $p \ne 5$. -/
theorem isUnit_five (h : p ≠ 5) : IsUnit (5 : ℤ_[p]) := by
  simpa using isUnit_prime (p := p) Nat.prime_five h

/-- Helper: at $p = 2$ the forms of (iii) are not $\mathbb Z_2$-equivalent: they are not even $\mathbb Q_2$-equivalent,
by Example 5 with the characteristic vectors $(0,0,1)$ (value $11$) and $(1,0,1)$ (value $7$). -/
theorem iii_two : ¬ ZpEquiv (p := 2) ((A3 : Matrix (Fin 3) (Fin 3) ℤ_[2]).map PadicInt.Coe.ringHom)
    ((B3 : Matrix (Fin 3) (Fin 3) ℤ_[2]).map PadicInt.Coe.ringHom) := by
  intro h
  obtain ⟨T, hT⟩ := h
  have hq : Ex5.QEquiv ((A3 : Matrix (Fin 3) (Fin 3) ℤ_[2]).map PadicInt.Coe.ringHom)
      ((B3 : Matrix (Fin 3) (Fin 3) ℤ_[2]).map PadicInt.Coe.ringHom) := by
    refine ⟨T.val.map PadicInt.Coe.ringHom, ?_, hT⟩
    have hd := isUnit_det_gl T
    have h := hd.map PadicInt.Coe.ringHom
    rwa [RingHom.map_det] at h
  have hu9 : IsUnit (9 : ℤ_[2]) := by
    have := (isUnit_three (p := 2) (by norm_num)).pow 2
    norm_num at this
    exact this
  have hAs : (A3 : Matrix (Fin 3) (Fin 3) ℤ_[2])ᵀ = A3 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [A3]
  have hBs : (B3 : Matrix (Fin 3) (Fin 3) ℤ_[2])ᵀ = B3 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [B3]
  have hbA : ∀ a : Fin 3 → ℤ_[2], (2 : ℤ_[2]) ∣ a ⬝ᵥ (A3 *ᵥ a) - a ⬝ᵥ (A3 *ᵥ ![0, 0, 1]) := by
    intro a
    have e : a ⬝ᵥ (A3 *ᵥ a) - a ⬝ᵥ (A3 *ᵥ ![0, 0, 1]) =
        5 * a 0 ^ 2 + 13 * a 1 ^ 2 + 11 * a 2 ^ 2 + 16 * (a 0 * a 1) + 2 * (a 0 * a 2) + 2 * (a 1 * a 2)
          - a 0 - a 1 - 11 * a 2 := by
      simp [A3, dotProduct, Matrix.mulVec, Fin.sum_univ_three]; ring
    rw [e, Ex5.two_dvd_iff_toZMod]
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    generalize PadicInt.toZMod (a 0) = x
    generalize PadicInt.toZMod (a 1) = y
    generalize PadicInt.toZMod (a 2) = z
    revert x y z
    decide
  have hbB : ∀ a : Fin 3 → ℤ_[2], (2 : ℤ_[2]) ∣ a ⬝ᵥ (B3 *ᵥ a) - a ⬝ᵥ (B3 *ᵥ ![1, 0, 1]) := by
    intro a
    have e : a ⬝ᵥ (B3 *ᵥ a) - a ⬝ᵥ (B3 *ᵥ ![1, 0, 1]) =
        a 0 ^ 2 + 16 * a 1 ^ 2 + 10 * a 2 ^ 2 + 2 * (a 0 * a 1) - 4 * (a 0 * a 2) + 14 * (a 1 * a 2)
          + a 0 - 8 * a 1 - 8 * a 2 := by
      simp [B3, dotProduct, Matrix.mulVec, Fin.sum_univ_three]; ring
    rw [e, Ex5.two_dvd_iff_toZMod]
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    generalize PadicInt.toZMod (a 0) = x
    generalize PadicInt.toZMod (a 1) = y
    generalize PadicInt.toZMod (a 2) = z
    revert x y z
    decide
  have key := (Ex5.ex5_iff A3 B3 hAs hBs (by rw [det_A3]; exact hu9) (by rw [det_B3]; exact hu9)
    ![0, 0, 1] ![1, 0, 1] hbA hbB).1 hq
  have e4 : ![0, 0, 1] ⬝ᵥ ((A3 : Matrix (Fin 3) (Fin 3) ℤ_[2]) *ᵥ ![0, 0, 1]) -
      ![1, 0, 1] ⬝ᵥ ((B3 : Matrix (Fin 3) (Fin 3) ℤ_[2]) *ᵥ ![1, 0, 1]) = 4 := by
    simp [A3, B3, dotProduct, Matrix.mulVec, Fin.sum_univ_three]; norm_num
  have h8 := key.2
  rw [e4, Ex5.eight_dvd_iff, map_ofNat] at h8
  revert h8
  decide

/-- Helper: zeros of $\vec x^{t}\bar A_3\vec x$ over $\mathbb F_3$: there are $3$. -/
theorem zeros_A3 : Nat.card {x : Fin 3 → ZMod 3 //
    x ⬝ᵥ ((A3 : Matrix (Fin 3) (Fin 3) ℤ_[3]).map PadicInt.toZMod *ᵥ x) = 0} = 3 := by
  have e : (A3 : Matrix (Fin 3) (Fin 3) ℤ_[3]).map PadicInt.toZMod = !![5, 8, 1; 8, 13, 1; 1, 1, 11] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [A3] <;> exact map_ofNat _ _
  rw [e, Nat.card_eq_fintype_card]
  decide

/-- Helper: zeros of $\vec x^{t}\bar B_3\vec x$ over $\mathbb F_3$: there are $9$. -/
theorem zeros_B3 : Nat.card {x : Fin 3 → ZMod 3 //
    x ⬝ᵥ ((B3 : Matrix (Fin 3) (Fin 3) ℤ_[3]).map PadicInt.toZMod *ᵥ x) = 0} = 9 := by
  have e : (B3 : Matrix (Fin 3) (Fin 3) ℤ_[3]).map PadicInt.toZMod = !![1, 1, -2; 1, 16, 7; -2, 7, 10] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [B3] <;> exact map_ofNat _ _
  rw [e, Nat.card_eq_fintype_card]
  decide

/-- **Cassels, Ch. 8, Example 2 (iii)** (pp. 124–125): *for which $p$ are
$5x_0^2 + 13x_1^2 + 11x_2^2 + 2x_1x_2 + 2x_2x_0 + 16x_0x_1$ and
$x_0^2 + 16x_1^2 + 10x_2^2 + 14x_1x_2 - 4x_2x_0 + 2x_0x_1$ $\mathbb Z_p$-equivalent?*  Exactly for $p \ne 2, 3$.
Both have determinant $9$, so for $p \ge 5$ they are unimodular of equal determinant; at $p = 2$ both are odd
unimodular but not even $\mathbb Q_2$-equivalent (Example 5: $11 \not\equiv 7 \pmod 8$); at $p = 3$ the reductions
modulo $3$ have $3$ and $9$ zeros in $\mathbb F_3^3$.  Here $p$ ranges over all primes. -/
@[kb "cassels1978" "Ch. 8, Ex. 2 (iii), pp. 124-125"]
theorem ex2_iii : ∀ (p : ℕ) [Fact p.Prime],
    ZpEquiv (p := p) !![5, 8, 1; 8, 13, 1; 1, 1, 11] !![1, 1, -2; 1, 16, 7; -2, 7, 10] ↔
      p ≠ 2 ∧ p ≠ 3 := by
  intro p hp
  rw [lit_A3, lit_B3]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rintro rfl; exact iii_two h
    · rintro rfl
      obtain ⟨T, hT⟩ := (zpEquiv_iff_zp _ _).1 h
      have := card_zeros_eq T hT
      rw [zeros_A3, zeros_B3] at this
      norm_num at this
  · rintro ⟨h2, h3⟩
    rw [zpEquiv_iff_zp]
    have hu9 : IsUnit (9 : ℤ_[p]) := by
      have := (isUnit_three h3).pow 2
      norm_num at this
      exact this
    refine zp_unimodular h2 _ _ ?_ ?_ (by rw [det_A3]; exact hu9) (by rw [det_A3, det_B3])
    · ext i j; fin_cases i <;> fin_cases j <;> simp [A3]
    · ext i j; fin_cases i <;> fin_cases j <;> simp [B3]

/-! ### (iv) -/

/-- Helper: the Gram matrix of the first form of (iv) over $\mathbb Z_p$ ($x_0^2 + 2x_1^2 + 6x_2^2 + 6x_1x_2$). -/
def C3 : Matrix (Fin 3) (Fin 3) ℤ_[p] := !![1, 0, 0; 0, 2, 3; 0, 3, 6]

/-- Helper: the Gram matrix of the second form of (iv) over $\mathbb Z_p$ ($2x_0^2 + 3x_1^2 + 5x_2^2$). -/
def D3 : Matrix (Fin 3) (Fin 3) ℤ_[p] := !![2, 0, 0; 0, 3, 0; 0, 0, 5]

/-- Helper: the literal Gram matrix of the first form of (iv) over $\mathbb Q_p$. -/
theorem lit_C3 : (!![1, 0, 0; 0, 2, 3; 0, 3, 6] : Matrix (Fin 3) (Fin 3) ℚ_[p]) =
    (C3 : Matrix (Fin 3) (Fin 3) ℤ_[p]).map PadicInt.Coe.ringHom := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [C3] <;> norm_cast

/-- Helper: the literal Gram matrix of the second form of (iv) over $\mathbb Q_p$. -/
theorem lit_D3 : (!![2, 0, 0; 0, 3, 0; 0, 0, 5] : Matrix (Fin 3) (Fin 3) ℚ_[p]) =
    (D3 : Matrix (Fin 3) (Fin 3) ℤ_[p]).map PadicInt.Coe.ringHom := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [D3] <;> norm_cast

/-- Helper: $\det C_3 = 3$. -/
theorem det_C3 : (C3 : Matrix (Fin 3) (Fin 3) ℤ_[p]).det = 3 := by
  simp [C3, Matrix.det_fin_three]; norm_num

/-- Helper: $\det D_3 = 30$. -/
theorem det_D3 : (D3 : Matrix (Fin 3) (Fin 3) ℤ_[p]).det = 30 := by
  simp [D3, Matrix.det_fin_three]; norm_num

/-- Helper: zeros of $\vec x^{t}\bar C_3\vec x$ over $\mathbb F_3$: there are $15$. -/
theorem zeros_C3 : Nat.card {x : Fin 3 → ZMod 3 //
    x ⬝ᵥ ((C3 : Matrix (Fin 3) (Fin 3) ℤ_[3]).map PadicInt.toZMod *ᵥ x) = 0} = 15 := by
  have e : (C3 : Matrix (Fin 3) (Fin 3) ℤ_[3]).map PadicInt.toZMod = !![1, 0, 0; 0, 2, 3; 0, 3, 6] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [C3] <;> exact map_ofNat _ _
  rw [e, Nat.card_eq_fintype_card]
  decide

/-- Helper: zeros of $\vec x^{t}\bar D_3\vec x$ over $\mathbb F_3$: there are $3$. -/
theorem zeros_D3 : Nat.card {x : Fin 3 → ZMod 3 //
    x ⬝ᵥ ((D3 : Matrix (Fin 3) (Fin 3) ℤ_[3]).map PadicInt.toZMod *ᵥ x) = 0} = 3 := by
  have e : (D3 : Matrix (Fin 3) (Fin 3) ℤ_[3]).map PadicInt.toZMod = !![2, 0, 0; 0, 3, 0; 0, 0, 5] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [D3] <;> exact map_ofNat _ _
  rw [e, Nat.card_eq_fintype_card]
  decide

/-- Helper: $10 \ne 0$ in $\mathbb F_p$ when $p \ne 2, 5$. -/
theorem ten_ne_zero (h2 : p ≠ 2) (h5 : p ≠ 5) : (10 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((10 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have : p ∣ 2 * 5 := h'
  rcases (Nat.Prime.dvd_mul hp.out).1 this with h | h
  · exact h2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 h)
  · exact h5 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_five).1 h)

/-- **Cassels, Ch. 8, Example 2 (iv)** (pp. 124–125): *for which $p$ are $x_0^2 + 2x_1^2 + 6x_2^2 + 6x_1x_2$ and
$2x_0^2 + 3x_1^2 + 5x_2^2$ $\mathbb Z_p$-equivalent?*  Exactly for the primes $p \notin \{2, 3, 5\}$ such that $10$ is a
square modulo $p$ (that is, $\left(\frac{10}{p}\right) = 1$; for example $p = 13, 31, 37, 41, 43$).  The determinants are
$3$ and $30$, so a $\mathbb Z_p$-equivalence needs $10$ to be the square of the unit $\det T$, which excludes
$p = 2, 5$ and forces $10$ to be a square modulo $p$; at $p = 3$ the reductions modulo $3$ have $15$ and $3$ zeros in
$\mathbb F_3^3$; for the remaining $p$ both forms are unimodular and Hensel's lemma supplies the square root of $10$.
Here $p$ ranges over all primes. -/
@[kb "cassels1978" "Ch. 8, Ex. 2 (iv), pp. 124-125"]
theorem ex2_iv : ∀ (p : ℕ) [Fact p.Prime],
    ZpEquiv (p := p) !![1, 0, 0; 0, 2, 3; 0, 3, 6] !![2, 0, 0; 0, 3, 0; 0, 0, 5] ↔
      p ≠ 2 ∧ p ≠ 3 ∧ p ≠ 5 ∧ IsSquare (10 : ZMod p) := by
  intro p hp
  rw [lit_C3, lit_D3, zpEquiv_iff_zp]
  constructor
  · rintro ⟨T, hT⟩
    have hd := det_eq_sq_mul T hT
    rw [det_C3, det_D3] at hd
    have hu : T.val.det ^ 2 = 10 := by
      refine mul_left_cancel₀ (show (3 : ℤ_[p]) ≠ 0 by norm_num) ?_
      linear_combination (-1 : ℤ_[p]) * hd
    have hs : (10 : ZMod p) = PadicInt.toZMod T.val.det * PadicInt.toZMod T.val.det := by
      have := congrArg (PadicInt.toZMod : ℤ_[p] →+* ZMod p) hu
      simp only [map_pow, map_ofNat] at this
      rw [← this, sq]
    have hs0 : PadicInt.toZMod T.val.det ≠ 0 :=
      Siegel.Kneser.toZMod_ne_zero_of_isUnit (isUnit_det_gl T)
    have h10 : (10 : ZMod p) ≠ 0 := by rw [hs]; exact mul_ne_zero hs0 hs0
    refine ⟨?_, ?_, ?_, ⟨_, hs⟩⟩
    · intro h2
      refine h10 ?_
      have : ((10 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff 10 p).2 (by rw [h2]; norm_num)
      exact_mod_cast this
    · rintro rfl
      have := card_zeros_eq T hT
      rw [zeros_C3, zeros_D3] at this
      norm_num at this
    · intro h5
      refine h10 ?_
      have : ((10 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff 10 p).2 (by rw [h5]; norm_num)
      exact_mod_cast this
  · rintro ⟨h2, h3, h5, s, hs⟩
    have hs0 : s ≠ 0 := by
      rintro rfl
      exact ten_ne_zero h2 h5 (by simpa using hs)
    obtain ⟨w, hw⟩ := Siegel.Kneser.exists_sq_eq_of_toZMod h2 (10 : ℤ_[p]) hs0
      (by rw [map_ofNat, hs, sq])
    have h10u : IsUnit (10 : ℤ_[p]) := by
      have := (isUnit_two h2).mul (isUnit_five h5)
      norm_num at this
      exact this
    have hwu : IsUnit w := (isUnit_pow_iff two_ne_zero).1 (hw ▸ h10u)
    have h3u := isUnit_three h3
    refine zp_unimodular_scaled3 h2 _ _ ?_ ?_ (by rw [det_C3]; exact h3u) hwu
      (by rw [det_C3, det_D3, hw]; norm_num)
    · ext i j; fin_cases i <;> fin_cases j <;> simp [C3]
    · ext i j; fin_cases i <;> fin_cases j <;> simp [D3]

end QuadFormsKB.Cassels.Ch8Ex2

end
