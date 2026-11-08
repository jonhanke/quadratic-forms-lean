/-
# Watson (1963): even unimodular summands at the prime $2$

G. L. Watson, *The class-number of a positive quadratic form*, Proc. London Math. Soc. (3) 13 (1963) 549–576.

Let $f$ be an integral form in $n$ variables and $\bar B_f$ its polar form reduced modulo $2$: the Hessian matrix
$\bar H_f \in M_n(\mathbb F_2)$, a symmetric matrix with zero diagonal (an alternating form).

**Proved here.**
* `exists_gram_unit`: for a form $Q$ over $\mathbb Z_2$ in $n$ variables with
  $2k \le \operatorname{rank}\bar H_Q + 1$ there is an $n \times 2k$ matrix $H$ over $\mathbb Z_2$ with
  $\det(H^{\mathsf T} H_Q H)$ a unit (induction on $k$, splitting off a hyperbolic pair with unit Gram matrix and
  passing to the Schur complement; the "$+1$" makes the evenness of the rank of an alternating form automatic).
* `exists_even_unimodular_rep`, `exists_even_unimodular_summand_of_rank`: if
  $2k \le \operatorname{rank}\bar H_f + 1$ (in particular if $\operatorname{rank}\bar H_f \ge 2k$) then over
  $\mathbb Z_2$, $f \cong U \perp \psi$ with $U$ in $2k$ variables with unit Hessian determinant (an even unimodular
  summand); `exists_even_unimodular_summand_of_rank_fin` states it on $\mathrm{Fin}(2k+m)$.
* `rankModP_two_le_rank_add_one`: $r_2(f) \le \operatorname{rank}\bar H_f + 1$ (`radModP 2 f` has codimension
  at most $1$ in the kernel of $\bar H_f$, because $\bar f$ is additive on that kernel).
* `IsWatsonMinimal.exists_even_unimodular_rep_six`: a positive definite Watson-minimal form in $n \ge 12$ variables
  has an even unimodular summand of rank $6$ over $\mathbb Z_2$.
* `quaternary_split_two`: for a Watson-minimal positive definite $f$ in $4 + m$ variables, $m \ge 8$, and a quaternary
  $g$ with odd Hessian determinant, $f \cong g \perp \psi$ over $\mathbb Z_2$.

Variables are $x_0, \dots, x_{n-1}$; in $\varphi \perp \psi$ the first variables carry $\varphi$.
-/
import QuadFormsKB.Literature.Watson1963.TwoAdic
import QuadFormsKB.Literature.Watson1963.Primitive

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Watson1963

open Siegel DefiniteForms QuadFormsKB.Hanke2011Structure QuadFormsKB.Cassels

section Aux

/-- An element of $\mathbb Z_2$ divisible by $2$ reduces to $0$ in $\mathbb F_2$. -/
theorem toZMod_eq_zero_of_two_dvd {x : ℤ_[2]} (h : (2 : ℤ_[2]) ∣ x) : PadicInt.toZMod x = 0 := by
  obtain ⟨y, rfl⟩ := h
  rw [map_mul]
  have h2 : PadicInt.toZMod (2 : ℤ_[2]) = (2 : ZMod 2) := map_ofNat _ 2
  rw [h2]
  have : (2 : ZMod 2) = 0 := by decide
  rw [this, zero_mul]

/-- An element of $\mathbb Z_2$ with nonzero reduction modulo $2$ is a unit. -/
theorem isUnit_of_toZMod_ne_zero {x : ℤ_[2]} (h : PadicInt.toZMod x ≠ 0) : IsUnit x := by
  by_contra hnu
  exact h (toZMod_eq_zero_of_two_dvd (two_dvd_of_not_isUnit_padic hnu))

/-- An odd integer is a unit of $\mathbb Z_2$. -/
theorem isUnit_intCast_two {d : ℤ} (hd : ¬ (2 : ℤ) ∣ d) : IsUnit ((d : ℤ) : ℤ_[2]) := by
  apply isUnit_of_toZMod_ne_zero
  rw [map_intCast]
  intro h
  exact hd ((ZMod.intCast_zmod_eq_zero_iff_dvd d 2).1 h)

/-- The Hessian matrix of a form reduced modulo $2$, as a matrix over $\mathbb F_2$. -/
def hessMod2 {n : ℕ} (Q : QuadForm ℤ_[2] n) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  Q.hessian.map PadicInt.toZMod

theorem hessian_isSymm' {R : Type*} [CommRing R] {n : ℕ} (Q : QuadForm R n) : Q.hessianᵀ = Q.hessian := by
  unfold QuadForm.hessian
  rw [Matrix.transpose_add, Matrix.transpose_transpose, add_comm]

/-- Orthogonality of two column families: if $X^{\mathsf T} A Y = 0$ then $(X\vec z_1)^{\mathsf T}A(Y\vec z_2)=0$. -/
theorem cross_eq_zero {R : Type*} [CommRing R] {n a b : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (X : Matrix (Fin n) (Fin a) R) (Y : Matrix (Fin n) (Fin b) R) (h : Xᵀ * A * Y = 0)
    (z₁ : Fin a → R) (z₂ : Fin b → R) : (X *ᵥ z₁) ⬝ᵥ (A *ᵥ (Y *ᵥ z₂)) = 0 := by
  have key : ∀ v : Fin n → R, z₁ ⬝ᵥ (Xᵀ *ᵥ v) = (X *ᵥ z₁) ⬝ᵥ v := fun v => by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  rw [← key, mulVec_mulVec, mulVec_mulVec, h]
  simp

/-- The reduction mod $2$ of a rank-$\le 2$ correction: $\operatorname{rank}$ of the product with a width-$2$ factor. -/
theorem rank_mul_two_le {m : ℕ} (X : Matrix (Fin m) (Fin 2) (ZMod 2)) {o : ℕ} (Y : Matrix (Fin 2) (Fin o) (ZMod 2)) :
    (X * Y).rank ≤ 2 := by
  refine (Matrix.rank_mul_le_left X Y).trans ?_
  simpa using Matrix.rank_le_width X

theorem rank_add_le' {m : ℕ} (X Y : Matrix (Fin m) (Fin m) (ZMod 2)) : (X + Y).rank ≤ X.rank + Y.rank := by
  unfold Matrix.rank
  have h1 : LinearMap.range (X + Y).mulVecLin ≤ LinearMap.range X.mulVecLin ⊔ LinearMap.range Y.mulVecLin := by
    rw [Matrix.mulVecLin_add]
    exact LinearMap.range_add_le _ _
  refine (Submodule.finrank_mono h1).trans ?_
  exact Submodule.finrank_add_le_finrank_add_finrank _ _

/-- **Unimodular Gram matrix on $2k$ vectors (Schur complement induction).** Let $Q$ be a form over $\mathbb Z_2$ in
$n$ variables whose Hessian reduced modulo $2$ has rank $r$ with $2k \le r + 1$. Then there is an $n \times 2k$ matrix
$H$ over $\mathbb Z_2$ such that the Gram matrix $H^{\mathsf T} H_Q H$ has unit determinant. *Proof:* induction on $k$.
A nonzero entry $\bar H_{ij}$ gives two basis vectors with Gram matrix $G$ of determinant
$\equiv -\bar H_{ij}^2 \not\equiv 0 \pmod 2$ (the diagonal of the Hessian is even); put $C = 1 - PG^{-1}P^{\mathsf T}H_Q$.
Then $C^{\mathsf T}H_QC = H_Q - H_QPG^{-1}P^{\mathsf T}H_Q$ has mod-$2$ rank at least $r - 2$, and the induction
hypothesis for $Q \circ C$ gives $H'$; the columns of $CH'$ and $P$ are orthogonal. The slack $+1$ makes the parity of
the rank of an alternating form automatic. -/
theorem exists_gram_unit (k : ℕ) : ∀ {n : ℕ} (Q : QuadForm ℤ_[2] n),
    2 * k ≤ (hessMod2 Q).rank + 1 →
    ∃ H : Matrix (Fin n) (Fin (2 * k)) ℤ_[2], IsUnit (Hᵀ * Q.hessian * H).det := by
  induction k with
  | zero =>
    intro n Q _
    have : IsEmpty (Fin (2 * 0)) := ⟨fun x => by have := x.2; omega⟩
    exact ⟨0, by rw [Matrix.det_isEmpty]; exact isUnit_one⟩
  | succ k ih =>
    intro n Q hrk
    have hAs : Q.hessianᵀ = Q.hessian := hessian_isSymm' Q
    have hne : hessMod2 Q ≠ 0 := by
      intro h0
      have : (hessMod2 Q).rank = 0 := by rw [h0]; exact Matrix.rank_zero
      omega
    obtain ⟨i, j, hij⟩ : ∃ i j, PadicInt.toZMod (Q.hessian i j) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hne
      ext i j
      exact hcon i j
    let P : Matrix (Fin n) (Fin 2) ℤ_[2] :=
      Matrix.of fun a c => ((![Pi.single i 1, Pi.single j 1] : Fin 2 → Fin n → ℤ_[2]) c) a
    have hc0 : (fun l => P l 0) = Pi.single i 1 := by ext l; simp [P]
    have hc1 : (fun l => P l 1) = Pi.single j 1 := by ext l; simp [P]
    obtain ⟨G, hGdef⟩ : ∃ G : Matrix (Fin 2) (Fin 2) ℤ_[2], G = Pᵀ * Q.hessian * P := ⟨_, rfl⟩
    have hGentry : ∀ a b : Fin 2, G a b = (fun l => P l a) ⬝ᵥ (Q.hessian *ᵥ fun l => P l b) := fun a b => by
      rw [hGdef]; exact QuadForm.transpose_mul_mul_apply _ P a b
    have hG00 : G 0 0 = 2 * Q.eval (Pi.single i 1) := by
      rw [hGentry, hc0, QuadForm.dotProduct_hessian_self]
    have hG11 : G 1 1 = 2 * Q.eval (Pi.single j 1) := by
      rw [hGentry, hc1, QuadForm.dotProduct_hessian_self]
    have hG01 : G 0 1 = Q.hessian i j := by
      rw [hGentry, hc0, hc1, mulVec_single_one, single_one_dotProduct]; rfl
    have hG10 : G 1 0 = Q.hessian i j := by
      rw [hGentry, hc0, hc1, mulVec_single_one, single_one_dotProduct]
      exact congrFun (congrFun hAs i) j
    have hGu : IsUnit G.det := by
      apply isUnit_of_toZMod_ne_zero
      have hz : PadicInt.toZMod (G 0 0) = 0 := toZMod_eq_zero_of_two_dvd ⟨Q.eval (Pi.single i 1), hG00⟩
      rw [Matrix.det_fin_two, map_sub, map_mul, map_mul, hz, zero_mul, zero_sub, hG01, hG10]
      exact neg_ne_zero.2 (mul_ne_zero hij hij)
    have hGs : Gᵀ = G := by
      rw [hGdef]; simp [Matrix.transpose_mul, hAs, Matrix.mul_assoc]
    have hGis : (G⁻¹)ᵀ = G⁻¹ := by rw [Matrix.transpose_nonsing_inv, hGs]
    have hGG : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G hGu
    obtain ⟨C, hC⟩ : ∃ C : Matrix (Fin n) (Fin n) ℤ_[2], C = 1 - P * G⁻¹ * Pᵀ * Q.hessian := ⟨_, rfl⟩
    have hb : Pᵀ * Q.hessian * C = 0 := by
      have : Pᵀ * Q.hessian * C = Pᵀ * Q.hessian - (Pᵀ * Q.hessian * P) * G⁻¹ * (Pᵀ * Q.hessian) := by
        rw [hC]; simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
      rw [this, ← hGdef, hGG, Matrix.one_mul, sub_self]
    have hb' : Cᵀ * Q.hessian * P = 0 := by
      have := congrArg Matrix.transpose hb
      simpa [Matrix.transpose_mul, hAs, Matrix.mul_assoc] using this
    have hCt : Cᵀ = 1 - Q.hessian * P * G⁻¹ * Pᵀ := by
      rw [hC]; simp [Matrix.transpose_mul, Matrix.transpose_sub, hAs, hGis, Matrix.mul_assoc]
    have hdecomp : Cᵀ * Q.hessian * C = Q.hessian - (Q.hessian * P) * G⁻¹ * (Pᵀ * Q.hessian) := by
      calc Cᵀ * Q.hessian * C = Cᵀ * Q.hessian * (1 - P * G⁻¹ * Pᵀ * Q.hessian) := by rw [← hC]
        _ = Cᵀ * Q.hessian - (Cᵀ * Q.hessian * P) * G⁻¹ * (Pᵀ * Q.hessian) := by
          simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
        _ = Cᵀ * Q.hessian := by rw [hb', Matrix.zero_mul, Matrix.zero_mul, sub_zero]
        _ = _ := by rw [hCt]; simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
    have hAeq : Q.hessian = (Q.compMat C).hessian + (Q.hessian * P) * (G⁻¹ * (Pᵀ * Q.hessian)) := by
      rw [QuadForm.hessian_compMat, hdecomp]
      simp only [Matrix.mul_assoc]; abel
    have hrank : (hessMod2 Q).rank ≤ (hessMod2 (Q.compMat C)).rank + 2 := by
      have h1 : hessMod2 Q = hessMod2 (Q.compMat C) +
          ((Q.hessian * P).map PadicInt.toZMod) * ((G⁻¹ * (Pᵀ * Q.hessian)).map PadicInt.toZMod) := by
        unfold hessMod2
        have := congrArg (fun M => M.map PadicInt.toZMod) hAeq
        simpa [Matrix.map_add, Matrix.map_mul] using this
      have h2 := rank_add_le' (hessMod2 (Q.compMat C))
        (((Q.hessian * P).map PadicInt.toZMod) * ((G⁻¹ * (Pᵀ * Q.hessian)).map PadicInt.toZMod))
      rw [← h1] at h2
      have h3 := rank_mul_two_le ((Q.hessian * P).map PadicInt.toZMod)
        ((G⁻¹ * (Pᵀ * Q.hessian)).map PadicInt.toZMod)
      omega
    obtain ⟨H', hH'⟩ := ih (Q.compMat C) (by omega)
    let T : Matrix (Fin n) (Fin (2 * k + 2)) ℤ_[2] :=
      Matrix.of fun r c => Fin.append (fun a => (C * H') r a) (fun b => P r b) c
    have hT : ∀ z, T *ᵥ z = (C * H') *ᵥ (fun a => z (Fin.castAdd 2 a)) +
        P *ᵥ (fun b => z (Fin.natAdd (2 * k) b)) := by
      intro z; ext r
      simp [T, mulVec, dotProduct, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
    have hcr : (C * H')ᵀ * Q.hessian * P = 0 := by
      calc (C * H')ᵀ * Q.hessian * P = H'ᵀ * (Cᵀ * Q.hessian * P) := by
            simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = 0 := by rw [hb', Matrix.mul_zero]
    have hQT : Q.compMat T = QuadForm.orthSum (Q.compMat (C * H')) (Q.compMat P) := by
      refine QuadForm.eq_of_eval_eq fun z => ?_
      rw [QuadForm.eval_compMat, hT]
      show _ = (QuadForm.orthSum (Q.compMat (C * H')) (Q.compMat P)).evalIn ℤ_[2] z
      rw [QuadForm.evalIn_orthSum]
      show _ = (Q.compMat (C * H')).eval _ + (Q.compMat P).eval _
      rw [QuadForm.eval_compMat, QuadForm.eval_compMat]
      have hpol := QuadForm.eval_polar Q ((C * H') *ᵥ (fun a => z (Fin.castAdd 2 a)))
        (P *ᵥ (fun b => z (Fin.natAdd (2 * k) b)))
      have hcross := cross_eq_zero Q.hessian (C * H') P hcr (fun a => z (Fin.castAdd 2 a))
        (fun b => z (Fin.natAdd (2 * k) b))
      linear_combination hpol + hcross
    refine ⟨T, ?_⟩
    have h1 : (Tᵀ * Q.hessian * T).det =
        ((Q.compMat (C * H')).hessian).det * ((Q.compMat P).hessian).det := by
      rw [← QuadForm.hessian_compMat, hQT, hessian_orthSum_det]
    rw [h1]
    refine IsUnit.mul ?_ ?_
    · have : (Q.compMat (C * H')).hessian = H'ᵀ * (Q.compMat C).hessian * H' := by
        rw [← QuadForm.compMat_mul, QuadForm.hessian_compMat]
      rw [this]; exact hH'
    · rw [QuadForm.hessian_compMat, ← hGdef]; exact hGu

end Aux

/-! ### The rank bound -/

section RankBound

/-- **$r_2(f) \le \operatorname{rank}(\bar H_f) + 1$.** The radical $R_2(f)$ (`radModP 2 f`) is the kernel of
$\bar f$ on $\ker \bar H_f$ (for $x \in \ker \bar H_f$ one has $\bar f(x + z) = \bar f(x) + \bar f(z)$ for $z \in
\ker\bar H_f$, so $\bar f$ is $\mathbb F_2$-linear there, as $c^2 = c$ in $\mathbb F_2$); a linear form on $\ker \bar H_f$
has kernel of codimension at most $1$. Hence $\dim R_2(f) \ge (n - \operatorname{rank}\bar H_f) - 1$.
Arguments: the form `f`. -/
theorem rankModP_two_le_rank_add_one {n : ℕ} (f : QuadForm ℤ n) :
    rankModP 2 f ≤ (f.hessian.map (algebraMap ℤ (ZMod 2))).rank + 1 := by
  classical
  have hMs : (f.hessian.map (algebraMap ℤ (ZMod 2)))ᵀ = f.hessian.map (algebraMap ℤ (ZMod 2)) := by
    rw [← Matrix.transpose_map, hessian_isSymm']
  let Krn : Submodule (ZMod 2) (Fin n → ZMod 2) :=
    LinearMap.ker (f.hessian.map (algebraMap ℤ (ZMod 2))).mulVecLin
  have hK : ∀ x ∈ Krn, ∀ z, x ⬝ᵥ (f.hessian.map (algebraMap ℤ (ZMod 2)) *ᵥ z) = 0 := by
    intro x hx z
    have hx' : f.hessian.map (algebraMap ℤ (ZMod 2)) *ᵥ x = 0 := hx
    have e : x ᵥ* (f.hessian.map (algebraMap ℤ (ZMod 2)))ᵀ = f.hessian.map (algebraMap ℤ (ZMod 2)) *ᵥ x :=
      Matrix.vecMul_transpose _ x
    rw [hMs] at e
    rw [Matrix.dotProduct_mulVec, e, hx', zero_dotProduct]
  let L : Krn →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun x => f.evalIn (ZMod 2) x.1
      map_add' := fun x y => by
        show f.evalIn (ZMod 2) (x.1 + y.1) = f.evalIn (ZMod 2) x.1 + f.evalIn (ZMod 2) y.1
        rw [evalIn_add', hK x.1 x.2 y.1]
        simp
      map_smul' := fun c x => by
        show f.evalIn (ZMod 2) (c • x.1) = c • f.evalIn (ZMod 2) x.1
        rw [evalIn_smul', smul_eq_mul, ZMod.pow_card c] }
  have hle : (LinearMap.ker L).map Krn.subtype ≤ radModP 2 f := by
    rintro x ⟨y, hy, rfl⟩
    exact ⟨hy, hK y.1 y.2⟩
  have h1 := LinearMap.finrank_range_add_finrank_ker (f.hessian.map (algebraMap ℤ (ZMod 2))).mulVecLin
  have h2 := LinearMap.finrank_range_add_finrank_ker L
  have h3 : Module.finrank (ZMod 2) (LinearMap.range L) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range L)
    simpa using this
  have h4 := Submodule.finrank_map_subtype_eq Krn (LinearMap.ker L)
  have h5 := Submodule.finrank_mono hle
  have h6 := rankModP_add_finrank 2 f
  simp only [Module.finrank_fin_fun] at h1
  have h7 : (f.hessian.map (algebraMap ℤ (ZMod 2))).rank =
      Module.finrank (ZMod 2) (LinearMap.range (f.hessian.map (algebraMap ℤ (ZMod 2))).mulVecLin) := rfl
  have h8 : Module.finrank (ZMod 2) Krn = Module.finrank (ZMod 2) (LinearMap.ker (f.hessian.map (algebraMap ℤ (ZMod 2))).mulVecLin) := rfl
  omega

end RankBound

/-! ### Even unimodular summands -/

section Summands

/-- **Even unimodular representation at $2$.** Let $f$ be an integral form in $n$ variables with
$2k \le \operatorname{rank}\bar H_f + 1$ ($\bar H_f$ the Hessian modulo $2$; in particular this holds when
$\operatorname{rank}\bar H_f \ge 2k$). Then over $\mathbb Z_2$, $f$ represents a form $U$ in $2k$ variables whose
Hessian determinant is a unit (an even unimodular form): $f(H\vec y) = U(\vec y)$ for an $n \times 2k$ matrix $H$ over
$\mathbb Z_2$. Arguments: the form `f` and the rank hypothesis `h`. -/
theorem exists_even_unimodular_rep {n k : ℕ} (f : QuadForm ℤ n)
    (h : 2 * k ≤ (f.hessian.map (algebraMap ℤ (ZMod 2))).rank + 1) :
    ∃ (U : QuadForm ℤ_[2] (2 * k)) (H : Matrix (Fin n) (Fin (2 * k)) ℤ_[2]),
      IsUnit U.hessian.det ∧ ∀ y, (f.map (Int.castRingHom ℤ_[2])).eval (H *ᵥ y) = U.eval y := by
  have hr : hessMod2 (f.map (Int.castRingHom ℤ_[2])) = f.hessian.map (algebraMap ℤ (ZMod 2)) := by
    unfold hessMod2
    rw [QuadForm.hessian_map, Matrix.map_map]
    ext i j
    simp
  obtain ⟨H, hH⟩ := exists_gram_unit k (f.map (Int.castRingHom ℤ_[2])) (hr ▸ h)
  refine ⟨(f.map (Int.castRingHom ℤ_[2])).compMat H, H, ?_, fun y => (QuadForm.eval_compMat _ _ _).symm⟩
  rw [QuadForm.hessian_compMat]; exact hH

/-- **Even unimodular summand at $2$** (with the dimension equation as a cast). Under the hypothesis
$2k \le \operatorname{rank}\bar H_f + 1$ of `exists_even_unimodular_rep`, over $\mathbb Z_2$
$f \cong U \perp \psi$ with $U$ in $2k$ variables with unit Hessian determinant and $\psi$ in $m = n - 2k$ variables;
`hm ▸` transports $U \perp \psi$ from $\mathrm{Fin}(2k+m)$ to $\mathrm{Fin}\,n$. -/
theorem exists_even_unimodular_summand_of_rank {n k : ℕ} (f : QuadForm ℤ n)
    (h : 2 * k ≤ (f.hessian.map (algebraMap ℤ (ZMod 2))).rank + 1) :
    ∃ (m : ℕ) (hm : 2 * k + m = n) (U : QuadForm ℤ_[2] (2 * k)) (ψ : QuadForm ℤ_[2] m),
      IsUnit U.hessian.det ∧
        IsometricGL (f.map (Int.castRingHom ℤ_[2])) (hm ▸ QuadForm.orthSum U ψ) := by
  obtain ⟨U, H, hU, hH⟩ := exists_even_unimodular_rep f h
  obtain ⟨m, hm, ψ, hiso⟩ := exists_isometricGL_orthSum_of_rep_padic 2 H hH hU
  exact ⟨m, hm, U, ψ, hU, hiso⟩

/-- **Even unimodular summand at $2$, on $\mathrm{Fin}(2k+m)$.** For $f$ in $2k + m$ variables with
$2k \le \operatorname{rank}\bar H_f + 1$: $f \cong U \perp \psi$ over $\mathbb Z_2$, $U$ in $2k$ variables with unit
Hessian determinant, $\psi$ in $m$ variables (no cast). -/
theorem exists_even_unimodular_summand_of_rank_fin {k m : ℕ} (f : QuadForm ℤ (2 * k + m))
    (h : 2 * k ≤ (f.hessian.map (algebraMap ℤ (ZMod 2))).rank + 1) :
    ∃ (U : QuadForm ℤ_[2] (2 * k)) (ψ : QuadForm ℤ_[2] m), IsUnit U.hessian.det ∧
      IsometricGL (f.map (Int.castRingHom ℤ_[2])) (QuadForm.orthSum U ψ) := by
  obtain ⟨m', hm, U, ψ, hU, hiso⟩ := exists_even_unimodular_summand_of_rank f h
  obtain rfl : m' = m := by omega
  exact ⟨U, ψ, hU, hiso⟩

/-- **A Watson-minimal form in $n \ge 12$ variables has an even unimodular summand of rank $6$ over $\mathbb Z_2$**
(as a representation). *Proof:* $n \le 2 r_2(f)$ (`IsWatsonMinimal.le_two_mul_rankModP`) gives $r_2(f) \ge 6$, hence
$\operatorname{rank}\bar H_f \ge 5$ (`rankModP_two_le_rank_add_one`) and $2\cdot 3 \le 5 + 1$. Arguments: `hf`
positive definiteness, `hmin` minimality, `hn : 12 ≤ n`. -/
theorem IsWatsonMinimal.exists_even_unimodular_rep_six {n : ℕ} {f : QuadForm ℤ n} (hf : IntQF.PosDef f)
    (hmin : IsWatsonMinimal f) (hn : 12 ≤ n) :
    ∃ (U : QuadForm ℤ_[2] (2 * 3)) (H : Matrix (Fin n) (Fin (2 * 3)) ℤ_[2]),
      IsUnit U.hessian.det ∧ ∀ y, (f.map (Int.castRingHom ℤ_[2])).eval (H *ᵥ y) = U.eval y := by
  have h1 := IsWatsonMinimal.le_two_mul_rankModP 2 hf hmin
  have h2 := rankModP_two_le_rank_add_one f
  exact exists_even_unimodular_rep f (by omega)

/-- **A Watson-minimal form in $n \ge 12$ variables has an even unimodular summand of rank $6$ over $\mathbb Z_2$:**
$f \cong U \perp \psi$ over $\mathbb Z_2$ with $U$ in $6$ variables and unit Hessian determinant, $\psi$ in $n - 6$
variables (`hm ▸` casts from $\mathrm{Fin}(6 + m)$ to $\mathrm{Fin}\,n$). -/
theorem IsWatsonMinimal.exists_even_unimodular_summand_six {n : ℕ} {f : QuadForm ℤ n} (hf : IntQF.PosDef f)
    (hmin : IsWatsonMinimal f) (hn : 12 ≤ n) :
    ∃ (m : ℕ) (hm : 2 * 3 + m = n) (U : QuadForm ℤ_[2] (2 * 3)) (ψ : QuadForm ℤ_[2] m),
      IsUnit U.hessian.det ∧
        IsometricGL (f.map (Int.castRingHom ℤ_[2])) (hm ▸ QuadForm.orthSum U ψ) := by
  have h1 := IsWatsonMinimal.le_two_mul_rankModP 2 hf hmin
  have h2 := rankModP_two_le_rank_add_one f
  exact exists_even_unimodular_summand_of_rank f (by omega)

/-- **Splitting of an even unimodular quaternary at $2$** (Watson 1963, proof of Lemma 9 (i) / §9). Let $f$ be a
positive definite Watson-minimal form in $4 + m$ variables with $m \ge 8$, and $g$ a quaternary integral form whose
Hessian determinant is odd (so $g$ is even unimodular at $2$). Then over $\mathbb Z_2$, $f \cong g \perp \psi_p$ for a
form $\psi_p$ in $m$ variables. *Proof:* $f_2$ represents an even unimodular form $U$ of rank $6$
(`IsWatsonMinimal.exists_even_unimodular_rep_six`); $U$ represents $g_2$ (`exists_rep_of_even_unimodular`, complement of
rank $2$); compose the representations and split off $g_2$ (`exists_isometricGL_orthSum_of_rep_padic`). -/
theorem quaternary_split_two {m : ℕ} {f : QuadForm ℤ (4 + m)} (hf : IntQF.PosDef f) (hmin : IsWatsonMinimal f)
    (hm : 8 ≤ m) {g : QuadForm ℤ 4} (hodd : ¬ (2 : ℤ) ∣ g.hessian.det) :
    ∃ ψp : QuadForm ℤ_[2] m,
      IsometricGL (f.map (Int.castRingHom ℤ_[2])) (QuadForm.orthSum (g.map (Int.castRingHom ℤ_[2])) ψp) := by
  obtain ⟨U, H₂, hU, hH₂⟩ := IsWatsonMinimal.exists_even_unimodular_rep_six hf hmin (by omega)
  have hg : IsUnit (g.map (Int.castRingHom ℤ_[2])).hessian.det := by
    have h : (g.hessian.map (Int.castRingHom ℤ_[2])).det = ((g.hessian.det : ℤ) : ℤ_[2]) :=
      (RingHom.map_det (Int.castRingHom ℤ_[2]) g.hessian).symm
    rw [QuadForm.hessian_map, h]
    exact isUnit_intCast_two hodd
  obtain ⟨H₁, hH₁⟩ := exists_rep_of_even_unimodular (j := 2) (m := 0) U (g.map (Int.castRingHom ℤ_[2])) hU hg
  have hrep : ∀ y, (f.map (Int.castRingHom ℤ_[2])).eval ((H₂ * H₁) *ᵥ y) =
      (g.map (Int.castRingHom ℤ_[2])).eval y := fun y => by
    rw [← mulVec_mulVec, hH₂, hH₁]
  obtain ⟨m', hm', ψp, hiso⟩ := exists_isometricGL_orthSum_of_rep_padic 2 (H₂ * H₁) hrep hg
  obtain rfl : m' = m := by omega
  exact ⟨ψp, hiso⟩

end Summands

end QuadFormsKB.Watson1963
