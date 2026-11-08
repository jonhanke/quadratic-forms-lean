/-
# Watson (1963): unimodular splitting and even unimodular forms over $\mathbb Z_p$

G. L. Watson, *The class-number of a positive quadratic form*, Proc. London Math. Soc. (3) 13 (1963) 549–576.

Local foundations (including the dyadic prime $p = 2$) for the remaining local inputs of the Watson formalization.

**Proved here.**
* `exists_isometricGL_orthSum_of_rep` (over any principal ideal domain $R$) and
  `exists_isometricGL_orthSum_of_rep_padic` ($R = \mathbb Z_p$, any prime $p$, including $2$): if a form $Q$ in $n$
  variables over $R$ represents a form $\varphi$ in $v$ variables, $Q(H\vec y) = \varphi(\vec y)$, and the Hessian
  determinant of $\varphi$ is a unit, then $Q \cong \varphi \perp \psi$ over $R$ ($\mathrm{GL}_n(R)$-equivalence) for a
  form $\psi$ in $m = n - v$ variables. This is the local analogue of `exists_intEquiv_orthSum_of_rep` (`Split.lean`).
* `isometricGL_two_of_unimodular_sq`: even unimodular forms over $\mathbb Z_2$ whose Hessian determinants differ by a
  unit square are isometric (variant of `isometricGL_two_of_unimodular`).
* `even_unimodular_classification`, `isometricGL_hyp_iff`, `isometricGL_hypA_iff`, `isometricGL_hyp_iff_dvd_eight`
  (**classification of even unimodular forms over $\mathbb Z_2$**): a form $Q$ over $\mathbb Z_2$ in $2k$ variables with
  unit Hessian determinant $d$ is isometric to $H^k$ (`hyp k`, $H = x_0x_1$) if $(-1)^k d$ is a square in $\mathbb Z_2$
  (equivalently $\equiv 1 \bmod 8$), and otherwise to $H^{k-1} \perp A$ (`hypA k`, $A = x_0^2 + x_0x_1 + x_1^2$); the two
  cases are mutually exclusive. The proof reuses Cassels' dyadic classification (`dyadic_EU_equiv`) and the mod $4$
  restriction `hessian_det_mod_four`.
* `exists_even_unimodular_summand` and `exists_rep_of_even_unimodular`: an even unimodular form over $\mathbb Z_2$ of
  rank $2j + 2(m+1)$ splits off (hence represents) every even unimodular form of rank $2j$, the complement being
  $H^{m+1}$ or $H^m \perp A$ (chosen by the square class of the determinant; needs complement rank $\ge 2$).
  Proved directly from the determinant criterion, without item 1.

Variables are $x_0, \dots, x_{n-1}$; in $\varphi \perp \psi$ the first $v$ variables carry $\varphi$.
-/
import QuadFormsKB.Literature.Cassels.Ch9.EvenUnimodularTwo
import QuadFormsKB.Literature.Hanke2011Structure.DyadicExistence
import QuadFormsKB.LocalDensity.FormDensitySelf

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Watson1963

open Siegel

section Split

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

/-- **Splitting of a unimodular sublattice, linear-algebra core, over a principal ideal domain $R$.** Let $A$ be an
$n \times n$ matrix and $H$ an $n \times v$ matrix over $R$ such that $H^{\mathsf T} A H$ has unit determinant. Then
there are $m$ with $v + m = n$ and an $n \times m$ matrix $K$ over $R$ whose columns lie in the $A$-orthogonal
complement of the columns of $H$ ($(H\vec y)^{\mathsf T} A (K\vec c) = 0$), such that every vector of $R^n$ is
$H\vec y + K\vec c$. -/
theorem exists_complement_of_unimodular_pid {n v : ℕ} (A : Matrix (Fin n) (Fin n) R) (H : Matrix (Fin n) (Fin v) R)
    (hB : IsUnit (Hᵀ * A * H).det) :
    ∃ (m : ℕ) (_ : v + m = n) (K : Matrix (Fin n) (Fin m) R),
      (∀ (y : Fin v → R) (c : Fin m → R), (H *ᵥ y) ⬝ᵥ (A *ᵥ (K *ᵥ c)) = 0) ∧
      ∀ z : Fin n → R, ∃ (y : Fin v → R) (c : Fin m → R), z = H *ᵥ y + K *ᵥ c := by
  set B := Hᵀ * A * H with hBdef
  set L : Matrix (Fin v) (Fin n) R := B⁻¹ * (Hᵀ * A) with hL
  have hBB : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv _ hB
  have hBB' : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul _ hB
  have hLH : L * H = 1 := by
    have : L * H = B⁻¹ * B := by
      rw [hL, hBdef]; simp only [Matrix.mul_assoc]
    rw [this, hBB']
  have hBL : B * L = Hᵀ * A := by
    rw [hL, ← Matrix.mul_assoc, hBB, Matrix.one_mul]
  let Kr : Submodule R (Fin n → R) := LinearMap.ker (Matrix.mulVecLin L)
  let b := Module.finBasis R Kr
  have hmem : ∀ k : Fin n → R, k ∈ Kr ↔ L *ᵥ k = 0 := fun k => by simp [Kr]
  let e : (Fin n → R) ≃ₗ[R] (Fin v → R) × Kr :=
    { toFun := fun z => (L *ᵥ z, ⟨z - H *ᵥ (L *ᵥ z), by
        rw [hmem, mulVec_sub, mulVec_mulVec, hLH, one_mulVec, sub_self]⟩)
      map_add' := fun z w => by
        apply Prod.ext
        · simp [mulVec_add]
        · apply Subtype.ext
          simp [mulVec_add]; abel
      map_smul' := fun r z => by
        apply Prod.ext
        · show L *ᵥ (r • z) = r • (L *ᵥ z)
          rw [mulVec_smul]
        · apply Subtype.ext
          show r • z - H *ᵥ (L *ᵥ (r • z)) = r • (z - H *ᵥ (L *ᵥ z))
          rw [mulVec_smul, mulVec_smul, smul_sub]
      invFun := fun p => H *ᵥ p.1 + (p.2 : Fin n → R)
      left_inv := fun z => by simp
      right_inv := fun p => by
        have hk : L *ᵥ (p.2 : Fin n → R) = 0 := (hmem _).1 p.2.2
        apply Prod.ext
        · simp [mulVec_add, mulVec_mulVec, hLH, hk]
        · apply Subtype.ext
          simp [mulVec_add, mulVec_mulVec, hLH, hk] }
  have hrank : n = v + Module.finrank R Kr := by
    have := e.finrank_eq
    simpa [Module.finrank_prod] using this
  have hK : ∀ c, (Matrix.of fun (i : Fin n) (c : Fin (Module.finrank R Kr)) => ((b c : Kr) : Fin n → R) i) *ᵥ c
      = ((b.equivFun.symm c : Kr) : Fin n → R) := fun c => by
    ext i
    simp [mulVec, dotProduct, Module.Basis.equivFun_symm_apply, Finset.sum_apply, mul_comm]
  refine ⟨Module.finrank R Kr, hrank.symm,
    Matrix.of fun i c => ((b c : Kr) : Fin n → R) i, ?_, ?_⟩
  · intro y c
    rw [hK]
    have hk : L *ᵥ ((b.equivFun.symm c : Kr) : Fin n → R) = 0 := (hmem _).1 (b.equivFun.symm c).2
    have h0 : Hᵀ *ᵥ (A *ᵥ ((b.equivFun.symm c : Kr) : Fin n → R)) = 0 := by
      rw [mulVec_mulVec, ← hBL, ← mulVec_mulVec, hk, mulVec_zero]
    rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, h0, zero_dotProduct]
  · intro z
    refine ⟨(e z).1, b.equivFun (e z).2, ?_⟩
    have hz : z = H *ᵥ (e z).1 + ((e z).2 : Fin n → R) := (e.symm_apply_apply z).symm
    rw [hK, LinearEquiv.symm_apply_apply]
    exact hz

/-- **Unimodular splitting over a principal ideal domain $R$.** Let $Q$ be a form in $n$ variables over $R$ and
$\varphi$ a form in $v$ variables over $R$ whose Hessian determinant is a unit of $R$. If $Q$ represents $\varphi$,
that is $Q(H\vec y) = \varphi(\vec y)$ for an $n \times v$ matrix $H$ over $R$, then
$Q \cong \varphi \perp \psi$ over $R$ (`IsometricGL`) for some form $\psi$ in $m = n - v$ variables. The cast `hm ▸`
transports $\varphi \perp \psi$ from $\mathrm{Fin}(v+m)$ to $\mathrm{Fin}\, n$. Arguments: the matrix `H` with
`hH` ($Q(H\vec y) = \varphi(\vec y)$) and the unit hypothesis `hφ`. -/
theorem exists_isometricGL_orthSum_of_rep {n v : ℕ} {Q : QuadForm R n} {φ : QuadForm R v}
    (H : Matrix (Fin n) (Fin v) R) (hH : ∀ y, Q.eval (H *ᵥ y) = φ.eval y)
    (hφ : IsUnit φ.hessian.det) :
    ∃ (m : ℕ) (hm : v + m = n) (ψ : QuadForm R m), IsometricGL Q (hm ▸ QuadForm.orthSum φ ψ) := by
  have hhess : φ.hessian = Hᵀ * Q.hessian * H := by
    have : Q.compMat H = φ := QuadForm.eq_of_eval_eq (fun y => by rw [QuadForm.eval_compMat, hH])
    rw [← this, QuadForm.hessian_compMat]
  rw [hhess] at hφ
  obtain ⟨m, hm, K, horth, hspan⟩ := exists_complement_of_unimodular_pid _ H hφ
  refine ⟨m, hm, Q.compMat K, ?_⟩
  subst hm
  let T : Matrix (Fin (v + m)) (Fin (v + m)) R :=
    Matrix.of fun i j => Fin.append (fun a => H i a) (fun b => K i b) j
  have hT : ∀ x, T *ᵥ x = H *ᵥ (fun a => x (Fin.castAdd m a)) + K *ᵥ (fun b => x (Fin.natAdd v b)) := by
    intro x; ext i
    simp [T, mulVec, dotProduct, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  have surj : ∀ z : Fin (v + m) → R, ∃ x, T *ᵥ x = z := by
    intro z
    obtain ⟨y, c, hz⟩ := hspan z
    refine ⟨Fin.append y c, ?_⟩
    rw [hT]
    simpa [Fin.append_left, Fin.append_right] using hz.symm
  choose S hS using surj
  let S' : Matrix (Fin (v + m)) (Fin (v + m)) R := Matrix.of fun i j => S (Pi.single j 1) i
  have hTS : T * S' = 1 := by
    ext i j
    have := congrFun (hS (Pi.single j 1)) i
    simp only [mulVec, dotProduct] at this
    simp only [Matrix.mul_apply, S', Matrix.of_apply, this, Matrix.one_apply, Pi.single_apply]
  have hST : S' * T = 1 := mul_eq_one_comm.mp hTS
  refine ⟨⟨T, S', hTS, hST⟩, fun x => ?_⟩
  show Q.eval (T *ᵥ x) = (QuadForm.orthSum φ (Q.compMat K)).eval x
  rw [hT]
  have hpol := QuadForm.eval_polar Q (H *ᵥ fun a => x (Fin.castAdd m a)) (K *ᵥ fun b => x (Fin.natAdd v b))
  rw [horth] at hpol
  show _ = (QuadForm.orthSum φ (Q.compMat K)).evalIn R x
  rw [QuadForm.evalIn_orthSum]
  show _ = φ.eval _ + (Q.compMat K).eval _
  rw [QuadForm.eval_compMat, ← hH]
  linear_combination hpol

end Split

/-- **Unimodular splitting over $\mathbb Z_p$, any prime $p$ (including $p = 2$).** If $Q$ over $\mathbb Z_p$
represents $\varphi$ ($Q(H\vec y) = \varphi(\vec y)$) and $\det H_\varphi \in \mathbb Z_p^\times$, then
$Q \cong \varphi \perp \psi$ over $\mathbb Z_p$ with $\psi$ in $m = n - v$ variables (`hm ▸` casts
$\mathrm{Fin}(v+m)$ to $\mathrm{Fin}\,n$). Specialization of `exists_isometricGL_orthSum_of_rep`, as
$\mathbb Z_p$ is a principal ideal domain. -/
theorem exists_isometricGL_orthSum_of_rep_padic (p : ℕ) [Fact p.Prime] {n v : ℕ} {Q : QuadForm ℤ_[p] n}
    {φ : QuadForm ℤ_[p] v} (H : Matrix (Fin n) (Fin v) ℤ_[p]) (hH : ∀ y, Q.eval (H *ᵥ y) = φ.eval y)
    (hφ : IsUnit φ.hessian.det) :
    ∃ (m : ℕ) (hm : v + m = n) (ψ : QuadForm ℤ_[p] m), IsometricGL Q (hm ▸ QuadForm.orthSum φ ψ) :=
  exists_isometricGL_orthSum_of_rep H hH hφ

/-! ### Even unimodular forms over $\mathbb Z_2$ -/

section EvenUnimodular

open QuadFormsKB.Hanke2011Structure QuadFormsKB.Cassels QuadFormsKB.Cassels.Ch9EvenUnimodularTwo

/-- **$k$ hyperbolic planes** $H^k$: the form $x_0x_1 + x_2x_3 + \cdots + x_{2k-2}x_{2k-1}$ in $2k$ variables
(the library's `hypSum`; $H = x_0x_1$ is `Hanke2011Structure.hypPlane`). Its Hessian determinant is $(-1)^k$
(`hypSum_hessian_det`). -/
abbrev hyp {R : Type*} [CommRing R] (k : ℕ) : QuadForm R (2 * k) := hypSum k

/-- **The binary form $A = x_0^2 + x_0x_1 + x_1^2$.** Its Hessian determinant is $3$ (`hessian_det_quadA`). -/
def quadA {R : Type*} [CommRing R] : QuadForm R 2 := Composition.bq 1 1 1

/-- **$H^{k-1} \perp A$**, in $2k$ variables: $x_0x_1 + \cdots + x_{2k-4}x_{2k-3} + (x_{2k-2}^2 + x_{2k-2}x_{2k-1} +
x_{2k-1}^2)$ for $k \ge 1$ (the index is $k$, the total rank is $2k$). For $k = 0$ there is no such form and the
value is the empty form (junk value, equal to `hyp 0`). Its Hessian determinant is $(-1)^{k-1}\cdot 3$
(`hessian_det_hypA`). -/
def hypA {R : Type*} [CommRing R] : (k : ℕ) → QuadForm R (2 * k)
  | 0 => hypSum 0
  | j + 1 => QuadForm.orthSum (hypSum j) quadA

/-- $\det H_A = 3$. -/
theorem hessian_det_quadA {R : Type*} [CommRing R] : (quadA (R := R)).hessian.det = 3 := by
  have := Composition.neg_det_bq (1 : R) 1 1
  unfold quadA
  linear_combination -this

/-- $\det H(H^{k-1} \perp A) = (-1)^{k-1} \cdot 3$, indexed as `hypA (j + 1)`: $(-1)^j \cdot 3$. -/
theorem hessian_det_hypA {R : Type*} [CommRing R] (j : ℕ) :
    (hypA (R := R) (j + 1)).hessian.det = (-1) ^ j * 3 := by
  show (QuadForm.orthSum (hypSum j) quadA).hessian.det = _
  rw [hessian_orthSum_det, hypSum_hessian_det, hessian_det_quadA]

/-- **Isometry changes the Hessian determinant by a unit square:** if $Q \cong Q'$ over a commutative ring $R$ then
$\det H_{Q'} = w^2 \det H_Q$ for a unit $w \in R$ (the determinant of the transformation). -/
theorem exists_hessian_det_of_isometricGL {R : Type*} [CommRing R] {n : ℕ} {Q Q' : QuadForm R n}
    (h : IsometricGL Q Q') : ∃ w : R, IsUnit w ∧ Q'.hessian.det = w ^ 2 * Q.hessian.det := by
  obtain ⟨g, hg⟩ := h
  have hc : Q.compMat g.val = Q' := QuadForm.eq_of_eval_eq (fun y => by rw [QuadForm.eval_compMat, hg])
  refine ⟨g.val.det, (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit, ?_⟩
  rw [← hc, QuadForm.hessian_compMat, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

/-- **A unit square times the determinant gives an isometry (even unimodular, $\mathbb Z_2$).** Variant of
`isometricGL_two_of_unimodular` (which needs equal determinants): if $Q, Q'$ over $\mathbb Z_2$ have unit Hessian
determinants and $\det H_{Q'} = s^2\det H_Q$ for a unit $s$, then $Q \cong Q'$ ($\mathrm{GL}_n(\mathbb Z_2)$).
Route: Cassels Ch. 8, Cor. to Lemma 4.1 (`dyadic_EU_equiv`) with `dyadicRel`. -/
theorem isometricGL_two_of_unimodular_sq {n : ℕ} (Q Q' : QuadForm ℤ_[2] n)
    (hQ : IsUnit Q.hessian.det) (hQ' : IsUnit Q'.hessian.det) {s : ℤ_[2]} (hs : IsUnit s)
    (hdet : Q'.hessian.det = s ^ 2 * Q.hessian.det) : IsometricGL Q Q' := by
  have hrel : dyadicRel (Q.hessian.map PadicInt.Coe.ringHom) (Q'.hessian.map PadicInt.Coe.ringHom) :=
    ⟨(s : ℚ_[2]), by rw [← PadicInt.norm_def]; exact PadicInt.isUnit_iff.1 hs, by
      rw [map_det_coe, map_det_coe, hdet]; simp⟩
  obtain ⟨T, hT⟩ := dyadic_EU_equiv n _ _ (hessian_dyadicEU Q hQ) (hessian_dyadicEU Q' hQ') hrel
  have hT' : T.val.transpose * Q.hessian * T.val = Q'.hessian := by
    apply Matrix.map_injective (f := PadicInt.Coe.ringHom) (fun a b h => PadicInt.ext h)
    calc (T.val.transpose * Q.hessian * T.val).map PadicInt.Coe.ringHom
        = (T.val.map PadicInt.Coe.ringHom)ᵀ * Q.hessian.map PadicInt.Coe.ringHom *
            T.val.map PadicInt.Coe.ringHom := by
          rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
      _ = _ := hT
  refine ⟨T, fun x => ?_⟩
  have h2 : (2 : ℤ_[2]) * Q.eval (T.val *ᵥ x) = 2 * Q'.eval x := by
    rw [two_mul_eval, two_mul_eval, ← hT', Matrix.mul_assoc, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec]
    have key : ∀ v : Fin n → ℤ_[2], x ⬝ᵥ (T.val.transpose *ᵥ v) = (T.val *ᵥ x) ⬝ᵥ v := fun v => by
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    exact (key _).symm
  exact mul_left_cancel₀ (by norm_num) h2

/-- The square of a unit of $\mathbb Z_2$ is $\equiv 1 \bmod 8$. -/
theorem eight_dvd_sq_sub_one {w : ℤ_[2]} (hw : IsUnit w) : (8 : ℤ_[2]) ∣ w ^ 2 - 1 := by
  obtain ⟨u₀, hu₀, t, ht⟩ := dyadic_exists_mod8 hw
  have hw' : w = u₀ + 8 * t := by linear_combination ht
  rcases hu₀ with rfl | rfl | rfl | rfl
  · exact ⟨2 * t + 8 * t ^ 2, by rw [hw']; push_cast; ring⟩
  · exact ⟨1 + 6 * t + 8 * t ^ 2, by rw [hw']; push_cast; ring⟩
  · exact ⟨3 + 10 * t + 8 * t ^ 2, by rw [hw']; push_cast; ring⟩
  · exact ⟨6 + 14 * t + 8 * t ^ 2, by rw [hw']; push_cast; ring⟩

/-- **Units of $\mathbb Z_2$ that are $\equiv 1 \bmod 4$:** such a unit $u$ is either a unit square, or $-3u$ is a
unit square (the classes $u \equiv 1$ and $u \equiv 5 \bmod 8$). -/
theorem unit_sq_or_neg_three_mul {u : ℤ_[2]} (h4 : (4 : ℤ_[2]) ∣ u - 1) :
    (∃ z : ℤ_[2], IsUnit z ∧ z ^ 2 = u) ∨ (∃ z : ℤ_[2], IsUnit z ∧ z ^ 2 = -3 * u) := by
  obtain ⟨c, hc⟩ := h4
  by_cases hcu : IsUnit c
  · obtain ⟨m, hm⟩ := Composition.two_dvd_sub_one_of_isUnit hcu
    right
    obtain ⟨z, hz, hzu⟩ := Composition.exists_sq_one_add_eight (-2 - 3 * m)
    refine ⟨z, hzu, ?_⟩
    rw [hz]
    have hu : u = 5 + 8 * m := by linear_combination hc + 4 * hm
    rw [hu]; ring
  · obtain ⟨e, he⟩ := two_dvd_of_not_isUnit_padic hcu
    left
    obtain ⟨z, hz, hzu⟩ := Composition.exists_sq_one_add_eight e
    refine ⟨z, hzu, ?_⟩
    rw [hz]
    linear_combination -hc - 4 * he

/-- For a unit $u \equiv 1 \bmod 4$ of $\mathbb Z_2$: $u$ is a square iff $u \equiv 1 \bmod 8$. -/
theorem isSquare_iff_dvd_eight {u : ℤ_[2]} (hu : IsUnit u) (h4 : (4 : ℤ_[2]) ∣ u - 1) :
    IsSquare u ↔ (8 : ℤ_[2]) ∣ u - 1 := by
  constructor
  · rintro ⟨r, rfl⟩
    have hr : IsUnit r := isUnit_of_mul_isUnit_left hu
    simpa [sq] using eight_dvd_sq_sub_one hr
  · rintro ⟨e, he⟩
    obtain ⟨z, hz, -⟩ := Composition.exists_sq_one_add_eight e
    exact ⟨z, by rw [← sq, hz]; linear_combination he⟩

/-- **Determinants of even unimodular forms** (variant with an explicit equation $n = 2k$ for the number of
variables): if $Q$ over $\mathbb Z_2$ has $n = 2k$ variables and unit Hessian determinant $d$, then
$(-1)^k d \equiv 1 \bmod 4$. -/
theorem four_dvd_neg_one_pow_mul_det_sub_one_of_eq {n k : ℕ} (hn : n = 2 * k) (Q : QuadForm ℤ_[2] n)
    (hQ : IsUnit Q.hessian.det) : (4 : ℤ_[2]) ∣ (-1) ^ k * Q.hessian.det - 1 := by
  have h := hessian_det_mod_four k Q.hessian ⟨Q.coeff, rfl⟩ (by simp [hn])
  have hsq : ((-1 : ℤ_[2]) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
  rcases h with h | ⟨c, hc⟩
  · exfalso
    exact dyadic_not_isUnit_of_two_dvd (dvd_trans (⟨2, by norm_num⟩ : (2 : ℤ_[2]) ∣ 4) h) hQ
  · exact ⟨(-1) ^ k * c, by linear_combination ((-1 : ℤ_[2]) ^ k) * hc + hsq⟩

/-- **Determinants of even unimodular forms:** if $Q$ over $\mathbb Z_2$ has $2k$ variables and unit Hessian
determinant $d$, then $(-1)^k d \equiv 1 \bmod 4$. -/
theorem four_dvd_neg_one_pow_mul_det_sub_one {k : ℕ} (Q : QuadForm ℤ_[2] (2 * k)) (hQ : IsUnit Q.hessian.det) :
    (4 : ℤ_[2]) ∣ (-1) ^ k * Q.hessian.det - 1 :=
  four_dvd_neg_one_pow_mul_det_sub_one_of_eq rfl Q hQ

theorem isUnit_neg_one_pow {k : ℕ} : IsUnit ((-1 : ℤ_[2]) ^ k) := (isUnit_one.neg).pow k

theorem neg_one_pow_mul_self {k : ℕ} : ((-1 : ℤ_[2]) ^ k) * (-1) ^ k = 1 := by
  rw [← mul_pow]; norm_num

/-- **Even unimodular forms of rank $2k$ over $\mathbb Z_2$ isometric to $H^k$.** For $Q$ over $\mathbb Z_2$ in $2k$
variables with unit Hessian determinant $d$ (an even unimodular lattice): $Q \cong H^k$ (`hyp k`) if and only if
$(-1)^k d$ is a square in $\mathbb Z_2$. -/
theorem isometricGL_hyp_iff {k : ℕ} (Q : QuadForm ℤ_[2] (2 * k)) (hQ : IsUnit Q.hessian.det) :
    IsometricGL Q (hyp k) ↔ IsSquare ((-1) ^ k * Q.hessian.det) := by
  constructor
  · intro h
    obtain ⟨w, hw, hd⟩ := exists_hessian_det_of_isometricGL h
    have hd' : ((-1 : ℤ_[2]) ^ k) = w ^ 2 * Q.hessian.det := (hypSum_hessian_det (R := ℤ_[2]) k).symm.trans hd
    exact ⟨w * Q.hessian.det, by rw [hd']; ring⟩
  · rintro ⟨t, ht⟩
    have htu : IsUnit t := isUnit_of_mul_isUnit_left (by rw [← ht]; exact isUnit_neg_one_pow.mul hQ)
    obtain ⟨t', htt'⟩ := htu.exists_right_inv
    have hd : Q.hessian.det = (-1) ^ k * (t * t) := by
      linear_combination ((-1 : ℤ_[2]) ^ k) * ht - Q.hessian.det * (neg_one_pow_mul_self (k := k))
    refine isometricGL_two_of_unimodular_sq Q (hyp k) hQ ?_ (s := t')
      (IsUnit.of_mul_eq_one t (by rw [mul_comm]; exact htt')) ?_
    · rw [show (hyp k : QuadForm ℤ_[2] (2 * k)).hessian.det = (-1) ^ k from hypSum_hessian_det k]
      exact isUnit_neg_one_pow
    · rw [show (hyp k : QuadForm ℤ_[2] (2 * k)).hessian.det = (-1) ^ k from hypSum_hessian_det k, hd]
      linear_combination (-((-1 : ℤ_[2]) ^ k) * (t * t' + 1)) * htt'

/-- **Even unimodular forms of rank $2(j+1)$ over $\mathbb Z_2$ isometric to $H^{j} \perp A$.** For $Q$ over
$\mathbb Z_2$ in $2(j+1)$ variables with unit Hessian determinant $d$: $Q \cong H^{j} \perp A$ (`hypA (j+1)`) if and
only if $(-1)^{j+1} d$ is *not* a square in $\mathbb Z_2$. -/
theorem isometricGL_hypA_iff {j : ℕ} (Q : QuadForm ℤ_[2] (2 * (j + 1))) (hQ : IsUnit Q.hessian.det) :
    IsometricGL Q (hypA (j + 1)) ↔ ¬ IsSquare ((-1) ^ (j + 1) * Q.hessian.det) := by
  have hA : IsUnit ((hypA (R := ℤ_[2]) (j + 1)).hessian.det) := by
    rw [hessian_det_hypA]; exact isUnit_neg_one_pow.mul dyadic_isUnit_three
  constructor
  · intro h ⟨t, ht⟩
    obtain ⟨w, hw, hd⟩ := exists_hessian_det_of_isometricGL h
    rw [hessian_det_hypA] at hd
    have htu : IsUnit t := isUnit_of_mul_isUnit_left (by rw [← ht]; exact isUnit_neg_one_pow.mul hQ)
    rw [pow_succ] at ht
    have h3 : (t * w) ^ 2 = -3 := by
      linear_combination (-w ^ 2) * ht + ((-1 : ℤ_[2]) ^ j) * hd - 3 * (neg_one_pow_mul_self (k := j))
    apply dyadic_neg_three_not_sq (s := ((t * w : ℤ_[2]) : ℚ_[2]))
    · rw [← PadicInt.norm_def]; exact PadicInt.isUnit_iff.1 (htu.mul hw)
    · rw [← PadicInt.coe_pow, h3]
      have : (((3 : ℤ_[2])) : ℚ_[2]) = 3 := by exact_mod_cast PadicInt.coe_natCast (p := 2) 3
      simp [this]
  · intro hns
    have h4 := four_dvd_neg_one_pow_mul_det_sub_one Q hQ
    rcases unit_sq_or_neg_three_mul h4 with ⟨z, -, hzu⟩ | ⟨z, hz, hzu⟩
    · exact absurd ⟨z, by rw [← hzu]; ring⟩ hns
    · obtain ⟨d', hdd'⟩ := hQ.exists_right_inv
      rw [pow_succ] at hzu
      refine isometricGL_two_of_unimodular_sq Q (hypA (j + 1)) hQ hA (s := z * d')
        (hz.mul (IsUnit.of_mul_eq_one Q.hessian.det (by rw [mul_comm]; exact hdd'))) ?_
      rw [hessian_det_hypA]
      linear_combination (-(d' ^ 2 * Q.hessian.det)) * hzu - 3 * (-1 : ℤ_[2]) ^ j * (Q.hessian.det * d' + 1) * hdd'

/-- **Classification of even unimodular forms over $\mathbb Z_2$ (Cassels Ch. 8 Cor. to Lemma 4.1; O'Meara 93:16).**
Let $Q$ be a form over $\mathbb Z_2$ in $2k$ variables whose Hessian determinant $d$ is a unit, that is, $Q$ is an even
unimodular lattice. Then exactly one of the following holds, according to the square class of $(-1)^k d$:
* $(-1)^k d$ is a square in $\mathbb Z_2$ (equivalently $\equiv 1 \bmod 8$) and $Q \cong H^k$ (`hyp k`);
* $(-1)^k d$ is not a square (equivalently $\equiv 5 \bmod 8$), $k \ge 1$ and $Q \cong H^{k-1} \perp A$ (`hypA k`).

(Here $H = x_0x_1$ and $A = x_0^2 + x_0x_1 + x_1^2$.) The two cases are distinguished by `isometricGL_hyp_iff` and
`isometricGL_hypA_iff`. Unconditional. -/
theorem even_unimodular_classification {k : ℕ} (Q : QuadForm ℤ_[2] (2 * k)) (hQ : IsUnit Q.hessian.det) :
    (IsSquare ((-1) ^ k * Q.hessian.det) ∧ IsometricGL Q (hyp k)) ∨
      (¬ IsSquare ((-1) ^ k * Q.hessian.det) ∧ 1 ≤ k ∧ IsometricGL Q (hypA k)) := by
  by_cases hs : IsSquare ((-1) ^ k * Q.hessian.det)
  · exact Or.inl ⟨hs, (isometricGL_hyp_iff Q hQ).2 hs⟩
  · refine Or.inr ⟨hs, ?_⟩
    cases k with
    | zero =>
      exfalso
      apply hs
      have : Q.hessian.det = 1 := by simp [Matrix.det_isEmpty]
      rw [this]; exact ⟨1, by norm_num⟩
    | succ j => exact ⟨Nat.succ_pos j, (isometricGL_hypA_iff Q hQ).2 hs⟩

/-- **Square class versus residue mod $8$:** for $Q$ as above, $Q \cong H^k$ if and only if
$(-1)^k \det H_Q \equiv 1 \bmod 8$ in $\mathbb Z_2$ (the other residue class allowed for even unimodular forms
being $5 \bmod 8$). -/
theorem isometricGL_hyp_iff_dvd_eight {k : ℕ} (Q : QuadForm ℤ_[2] (2 * k)) (hQ : IsUnit Q.hessian.det) :
    IsometricGL Q (hyp k) ↔ (8 : ℤ_[2]) ∣ (-1) ^ k * Q.hessian.det - 1 :=
  (isometricGL_hyp_iff Q hQ).trans
    (isSquare_iff_dvd_eight (isUnit_neg_one_pow.mul hQ) (four_dvd_neg_one_pow_mul_det_sub_one Q hQ))

end EvenUnimodular

/-! ### Even unimodular summands -/

section Summand

open QuadFormsKB.Hanke2011Structure QuadFormsKB.Cassels QuadFormsKB.Cassels.Ch9EvenUnimodularTwo

/-- Algebra for the case $\psi = H^{m+1}$ of `exists_even_unimodular_summand`. -/
theorem summand_alg_hyp {R : Type*} [CommRing R] (ε δ κ dφ dQ uQ' z : R) (hκ : κ = ε * δ) (hεε : ε * ε = 1)
    (hκκ : κ * κ = 1) (huQ : κ * dQ * uQ' = 1) (hz : z ^ 2 = ε * dφ * (κ * dQ)) :
    dφ * δ = (z * uQ') ^ 2 * dQ := by
  have hX : (dQ * uQ') ^ 2 = 1 := by
    linear_combination (κ * (dQ * uQ') + 1) * huQ - (dQ * uQ') ^ 2 * hκκ
  linear_combination (-(uQ' ^ 2 * dQ)) * hz - dφ * δ * hεε - dφ * ε * hκ - ε * κ * dφ * hX

/-- Algebra for the case $\psi = H^m \perp A$ of `exists_even_unimodular_summand`. -/
theorem summand_alg_hypA {R : Type*} [CommRing R] (ε μ κ dφ dQ uQ' z : R) (hκ : κ + ε * μ = 0)
    (hεε : ε * ε = 1) (hκκ : κ * κ = 1) (huQ : κ * dQ * uQ' = 1)
    (hz : z ^ 2 = -3 * (ε * dφ * (κ * dQ))) : dφ * (μ * 3) = (z * uQ') ^ 2 * dQ := by
  have hX : (dQ * uQ') ^ 2 = 1 := by
    linear_combination (κ * (dQ * uQ') + 1) * huQ - (dQ * uQ') ^ 2 * hκκ
  linear_combination (-(uQ' ^ 2 * dQ)) * hz + 3 * dφ * ε * hκ - 3 * dφ * μ * hεε + 3 * ε * κ * dφ * hX

/-- **An even unimodular form of rank $2j + 2(m+1)$ over $\mathbb Z_2$ splits off every even unimodular form
$\varphi$ of rank $2j$.** Let $Q$ be a form in $2j + 2(m+1)$ variables and $\varphi$ a form in $2j$ variables over
$\mathbb Z_2$, both with unit Hessian determinant. Then $Q \cong \varphi \perp \psi$ over $\mathbb Z_2$ for a form $\psi$
in $2(m+1) \ge 2$ variables with unit Hessian determinant (the first $2j$ variables carry $\varphi$). The complement
$\psi$ is $H^{m+1}$ or $H^m \perp A$, chosen to fix the square class of the determinant; this is where the rank
condition ($m + 1 \ge 1$, so that $H^m \perp A$ exists) is used. -/
theorem exists_even_unimodular_summand {j m : ℕ} (Q : QuadForm ℤ_[2] (2 * j + 2 * (m + 1)))
    (φ : QuadForm ℤ_[2] (2 * j)) (hQ : IsUnit Q.hessian.det) (hφ : IsUnit φ.hessian.det) :
    ∃ ψ : QuadForm ℤ_[2] (2 * (m + 1)), IsUnit ψ.hessian.det ∧ IsometricGL Q (QuadForm.orthSum φ ψ) := by
  have h4Q := four_dvd_neg_one_pow_mul_det_sub_one_of_eq (n := 2 * j + 2 * (m + 1)) (k := j + (m + 1))
    (by ring) Q hQ
  have h4φ := four_dvd_neg_one_pow_mul_det_sub_one φ hφ
  set dQ := Q.hessian.det with hdQ
  set dφ := φ.hessian.det with hdφ
  set uQ : ℤ_[2] := (-1) ^ (j + (m + 1)) * dQ with huQdef
  set uφ : ℤ_[2] := (-1) ^ j * dφ with huφdef
  have huQ : IsUnit uQ := isUnit_neg_one_pow.mul hQ
  obtain ⟨uQ', huQ'⟩ := huQ.exists_right_inv
  have h4w : (4 : ℤ_[2]) ∣ uφ * uQ - 1 := by
    have : uφ * uQ - 1 = uφ * (uQ - 1) + (uφ - 1) := by ring
    rw [this]
    exact (h4Q.mul_left uφ).add h4φ
  have hεε : ((-1 : ℤ_[2]) ^ j) * (-1) ^ j = 1 := neg_one_pow_mul_self
  have hκκ : ((-1 : ℤ_[2]) ^ (j + (m + 1))) * (-1) ^ (j + (m + 1)) = 1 := neg_one_pow_mul_self
  have huQ'' : (-1 : ℤ_[2]) ^ (j + (m + 1)) * dQ * uQ' = 1 := huQ'
  rcases unit_sq_or_neg_three_mul h4w with ⟨z, hz, hzw⟩ | ⟨z, hz, hzw⟩
  · refine ⟨hyp (m + 1), ?_, ?_⟩
    · rw [show (hyp (m + 1) : QuadForm ℤ_[2] (2 * (m + 1))).hessian.det = (-1) ^ (m + 1) from
        hypSum_hessian_det (m + 1)]
      exact isUnit_neg_one_pow
    · refine isometricGL_two_of_unimodular_sq Q _ hQ ?_ (s := z * uQ') (hz.mul (IsUnit.of_mul_eq_one uQ
        (by rw [mul_comm]; exact huQ'))) ?_
      · rw [hessian_orthSum_det, show (hyp (m + 1) : QuadForm ℤ_[2] (2 * (m + 1))).hessian.det = (-1) ^ (m + 1) from
          hypSum_hessian_det (m + 1)]
        exact hφ.mul isUnit_neg_one_pow
      · rw [hessian_orthSum_det, show (hyp (m + 1) : QuadForm ℤ_[2] (2 * (m + 1))).hessian.det = (-1) ^ (m + 1) from
          hypSum_hessian_det (m + 1)]
        exact summand_alg_hyp ((-1) ^ j) ((-1) ^ (m + 1)) ((-1) ^ (j + (m + 1))) dφ dQ uQ' z (pow_add _ _ _)
          hεε hκκ huQ'' (by rw [hzw])
  · refine ⟨hypA (m + 1), ?_, ?_⟩
    · rw [hessian_det_hypA]; exact isUnit_neg_one_pow.mul dyadic_isUnit_three
    · refine isometricGL_two_of_unimodular_sq Q _ hQ ?_ (s := z * uQ') (hz.mul (IsUnit.of_mul_eq_one uQ
        (by rw [mul_comm]; exact huQ'))) ?_
      · rw [hessian_orthSum_det, hessian_det_hypA]
        exact hφ.mul (isUnit_neg_one_pow.mul dyadic_isUnit_three)
      · rw [hessian_orthSum_det, hessian_det_hypA]
        refine summand_alg_hypA ((-1) ^ j) ((-1) ^ m) ((-1) ^ (j + (m + 1))) dφ dQ uQ' z ?_ hεε hκκ huQ'' ?_
        · simp only [pow_add, pow_one]; ring
        · rw [hzw]

/-- **Representation of an even unimodular form by a larger one** (corollary of `exists_even_unimodular_summand`):
an even unimodular form $Q$ over $\mathbb Z_2$ of rank $2j + 2(m+1)$ represents every even unimodular form $\varphi$ of
rank $2j$: $Q(H\vec y) = \varphi(\vec y)$ for an $n \times 2j$ matrix $H$ over $\mathbb Z_2$ (indeed as an orthogonal
summand). -/
theorem exists_rep_of_even_unimodular {j m : ℕ} (Q : QuadForm ℤ_[2] (2 * j + 2 * (m + 1)))
    (φ : QuadForm ℤ_[2] (2 * j)) (hQ : IsUnit Q.hessian.det) (hφ : IsUnit φ.hessian.det) :
    ∃ H : Matrix (Fin (2 * j + 2 * (m + 1))) (Fin (2 * j)) ℤ_[2], ∀ y, Q.eval (H *ᵥ y) = φ.eval y := by
  obtain ⟨ψ, -, g, hg⟩ := exists_even_unimodular_summand Q φ hQ hφ
  let E : Matrix (Fin (2 * j + 2 * (m + 1))) (Fin (2 * j)) ℤ_[2] :=
    Matrix.of fun i c => Fin.append (Pi.single c (1 : ℤ_[2])) (0 : Fin (2 * (m + 1)) → ℤ_[2]) i
  have hE : ∀ y, E *ᵥ y = Fin.append y (0 : Fin (2 * (m + 1)) → ℤ_[2]) := by
    intro y
    ext i
    induction i using Fin.addCases with
    | left a =>
      simp [E, mulVec, dotProduct, Fin.append_left, Pi.single_apply]
    | right b =>
      simp [E, mulVec, dotProduct, Fin.append_right]
  refine ⟨g.val * E, fun y => ?_⟩
  rw [← mulVec_mulVec, hg, hE]
  show (QuadForm.orthSum φ ψ).evalIn ℤ_[2] _ = _
  rw [QuadForm.evalIn_orthSum]
  have h1 : ψ.evalIn ℤ_[2] (fun b => (Fin.append y (0 : Fin (2 * (m + 1)) → ℤ_[2])) (Fin.natAdd _ b)) = 0 := by
    have : (fun b => (Fin.append y (0 : Fin (2 * (m + 1)) → ℤ_[2])) (Fin.natAdd (2 * j) b)) = 0 := by
      ext b; simp [Fin.append_right]
    rw [this]
    show ψ.eval 0 = 0
    simp [QuadForm.eval, QuadForm.evalIn]
  rw [h1, add_zero]
  show φ.eval _ = φ.eval y
  congr 1
  ext a
  simp [Fin.append_left]

end Summand

end QuadFormsKB.Watson1963
