/-
# Isomorphic even Clifford orders come from similar forms (Voight, Proposition 22.4.12)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021, 22.4.8, Proposition 22.4.12 and
Main Theorem 22.4.1 (key `voight2021`).

**Statement** (`similar_of_nonempty_clf0_equiv`). Let $R$ be a domain and let $Q, Q'$ be ternary
quadratic forms over $R$ with nonzero half-discriminants
$N = 4abc + uvw - au^2 - bv^2 - cw^2$, $N'$ (`ternaryDisc`). If
$\operatorname{Clf}^0(Q) \cong \operatorname{Clf}^0(Q')$ as $R$-algebras, then $Q$ and $Q'$ are similar:
$Q'(\vec x) = d\,Q(P\vec x)$ for some $P \in \mathrm{GL}_3(R)$ and $d \in R^\times$. Together with the
converse (`nonempty_clf0_equiv_of_similar`, Theorem 22.2.11) this is the clause
`EvenCliffordCorrespondence.nonempty_equiv_iff_similar` of Main Theorem 22.4.1
(`nonempty_clf0_equiv_iff_similar`), proved here for every domain (Voight assumes $R$ is a principal ideal domain).

**Proof** (Voight's inverse map $O \mapsto N\operatorname{nrd}^\sharp(O)$ of 22.4.8, written without
leaving $O$).
* An $R$-algebra isomorphism $\varphi$ preserves the reduced trace and norm
  (`EvenClf.trd_map`, `EvenClf.nrd_map`): both are the coefficients of the reduced characteristic
  polynomial $x^2 - \operatorname{trd}(x)x + \operatorname{nrd}(x)$, which are unique for $x \notin R$
  over a domain, and $\varphi$ fixes $R$.
* The commutators $xy - yx$ span exactly $N(O^\sharp)^0 = R\,Ni^\sharp + R\,Nj^\sharp + R\,Nk^\sharp$
  (Voight (22.4.13)): $xy - yx$ is the combination of $Ni^\sharp, Nj^\sharp, Nk^\sharp$ with the
  cross product of the vector parts of $x$ and $y$ as coefficients (`EvenClf.commutator_eq_dualVec`).
  So $\varphi$ maps this lattice to the corresponding lattice of $\operatorname{Clf}^0(Q')$, by a
  matrix $P$ (`EvenClf.map_dualVec`).
* The trilinear form $m(x, y, z) = \operatorname{trd}((xy - yx)z)$ is $N$ times the determinant of
  the vector parts (`EvenClf.trd_commutator_mul`, Voight 15.4.2 and (22.3.20)); comparing
  $m(i, j, k)$ on both sides gives $N = N'D$, and the same for $\varphi^{-1}$ gives $N' = N D'$, so
  $D D' = 1$: the discriminant is preserved up to a unit and $\det P = D^2$ is a unit.
* By (22.4.14), $N\,Q(\vec x) = \operatorname{nrd}(\sum x_p\,Ne_p^\sharp)
  = \operatorname{nrd}(\varphi(\cdots)) = N'\,Q'(P\vec x)$, so $D\,Q(\vec x) = Q'(P\vec x)$.

Indices are 0-based (Voight's $x, y, z$ are $x_0, x_1, x_2$).
-/
import QuadFormsKB.Literature.Voight.QuaternionOrder

set_option linter.unusedSectionVars false

universe u
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

open Matrix

namespace QuadFormsKB.Voight

namespace EvenClf

variable {R : Type*} [CommRing R] {a b c u v w : R}

/-! ## Commutators and the trilinear form -/

/-- The cross product of the vector parts $(x_i, x_j, x_k)$ and $(y_i, y_j, y_k)$. -/
def cross (x y : EvenClf R a b c u v w) : Fin 3 → R :=
  ![x.j * y.k - x.k * y.j, x.k * y.i - x.i * y.k, x.i * y.j - x.j * y.i]

/-- The determinant of the vector parts of $x, y, z$ (rows $(x_i, x_j, x_k)$, …). -/
def vdet (x y z : EvenClf R a b c u v w) : R :=
  x.i * (y.j * z.k - y.k * z.j) - x.j * (y.i * z.k - y.k * z.i) + x.k * (y.i * z.j - y.j * z.i)

/-- **Commutators lie in $N(O^\sharp)^0$** (Voight (22.4.13)): $xy - yx$ is the combination of
$Ni^\sharp = jk - kj$, $Nj^\sharp = ki - ik$, $Nk^\sharp = ij - ji$ whose coefficients are the cross
product of the vector parts of $x$ and $y$. -/
theorem commutator_eq_dualVec (x y : EvenClf R a b c u v w) :
    x * y - y * x = dualVec (cross x y 0) (cross x y 1) (cross x y 2) := by
  obtain ⟨h1, h2, h3⟩ := dual_eq (R := R) (a := a) (b := b) (c := c) (u := u) (v := v) (w := w)
  simp only [dualVec, h1, h2, h3, cross]
  ext <;> simp <;> ring

/-- **The alternating trilinear form** (Voight 15.4.2 and (22.3.20)):
$\operatorname{trd}((xy - yx)z) = N \det(\text{vector parts of } x, y, z)$. -/
@[kb "voight2021" "15.4.2, p. 254; (22.3.20), p. 362"]
theorem trd_commutator_mul (x y z : EvenClf R a b c u v w) :
    trd ((x * y - y * x) * z) = halfDisc a b c u v w * vdet x y z := by
  simp only [trd, vdet, halfDisc, mul_re, mul_i, mul_j, mul_k, sub_re, sub_i, sub_j, sub_k]
  ring

theorem dualVec_add_smul (x y z : R) (p q : Fin 3 → R) (r : Fin 3 → R) :
    x • dualVec (a := a) (b := b) (c := c) (u := u) (v := v) (w := w) (p 0) (p 1) (p 2) +
      y • dualVec (q 0) (q 1) (q 2) + z • dualVec (r 0) (r 1) (r 2) =
      dualVec (x * p 0 + y * q 0 + z * r 0) (x * p 1 + y * q 1 + z * r 1)
        (x * p 2 + y * q 2 + z * r 2) := by
  simp only [dualVec]; ext <;> simp <;> ring

/-! ## Algebra maps preserve the reduced trace and norm -/

section Domain

variable [IsDomain R] {a' b' c' u' v' w' : R}

theorem algebraMap_injective : Function.Injective (algebraMap R (EvenClf R a b c u v w)) :=
  fun r s h => by simpa using congrArg EvenClf.re h

/-- **Isomorphisms preserve the reduced trace and norm** (over a domain): for an $R$-algebra
isomorphism $\varphi$ between even Clifford algebras, $\operatorname{trd}(\varphi x) = \operatorname{trd}(x)$
and $\operatorname{nrd}(\varphi x) = \operatorname{nrd}(x)$ (the reduced characteristic polynomial is
determined by the algebra structure: the uniqueness of the standard involution, Voight Corollary 3.4.4,
p. 40; proved here directly from the table). -/
theorem trd_nrd_map (φ : EvenClf R a b c u v w ≃ₐ[R] EvenClf R a' b' c' u' v' w')
    (x : EvenClf R a b c u v w) : trd (φ x) = trd x ∧ nrd (φ x) = nrd x := by
  set y := φ x with hy
  have h1 := sq_sub_trd_mul_add_nrd y
  have h2 : y * y - trd x • y + algebraMap R _ (nrd x) = 0 := by
    have := congrArg φ (sq_sub_trd_mul_add_nrd x)
    simpa [map_sub, map_add, map_mul, map_smul, AlgEquiv.commutes, ← hy] using this
  have hd : (trd y - trd x) • y = algebraMap R _ (nrd y - nrd x) := by
    have := congrArg₂ (· - ·) h1 h2
    simp only [sub_self] at this
    rw [map_sub, sub_smul]
    linear_combination (norm := skip) -this
    ext <;> simp <;> ring
  have htr : trd y = trd x := by
    by_contra hne
    have ht : trd y - trd x ≠ 0 := sub_ne_zero.2 hne
    have hi : y.i = 0 := by
      have := congrArg EvenClf.i hd; simp at this
      exact this.resolve_left ht
    have hj : y.j = 0 := by
      have := congrArg EvenClf.j hd; simp at this
      exact this.resolve_left ht
    have hk : y.k = 0 := by
      have := congrArg EvenClf.k hd; simp at this
      exact this.resolve_left ht
    have hys : y = algebraMap R _ y.re := by ext <;> simp [hi, hj, hk]
    have hx : x = algebraMap R _ y.re := by
      apply φ.injective; rw [AlgEquiv.commutes, ← hy]; exact hys
    apply hne
    rw [hys, hx]; simp [trd]
  refine ⟨htr, ?_⟩
  rw [htr, sub_self, zero_smul] at hd
  have := algebraMap_injective (a := a') (b := b') (c := c') (u := u') (v := v') (w := w')
    (hd.symm.trans (map_zero _).symm)
  exact sub_eq_zero.1 this

/-! ## The matrix of an isomorphism on $N(O^\sharp)^0$ -/

variable (φ : EvenClf R a b c u v w ≃ₐ[R] EvenClf R a' b' c' u' v' w')

/-- The matrix $P$ of $\varphi$ on the lattice $N(O^\sharp)^0$ in the bases
$(Ni^\sharp, Nj^\sharp, Nk^\sharp)$: its columns are the cross products of the vector parts of
$(\varphi j, \varphi k)$, $(\varphi k, \varphi i)$, $(\varphi i, \varphi j)$. -/
def dualMat : Matrix (Fin 3) (Fin 3) R :=
  Matrix.of fun p q => (![cross (φ ej) (φ ek), cross (φ ek) (φ ei), cross (φ ei) (φ ej)] q) p

/-- The determinant $D$ of the vector parts of $\varphi i, \varphi j, \varphi k$. -/
def isoDet : R := vdet (φ ei) (φ ej) (φ ek)

/-- **$\varphi$ on $N(O^\sharp)^0$** (Voight 22.4.8): $\varphi(\sum_p x_p\,Ne_p^\sharp) =
\sum_p (P\vec x)_p\,Ne_p'^\sharp$. -/
theorem map_dualVec (x : Fin 3 → R) :
    φ (dualVec (x 0) (x 1) (x 2)) =
      dualVec ((dualMat φ *ᵥ x) 0) ((dualMat φ *ᵥ x) 1) ((dualMat φ *ᵥ x) 2) := by
  have hI : φ dualI = dualVec (cross (φ ej) (φ ek) 0) (cross (φ ej) (φ ek) 1)
      (cross (φ ej) (φ ek) 2) := by
    rw [dualI, map_sub, map_mul, map_mul, commutator_eq_dualVec]
  have hJ : φ dualJ = dualVec (cross (φ ek) (φ ei) 0) (cross (φ ek) (φ ei) 1)
      (cross (φ ek) (φ ei) 2) := by
    rw [dualJ, map_sub, map_mul, map_mul, commutator_eq_dualVec]
  have hK : φ dualK = dualVec (cross (φ ei) (φ ej) 0) (cross (φ ei) (φ ej) 1)
      (cross (φ ei) (φ ej) 2) := by
    rw [dualK, map_sub, map_mul, map_mul, commutator_eq_dualVec]
  rw [dualVec, map_add, map_add, map_smul, map_smul, map_smul, hI, hJ, hK, dualVec_add_smul]
  simp only [dualMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  congr 1 <;> ring

/-- $\det P = D^2$ ($P$ is the cofactor matrix of the matrix of vector parts). -/
theorem det_dualMat : (dualMat φ).det = isoDet φ ^ 2 := by
  simp only [dualMat, isoDet, vdet, cross, Matrix.det_fin_three, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring

/-- **The discriminant transforms by $D$**: $N = N' D$. -/
theorem halfDisc_eq_mul_isoDet :
    halfDisc a b c u v w = halfDisc a' b' c' u' v' w' * isoDet φ := by
  have h := (trd_nrd_map φ ((ei * ej - ej * ei) * ek)).1
  rw [map_mul, map_sub, map_mul, map_mul, trd_commutator_mul, trd_commutator_mul] at h
  rw [isoDet, h]
  simp [vdet, ei, ej, ek]

/-- **$D$ is a unit** when $N \ne 0$: applying `halfDisc_eq_mul_isoDet` to $\varphi$ and
$\varphi^{-1}$ gives $N = N D' D$. -/
theorem isUnit_isoDet (hN : halfDisc a b c u v w ≠ 0) : IsUnit (isoDet φ) := by
  have h1 := halfDisc_eq_mul_isoDet φ
  have h2 := halfDisc_eq_mul_isoDet φ.symm
  have : halfDisc a b c u v w * (isoDet φ.symm * isoDet φ - 1) = 0 := by
    linear_combination -(isoDet φ) * h2 - h1
  have h3 := (mul_eq_zero.1 this).resolve_left hN
  have h4 := sub_eq_zero.1 h3
  exact ⟨⟨isoDet φ, isoDet φ.symm, by rw [mul_comm]; exact h4, h4⟩, rfl⟩

/-- **The ternary forms are related by $P$ and $D$** (Voight (22.4.14)):
$D\,Q(\vec x) = Q'(P\vec x)$, where $Q = ax_0^2 + bx_1^2 + cx_2^2 + ux_1x_2 + vx_0x_2 + wx_0x_1$. -/
theorem isoDet_mul_form (hN' : halfDisc a' b' c' u' v' w' ≠ 0) (x : Fin 3 → R) :
    isoDet φ * (a * x 0 ^ 2 + b * x 1 ^ 2 + c * x 2 ^ 2 + u * x 1 * x 2 + v * x 0 * x 2
      + w * x 0 * x 1) =
      a' * (dualMat φ *ᵥ x) 0 ^ 2 + b' * (dualMat φ *ᵥ x) 1 ^ 2 + c' * (dualMat φ *ᵥ x) 2 ^ 2
        + u' * (dualMat φ *ᵥ x) 1 * (dualMat φ *ᵥ x) 2
        + v' * (dualMat φ *ᵥ x) 0 * (dualMat φ *ᵥ x) 2
        + w' * (dualMat φ *ᵥ x) 0 * (dualMat φ *ᵥ x) 1 := by
  have h := (trd_nrd_map φ (dualVec (x 0) (x 1) (x 2))).2
  rw [map_dualVec, nrd_dualVec, nrd_dualVec, halfDisc_eq_mul_isoDet φ] at h
  refine mul_left_cancel₀ hN' ?_
  linear_combination -h

end Domain

end EvenClf

/-! ## Proposition 22.4.12 for $\operatorname{Clf}^0(Q)$ -/

section Clf0

variable {R : Type*} [CommRing R] [IsDomain R]

theorem eval_smul_ring (r : R) (Q : QuadForm R 3) (x : Fin 3 → R) :
    (r • Q).eval x = r * Q.eval x := by
  simp only [QuadForm.evalIn, QuadForm.smul_coeff, Matrix.smul_apply, smul_eq_mul,
    Algebra.algebraMap_self, RingHom.id_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

/-- **Isomorphic even Clifford orders have associated discriminants** (Voight Lemma 22.3.19 and
Main Theorem 22.4.1, "discriminant-preserving"): if
$\operatorname{Clf}^0(Q) \cong \operatorname{Clf}^0(Q')$ and $N \ne 0$, then $N' = \varepsilon N$ for a unit
$\varepsilon$, i.e. $NR = N'R$. -/
@[kb "voight2021" "Main Theorem 22.4.1, p. 364; Lemma 22.3.19, p. 362"]
theorem associated_ternaryDisc_of_equiv {Q Q' : QuadForm R 3} (φ : Clf0 Q ≃ₐ[R] Clf0 Q')
    (hN : ternaryDisc Q ≠ 0) : Associated (ternaryDisc Q') (ternaryDisc Q) := by
  obtain ⟨d, hd⟩ := EvenClf.isUnit_isoDet φ hN
  exact ⟨d, by rw [hd, ternaryDisc, ternaryDisc, EvenClf.halfDisc_eq_mul_isoDet φ]⟩

/-- **Proposition 22.4.12, second half (Voight 2021)**: over a domain $R$, if $Q, Q'$ are ternary
forms with nonzero half-discriminants and $\operatorname{Clf}^0(Q) \cong \operatorname{Clf}^0(Q')$ as
$R$-algebras, then $Q$ and $Q'$ are similar: $Q'(\vec y) = d\,Q(P'\vec y)$ with $d \in R^\times$ and
$P' \in \mathrm{GL}_3(R)$. Voight proves it for a principal ideal domain $R$; the proof here works over every domain. -/
@[kb "voight2021" "Proposition 22.4.12, p. 366; 22.4.8, p. 366"]
theorem similar_of_nonempty_clf0_equiv {Q Q' : QuadForm R 3} (hN : ternaryDisc Q ≠ 0)
    (hN' : ternaryDisc Q' ≠ 0) (h : Nonempty (Clf0 Q ≃ₐ[R] Clf0 Q')) : Similar Q Q' := by
  obtain ⟨φ⟩ := h
  obtain ⟨d, hd⟩ := EvenClf.isUnit_isoDet φ hN
  set P := EvenClf.dualMat φ
  have hP : IsUnit P.det := by
    rw [EvenClf.det_dualMat, ← hd]; exact (Units.isUnit d).pow 2
  refine ⟨d, P⁻¹, (Matrix.isUnit_nonsing_inv_det_iff).2 hP, fun y => ?_⟩
  have key := EvenClf.isoDet_mul_form φ hN' (P⁻¹ *ᵥ y)
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hP, Matrix.one_mulVec] at key
  show (((d : R) • Q).eval (P⁻¹ *ᵥ y)) = Q'.eval y
  rw [eval_smul_ring, eval_ternary, eval_ternary, hd]
  exact key

/-- **The correspondence on isomorphism classes** (Voight Main Theorem 22.4.1, clause
`EvenCliffordCorrespondence.nonempty_equiv_iff_similar`), for every domain $R$: for ternary forms
$Q, Q'$ with nonzero half-discriminants,
$\operatorname{Clf}^0(Q) \cong \operatorname{Clf}^0(Q')$ as $R$-algebras if and only if $Q$ and $Q'$ are
similar. -/
@[kb "voight2021" "Main Theorem 22.4.1, p. 364; Proposition 22.4.12, p. 366; Theorem 22.2.11, p. 357"]
theorem nonempty_clf0_equiv_iff_similar {Q Q' : QuadForm R 3} (hN : ternaryDisc Q ≠ 0)
    (hN' : ternaryDisc Q' ≠ 0) : Nonempty (Clf0 Q ≃ₐ[R] Clf0 Q') ↔ Similar Q Q' :=
  ⟨similar_of_nonempty_clf0_equiv hN hN', nonempty_clf0_equiv_of_similar⟩

end Clf0

/-- **Main Theorem 22.4.1 reduces to Proposition 22.4.4** (Voight 2021): for a domain $R$ whose fraction field $F$
has $2 \ne 0$, the correspondence `EvenCliffordCorrespondence R F` holds as soon as every quaternion $R$-order is
isomorphic to the even Clifford algebra of a nondegenerate ternary form (Proposition 22.4.4, the clause
`exists_clf0`). The other two clauses are proved: `isQuaternionOrder_clf0` (Corollary 22.3.22) and
`nonempty_clf0_equiv_iff_similar` (Proposition 22.4.12 and Theorem 22.2.11). -/
@[kb "voight2021" "Main Theorem 22.4.1, p. 364; Proposition 22.4.4, p. 364"]
theorem evenCliffordCorrespondence_iff_exists_clf0 {R : Type u} {F : Type*} [CommRing R] [IsDomain R]
    [Field F] [Algebra R F] [IsFractionRing R F] (h2 : (2 : F) ≠ 0) :
    EvenCliffordCorrespondence R F ↔
      ∀ (O : Type u) [Ring O] [Algebra R O], IsQuaternionOrder R F O →
        ∃ Q : QuadForm R 3, ternaryDisc Q ≠ 0 ∧ Nonempty (O ≃ₐ[R] Clf0 Q) :=
  ⟨fun h => h.exists_clf0, fun h =>
    ⟨fun Q hQ => isQuaternionOrder_clf0 h2 Q hQ, h, fun _ _ hQ hQ' => nonempty_clf0_equiv_iff_similar hQ hQ'⟩⟩

end QuadFormsKB.Voight
