/-
# Cassels, Chapter 6, §11: the localization maps of the Witt group, Corollary 1 to Theorem 11.1

**Setting.** The Witt group $W(k)$ of Cassels, Ch. 2, §5, as built in `Ch2/WittGroup.lean`: regular spaces in
coordinates (`QSpace k`: a quadratic form on $k^n$ with nondegenerate polar form), their isometry classes `S k`, the
Grothendieck group `G k` and $W(k) = G(k)/\langle h\rangle$. For a field extension $K/F$ a regular space over $F$ is
extended to $K$ by viewing its coefficients in $K$ (`QSpace.extend`); this induces the localization map
$\lambda_K : W(F) \to W(K)$ (`localize`), which for $F = \mathbb Q$, $K = \mathbb Q_p$ is Cassels' $\lambda_p$
(p. 93): it maps $\langle a\rangle \in W(\mathbb Q)$ to $\langle a\rangle \in W(\mathbb Q_p)$ (`localize_unary`).

**Proves** (Cassels, *Rational Quadratic Forms*, Chapter 6, §11)
* the localization maps $\lambda_p : W(\mathbb Q) \to W(\mathbb Q_p)$, $p \le \infty$ (p. 93): `localize`,
  `localize_unary`;
* Corollary 1 to Theorem 11.1: an element of $W(\mathbb Q)$ in the kernel of all the $\lambda_p$ (including
  $p = \infty$) is $0$ (`localize_injective_everywhere`).

**Proof notes.** Cassels deduces Corollary 1 from Theorem 11.1 (the structure of $W(\mathbb Q)$), which is not
formalized. Here: every element of $W(\mathbb Q)$ is the class of a single regular space $X$ (Ch. 2, Lemma 5.3); if
$\lambda_v[X] = 0$ for every $v$, then $X$ is hyperbolic over every $\mathbb Q_v$ (Lemma 5.5 and Witt cancellation),
so $X$ is isometric over every $\mathbb Q_v$ to the hyperbolic space of the same dimension, hence over $\mathbb Q$ by
the Weak Hasse Principle (Theorem 1.2, `isometric_iff_everywhere`), and $[X] = 0$.
-/
import QuadFormsKB.Literature.Cassels.Ch2.WittGroup
import QuadFormsKB.Witt.Bridge
import QuadFormsKB.Equiv.Mathlib
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowski

namespace QuadFormsKB.Cassels.Ch6

open QuadraticMap Matrix

/-- A quadratic polynomial $x^{\mathsf T} M x$ in terms of the diagonal and the symmetrization of $M$. -/
theorem dot_mulVec_expand {R : Type*} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (x : Fin n → R) :
    x ⬝ᵥ (M *ᵥ x) = (∑ i, ∑ j, if i < j then x i * x j * (M i j + M j i) else 0) +
      ∑ i, x i * x i * M i i := by
  have e1 : x ⬝ᵥ (M *ᵥ x) = ∑ i, ∑ j, x i * M i j * x j := by
    simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  have e2 : ∀ i j, x i * M i j * x j = (if i < j then x i * M i j * x j else 0) +
      (if j < i then x i * M i j * x j else 0) + (if i = j then x i * M i j * x j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · subst h; simp
    · simp [h, h.ne', not_lt.mpr h.le]
  simp only [e1]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => e2 i j]
  simp only [Finset.sum_add_distrib]
  have h3 : (∑ i, ∑ j, if j < i then x i * M i j * x j else 0) =
      ∑ i, ∑ j, if i < j then x j * M j i * x i else 0 := by
    rw [Finset.sum_comm]
  have h4 : (∑ i, ∑ j, if i = j then x i * M i j * x j else 0) = ∑ i, x i * x i * M i i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Finset.sum_ite_eq]
    ring
  have h5 : (∑ i, ∑ j, if i < j then x i * x j * (M i j + M j i) else 0) =
      (∑ i, ∑ j, if i < j then x i * M i j * x j else 0) +
      ∑ i, ∑ j, if i < j then x j * M j i * x i else 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  rw [h3, h4, h5]

/-- Equal diagonals and symmetrizations give equal quadratic polynomials. -/
theorem dot_mulVec_eq_of_diag_symm {R : Type*} [CommRing R] {n : ℕ} (A B : Matrix (Fin n) (Fin n) R)
    (hd : ∀ i, A i i = B i i) (hs : ∀ i j, A i j + A j i = B i j + B j i) (x : Fin n → R) :
    x ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (B *ᵥ x) := by
  rw [dot_mulVec_expand, dot_mulVec_expand]
  simp only [hd, hs]

/-- Conversely, equal values on all vectors force equal diagonals and symmetrizations. -/
theorem diag_symm_of_dot_mulVec_eq {R : Type*} [CommRing R] {n : ℕ} (A B : Matrix (Fin n) (Fin n) R)
    (h : ∀ x : Fin n → R, x ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (B *ᵥ x)) :
    (∀ i, A i i = B i i) ∧ ∀ i j, A i j + A j i = B i j + B j i := by
  have hd : ∀ i, A i i = B i i := fun i => by simpa using h (Pi.single i 1)
  refine ⟨hd, fun i j => ?_⟩
  by_cases hij : i = j
  · subst hij; rw [hd]
  · have := h (Pi.single i 1 + Pi.single j 1)
    simp [dotProduct_add, add_dotProduct, mulVec_add] at this
    rw [hd i, hd j] at this
    linear_combination this

/-- Substituting $Px$ into $x \mapsto x^{\mathsf T} C x$. -/
theorem dot_comp {R : Type*} [CommRing R] {n : ℕ} (P C : Matrix (Fin n) (Fin n) R) (x : Fin n → R) :
    (P *ᵥ x) ⬝ᵥ (C *ᵥ (P *ᵥ x)) = x ⬝ᵥ ((Pᵀ * C * P) *ᵥ x) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec]
  conv_rhs => rw [dotProduct_mulVec, vecMul_transpose]

variable {F : Type*} [Field F] (K : Type*) [Field K] [Algebra F K]

/-- The coefficient matrix of `ofQuadraticForm Q` evaluates to $Q$ over $F$. -/
theorem dot_ofQF {n : ℕ} (Q : QuadraticForm F (Fin n → F)) (w : Fin n → F) :
    w ⬝ᵥ ((QuadForm.ofQuadraticForm Q).coeff *ᵥ w) = Q w := by
  have := QuadForm.evalIn_eq_dotProduct F (QuadForm.ofQuadraticForm Q) w
  rw [← QuadForm.eval_ofQuadraticForm Q w]
  simpa using this.symm

/-- An isometry over $F$ of Mathlib forms gives an identity of the coefficient polynomials over any $K \supseteq F$. -/
theorem evalIn_comp {n : ℕ} (Q R : QuadraticForm F (Fin n → F)) (P : Matrix (Fin n) (Fin n) F)
    (h : ∀ x, R (P *ᵥ x) = Q x) (x : Fin n → K) :
    (QuadForm.ofQuadraticForm R).evalIn K ((P.map (algebraMap F K)) *ᵥ x) =
      (QuadForm.ofQuadraticForm Q).evalIn K x := by
  rw [QuadForm.evalIn_eq_dotProduct, QuadForm.evalIn_eq_dotProduct]
  have hF : ∀ y : Fin n → F, y ⬝ᵥ ((Pᵀ * (QuadForm.ofQuadraticForm R).coeff * P) *ᵥ y) =
      y ⬝ᵥ ((QuadForm.ofQuadraticForm Q).coeff *ᵥ y) := by
    intro y
    rw [← dot_comp, dot_ofQF, dot_ofQF, h]
  obtain ⟨hd, hs⟩ := diag_symm_of_dot_mulVec_eq _ _ hF
  have key := dot_mulVec_eq_of_diag_symm ((Pᵀ * (QuadForm.ofQuadraticForm R).coeff * P).map (algebraMap F K))
    ((QuadForm.ofQuadraticForm Q).coeff.map (algebraMap F K)) (by simp [hd])
    (by intro i j; simp only [Matrix.map_apply, ← map_add, hs i j]) x
  rw [dot_comp, ← key]
  simp [Matrix.map_mul, Matrix.transpose_map]

/-- A regular Mathlib form gives a nondegenerate `QuadForm` (nonzero Hessian determinant). -/
theorem nondeg_ofQuadraticForm {n : ℕ} (Q : QuadraticForm F (Fin n → F))
    (h : (polarBilin Q).Nondegenerate) : (QuadForm.ofQuadraticForm Q).Nondegenerate := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv0
  rw [QSpace.reg_iff] at h
  apply h
  intro w
  rw [polar_comm]
  have := QuadForm.polar_eq_hessian F (QuadForm.ofQuadraticForm Q) w v
  have e : ∀ x, (QuadForm.ofQuadraticForm Q).evalIn F x = Q x := fun x => QuadForm.eval_ofQuadraticForm Q x
  rw [e, e, e] at this
  have e2 : (QuadForm.ofQuadraticForm Q).hessian.map (algebraMap F F) = (QuadForm.ofQuadraticForm Q).hessian := by
    ext i j; simp
  rw [e2, hv, dotProduct_zero] at this
  exact this

/-- **A regular space over $F$ viewed over an extension field $K$**: the same dimension and the form with the
coefficients mapped into $K$ (`QuadForm.toQuadraticFormIn` of the coefficient form `QuadForm.ofQuadraticForm`). -/
noncomputable def _root_.QuadFormsKB.Cassels.QSpace.extend (X : QSpace F) : QSpace K where
  dim := X.dim
  form := QuadForm.toQuadraticFormIn K (QuadForm.ofQuadraticForm X.form)
  reg := by
    exact QuadForm.nondegenerate_polarBilin_toQuadraticFormIn K (nondeg_ofQuadraticForm _ X.reg)

/-- Extension of scalars respects isometry. -/
theorem extend_equiv {X Y : QSpace F} (h : X.form.Equivalent Y.form) :
    (QSpace.extend K X).form.Equivalent (QSpace.extend K Y).form := by
  obtain ⟨m, Q, hQ⟩ := X
  obtain ⟨n, R, hR⟩ := Y
  have hd : m = n := S.dim_eq_of_equivalent h
  subst hd
  obtain ⟨e⟩ := h
  have h1 : (QuadForm.ofQuadraticForm R).IsometricIn K (QuadForm.ofQuadraticForm Q) := by
    refine ⟨(LinearMap.toMatrix' e.toLinearEquiv.toLinearMap).map (algebraMap F K), ?_, fun x => ?_⟩
    · have hP : IsUnit (LinearMap.toMatrix' e.toLinearEquiv.toLinearMap).det := by
        rw [LinearMap.det_toMatrix']
        exact LinearEquiv.isUnit_det' e.toLinearEquiv
      have := hP.map (algebraMap F K)
      rw [RingHom.map_det] at this
      exact this
    · refine evalIn_comp K Q R _ (fun y => ?_) x
      rw [LinearMap.toMatrix'_mulVec]
      exact e.map_app y
  rw [QuadForm.isometricIn_iff_equivalent] at h1
  exact h1

/-- Over $F$ itself the Mathlib form of `ofQuadraticForm Q` is $Q$. -/
theorem toQuadraticFormIn_self {n : ℕ} (Q : QuadraticForm F (Fin n → F)) :
    (QuadForm.ofQuadraticForm Q).toQuadraticFormIn F = Q := by
  ext x
  rw [QuadForm.toQuadraticFormIn_apply]
  exact QuadForm.eval_ofQuadraticForm Q x

/-- The coefficient form of an orthogonal sum is the orthogonal sum of the coefficient forms. -/
theorem ofQF_add (X Y : QSpace F) :
    QuadForm.ofQuadraticForm (QSpace.add X Y).form =
      QuadForm.orthSum (QuadForm.ofQuadraticForm X.form) (QuadForm.ofQuadraticForm Y.form) := by
  have : (QSpace.add X Y).form =
      (QuadForm.orthSum (QuadForm.ofQuadraticForm X.form) (QuadForm.ofQuadraticForm Y.form)).toQuadraticForm := by
    ext x
    rw [QuadForm.toQuadraticForm_apply]
    show _ = (QuadForm.orthSum _ _).evalIn F x
    rw [QuadForm.evalIn_orthSum]
    exact congrArg₂ _ (QuadForm.eval_ofQuadraticForm _ _).symm (QuadForm.eval_ofQuadraticForm _ _).symm
  rw [this, QuadForm.ofQuadraticForm_toQuadraticForm]

/-- Extension of scalars commutes with orthogonal sums up to isometry. -/
theorem extend_add_equiv (X Y : QSpace F) :
    ((QSpace.add X Y).extend K).form.Equivalent ((QSpace.extend K X).add (QSpace.extend K Y)).form := by
  have e1 : ((QSpace.add X Y).extend K).form.Equivalent
      ((QuadForm.toQuadraticFormIn K (QuadForm.ofQuadraticForm X.form)).prod
        (QuadForm.toQuadraticFormIn K (QuadForm.ofQuadraticForm Y.form))) := by
    show (QuadForm.toQuadraticFormIn K (QuadForm.ofQuadraticForm (QSpace.add X Y).form)).Equivalent _
    rw [ofQF_add]
    exact QuadForm.equivalent_toQuadraticFormIn_orthSum K _ _
  exact e1.trans (QSpace.add_equiv (QSpace.extend K X) (QSpace.extend K Y)).symm

/-- Extension of scalars preserves the $0$-dimensional space. -/
theorem extend_zero_equiv :
    ((QSpace.zero : QSpace F).extend K).form.Equivalent (QSpace.zero : QSpace K).form :=
  equiv_of_apply (V := Fin 0 → K) fun x => by
    have : x = 0 := Subsingleton.elim _ _
    subst this
    exact (QuadraticMap.map_zero ((QSpace.zero : QSpace F).extend K).form).trans
      (QuadraticMap.map_zero (QSpace.zero : QSpace K).form).symm

/-- Extension of scalars on isometry classes, $S(F) \to S(K)$, an additive map. -/
noncomputable def extendS : S F →+ S K := by
  refine
    { toFun := Quotient.lift (fun X => S.mk (QSpace.extend K X)) fun _ _ h => S.mk_eq_mk.mpr (extend_equiv K h)
      map_zero' := S.mk_eq_mk.mpr (extend_zero_equiv K)
      map_add' := fun a b => ?_ }
  induction a using S.ind; induction b using S.ind
  rename_i X Y
  exact S.mk_eq_mk.mpr (extend_add_equiv K X Y)

theorem extendS_mk (X : QSpace F) : extendS K (S.mk X) = S.mk (QSpace.extend K X) := by
  rfl

/-- The extension of the hyperbolic plane is the hyperbolic plane. -/
theorem extend_hyp_equiv :
    ((hypSpace F).extend K).form.Equivalent (hypSpace K).form :=
  equiv_of_apply (V := Fin 2 → K) fun x => by
    refine (QuadForm.toQuadraticFormIn_apply K _ x).trans ?_
    show _ = (linMulLin (LinearMap.proj 0) (LinearMap.proj 1) : QuadraticForm K (Fin 2 → K)) x
    simp [QuadForm.evalIn, Fin.sum_univ_two, QuadForm.ofQuadraticForm, QuadForm.ofUpper, linMulLin_apply, polar]

/-- Extension of scalars sends $h$ to $h$. -/
theorem extendS_hyp : extendS K (hyp F) = hyp K :=
  (extendS_mk K (hypSpace F)).trans (S.mk_eq_mk.mpr (extend_hyp_equiv K))

/-- $h$ is zero in $W(K)$. -/
theorem toW_toG_hyp : toW K (toG K (hyp K)) = 0 := by
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  exact AddSubgroup.mem_zmultiples _

/-- Extension of scalars of $\langle a\rangle$ is $\langle a\rangle$. -/
theorem extend_unary_equiv [Invertible (2 : F)] [Invertible (2 : K)] (a : Fˣ) :
    ((diagSp F (fun _ : Fin 1 => (a : F)) fun _ => a.ne_zero).extend K).form.Equivalent
      (diagSp K (fun _ : Fin 1 => (algebraMap F K a)) fun _ =>
        (Units.map (algebraMap F K : F →* K) a).ne_zero).form :=
  equiv_of_apply (V := Fin 1 → K) fun x => by
    refine (QuadForm.toQuadraticFormIn_apply K _ x).trans ?_
    simp [QuadForm.evalIn, QuadForm.ofQuadraticForm, QuadForm.ofUpper]
    show _ = weightedSumSquares K (fun _ : Fin 1 => algebraMap F K a) x
    rw [weightedSumSquares_apply, Fin.sum_univ_one, smul_eq_mul]
    ring

/-- **Cassels' localization map** $\lambda_K : W(F) \to W(K)$ (Ch. 6, §11, p. 93, for $F = \mathbb Q$ and
$K = \mathbb Q_p$, $p \le \infty$): the map induced by extension of scalars. -/
@[kb "cassels1978" "Ch. 6, §11, p. 93 (the localization maps λ_p : W(ℚ) → W(ℚ_p))"]
noncomputable def localize : W F →+ W K :=
  liftW F ((toW K).comp ((toG K).comp (extendS K))) (by
    show toW K (toG K (extendS K (hyp F))) = 0
    rw [extendS_hyp, toW_toG_hyp])

/-- $\lambda_K$ on the class of $s \in S(F)$. -/
theorem localize_toW (s : S F) : localize K (toW F (toG F s)) = toW K (toG K (extendS K s)) :=
  liftW_apply F _ _ s

/-- **Cassels, Ch. 6, §11, p. 93**: $\lambda_K$ *maps $\langle a\rangle$, considered as an element of $W(F)$, into
$\langle a\rangle$, considered as an element of $W(K)$.* -/
@[kb "cassels1978" "Ch. 6, §11, p. 93 (λ_p⟨a⟩ = ⟨a⟩)"]
theorem localize_unary [Invertible (2 : F)] [Invertible (2 : K)] (a : Fˣ) :
    localize K (toW F (toG F (unary F a))) = toW K (toG K (unary K (Units.map (algebraMap F K) a))) := by
  rw [localize_toW, unary_def, extendS_mk]
  exact congrArg (fun s => toW K (toG K s)) (S.mk_eq_mk.mpr (extend_unary_equiv K a))

/-- Every element of the Grothendieck group is a difference of two classes. -/
theorem G_exists_sub (g : G F) : ∃ a b : S F, g = toG F a - toG F b := by
  have h1 : Algebra.GrothendieckAddGroup.lift (toG F) = AddMonoidHom.id (G F) :=
    Algebra.GrothendieckAddGroup.lift.apply_symm_apply (AddMonoidHom.id _)
  have h2 := Algebra.GrothendieckAddGroup.lift_apply (toG F) g
  rw [h1] at h2
  exact ⟨_, _, h2⟩

/-- ($\operatorname{char} \ne 2$.) Every element of $W(F)$ is the class of a single element of $S(F)$. -/
theorem W_exists_S [Invertible (2 : F)] (x : W F) : ∃ s : S F, x = toW F (toG F s) := by
  obtain ⟨g, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨a, b, rfl⟩ := G_exists_sub g
  refine ⟨a + S.star b, ?_⟩
  have h : toW F (toG F b) + toW F (toG F (S.star b)) = 0 := by
    rw [← map_add, ← map_add, add_star_eq_dim_smul, map_nsmul, map_nsmul, toW_toG_hyp, smul_zero]
  rw [map_add, map_add, sub_eq_add_neg, eq_neg_of_add_eq_zero_right h]
  rfl

/-- If $t + m h = m' h$ in $S(K)$ then $t = (\dim t / 2)\, h$ (cancellation and dimension count). -/
theorem eq_smul_hyp_of_add_eq (t : S K) {m m' : ℕ} (h : t + m • hyp K = 0 + m' • hyp K) :
    t = (S.dim t / 2) • hyp K := by
  have hd := congrArg S.dim h
  simp only [map_add, map_nsmul, zero_add] at hd
  have h2 : S.dim (hyp K) = 2 := rfl
  rw [h2] at hd
  simp only [smul_eq_mul] at hd
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (show m ≤ m' by omega)
  subst hk
  have hk2 : S.dim t / 2 = k := by omega
  rw [hk2]
  refine S.add_left_cancel' (a := m • hyp K) ?_
  rw [add_comm (m • hyp K) t, h, zero_add, add_smul, add_comm]

/-- If $\lambda_K[s] = 0$ then $s$ becomes $(\dim s / 2)\, h$ over $K$. -/
theorem extendS_eq_of_localize (s : S F) (h : localize K (toW F (toG F s)) = 0) :
    extendS K s = (S.dim s / 2) • hyp K := by
  rw [localize_toW] at h
  have h' : toW K (toG K (extendS K s)) = toW K (toG K 0) := by rw [h]; simp
  obtain ⟨m, m', hm⟩ := (toW_toG_eq_iff K _ _).mp h'
  have h1 : S.dim (extendS K s) = S.dim s := by
    induction s using S.ind
    rfl
  rw [← h1]
  exact eq_smul_hyp_of_add_eq K (extendS K s) hm

/-- **Cassels, Ch. 6, Corollary 1 to Theorem 11.1**: *suppose that an element of $W(\mathbb Q)$ is in the kernel of
all the localization maps $\lambda_p$ (including $p = \infty$). Then it is $0$.* (Proved from the Weak Hasse
Principle, not from Theorem 11.1; see the module docstring.) -/
@[kb "cassels1978" "Ch. 6, Cor. 1 to Thm. 11.1, p. 94"]
theorem localize_injective_everywhere (x : W ℚ) (h : RatPlace.Everywhere fun K _ _ => localize K x = 0) : x = 0 := by
  let _ : Invertible (2 : ℚ) := invertibleOfNonzero two_ne_zero
  obtain ⟨s, rfl⟩ := W_exists_S x
  induction s using S.ind with
  | h X =>
  obtain ⟨Y, hY⟩ : ∃ Y : QSpace ℚ, S.mk Y = (X.dim / 2) • hyp ℚ := by
    induction ((X.dim / 2) • hyp ℚ) using S.ind with
    | h Y => exact ⟨Y, rfl⟩
  have hext : ∀ (K : Type) [Field K] [CharZero K], localize K (toW ℚ (toG ℚ (S.mk X))) = 0 →
      extendS K (S.mk X) = extendS K (S.mk Y) := by
    intro K _ _ hK
    rw [extendS_eq_of_localize K _ hK, hY, map_nsmul, extendS_hyp]
    rfl
  have hdim : X.dim = Y.dim := congrArg S.dim (hext ℝ (h RatPlace.infinite))
  have hzero : toW ℚ (toG ℚ (S.mk Y)) = 0 := by
    rw [hY, map_nsmul, map_nsmul, toW_toG_hyp, smul_zero]
  suffices hXY : (S.mk X) = S.mk Y by rw [hXY]; exact hzero
  obtain ⟨n, Q, hQ⟩ := X
  obtain ⟨n', R, hR⟩ := Y
  dsimp only at hdim
  subst hdim
  have step : ∀ (K : Type) [Field K] [CharZero K], localize K (toW ℚ (toG ℚ (S.mk ⟨n, Q, hQ⟩))) = 0 →
      (QuadForm.ofQuadraticForm R).IsometricIn K (QuadForm.ofQuadraticForm Q) := by
    intro K _ _ hK
    rw [QuadForm.isometricIn_iff_equivalent]
    exact S.mk_eq_mk.mp (hext K hK)
  have hev : RatPlace.Everywhere fun K _ _ =>
      (QuadForm.ofQuadraticForm R).IsometricIn K (QuadForm.ofQuadraticForm Q) := by
    intro v
    cases v with
    | infinite => exact step ℝ (h RatPlace.infinite)
    | finite p =>
      have : Fact p.1.Prime := ⟨p.2⟩
      exact step ℚ_[p.1] (h (RatPlace.finite p))
  have hiso := (isometric_iff_everywhere _ _ (nondeg_ofQuadraticForm R hR) (nondeg_ofQuadraticForm Q hQ)).mpr hev
  rw [QuadForm.isometricIn_iff_equivalent, toQuadraticFormIn_self, toQuadraticFormIn_self] at hiso
  exact S.mk_eq_mk.mpr hiso

end QuadFormsKB.Cassels.Ch6
