/-
# Cassels, Chapter 2: remaining running-text items (pp. 19, 25, 27)

Source: J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 2.

**Proves.**
* p. 19 (§4): for a regular subspace $V$ of a quadratic space $U$, the linear map that is $-1$ on $V$ and $1$ on
  $V^{\perp}$ exists, is unique, is an autometry, and has determinant $(-1)^{\dim V}$ (`exists_unique_negOnRegular`,
  `negOnRegular_isometry`, `det_negOnRegular`).
* p. 25 (footnote to §5): the modified determinant $\det^{*}(s) = (-1)^{n(n-1)/2}\det(s)$, $n = \dim s$ (`detStar`);
  it is unchanged by adding $h$ (`detStar_add_hyp`), hence constant on Witt classes (`detStar_eq_of_toW_eq`), and it
  is not a homomorphism when $-1$ is not a square (`detStar_not_hom`).
* p. 27 (§6): the quadratic form induced on $V/V_0$ ($V_0$ the radical) is well defined and regular
  (`quad_eq_of_sub_mem_radical`, `quotRadicalForm`, `quotRadicalForm_mk`, `regular_quotRadicalForm`).

**Setting.** $k$ is a field of characteristic $\neq 2$ (`[Invertible (2 : k)]`); a quadratic space is
`Q : QuadraticForm k U`, Cassels' bilinear form $\phi(u, v)$ (with $\phi(u, u) = Q(u)$) is `associated Q`.
-/
import QuadFormsKB.Literature.Cassels.Ch2.WittGroup
import QuadFormsKB.Literature.Cassels.Ch2.Basic

open QuadraticMap Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Cassels

section Autometry

variable {k U : Type*} [Field k] [Invertible (2 : k)] [AddCommGroup U] [Module k U]

/-- Cassels' bilinear form $\phi$ of a quadratic form $Q$, as a Mathlib bilinear form. -/
abbrev assocB (Q : QuadraticForm k U) : LinearMap.BilinForm k U := associated Q

theorem assocB_isSymm (Q : QuadraticForm k U) : (assocB Q).IsSymm :=
  ⟨fun x y => QuadraticMap.associated_isSymm k Q x y⟩

/-- The two defining conditions of Cassels' map $\sigma$ (p. 19): $\sigma u = -u$ on $V$ and $\sigma u = u$ on
$V^{\perp}$ (the orthogonal complement for $\phi$ = `associated Q`). -/
def IsNegOnRegular (Q : QuadraticForm k U) (V : Submodule k U) (σ : U →ₗ[k] U) : Prop :=
  (∀ u ∈ V, σ u = -u) ∧ ∀ u ∈ (assocB Q).orthogonal V, σ u = u

/-- **Cassels, Ch. 2, §4, p. 19.** Let $V$ be a regular subspace of the finite-dimensional quadratic space $(U, Q)$
(the restriction of $\phi$ to $V$ is nondegenerate; `[Invertible (2 : k)]`, i.e. $\operatorname{char} k \neq 2$), so
that $U = V \oplus V^{\perp}$ (Lemma 1.3). There is a uniquely defined linear map $\sigma : U \to U$ such that
$\sigma u = -u$ for $u \in V$ and $\sigma u = u$ for $u \in V^{\perp}$ (`IsNegOnRegular`). -/
@[kb "cassels1978" "Ch. 2, §4, p. 19 (the autometry −1 on a regular subspace V and 1 on V^⊥)"]
theorem exists_unique_negOnRegular [FiniteDimensional k U] (Q : QuadraticForm k U) (V : Submodule k U)
    (hV : ((assocB Q).restrict V).Nondegenerate) :
    ∃! σ : U →ₗ[k] U, IsNegOnRegular Q V σ := by
  have hc := isCompl_orthogonal_of_regular (assocB_isSymm Q) hV
  set W := (assocB Q).orthogonal V
  refine ⟨LinearMap.ofIsCompl hc (-V.subtype) W.subtype, ⟨?_, ?_⟩, ?_⟩
  · intro u hu
    simpa using LinearMap.ofIsCompl_apply_left (φ := -V.subtype) (ψ := W.subtype) hc (⟨u, hu⟩ : V)
  · intro u hu
    simpa using LinearMap.ofIsCompl_apply_right (φ := -V.subtype) (ψ := W.subtype) hc (⟨u, hu⟩ : W)
  · rintro τ ⟨h1, h2⟩
    refine LinearMap.ext_on_codisjoint (f := τ) (g := LinearMap.ofIsCompl hc (-V.subtype) W.subtype)
      hc.codisjoint ?_ ?_
    · intro u hu
      simpa [h1 u hu] using (LinearMap.ofIsCompl_apply_left (φ := -V.subtype) (ψ := W.subtype) hc (⟨u, hu⟩ : V)).symm
    · intro u hu
      simpa [h2 u hu] using (LinearMap.ofIsCompl_apply_right (φ := -V.subtype) (ψ := W.subtype) hc (⟨u, hu⟩ : W)).symm

/-- **Cassels, Ch. 2, §4, p. 19 ("Clearly $\sigma$ is an autometry").** The map $\sigma$ of
`exists_unique_negOnRegular` preserves the quadratic form: $Q(\sigma u) = Q(u)$ for all $u \in U$. -/
@[kb "cassels1978" "Ch. 2, §4, p. 19 (the autometry −1 on a regular subspace V and 1 on V^⊥)"]
theorem negOnRegular_isometry [FiniteDimensional k U] (Q : QuadraticForm k U) (V : Submodule k U)
    (hV : ((assocB Q).restrict V).Nondegenerate)
    (σ : U →ₗ[k] U) (hσ : IsNegOnRegular Q V σ) (u : U) : Q (σ u) = Q u := by
  have hc := isCompl_orthogonal_of_regular (assocB_isSymm Q) hV
  obtain ⟨v, hv, w, hw, rfl⟩ := Submodule.mem_sup.mp (hc.sup_eq_top ▸ Submodule.mem_top (x := u))
  have hperp : polar Q v w = 0 := by
    have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hw) v hv
    have h2 : (2 : k) * associated Q v w = polar Q v w := by
      show (2 : k) * (⅟2 * (Q (v + w) - Q v - Q w)) = _
      rw [← mul_assoc, mul_invOf_self, one_mul]; rfl
    rw [← h2, h, mul_zero]
  have hperp' : polar Q (-v) w = 0 := by rw [QuadraticMap.polar_neg_left, hperp, neg_zero]
  rw [map_add, hσ.1 v hv, hσ.2 w hw, QuadraticMap.map_add Q (-v) w, QuadraticMap.map_add Q v w, hperp, hperp',
    QuadraticMap.map_neg]

/-- **Cassels, Ch. 2, §4, p. 19.** The map $\sigma$ of `exists_unique_negOnRegular` has determinant
$(-1)^{\dim V}$. -/
@[kb "cassels1978" "Ch. 2, §4, p. 19 (the autometry −1 on a regular subspace V and 1 on V^⊥)"]
theorem det_negOnRegular [FiniteDimensional k U] (Q : QuadraticForm k U) (V : Submodule k U)
    (hV : ((assocB Q).restrict V).Nondegenerate)
    (σ : U →ₗ[k] U) (hσ : IsNegOnRegular Q V σ) : LinearMap.det σ = (-1) ^ finrank k V := by
  have hc := isCompl_orthogonal_of_regular (assocB_isSymm Q) hV
  set W := (assocB Q).orthogonal V
  let e := Submodule.prodEquivOfIsCompl V W hc
  have hconj : (e.symm : U →ₗ[k] V × W) ∘ₗ σ ∘ₗ (e : V × W →ₗ[k] U) =
      LinearMap.prodMap (-LinearMap.id) LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨v, w⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.prodMap_apply, LinearMap.neg_apply,
      LinearMap.id_apply]
    have h1 : e (v, w) = (v : U) + (w : U) := Submodule.coe_prodEquivOfIsCompl' V W hc (v, w)
    have h2 : e.symm (-(v : U) + (w : U)) = (-v, w) := by
      rw [LinearEquiv.symm_apply_eq]
      have := Submodule.coe_prodEquivOfIsCompl' V W hc (-v, w)
      exact (by simp : -(v : U) + (w : U) = ((-v : V) : U) + (w : U)).trans this.symm
    rw [h1, map_add, hσ.1 v v.2, hσ.2 w w.2, h2]
  have hd := LinearMap.det_conj σ e.symm
  rw [LinearEquiv.symm_symm] at hd
  rw [← hd, hconj, LinearMap.det_prodMap, LinearMap.det_id, mul_one]
  have : (-LinearMap.id : V →ₗ[k] V) = (-1 : k) • LinearMap.id := by ext; simp
  rw [this, LinearMap.det_smul, LinearMap.det_id, mul_one]

end Autometry

section DetStar

variable {K : Type*} [Field K] [Invertible (2 : K)]

/-- The class of $-1$ in $k^{\times}/(k^{\times})^{2}$, written additively. -/
def negOneClass : Additive (SqClass K) := Additive.ofMul (QuotientGroup.mk (-1 : Kˣ))

theorem two_nsmul_negOneClass : 2 • (negOneClass : Additive (SqClass K)) = 0 := by
  unfold negOneClass
  rw [← ofMul_pow, ← QuotientGroup.mk_pow, neg_one_sq]
  rfl

theorem det_hyp : S.det (hyp K) = negOneClass := by
  have h2 := Invertible.ne_zero (2 : K)
  have : detU (hypSpace K) = (Units.mk0 (⅟2 : K) (by simp; exact h2)) ^ 2 * (-1) := by
    ext; rw [detU_hyp]; simp
  show Additive.ofMul (QuotientGroup.mk (detU (hypSpace K)) : SqClass K) = negOneClass
  congr 1
  rw [QuotientGroup.eq]
  refine ⟨(Units.mk0 (⅟2 : K) (by simp; exact h2))⁻¹, ?_⟩
  rw [this]
  simp [powMonoidHom_apply]

/-- **The modified determinant** $\det^{*}(s) = (-1)^{n(n-1)/2}\det(s)$ with $n = \dim s$ (Cassels p. 25,
footnote), with values in $k^{\times}/(k^{\times})^{2}$ (written additively, as `S.det`). Here $n(n-1)/2$ is the
natural-number division, exact since $n(n-1)$ is even. -/
@[kb "cassels1978" "Ch. 2, §5, p. 25, footnote (the modified determinant det*)"]
def detStar (s : S K) : Additive (SqClass K) :=
  S.det s + (S.dim s * (S.dim s - 1) / 2) • negOneClass

theorem detStar_eq_choose (s : S K) : detStar s = S.det s + (S.dim s).choose 2 • negOneClass := by
  rw [detStar, Nat.choose_two_right]

theorem choose_add_two (n : ℕ) : (n + 2).choose 2 = n.choose 2 + (2 * n + 1) := by
  have h1 : (n + 2).choose 2 = (n + 1).choose 1 + (n + 1).choose 2 := Nat.choose_succ_succ' (n + 1) 1
  have h2 : (n + 1).choose 2 = n.choose 1 + n.choose 2 := Nat.choose_succ_succ' n 1
  have h3 := Nat.choose_one_right n
  have h4 := Nat.choose_one_right (n + 1)
  omega

theorem aux_add {A : Type*} [AddCommGroup A] (d e : A) (he : 2 • e = 0) (c n : ℕ) :
    d + e + ((c + (2 * n + 1)) • e) = d + c • e := by
  have h : (2 * n) • e = 0 := by rw [mul_comm, mul_nsmul', he, smul_zero]
  have h2 : e + e = 0 := by rwa [two_nsmul] at he
  rw [add_nsmul, add_nsmul, h, zero_add, one_nsmul]
  calc d + e + (c • e + e) = d + c • e + (e + e) := by abel
    _ = _ := by rw [h2, add_zero]

theorem aux_two {A : Type*} [AddCommGroup A] (e : A) : (0 : A) + 0 + (1 + 1).choose 2 • e = e := by
  simp [Nat.choose]

theorem aux_one {A : Type*} [AddCommGroup A] (e : A) : (0 : A) + (1 : ℕ).choose 2 • e = 0 := by
  simp [Nat.choose]

/-- **Cassels, Ch. 2, §5, p. 25, footnote.** $\det^{*}(s + h) = \det^{*}(s)$, where $h$ is the class of the
hyperbolic plane. Hence $\det^{*}$ induces a well-defined function on $W(k)$ (`detStar_eq_of_toW_eq`). -/
@[kb "cassels1978" "Ch. 2, §5, p. 25, footnote (the modified determinant det*)"]
theorem detStar_add_hyp (s : S K) : detStar (s + hyp K) = detStar s := by
  rw [detStar_eq_choose, detStar_eq_choose, map_add, map_add, det_hyp]
  have hd : S.dim (hyp K) = 2 := rfl
  rw [hd, choose_add_two]
  exact aux_add (A := Additive (SqClass K)) _ negOneClass two_nsmul_negOneClass _ _

theorem detStar_add_nsmul_hyp (s : S K) (m : ℕ) : detStar (s + m • hyp K) = detStar s := by
  induction m with
  | zero => simp
  | succ m ih => rw [succ_nsmul, ← add_assoc, detStar_add_hyp, ih]

/-- **Cassels, Ch. 2, §5, p. 25, footnote.** $\det^{*}$ is well defined on $W(k)$: if $s, s' \in S(k)$ have the
same image in the Witt group then $\det^{*}(s) = \det^{*}(s')$. -/
@[kb "cassels1978" "Ch. 2, §5, p. 25, footnote (the modified determinant det*)"]
theorem detStar_eq_of_toW_eq {s s' : S K} (h : toW K (toG K s) = toW K (toG K s')) :
    detStar s = detStar s' := by
  obtain ⟨m, m', hm⟩ := (toW_toG_eq_iff K s s').mp h
  rw [← detStar_add_nsmul_hyp s m, hm, detStar_add_nsmul_hyp]

/-- **Cassels, Ch. 2, §5, p. 25, footnote.** $\det^{*}$ is not a homomorphism: if $-1$ is not a square in $k$
then $\det^{*}(\langle 1\rangle + \langle 1\rangle) = -1 \neq 1 = \det^{*}\langle 1\rangle +
\det^{*}\langle 1\rangle$ (in $k^{\times}/(k^{\times})^{2}$). *Remark:* the book states that neither $\det^{*}$
nor $\det^{*}_W$ is a homomorphism without qualification; this holds exactly when $-1 \notin (k^{\times})^{2}$
(if $-1$ is a square then $(-1)^{m} = 1$ modulo squares and $\det^{*} = \det$, a homomorphism). -/
@[kb "cassels1978" "Ch. 2, §5, p. 25, footnote (the modified determinant det*)"]
theorem detStar_not_hom (hK : ¬ IsSquare (-1 : K)) :
    detStar (unary K 1 + unary K 1) ≠ detStar (unary K 1) + detStar (unary K 1) := by
  have hd : S.dim (unary K 1) = 1 := rfl
  have h0 : S.det (unary K 1) = 0 := by
    rw [det_unary]; rfl
  have hne : (negOneClass : Additive (SqClass K)) ≠ 0 := by
    intro h
    apply hK
    have h' : (QuotientGroup.mk (-1 : Kˣ) : SqClass K) = 1 := h
    obtain ⟨y, hy⟩ := (QuotientGroup.eq_one_iff _).mp h'
    refine ⟨y, ?_⟩
    have := congrArg (fun u : Kˣ => (u : K)) hy
    simp [powMonoidHom] at this
    linear_combination -this
  have e1 : detStar (unary K 1 + unary K 1) = negOneClass := by
    rw [detStar_eq_choose, map_add, map_add, h0, hd]
    exact aux_two (A := Additive (SqClass K)) _
  have e2 : detStar (unary K 1) = 0 := by
    rw [detStar_eq_choose, h0, hd]
    exact aux_one (A := Additive (SqClass K)) _
  rw [e1, e2]
  intro h
  exact hne (h.trans (add_zero (0 : Additive (SqClass K))))

end DetStar

section Radical

variable {k V : Type*} [Field k] [Invertible (2 : k)] [AddCommGroup V] [Module k V]

/-- The radical $V_0 = \{a : \phi(a, b) = 0 \text{ for all } b\}$ of Cassels' bilinear form is Mathlib's
radical of the quadratic form. -/
theorem orthogonal_top_eq_radical (Q : QuadraticForm k V) : (assocB Q).orthogonal ⊤ = Q.radical := by
  rw [QuadraticMap.radical_eq_ker_associated]
  ext r
  simp only [LinearMap.BilinForm.mem_orthogonal_iff, Submodule.mem_top, forall_const, LinearMap.mem_ker,
    LinearMap.ext_iff, LinearMap.zero_apply]
  refine forall_congr' fun w => ?_
  rw [(assocB_isSymm Q).eq w r]

/-- **Cassels, Ch. 2, §6, p. 27.** If $b_1 - b_2$ lies in the radical $V_0$ then $\phi(b_1) = \phi(b_2)$. -/
@[kb "cassels1978" "Ch. 2, §6, p. 27 (the induced form on V/V₀ is a regular quadratic space)"]
theorem quad_eq_of_sub_mem_radical (Q : QuadraticForm k V) {b₁ b₂ : V}
    (h : b₁ - b₂ ∈ (assocB Q).orthogonal ⊤) : Q b₁ = Q b₂ := by
  rw [orthogonal_top_eq_radical] at h
  have := (QuadraticMap.mem_radical_iff'.mp h)
  have h2 := this.2 b₂
  rwa [sub_add_cancel] at h2

/-- **The induced form** $\bar\phi$ on $\bar V = V/V_0$ (Cassels, p. 27), where $V_0 = \{a : \phi(a, b) = 0 \
\text{for all } b\}$ is the radical: $\bar\phi(b + V_0) = \phi(b)$. This is Mathlib's `QuadraticMap.lift` on the
radical. -/
def quotRadicalForm (Q : QuadraticForm k V) : QuadraticForm k (V ⧸ (assocB Q).orthogonal ⊤) :=
  Q.lift _ (orthogonal_top_eq_radical Q).le

/-- **Cassels, Ch. 2, §6, p. 27.** $\bar\phi(b + V_0) = \phi(b)$ for all $b \in V$. -/
@[kb "cassels1978" "Ch. 2, §6, p. 27 (the induced form on V/V₀ is a regular quadratic space)"]
theorem quotRadicalForm_mk (Q : QuadraticForm k V) (v : V) :
    quotRadicalForm Q (Submodule.Quotient.mk v) = Q v := rfl

/-- **Cassels, Ch. 2, §6, p. 27.** The quadratic space $(\bar V, \bar\phi)$, $\bar V = V/V_0$, is regular: the
bilinear form of $\bar\phi$ is nondegenerate. -/
@[kb "cassels1978" "Ch. 2, §6, p. 27 (the induced form on V/V₀ is a regular quadratic space)"]
theorem regular_quotRadicalForm (Q : QuadraticForm k V) :
    (associated (quotRadicalForm Q)).Nondegenerate := by
  rw [QuadraticMap.nondegenerate_associated_iff, QuadraticMap.nondegenerate_iff_radical_eq_bot,
    eq_bot_iff]
  intro x hx
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [QuadraticMap.mem_radical_iff'] at hx
  have hv : v ∈ Q.radical := by
    rw [QuadraticMap.mem_radical_iff']
    refine ⟨hx.1, fun n => ?_⟩
    have := hx.2 (Submodule.Quotient.mk n)
    rwa [← Submodule.Quotient.mk_add] at this
  rw [← orthogonal_top_eq_radical] at hv
  rw [Submodule.mem_bot]
  exact (Submodule.Quotient.mk_eq_zero _).mpr hv

end Radical

end QuadFormsKB.Cassels
