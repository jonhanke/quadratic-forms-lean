/-
# Cassels, Chapter 2, §§1–4 and 6: orthogonal complements, binary forms over a finite field, autometries, the radical

Source: J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 2, *Quadratic forms over a field*, pp. 11–21.

**Setting.** Cassels' quadratic space $(U, \phi)$ is a finite-dimensional vector space $U$ over a field $k$ with a
symmetric bilinear form $\phi$; here $U$ = `V`, $k$ = `K` and $\phi$ = `B : LinearMap.BilinForm K V` with
`B.IsSymm`. The space is *regular* when $\phi$ is nondegenerate (`B.Nondegenerate`, Cassels p. 12, (i)–(ii) of
Lemma 1.2); a linear subspace $W$ is regular when the restriction of $\phi$ to $W$ is (`(B.restrict W).Nondegenerate`).
The orthogonal complement $W^{\perp}$ (Cassels' $V^{\perp}$, p. 13) is `B.orthogonal W`. Cassels assumes
$\operatorname{char} k \neq 2$ throughout; the statements of §1 and §4 proved here hold for every field.

**Proves.**
* Lemma 1.3 (p. 13), `isCompl_orthogonal_of_regular`: $U = W \oplus W^{\perp}$ for a regular subspace $W$ of any
  (possibly singular) quadratic space.
* Lemma 1.6 (p. 14), `orthogonal_orthogonal_of_regular`: $(W^{\perp})^{\perp} = W$ in a regular space.
* Lemma 1.7 (p. 14), `regular_tfae`: in a regular space, $W \cap W^{\perp} = 0$, $W$ regular and $W^{\perp}$ regular
  are equivalent.
* Lemma 2.2 (pp. 15–16), `binary_universal_finiteField`: over a finite field of odd order every regular binary
  diagonal form $a x^{2} + b y^{2}$ represents every element (Cassels: over $\mathbb F_p$, $p \neq 2$; since every
  binary space has a normal basis (Lemma 1.4) this is the statement for every regular binary space).
* Lemma 4.1 (p. 19), `det_autometry`: an autometry $\sigma$ of a regular space has $\det \sigma = \pm 1$.
* Lemma 6.1 (p. 28), `exists_regular_compl_radical`: every quadratic space is $V_0 \oplus V_1$ with $V_0$ the radical
  and $V_1$ regular (proof: any linear complement of the radical is regular).
* Lemma 6.2 (p. 28), `exists_equivalent_regular_prod_zero` ($\operatorname{char} k \neq 2$): every quadratic form
  $f$ on $k^{n}$ is equivalent to $h \perp 0_r$ with $h$ regular in $m = n - r$ variables (Mathlib forms; proof:
  $\phi$ vanishes on the radical, so $\phi(w + r) = \phi(w)$ for the decomposition of Lemma 6.1).

**Proof notes.** Lemmas 1.3, 1.6 and 1.7 come from Mathlib's `LinearMap.BilinForm` orthogonal-complement API.
Lemma 2.2 is the counting argument of Mathlib's `FiniteField.exists_root_sum_quadratic` (the value sets of
$a x^{2}$ and $c - b y^{2}$ each have $(q+1)/2$ elements, so they meet), which is Cassels' proof. Lemma 4.1 is
Cassels' determinant computation: the Gram matrix $\Phi$ satisfies $\Sigma^{\mathsf T}\Phi\Sigma = \Phi$, so
$(\det\Sigma)^{2}\det\Phi = \det\Phi \neq 0$.
-/
import Mathlib
import QuadFormsKB.Citation

open Module LinearMap LinearMap.BilinForm Polynomial

namespace QuadFormsKB.Cassels

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- **Cassels, Ch. 2, Lemma 1.3.** Let $(U, \phi)$ be a finite-dimensional quadratic space, not necessarily regular,
with $\phi$ symmetric, and let $W \subseteq U$ be a regular subspace (the restriction of $\phi$ to $W$ is
nondegenerate). Then $U$ is the direct sum of $W$ and its orthogonal complement
$W^{\perp} = \{u : \phi(u, w) = 0 \text{ for all } w \in W\}$: $U = W \oplus W^{\perp}$. -/
@[kb "cassels1978" "Ch. 2, Lemma 1.3, p. 13"]
theorem isCompl_orthogonal_of_regular [FiniteDimensional K V] {B : LinearMap.BilinForm K V} (hB : B.IsSymm)
    {W : Submodule K V} (hW : (B.restrict W).Nondegenerate) : IsCompl W (B.orthogonal W) :=
  isCompl_orthogonal_of_restrict_nondegenerate hB.isRefl hW

/-- **Cassels, Ch. 2, Lemma 1.6.** If the finite-dimensional quadratic space $(U, \phi)$ is regular ($\phi$
symmetric and nondegenerate), then $(W^{\perp})^{\perp} = W$ for every linear subspace $W$ of $U$. -/
@[kb "cassels1978" "Ch. 2, Lemma 1.6, p. 14"]
theorem orthogonal_orthogonal_of_regular [FiniteDimensional K V] {B : LinearMap.BilinForm K V} (hB : B.IsSymm)
    (hreg : B.Nondegenerate) (W : Submodule K V) : B.orthogonal (B.orthogonal W) = W :=
  orthogonal_orthogonal hreg hB.isRefl W

/-- **Cassels, Ch. 2, Lemma 1.7.** Let $W$ be a linear subspace of the regular finite-dimensional quadratic space
$(U, \phi)$ ($\phi$ symmetric and nondegenerate). The following are equivalent: (i) $W \cap W^{\perp} = \{0\}$;
(ii) $W$ is regular; (iii) $W^{\perp}$ is regular. -/
@[kb "cassels1978" "Ch. 2, Lemma 1.7, p. 14"]
theorem regular_tfae [FiniteDimensional K V] {B : LinearMap.BilinForm K V} (hB : B.IsSymm) (hreg : B.Nondegenerate)
    (W : Submodule K V) :
    [Disjoint W (B.orthogonal W), (B.restrict W).Nondegenerate,
      (B.restrict (B.orthogonal W)).Nondegenerate].TFAE := by
  have key : ∀ W' : Submodule K V, (B.restrict W').Nondegenerate ↔ Disjoint W' (B.orthogonal W') :=
    fun W' => (restrict_nondegenerate_iff_isCompl_orthogonal hB.isRefl).trans
      (isCompl_orthogonal_iff_disjoint hB.isRefl)
  tfae_have 1 ↔ 2 := (key W).symm
  tfae_have 3 ↔ 1 := by
    rw [key, orthogonal_orthogonal hreg hB.isRefl, disjoint_comm]
  tfae_finish

/-- **Cassels, Ch. 2, Lemma 2.2.** Let $k$ be a finite field of odd order (Cassels: $k = \mathbb F_p$, $p \neq 2$
prime). Then every regular binary diagonal form $a x^{2} + b y^{2}$ ($a, b \in k^{\times}$) is universal: for every
$c \in k$ there are $x, y \in k$ with $a x^{2} + b y^{2} = c$. Every regular binary space has a normal basis
(Lemma 1.4), so this is the statement for all regular binary spaces. -/
@[kb "cassels1978" "Ch. 2, Lemma 2.2, pp. 15–16"]
theorem binary_universal_finiteField [Fintype K] (hK : Fintype.card K % 2 = 1) {a b : K} (ha : a ≠ 0)
    (hb : b ≠ 0) (c : K) : ∃ x y : K, a * x ^ 2 + b * y ^ 2 = c := by
  have hf : degree (C a * X ^ 2) = 2 := by rw [degree_C_mul_X_pow 2 ha]; rfl
  have hg : degree (C b * X ^ 2 - C c) = 2 := by
    rw [degree_sub_C (by rw [degree_C_mul_X_pow 2 hb]; exact compareOfLessAndEq_eq_lt.mp rfl)]
    rw [degree_C_mul_X_pow 2 hb]; rfl
  obtain ⟨x, y, h⟩ := FiniteField.exists_root_sum_quadratic hf hg hK
  refine ⟨x, y, ?_⟩
  simp only [eval_mul, eval_C, eval_pow, eval_X, eval_sub] at h
  linear_combination h

/-- **Cassels, Ch. 2, Lemma 4.1.** Let $\sigma$ be an autometry of a regular finite-dimensional quadratic space
$(U, \phi)$, i.e. a linear automorphism with $\phi(\sigma u, \sigma v) = \phi(u, v)$ for all $u, v \in U$. Then
$\det \sigma = \pm 1$. -/
@[kb "cassels1978" "Ch. 2, Lemma 4.1, p. 19"]
theorem det_autometry [FiniteDimensional K V] {B : LinearMap.BilinForm K V} (hreg : B.Nondegenerate)
    (σ : V ≃ₗ[K] V) (hσ : ∀ u v, B (σ u) (σ v) = B u v) :
    LinearMap.det (σ : V →ₗ[K] V) = 1 ∨ LinearMap.det (σ : V →ₗ[K] V) = -1 := by
  classical
  let b := Module.finBasis K V
  have hcomp : B.comp (σ : V →ₗ[K] V) (σ : V →ₗ[K] V) = B := by
    ext u v; simp [hσ]
  have hmat := LinearMap.BilinForm.toMatrix_comp b b B (σ : V →ₗ[K] V) (σ : V →ₗ[K] V)
  rw [hcomp] at hmat
  have hdet := congrArg Matrix.det hmat
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix] at hdet
  have h0 : (BilinForm.toMatrix b B).det ≠ 0 := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hreg
  have h1 : LinearMap.det (σ : V →ₗ[K] V) * LinearMap.det (σ : V →ₗ[K] V) = 1 := by
    have : (LinearMap.det (σ : V →ₗ[K] V) * LinearMap.det (σ : V →ₗ[K] V) - 1) *
        (BilinForm.toMatrix b B).det = 0 := by linear_combination -hdet
    rcases mul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h h0
  exact mul_self_eq_one_iff.mp h1

/-- **Cassels, Ch. 2, Lemma 6.1.** Every finite-dimensional quadratic space $(V, \phi)$ ($\phi$ symmetric, possibly
singular) is the direct sum $V = V_0 \oplus V_1$ of its radical
$V_0 = \{a : \phi(a, b) = 0 \text{ for all } b \in V\}$ (`B.orthogonal ⊤`) and a subspace $V_1$ on which $\phi$
restricts to a regular (nondegenerate) form. -/
@[kb "cassels1978" "Ch. 2, Lemma 6.1, p. 28"]
theorem exists_regular_compl_radical [FiniteDimensional K V] {B : LinearMap.BilinForm K V} (hB : B.IsSymm) :
    ∃ W : Submodule K V, IsCompl (B.orthogonal ⊤) W ∧ (B.restrict W).Nondegenerate := by
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (B.orthogonal ⊤)
  refine ⟨W, hW, ?_⟩
  have hrefl : (B.restrict W).IsRefl := fun x y h => by
    simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply] at h ⊢
    rw [← hB.eq]; simpa using h
  show LinearMap.Nondegenerate (B.restrict W)
  rw [LinearMap.IsRefl.nondegenerate_iff_separatingLeft hrefl]
  intro w hw
  have hmem : (w : V) ∈ B.orthogonal ⊤ := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro v _
    have hv : v ∈ B.orthogonal ⊤ ⊔ W := by rw [hW.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨r, hr, w', hw', rfl⟩ := Submodule.mem_sup.mp hv
    have h1 : B r w = 0 := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff] at hr
      have : B (w : V) r = 0 := hr w Submodule.mem_top
      rw [← hB.eq]; simpa using this
    have h2 : B w' w = 0 := by
      have := hw ⟨w', hw'⟩
      simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply] at this
      rw [← hB.eq]; simpa using this
    show B (r + w') w = 0
    rw [map_add, LinearMap.add_apply, h1, h2, add_zero]
  have : (w : V) ∈ B.orthogonal ⊤ ⊓ W := ⟨hmem, w.2⟩
  rw [hW.inf_eq_bot, Submodule.mem_bot] at this
  exact Subtype.ext this

/-- **Cassels, Ch. 2, Lemma 6.2.** ($\operatorname{char} k \neq 2$.) Every quadratic form $f$ in $n$ variables over
$k$ is equivalent to a form $h(x_1, \dots, x_{n-r})$ in the first $n - r$ variables only, with $h$ regular: there are
$m + r = n$ and a quadratic form $h$ on $k^{m}$ with nondegenerate polar form such that $f \cong h \perp 0_r$, where
$0_r$ is the zero form on $k^{r}$. -/
@[kb "cassels1978" "Ch. 2, Lemma 6.2, p. 28"]
theorem exists_equivalent_regular_prod_zero [Invertible (2 : K)] {n : ℕ} (Q : QuadraticForm K (Fin n → K)) :
    ∃ (m r : ℕ) (Q₁ : QuadraticForm K (Fin m → K)), m + r = n ∧ (QuadraticMap.polarBilin Q₁).Nondegenerate ∧
      Q.Equivalent (Q₁.prod (0 : QuadraticForm K (Fin r → K))) := by
  set B : LinearMap.BilinForm K (Fin n → K) := QuadraticMap.polarBilin Q with hBdef
  have hB : B.IsSymm := ⟨fun x y => by
    simp only [hBdef, QuadraticMap.polarBilin_apply_apply]; exact QuadraticMap.polar_comm Q x y⟩
  obtain ⟨W, hW, hreg⟩ := exists_regular_compl_radical hB
  set R := B.orthogonal ⊤
  have hR : ∀ (x : Fin n → K) (r : Fin n → K), r ∈ R → QuadraticMap.polar Q x r = 0 := fun x r hr =>
    (LinearMap.BilinForm.mem_orthogonal_iff.mp hr) x Submodule.mem_top
  have hQr : ∀ r ∈ R, Q r = 0 := fun r hr => by
    have h := hR r r hr
    rw [QuadraticMap.polar_self, two_smul] at h
    have h2 : (2 : K) * Q r = 0 := by rw [two_mul]; exact h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 (Invertible.ne_zero (2 : K))
    · exact h3
  let e0 : (W × R) ≃ₗ[K] (Fin n → K) := Submodule.prodEquivOfIsCompl W R hW.symm
  let QW : QuadraticForm K W := Q.comp W.subtype
  have hsplit : ∀ p : W × R, Q (e0 p) = (QW.prod (0 : QuadraticForm K R)) p := fun p => by
    show Q ((p.1 : Fin n → K) + p.2) = Q p.1 + 0
    have := QuadraticMap.map_add Q (p.1 : Fin n → K) p.2
    rw [hQr _ p.2.2, hR _ _ p.2.2] at this
    rw [add_zero]; linear_combination this
  let eW := (Module.finBasis K W).equivFun
  let eR := (Module.finBasis K R).equivFun
  refine ⟨Module.finrank K W, Module.finrank K R, QW.comp (eW.symm : _ →ₗ[K] W), ?_, ?_, ?_⟩
  · rw [add_comm, Submodule.finrank_add_eq_of_isCompl hW]; simp
  · show LinearMap.Nondegenerate _
    rw [LinearMap.IsRefl.nondegenerate_iff_separatingLeft
      (fun x y h => by
        rw [QuadraticMap.polarBilin_apply_apply] at h ⊢; rw [QuadraticMap.polar_comm]; exact h)]
    intro v hv
    have hsep := hreg.1
    have : eW.symm v = 0 := hsep (eW.symm v) fun w => by
      have := hv (eW w)
      simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, QuadraticMap.comp_apply,
        LinearEquiv.coe_coe, map_add, LinearEquiv.symm_apply_apply] at this
      simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply, hBdef,
        QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
      simpa [QW] using this
    simpa using congrArg eW this
  · refine ⟨((⟨e0, fun p => hsplit p⟩ : QuadraticMap.IsometryEquiv (QW.prod 0) Q).symm).trans
      (QuadraticMap.IsometryEquiv.prod
        (⟨eW, fun w => by simp⟩ : QuadraticMap.IsometryEquiv QW (QW.comp (eW.symm : _ →ₗ[K] W)))
        (⟨eR, fun _ => rfl⟩ : QuadraticMap.IsometryEquiv (0 : QuadraticForm K R) 0))⟩

end QuadFormsKB.Cassels
