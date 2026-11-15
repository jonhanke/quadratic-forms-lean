/-
# Shimura 2004, Theorem 7.13: when is $(V, s\varphi)$ isomorphic to $(V, \varphi)$?

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), Theorem 7.13 (printed
pp. 60--61), with its proof. Page numbers in the tags are printed pages.

**Setting and dictionary.** $F$ a field of characteristic $\ne 2$ (`Invertible (2 : F)`), $V$ a finite-dimensional
$F$-vector space of dimension $n$ (`Module.finrank F V`), $\varphi[x] = Q(x)$ for `Q : QuadraticForm F V`, and
$\varphi$ nondegenerate means `(QuadraticMap.associated Q).Nondegenerate`. For $s \in F^\times$ the form $s\varphi$
is `s • Q`, and "$(V, s\varphi)$ is isomorphic to $(V, \varphi)$" is `(s • Q).Equivalent Q`, i.e. there is a linear
bijection $g$ of $V$ with $Q(g x) = s\,Q(x)$. The polar form is `QuadraticMap.polar Q`, so
$\operatorname{polar}Q(x,y) = Q(x+y)-Q(x)-Q(y) = 2\varphi(x,y)$.

**Proves** (unconditional; standard axioms only)
* *n odd* (the proof's first half, valid over every field of characteristic $\ne 2$):
  `odd_equivalent_iff`: for $s \ne 0$, $(V, sQ) \cong (V, Q)$ iff $s \in F^{\times 2}$ (that is $\mathfrak{G} = F^{\times 2}$
  of (7.11a)); via $G^{T} M G = sM$ and $\det(G)^2 = s^n$ (`det_sq_eq_pow_of_equivalent`).
* *Dimension 2* (the case $\dim Z = 2$ of the proof, over any field of characteristic $\ne 2$): for an orthogonal
  basis $g, h$ with $Q(g) = a \ne 0$, $Q(h) = b \ne 0$, `dim2_equivalent_iff`: for $s \ne 0$,
  $(V, sQ) \cong (V, Q)$ iff $s = x^2 + ab\,y^2$ for some $x, y \in F$, the norm form of the discriminant field
  $K = F(\sqrt{-ab})$ (`dim2_equivalent_of_norm` gives the explicit isometry
  $g \mapsto xg + ay\,h$, $h \mapsto -by\,g + x\,h$).

**Stated, not proved.**
* *n even, $F$ a nonarchimedean local field arising as a completion $F_{\mathfrak p}$ of a number field*
  (`Theorem7_13_even`): the named proposition "$(V, sQ) \cong (V, Q)$ iff $s = x^2 - \delta y^2$", with
  $\delta = (-1)^{n/2}\det(\text{Gram matrix})$, so that $x^2 - \delta y^2$ is the norm form of $K = F(\sqrt{\delta})$
  (all of $F^\times$ when $\delta$ is a square, the case $K = F$). The proof in the book uses the Witt
  decomposition, the classification of anisotropic forms (Thm. 7.5) and Prop. 5.15, none of which is available in this form.

**Not covered.** The archimedean cases, the positivity conditions at the real places, and the global case of
(7.11b) (these go through the Hasse principle, Thm. 7.10). Over a general field the even-$n$ statement is false
for $n \ge 4$, so it is only stated for the completions above.
-/
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import QuadFormsKB.Defs.NumberField
import QuadFormsKB.Citation

open Module

noncomputable section

namespace QuadFormsKB.Shimura2004.Similar

variable {F V : Type*} [Field F] [Invertible (2 : F)] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

/-! ### n odd -/

/-- The associated bilinear form of $Q$ is scaled by $s$ under a linear map $g$ with $Q(gx) = sQ(x)$. -/
theorem associated_comp_eq_smul (s : F) (g : V →ₗ[F] V) (hg : ∀ x, Q (g x) = s * Q x) :
    (QuadraticMap.associated Q).compl₁₂ g g = s • QuadraticMap.associated Q := by
  have h : Q.comp g = s • Q := by
    ext x; simp [hg]
  rw [← QuadraticMap.associated_comp, h, map_smul]

/-- If $(V, sQ) \cong (V, Q)$ and $Q$ is nondegenerate, then $s^n$ is a square, $n = \dim V$: indeed
$\det(G)^2 = s^n$ for the matrix $G$ of the isometry. -/
theorem det_sq_eq_pow_of_equivalent (hQ : (QuadraticMap.associated Q).Nondegenerate) (s : F)
    (h : (s • Q).Equivalent Q) : ∃ d : F, d ^ 2 = s ^ (finrank F V) := by
  obtain ⟨e⟩ := h
  set g : V →ₗ[F] V := e.toLinearEquiv.toLinearMap
  have hg : ∀ x, Q (g x) = s * Q x := fun x => by simpa [g] using e.map_app x
  let b := Module.finBasis F V
  have hcomp := associated_comp_eq_smul s g hg
  have hM : LinearMap.BilinForm.toMatrix b (LinearMap.BilinForm.comp (QuadraticMap.associated Q) g g) =
      s • LinearMap.BilinForm.toMatrix b (QuadraticMap.associated Q) := by
    rw [show LinearMap.BilinForm.comp (QuadraticMap.associated Q) g g =
      (QuadraticMap.associated Q).compl₁₂ g g from rfl, hcomp, map_smul]
  rw [LinearMap.BilinForm.toMatrix_comp b b] at hM
  have hdet := congrArg Matrix.det hM
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Fintype.card_fin] at hdet
  have hne := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hQ
  refine ⟨(LinearMap.toMatrix b b g).det, ?_⟩
  apply mul_right_cancel₀ hne
  rw [← hdet]; ring

/-- **Theorem 7.13, $n$ odd.** For a nondegenerate $(V, Q)$ of odd dimension over a field of characteristic
$\ne 2$ and $s \in F^\times$: $(V, sQ) \cong (V, Q)$ iff $s \in F^{\times 2}$. -/
@[kb "shimura2004" "Thm. 7.13, p. 60 (n odd: (V, sφ) ≅ (V, φ) iff s ∈ F^{×2}, eq. (7.11a))"]
theorem odd_equivalent_iff (hn : Odd (finrank F V)) (hQ : (QuadraticMap.associated Q).Nondegenerate)
    {s : F} (hs : s ≠ 0) : (s • Q).Equivalent Q ↔ IsSquare s := by
  constructor
  · intro h
    obtain ⟨d, hd⟩ := det_sq_eq_pow_of_equivalent hQ s h
    obtain ⟨k, hk⟩ := hn
    rw [hk, pow_succ s, pow_mul s] at hd
    have hk0 : s ^ k ≠ 0 := pow_ne_zero _ hs
    refine ⟨d / s ^ k, ?_⟩
    field_simp
    rw [hd]; ring
  · rintro ⟨b, rfl⟩
    refine ⟨{ LinearEquiv.smulOfNeZero F V b ?_ with map_app' := fun x => ?_ }⟩
    · rintro rfl; exact hs (by simp)
    · simp [QuadraticMap.map_smul, smul_eq_mul]

/-! ### Dimension 2 -/

section Dim2

variable {g h : V} {a b : F}

private theorem Q_comb (hg : Q g = a) (hh : Q h = b) (hgh : QuadraticMap.polar Q g h = 0) (α β : F) :
    Q (α • g + β • h) = α ^ 2 * a + β ^ 2 * b := by
  rw [QuadraticMap.map_add (⇑Q), QuadraticMap.map_smul, QuadraticMap.map_smul,
    QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hgh, hg, hh]
  simp only [smul_eq_mul, mul_zero, add_zero]; ring

private theorem li_pair (ha : a ≠ 0) (hb : b ≠ 0) (hg : Q g = a) (hh : Q h = b)
    (hgh : QuadraticMap.polar Q g h = 0) : LinearIndependent F ![g, h] := by
  rw [LinearIndependent.pair_iff]
  intro α β hαβ
  have h1 := Q_comb hg hh hgh α β
  have hpg : QuadraticMap.polar Q (α • g + β • h) g = α * (2 * a) := by
    rw [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_left,
      QuadraticMap.polar_comm Q h g, hgh]
    have : QuadraticMap.polar Q g g = 2 * a := by
      rw [QuadraticMap.polar_self, hg, nsmul_eq_mul]; norm_num
    rw [this]; simp
  have hph : QuadraticMap.polar Q (α • g + β • h) h = β * (2 * b) := by
    rw [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_left, hgh]
    have : QuadraticMap.polar Q h h = 2 * b := by
      rw [QuadraticMap.polar_self, hh, nsmul_eq_mul]; norm_num
    rw [this]; simp
  have h2 : (2 : F) ≠ 0 := (isUnit_of_invertible (2 : F)).ne_zero
  rw [hαβ, QuadraticMap.polar_zero_left] at hpg hph
  exact ⟨(mul_eq_zero.1 hpg.symm).resolve_right (mul_ne_zero h2 ha),
    (mul_eq_zero.1 hph.symm).resolve_right (mul_ne_zero h2 hb)⟩

/-- **Dimension 2, easy direction.** If $s = x^2 + ab\,y^2 \ne 0$ then
$g \mapsto xg + ay\,h$, $h \mapsto -by\,g + xh$ is an isometry of $(V, sQ)$ onto $(V, Q)$. -/
theorem dim2_equivalent_of_norm (ha : a ≠ 0) (hb : b ≠ 0) (hg : Q g = a) (hh : Q h = b)
    (hgh : QuadraticMap.polar Q g h = 0) (hspan : ∀ z : V, ∃ α β : F, z = α • g + β • h)
    {x y : F} (hs : x ^ 2 + a * b * y ^ 2 ≠ 0) :
    ((x ^ 2 + a * b * y ^ 2) • Q).Equivalent Q := by
  have li := li_pair ha hb hg hh hgh
  have hsp : ⊤ ≤ Submodule.span F (Set.range ![g, h]) := by
    intro z _
    obtain ⟨α, β, rfl⟩ := hspan z
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  let bs := Basis.mk li hsp
  let T : V →ₗ[F] V := bs.constr F ![x • g + (a * y) • h, (-(b * y)) • g + x • h]
  have hb0 : bs 0 = g := by simp [bs]
  have hb1 : bs 1 = h := by simp [bs]
  have hTg : T g = x • g + (a * y) • h := by
    have := bs.constr_basis F ![x • g + (a * y) • h, (-(b * y)) • g + x • h] 0
    rw [hb0] at this
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using this
  have hTh : T h = (-(b * y)) • g + x • h := by
    have := bs.constr_basis F ![x • g + (a * y) • h, (-(b * y)) • g + x • h] 1
    rw [hb1] at this
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using this
  have hT : ∀ α β : F, T (α • g + β • h) =
      (α * x - β * (b * y)) • g + (α * (a * y) + β * x) • h := by
    intro α β
    rw [map_add, map_smul, map_smul, hTg, hTh]
    simp only [smul_add, smul_smul, add_smul]
    module
  have hQ : ∀ z, Q (T z) = (x ^ 2 + a * b * y ^ 2) * Q z := by
    intro z
    obtain ⟨α, β, rfl⟩ := hspan z
    rw [hT, Q_comb hg hh hgh, Q_comb hg hh hgh]
    ring
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    obtain ⟨α, β, rfl⟩ := hspan z
    rw [hT] at hz
    have := (LinearIndependent.pair_iff.mp li) _ _ hz
    obtain ⟨h1, h2⟩ := this
    have hα : α * (x ^ 2 + a * b * y ^ 2) = 0 := by
      linear_combination x * h1 + (b * y) * h2
    have hβ : β * (x ^ 2 + a * b * y ^ 2) = 0 := by
      linear_combination x * h2 - (a * y) * h1
    rw [(mul_eq_zero.mp hα).resolve_right hs, (mul_eq_zero.mp hβ).resolve_right hs]
    simp
  refine ⟨{ toLinearEquiv := LinearEquiv.ofInjectiveEndo T hinj, map_app' := fun z => ?_ }⟩
  change Q (T z) = _
  rw [hQ, smul_apply, smul_eq_mul]

/-- **Dimension 2** (the case $\dim Z = 2$ in the proof of Thm. 7.13). For an orthogonal basis $g, h$ of $V$
with $Q(g) = a \ne 0$, $Q(h) = b \ne 0$ and $s \ne 0$: $(V, sQ) \cong (V, Q)$ iff $s = x^2 + ab\,y^2$ for some
$x, y \in F$, i.e. $s$ is a norm from the discriminant field $K = F(\sqrt{-ab})$ (or $K = F$ when $-ab$ is a
square, where $x^2 + aby^2$ is still the norm form of the algebra $F[t]/(t^2 + ab)$). -/
@[kb "shimura2004" "Thm. 7.13, p. 61 (dim Z = 2: (V, sφ) ≅ (V, φ) iff s is a norm from the discriminant field K)"]
theorem dim2_equivalent_iff (ha : a ≠ 0) (hb : b ≠ 0) (hg : Q g = a) (hh : Q h = b)
    (hgh : QuadraticMap.polar Q g h = 0) (hspan : ∀ z : V, ∃ α β : F, z = α • g + β • h)
    {s : F} (hs : s ≠ 0) :
    (s • Q).Equivalent Q ↔ ∃ x y : F, s = x ^ 2 + a * b * y ^ 2 := by
  constructor
  · rintro ⟨e⟩
    obtain ⟨u, v, huv⟩ := hspan (e g)
    have h1 := e.map_app g
    rw [huv, Q_comb hg hh hgh] at h1
    simp only [smul_apply, hg, smul_eq_mul] at h1
    refine ⟨u, v / a, ?_⟩
    apply mul_right_cancel₀ ha
    have e1 : (u ^ 2 + a * b * (v / a) ^ 2) * a = u ^ 2 * a + v ^ 2 * b := by field_simp
    rw [e1]
    linear_combination -h1
  · rintro ⟨x, y, rfl⟩
    exact dim2_equivalent_of_norm ha hb hg hh hgh hspan hs

end Dim2

/-! ### n even: stated for completions of number fields at finite places -/

open NumberField IsDedekindDomain in
/-- **Theorem 7.13, $n$ even, $F = F_{\mathfrak p}$ nonarchimedean local (stated, not proved).** For the completion
$F_{\mathfrak p}$ of a number field $F$ at a finite place $\mathfrak p$, every even $n = 2m$ and every nondegenerate
$Q$ on $F_{\mathfrak p}^{\,n}$ with Gram matrix $M$ of the polar form $(x, y) \mapsto Q(x+y) - Q(x) - Q(y) = 2\varphi(x, y)$ (its determinant
differs from that of $\varphi$ by the square $4^m$, so the square class below is Shimura's), put
$\delta = (-1)^m \det M$ (the discriminant of $Q$, so $K = F_{\mathfrak p}(\sqrt{\delta})$): for $s \ne 0$,
$(F_{\mathfrak p}^{\,n}, sQ) \cong (F_{\mathfrak p}^{\,n}, Q)$ iff $s = x^2 - \delta y^2$ for some $x, y$, i.e. $s \in
N_{K/F_{\mathfrak p}}(K^\times)$ (equal to $F_{\mathfrak p}^\times$ when $\delta$ is a square). Not proved here. -/
@[kb "shimura2004" "Thm. 7.13, p. 60 (n even, F nonarchimedean local: G = N_{K/F}(K^×), eq. (7.11b))"]
def Theorem7_13_even (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ (m : ℕ) (Q : QuadraticForm (v.adicCompletion F) (Fin (2 * m) → v.adicCompletion F)),
    (QuadraticMap.polarBilin Q).Nondegenerate →
    ∀ s : v.adicCompletion F, s ≠ 0 →
      ((s • Q).Equivalent Q ↔
        ∃ x y : v.adicCompletion F,
          s = x ^ 2 - ((-1) ^ m * (LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Q)).det) * y ^ 2)

end QuadFormsKB.Shimura2004.Similar
