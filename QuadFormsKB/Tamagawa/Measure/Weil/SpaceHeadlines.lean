import QuadFormsKB.Tamagawa.Measure.Weil.ReleaseHeadlines
import QuadFormsKB.Tamagawa.Measure.Weil.RankOneAdelic
import QuadFormsKB.Equiv.Mathlib

/-!
# $\tau(SO(V)) = 2$ for a quadratic space $(V, Q)$ over a number field

**Layer:** number fields. $F$ is a number field, $V$ a finite-dimensional $F$-vector space of dimension
$n = \dim_F V$ and $Q$ a nondegenerate quadratic form on $V$ (Mathlib's `QuadraticForm F V`; nondegenerate means
that its polar bilinear form $B_Q(x, y) = Q(x + y) - Q(x) - Q(y)$ is nondegenerate, `(polarBilin Q).Nondegenerate`).

The headline `tauTwoAll_release_uncond` (ReleaseHeadlines.lean) is stated for integral Gram forms
$Q_0$ = `QuadForm (𝓞 F) n` on $F^n$. This file restates it with the quadratic space $(V, Q)$ as the object.

**Defines**
* **`IntegralModel Q`**: an *integral model* of $(V, Q)$: a basis $b = (b_0,\dots,b_{n-1})$ of $V$ (field `basis`), a
  nonzero $d\in\mathcal O_F$ (fields `scale`, `scale_ne_zero`) and a form $Q_0$ in $n$ variables with coefficients in
  $\mathcal O_F$ (field `form`) such that, in the coordinates of $b$, $Q_0\otimes F = d\cdot Q$ (field `eq`):
  $$Q_0(w_0,\dots,w_{n-1}) = d\cdot Q\Big(\sum_{i<n} w_i b_i\Big)\qquad(w\in F^n).$$
* `soSpace Q` $= SO(V, Q)(F) = \{g\in GL(V) : Q(gx) = Q(x)\ \forall x,\ \det g = 1\}$.
* **`TamagawaNumberTwoSpace Q`**: $(V, Q)$ has an integral model, and every integral model $Q_0$ is nondegenerate with
  $\mathrm{covol}(SO(V)(F), SO(V)(\mathbb A), \mu_{\mathrm{Tam}}) = 2$ (`TamagawaNumberTwoAdelic Q₀`, MuTamSO.lean).

**Proves**
* `IntegralModel.isometryEquiv`: $Q_0\otimes F$ on $F^n$ is isometric to $(V, d\cdot Q)$ (by the coordinates of $b$);
* **`integralModel_nonempty`**: every $(V, Q)$ has an integral model (clear the denominators of the coefficients of $Q$
  in any basis);
* `IntegralModel.nondegenerate`: an integral model of a nondegenerate $Q$ is nondegenerate;
* `soSpace_smul`: $SO(V, d\cdot Q) = SO(V, Q)$ for $d\ne0$; `IntegralModel.soEquiv`: the basis $b$ identifies
  $SO(V, Q)(F)$ with $SO(Q_0\otimes F)(F)$ (`soSub`, the group whose diagonal image is `GammaSOAdele Q₀`);
* **`tauTwo_space_uncond`**: for every number field $F$ and every nondegenerate $(V, Q)$ with $\dim_F V\ge3$,
  `TamagawaNumberTwoSpace Q`: **unconditional**;
* `tauOne_space_rankOne`: for $\dim_F V = 1$, every integral model has covolume $1$ for `muTam` (from
  `covolume_muTam_rankOne`): **unconditional**. Dimension $2$ is not restated here: its measures (`muTamBin`,
  `muTamIso`) are defined for `QuadForm (𝓞 F) 2`, while a model's form has type `QuadForm (𝓞 F) (finrank F V)`.

*Independence of the model* (that the covolume is the same for all integral models, a priori, by a change of basis in
$GL_n(F)$ and the product formula for the scaling) is not proved here; it is not needed, since the statement asserts
the value $2$ for every model.
-/

open MeasureTheory

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField QuadFormsKB.Lattices QuadFormsKB.Tamagawa

variable {F : Type} [Field F] [NumberField F] {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-! ### Integral models -/

/-- **An integral model of a quadratic space** $(V, Q)$ over a number field $F$, $n = \dim_F V$: a basis
$b = (b_0,\dots,b_{n-1})$ of $V$ (`basis`), a nonzero $d\in\mathcal O_F$ (`scale`, `scale_ne_zero`) and a quadratic form
$Q_0$ in $n$ variables with coefficients in $\mathcal O_F$ (`form`) such that $Q_0$, viewed over $F$, is $d\cdot Q$ in the
coordinates of $b$ (`eq`): $Q_0(w) = d\cdot Q(\sum_{i<n} w_i b_i)$ for $w\in F^n$. Every $(V, Q)$ has one
(`integralModel_nonempty`). -/
@[kb "weil1982" "§2.4, p. 23; §3.7, p. 62 (G = SO(Q) for a quadratic space over k, k-structure by a lattice) [unverified page]"]
structure IntegralModel (Q : QuadraticForm F V) where
  /-- The basis $b_0,\dots,b_{n-1}$ of $V$ ($n = \dim_F V$). -/
  basis : Module.Basis (Fin (Module.finrank F V)) F V
  /-- The scaling factor $d\in\mathcal O_F$. -/
  scale : 𝓞 F
  /-- $d\ne0$. -/
  scale_ne_zero : scale ≠ 0
  /-- The integral form $Q_0$ in $n$ variables over $\mathcal O_F$. -/
  form : QuadForm (𝓞 F) (Module.finrank F V)
  /-- $Q_0\otimes F = d\cdot Q$ in the coordinates of $b$. -/
  eq : (form.map (algebraMap (𝓞 F) F)).toQuadraticForm = ((scale : F) • Q).basisRepr basis

/-- **$\tau(SO(V)) = 2$ for a quadratic space** $(V, Q)$ over a number field $F$ (target statement): $(V, Q)$ has an
integral model, and for every integral model $(b, d, Q_0)$ (`IntegralModel Q`) the form $Q_0$ is nondegenerate and
$\mathrm{covol}(SO(V)(F), SO(V)(\mathbb A), \mu_{\mathrm{Tam}}) = 2$ for Weil's Tamagawa measure of $Q_0$
(`TamagawaNumberTwoAdelic`, convergence factors $\lambda_v = 1$). The existence clause makes the statement non-vacuous. -/
@[kb "weil1982" "§2.4, p. 23 (τ(G) = vol(G_𝔸/G_k)); Thm 3.7.1, Thm 4.5.1, p. 109 (τ(SO) = 2) [unverified page]"]
def TamagawaNumberTwoSpace (Q : QuadraticForm F V) : Prop :=
  Nonempty (IntegralModel Q) ∧
    ∀ M : IntegralModel Q, ∃ hM : M.form.Nondegenerate, TamagawaNumberTwoAdelic M.form hM

namespace IntegralModel

variable {Q : QuadraticForm F V} (M : IntegralModel Q)

/-- The value of the base change of the integral form on $F^n$: $Q_0(w) = d\cdot Q(\sum w_i b_i)$. -/
theorem eval_apply (w : Fin (Module.finrank F V) → F) :
    (M.form.map (algebraMap (𝓞 F) F)).eval w = (M.scale : F) * Q (M.basis.equivFun.symm w) := by
  have h := congrArg (fun q => q w) M.eq
  simp only [QuadForm.toQuadraticForm_apply, QuadraticMap.basisRepr_apply,
    smul_apply, smul_eq_mul] at h
  rw [h, Module.Basis.equivFun_symm_apply]

/-- The scale is nonzero in $F$. -/
theorem scale_ne_zero' : (M.scale : F) ≠ 0 := by
  intro h
  exact M.scale_ne_zero (IsFractionRing.injective (𝓞 F) F (h.trans (map_zero (algebraMap (𝓞 F) F)).symm))

/-- The polar form of the base change of $Q_0$ in coordinates. -/
theorem polar_apply (u v : Fin (Module.finrank F V) → F) :
    QuadraticMap.polar (M.form.map (algebraMap (𝓞 F) F)).toQuadraticForm u v =
      (M.scale : F) * QuadraticMap.polar Q (M.basis.equivFun.symm u) (M.basis.equivFun.symm v) := by
  simp only [QuadraticMap.polar, QuadForm.toQuadraticForm_apply, eval_apply, map_add]
  ring

/-- **An integral model is an isometry** $(F^n, Q_0\otimes F)\cong(V, d\cdot Q)$ (the coordinates of $b$). -/
def isometryEquiv :
    ((M.scale : F) • Q).IsometryEquiv (M.form.map (algebraMap (𝓞 F) F)).toQuadraticForm := by
  rw [M.eq]
  exact QuadraticMap.isometryEquivBasisRepr _ M.basis

/-- **An integral model of a nondegenerate space is nondegenerate:** $\det(C + C^{\mathsf T})\ne0$ for $Q_0$. -/
theorem nondegenerate (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) : M.form.Nondegenerate := by
  intro hdet
  have hdet' : ((M.form.map (algebraMap (𝓞 F) F)).hessian).det = 0 := by
    have : (M.form.map (algebraMap (𝓞 F) F)).hessian = M.form.hessian.map (algebraMap (𝓞 F) F) := by
      simp [QuadForm.hessian, QuadForm.map, Matrix.transpose_map, Matrix.map_add]
    rw [this, show (M.form.hessian.map (algebraMap (𝓞 F) F)).det = algebraMap (𝓞 F) F M.form.hessian.det from
      (RingHom.map_det _ _).symm, hdet, map_zero]
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet'
  refine hv0 ?_
  have hpol : ∀ u : Fin (Module.finrank F V) → F,
      QuadraticMap.polar (M.form.map (algebraMap (𝓞 F) F)).toQuadraticForm u v = 0 := by
    intro u
    have h := QuadForm.polar_eq_hessian F (M.form.map (algebraMap (𝓞 F) F)) u v
    have e : (M.form.map (algebraMap (𝓞 F) F)).hessian.map (algebraMap F F) =
        (M.form.map (algebraMap (𝓞 F) F)).hessian := by ext; simp
    rw [e, hv] at h
    simpa [QuadraticMap.polar, QuadForm.toQuadraticForm_apply] using h
  have hx := (QuadraticForm.nondegenerate_polarBilin_iff _).mp hQ (M.basis.equivFun.symm v) (by
    intro y
    have h := hpol (M.basis.equivFun y)
    rw [M.polar_apply] at h
    simp only [LinearEquiv.symm_apply_apply] at h
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h M.scale_ne_zero'
    · rw [QuadraticMap.polar_comm]; exact h)
  have := congrArg M.basis.equivFun hx
  rwa [LinearEquiv.apply_symm_apply, map_zero] at this

end IntegralModel
/-- Scaling commutes with `ofQuadraticForm` on coefficients. -/
private theorem coeff_ofQuadraticForm_smul {n : ℕ} (a : F) (B : QuadraticForm F (Fin n → F)) (i j : Fin n) :
    (QuadForm.ofQuadraticForm (a • B)).coeff i j = a * (QuadForm.ofQuadraticForm B).coeff i j := by
  simp only [QuadForm.ofQuadraticForm, QuadForm.ofUpper, Matrix.of_apply]
  split_ifs <;> simp [QuadraticMap.polar, mul_sub]

/-- **Every quadratic space over a number field has an integral model** (clear denominators): take any basis $b$ of $V$
and a common denominator $d\in\mathcal O_F\setminus0$ of the coefficients of $Q$ in $b$. -/
@[kb "omeara1963" "§82, p. 220 (lattices on a quadratic space; scaling) [unverified page]"]
theorem integralModel_nonempty (Q : QuadraticForm F V) : Nonempty (IntegralModel Q) := by
  classical
  set b := Module.finBasis F V with hb
  set B := Q.basisRepr b with hB
  set P := QuadForm.ofQuadraticForm B with hP
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 F))
    (fun p : Fin (Module.finrank F V) × Fin (Module.finrank F V) => P.coeff p.1 p.2)
  choose c hc using hd
  have hd0 : ((d : 𝓞 F)) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  have hmap : (QuadForm.ofUpper fun i j => c (i, j)).map (algebraMap (𝓞 F) F) =
      QuadForm.ofQuadraticForm (((d : 𝓞 F) : F) • B) := by
    have hcoef : ∀ i j, ((QuadForm.ofUpper fun i j => c (i, j)).map (algebraMap (𝓞 F) F)).coeff i j =
        (QuadForm.ofQuadraticForm (((d : 𝓞 F) : F) • B)).coeff i j := by
      intro i j
      rw [coeff_ofQuadraticForm_smul]
      by_cases hij : i ≤ j
      · have := hc (i, j)
        simp only [Algebra.smul_def] at this
        have hPc : P.coeff i j = (QuadForm.ofQuadraticForm B).coeff i j := rfl
        simp [QuadForm.map, QuadForm.ofUpper, hij, this, hPc]
      · have h0 : P.coeff i j = 0 := P.upper (not_le.mp hij)
        have h0' : (QuadForm.ofQuadraticForm B).coeff i j = 0 := h0
        simp [QuadForm.map, QuadForm.ofUpper, hij, h0']
    have : ∀ X Y : QuadForm F (Module.finrank F V), (∀ i j, X.coeff i j = Y.coeff i j) → X = Y := by
      intro X Y h
      cases X; cases Y
      simp only [QuadForm.mk.injEq]
      ext i j; exact h i j
    exact this _ _ hcoef
  refine ⟨⟨b, d, hd0, QuadForm.ofUpper fun i j => c (i, j), ?_⟩⟩
  rw [hmap, QuadForm.toQuadraticForm_ofQuadraticForm]
  ext w
  simp [hB, QuadraticMap.basisRepr_apply]

/-! ### $SO(V)$ and the integral models -/

/-- **The special orthogonal group** $SO(V, Q)(F) = \{g\in GL(V) : Q(gx) = Q(x)\ \forall x\in V,\ \det g = 1\}$. -/
@[kb "omeara1963" "§43A, p. 100 (rotations O⁺(V))"]
def soSpace (Q : QuadraticForm F V) : Subgroup (V ≃ₗ[F] V) where
  carrier := {g | (∀ x, Q (g x) = Q x) ∧ LinearMap.det (g : V →ₗ[F] V) = 1}
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨fun x => ?_, ?_⟩
    · show Q (a (b x)) = Q x
      rw [ha1, hb1]
    · have : ((a * b : V ≃ₗ[F] V) : V →ₗ[F] V) = (a : V →ₗ[F] V) * (b : V →ₗ[F] V) := rfl
      rw [this, map_mul, ha2, hb2, one_mul]
  one_mem' := ⟨fun x => rfl, by simp⟩
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    refine ⟨fun x => ?_, ?_⟩
    · have := ha1 (a.symm x)
      rw [LinearEquiv.apply_symm_apply] at this
      exact this.symm
    · have h := congrArg LinearMap.det (show (a : V →ₗ[F] V) * ((a⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V) = 1 from
        LinearMap.ext fun x => a.apply_symm_apply x)
      rw [map_mul, ha2, one_mul, map_one] at h
      exact h

/-- **$SO(V)$ is unchanged by scaling:** $SO(V, d\cdot Q) = SO(V, Q)$ for $d\ne0$. -/
theorem soSpace_smul (Q : QuadraticForm F V) {d : F} (hd : d ≠ 0) : soSpace (d • Q) = soSpace Q := by
  ext g
  have : (∀ x, (d • Q) (g x) = (d • Q) x) ↔ ∀ x, Q (g x) = Q x := by
    simp only [smul_apply, smul_eq_mul]
    exact forall_congr' fun x => ⟨fun h => mul_left_cancel₀ hd h, fun h => by rw [h]⟩
  exact and_congr_left' this

/-- The group isomorphism $GL(V)\cong GL_n(F)$ given by the matrix in the basis $b$. -/
def IntegralModel.glEquiv {Q : QuadraticForm F V} (M : IntegralModel Q) :
    (V ≃ₗ[F] V) ≃* GL (Fin (Module.finrank F V)) F :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv F V).symm.trans
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv M.basis).toMulEquiv)

theorem IntegralModel.glEquiv_val {Q : QuadraticForm F V} (M : IntegralModel Q) (g : V ≃ₗ[F] V) :
    (M.glEquiv g).val = LinearMap.toMatrix M.basis M.basis (g : V →ₗ[F] V) := rfl

theorem IntegralModel.glEquiv_mulVec {Q : QuadraticForm F V} (M : IntegralModel Q) (g : V ≃ₗ[F] V)
    (w : Fin (Module.finrank F V) → F) :
    Matrix.mulVec (M.glEquiv g).val w = M.basis.equivFun (g (M.basis.equivFun.symm w)) := by
  rw [M.glEquiv_val]
  have := LinearMap.toMatrix_mulVec_repr M.basis M.basis (g : V →ₗ[F] V) (M.basis.equivFun.symm w)
  have e : M.basis.repr (M.basis.equivFun.symm w) = w := M.basis.equivFun.apply_symm_apply w
  rw [e] at this
  exact this

theorem IntegralModel.glEquiv_mem {Q : QuadraticForm F V} (M : IntegralModel Q) (g : V ≃ₗ[F] V) :
    (∀ x, Q (g x) = Q x) ↔ M.glEquiv g ∈ orthGroup (M.form.map (algebraMap (𝓞 F) F)) F := by
  have key : (∀ x, Q (g x) = Q x) ↔
      ∀ w, (M.form.map (algebraMap (𝓞 F) F)).eval (Matrix.mulVec (M.glEquiv g).val w) =
        (M.form.map (algebraMap (𝓞 F) F)).eval w := by
    simp only [M.glEquiv_mulVec, M.eval_apply, LinearEquiv.symm_apply_apply]
    constructor
    · intro h w; rw [h]
    · intro h x
      have := h (M.basis.equivFun x)
      simp only [LinearEquiv.symm_apply_apply] at this
      exact mul_left_cancel₀ M.scale_ne_zero' this
  rw [key]
  constructor
  · exact fun h => mem_orthGroup_of_eval _ h
  · intro h w
    exact evalIn_mulVec_of_mem _ h w

/-- **The basis of an integral model identifies $SO(V, Q)(F)$ with $SO(Q_0\otimes F)(F)$** (`soSub`, whose diagonal image
in $SO(V)(\mathbb A)$ is `GammaSOAdele Q₀`): $g\mapsto$ the matrix of $g$ in the basis $b$. -/
def IntegralModel.soEquiv {Q : QuadraticForm F V} (M : IntegralModel Q) :
    soSpace Q ≃* soSub (M.form.map (algebraMap (𝓞 F) F)) F where
  toFun g := ⟨⟨M.glEquiv g.1, (M.glEquiv_mem g.1).mp g.2.1⟩, by
    show (M.glEquiv g.1).val.det = 1
    rw [M.glEquiv_val, LinearMap.det_toMatrix]
    exact g.2.2⟩
  invFun h := ⟨M.glEquiv.symm h.1.1, by
    have h1 : M.glEquiv (M.glEquiv.symm h.1.1) ∈ orthGroup (M.form.map (algebraMap (𝓞 F) F)) F := by
      rw [MulEquiv.apply_symm_apply]; exact h.1.2
    refine ⟨(M.glEquiv_mem _).mpr h1, ?_⟩
    have h2 : (h.1.1 : GL (Fin (Module.finrank F V)) F).val.det = 1 := h.2
    rw [← M.glEquiv.apply_symm_apply h.1.1, M.glEquiv_val, LinearMap.det_toMatrix] at h2
    simpa using h2⟩
  left_inv g := by ext1; simp
  right_inv h := by ext1; ext1; simp
  map_mul' a b := by ext1; ext1; simp

/-- The matrix of $g\in SO(V)$ under `soEquiv` is the matrix of $g$ in the basis $b$. -/
theorem IntegralModel.soEquiv_apply {Q : QuadraticForm F V} (M : IntegralModel Q) (g : soSpace Q) :
    ((M.soEquiv g).1.1 : GL (Fin (Module.finrank F V)) F).val =
      LinearMap.toMatrix M.basis M.basis (g : V ≃ₗ[F] V) := rfl

/-! ### The headline -/

/-- **Weil's theorem $\tau(SO(V)) = 2$ for quadratic spaces** (Weil 1982, Thm 3.7.1 ($n = 3, 4$) and Thm 4.5.1 (the
induction)): for every number field $F$, every finite-dimensional $F$-vector space $V$ with $\dim_F V\ge3$ and every
nondegenerate quadratic form $Q$ on $V$, `TamagawaNumberTwoSpace Q` holds: $(V, Q)$ has an integral model $(b, d, Q_0)$
(`integralModel_nonempty`), and for every one the covolume of $SO(V)(F)$ in $SO(V)(\mathbb A)$ for Weil's Tamagawa
measure of $Q_0$ is $2$. **Unconditional**: from `tauTwoAll_release_uncond`. -/
@[kb "weil1982" "Thm 3.7.1, p. 65; Thm 4.5.1, p. 109 (τ(SO(V)) = 2, dim V ≥ 3) [unverified page]"]
theorem tauTwo_space_uncond (hV : 3 ≤ Module.finrank F V) (Q : QuadraticForm F V)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) : TamagawaNumberTwoSpace Q :=
  ⟨integralModel_nonempty Q, fun M => ⟨M.nondegenerate hQ, tauTwoAll_release_uncond _ hV M.form _⟩⟩

set_option synthInstance.maxHeartbeats 400000 in
/-- **$\tau(SO(V)) = 1$ for quadratic spaces of dimension $1$** (Weil's adelic normalization, $\lambda_v = 1$): for every
number field $F$, every $F$-vector space $V$ with $\dim_F V = 1$ and every nondegenerate quadratic form $Q$ on $V$,
$(V, Q)$ has an integral model (`integralModel_nonempty`), and for every integral model $(b, d, Q_0)$ the form $Q_0$ is
nondegenerate and the covolume of $SO(V)(F)$ in $SO(V)(\mathbb A)$ for Weil's Tamagawa measure `muTam Q₀ hQ 1` is $1$
($SO_1$ is trivial). **Unconditional**: from `covolume_muTam_rankOne` (RankOneAdelic.lean). -/
@[kb "weil1982" "§3.7, p. 62 (rank one: SO_1 trivial, τ = 1) [unverified page]"]
theorem tauOne_space_rankOne (hV : Module.finrank F V = 1) (Q : QuadraticForm F V)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) :
    Nonempty (IntegralModel Q) ∧ ∀ M : IntegralModel Q, ∃ hM : M.form.Nondegenerate,
      covolume (GammaSOAdele M.form) (SOAdele M.form) (muTam M.form hM fun _ => 1) = 1 := by
  have key : ∀ (n : ℕ), n = 1 → ∀ (Q₀ : QuadForm (𝓞 F) n) (hQ₀ : Q₀.Nondegenerate),
      covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ₀ fun _ => 1) = 1 := by
    rintro n rfl Q₀ hQ₀
    exact covolume_muTam_rankOne Q₀ hQ₀
  exact ⟨integralModel_nonempty Q, fun M => ⟨M.nondegenerate hQ, key _ hV M.form _⟩⟩

end QuadFormsKB.Tamagawa.Measure.Weil
