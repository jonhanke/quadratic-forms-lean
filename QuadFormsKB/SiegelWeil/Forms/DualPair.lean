/-
# The dual pair $(\mathrm{Sp}_{2r}, O(V))$: the orthogonal group commutes with the Weil representation of degree $r$

**Layer:** local harmonic analysis at a non-archimedean place (abstract part over any commutative ring), then every finite
place $v$ of a number field $F$, dyadic places included.

**Setting.** $V = K^n$, $n = 2m$, $Q = \langle a_0, \dots, a_{n-1}\rangle$ with $a_i \in K^\times$ (0-based indices), $D_a = \operatorname{diag}(a)$,
$V^r = M_{n\times r}(K)$ (`PtG m r K`; column $j$ is $x_j \in V$), and the Schrödinger operators $\omega(n(B))$, $\omega(m(A))$, $\omega(w)$ of
`Weil/Genus/Model.lean` (`opNg`, `opMg`, `opWg`). **The orthogonal group** $O(V) = \{h \in \mathrm{GL}_n(K) : h^{\mathsf T}D_ah = D_a\}$ (`orthV a`)
acts on functions on $V^r$ by
$$(\rho(h)\Phi)(X) = \Phi(h^{-1}X)\qquad(\texttt{actO}).$$

**Results.**
* `QX_orth`, `BX_orth`: $Q[hX] = Q[X]$ and $\langle hX, hY\rangle = \langle X, Y\rangle$ for $h \in O(V)$.
* `opNg_actO`, `opMg_actO`: $\rho(h)$ commutes with $\omega(n(B))$ and $\omega(m(A))$ on all functions (pointwise).
* `opWg_actO_eq_smul`: $\omega(w)\rho(h) = \mathrm{c}_O(h^{-1})^{-1}\,\rho(h)\,\omega(w)$, where $\mathrm{c}_O(h)$ (`cO`) is the factor by which
  $X \mapsto hX$ scales Haar measure on $V^r$ (change of variables, `integral_comp_mulLeft`).
* **`cO_eq_one`**: $\mathrm{c}_O(h) = 1$ for $h \in O(V)$. *Proof* (no determinant computation): conjugating $\omega(w)^2 = \omega(m(-1))$
  (`opWg_opWg`) by $\rho(h)$ gives $\mathrm{c}_O(h^{-1})^{-2}\omega(m(-1)) = \omega(m(-1))$ on $\rho(h)\Phi_0$, $\Phi_0$ the indicator of the unit box,
  and $\omega(m(-1))$ is invertible; so $\mathrm{c}_O(h^{-1})^2 = 1$ with $\mathrm{c}_O > 0$.
* **`opWg_actO`**: hence $\omega(w)\rho(h) = \rho(h)\omega(w)$ on all functions.
* `SBG_comp_mulLeft`, `endO`, **`weilRepOV`**: $\mathcal S(V^r)$ is stable under $\rho(h)$, and $\rho$ is a representation
  $O(V) \to \operatorname{End}_{\mathbb C}\mathcal S(V^r)$.
* **`weilRepSpV_commute_weilRepOV`** (the dual pair): at every finite place $v$ of a number field $F$, every degree $r$ and every
  $h \in O(V_v)$, $\gamma \in \mathrm{Sp}_{2r}(F_v)$:
  $$\omega_v(\gamma)\,\rho_v(h) = \rho_v(h)\,\omega_v(\gamma)\quad\text{on } \mathcal S(V_v^r),$$
  i.e. `weilRepSpV v a r` and `weilRepOV` give commuting actions of $\mathrm{Sp}_{2r}(F_v)$ and $O(V_v)$, the Weil representation of the dual pair
  $\mathrm{Sp}_{2r}\times O(V)$. *Proof:* the set of $\gamma$ for which this holds is a submonoid containing the generators $n(B)$, $m(A)$, $w$
  (`spGen_closure`). Unconditional.

Sources: Weil, Acta Math. 111 (1964), §14 [unverified]; Kudla, *Notes on the local theta correspondence* (1996), §I.1, Prop. 1.3
(the formulas for $\omega(n(b))$, $\omega(m(a))$, $\omega(w)$ and the linear action of $O(V)$) [unverified].
-/
import QuadFormsKB.Weil.Genus.WeilRepUncond
import QuadFormsKB.Weil.Genus.SiegelTwoCell

open MeasureTheory Matrix
open scoped MatrixGroups NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms.DualPair

open QuadFormsKB.WeilRep QuadFormsKB.WeilRep.Genus QuadFormsKB.WeilRep.LocalData

/-! ### The orthogonal group and its action on functions on $V^r$ -/

section Abstract

variable {K : Type*} [CommRing K] [MeasurableSpace K] {m g : ℕ}

/-- $D_a = \operatorname{diag}(a_0, \dots, a_{n-1})$. -/
abbrev diagA (a : Fin (2 * m) → Kˣ) : Matrix (Fin (2 * m)) (Fin (2 * m)) K := diagonal fun i => (a i : K)

/-- **The orthogonal group** $O(V) = \{h \in \mathrm{GL}_n(K) : h^{\mathsf T}D_ah = D_a\}$ of $Q = \langle a_0, \dots, a_{n-1}\rangle$. -/
@[kb "kudla1996" "§I.1 (the orthogonal group $O(V)$ of the quadratic space $V$) [unverified]"]
def orthV (a : Fin (2 * m) → Kˣ) : Subgroup (GL (Fin (2 * m)) K) where
  carrier := {h | h.1ᵀ * diagA a * h.1 = diagA a}
  one_mem' := by simp
  mul_mem' := by
    intro h h' hh hh'
    simp only [Set.mem_ofPred_eq, Units.val_mul, transpose_mul] at hh hh' ⊢
    calc h'.1ᵀ * h.1ᵀ * diagA a * (h.1 * h'.1)
        = h'.1ᵀ * (h.1ᵀ * diagA a * h.1) * h'.1 := by simp only [Matrix.mul_assoc]
      _ = diagA a := by rw [hh, hh']
  inv_mem' := by
    intro h hh
    simp only [Set.mem_ofPred_eq] at hh ⊢
    have e : h.1 * (h⁻¹).1 = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc (h⁻¹).1ᵀ * diagA a * (h⁻¹).1
        = (h⁻¹).1ᵀ * (h.1ᵀ * diagA a * h.1) * (h⁻¹).1 := by rw [hh]
      _ = (h.1 * (h⁻¹).1)ᵀ * diagA a * (h.1 * (h⁻¹).1) := by
          rw [transpose_mul]; simp only [Matrix.mul_assoc]
      _ = diagA a := by rw [e, transpose_one, Matrix.one_mul, Matrix.mul_one]

lemma mem_orthV {a : Fin (2 * m) → Kˣ} {h : GL (Fin (2 * m)) K} :
    h ∈ orthV a ↔ h.1ᵀ * diagA a * h.1 = diagA a := Iff.rfl

/-- **The linear action of $O(V)$** (indeed of $\mathrm{GL}(V)$) on functions on $V^r$: $(\rho(h)\Phi)(X) = \Phi(h^{-1}X)$. -/
@[kb "kudla1996" "§I.1 ($O(V)$ acts on $S(V^n)$ linearly, $\\omega(h)\\varphi(x) = \\varphi(h^{-1}x)$) [unverified]"]
def actO (h : GL (Fin (2 * m)) K) (Φ : PtG m g K → ℂ) : PtG m g K → ℂ :=
  fun X => Φ ((h⁻¹).1 * X)

lemma actO_mul (h h' : GL (Fin (2 * m)) K) (Φ : PtG m g K → ℂ) : actO (h * h') Φ = actO h (actO h' Φ) := by
  funext X; simp [actO, _root_.mul_inv_rev, Matrix.mul_assoc]

lemma actO_one (Φ : PtG m g K → ℂ) : actO (1 : GL (Fin (2 * m)) K) Φ = Φ := by
  funext X; simp [actO]

/-- $Q[hX] = Q[X]$ for $h \in O(V)$. -/
lemma QX_orth (a : Fin (2 * m) → Kˣ) {h : GL (Fin (2 * m)) K} (hh : h ∈ orthV a) (X : PtG m g K) :
    QX a (h.1 * X) = QX a X := by
  unfold QX
  rw [transpose_mul]
  calc Xᵀ * h.1ᵀ * diagonal (fun i => (a i : K)) * (h.1 * X)
      = Xᵀ * (h.1ᵀ * diagA a * h.1) * X := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [mem_orthV.mp hh]

/-- $\langle X, Y\rangle = 2\operatorname{tr}(X^{\mathsf T}D_aY)$. -/
lemma BX_eq_trace (a : Fin (2 * m) → Kˣ) (X Y : PtG m g K) :
    BX a X Y = 2 * trace (Xᵀ * diagA a * Y) := by
  simp only [BX, trace, diag, Matrix.mul_apply, diagonal_apply, transpose_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

/-- $\langle hX, hY\rangle = \langle X, Y\rangle$ for $h \in O(V)$. -/
lemma BX_orth (a : Fin (2 * m) → Kˣ) {h : GL (Fin (2 * m)) K} (hh : h ∈ orthV a) (X Y : PtG m g K) :
    BX a (h.1 * X) (h.1 * Y) =
      BX a X Y := by
  rw [BX_eq_trace, BX_eq_trace, transpose_mul]
  congr 2
  calc Xᵀ * h.1ᵀ * diagA a * (h.1 * Y)
      = Xᵀ * (h.1ᵀ * diagA a * h.1) * Y := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [mem_orthV.mp hh]

/-- $\langle hX, Y\rangle = \langle X, h^{-1}Y\rangle$ for $h \in O(V)$. -/
lemma BX_orth_left (a : Fin (2 * m) → Kˣ) {h : GL (Fin (2 * m)) K} (hh : h ∈ orthV a) (X Y : PtG m g K) :
    BX a (h.1 * X) Y =
      BX a X ((h⁻¹).1 * Y) := by
  conv_lhs => rw [show Y = h.1 * ((h⁻¹).1 * Y) by
    rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]]
  exact BX_orth a hh _ _

variable {D : LocalData K} {a : Fin (2 * m) → Kˣ}

/-- $\rho(h)$ commutes with $\omega(n(B))$ (pointwise, every function). -/
theorem opNg_actO {h : GL (Fin (2 * m)) K} (hh : h ∈ orthV a) (B : Matrix (Fin g) (Fin g) K) (Φ : PtG m g K → ℂ) :
    opNg D a B (actO h Φ) = actO h (opNg D a B Φ) := by
  funext X
  simp only [opNg, actO, QX_orth a ((orthV a).inv_mem hh)]

/-- $\rho(h)$ commutes with $\omega(m(A))$ (pointwise, every function). -/
theorem opMg_actO (h : GL (Fin (2 * m)) K) (A : GL (Fin g) K) (Φ : PtG m g K → ℂ) :
    opMg D a A (actO h Φ) = actO h (opMg D a A Φ) := by
  funext X
  simp only [opMg, actO, Matrix.mul_assoc]

end Abstract

/-! ### The Fourier transform: change of variables and the modulus of $X \mapsto hX$ -/

section NonArch

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
  [MeasurableSpace K] [BorelSpace K] {m g : ℕ}

/-- **Left multiplication by $h \in \mathrm{GL}_n(K)$** as a topological additive automorphism of $V^r = M_{n\times r}(K)$. -/
def mulLeftHomeo (h : GL (Fin (2 * m)) K) : PtG m g K ≃ₜ+ PtG m g K where
  toFun X := h.1 * X
  invFun X := (h⁻¹).1 * X
  left_inv X := by simp [← Matrix.mul_assoc]
  right_inv X := by simp [← Matrix.mul_assoc]
  map_add' X Y := Matrix.mul_add _ X Y
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

variable (m g) in
/-- **The modulus of $X \mapsto hX$ on $V^r$**: the factor by which `mulLeftHomeo h` scales Haar measure. -/
def cO (h : GL (Fin (2 * m)) K) : ℝ≥0 := addEquivAddHaarChar (mulLeftHomeo (g := g) h)

lemma cO_pos (h : GL (Fin (2 * m)) K) : 0 < cO m g h := addEquivAddHaarChar_pos _

/-- **Change of variables for $X \mapsto hX$:** $\int F(hX)\,d\mu(X) = \mathrm{c}_O(h)^{-1}\int F\,d\mu$ for a regular Haar measure $\mu$. -/
lemma integral_comp_mulLeft (μ : Measure (PtG m g K)) [μ.IsAddHaarMeasure] [μ.Regular]
    (h : GL (Fin (2 * m)) K) (F : PtG m g K → ℂ) :
    ∫ X, F (h.1 * X) ∂μ = ((cO m g h : ℝ)⁻¹ : ℝ) • ∫ X, F X ∂μ := by
  have hc := addEquivAddHaarChar_smul_map μ (mulLeftHomeo (g := g) h)
  have e : ∫ X, F X ∂μ = ∫ X, F X ∂((cO m g h) • μ.map (mulLeftHomeo (g := g) h)) := by
    rw [cO, hc]
  rw [e, integral_smul_nnreal_measure]
  have hm : ∫ X, F X ∂(μ.map (mulLeftHomeo (g := g) h)) =
      ∫ X, F (h.1 * X) ∂μ :=
    (mulLeftHomeo (g := g) h).toHomeomorph.toMeasurableEquiv.measurableEmbedding.integral_map F
  rw [hm, NNReal.smul_def, smul_smul, inv_mul_cancel₀ (by exact_mod_cast (cO_pos (m := m) (g := g) h).ne'), one_smul]

variable {D : LocalData K} [D.μ.IsAddHaarMeasure] {a : Fin (2 * m) → Kˣ}

/-- $\omega(w)\rho(h) = \mathrm{c}_O(h^{-1})^{-1}\rho(h)\omega(w)$ for $h \in O(V)$ (every function). -/
lemma opWg_actO_eq_smul {h : GL (Fin (2 * m)) K} (hh : h ∈ orthV a) (Φ : PtG m g K → ℂ) :
    opWg D a (actO h Φ) = ((((cO m g h⁻¹ : ℝ)⁻¹ : ℝ) : ℂ)) • actO h (opWg D a Φ) := by
  funext Y
  simp only [opWg, actO, Pi.smul_apply, smul_eq_mul]
  have key := integral_comp_mulLeft (muG D m g) h⁻¹
    (fun X => Φ X * (D.ψ (BX a (h.1 * X) Y) : ℂ))
  have e : ∀ X : PtG m g K, h.1 *
      ((h⁻¹).1 * X) = X := fun X => by
    rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  simp only [e] at key
  rw [key, Complex.real_smul]
  simp only [BX_orth_left a hh]
  ring

/-- The indicator of the unit box of $V^r$. -/
def boxInd (K : Type*) [NontriviallyNormedField K] (m g : ℕ) : PtG m g K → ℂ :=
  ptG (fun _ _ => (Metric.closedBall (0 : K) 1).indicator fun _ => (1 : ℂ))

lemma boxInd_zero : boxInd K m g 0 = 1 := by
  simp [boxInd, ptG]

/-- $\mathcal S(V^r)$ (locally constant, compactly supported) is stable under $X \mapsto hX$. -/
lemma SBG_comp_mulLeft {Φ : PtG m g K → ℂ} (hΦ : Φ ∈ SBG K m g)
    (A B : Matrix (Fin (2 * m)) (Fin (2 * m)) K) (hAB : B * A = 1) : (fun X => Φ (A * X)) ∈ SBG K m g := by
  obtain ⟨R, ε, hε, hR, hinv⟩ := hΦ
  set NA : ℝ := ∑ j, ∑ k, ‖A j k‖ with hNA
  set NB : ℝ := ∑ j, ∑ k, ‖B j k‖ with hNB
  have hNA0 : 0 ≤ NA := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hNB0 : 0 ≤ NB := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hleft : ∀ (M : Matrix (Fin (2 * m)) (Fin (2 * m)) K) (X : PtG m g K) {r N : ℝ}, 0 ≤ r → 0 ≤ N →
      (∀ i j, ‖X i j‖ ≤ r) → (∀ j k, ‖M j k‖ ≤ N) → ∀ i k, ‖(M * X) i k‖ ≤ N * r := by
    intro M X r N hr hN hX hM i k
    rw [Matrix.mul_apply]
    refine norm_sum_le_ult _ _ (mul_nonneg hN hr) fun j _ => ?_
    rw [norm_mul]
    exact mul_le_mul (hM i j) (hX j k) (norm_nonneg _) hN
  refine ⟨NB * |R|, ε / (NA + 1), by positivity, fun X hX i j => ?_, fun X H hH => ?_⟩
  · have h1 : ∀ i j, ‖(A * X) i j‖ ≤ |R| := fun i j => (hR _ hX i j).trans (le_abs_self _)
    have h2 := hleft B (A * X) (abs_nonneg R) hNB0 h1 (entry_le_sum B) i j
    rwa [← Matrix.mul_assoc, hAB, Matrix.one_mul] at h2
  · show Φ (A * (X + H)) = Φ (A * X)
    rw [Matrix.mul_add]
    refine hinv _ _ fun i k => ?_
    have h3 := hleft A H (by positivity) hNA0 hH (entry_le_sum A) i k
    refine h3.trans ?_
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith

lemma actO_mem_Sg (hS : D.S = SBK K) (h : GL (Fin (2 * m)) K) {Φ : PtG m g K → ℂ} (hΦ : Φ ∈ Sg D m g) :
    actO h Φ ∈ Sg D m g := by
  rw [mem_Sg_iff hS] at hΦ ⊢
  exact SBG_comp_mulLeft hΦ _ h.1
    (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])

/-- **The Haar modulus of $X \mapsto hX$ is $1$ for $h \in O(V)$** (from $\omega(w)^2 = \omega(m(-1))$; see the module docstring). -/
@[kb "weil1964" "§14 (the Fourier transform on $V^r$ commutes with $O(V)$) [unverified]"]
theorem cO_eq_one (hD : D.IsModel) (hS : D.S = SBK K) {h : GL (Fin (2 * m)) K} (hh : h ∈ orthV a) :
    cO m g h = 1 := by
  -- work with `h⁻¹ ∈ O(V)`, whose inverse is `h`
  have hh' : h⁻¹ ∈ orthV a := (orthV a).inv_mem hh
  set c : ℂ := ((((cO m g h : ℝ)⁻¹ : ℝ) : ℂ)) with hc
  have hW : ∀ Φ : PtG m g K → ℂ, opWg D a (actO h⁻¹ Φ) = c • actO h⁻¹ (opWg D a Φ) := fun Φ => by
    rw [opWg_actO_eq_smul hh', inv_inv]
  have h0 : (Metric.closedBall (0 : K) 1).indicator (fun _ => (1 : ℂ)) ∈ D.S := by
    rw [hS]; exact indicator_closedBall_mem_SBK 0 one_pos
  have hΦ0 : boxInd K m g ∈ Sg D m g := ptG_mem_Sg (fun _ _ => h0)
  set Ψ := actO h⁻¹ (boxInd K m g) with hΨ
  have hΨS : Ψ ∈ Sg D m g := actO_mem_Sg hS _ hΦ0
  have h1 := opWg_opWg (a := a) hD hΨS
  rw [hΨ, hW, opWg_smul, hW, smul_smul, opWg_opWg hD hΦ0, ← opMg_actO, ← hΨ] at h1
  -- `h1 : (c * c) • ω(m(-1))Ψ = ω(m(-1))Ψ`; apply `ω(m(-1))` once more
  have h2 := congrArg (opMg D a (-1)) h1
  rw [opMg_smul, ← opMg_mul hD, neg_one_mul, neg_neg, opMg_one hD] at h2
  have h3 := congrFun h2 0
  simp only [Pi.smul_apply, smul_eq_mul, hΨ, actO, Matrix.mul_zero, boxInd_zero, mul_one] at h3
  -- `h3 : c * c = 1`
  have hpos : 0 < (cO m g h : ℝ) := by exact_mod_cast cO_pos h
  have hr : ((cO m g h : ℝ)⁻¹) * ((cO m g h : ℝ)⁻¹) = 1 := by
    rw [hc] at h3; exact_mod_cast h3
  have : (cO m g h : ℝ)⁻¹ = 1 := by nlinarith [inv_pos.mpr hpos]
  have : (cO m g h : ℝ) = 1 := by rw [← inv_inv (cO m g h : ℝ), this, inv_one]
  exact_mod_cast this

/-- **$\rho(h)$ commutes with the Fourier transform $\omega(w)$** for $h \in O(V)$ (every function). -/
@[kb "weil1964" "§14 (the Fourier transform on $V^r$ commutes with $O(V)$) [unverified]"]
theorem opWg_actO (hD : D.IsModel) (hS : D.S = SBK K) {h : GL (Fin (2 * m)) K} (hh : h ∈ orthV a)
    (Φ : PtG m g K → ℂ) : opWg D a (actO h Φ) = actO h (opWg D a Φ) := by
  rw [opWg_actO_eq_smul hh, cO_eq_one hD hS ((orthV a).inv_mem hh)]
  simp

variable (hS : D.S = SBK K)

/-- $\rho(h)$ as an endomorphism of $\mathcal S(V^r)$. -/
def endO (h : GL (Fin (2 * m)) K) : Module.End ℂ (Sg D m g) where
  toFun Φ := ⟨actO h Φ, actO_mem_Sg hS h Φ.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma endO_apply (h : GL (Fin (2 * m)) K) (Φ : Sg D m g) :
    ((endO hS h Φ : Sg D m g) : PtG m g K → ℂ) = actO h Φ := rfl

variable (a) in
/-- **The linear representation of $O(V)$ on $\mathcal S(V^r)$**, $\rho(h)\Phi = \Phi(h^{-1}\,\cdot)$. -/
@[kb "kudla1996" "§I.1 ($O(V)$ acts on $S(V^n)$ by $\\omega(h)\\varphi(x) = \\varphi(h^{-1}x)$) [unverified]"]
def weilRepOV : orthV a →* Module.End ℂ (Sg D m g) where
  toFun h := endO hS h
  map_one' := by ext Φ X; simp [actO_one]
  map_mul' h h' := by ext Φ X; simp [actO_mul]

end NonArch

/-! ### The dual pair at a finite place -/

section Place

open IsDedekindDomain NumberField QuadFormsKB.Analysis

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

variable {m : ℕ}

instance instHaarV : (localDataV v).μ.IsAddHaarMeasure := inferInstanceAs ((selfDualV v).IsAddHaarMeasure)

/-- **The Weil representation of the dual pair $\mathrm{Sp}_{2r}\times O(V)$ at a finite place** (dyadic included): for
$Q = \langle a_0, \dots, a_{n-1}\rangle$ over $F_v$, $n = 2m$, every degree $r$, every $h \in O(V_v)$ and every $\gamma \in \mathrm{Sp}_{2r}(F_v)$,
$\omega_v(\gamma)\rho_v(h) = \rho_v(h)\omega_v(\gamma)$ on $\mathcal S(V_v^r)$ (`weilRepSpV`, `weilRepOV`). Unconditional. -/
@[kb "weil1964" "§14 and Kudla 1996 §I.1 (the Weil representation of the dual pair $\\mathrm{Sp}(W)\\times O(V)$) [unverified]"]
theorem weilRepSpV_commute_weilRepOV (a : Fin (2 * m) → (Fv)ˣ) (r : ℕ) (h : orthV a) (γ : Sp r Fv) :
    weilRepSpV v a r γ * weilRepOV (D := localDataV v) a rfl h =
      weilRepOV (D := localDataV v) a rfl h * weilRepSpV v a r γ := by
  have hγ : γ ∈ Submonoid.closure (Set.range (spGen (g := r) (k := Fv))) := by
    rw [spGen_closure]; trivial
  induction hγ using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rcases i with ⟨B, hB⟩ | A | ⟨⟩
    · show weilRepSpV v a r (spN B hB) * _ = _ * weilRepSpV v a r (spN B hB)
      rw [weilRepSpV_spN]
      ext Φ X
      simp only [Module.End.mul_apply, endN_apply _ _ hB, weilRepOV, MonoidHom.coe_mk, OneHom.coe_mk]
      show opNg _ a (B.map ⇑(RingHom.id Fv)) (actO h.1 Φ.1) X =
        actO h.1 ((endN (isGLModel_V v a r) (RingHom.id Fv) B Φ : Sg (localDataV v) m r) : PtG m r Fv → ℂ) X
      rw [endN_apply _ _ hB, RingHom.coe_id, Matrix.map_id]
      exact congrFun (opNg_actO h.2 B Φ.1) X
    · show weilRepSpV v a r (spM A) * _ = _ * weilRepSpV v a r (spM A)
      rw [weilRepSpV_spM]
      ext Φ X
      simp only [Module.End.mul_apply, endM_apply, weilRepOV, MonoidHom.coe_mk, OneHom.coe_mk]
      exact congrFun (opMg_actO h.1 _ Φ.1) X
    · show weilRepSpV v a r spW * _ = _ * weilRepSpV v a r spW
      rw [weilRepSpV_spW]
      ext Φ X
      simp only [Module.End.mul_apply, endW_apply, weilRepOV, MonoidHom.coe_mk, OneHom.coe_mk]
      exact congrFun (opWg_actO (isModel_V v) rfl h.2 Φ.1) X
  | one => simp
  | mul x y _ _ hx hy => rw [map_mul, mul_assoc, hy, ← mul_assoc, hx, mul_assoc]

end Place

end QuadFormsKB.SiegelWeil.Forms.DualPair
