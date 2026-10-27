/-
# Representation, splitting and cancellation for diagonal forms

General-field lemmas behind the corollaries of Hasse–Minkowski (Serre, *A Course in Arithmetic*,
IV §3.2 Cor. 1 and §3.3 Thm. 9). $F$ is a field, $K$ any field with `Algebra F K`.

**Main results.**
* `QuadForm.representsIn_iff_isotropicIn_orthSum`: for nondegenerate $Q$ over $F$ and $c \in F^\times$,
  $Q$ represents $c$ over $K$ iff $Q \perp \langle -c \rangle$ is isotropic over $K$
  (Serre IV §1.6 Cor. 1; every characteristic).
* `QuadForm.nondegenerate_orthSum`, `QuadForm.nondegenerate_diag`.
* `QuadForm.exists_isometric_diag_cons` (characteristic $0$): if nondegenerate $Q$ represents
  $b \ne 0$ over $F$, then $Q \cong \langle b, \alpha_1, \dots, \alpha_m \rangle$ over $F$ with all
  $\alpha_i \ne 0$ (Serre IV §1.6 Cor. 1; Lam I Cor. 2.4).
* `QuadForm.isometricIn_of_diag_cons` (Witt cancellation of a first diagonal entry) and its converse
  `QuadForm.isometricIn_diag_cons_of`.
-/
import QuadFormsKB.Witt.Bridge
import QuadFormsKB.Literature.LocalGlobal.FieldGeneral

open Module QuadraticMap Matrix

namespace QuadFormsKB.QuadForm

variable {F : Type*} [Field F] {k m n : ℕ}

section General

variable (K : Type*) [Field K] [Algebra F K]

/-- $Q(s\vec{x}) = s^2 Q(\vec{x})$. -/
theorem evalIn_smul (Q : QuadForm F n) (s : K) (x : Fin n → K) :
    Q.evalIn K (s • x) = s ^ 2 * Q.evalIn K x := by
  rw [← toQuadraticFormIn_apply, ← toQuadraticFormIn_apply, QuadraticMap.map_smul, smul_eq_mul, pow_two]

/-- Values of a diagonal form: $\langle a_0, \dots, a_{n-1} \rangle(\vec{x}) = \sum_i a_i x_i^2$. -/
theorem evalIn_diag (a : Fin n → F) (x : Fin n → K) :
    (diag a).evalIn K x = ∑ i, algebraMap F K (a i) * x i ^ 2 := by
  simp only [evalIn, diag]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp; ring
  · intro j _ hj; simp [Matrix.diagonal_apply_ne _ (Ne.symm hj)]
  · simp

/-- **Isometric forms represent the same values:** if $Q(P\vec{x}) = Q'(\vec{x})$ and $Q'$ represents
$c$ over $K$, so does $Q$. -/
theorem representsIn_of_isometricIn {Q Q' : QuadForm F n} (h : Q.IsometricIn K Q') {c : F}
    (hc : Q'.RepresentsIn K c) : Q.RepresentsIn K c := by
  obtain ⟨P, -, hP⟩ := h
  obtain ⟨x, hx⟩ := hc
  exact ⟨P *ᵥ x, by rw [hP, hx]⟩

theorem isometricIn_refl (Q : QuadForm F n) : Q.IsometricIn K Q :=
  ⟨1, by simp, fun x => by rw [Matrix.one_mulVec]⟩

theorem isometricIn_symm {Q Q' : QuadForm F n} (h : Q.IsometricIn K Q') : Q'.IsometricIn K Q := by
  rw [isometricIn_iff_equivalent] at h ⊢
  exact h.symm

theorem isometricIn_trans {Q Q' Q'' : QuadForm F n} (h : Q.IsometricIn K Q')
    (h' : Q'.IsometricIn K Q'') : Q.IsometricIn K Q'' := by
  rw [isometricIn_iff_equivalent] at h h' ⊢
  exact h'.trans h

/-- Nondegeneracy (over the base field) persists over $K$: a vector $\vec{x} \ne 0$ in $K^n$ has
$b_Q(\vec{x}, \vec{w}) \ne 0$ for some $\vec{w} \in K^n$. -/
theorem exists_polar_ne_zero {Q : QuadForm F n} (hQ : Q.Nondegenerate) {x : Fin n → K}
    (hx : x ≠ 0) : ∃ w, polar (Q.toQuadraticFormIn K) x w ≠ 0 := by
  have := (QuadraticForm.nondegenerate_polarBilin_iff _).mp
    (nondegenerate_polarBilin_toQuadraticFormIn K hQ)
  by_contra! h
  exact hx (this x h)

/-- The polar form of $Q_1 \perp Q_2$ is the sum of the polar forms on the two blocks. -/
theorem polar_orthSum (Q₁ : QuadForm F m) (Q₂ : QuadForm F n) (x y : Fin (m + n) → K) :
    polar ((orthSum Q₁ Q₂).toQuadraticFormIn K) x y =
      polar (Q₁.toQuadraticFormIn K) (fun a => x (Fin.castAdd n a)) (fun a => y (Fin.castAdd n a)) +
      polar (Q₂.toQuadraticFormIn K) (fun b => x (Fin.natAdd m b))
        (fun b => y (Fin.natAdd m b)) := by
  have e1 : (fun a => (x + y) (Fin.castAdd n a)) =
      (fun a => x (Fin.castAdd n a)) + fun a => y (Fin.castAdd n a) := rfl
  have e2 : (fun b => (x + y) (Fin.natAdd m b)) =
      (fun b => x (Fin.natAdd m b)) + fun b => y (Fin.natAdd m b) := rfl
  simp only [polar, toQuadraticFormIn_apply, evalIn_orthSum, e1, e2]
  ring

end General

/-- **Nondegeneracy from the polar form over $F$:** if no nonzero $\vec{x} \in F^n$ is
$b_Q$-orthogonal to all of $F^n$, then $\det(C + C^{\mathsf T}) \ne 0$. -/
theorem nondegenerate_of_polar {Q : QuadForm F n}
    (h : ∀ x : Fin n → F, (∀ y, polar (Q.toQuadraticFormIn F) x y = 0) → x = 0) :
    Q.Nondegenerate := by
  intro hdet
  obtain ⟨x, hx, hxH⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  apply hx
  apply h
  intro y
  rw [polar, toQuadraticFormIn_apply, toQuadraticFormIn_apply, toQuadraticFormIn_apply,
    polar_eq_hessian]
  have : Q.hessian.map (algebraMap F F) = Q.hessian := by ext; simp
  rw [this, Matrix.dotProduct_mulVec, hxH, zero_dotProduct]

/-- **The orthogonal sum of nondegenerate forms is nondegenerate.** -/
theorem nondegenerate_orthSum {Q₁ : QuadForm F m} {Q₂ : QuadForm F n} (h₁ : Q₁.Nondegenerate)
    (h₂ : Q₂.Nondegenerate) : (orthSum Q₁ Q₂).Nondegenerate := by
  apply nondegenerate_of_polar
  intro x hx
  have e₁ := (QuadraticForm.nondegenerate_polarBilin_iff _).mp
    (nondegenerate_polarBilin_toQuadraticFormIn F h₁)
  have e₂ := (QuadraticForm.nondegenerate_polarBilin_iff _).mp
    (nondegenerate_polarBilin_toQuadraticFormIn F h₂)
  have hl : (fun a => x (Fin.castAdd n a)) = 0 := e₁ _ fun w => by
    have := hx (Fin.append w 0)
    rw [polar_orthSum] at this
    have h0 : (fun b => (Fin.append w (0 : Fin n → F)) (Fin.natAdd m b)) = 0 := by
      funext b; simp
    have h1 : (fun a => (Fin.append w (0 : Fin n → F)) (Fin.castAdd n a)) = w := by
      funext a; simp
    rwa [h0, h1, polar_zero_right, add_zero] at this
  have hr : (fun b => x (Fin.natAdd m b)) = 0 := e₂ _ fun w => by
    have := hx (Fin.append 0 w)
    rw [polar_orthSum] at this
    have h0 : (fun a => (Fin.append (0 : Fin m → F) w) (Fin.castAdd n a)) = 0 := by
      funext a; simp
    have h1 : (fun b => (Fin.append (0 : Fin m → F) w) (Fin.natAdd m b)) = w := by
      funext b; simp
    rwa [h0, h1, polar_zero_right, zero_add] at this
  funext i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · exact congrFun hl a
  · exact congrFun hr b

/-- **A diagonal form with nonzero entries is nondegenerate** (characteristic $0$): its Hessian is
$\operatorname{diag}(2a_0, \dots, 2a_{n-1})$. -/
@[kb "cassels1978" "Ch. 2, Lemma 1.5, p. 14"]
theorem nondegenerate_diag [CharZero F] {a : Fin n → F} (ha : ∀ i, a i ≠ 0) :
    (diag a).Nondegenerate := by
  unfold Nondegenerate hessian diag
  simp only [Matrix.diagonal_transpose, Matrix.diagonal_add, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => by
    rw [← two_mul]; exact mul_ne_zero two_ne_zero (ha i)

section General

variable (K : Type*) [Field K] [Algebra F K]

/-- **Representation as isotropy** (Serre IV §1.6, Cor. 1; every characteristic): for a nondegenerate
form $Q$ over $F$ and $c \in F^\times$, $Q$ represents $c$ over $K$ iff
$Q \perp \langle -c \rangle$ is isotropic over $K$.

*Proof.* If $Q(\vec{x}) = c$ then $(\vec{x}, 1)$ is a zero. Conversely let $(\vec{x}, t) \ne 0$ with
$Q(\vec{x}) = c t^2$. If $t \ne 0$, $Q(t^{-1}\vec{x}) = c$. If $t = 0$, then $\vec{x} \ne 0$ is isotropic;
by nondegeneracy some $\vec{w}$ has $b_Q(\vec{x}, \vec{w}) \ne 0$, and
$Q(s\vec{x} + \vec{w}) = s\, b_Q(\vec{x}, \vec{w}) + Q(\vec{w})$ takes the value $c$. -/
@[kb "cassels1978" "Ch. 2, Lemma 2.3, p. 16"]
theorem representsIn_iff_isotropicIn_orthSum {Q : QuadForm F n} (hQ : Q.Nondegenerate) (c : F) :
    Q.RepresentsIn K c ↔ (orthSum Q (diag ![-c])).IsotropicIn K := by
  have hev : ∀ x : Fin (n + 1) → K, (orthSum Q (diag ![-c])).evalIn K x =
      Q.evalIn K (fun a => x (Fin.castAdd 1 a)) - algebraMap F K c * x (Fin.natAdd n 0) ^ 2 := by
    intro x
    rw [evalIn_orthSum, evalIn_diag]
    simp
    ring
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨Fin.append x (fun _ => 1), fun h0 => ?_, ?_⟩
    · have := congrFun h0 (Fin.natAdd n 0)
      simp [Fin.append_right] at this
    · rw [hev]
      simp [Fin.append_left, Fin.append_right, hx]
  · rintro ⟨y, hy0, hy⟩
    rw [hev] at hy
    set x : Fin n → K := fun a => y (Fin.castAdd 1 a) with hxdef
    set t := y (Fin.natAdd n 0) with htdef
    by_cases ht : t = 0
    · have hx0 : x ≠ 0 := by
        intro hx0
        apply hy0
        funext i
        refine Fin.addCases (fun a => ?_) (fun b => ?_) i
        · exact congrFun hx0 a
        · rw [Subsingleton.elim b 0]; exact ht
      rw [ht] at hy
      have hQx : Q.toQuadraticFormIn K x = 0 := by
        rw [toQuadraticFormIn_apply]; simpa using hy
      obtain ⟨w, hw⟩ := exists_polar_ne_zero K hQ hx0
      set q := Q.toQuadraticFormIn K
      refine ⟨((algebraMap F K c - q w) / polar q x w) • x + w, ?_⟩
      rw [← toQuadraticFormIn_apply]
      have hadd : ∀ u v, q (u + v) = q u + q v + polar q u v := fun u v => by
        rw [polar]; ring
      rw [hadd, QuadraticMap.map_smul, hQx, polar_smul_left, smul_eq_mul, smul_eq_mul]
      field_simp
      ring
    · refine ⟨t⁻¹ • x, ?_⟩
      rw [evalIn_smul]
      have : Q.evalIn K x = algebraMap F K c * t ^ 2 := by
        rw [← sub_eq_zero]; exact hy
      rw [this]
      field_simp

/-- The coordinate split $K^{m+1} \cong K^1 \times K^m$, $\vec{x} \mapsto ((x_0), (x_1, \dots, x_m))$. -/
def finConsLinearEquiv (m : ℕ) : (Fin (m + 1) → K) ≃ₗ[K] (Fin 1 → K) × (Fin m → K) where
  toFun x := (fun _ => x 0, Fin.tail x)
  invFun p := Fin.cons (p.1 0) p.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := Fin.cons_self_tail x
  right_inv p := by
    ext i
    · simp [Subsingleton.elim i 0]
    · simp

/-- $\langle b, \alpha_1, \dots, \alpha_m \rangle \cong \langle b \rangle \perp \langle \alpha_1, \dots,
\alpha_m \rangle$ over $K$, as Mathlib forms. -/
noncomputable def isometryEquivDiagCons (b : F) (α : Fin m → F) :
    ((diag (Fin.cons b α)).toQuadraticFormIn K).IsometryEquiv
      (((diag ![b]).toQuadraticFormIn K).prod ((diag α).toQuadraticFormIn K)) :=
  { finConsLinearEquiv K m with
    map_app' := fun x => by
      simp [QuadraticMap.prod_apply, toQuadraticFormIn_apply, evalIn_diag, Fin.sum_univ_succ,
        finConsLinearEquiv]
      rfl }

/-- **Witt cancellation of a first diagonal entry** (characteristic $0$): if
$\langle b, \alpha \rangle \cong \langle b, \beta \rangle$ over $K$ with $b \ne 0$ and all
$\alpha_i \ne 0$, then $\langle \alpha \rangle \cong \langle \beta \rangle$ over $K$. -/
theorem isometricIn_of_diag_cons [CharZero F] {b : F} (hb : b ≠ 0) {α β : Fin m → F}
    (hα : ∀ i, α i ≠ 0) (h : (diag (Fin.cons b α)).IsometricIn K (diag (Fin.cons b β))) :
    (diag α).IsometricIn K (diag β) := by
  rw [isometricIn_iff_equivalent] at h ⊢
  obtain ⟨g⟩ := h
  have hb' : ∀ i, (![b] : Fin 1 → F) i ≠ 0 := fun i => by simpa [Subsingleton.elim i 0] using hb
  have := QuadraticForm.equivalent_of_prod_equivalent_prod_of_nondegenerate
    (nondegenerate_polarBilin_toQuadraticFormIn K (nondegenerate_diag hb'))
    (nondegenerate_polarBilin_toQuadraticFormIn K (nondegenerate_diag hα))
    ⟨(isometryEquivDiagCons K b α).symm.trans (g.symm.trans (isometryEquivDiagCons K b β))⟩
  exact this.symm

/-- **Adding a common first diagonal entry preserves isometry.** -/
theorem isometricIn_diag_cons_of (b : F) {α β : Fin m → F}
    (h : (diag α).IsometricIn K (diag β)) :
    (diag (Fin.cons b α)).IsometricIn K (diag (Fin.cons b β)) := by
  rw [isometricIn_iff_equivalent] at h ⊢
  obtain ⟨g⟩ := h
  exact ⟨(isometryEquivDiagCons K b β).trans
    ((QuadraticMap.IsometryEquiv.prod (QuadraticMap.IsometryEquiv.refl _) g).trans (isometryEquivDiagCons K b α).symm)⟩

end General

/-- **An orthogonal basis with a prescribed first vector:** for a symmetric bilinear form $B$ on
$V$ ($\dim V = d + 1$, $2$ invertible) and $x$ with $B(x,x) \ne 0$, there is a $B$-orthogonal basis
$v_0 = x, v_1, \dots, v_d$. (The first step of Mathlib's `LinearMap.BilinForm.exists_orthogonal_basis`.) -/
theorem exists_orthogonal_basis_cons {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Invertible (2 : K)] {B : LinearMap.BilinForm K V} (hB : B.IsSymm)
    {x : V} (hx : B x x ≠ 0) {d : ℕ} (hd : finrank K V = d + 1) :
    ∃ v : Module.Basis (Fin (d + 1)) K V, B.IsOrthoᵢ v ∧ v 0 = x := by
  rw [← Submodule.finrank_add_eq_of_isCompl
    (LinearMap.BilinForm.isCompl_span_singleton_orthogonal hx).symm,
    finrank_span_singleton (ne_zero_of_map hx)] at hd
  let B' : LinearMap.BilinForm K ((K ∙ x).orthogonalBilin B) := B.domRestrict₁₂ ((K ∙ x).orthogonalBilin B) ((K ∙ x).orthogonalBilin B)
  obtain ⟨v', hv₁⟩ := LinearMap.BilinForm.exists_orthogonal_basis (B := B')
    (LinearMap.IsSymm.domRestrict (LinearMap.BilinForm.isSymm_iff.mp hB)
      ((K ∙ x).orthogonalBilin B))
  let v'' := v'.reindex (finCongr (Nat.succ.inj hd))
  let b :=
    Module.Basis.mkFinCons x v''
      (by
        rintro c y hy hc
        rw [add_eq_zero_iff_neg_eq] at hc
        rw [← hc, Submodule.neg_mem_iff] at hy
        have := (LinearMap.BilinForm.isCompl_span_singleton_orthogonal hx).disjoint
        rw [Submodule.disjoint_def] at this
        have := this (c • x) (Submodule.smul_mem _ _ <| Submodule.mem_span_singleton_self _) hy
        exact (smul_eq_zero.1 this).resolve_right fun h => hx <| h.symm ▸ map_zero _)
      (by
        intro y
        refine ⟨-B x y / B x x, fun z hz => ?_⟩
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
        rw [map_smul, LinearMap.smul_apply, map_add, map_smul, smul_eq_mul, smul_eq_mul,
          div_mul_cancel₀ _ hx, add_neg_cancel, mul_zero])
  refine ⟨b, ?_, by simp [b]⟩
  rw [Module.Basis.coe_mkFinCons]
  intro j i
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> intro hij <;>
    simp only [Function.onFun, Fin.cons_zero, Fin.cons_succ, Function.comp_apply]
  · exact (hij rfl).elim
  · rw [← hB.eq]
    exact (v'' j).prop _ (Submodule.mem_span_singleton_self x)
  · exact (v'' i).prop _ (Submodule.mem_span_singleton_self x)
  · have hij' : j ≠ i := fun h => hij (by rw [h])
    have := (LinearMap.isOrthoᵢ_def (B := B')).mp hv₁ _ _ (show (finCongr (Nat.succ.inj hd)).symm j ≠ (finCongr (Nat.succ.inj hd)).symm i
      from fun h => hij' ((finCongr _).symm.injective h))
    simp only [v'', B', LinearMap.domRestrict₁₂_apply] at this
    convert this using 3 <;> simp only [v'', Module.Basis.reindex_apply] <;> rfl

section Diag

/-- The bilinear form $\tfrac12 b_Q(\vec{x}, \vec{y}) = \vec{x}^{\mathsf T} (\tfrac12 H) \vec{y}$ of $Q$
over $F$. -/
noncomputable def halfBilin (Q : QuadForm F n) : LinearMap.BilinForm F (Fin n → F) :=
  Matrix.toLinearMap₂' F ((1 / 2 : F) • Q.hessian)

theorem halfBilin_apply (Q : QuadForm F n) (x y : Fin n → F) :
    Q.halfBilin x y = x ⬝ᵥ ((1 / 2 : F) • Q.hessian) *ᵥ y :=
  Matrix.toLinearMap₂'_apply' _ x y

theorem halfBilin_isSymm (Q : QuadForm F n) : Q.halfBilin.IsSymm := by
  have hMt : ((1 / 2 : F) • Q.hessian).transpose = (1 / 2 : F) • Q.hessian := by
    simp [QuadForm.hessian, Matrix.transpose_add, add_comm]
  refine ⟨fun x y => ?_⟩
  simp only [halfBilin_apply]
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hMt, dotProduct_comm]

variable [CharZero F]

theorem halfBilin_self (Q : QuadForm F n) (y : Fin n → F) : Q.halfBilin y y = Q.evalIn F y := by
  have h := QuadForm.polar_eq_hessian F Q y y
  have h2 : y + y = (2 : F) • y := by rw [two_smul]
  rw [h2, evalIn_smul] at h
  rw [halfBilin_apply, Matrix.smul_mulVec, dotProduct_smul]
  have h3 : Q.hessian.map (algebraMap F F) = Q.hessian := by ext; simp
  rw [h3] at h
  rw [← h, smul_eq_mul]; ring

/-- **Diagonalisation along an orthogonal basis:** if $\vec{w}_0, \dots, \vec{w}_{n-1}$ is a basis of
$F^n$, orthogonal for $\tfrac12 b_Q$, and $Q$ is nondegenerate, then all $Q(\vec{w}_i) \ne 0$ and
$Q \cong \langle Q(\vec{w}_0), \dots, Q(\vec{w}_{n-1}) \rangle$ over $F$. (The second half of the
proof of `FieldGen.exists_isometric_diag`.) -/
theorem isometric_diag_of_basis (Q : QuadForm F n) (hQ : Q.Nondegenerate)
    (w : Module.Basis (Fin n) F (Fin n → F)) (hwo : ∀ i j, i ≠ j → Q.halfBilin (w i) (w j) = 0) :
    (∀ i, Q.evalIn F (w i) ≠ 0) ∧ Q.IsometricIn F (diag fun i => Q.evalIn F (w i)) := by
  classical
  have hMdet : ((1 / 2 : F) • Q.hessian).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hQ
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [← halfBilin_self] at hi
    have hz : Q.halfBilin (w i) = 0 := by
      apply w.ext
      intro j
      by_cases hij : i = j
      · subst hij; simpa using hi
      · simpa using hwo i j hij
    apply hMdet
    rw [← Matrix.exists_vecMul_eq_zero_iff]
    refine ⟨w i, w.ne_zero i, ?_⟩
    funext j
    have := LinearMap.congr_fun hz (Pi.single j 1)
    rw [halfBilin_apply, Matrix.dotProduct_mulVec, dotProduct_single] at this
    simpa using this
  · refine ⟨(Pi.basisFun F (Fin n)).toMatrix w, ?_, ?_⟩
    · rw [← Module.Basis.det_apply]; exact Module.Basis.isUnit_det _ _
    · intro x
      have hmv : ((Pi.basisFun F (Fin n)).toMatrix w).mulVec x = ∑ j, x j • w j := by
        funext i
        simp [Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply, mul_comm]
      rw [← halfBilin_self, hmv, evalIn_diag]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_eq_single i, ← halfBilin_self]
      · simp; ring
      · intro j _ hj; simp [hwo j i hj]
      · simp

/-- **Splitting off a represented value** (Serre IV §1.6, Cor. 1; Lam I Cor. 2.4; characteristic
$0$): if a nondegenerate form $Q$ in $m + 1$ variables over $F$ represents $b \ne 0$ over $F$, then
$Q \cong \langle b, \alpha_1, \dots, \alpha_m \rangle$ over $F$ with all $\alpha_i \ne 0$. -/
theorem exists_isometric_diag_cons {Q : QuadForm F (m + 1)} (hQ : Q.Nondegenerate) {b : F}
    (hb : b ≠ 0) (hr : Q.RepresentsIn F b) :
    ∃ α : Fin m → F, (∀ i, α i ≠ 0) ∧ Q.IsometricIn F (diag (Fin.cons b α)) := by
  let _ : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  obtain ⟨x, hx⟩ := hr
  have hxb : Q.evalIn F x = b := by simpa using hx
  obtain ⟨w, hwo, hw0⟩ := exists_orthogonal_basis_cons (halfBilin_isSymm Q)
    (x := x) (by rw [halfBilin_self, hxb]; exact hb) (Module.finrank_fin_fun F)
  obtain ⟨hne, hiso⟩ := isometric_diag_of_basis Q hQ w fun i j hij => hwo hij
  refine ⟨fun i => Q.evalIn F (w i.succ), fun i => hne _, ?_⟩
  convert hiso using 2
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [hw0, hxb]
  · simp

end Diag

end QuadFormsKB.QuadForm
