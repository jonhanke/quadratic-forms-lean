/-
# O'Meara §101C: Lemma 101:11

**Layer:** $F$ a number field, $V = F^n$ with a nondegenerate `Q : QuadForm F n`; completions $F_\mathfrak p$
(`v.adicCompletion F`, finite spots) and $F_w$ (`w.Completion`, infinite spots). A *regular ternary subspace
representing $X$* over a field $K \supseteq F$ is `RegTernaryRepresents Q K X` (`Sec101Named.lean`); orthogonality is
for the Hessian pairing `qbil Q K` ($x^{\mathsf T}H_Qy$, twice O'Meara's $B$).

**Proves**
* transport lemmas: `regTernaryRepresents_of_map` (image under a linear map that is isometric on the subspace),
  `regTernaryRepresents_iff_of_isometricIn` (invariance under isometry), `regTernaryRepresents_cons`
  ($W \subseteq \langle\alpha\rangle$ gives $W \subseteq \langle\gamma\rangle \perp \langle\alpha\rangle$),
  `exists_orth_anisotropic` (a regular subspace of dimension $3 < n$ has an anisotropic vector orthogonal to it),
  `regTernaryRepresents_split` (Witt's theorem: if $U \perp y$ with $Q(y) = \gamma$ and $V \cong \langle\gamma\rangle
  \perp \langle\alpha\rangle$, then $\langle\alpha\rangle$ has a regular ternary subspace isometric to $U$).
-/
import QuadFormsKB.Literature.OMeara.Sec101TwelveFull
import QuadFormsKB.Literature.OMeara.Sec72Approx
import QuadFormsKB.Literature.OMeara.Sec63C
import QuadFormsKB.Literature.OMeara.Sec95Local
import QuadFormsKB.Literature.LocalGlobal.NumberFieldMain
import QuadFormsKB.Witt.Extension
import QuadFormsKB.Lattices.SAVectorsAnisotropic
import QuadFormsKB.Literature.OMeara.Sec101ElevenLocal

open NumberField IsDedekindDomain Module
open scoped Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F]

section Transport

variable (K : Type) [Field K] [Algebra F K] [CharZero K]

theorem qbil_eq_evalIn {n : ℕ} (Q : QuadForm F n) (x y : Fin n → K) :
    qbil Q K x y = Q.evalIn K (x + y) - Q.evalIn K x - Q.evalIn K y :=
  (QuadForm.polar_eq_hessian K Q x y).symm

/-- **Image of a regular subspace** under a linear map $f$ that is isometric on it: if $U \subseteq K^n$ is regular for
$Q$ and $Q'(f(x)) = Q(x)$ for $x \in U$, then $f(U)$ is regular for $Q'$ and has the dimension of $U$ ($f$ is
injective on $U$ because $U$ is regular). -/
theorem regular_map {n m : ℕ} (Q : QuadForm F n) (Q' : QuadForm F m)
    (U : Submodule K (Fin n → K)) (hUreg : ∀ x ∈ U, (∀ y ∈ U, qbil Q K x y = 0) → x = 0)
    (f : (Fin n → K) →ₗ[K] (Fin m → K)) (hf : ∀ x ∈ U, Q'.evalIn K (f x) = Q.evalIn K x) :
    finrank K (U.map f) = finrank K U ∧ ∀ x ∈ U.map f, (∀ y ∈ U.map f, qbil Q' K x y = 0) → x = 0 := by
  have hb : ∀ x ∈ U, ∀ y ∈ U, qbil Q' K (f x) (f y) = qbil Q K x y := by
    intro x hx y hy
    rw [qbil_eq_evalIn, qbil_eq_evalIn, ← map_add, hf _ (U.add_mem hx hy), hf x hx, hf y hy]
  have hinj : Function.Injective (f.domRestrict U) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h0 : f x = 0 := hx
    refine Subtype.ext (hUreg x x.2 fun y hy => ?_)
    rw [← hb x x.2 y hy, h0]
    simp [qbil]
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hinj]
  · rintro _ ⟨x, hx, rfl⟩ hz
    have : x = 0 := hUreg x hx fun y hy => by
      rw [← hb x hx y hy]
      exact hz _ ⟨y, hy, rfl⟩
    rw [this, map_zero]

/-- **Image of a regular ternary subspace representing $X$** under a linear map $f$ that is isometric on it. -/
theorem regTernaryRepresents_of_map {n m : ℕ} (Q : QuadForm F n) (Q' : QuadForm F m) (X : Finset F)
    (U : Submodule K (Fin n → K)) (hU3 : finrank K U = 3)
    (hUreg : ∀ x ∈ U, (∀ y ∈ U, qbil Q K x y = 0) → x = 0)
    (hUrep : ∀ a ∈ X, ∃ x ∈ U, Q.evalIn K x = algebraMap F K a)
    (f : (Fin n → K) →ₗ[K] (Fin m → K)) (hf : ∀ x ∈ U, Q'.evalIn K (f x) = Q.evalIn K x) :
    RegTernaryRepresents Q' K X := by
  obtain ⟨h3, hreg⟩ := regular_map K Q Q' U hUreg f hf
  refine ⟨U.map f, h3.trans hU3, hreg, ?_⟩
  intro a ha
  obtain ⟨x, hx, hxa⟩ := hUrep a ha
  exact ⟨f x, ⟨x, hx, rfl⟩, by rw [hf x hx, hxa]⟩

/-- Unpacking `RegTernaryRepresents` with the pairing `qbil`. -/
theorem RegTernaryRepresents.elim {n : ℕ} {Q : QuadForm F n} {X : Finset F} (h : RegTernaryRepresents Q K X) :
    ∃ U : Submodule K (Fin n → K), finrank K U = 3 ∧ (∀ x ∈ U, (∀ y ∈ U, qbil Q K x y = 0) → x = 0) ∧
      ∀ a ∈ X, ∃ x ∈ U, Q.evalIn K x = algebraMap F K a := h

/-- **Invariance under isometry:** if $Q \cong Q'$ over $K$, then $Q$ has a regular ternary subspace representing $X$
over $K$ iff $Q'$ has. -/
theorem regTernaryRepresents_iff_of_isometricIn {n : ℕ} {Q Q' : QuadForm F n} (h : Q.IsometricIn K Q')
    (X : Finset F) : RegTernaryRepresents Q K X ↔ RegTernaryRepresents Q' K X := by
  obtain ⟨P, hP, hPx⟩ := h
  have hPinv : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  constructor
  · intro hR
    obtain ⟨U, hU3, hreg, hrep⟩ := hR.elim K
    refine regTernaryRepresents_of_map K Q Q' X U hU3 hreg hrep (Matrix.toLin' P⁻¹) fun x _ => ?_
    rw [Matrix.toLin'_apply, ← hPx, Matrix.mulVec_mulVec, hPinv, Matrix.one_mulVec]
  · intro hR
    obtain ⟨U, hU3, hreg, hrep⟩ := hR.elim K
    exact regTernaryRepresents_of_map K Q' Q X U hU3 hreg hrep (Matrix.toLin' P) fun x _ => by
      rw [Matrix.toLin'_apply, hPx]

/-- The linear map $z \mapsto (0, z)$, $K^m \to K^{m+1}$. -/
def consZero (m : ℕ) : (Fin m → K) →ₗ[K] (Fin (m + 1) → K) where
  toFun z := Fin.cons 0 z
  map_add' x y := by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' c x := by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem evalIn_diag_cons_consZero {m : ℕ} (γ : F) (α : Fin m → F) (z : Fin m → K) :
    (QuadForm.diag (Fin.cons γ α : Fin (m + 1) → F)).evalIn K (consZero K m z) = (QuadForm.diag α).evalIn K z := by
  rw [QuadForm.evalIn_diag, QuadForm.evalIn_diag, Fin.sum_univ_succ]
  simp [consZero]

/-- **Embedding in an orthogonal sum:** a regular ternary subspace of $\langle\alpha\rangle$ representing $X$ is one
of $\langle\gamma\rangle \perp \langle\alpha\rangle$. -/
theorem regTernaryRepresents_cons {m : ℕ} (γ : F) (α : Fin m → F) (X : Finset F)
    (h : RegTernaryRepresents (QuadForm.diag α) K X) :
    RegTernaryRepresents (QuadForm.diag (Fin.cons γ α : Fin (m + 1) → F)) K X := by
  obtain ⟨U, hU3, hreg, hrep⟩ := h.elim K
  exact regTernaryRepresents_of_map K _ _ X U hU3 hreg hrep (consZero K m) fun x _ =>
    evalIn_diag_cons_consZero K γ α x

/-- Nondegeneracy of the Hessian pairing over any $K \supseteq F$. -/
theorem eq_zero_of_qbil_eq_zero' {n : ℕ} {Q : QuadForm F n} (hQ : Q.Nondegenerate) {z : Fin n → K}
    (hz : ∀ y, qbil Q K z y = 0) : z = 0 := by
  have hdet : (Q.hessian.map (algebraMap F K)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).mpr hQ
  exact (Matrix.nondegenerate_of_det_ne_zero hdet).eq_zero_of_ortho hz

/-- **An anisotropic vector orthogonal to a regular ternary subspace** (O'Meara 42:? splitting $V = U \perp U^\perp$):
if $U \subseteq K^n$ is a regular subspace of dimension $3 < n$, some $e \perp U$ has $Q(e) \ne 0$. (Otherwise $Q$
vanishes on $U^\perp$, so $U^\perp$ is orthogonal to itself and to $U$, hence to $U + U^\perp = K^n$, and $U^\perp =
0$.) -/
theorem exists_orth_anisotropic {n : ℕ} {Q : QuadForm F n} (hQ : Q.Nondegenerate) (hn : 4 ≤ n)
    (U : Submodule K (Fin n → K)) (hU3 : finrank K U = 3)
    (hUreg : ∀ x ∈ U, (∀ y ∈ U, qbil Q K x y = 0) → x = 0) :
    ∃ e : Fin n → K, Q.evalIn K e ≠ 0 ∧ ∀ u ∈ U, qbil Q K e u = 0 := by
  set B : LinearMap.BilinForm K (Fin n → K) := Matrix.toBilin' (Q.hessian.map (algebraMap F K)) with hBdef
  have hB : ∀ x y, B x y = qbil Q K x y := fun x y => by
    rw [hBdef, Matrix.toBilin'_apply']; rfl
  have hrefl : B.IsRefl := fun x y h => by rw [hB] at h ⊢; rw [qbil_comm]; exact h
  have hsep : ∀ x : U, (∀ y : U, B.restrict U x y = 0) → x = 0 := by
    intro x hx
    refine Subtype.ext (hUreg x x.2 fun y hy => ?_)
    have : B x y = 0 := hx ⟨y, hy⟩
    rwa [hB] at this
  have hres : (B.restrict U).Nondegenerate := by
    refine ⟨hsep, fun y hy => hsep y fun x => ?_⟩
    have : B x y = 0 := hy x
    exact hrefl _ _ this
  have hc := LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hrefl hres
  by_contra hcon
  have hQ0 : ∀ z ∈ B.orthogonal U, Q.evalIn K z = 0 := by
    intro z hz
    by_contra h0
    refine hcon ⟨z, h0, fun u hu => ?_⟩
    rw [qbil_comm, ← hB]
    exact hz u hu
  have hbot : B.orthogonal U = ⊥ := by
    refine eq_bot_iff.mpr fun z hz => (Submodule.mem_bot K).mpr ?_
    refine eq_zero_of_qbil_eq_zero' K hQ fun y => ?_
    have hy : y ∈ U ⊔ B.orthogonal U := by rw [hc.sup_eq_top]; trivial
    obtain ⟨u, hu, z', hz', rfl⟩ := Submodule.mem_sup.mp hy
    rw [qbil_add_right]
    have h1 : qbil Q K z u = 0 := by rw [qbil_comm, ← hB]; exact hz u hu
    have h2 : qbil Q K z z' = 0 := by
      rw [qbil_eq_evalIn, hQ0 _ hz, hQ0 _ hz', hQ0 _ ((B.orthogonal U).add_mem hz hz')]
      ring
    rw [h1, h2, add_zero]
  have htop : U = ⊤ := by
    have := hc.sup_eq_top
    rwa [hbot, sup_bot_eq] at this
  have := finrank_top K (Fin n → K)
  rw [← htop, hU3, finrank_fin_fun] at this
  omega

/-- The linear map $z \mapsto (z_1, \dots, z_m)$, $K^{m+1} \to K^m$ (drop the coordinate $0$). -/
def dropZero (m : ℕ) : (Fin (m + 1) → K) →ₗ[K] (Fin m → K) := LinearMap.funLeft K K Fin.succ

theorem qbil_diag_single_zero {m : ℕ} (γ : F) (α : Fin m → F) (z : Fin (m + 1) → K) :
    qbil (QuadForm.diag (Fin.cons γ α : Fin (m + 1) → F)) K z (Pi.single 0 1) = z 0 * (2 * algebraMap F K γ) := by
  simp only [qbil, QuadForm.hessian, QuadForm.diag, Matrix.diagonal_transpose, Matrix.diagonal_add]
  simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, Pi.single_apply, apply_ite (algebraMap F K), mul_ite]
  left; ring

/-- **Witt's theorem at a spot** (O'Meara 1973, proof of 101:11, p. 293: "$W_\mathfrak p \cong U_\mathfrak p$ by
Witt's theorem"): let $V \cong \langle\gamma\rangle \perp \langle\alpha\rangle$ over $K$, and let $U \subseteq V$ be a
regular ternary subspace representing $X$ with $U \perp y$, $Q(y) = \gamma$. Then $\langle\alpha\rangle$ has a regular
ternary subspace representing $X$. (Extend $y \mapsto e_0$ to an isometry $\rho$ (42:17); $\rho(U) \perp e_0$ lies in
$\langle\alpha\rangle$.) -/
theorem regTernaryRepresents_split {m : ℕ} {Q : QuadForm F (m + 1)} {γ : F} (hγ : γ ≠ 0) {α : Fin m → F}
    (hα : ∀ i, α i ≠ 0) (hiso : Q.IsometricIn K (QuadForm.diag (Fin.cons γ α))) (X : Finset F)
    (U : Submodule K (Fin (m + 1) → K)) (hU3 : finrank K U = 3)
    (hUreg : ∀ x ∈ U, (∀ y ∈ U, qbil Q K x y = 0) → x = 0)
    (hUrep : ∀ a ∈ X, ∃ x ∈ U, Q.evalIn K x = algebraMap F K a)
    (y : Fin (m + 1) → K) (hy : Q.evalIn K y = algebraMap F K γ) (hyU : ∀ u ∈ U, qbil Q K y u = 0) :
    RegTernaryRepresents (QuadForm.diag α) K X := by
  set Q' : QuadForm F (m + 1) := QuadForm.diag (Fin.cons γ α) with hQ'
  have hQ'nd : Q'.Nondegenerate := QuadForm.nondegenerate_diag fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hγ
    · simpa using hα j
  let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  obtain ⟨P, hP, hPx⟩ := hiso
  have hPinv : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  have hPi : ∀ x, Q'.evalIn K (P⁻¹ *ᵥ x) = Q.evalIn K x := fun x => by
    rw [← hPx, Matrix.mulVec_mulVec, hPinv, Matrix.one_mulVec]
  set y' := P⁻¹ *ᵥ y with hy'
  set e0 : Fin (m + 1) → K := Pi.single 0 1 with he0
  have hy'Q : Q'.evalIn K y' = algebraMap F K γ := by rw [hy', hPi, hy]
  have he0Q : Q'.evalIn K e0 = algebraMap F K γ := by
    rw [hQ', QuadForm.evalIn_diag, Fin.sum_univ_succ]
    simp [he0]
  have hy'0 : y' ≠ 0 := by
    intro h
    rw [h, ← qk_apply, map_zero] at hy'Q
    exact hγ ((map_eq_zero _).mp hy'Q.symm)
  -- Witt's theorem: extend `y' ↦ e0`.
  let eW := LinearEquiv.toSpanNonzeroSingleton K (Fin (m + 1) → K) y' hy'0
  let σ : (K ∙ y') →ₗ[K] (Fin (m + 1) → K) := (LinearMap.toSpanSingleton K _ e0).comp eW.symm.toLinearMap
  have hσ : ∀ t : K, σ (eW t) = t • e0 := fun t => by simp [σ]
  have heW : ∀ t : K, ((eW t : K ∙ y') : Fin (m + 1) → K) = t • y' := fun t => by simp [eW]
  have hσi : Function.Injective σ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    obtain ⟨t, rfl⟩ := eW.surjective w
    rw [hσ] at hw
    have ht : t = 0 := by
      have := congrFun hw 0
      simpa [he0] using this
    rw [ht, map_zero]
  have hσQ : ∀ w, qk Q' K (σ w) = qk Q' K w := fun w => by
    obtain ⟨t, rfl⟩ := eW.surjective w
    rw [hσ, heW, QuadraticMap.map_smul, QuadraticMap.map_smul, qk_apply, qk_apply, he0Q, hy'Q]
  obtain ⟨ρ, hρ⟩ := QuadraticForm.exists_isometryEquiv_extend_of_associated (qk Q' K)
    (nondegenerate_qk_of Q' K hQ'nd) σ hσi hσQ
  have hρy : ρ y' = e0 := by
    have := hρ (eW 1)
    rw [hσ, one_smul] at this
    rw [← this, heW, one_smul]
  have hρQ : ∀ x, Q'.evalIn K (ρ x) = Q'.evalIn K x := fun x => by
    rw [← qk_apply, ← qk_apply]; exact ρ.map_app x
  let f : (Fin (m + 1) → K) →ₗ[K] (Fin m → K) :=
    (dropZero K m).comp (ρ.toLinearEquiv.toLinearMap.comp (Matrix.toLin' P⁻¹))
  refine regTernaryRepresents_of_map K Q (QuadForm.diag α) X U hU3 hUreg hUrep f fun u hu => ?_
  set z := ρ (P⁻¹ *ᵥ u) with hz
  have hz0 : z 0 = 0 := by
    have hb : qbil Q' K z e0 = qbil Q K u y := by
      rw [← hρy, qbil_eq_evalIn, qbil_eq_evalIn, hz, ← map_add, hρQ, hρQ, hρQ, hy', ← Matrix.mulVec_add, hPi, hPi,
        hPi]
    rw [qbil_comm Q K u y, hyU u hu, he0, hQ', qbil_diag_single_zero] at hb
    have h2 : (2 : K) * algebraMap F K γ ≠ 0 := mul_ne_zero two_ne_zero ((map_ne_zero _).mpr hγ)
    exact (mul_eq_zero.mp hb).resolve_right h2
  have hfz : f u = dropZero K m z := rfl
  have hzQ : Q'.evalIn K z = Q.evalIn K u := by rw [hz, hρQ, hPi]
  rw [hfz, ← hzQ, hQ', QuadForm.evalIn_diag, QuadForm.evalIn_diag, Fin.sum_univ_succ]
  simp [dropZero, hz0]

end Transport

/-! ### The global splitting step -/

section Global

/-- Regular ternary subspace data at a spot, together with an anisotropic vector orthogonal to it. -/
private theorem exists_orth_data {m : ℕ} {Q : QuadForm F (m + 1)} (hQ : Q.Nondegenerate) (hm : 3 ≤ m)
    (K : Type) [Field K] [Algebra F K] [CharZero K] {X : Finset F} (h : RegTernaryRepresents Q K X) :
    ∃ e : Fin (m + 1) → K, Q.evalIn K e ≠ 0 ∧ ∃ U : Submodule K (Fin (m + 1) → K), finrank K U = 3 ∧
      (∀ x ∈ U, (∀ y ∈ U, qbil Q K x y = 0) → x = 0) ∧ (∀ a ∈ X, ∃ x ∈ U, Q.evalIn K x = algebraMap F K a) ∧
      ∀ u ∈ U, qbil Q K e u = 0 := by
  obtain ⟨U, hU3, hreg, hrep⟩ := h.elim K
  obtain ⟨e, he, horth⟩ := exists_orth_anisotropic K hQ (by omega) U hU3 hreg
  exact ⟨e, he, U, hU3, hreg, hrep, horth⟩

/-- From the data at a spot and $\gamma \in \gamma_\mathfrak p\dot K^2$: the complement $\langle\alpha\rangle$ of
$\langle\gamma\rangle$ has a regular ternary subspace representing $X$. -/
private theorem split_at {m : ℕ} {Q : QuadForm F (m + 1)} {γ : F} (hγ : γ ≠ 0) {α : Fin m → F}
    (hα : ∀ i, α i ≠ 0) (K : Type) [Field K] [Algebra F K] [CharZero K]
    (hiso : Q.IsometricIn F (QuadForm.diag (Fin.cons γ α))) {X : Finset F} (e : Fin (m + 1) → K)
    (he : Q.evalIn K e ≠ 0) (hsq : IsSquare (algebraMap F K γ / Q.evalIn K e))
    (hU : ∃ U : Submodule K (Fin (m + 1) → K), finrank K U = 3 ∧
      (∀ x ∈ U, (∀ y ∈ U, qbil Q K x y = 0) → x = 0) ∧ (∀ a ∈ X, ∃ x ∈ U, Q.evalIn K x = algebraMap F K a) ∧
      ∀ u ∈ U, qbil Q K e u = 0) :
    RegTernaryRepresents (QuadForm.diag α) K X := by
  obtain ⟨U, hU3, hreg, hrep, horth⟩ := hU
  obtain ⟨s, hs⟩ := hsq
  refine regTernaryRepresents_split K hγ hα (FieldGen.isometricIn_of_base K hiso) X U hU3 hreg hrep (s • e) ?_
    fun u hu => by rw [qbil_smul_left, horth u hu, mul_zero]
  rw [QuadForm.evalIn_smul, sq, ← hs, div_mul_cancel₀ _ he]

/-- **The global splitting step** of O'Meara's proof of 101:11 (p. 293): let $T$ be a finite set of finite spots such
that at each $\mathfrak p \in T$ and at each infinite spot some regular ternary subspace $U_\mathfrak p$ of $V_\mathfrak p$
represents $X$, and $\dim V \ge 4$. Write $V_\mathfrak p = \langle\gamma_\mathfrak p\rangle \perp U_\mathfrak p \perp
\cdots$; by weak approximation (`OMeara.exists_approx_sq`) there is $\gamma \in \gamma_\mathfrak p\dot F_\mathfrak p^2$
at all these spots; $V$ represents $\gamma$ (63:18 at the finite spots, `S95.exists_Q_eq_of_four_le`, and 66:3,
`represents_iff_everywhere_nf`), so $V \cong \langle\gamma\rangle \perp \langle\alpha\rangle$ over $F$, and by Witt's
theorem $\langle\alpha\rangle_\mathfrak p$ contains a copy of $U_\mathfrak p$ at each $\mathfrak p \in T$ and each infinite
spot. -/
theorem exists_split_global {m : ℕ} (Q : QuadForm F (m + 1)) (hQ : Q.Nondegenerate) (hm : 3 ≤ m) (X : Finset F)
    (T : Finset (HeightOneSpectrum (𝓞 F)))
    (hT : ∀ v ∈ T, RegTernaryRepresents Q (v.adicCompletion F) X)
    (hw : ∀ w : InfinitePlace F, RegTernaryRepresents Q w.Completion X) :
    ∃ γ : F, γ ≠ 0 ∧ ∃ α : Fin m → F, (∀ i, α i ≠ 0) ∧ Q.IsometricIn F (QuadForm.diag (Fin.cons γ α)) ∧
      (∀ v ∈ T, RegTernaryRepresents (QuadForm.diag α) (v.adicCompletion F) X) ∧
      ∀ w : InfinitePlace F, RegTernaryRepresents (QuadForm.diag α) w.Completion X := by
  classical
  have dT := fun v (hv : v ∈ T) => exists_orth_data hQ hm (v.adicCompletion F) (hT v hv)
  have dW := fun w : InfinitePlace F => exists_orth_data hQ hm w.Completion (hw w)
  choose eT heT hUT using dT
  choose eW heW hUW using dW
  let c : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F := fun v =>
    if hv : v ∈ T then Q.evalIn _ (eT v hv) else 1
  have hc : ∀ v, c v ≠ 0 := fun v => by
    by_cases hv : v ∈ T
    · simp only [c, hv, ↓reduceDIte]; exact heT v hv
    · simp only [c, hv, ↓reduceDIte]; exact one_ne_zero
  obtain ⟨γ, hγ, hsqT, hsqW⟩ := OMeara.exists_approx_sq T c hc (fun w => Q.evalIn _ (eW w)) heW
  have hrep : Q.RepresentsIn F γ := by
    refine (represents_iff_everywhere_nf Q hQ γ hγ).mpr fun (p : NFPlace F) => ?_
    cases p with
    | infinite w =>
      obtain ⟨s, hs⟩ := hsqW w
      refine ⟨s • eW w, ?_⟩
      rw [QuadForm.evalIn_smul, sq, ← hs, div_mul_cancel₀ _ (heW w)]
    | finite v =>
      let _ : Invertible (2 : v.adicCompletion F) := invertibleOfNonzero two_ne_zero
      obtain ⟨x, hx⟩ := OMeara.S95.exists_Q_eq_of_four_le v (qk Q (v.adicCompletion F))
        (nondegenerate_qk_of Q _ hQ) (by rw [finrank_fin_fun]; omega) (algebraMap F _ γ)
      exact ⟨x, by rw [← qk_apply]; exact hx⟩
  obtain ⟨α, hα, hiso⟩ := QuadForm.exists_isometric_diag_cons hQ hγ hrep
  refine ⟨γ, hγ, α, hα, hiso, fun v hv => ?_, fun w => ?_⟩
  · have := hsqT v hv
    simp only [c, hv, ↓reduceDIte] at this
    exact split_at hγ hα _ hiso (eT v hv) (heT v hv) this (hUT v hv)
  · exact split_at hγ hα _ hiso (eW w) (heW w) (hsqW w) (hUW w)

/-- $(2 : \mathcal O_F) \notin \mathfrak p$ when $|2|_\mathfrak p = 1$. -/
theorem two_notMem_of_valuation {v : HeightOneSpectrum (𝓞 F)} (h : v.valuation F (2 : F) = 1) :
    (2 : 𝓞 F) ∉ v.asIdeal := by
  rw [← HeightOneSpectrum.intValuation_eq_one_iff, ← HeightOneSpectrum.valuation_of_algebraMap (K := F)]
  exact_mod_cast h

/-- The spots where $2$, or a non-zero element of a finite set $Y$, is not a unit: a finite set. -/
theorem finite_bad (Y : Finset F) :
    {v : HeightOneSpectrum (𝓞 F) | ¬ (v.valuation F (2 : F) = 1 ∧ ∀ y ∈ Y, y ≠ 0 → v.valuation F y = 1)}.Finite := by
  have h2 := eventually_valuation_eq_one (F := F) (two_ne_zero (α := F))
  have hY : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ y ∈ Y, y ≠ 0 → v.valuation F y = 1 := by
    rw [Filter.eventually_all_finset]
    intro y _
    by_cases hy : y = 0
    · exact Filter.Eventually.of_forall fun _ h => absurd hy h
    · filter_upwards [eventually_valuation_eq_one (F := F) hy] with v hv _ using hv
  exact Filter.eventually_cofinite.mp (h2.and hY)

end Global

end QuadFormsKB.Lattices
