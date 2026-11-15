/-
# Kitaoka 1993, Theorem 1.3.2 in characteristic $2$: isometries of a regular plane

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §1.3, proof of Theorem 1.3.2, second claim,
pp. 17–18 (printed pages).

**Setting.** $F$ is a finite field of characteristic $2$ with $q$ elements, $b$ the polar form. A regular plane has a
basis $v_1, v_2$ with $b(v_1, v_2) = 1$ and is then isometric to `binForm a c`:
$(s, t) \mapsto as^2 + st + ct^2$ with $a = Q(v_1)$, $c = Q(v_2)$.

**Proves**
* `isomCount_binForm`: $r(\mathrm{binForm}\ a\ c, W) = \#\{(x, y) : Q(x) = a, Q(y) = c, b(x, y) = 1\}$;
* `fiberCount`: for $x$ with $Q(x) = a$ and an isotropic $y_0$ with $b(x, y_0) = 1$,
  $\#\{y : Q(y) = c, b(x, y) = 1\} = \sum_s a(c - as^2 - s, W_1)$, $W_1$ the orthogonal complement of
  $\langle x, y_0\rangle$ (Kitaoka's computation with $W = H \perp W_0$);
* `exists_partner`: such a $y_0$ exists when $x \ne 0$ is isotropic, or when $W$ is isotropic (Witt's theorem,
  `QuadraticForm.exists_isometryEquiv_apply_eq_of_nondegenerate`).
-/
import QuadFormsKB.Literature.Kitaoka.Wave5.Ch1Char2Chi

open QuadraticMap Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Kitaoka.FqCount

variable {F : Type} [Field F]

/-- The binary form $(s, t) \mapsto as^2 + st + ct^2$. -/
def binForm (a c : F) : QuadraticForm F (F × F) :=
  a • QuadraticMap.linMulLin (LinearMap.fst F F F) (LinearMap.fst F F F) +
    QuadraticMap.linMulLin (LinearMap.fst F F F) (LinearMap.snd F F F) +
    c • QuadraticMap.linMulLin (LinearMap.snd F F F) (LinearMap.snd F F F)

@[simp] theorem binForm_apply (a c : F) (p : F × F) :
    binForm a c p = a * (p.1 * p.1) + p.1 * p.2 + c * (p.2 * p.2) := by
  simp [binForm]

/-- The linear map $(s, t) \mapsto sx + ty$. -/
def pairMap {W : Type} [AddCommGroup W] [Module F W] (x y : W) : (F × F) →ₗ[F] W :=
  (LinearMap.fst F F F).smulRight x + (LinearMap.snd F F F).smulRight y

@[simp] theorem pairMap_apply {W : Type} [AddCommGroup W] [Module F W] (x y : W) (p : F × F) :
    pairMap x y p = p.1 • x + p.2 • y := by simp [pairMap]

section Char2

variable (hF : ringChar F = 2)
include hF

theorem Q_pairMap {W : Type} [AddCommGroup W] [Module F W] (QW : QuadraticForm F W) (x y : W) (p : F × F) :
    QW (pairMap x y p) = QW x * (p.1 * p.1) + polar QW x y * (p.1 * p.2) + QW y * (p.2 * p.2) := by
  rw [pairMap_apply, QuadraticMap.map_add QW, QuadraticMap.map_smul, QuadraticMap.map_smul, polar_smul_left,
    polar_smul_right]
  simp only [smul_eq_mul]
  ring

/-- The polar form of `binForm a c` (characteristic $2$). -/
theorem polar_binForm (a c : F) (p p' : F × F) :
    polar (binForm a c) p p' = p.1 * p'.2 + p'.1 * p.2 := by
  have h2 := two_eq_zero_of_ringChar hF
  simp only [polar, binForm_apply, Prod.fst_add, Prod.snd_add]
  linear_combination (a * p.1 * p'.1 + c * p.2 * p'.2) * h2

theorem binForm_nondegenerate (a c : F) : (polarBilin (binForm a c)).Nondegenerate := by
  rw [QuadraticForm.nondegenerate_polarBilin_iff]
  intro p hp
  have h1 := hp (1, 0)
  have h2 := hp (0, 1)
  rw [polar_binForm hF] at h1 h2
  ext <;> simp_all

/-- **The isometries from `binForm a c`** are the pairs $(x, y)$ with $Q(x) = a$, $Q(y) = c$, $b(x, y) = 1$. -/
def isoBinEquiv {W : Type} [AddCommGroup W] [Module F W] (QW : QuadraticForm F W) (a c : F) :
    IsoT (binForm a c) QW ≃ {p : W × W // QW p.1 = a ∧ QW p.2 = c ∧ polar QW p.1 p.2 = 1} where
  toFun σ := ⟨(σ.1 (1, 0), σ.1 (0, 1)), by
    refine ⟨by rw [σ.2.2]; simp, by rw [σ.2.2]; simp, ?_⟩
    rw [polar_of_iso σ.1 σ.2.2, polar_binForm hF]; simp⟩
  invFun p := ⟨pairMap p.1.1 p.1.2,
    by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      rintro ⟨s, t⟩ h
      have h1 := congrArg (polar QW p.1.1) h
      have h2 := congrArg (polar QW p.1.2) h
      simp only [pairMap_apply, polar_add_right, polar_smul_right, polar_self_char2 hF, p.2.2.2,
        QuadraticMap.polar_zero_right, smul_eq_mul] at h1 h2
      rw [polar_comm, p.2.2.2] at h2
      simp at h1 h2
      simp [h1, h2],
    fun r => by
      rw [Q_pairMap hF, p.2.1, p.2.2.1, p.2.2.2, binForm_apply]; ring⟩
  left_inv σ := by
    apply Subtype.ext
    apply LinearMap.ext
    rintro ⟨s, t⟩
    simp only [pairMap_apply]
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1
    ext <;> simp
  right_inv p := by
    apply Subtype.ext
    simp

theorem isomCount_binForm {W : Type} [AddCommGroup W] [Module F W] (QW : QuadraticForm F W) (a c : F) :
    isomCount (binForm a c) QW = Nat.card {p : W × W // QW p.1 = a ∧ QW p.2 = c ∧ polar QW p.1 p.2 = 1} :=
  Nat.card_congr (isoBinEquiv hF QW a c)

/-- Every regular plane in characteristic $2$ is isometric to some `binForm a c`. -/
theorem exists_binForm {U : Type} [AddCommGroup U] [Module F U]
    [FiniteDimensional F U] {A : QuadraticForm F U} (hU : finrank F U = 2) (hA : (polarBilin A).Nondegenerate) :
    ∃ a c : F, A.Equivalent (binForm a c) := by
  have : Nontrivial U := Module.nontrivial_of_finrank_pos (by rw [hU]; norm_num)
  obtain ⟨v, hv⟩ : ∃ v : U, v ≠ 0 := exists_ne 0
  obtain ⟨w, hw⟩ : ∃ w, polar A v w ≠ 0 := by
    by_contra! h
    exact hv ((QuadraticForm.nondegenerate_polarBilin_iff A).mp hA v h)
  set w' := (polar A v w)⁻¹ • w
  have hvw : polar A v w' = 1 := by rw [polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hw]
  have hinj : Function.Injective (pairMap (F := F) v w') := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨s, t⟩ h
    have h1 := congrArg (polar A v) h
    have h2 := congrArg (polar A w') h
    simp only [pairMap_apply, polar_add_right, polar_smul_right, polar_self_char2 hF, hvw,
      QuadraticMap.polar_zero_right, smul_eq_mul] at h1 h2
    rw [polar_comm, hvw] at h2
    simp at h1 h2
    simp [h1, h2]
  have hbij : Function.Bijective (pairMap (F := F) v w') :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hU])).mp hinj⟩
  refine ⟨A v, A w', ⟨{ toLinearEquiv := (LinearEquiv.ofBijective _ hbij).symm, map_app' := fun u => ?_ }⟩⟩
  obtain ⟨p, rfl⟩ := hbij.2 u
  have : (LinearEquiv.ofBijective _ hbij).symm (pairMap (F := F) v w' p) = p :=
    (LinearEquiv.ofBijective _ hbij).symm_apply_apply p
  show binForm (A v) (A w') ((LinearEquiv.ofBijective _ hbij).symm (pairMap (F := F) v w' p)) = _
  rw [this]
  rw [Q_pairMap hF, hvw, binForm_apply]
  ring

end Char2

end QuadFormsKB.Kitaoka.FqCount
