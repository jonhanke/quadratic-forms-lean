import Mathlib
import QuadFormsKB.Citation

/-!
# Orbits of $\mathrm{SO}(V)$ on the quadrics $\{q = c\}$, $c\ne0$, with an explicit measurable section


**Generic, Mathlib-only hypotheses (upstreamable).** $R$ is a field with $2\ne0$, $H\in M_n(R)$ symmetric,
$q(x) = x^{\mathsf T}Hx$, $B(x, y) = x^{\mathsf T}Hy$ (for the library's `QuadForm`, $H$ = `hessian` and $q = 2Q$). For $q(u)\ne0$ the
reflection $\tau_u x = x - \frac{2B(u, x)}{q(u)}u$ is the matrix `refl H u` $= 1 - \frac{2}{q(u)}\,u\,(Hu)^{\mathsf T}$, with
**`transpose_refl_mul_mul_refl`** ($\tau_u^{\mathsf T}H\tau_u = H$) and **`det_refl`** ($\det\tau_u = -1$).

Fix $x_0$ with $q(x_0) = c\ne0$ and $w\perp x_0$ with $q(w)\ne0$. The **explicit section** of the orbit map
$g\mapsto gx_0$ on the quadric $\{q = c\}$ is
$$ s(x) = \begin{cases}\tau_{x + x_0}\,\tau_{x_0} & q(x + x_0)\ne 0,\\ \tau_{x - x_0}\,\tau_w & \text{otherwise}\end{cases} $$
(`sphereSec`): **`sphereSec_mulVec`** $s(x)x_0 = x$ for $q(x) = c$ (in the second case $q(x - x_0) = 4c\ne0$),
**`sphereSec_mem`** $s(x)^{\mathsf T}Hs(x) = H$ and $\det s(x) = 1$, and **`measurable_sphereSec`** ($R$ with measurable
field operations). Consequences:

* **`exists_SO_mulVec_eq`** (Witt's theorem for nonzero values, in the library's matrix form): if $q(x) = q(y) = c\ne0$ then
  $y = gx$ for some $g$ with $g^{\mathsf T}Hg = H$, $\det g = 1$; so for every field $R\supseteq F$ (local $F_v$, $\mathbb R$,
  $\mathbb C$, or $F$ itself) the $\mathrm{SO}(V)(R)$-orbits on $\{q = c\}$, $c\ne0$, are the whole quadric;
* **`exists_orth_anisotropic`**: such a $w$ exists when $\det H\ne0$ and $n\ge2$.

No reflection-generation theorem (Cartan–Dieudonné) and no Witt extension theorem is needed: two reflections suffice.
-/

open Matrix MeasureTheory
open scoped Matrix

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {R : Type*} [Field R] {n : ℕ} (H : Matrix (Fin n) (Fin n) R)

/-- $q(x) = x^{\mathsf T}Hx$. -/
def qH (x : Fin n → R) : R := x ⬝ᵥ (H *ᵥ x)

/-- $B(x, y) = x^{\mathsf T}Hy$. -/
def bH (x y : Fin n → R) : R := x ⬝ᵥ (H *ᵥ y)

theorem qH_eq_bH (x : Fin n → R) : qH H x = bH H x x := rfl

variable {H}

theorem bH_comm (hH : Hᵀ = H) (x y : Fin n → R) : bH H x y = bH H y x := by
  unfold bH
  rw [dotProduct_mulVec, ← mulVec_transpose, hH, dotProduct_comm]

theorem bH_add_left (x y z : Fin n → R) : bH H (x + y) z = bH H x z + bH H y z := add_dotProduct _ _ _

theorem bH_add_right (x y z : Fin n → R) : bH H x (y + z) = bH H x y + bH H x z := by
  simp [bH, mulVec_add, dotProduct_add]

theorem bH_sub_left (x y z : Fin n → R) : bH H (x - y) z = bH H x z - bH H y z := sub_dotProduct _ _ _

theorem bH_sub_right (x y z : Fin n → R) : bH H x (y - z) = bH H x y - bH H x z := by
  simp [bH, mulVec_sub, dotProduct_sub]

theorem bH_smul_left (a : R) (x y : Fin n → R) : bH H (a • x) y = a * bH H x y := smul_dotProduct _ _ _

theorem bH_smul_right (a : R) (x y : Fin n → R) : bH H x (a • y) = a * bH H x y := by
  simp [bH, mulVec_smul, dotProduct_smul]

theorem bH_neg_left (x y : Fin n → R) : bH H (-x) y = -bH H x y := neg_dotProduct _ _

theorem qH_add (hH : Hᵀ = H) (x y : Fin n → R) : qH H (x + y) = qH H x + 2 * bH H x y + qH H y := by
  simp only [qH_eq_bH, bH_add_left, bH_add_right, bH_comm hH y x]; ring

theorem qH_sub (hH : Hᵀ = H) (x y : Fin n → R) : qH H (x - y) = qH H x - 2 * bH H x y + qH H y := by
  simp only [qH_eq_bH, bH_sub_left, bH_sub_right, bH_comm hH y x]; ring

variable (H) in
/-- **The reflection** $\tau_u = 1 - \frac{2}{q(u)}\,u\,(Hu)^{\mathsf T}$. -/
def refl (u : Fin n → R) : Matrix (Fin n) (Fin n) R := 1 - (2 / qH H u) • vecMulVec u (H *ᵥ u)

/-- $\tau_u x = x - \frac{2B(u, x)}{q(u)}u$. -/
theorem refl_mulVec (hH : Hᵀ = H) (u x : Fin n → R) :
    refl H u *ᵥ x = x - (2 * bH H u x / qH H u) • u := by
  rw [refl, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, smul_smul]
  have : (H *ᵥ u) ⬝ᵥ x = bH H u x := by rw [dotProduct_comm]; exact bH_comm hH x u
  rw [this]
  congr 2
  ring

/-- **$\tau_u^{\mathsf T}H\tau_u = H$.** -/
theorem transpose_refl_mul_mul_refl (hH : Hᵀ = H) {u : Fin n → R} (hu : qH H u ≠ 0) :
    (refl H u)ᵀ * H * refl H u = H := by
  set b := H *ᵥ u
  set c := 2 / qH H u
  have hub : u ᵥ* H = b := by rw [← mulVec_transpose, hH]
  have hq : b ⬝ᵥ u = qH H u := by rw [dotProduct_comm]; rfl
  have e1 : H * vecMulVec u b = vecMulVec b b := mul_vecMulVec _ _ _
  have e2 : vecMulVec b u * H = vecMulVec b b := by rw [vecMulVec_mul, hub]
  have e3 : vecMulVec b u * H * vecMulVec u b = qH H u • vecMulVec b b := by
    rw [e2, vecMulVec_mul_vecMulVec, hq, vecMulVec_smul]
  have hc : c * c * qH H u = 2 * c := by
    simp only [c]; field_simp
  have hT : (refl H u)ᵀ = 1 - c • vecMulVec b u := by
    simp only [refl, transpose_sub, transpose_one, transpose_smul, transpose_vecMulVec, b, c]
  have hexp : (1 - c • vecMulVec b u) * H * (1 - c • vecMulVec u b) =
      H - c • (vecMulVec b u * H) - c • (H * vecMulVec u b) + (c * c) • (vecMulVec b u * H * vecMulVec u b) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
    abel
  rw [hT, show refl H u = 1 - c • vecMulVec u b from rfl, hexp, e3, e1, e2, smul_smul, hc]
  module

/-- **$\det\tau_u = -1$.** -/
theorem det_refl {u : Fin n → R} (hu : qH H u ≠ 0) : (refl H u).det = -1 := by
  have : refl H u = 1 + replicateCol Unit (-(2 / qH H u) • u) * replicateRow Unit (H *ᵥ u) := by
    rw [refl, ← vecMulVec_eq Unit, smul_vecMulVec, neg_smul, sub_eq_add_neg]
  rw [this, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, dotProduct_comm, smul_eq_mul]
  have : u ⬝ᵥ (H *ᵥ u) = qH H u := rfl
  rw [this]
  field_simp
  ring

theorem refl_self (hH : Hᵀ = H) {u : Fin n → R} (hu : qH H u ≠ 0) : refl H u *ᵥ u = -u := by
  rw [refl_mulVec hH, ← qH_eq_bH]
  rw [show 2 * qH H u / qH H u = 2 by field_simp]
  rw [two_smul]; abel

theorem refl_of_orth (hH : Hᵀ = H) {u x : Fin n → R} (h : bH H u x = 0) : refl H u *ᵥ x = x := by
  rw [refl_mulVec hH, h]; simp

/-! ### The explicit section on the quadric -/

/-- Data for the section: a base point $x_0$ with $q(x_0)\ne0$ and an anisotropic $w\perp x_0$. -/
structure SphereData (H : Matrix (Fin n) (Fin n) R) where
  /-- The base point $x_0$. -/
  x₀ : Fin n → R
  /-- An auxiliary vector $w$. -/
  w : Fin n → R
  /-- $q(x_0)\ne 0$. -/
  hx₀ : qH H x₀ ≠ 0
  /-- $q(w)\ne 0$. -/
  hw : qH H w ≠ 0
  /-- $B(w, x_0) = 0$. -/
  horth : bH H w x₀ = 0

open Classical in
/-- **The section** $s(x) = \tau_{x+x_0}\tau_{x_0}$ if $q(x + x_0)\ne0$, else $\tau_{x-x_0}\tau_w$. -/
def sphereSec (D : SphereData H) (x : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  if qH H (x + D.x₀) ≠ 0 then refl H (x + D.x₀) * refl H D.x₀ else refl H (x - D.x₀) * refl H D.w

/-- In the second case, $q(x - x_0) = 4c\ne 0$. -/
theorem qH_sub_ne_zero (hH : Hᵀ = H) (h2 : (2 : R) ≠ 0) (D : SphereData H) {x : Fin n → R}
    (hx : qH H x = qH H D.x₀) (h : qH H (x + D.x₀) = 0) : qH H (x - D.x₀) ≠ 0 := by
  rw [qH_add hH] at h
  rw [qH_sub hH]
  intro h'
  have : 4 * qH H D.x₀ = 0 := by linear_combination h + h' - 2 * hx
  have h4 : (4 : R) ≠ 0 := by
    have : (4 : R) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  exact D.hx₀ ((mul_eq_zero.1 this).resolve_left h4)

/-- **$s(x)x_0 = x$** on the quadric $q(x) = q(x_0)$. -/
@[kb "weil1982" "§2.4 (orbits of SO(V) on {q = c}) [unverified page]; omeara1963 §42 (Witt's theorem) [unverified]"]
theorem sphereSec_mulVec (hH : Hᵀ = H) (h2 : (2 : R) ≠ 0) (D : SphereData H) {x : Fin n → R}
    (hx : qH H x = qH H D.x₀) : sphereSec D x *ᵥ D.x₀ = x := by
  unfold sphereSec
  split_ifs with h
  · rw [← mulVec_mulVec, refl_self hH D.hx₀, mulVec_neg, refl_mulVec hH]
    have hq : qH H (x + D.x₀) = 2 * bH H (x + D.x₀) D.x₀ := by
      rw [qH_add hH, bH_add_left, ← qH_eq_bH, hx]; ring
    have hB0 : bH H (x + D.x₀) D.x₀ ≠ 0 := fun h0 => h (by rw [hq, h0, mul_zero])
    rw [hq, div_self (mul_ne_zero h2 hB0), one_smul]
    abel
  · push Not at h
    have hne := qH_sub_ne_zero hH h2 D hx h
    rw [← mulVec_mulVec, refl_of_orth hH D.horth, refl_mulVec hH]
    have hB : bH H x D.x₀ = -qH H D.x₀ := by
      rw [qH_add hH, hx] at h
      have : 2 * (bH H x D.x₀ + qH H D.x₀) = 0 := by linear_combination h
      have := (mul_eq_zero.1 this).resolve_left h2
      linear_combination this
    have hq : qH H (x - D.x₀) = 4 * qH H D.x₀ := by
      rw [qH_sub hH, hx, hB]; ring
    have hb : bH H (x - D.x₀) D.x₀ = -2 * qH H D.x₀ := by
      rw [bH_sub_left, hB, ← qH_eq_bH]; ring
    have h4 : (4 : R) ≠ 0 := by
      have : (4 : R) = 2 * 2 := by norm_num
      rw [this]; exact mul_ne_zero h2 h2
    rw [hb, hq, show 2 * (-2 * qH H D.x₀) / (4 * qH H D.x₀) = -1 by
      rw [div_eq_iff (mul_ne_zero h4 D.hx₀)]; ring]
    simp

/-- **$s(x)\in\mathrm{SO}(H)$:** $s(x)^{\mathsf T}Hs(x) = H$ and $\det s(x) = 1$, on the quadric $q(x) = q(x_0)$. -/
@[kb "weil1982" "§2.4 (orbits of SO(V) on {q = c}) [unverified page]"]
theorem sphereSec_mem (hH : Hᵀ = H) (h2 : (2 : R) ≠ 0) (D : SphereData H) {x : Fin n → R}
    (hx : qH H x = qH H D.x₀) :
    (sphereSec D x)ᵀ * H * sphereSec D x = H ∧ (sphereSec D x).det = 1 := by
  have key : ∀ {u v : Fin n → R}, qH H u ≠ 0 → qH H v ≠ 0 →
      (refl H u * refl H v)ᵀ * H * (refl H u * refl H v) = H ∧ (refl H u * refl H v).det = 1 := by
    intro u v hu hv
    refine ⟨?_, ?_⟩
    · rw [transpose_mul, show (refl H v)ᵀ * (refl H u)ᵀ * H * (refl H u * refl H v) =
          (refl H v)ᵀ * ((refl H u)ᵀ * H * refl H u) * refl H v by simp only [Matrix.mul_assoc],
        transpose_refl_mul_mul_refl hH hu, transpose_refl_mul_mul_refl hH hv]
    · rw [det_mul, det_refl hu, det_refl hv]; ring
  unfold sphereSec
  split_ifs with h
  · exact key h D.hx₀
  · push Not at h
    exact key (qH_sub_ne_zero hH h2 D hx h) D.hw

/-- **Witt's theorem for nonzero values, explicit form:** if $q(x) = q(y)\ne 0$ (and an anisotropic vector orthogonal
to $x$ exists, e.g. by `exists_orth_anisotropic`), then $y = gx$ with $g^{\mathsf T}Hg = H$, $\det g = 1$. -/
@[kb "omeara1963" "§42 (Witt's theorem) [unverified]; weil1982 §2.4 [unverified page]"]
theorem exists_SO_mulVec_eq (hH : Hᵀ = H) (h2 : (2 : R) ≠ 0) (D : SphereData H) {y : Fin n → R}
    (hy : qH H y = qH H D.x₀) :
    ∃ g : Matrix (Fin n) (Fin n) R, gᵀ * H * g = H ∧ g.det = 1 ∧ g *ᵥ D.x₀ = y :=
  ⟨sphereSec D y, (sphereSec_mem hH h2 D hy).1, (sphereSec_mem hH h2 D hy).2, sphereSec_mulVec hH h2 D hy⟩

/-- **Existence of the auxiliary vector:** if $\det H\ne 0$, $n\ge2$ and $q(x_0)\ne0$, some $w\perp x_0$ has
$q(w)\ne 0$ (else $q(x_0)\,H = (Hx_0)(Hx_0)^{\mathsf T}$ would have rank $\le 1$). -/
theorem exists_orth_anisotropic (hH : Hᵀ = H) (h2 : (2 : R) ≠ 0) (hdet : H.det ≠ 0) (hn : 2 ≤ n)
    {x₀ : Fin n → R} (hx₀ : qH H x₀ ≠ 0) : ∃ w, qH H w ≠ 0 ∧ bH H w x₀ = 0 := by
  by_contra hcon
  push Not at hcon
  set c := qH H x₀
  -- the projection of `z` to `x₀^⊥`
  have hproj : ∀ z : Fin n → R, c * qH H z = bH H x₀ z ^ 2 := by
    intro z
    set w := z - (bH H x₀ z / c) • x₀
    have hw0 : bH H w x₀ = 0 := by
      rw [bH_sub_left, bH_smul_left, ← qH_eq_bH, bH_comm hH]
      field_simp
      ring
    have hqw : qH H w = 0 := by
      by_contra hne; exact hcon w hne hw0
    rw [qH_sub hH, bH_smul_right, show qH H ((bH H x₀ z / c) • x₀) = (bH H x₀ z / c) ^ 2 * c by
      rw [qH_eq_bH, bH_smul_left, bH_smul_right, ← qH_eq_bH]; ring, bH_comm hH z x₀] at hqw
    field_simp at hqw
    linear_combination hqw
  -- polarize: `c • H = vecMulVec (H x₀) (H x₀)`
  have hmat : c • H = vecMulVec (H *ᵥ x₀) (H *ᵥ x₀) := by
    ext i j
    have hi := hproj (Pi.single i 1)
    have hj := hproj (Pi.single j 1)
    have hij := hproj (Pi.single i 1 + Pi.single j 1)
    have hbi : bH H x₀ (Pi.single i 1) = (H *ᵥ x₀) i := by
      rw [bH_comm hH]; simp [bH, mulVec, dotProduct, Pi.single_apply]
    have hbj : bH H x₀ (Pi.single j 1) = (H *ᵥ x₀) j := by
      rw [bH_comm hH]; simp [bH, mulVec, dotProduct, Pi.single_apply]
    have hbij : bH H (Pi.single i 1) (Pi.single j 1) = H i j := by
      simp [bH, mulVec, dotProduct, Pi.single_apply]
    rw [qH_add hH, bH_add_right, hbi, hbj, hbij] at hij
    rw [hbi] at hi
    rw [hbj] at hj
    simp only [Matrix.smul_apply, smul_eq_mul, vecMulVec_apply]
    have : 2 * (c * H i j) = 2 * ((H *ᵥ x₀) i * (H *ᵥ x₀) j) := by linear_combination hij - hi - hj
    exact mul_left_cancel₀ h2 this
  have hne : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  have := congrArg Matrix.det hmat
  rw [det_smul, det_vecMulVec, Fintype.card_fin] at this
  exact mul_ne_zero (pow_ne_zero _ hx₀) hdet this

/-! ### Measurability -/

section Measurable

variable [MeasurableSpace R] [MeasurableAdd₂ R] [MeasurableSub₂ R] [MeasurableMul₂ R] [MeasurableInv R]
  [MeasurableSingletonClass R]

theorem measurable_qH_comp {α : Type*} [MeasurableSpace α] {f : α → Fin n → R} (hf : Measurable f) :
    Measurable fun a => qH H (f a) := by
  unfold qH dotProduct mulVec dotProduct
  exact Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).comp hf).mul
    (Finset.measurable_sum _ fun j _ => measurable_const.mul ((measurable_pi_apply j).comp hf))

theorem measurable_refl_comp {α : Type*} [MeasurableSpace α] {f : α → Fin n → R} (hf : Measurable f) :
    Measurable fun a => refl H (f a) := by
  have hq := measurable_qH_comp (H := H) hf
  have hHu : ∀ j, Measurable fun a => (H *ᵥ f a) j := fun j => by
    unfold mulVec dotProduct
    exact Finset.measurable_sum _ fun k _ => measurable_const.mul ((measurable_pi_apply k).comp hf)
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  simp only [refl, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  exact measurable_const.sub ((measurable_const.div hq).mul (((measurable_pi_apply i).comp hf).mul (hHu j)))

theorem measurable_matMul {α : Type*} [MeasurableSpace α] {f g : α → Matrix (Fin n) (Fin n) R}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun a => f a * g a := by
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  simp only [mul_apply]
  exact Finset.measurable_sum _ fun k _ =>
    ((measurable_pi_apply k).comp ((measurable_pi_apply i).comp hf)).mul
      ((measurable_pi_apply j).comp ((measurable_pi_apply k).comp hg))

/-- **The section is measurable** (for measurable field operations on $R$). -/
@[kb "weil1982" "§2.4 (measurable sections of orbit maps) [unverified page]"]
theorem measurable_sphereSec (D : SphereData H) : Measurable (sphereSec D) := by
  classical
  have hs : MeasurableSet {x : Fin n → R | qH H (x + D.x₀) ≠ 0} :=
    (measurable_qH_comp (measurable_id.add_const D.x₀)) (measurableSet_singleton 0).compl
  have h1 : Measurable fun x : Fin n → R => refl H (x + D.x₀) * refl H D.x₀ :=
    measurable_matMul (measurable_refl_comp (measurable_id.add_const D.x₀)) measurable_const
  have h2 : Measurable fun x : Fin n → R => refl H (x - D.x₀) * refl H D.w :=
    measurable_matMul (measurable_refl_comp (measurable_id.sub_const D.x₀)) measurable_const
  exact Measurable.ite hs h1 h2

end Measurable

end

end QuadFormsKB.Tamagawa.Measure.Weil
